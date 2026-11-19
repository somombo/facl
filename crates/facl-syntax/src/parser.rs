//! The parser itself. It works directly on bytes, because path patterns use a
//! different character set from expressions.

use crate::MAX_NESTING;
use facl_core::{Allow, CmpOp, Expr, ExprKind, Item, Match, PatSeg, Service, Span, action_bits};

/// A syntax error and where it is.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct ParseError {
    /// What went wrong.
    pub message: String,
    /// The offending bytes.
    pub span: Span,
}

/// Words that cannot be used as names: CEL's reserved words and facl's own.
const RESERVED: [&str; 24] = [
    "in",
    "true",
    "false",
    "null",
    "as",
    "break",
    "const",
    "continue",
    "else",
    "for",
    "function",
    "if",
    "import",
    "let",
    "loop",
    "package",
    "namespace",
    "return",
    "var",
    "void",
    "while",
    "service",
    "match",
    "allow",
];

/// Parses a rules file.
pub fn parse(source: &str) -> Result<Service, ParseError> {
    if source.len() > u32::MAX as usize {
        return Err(ParseError {
            message: "source is too large".to_string(),
            span: Span { start: 0, end: 0 },
        });
    }
    let mut p = Parser {
        text: source,
        src: source.as_bytes(),
        pos: 0,
        depth: 0,
    };
    p.parse_service()
}

struct Parser<'a> {
    text: &'a str,
    src: &'a [u8],
    pos: usize,
    depth: u32,
}

type Res<T> = Result<T, ParseError>;

fn is_name_start(b: u8) -> bool {
    b.is_ascii_alphabetic() || b == b'_'
}

fn is_name_char(b: u8) -> bool {
    b.is_ascii_alphanumeric() || b == b'_'
}

fn is_literal_char(b: u8) -> bool {
    b.is_ascii_alphanumeric() || matches!(b, b'_' | b'.' | b'~' | b'-')
}

fn span(start: usize, end: usize) -> Span {
    Span {
        start: start as u32,
        end: end as u32,
    }
}

impl Parser<'_> {
    // ---- errors and low-level helpers ----

    fn error<T>(&self, start: usize, end: usize, message: String) -> Res<T> {
        Err(ParseError {
            message,
            span: span(start, end),
        })
    }

    fn error_here<T>(&self, message: String) -> Res<T> {
        let end = (self.pos + 1).min(self.src.len());
        self.error(self.pos, end, message)
    }

    /// Describes the next input for "found ..." messages.
    fn found(&self) -> String {
        match self.text.get(self.pos..).and_then(|s| s.chars().next()) {
            Some(c) => format!("'{c}'"),
            None if self.pos >= self.src.len() => "end of input".to_string(),
            None => "an invalid byte".to_string(),
        }
    }

    fn peek(&self) -> Option<u8> {
        self.src.get(self.pos).copied()
    }

    fn peek_at(&self, offset: usize) -> Option<u8> {
        self.src.get(self.pos + offset).copied()
    }

    fn starts_with(&self, s: &str) -> bool {
        self.src[self.pos..].starts_with(s.as_bytes())
    }

    /// Skips whitespace and comments.
    fn skip_ws(&mut self) -> Res<()> {
        loop {
            match self.peek() {
                Some(b) if b.is_ascii_whitespace() => self.pos += 1,
                Some(b'/') if self.peek_at(1) == Some(b'/') => {
                    while !matches!(self.peek(), None | Some(b'\n')) {
                        self.pos += 1;
                    }
                }
                Some(b'/') if self.peek_at(1) == Some(b'*') => {
                    let start = self.pos;
                    self.pos += 2;
                    loop {
                        if self.pos >= self.src.len() {
                            return self.error(start, start + 2, "unterminated comment".into());
                        }
                        if self.starts_with("*/") {
                            self.pos += 2;
                            break;
                        }
                        self.pos += 1;
                    }
                }
                _ => return Ok(()),
            }
        }
    }

    /// Consumes `p` if it comes next, after whitespace.
    /// On failure the position is left where it was, so spans never include
    /// trailing whitespace.
    fn eat(&mut self, p: &str) -> Res<bool> {
        let before = self.pos;
        self.skip_ws()?;
        if self.starts_with(p) {
            self.pos += p.len();
            Ok(true)
        } else {
            self.pos = before;
            Ok(false)
        }
    }

    fn expect(&mut self, p: &str) -> Res<()> {
        if self.eat(p)? {
            Ok(())
        } else {
            self.skip_ws()?;
            self.error_here(format!("expected '{p}', found {}", self.found()))
        }
    }

    /// Reads the word after any whitespace, without consuming anything.
    fn peek_word(&mut self) -> Res<String> {
        let before = self.pos;
        self.skip_ws()?;
        let mut end = self.pos;
        if self.src.get(end).is_some_and(|b| is_name_start(*b)) {
            while self.src.get(end).is_some_and(|b| is_name_char(*b)) {
                end += 1;
            }
        }
        let word = self.text[self.pos..end].to_string();
        self.pos = before;
        Ok(word)
    }

    /// Reads and consumes a word, which may be reserved.
    fn word(&mut self) -> Res<(String, Span)> {
        self.skip_ws()?;
        let w = self.peek_word()?;
        if w.is_empty() {
            return self.error_here(format!("expected a name, found {}", self.found()));
        }
        let start = self.pos;
        self.pos += w.len();
        Ok((w, span(start, self.pos)))
    }

    /// Reads a name that must not be a reserved word.
    fn name(&mut self) -> Res<(String, Span)> {
        let (w, sp) = self.word()?;
        if RESERVED.contains(&w.as_str()) {
            return self.error(
                sp.start as usize,
                sp.end as usize,
                format!("'{w}' is a reserved word and cannot be used as a name"),
            );
        }
        Ok((w, sp))
    }

    fn keyword(&mut self, kw: &str) -> Res<()> {
        self.skip_ws()?;
        let w = self.peek_word()?;
        if w == kw {
            self.pos += kw.len();
            Ok(())
        } else {
            self.error_here(format!("expected '{kw}', found {}", self.found()))
        }
    }

    fn enter(&mut self) -> Res<()> {
        if self.depth >= MAX_NESTING {
            return self.error_here(format!("nested more than {MAX_NESTING} levels deep"));
        }
        self.depth += 1;
        Ok(())
    }

    // ---- structure ----

    fn parse_service(&mut self) -> Res<Service> {
        self.skip_ws()?;
        let start = self.pos;
        self.keyword("service")?;
        let mut name = self.word()?.0;
        while self.eat(".")? {
            name.push('.');
            name.push_str(&self.word()?.0);
        }
        self.expect("{")?;
        let mut matches = Vec::new();
        loop {
            self.skip_ws()?;
            let w = self.peek_word()?;
            if w == "match" {
                matches.push(self.parse_match()?);
            } else if self.peek() == Some(b'}') {
                break;
            } else {
                return self
                    .error_here(format!("expected 'match' or '}}', found {}", self.found()));
            }
        }
        self.expect("}")?;
        let end = self.pos;
        self.skip_ws()?;
        if self.pos < self.src.len() {
            return self.error_here("unexpected content after the service block".to_string());
        }
        Ok(Service {
            name: name.into_bytes(),
            matches,
            span: span(start, end),
        })
    }

    fn parse_match(&mut self) -> Res<Match> {
        self.enter()?;
        let start = self.pos;
        self.keyword("match")?;
        let pattern = self.parse_pattern()?;
        self.expect("{")?;
        let mut body = Vec::new();
        loop {
            self.skip_ws()?;
            let w = self.peek_word()?;
            if w == "match" {
                body.push(Item::Match(self.parse_match()?));
            } else if w == "allow" {
                body.push(Item::Allow(self.parse_allow()?));
            } else if self.peek() == Some(b'}') {
                break;
            } else {
                return self.error_here(format!(
                    "expected 'match', 'allow' or '}}', found {}",
                    self.found()
                ));
            }
        }
        self.expect("}")?;
        self.depth -= 1;
        Ok(Match {
            pattern,
            body,
            span: span(start, self.pos),
        })
    }

    fn at_segment_start(&self) -> bool {
        self.peek().is_some_and(|b| is_literal_char(b) || b == b'{')
    }

    fn parse_pattern(&mut self) -> Res<Vec<PatSeg>> {
        self.skip_ws()?;
        if self.peek() != Some(b'/') {
            return self.error_here(format!(
                "expected a path pattern starting with '/', found {}",
                self.found()
            ));
        }
        self.pos += 1;
        let mut segs = Vec::new();
        if !self.at_segment_start() {
            return Ok(segs);
        }
        loop {
            segs.push(self.parse_segment()?);
            if self.peek() == Some(b'/') {
                self.pos += 1;
                if !self.at_segment_start() {
                    return self.error_here(format!(
                        "expected a path segment after '/', found {}",
                        self.found()
                    ));
                }
            } else {
                return Ok(segs);
            }
        }
    }

    fn parse_segment(&mut self) -> Res<PatSeg> {
        if self.peek() == Some(b'{') {
            self.pos += 1;
            let name = self.name()?.0.into_bytes();
            let rest = self.eat("=")?;
            if rest {
                self.expect("**")?;
            }
            self.expect("}")?;
            return Ok(if rest {
                PatSeg::Rest(name)
            } else {
                PatSeg::Var(name)
            });
        }
        let start = self.pos;
        while self.peek().is_some_and(is_literal_char) {
            self.pos += 1;
        }
        let lit = &self.src[start..self.pos];
        if lit == b"." || lit == b".." {
            return self.error(
                start,
                self.pos,
                "'.' and '..' are not valid segments".into(),
            );
        }
        Ok(PatSeg::Lit(lit.to_vec()))
    }

    fn parse_allow(&mut self) -> Res<Allow> {
        let start = self.pos;
        self.keyword("allow")?;
        let mut methods = 0u8;
        loop {
            let (w, sp) = self.word()?;
            match action_bits(w.as_bytes()) {
                Some(bits) => methods |= bits,
                None => {
                    return self.error(
                        sp.start as usize,
                        sp.end as usize,
                        format!("unknown action '{w}'"),
                    );
                }
            }
            if !self.eat(",")? {
                break;
            }
        }
        let cond = if self.eat(":")? {
            self.keyword("if")?;
            Some(self.parse_expr()?)
        } else {
            None
        };
        self.expect(";")?;
        Ok(Allow {
            methods,
            cond,
            span: span(start, self.pos),
        })
    }

    // ---- expressions ----

    fn parse_expr(&mut self) -> Res<Expr> {
        self.enter()?;
        let e = self.parse_or()?;
        self.depth -= 1;
        Ok(e)
    }

    fn chain_limit(&self, count: u32) -> Res<()> {
        if count > MAX_NESTING {
            return self.error_here(format!("expression has more than {MAX_NESTING} operands"));
        }
        Ok(())
    }

    fn parse_or(&mut self) -> Res<Expr> {
        let mut left = self.parse_and()?;
        let mut count = 1;
        while self.eat("||")? {
            let right = self.parse_and()?;
            count += 1;
            self.chain_limit(count)?;
            left = binary(left, right, ExprKind::Or);
        }
        Ok(left)
    }

    fn parse_and(&mut self) -> Res<Expr> {
        let mut left = self.parse_rel()?;
        let mut count = 1;
        while self.eat("&&")? {
            let right = self.parse_rel()?;
            count += 1;
            self.chain_limit(count)?;
            left = binary(left, right, ExprKind::And);
        }
        Ok(left)
    }

    fn rel_op(&mut self) -> Res<Option<Option<CmpOp>>> {
        // Some(None) is `in`; Some(Some(op)) is a comparison.
        let before = self.pos;
        self.skip_ws()?;
        for (text, op) in [
            ("==", CmpOp::Eq),
            ("!=", CmpOp::Ne),
            ("<=", CmpOp::Le),
            (">=", CmpOp::Ge),
            ("<", CmpOp::Lt),
            (">", CmpOp::Gt),
        ] {
            if self.starts_with(text) {
                self.pos += text.len();
                return Ok(Some(Some(op)));
            }
        }
        if self.peek_word()? == "in" {
            self.pos += 2;
            return Ok(Some(None));
        }
        self.pos = before;
        Ok(None)
    }

    fn parse_rel(&mut self) -> Res<Expr> {
        let mut left = self.parse_unary()?;
        let mut count = 1;
        while let Some(op) = self.rel_op()? {
            let right = self.parse_unary()?;
            count += 1;
            self.chain_limit(count)?;
            left = match op {
                Some(op) => binary(left, right, |a, b| ExprKind::Cmp(op, a, b)),
                None => binary(left, right, ExprKind::In),
            };
        }
        Ok(left)
    }

    fn parse_unary(&mut self) -> Res<Expr> {
        let mut bangs = Vec::new();
        while self.eat("!")? {
            self.enter()?;
            bangs.push(self.pos - 1);
        }
        let mut e = self.parse_postfix()?;
        while let Some(start) = bangs.pop() {
            self.depth -= 1;
            e = Expr {
                span: span(start, e.span.end as usize),
                kind: ExprKind::Not(Box::new(e)),
            };
        }
        Ok(e)
    }

    fn parse_postfix(&mut self) -> Res<Expr> {
        let mut e = self.parse_primary()?;
        let mut count = 1;
        loop {
            let start = e.span.start as usize;
            let target = Box::new(e);
            if self.eat(".")? {
                let name = self.name()?.0.into_bytes();
                let kind = if self.eat("(")? {
                    ExprKind::Method(target, name, self.parse_args(")")?)
                } else {
                    ExprKind::Select(target, name)
                };
                e = Expr {
                    kind,
                    span: span(start, self.pos),
                };
            } else if self.eat("[")? {
                let key = self.parse_expr()?;
                self.expect("]")?;
                e = Expr {
                    kind: ExprKind::Index(target, Box::new(key)),
                    span: span(start, self.pos),
                };
            } else {
                return Ok(*target);
            }
            count += 1;
            self.chain_limit(count)?;
        }
    }

    /// Parses comma-separated expressions up to the closing token.
    fn parse_args(&mut self, close: &str) -> Res<Vec<Expr>> {
        let mut args = Vec::new();
        if self.eat(close)? {
            return Ok(args);
        }
        loop {
            args.push(self.parse_expr()?);
            if self.eat(",")? {
                continue;
            }
            self.expect(close)?;
            return Ok(args);
        }
    }

    fn parse_primary(&mut self) -> Res<Expr> {
        self.skip_ws()?;
        let start = self.pos;
        let Some(b) = self.peek() else {
            return self.error_here("expected an expression, found end of input".to_string());
        };
        let kind = match b {
            b'0'..=b'9' => ExprKind::Int(self.parse_int(false)?),
            b'-' => {
                self.pos += 1;
                self.skip_ws()?;
                if !self.peek().is_some_and(|d| d.is_ascii_digit()) {
                    return self.error_here("expected an integer after '-'".to_string());
                }
                ExprKind::Int(self.parse_int(true)?)
            }
            b'"' | b'\'' => ExprKind::Str(self.parse_string(b)?),
            b'(' => {
                self.pos += 1;
                let inner = self.parse_expr()?;
                self.expect(")")?;
                return Ok(Expr {
                    kind: inner.kind,
                    span: span(start, self.pos),
                });
            }
            b'[' => {
                self.pos += 1;
                ExprKind::List(self.parse_args("]")?)
            }
            b if is_name_start(b) => self.parse_word_expr()?,
            _ => {
                return self.error_here(format!("expected an expression, found {}", self.found()));
            }
        };
        Ok(Expr {
            kind,
            span: span(start, self.pos),
        })
    }

    /// A literal keyword, an identifier or a global call.
    fn parse_word_expr(&mut self) -> Res<ExprKind> {
        let w = self.peek_word()?;
        match w.as_str() {
            "true" | "false" | "null" => {
                self.pos += w.len();
                return Ok(match w.as_str() {
                    "true" => ExprKind::Bool(true),
                    "false" => ExprKind::Bool(false),
                    _ => ExprKind::Null,
                });
            }
            _ => {}
        }
        let name = self.name()?.0.into_bytes();
        if self.eat("(")? {
            Ok(ExprKind::Call(name, self.parse_args(")")?))
        } else {
            Ok(ExprKind::Ident(name))
        }
    }

    fn parse_int(&mut self, negative: bool) -> Res<i64> {
        let start = self.pos;
        let mut magnitude: u64 = 0;
        let mut overflow = false;
        while let Some(d) = self.peek().filter(u8::is_ascii_digit) {
            match magnitude
                .checked_mul(10)
                .and_then(|m| m.checked_add(u64::from(d - b'0')))
            {
                Some(m) => magnitude = m,
                None => overflow = true,
            }
            self.pos += 1;
        }
        if self.peek().is_some_and(is_name_char) {
            return self.error_here("invalid number".to_string());
        }
        let limit = if negative {
            i64::MAX as u64 + 1
        } else {
            i64::MAX as u64
        };
        if overflow || magnitude > limit {
            return self.error(start, self.pos, "integer literal out of range".to_string());
        }
        Ok(if negative {
            (magnitude as i64).wrapping_neg()
        } else {
            magnitude as i64
        })
    }

    fn parse_string(&mut self, quote: u8) -> Res<Vec<u8>> {
        let start = self.pos;
        self.pos += 1;
        let mut out = Vec::new();
        loop {
            match self.peek() {
                None | Some(b'\n') => {
                    return self.error(start, start + 1, "unterminated string".to_string());
                }
                Some(b) if b == quote => {
                    self.pos += 1;
                    return Ok(out);
                }
                Some(b'\\') => self.parse_escape(&mut out)?,
                Some(b) => {
                    out.push(b);
                    self.pos += 1;
                }
            }
        }
    }

    fn parse_escape(&mut self, out: &mut Vec<u8>) -> Res<()> {
        let start = self.pos;
        self.pos += 1;
        let Some(c) = self.peek() else {
            return self.error(start, start + 1, "unterminated string".to_string());
        };
        self.pos += 1;
        match c {
            b'\\' | b'"' | b'\'' => out.push(c),
            b'n' => out.push(b'\n'),
            b'r' => out.push(b'\r'),
            b't' => out.push(b'\t'),
            b'u' => {
                let hex = self.src.get(self.pos..self.pos + 4).unwrap_or(&[]);
                let code = std::str::from_utf8(hex)
                    .ok()
                    .filter(|h| h.bytes().all(|b| b.is_ascii_hexdigit()))
                    .and_then(|h| u32::from_str_radix(h, 16).ok())
                    .and_then(char::from_u32);
                let Some(ch) = code else {
                    return self.error(start, self.pos, "invalid \\u escape".to_string());
                };
                self.pos += 4;
                out.extend_from_slice(ch.to_string().as_bytes());
            }
            _ => {
                return self.error(start, self.pos, "unknown escape sequence".to_string());
            }
        }
        Ok(())
    }
}

/// Builds a binary node spanning both operands.
fn binary(left: Expr, right: Expr, make: impl FnOnce(Box<Expr>, Box<Expr>) -> ExprKind) -> Expr {
    Expr {
        span: Span {
            start: left.span.start,
            end: right.span.end,
        },
        kind: make(Box::new(left), Box::new(right)),
    }
}
