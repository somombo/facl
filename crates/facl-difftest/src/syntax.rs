use facl_core::{self as ast, CmpOp, Expr, ExprKind, PatSeg, Span};
use std::fmt::Write as _;

pub(crate) const SPAN: Span = Span { start: 0, end: 0 };
pub(crate) const METHODS: [&str; 7] = ["GET", "HEAD", "OPTIONS", "POST", "PUT", "PATCH", "DELETE"];
// The v0.3 text grammar's limit, independent of the parser under test.
pub(crate) const MATCH_DEPTH_LIMIT: usize = 64;

#[derive(Clone)]
pub(crate) struct Rules {
    pub service: String,
    pub blocks: Vec<Block>,
}

#[derive(Clone)]
pub(crate) struct Block {
    pub pattern: Vec<PatSeg>,
    pub body: Vec<Item>,
}

#[derive(Clone)]
pub(crate) enum Item {
    Match(Block),
    Allow(Allow),
}

#[derive(Clone)]
pub(crate) struct Allow {
    pub actions: Vec<String>,
    pub cond: Option<Expr>,
}

pub(crate) fn action_mask(action: &str) -> Option<u8> {
    match action.to_ascii_uppercase().as_str() {
        "READ" => Some(0b0000111),
        "WRITE" => Some(0b1111000),
        word => METHODS
            .iter()
            .position(|method| *method == word)
            .map(|i| 1 << i),
    }
}

pub(crate) fn text(bytes: &[u8]) -> &str {
    std::str::from_utf8(bytes).expect("facl syntax contains only UTF-8 strings")
}

pub(crate) fn cmp_op(op: &CmpOp) -> &'static str {
    match op {
        CmpOp::Eq => "==",
        CmpOp::Ne => "!=",
        CmpOp::Lt => "<",
        CmpOp::Le => "<=",
        CmpOp::Gt => ">",
        CmpOp::Ge => ">=",
    }
}

pub(crate) enum Parsed {
    Tree(ast::Service),
    Rejected(ParseRejection),
}

pub(crate) enum ParseRejection {
    UnknownAction(String),
    MatchDepth,
}

impl ParseRejection {
    pub(crate) fn kind(&self) -> &'static str {
        match self {
            Self::UnknownAction(_) => "unknownAction",
            Self::MatchDepth => "tooDeep",
        }
    }

    fn message(&self) -> String {
        match self {
            Self::UnknownAction(action) => format!("unknown action '{action}'"),
            Self::MatchDepth => format!("nested more than {MATCH_DEPTH_LIMIT} levels deep"),
        }
    }
}

impl Rules {
    pub(crate) fn from_parsed(service: ast::Service) -> Self {
        Self {
            service: text(&service.name).to_owned(),
            blocks: service
                .matches
                .into_iter()
                .map(Block::from_parsed)
                .collect(),
        }
    }

    pub(crate) fn print(&self) -> String {
        let mut buf = String::new();
        writeln!(buf, "service {} {{", self.service).unwrap();
        for block in &self.blocks {
            block.print(&mut buf, 1);
        }
        buf.push_str("}\n");
        buf
    }

    pub(crate) fn check_round_trip(&self, source: &str) -> Result<Parsed, String> {
        let expected = self
            .blocks
            .iter()
            .map(|block| block.expected(1))
            .collect::<Result<Vec<_>, _>>();
        match (expected, facl_syntax::parse(source)) {
            (Ok(blocks), Ok(mut actual)) => {
                let expected = ast::Service {
                    name: self.service.as_bytes().to_vec(),
                    matches: blocks,
                    span: SPAN,
                };
                actual.span = SPAN;
                for block in &mut actual.matches {
                    clear_block_spans(block);
                }
                if actual != expected {
                    return Err(format!(
                        "expected tree {expected:#?}\nparsed tree {actual:#?}"
                    ));
                }
                Ok(Parsed::Tree(actual))
            }
            (Err(expected), Err(err)) if err.message == expected.message() => {
                Ok(Parsed::Rejected(expected))
            }
            (_, Err(err)) => Err(format!("parser rejected the printed tree: {err:?}")),
            (Err(expected), Ok(_)) => Err(format!(
                "parser accepted a tree with {}",
                expected.message()
            )),
        }
    }
}

impl Block {
    fn from_parsed(block: ast::Match) -> Self {
        let body = block
            .body
            .into_iter()
            .map(|item| match item {
                ast::Item::Match(child) => Item::Match(Self::from_parsed(child)),
                ast::Item::Allow(allow) => Item::Allow(Allow {
                    actions: METHODS
                        .iter()
                        .enumerate()
                        .filter(|(i, _)| allow.methods & (1 << i) != 0)
                        .map(|(_, method)| (*method).to_owned())
                        .collect(),
                    cond: allow.cond,
                }),
            })
            .collect();
        Self {
            pattern: block.pattern,
            body,
        }
    }

    fn expected(&self, depth: usize) -> Result<ast::Match, ParseRejection> {
        if depth > MATCH_DEPTH_LIMIT {
            return Err(ParseRejection::MatchDepth);
        }
        let mut body = Vec::with_capacity(self.body.len());
        for item in &self.body {
            body.push(match item {
                Item::Match(child) => ast::Item::Match(child.expected(depth + 1)?),
                Item::Allow(allow) => {
                    let mut methods = 0;
                    for action in &allow.actions {
                        methods |= action_mask(action)
                            .ok_or_else(|| ParseRejection::UnknownAction(action.clone()))?;
                    }
                    let mut cond = allow.cond.clone();
                    if let Some(expr) = &mut cond {
                        clear_expr_spans(expr);
                    }
                    ast::Item::Allow(ast::Allow {
                        methods,
                        cond,
                        span: SPAN,
                    })
                }
            });
        }
        Ok(ast::Match {
            pattern: self.pattern.clone(),
            body,
            span: SPAN,
        })
    }

    fn print(&self, buf: &mut String, depth: usize) {
        let indent = "  ".repeat(depth);
        write!(buf, "{indent}match ").unwrap();
        if self.pattern.is_empty() {
            buf.push('/');
        }
        for seg in &self.pattern {
            buf.push('/');
            match seg {
                PatSeg::Lit(s) => buf.push_str(text(s)),
                PatSeg::Var(n) => write!(buf, "{{{}}}", text(n)).unwrap(),
                PatSeg::Rest(n) => write!(buf, "{{{}=**}}", text(n)).unwrap(),
            }
        }
        buf.push_str(" {\n");
        for item in &self.body {
            match item {
                Item::Match(child) => child.print(buf, depth + 1),
                Item::Allow(allow) => {
                    write!(buf, "{indent}  allow {}", allow.actions.join(", ")).unwrap();
                    if let Some(expr) = &allow.cond {
                        buf.push_str(": if ");
                        print_expr(buf, expr, 1);
                    }
                    buf.push_str(";\n");
                }
            }
        }
        writeln!(buf, "{indent}}}").unwrap();
    }
}

fn print_expr(buf: &mut String, expr: &Expr, min: u8) {
    let precedence = match expr.kind {
        ExprKind::Or(..) => 1,
        ExprKind::And(..) => 2,
        ExprKind::Cmp(..) | ExprKind::In(..) => 3,
        ExprKind::Not(..) => 4,
        ExprKind::Select(..) | ExprKind::Index(..) | ExprKind::Method(..) => 5,
        _ => 6,
    };
    if precedence < min {
        buf.push('(');
    }
    match &expr.kind {
        ExprKind::Null => buf.push_str("null"),
        ExprKind::Bool(b) => write!(buf, "{b}").unwrap(),
        ExprKind::Int(n) => write!(buf, "{n}").unwrap(),
        ExprKind::Str(s) => print_string(buf, text(s)),
        ExprKind::List(items) => {
            buf.push('[');
            print_args(buf, items);
            buf.push(']');
        }
        ExprKind::Ident(id) => buf.push_str(text(id)),
        ExprKind::Select(target, field) => {
            print_expr(buf, target, precedence);
            write!(buf, ".{}", text(field)).unwrap();
        }
        ExprKind::Index(target, key) => {
            print_expr(buf, target, precedence);
            buf.push('[');
            print_expr(buf, key, 1);
            buf.push(']');
        }
        ExprKind::Call(name, args) => {
            write!(buf, "{}(", text(name)).unwrap();
            print_args(buf, args);
            buf.push(')');
        }
        ExprKind::Method(target, name, args) => {
            print_expr(buf, target, precedence);
            write!(buf, ".{}(", text(name)).unwrap();
            print_args(buf, args);
            buf.push(')');
        }
        ExprKind::Not(arg) => {
            buf.push('!');
            print_expr(buf, arg, precedence);
        }
        ExprKind::And(l, r) => print_binary(buf, l, "&&", r, precedence),
        ExprKind::Or(l, r) => print_binary(buf, l, "||", r, precedence),
        ExprKind::Cmp(op, l, r) => print_binary(buf, l, cmp_op(op), r, precedence),
        ExprKind::In(l, r) => print_binary(buf, l, "in", r, precedence),
    }
    if precedence < min {
        buf.push(')');
    }
}

fn print_binary(buf: &mut String, left: &Expr, op: &str, right: &Expr, precedence: u8) {
    print_expr(buf, left, precedence);
    write!(buf, " {op} ").unwrap();
    print_expr(buf, right, precedence + 1);
}

fn print_args(buf: &mut String, args: &[Expr]) {
    for (i, arg) in args.iter().enumerate() {
        if i != 0 {
            buf.push_str(", ");
        }
        print_expr(buf, arg, 1);
    }
}

fn print_string(buf: &mut String, s: &str) {
    buf.push('"');
    for c in s.chars() {
        match c {
            '"' => buf.push_str("\\\""),
            '\\' => buf.push_str("\\\\"),
            '\n' => buf.push_str("\\n"),
            '\r' => buf.push_str("\\r"),
            '\t' => buf.push_str("\\t"),
            c if c.is_control() => write!(buf, "\\u{:04x}", u32::from(c)).unwrap(),
            c => buf.push(c),
        }
    }
    buf.push('"');
}

fn clear_block_spans(block: &mut ast::Match) {
    block.span = SPAN;
    for item in &mut block.body {
        match item {
            ast::Item::Match(child) => clear_block_spans(child),
            ast::Item::Allow(allow) => {
                allow.span = SPAN;
                if let Some(expr) = &mut allow.cond {
                    clear_expr_spans(expr);
                }
            }
        }
    }
}

fn clear_expr_spans(expr: &mut Expr) {
    expr.span = SPAN;
    match &mut expr.kind {
        ExprKind::Not(arg) | ExprKind::Select(arg, _) => clear_expr_spans(arg),
        ExprKind::Index(l, r)
        | ExprKind::And(l, r)
        | ExprKind::Or(l, r)
        | ExprKind::Cmp(_, l, r)
        | ExprKind::In(l, r) => {
            clear_expr_spans(l);
            clear_expr_spans(r);
        }
        ExprKind::List(args) | ExprKind::Call(_, args) => {
            args.iter_mut().for_each(clear_expr_spans);
        }
        ExprKind::Method(target, _, args) => {
            clear_expr_spans(target);
            args.iter_mut().for_each(clear_expr_spans);
        }
        ExprKind::Null
        | ExprKind::Bool(_)
        | ExprKind::Int(_)
        | ExprKind::Str(_)
        | ExprKind::Ident(_) => {}
    }
}
