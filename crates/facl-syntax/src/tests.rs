use super::*;
use facl_core::{CmpOp, Expr, ExprKind, Item, Match, PatSeg, Service};

fn parse_ok(src: &str) -> Service {
    match parse(src) {
        Ok(s) => s,
        Err(e) => panic!("parse failed: {e:?}"),
    }
}

/// Wraps a condition in a minimal file and returns its expression.
fn cond(expr: &str) -> Expr {
    let src = format!("service http {{ match /a {{ allow read: if {expr}; }} }}");
    let s = parse_ok(&src);
    match &s.matches[0].body[0] {
        Item::Allow(a) => a.cond.clone().expect("has a condition"),
        Item::Match(_) => panic!("expected an allow"),
    }
}

fn cond_err(expr: &str) -> String {
    let src = format!("service http {{ match /a {{ allow read: if {expr}; }} }}");
    parse(&src).expect_err("should fail").message
}

/// The error's `(line, column, message)`.
fn err_at(src: &str) -> (u32, u32, String) {
    let e = parse(src).expect_err("should fail");
    let (line, col) = line_col(src, e.span.start);
    (line, col, e.message)
}

fn pattern(p: &str) -> Vec<PatSeg> {
    let src = format!("service http {{ match {p} {{ }} }}");
    parse_ok(&src).matches[0].pattern.clone()
}

fn first_match(s: &Service) -> &Match {
    &s.matches[0]
}

fn b(s: &str) -> Vec<u8> {
    s.as_bytes().to_vec()
}

fn ident(e: &Expr) -> String {
    match &e.kind {
        ExprKind::Ident(n) => String::from_utf8(n.clone()).expect("utf8"),
        other => panic!("expected an identifier, got {other:?}"),
    }
}

#[test]
fn parses_the_design_example() {
    let src = std::fs::read_to_string(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../conformance/design-example.rules"
    ))
    .expect("example file");
    let s = parse_ok(&src);
    assert_eq!(s.name, b("http"));
    assert_eq!(s.matches.len(), 3);
    let users = first_match(&s);
    assert_eq!(
        users.pattern,
        vec![PatSeg::Lit(b("users")), PatSeg::Var(b("userId"))]
    );
    assert_eq!(users.body.len(), 3);
    assert!(matches!(users.body[2], Item::Match(_)));
}

#[test]
fn empty_service() {
    let s = parse_ok("service http {}");
    assert!(s.matches.is_empty());
    assert_eq!(s.span.start, 0);
    assert_eq!(s.span.end, 15);
}

#[test]
fn dotted_service_name() {
    let s = parse_ok("service https.cloudfunctions.net { }");
    assert_eq!(s.name, b("https.cloudfunctions.net"));
}

#[test]
fn comments_are_whitespace() {
    let s = parse_ok(
        "// leading\nservice /* inline */ http {\n  /* block\n comment */\n  match /a { } // trailing\n}\n// end",
    );
    assert_eq!(s.matches.len(), 1);
}

#[test]
fn patterns() {
    assert_eq!(pattern("/"), vec![]);
    assert_eq!(pattern("/a"), vec![PatSeg::Lit(b("a"))]);
    assert_eq!(
        pattern("/a/{b}/c"),
        vec![
            PatSeg::Lit(b("a")),
            PatSeg::Var(b("b")),
            PatSeg::Lit(b("c"))
        ]
    );
    assert_eq!(pattern("/{p=**}"), vec![PatSeg::Rest(b("p"))]);
    assert_eq!(
        pattern("/a/{ p = ** }"),
        vec![PatSeg::Lit(b("a")), PatSeg::Rest(b("p"))]
    );
    assert_eq!(
        pattern("/v1.0/my-file_x~y"),
        vec![PatSeg::Lit(b("v1.0")), PatSeg::Lit(b("my-file_x~y"))]
    );
    assert_eq!(pattern("/123"), vec![PatSeg::Lit(b("123"))]);
}

#[test]
fn a_pattern_ends_at_the_first_character_that_is_not_a_slash() {
    let s = parse_ok("service http { match /a/{b}{ allow read; } }");
    assert_eq!(first_match(&s).pattern.len(), 2);
    assert_eq!(first_match(&s).body.len(), 1);
}

#[test]
fn pattern_errors() {
    assert_eq!(
        err_at("service http { match a { } }").2,
        "expected a path pattern starting with '/', found 'a'"
    );
    assert!(
        err_at("service http { match /a/ { } }")
            .2
            .starts_with("expected a path segment after '/'")
    );
    assert!(
        err_at("service http { match /a//b { } }")
            .2
            .starts_with("expected a path segment after '/'")
    );
    assert!(
        err_at("service http { match /. { } }")
            .2
            .contains("not valid segments")
    );
    assert!(
        err_at("service http { match /a/.. { } }")
            .2
            .contains("not valid segments")
    );
    assert!(
        err_at("service http { match /{a=*} { } }")
            .2
            .starts_with("expected '**'")
    );
    assert!(
        err_at("service http { match /{} { } }")
            .2
            .starts_with("expected a name")
    );
    assert!(
        err_at("service http { match /{in} { } }")
            .2
            .contains("reserved word")
    );
    assert!(
        err_at("service http { match /{a b} { } }")
            .2
            .starts_with("expected '}'")
    );
}

#[test]
fn actions_and_method_bits() {
    let bits = |actions: &str| {
        let s = parse_ok(&format!(
            "service http {{ match / {{ allow {actions}; }} }}"
        ));
        match &first_match(&s).body[0] {
            Item::Allow(a) => a.methods,
            Item::Match(_) => panic!("expected an allow"),
        }
    };
    assert_eq!(bits("get"), 1);
    assert_eq!(bits("head"), 2);
    assert_eq!(bits("options"), 4);
    assert_eq!(bits("post"), 8);
    assert_eq!(bits("put"), 16);
    assert_eq!(bits("patch"), 32);
    assert_eq!(bits("delete"), 64);
    assert_eq!(bits("read"), 7);
    assert_eq!(bits("write"), 120);
    assert_eq!(bits("get, head"), 3);
    assert_eq!(bits("read, write"), 127);
    assert_eq!(bits("GET, Post , DELETE"), 73);
    assert_eq!(bits("read, get"), 7);
}

#[test]
fn allow_without_a_condition() {
    let s = parse_ok("service http { match / { allow read; } }");
    match &first_match(&s).body[0] {
        Item::Allow(a) => assert!(a.cond.is_none()),
        Item::Match(_) => panic!("expected an allow"),
    }
}

#[test]
fn allow_errors() {
    assert_eq!(
        err_at("service http { match / { allow fetch; } }").2,
        "unknown action 'fetch'"
    );
    assert!(
        err_at("service http { match / { allow ; } }")
            .2
            .starts_with("expected a name")
    );
    assert!(
        err_at("service http { match / { allow read } }")
            .2
            .starts_with("expected ';'")
    );
    assert!(
        err_at("service http { match / { allow read: true; } }")
            .2
            .starts_with("expected 'if'")
    );
    assert!(
        err_at("service http { match / { allow read: if ; } }")
            .2
            .starts_with("expected an expression")
    );
    assert!(
        err_at("service http { match / { allow read, ; } }")
            .2
            .starts_with("expected a name")
    );
}

#[test]
fn nested_matches_keep_source_order() {
    let s = parse_ok("service http { match /a { match /b { } allow read; match /c { } } }");
    let kinds: Vec<bool> = first_match(&s)
        .body
        .iter()
        .map(|i| matches!(i, Item::Match(_)))
        .collect();
    assert_eq!(kinds, vec![true, false, true]);
}

#[test]
fn literals() {
    assert_eq!(cond("null").kind, ExprKind::Null);
    assert_eq!(cond("true").kind, ExprKind::Bool(true));
    assert_eq!(cond("false").kind, ExprKind::Bool(false));
    assert_eq!(cond("42").kind, ExprKind::Int(42));
    assert_eq!(cond("007").kind, ExprKind::Int(7));
    assert_eq!(cond("-5").kind, ExprKind::Int(-5));
    assert_eq!(cond("- 5").kind, ExprKind::Int(-5));
    assert_eq!(cond("9223372036854775807").kind, ExprKind::Int(i64::MAX));
    assert_eq!(cond("-9223372036854775808").kind, ExprKind::Int(i64::MIN));
}

#[test]
fn integer_range_errors() {
    assert!(cond_err("9223372036854775808").contains("out of range"));
    assert!(cond_err("-9223372036854775809").contains("out of range"));
    assert!(cond_err("99999999999999999999999").contains("out of range"));
    assert_eq!(cond_err("12abc"), "invalid number");
    assert!(cond_err("-").starts_with("expected an integer"));
    assert!(cond_err("1.5").starts_with("expected a name"));
}

#[test]
fn strings_and_escapes() {
    assert_eq!(cond(r#""abc""#).kind, ExprKind::Str(b("abc")));
    assert_eq!(cond("'abc'").kind, ExprKind::Str(b("abc")));
    assert_eq!(cond(r#""a'b""#).kind, ExprKind::Str(b("a'b")));
    assert_eq!(cond(r#"'a"b'"#).kind, ExprKind::Str(b("a\"b")));
    assert_eq!(
        cond(r#""\\ \" \' \n \r \t""#).kind,
        ExprKind::Str(b("\\ \" ' \n \r \t"))
    );
    assert_eq!(
        cond(r#""é""#).kind,
        ExprKind::Str("\u{e9}".as_bytes().to_vec())
    );
    assert_eq!(
        cond(r#""€""#).kind,
        ExprKind::Str("\u{20ac}".as_bytes().to_vec())
    );
    assert_eq!(
        cond("\"\u{1F600}\"").kind,
        ExprKind::Str("\u{1F600}".as_bytes().to_vec())
    );
    assert_eq!(cond(r#""""#).kind, ExprKind::Str(vec![]));
}

#[test]
fn string_errors() {
    assert_eq!(cond_err(r#""abc"#), "unterminated string");
    assert_eq!(cond_err("\"a\nb\""), "unterminated string");
    assert_eq!(cond_err(r#""\q""#), "unknown escape sequence");
    assert_eq!(cond_err(r#""\u12""#), "invalid \\u escape");
    assert_eq!(cond_err(r#""\uD800""#), "invalid \\u escape");
    assert_eq!(cond_err(r#""\uZZZZ""#), "invalid \\u escape");
}

#[test]
fn identifiers_selects_and_indexes() {
    assert_eq!(cond("request").kind, ExprKind::Ident(b("request")));
    let ExprKind::Select(inner, name) = cond("request.auth").kind else {
        panic!("select")
    };
    assert_eq!(ident(&inner), "request");
    assert_eq!(name, b("auth"));
    let ExprKind::Index(target, key) = cond("a[0]").kind else {
        panic!("index")
    };
    assert_eq!(ident(&target), "a");
    assert_eq!(key.kind, ExprKind::Int(0));
    let ExprKind::Select(inner, _) = cond("a.b[1].c").kind else {
        panic!("select")
    };
    assert!(matches!(inner.kind, ExprKind::Index(..)));
}

#[test]
fn calls_and_methods() {
    let ExprKind::Call(name, args) = cond("size(a)").kind else {
        panic!("call")
    };
    assert_eq!(name, b("size"));
    assert_eq!(args.len(), 1);
    let ExprKind::Call(_, args) = cond("f()").kind else {
        panic!("call")
    };
    assert!(args.is_empty());
    let ExprKind::Call(_, args) = cond("f(1, 2, 3)").kind else {
        panic!("call")
    };
    assert_eq!(args.len(), 3);
    let ExprKind::Method(target, name, args) = cond("a.startsWith('x')").kind else {
        panic!("method")
    };
    assert_eq!(ident(&target), "a");
    assert_eq!(name, b("startsWith"));
    assert_eq!(args.len(), 1);
    let ExprKind::Method(_, name, args) = cond("request.auth.uid.size()").kind else {
        panic!("method")
    };
    assert_eq!(name, b("size"));
    assert!(args.is_empty());
    assert!(matches!(cond("has(a.b)").kind, ExprKind::Call(..)));
}

#[test]
fn list_literals() {
    assert_eq!(cond("[]").kind, ExprKind::List(vec![]));
    let ExprKind::List(items) = cond("[1, 'a', [2]]").kind else {
        panic!("list")
    };
    assert_eq!(items.len(), 3);
    assert!(cond_err("[1,]").starts_with("expected an expression"));
    assert!(cond_err("[1").starts_with("expected ']'"));
}

#[test]
fn operators_and_precedence() {
    // && binds tighter than ||.
    let ExprKind::Or(l, r) = cond("a || b && c").kind else {
        panic!("or")
    };
    assert_eq!(ident(&l), "a");
    assert!(matches!(r.kind, ExprKind::And(..)));
    // Comparisons bind tighter than &&.
    let ExprKind::And(l, r) = cond("a == 1 && b != 2").kind else {
        panic!("and")
    };
    assert!(matches!(l.kind, ExprKind::Cmp(CmpOp::Eq, ..)));
    assert!(matches!(r.kind, ExprKind::Cmp(CmpOp::Ne, ..)));
    // ! binds tighter than comparison.
    let ExprKind::Cmp(_, l, _) = cond("!a == b").kind else {
        panic!("cmp")
    };
    assert!(matches!(l.kind, ExprKind::Not(_)));
    // Left associativity.
    let ExprKind::Or(l, r) = cond("a || b || c").kind else {
        panic!("or")
    };
    assert!(matches!(l.kind, ExprKind::Or(..)));
    assert_eq!(ident(&r), "c");
    // Parentheses override.
    let ExprKind::And(l, _) = cond("(a || b) && c").kind else {
        panic!("and")
    };
    assert!(matches!(l.kind, ExprKind::Or(..)));
}

#[test]
fn every_comparison_operator() {
    let op = |text: &str| match cond(&format!("a {text} b")).kind {
        ExprKind::Cmp(op, ..) => op,
        other => panic!("expected a comparison, got {other:?}"),
    };
    assert_eq!(op("=="), CmpOp::Eq);
    assert_eq!(op("!="), CmpOp::Ne);
    assert_eq!(op("<"), CmpOp::Lt);
    assert_eq!(op("<="), CmpOp::Le);
    assert_eq!(op(">"), CmpOp::Gt);
    assert_eq!(op(">="), CmpOp::Ge);
    assert!(matches!(cond("a in b").kind, ExprKind::In(..)));
}

#[test]
fn in_needs_a_word_boundary() {
    // `index` is a name, not `in` followed by `dex`.
    assert!(cond_err("a index").starts_with("expected ';'"));
    assert!(matches!(cond("a in[1]").kind, ExprKind::In(..)));
}

#[test]
fn negation() {
    let ExprKind::Not(inner) = cond("!!a").kind else {
        panic!("not")
    };
    assert!(matches!(inner.kind, ExprKind::Not(_)));
    assert!(matches!(cond("!(a && b)").kind, ExprKind::Not(_)));
    assert!(matches!(cond("! a").kind, ExprKind::Not(_)));
}

#[test]
fn reserved_words_are_not_names() {
    for word in [
        "in",
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
    ] {
        let msg = cond_err(word);
        let reserved = msg.contains("reserved word") || msg.starts_with("expected an expression");
        assert!(reserved, "{word}: {msg}");
        assert!(
            cond_err(&format!("a.{word}")).contains("reserved word"),
            "{word}"
        );
    }
    assert_eq!(ident(&cond("trueish")), "trueish");
    assert_eq!(ident(&cond("nullable")), "nullable");
}

#[test]
fn spans_cover_the_text() {
    let src = "service http { match /a { allow read: if a && !b; } }";
    let s = parse_ok(src);
    let Item::Allow(a) = &first_match(&s).body[0] else {
        panic!("allow")
    };
    let e = a.cond.as_ref().expect("cond");
    assert_eq!(&src[e.span.start as usize..e.span.end as usize], "a && !b");
    assert_eq!(
        &src[a.span.start as usize..a.span.end as usize],
        "allow read: if a && !b;"
    );
    let m = first_match(&s);
    assert_eq!(
        &src[m.span.start as usize..m.span.end as usize],
        "match /a { allow read: if a && !b; }"
    );
    let ExprKind::And(_, r) = &e.kind else {
        panic!("and")
    };
    assert_eq!(&src[r.span.start as usize..r.span.end as usize], "!b");
}

#[test]
fn nesting_limits() {
    let nested_parens = |n: usize| format!("{}1{}", "(".repeat(n), ")".repeat(n));
    assert!(
        parse(&format!(
            "service http {{ match /a {{ allow read: if {}; }} }}",
            nested_parens(63)
        ))
        .is_ok()
    );
    assert!(cond_err(&nested_parens(70)).contains("nested more than 64"));
    assert!(cond_err(&format!("{}a", "!".repeat(70))).contains("nested more than 64"));
    assert!(cond_err(&vec!["a"; 70].join(" || ")).contains("more than 64 operands"));
    assert!(cond_err(&format!("a{}", ".b".repeat(70))).contains("more than 64 operands"));
    let matches = |n: usize| {
        format!(
            "service http {{ {}{} }}",
            "match /a { ".repeat(n),
            "}".repeat(n)
        )
    };
    assert!(parse(&matches(64)).is_ok());
    // A condition has its own budget, however deep its match is.
    let deep_allow = format!(
        "service http {{ {}allow read: if {};{} }}",
        "match /a { ".repeat(64),
        nested_parens(63),
        " }".repeat(64)
    );
    assert!(parse(&deep_allow).is_ok());
    assert!(
        parse(&matches(65))
            .expect_err("too deep")
            .message
            .contains("nested more than 64")
    );
}

#[test]
fn error_positions_are_one_based_lines_and_columns() {
    // The unknown action starts at line 3, column 9.
    let src = "service http {\n  match /a {\n    allow fetch;\n  }\n}\n";
    let (line, col, msg) = err_at(src);
    assert_eq!((line, col), (3, 11));
    assert_eq!(msg, "unknown action 'fetch'");

    let (line, col, _) = err_at("service http {\n  match /a {\n    allow read: if a &&;\n  }\n}");
    assert_eq!((line, col), (3, 24));

    // Missing closing brace reports the end of input.
    let (line, col, msg) = err_at("service http {\n  match /a {\n  }\n");
    assert_eq!((line, col), (4, 1));
    assert!(msg.contains("end of input"), "{msg}");
}

#[test]
fn columns_count_characters_not_bytes() {
    // The unknown action follows a two-byte character in a comment.
    let src = "service http { match /a { /* \u{e9}\u{e9} */ allow x; } }";
    let (line, col, _) = err_at(src);
    assert_eq!(line, 1);
    assert_eq!(
        col as usize,
        "service http { match /a { /* \u{e9}\u{e9} */ allow "
            .chars()
            .count()
            + 1
    );
}

#[test]
fn line_col_edge_cases() {
    assert_eq!(line_col("", 0), (1, 1));
    assert_eq!(line_col("abc", 0), (1, 1));
    assert_eq!(line_col("abc", 2), (1, 3));
    assert_eq!(line_col("abc", 3), (1, 4));
    assert_eq!(line_col("abc", 99), (1, 4));
    assert_eq!(line_col("a\nbc", 2), (2, 1));
    assert_eq!(line_col("a\nbc", 3), (2, 2));
    assert_eq!(line_col("a\r\nb", 3), (2, 1));
    assert_eq!(line_col("\u{e9}x", 2), (1, 2));
}

#[test]
fn structural_errors() {
    assert!(
        parse("")
            .expect_err("empty")
            .message
            .starts_with("expected 'service'")
    );
    assert!(
        parse("   // only a comment")
            .expect_err("empty")
            .message
            .starts_with("expected 'service'")
    );
    assert!(err_at("service { }").2.starts_with("expected a name"));
    assert!(err_at("service http").2.starts_with("expected '{'"));
    assert!(
        err_at("service http { allow read; }")
            .2
            .starts_with("expected 'match' or '}'")
    );
    assert!(
        err_at("service http { match /a { foo } }")
            .2
            .starts_with("expected 'match', 'allow' or '}'")
    );
    assert_eq!(
        err_at("service http { } extra").2,
        "unexpected content after the service block"
    );
    assert_eq!(
        err_at("service http { } }").2,
        "unexpected content after the service block"
    );
    assert_eq!(err_at("service http { /* open").2, "unterminated comment");
    assert!(
        err_at("service http { match /a { allow read: if a $ b; } }")
            .2
            .starts_with("expected ';'")
    );
}

#[test]
fn bad_input_never_panics() {
    // Cut the example off at every byte, and at every character boundary
    // inside a multibyte string, to catch indexing mistakes.
    let src = "service http { match /a/{b=**} { allow read, write: if !(a[0] in [1, 'x\u{e9}']) && size(b) >= -3; } }";
    let mut i = 0;
    while i <= src.len() {
        if src.is_char_boundary(i) {
            let _ = parse(&src[..i]);
        }
        i += 1;
    }
}
