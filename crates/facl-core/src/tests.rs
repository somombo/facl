//! Unit tests for the engine. Tests may use `std`; the engine itself does not.

use crate::*;
use alloc::boxed::Box;
use alloc::vec;
use alloc::vec::Vec;

fn bytes(s: &str) -> Vec<u8> {
    s.as_bytes().to_vec()
}

fn st(s: &str) -> Value {
    Value::Str(bytes(s))
}

fn map(entries: &[(&str, Value)]) -> Value {
    Value::Map(entries.iter().map(|(k, v)| (bytes(k), v.clone())).collect())
}

fn segs(parts: &[&str]) -> Vec<Vec<u8>> {
    parts.iter().map(|p| bytes(p)).collect()
}

mod canonicalize_tests {
    use super::*;

    fn ok(raw: &str) -> Vec<Vec<u8>> {
        canonicalize(raw.as_bytes()).expect("should canonicalize")
    }

    fn err(raw: &[u8]) -> PathError {
        canonicalize(raw).expect_err("should be rejected")
    }

    #[test]
    fn splits_segments() {
        assert_eq!(ok("/a/b/c"), segs(&["a", "b", "c"]));
    }

    #[test]
    fn root_has_zero_segments() {
        assert_eq!(ok("/"), Vec::<Vec<u8>>::new());
    }

    #[test]
    fn rejects_empty_segments() {
        for raw in ["//", "///", "//a", "/a//b", "/a/", "/a/b/", "/a///"] {
            assert_eq!(
                canonicalize(raw.as_bytes()),
                Err(PathError::EmptySegment),
                "{raw}"
            );
        }
    }

    #[test]
    fn decodes_each_segment_once() {
        assert_eq!(ok("/%61/%2561"), segs(&["a", "%61"]));
        assert_eq!(ok("/%c3%A9"), segs(&["\u{e9}"]));
    }

    #[test]
    fn keeps_non_ascii_bytes() {
        assert_eq!(ok("/\u{e9}"), segs(&["\u{e9}"]));
    }

    #[test]
    fn requires_a_leading_slash() {
        assert_eq!(err(b""), PathError::NoLeadingSlash);
        assert_eq!(err(b"a/b"), PathError::NoLeadingSlash);
    }

    #[test]
    fn rejects_query_and_fragment() {
        assert_eq!(err(b"/a?x"), PathError::QueryOrFragment);
        assert_eq!(err(b"/a#x"), PathError::QueryOrFragment);
    }

    #[test]
    fn rejects_dot_segments_raw_and_encoded() {
        for raw in ["/.", "/..", "/a/../b", "/%2e", "/%2E%2e", "/.%2e"] {
            assert_eq!(err(raw.as_bytes()), PathError::DotSegment, "{raw}");
        }
    }

    #[test]
    fn accepts_dots_inside_names() {
        assert_eq!(ok("/..a/a../.a"), segs(&["..a", "a..", ".a"]));
    }

    #[test]
    fn rejects_slash_and_nul() {
        assert_eq!(err(b"/a%2Fb"), PathError::ForbiddenByte);
        assert_eq!(err(b"/a%2fb"), PathError::ForbiddenByte);
        assert_eq!(err(b"/a%00"), PathError::ForbiddenByte);
    }

    #[test]
    fn rejects_bad_percent_encoding() {
        for raw in ["/%", "/%4", "/%zz", "/a%g0", "/%0"] {
            assert_eq!(err(raw.as_bytes()), PathError::BadPercentEncoding, "{raw}");
        }
    }

    #[test]
    fn rejects_invalid_utf8() {
        for raw in [
            "/%FF",
            "/%C3",
            "/%C0%AF",
            "/%E0%80%80",
            "/%ED%A0%80",
            "/%F4%90%80%80",
            "/%80",
            "/%C3%28",
            "/%F0%9F%98",
        ] {
            assert_eq!(err(raw.as_bytes()), PathError::InvalidUtf8, "{raw}");
        }
        assert_eq!(err(&[b'/', 0xFF]), PathError::InvalidUtf8);
    }

    #[test]
    fn accepts_valid_multibyte_utf8() {
        assert_eq!(ok("/%F0%9F%98%80"), segs(&["\u{1F600}"]));
        assert_eq!(ok("/%E2%82%AC"), segs(&["\u{20AC}"]));
        assert_eq!(ok("/%F4%8F%BF%BF"), segs(&["\u{10FFFF}"]));
    }
}

mod match_pattern_tests {
    use super::*;

    fn one(s: &str) -> Capture {
        Capture::One(bytes(s))
    }

    fn pat(parts: &[Option<&str>], rest: bool) -> Pattern {
        Pattern {
            segs: parts
                .iter()
                .map(|p| match p {
                    Some(l) => Seg::Lit(bytes(l)),
                    None => Seg::Var,
                })
                .collect(),
            rest,
        }
    }

    #[test]
    fn literal_must_match_exactly() {
        let p = pat(&[Some("a"), Some("b")], false);
        assert_eq!(match_pattern(&p, &segs(&["a", "b"])), Some(vec![]));
        assert_eq!(match_pattern(&p, &segs(&["a", "B"])), None);
        assert_eq!(match_pattern(&p, &segs(&["a"])), None);
        assert_eq!(match_pattern(&p, &segs(&["a", "b", "c"])), None);
    }

    #[test]
    fn vars_capture_in_order() {
        let p = pat(&[Some("u"), None, Some("p"), None], false);
        let caps = match_pattern(&p, &segs(&["u", "x", "p", "y"]));
        assert_eq!(caps, Some(vec![one("x"), one("y")]));
    }

    #[test]
    fn empty_pattern_matches_only_the_root() {
        let p = pat(&[], false);
        assert_eq!(match_pattern(&p, &segs(&[])), Some(vec![]));
        assert_eq!(match_pattern(&p, &segs(&["a"])), None);
    }

    #[test]
    fn rest_matches_zero_segments() {
        let p = pat(&[Some("f")], true);
        assert_eq!(
            match_pattern(&p, &segs(&["f"])),
            Some(vec![Capture::Rest(vec![])])
        );
    }

    #[test]
    fn rest_binds_a_list_after_the_vars() {
        let p = pat(&[Some("f"), None], true);
        let caps = match_pattern(&p, &segs(&["f", "u", "a", "b.txt"]));
        let tail = Capture::Rest(segs(&["a", "b.txt"]));
        assert_eq!(caps, Some(vec![one("u"), tail]));
    }

    #[test]
    fn rest_needs_the_prefix() {
        let p = pat(&[Some("f"), None], true);
        assert_eq!(match_pattern(&p, &segs(&["f"])), None);
        assert_eq!(match_pattern(&p, &segs(&["g", "u"])), None);
    }

    #[test]
    fn root_with_rest_matches_everything() {
        let p = pat(&[], true);
        assert_eq!(
            match_pattern(&p, &segs(&[])),
            Some(vec![Capture::Rest(vec![])])
        );
        let caps = match_pattern(&p, &segs(&["a"]));
        assert_eq!(caps, Some(vec![Capture::Rest(segs(&["a"]))]));
    }
}

mod value_tests {
    use super::*;

    #[test]
    fn equality_is_structural_and_typed() {
        assert!(value_eq(&Value::Null, &Value::Null));
        assert!(value_eq(&Value::Int(1), &Value::Int(1)));
        assert!(!value_eq(&Value::Int(1), &st("1")));
        assert!(!value_eq(&Value::Bool(false), &Value::Null));
        assert!(value_eq(&st("a"), &st("a")));
        assert!(!value_eq(&st("a"), &st("ab")));
    }

    #[test]
    fn map_equality_ignores_order() {
        let a = map(&[("x", Value::Int(1)), ("y", Value::List(vec![Value::Null]))]);
        let b = map(&[("y", Value::List(vec![Value::Null])), ("x", Value::Int(1))]);
        assert!(value_eq(&a, &b));
        assert!(!value_eq(&a, &map(&[("x", Value::Int(1))])));
        assert!(!value_eq(
            &a,
            &map(&[("x", Value::Int(1)), ("z", Value::Null)])
        ));
        assert!(!value_eq(
            &map(&[("x", Value::Int(1))]),
            &map(&[("x", Value::Int(2))])
        ));
    }

    #[test]
    fn list_equality_respects_order() {
        let a = Value::List(vec![Value::Int(1), Value::Int(2)]);
        let b = Value::List(vec![Value::Int(2), Value::Int(1)]);
        assert!(value_eq(&a, &a.clone()));
        assert!(!value_eq(&a, &b));
    }

    #[test]
    fn bytes_eq_works() {
        assert!(bytes_eq(b"abc", b"abc"));
        assert!(!bytes_eq(b"abc", b"abd"));
        assert!(!bytes_eq(b"abc", b"ab"));
        assert!(bytes_eq(b"", b""));
    }
}

mod eval_tests {
    use super::*;

    struct TestHost(Result<bool, EvalError>);

    impl Host for TestHost {
        fn request_is(&self, _request: &Value, media: &[u8]) -> Result<bool, EvalError> {
            if media == b"boom" {
                return Err(EvalError::Host);
            }
            self.0.clone()
        }
    }

    fn with_env<T>(f: impl FnOnce(&Env) -> T) -> T {
        let request = map(&[
            ("method", st("GET")),
            ("auth", map(&[("uid", st("u1"))])),
            ("none", Value::Null),
        ]);
        let context = map(&[("n", Value::Int(7)), ("t", Value::Bool(true))]);
        f(&Env {
            slots: vec![st("slot0"), Value::List(vec![st("a"), st("b")])],
            request: &request,
            context: &context,
        })
    }

    fn run(e: &CExpr) -> Result<Value, EvalError> {
        with_env(|env| eval(e, env, &TestHost(Ok(true))))
    }

    fn lit(v: Value) -> CExpr {
        CExpr::Lit(v)
    }

    fn int(n: i64) -> CExpr {
        lit(Value::Int(n))
    }

    fn string(s: &str) -> CExpr {
        lit(st(s))
    }

    fn truth(b: bool) -> CExpr {
        lit(Value::Bool(b))
    }

    fn bx(e: CExpr) -> Box<CExpr> {
        Box::new(e)
    }

    fn sel(e: CExpr, k: &str) -> CExpr {
        CExpr::Select(bx(e), bytes(k))
    }

    fn cmp(op: CmpOp, a: CExpr, b: CExpr) -> CExpr {
        CExpr::Cmp(op, bx(a), bx(b))
    }

    fn and(a: CExpr, b: CExpr) -> CExpr {
        CExpr::And(bx(a), bx(b))
    }

    fn or(a: CExpr, b: CExpr) -> CExpr {
        CExpr::Or(bx(a), bx(b))
    }

    /// An expression that fails with `NoSuchKey`.
    fn error() -> CExpr {
        sel(CExpr::Context, "missing")
    }

    #[test]
    fn literals_slots_and_roots() {
        assert_eq!(run(&int(3)), Ok(Value::Int(3)));
        assert_eq!(run(&CExpr::Slot(0)), Ok(st("slot0")));
        assert_eq!(run(&CExpr::Slot(2)), Err(EvalError::BadArgument));
        assert_eq!(run(&sel(CExpr::Context, "n")), Ok(Value::Int(7)));
        assert!(run(&CExpr::Request).is_ok());
    }

    #[test]
    fn list_literal_propagates_errors() {
        let ok = CExpr::List(vec![int(1), string("a")]);
        assert_eq!(run(&ok), Ok(Value::List(vec![Value::Int(1), st("a")])));
        assert_eq!(
            run(&CExpr::List(vec![int(1), error()])),
            Err(EvalError::NoSuchKey)
        );
        assert_eq!(run(&CExpr::List(vec![])), Ok(Value::List(vec![])));
    }

    #[test]
    fn select() {
        assert_eq!(run(&sel(sel(CExpr::Request, "auth"), "uid")), Ok(st("u1")));
        assert_eq!(run(&sel(CExpr::Request, "nope")), Err(EvalError::NoSuchKey));
        // Null has no fields, and neither does any other non-map.
        assert_eq!(
            run(&sel(sel(CExpr::Request, "none"), "x")),
            Err(EvalError::TypeMismatch)
        );
        assert_eq!(run(&sel(int(1), "x")), Err(EvalError::TypeMismatch));
        assert_eq!(run(&sel(string("s"), "x")), Err(EvalError::TypeMismatch));
    }

    #[test]
    fn index() {
        let at = |list: CExpr, i: CExpr| CExpr::Index(bx(list), bx(i));
        assert_eq!(run(&at(CExpr::Slot(1), int(0))), Ok(st("a")));
        assert_eq!(run(&at(CExpr::Slot(1), int(1))), Ok(st("b")));
        assert_eq!(
            run(&at(CExpr::Slot(1), int(2))),
            Err(EvalError::IndexOutOfRange)
        );
        assert_eq!(
            run(&at(CExpr::Slot(1), int(-1))),
            Err(EvalError::IndexOutOfRange)
        );
        assert_eq!(
            run(&at(CExpr::Slot(1), int(i64::MAX))),
            Err(EvalError::IndexOutOfRange)
        );
        assert_eq!(
            run(&at(CExpr::Slot(1), int(i64::MIN))),
            Err(EvalError::IndexOutOfRange)
        );
        assert_eq!(
            run(&at(CExpr::Slot(1), string("a"))),
            Err(EvalError::TypeMismatch)
        );
        assert_eq!(run(&at(CExpr::Context, string("n"))), Ok(Value::Int(7)));
        assert_eq!(
            run(&at(CExpr::Context, string("z"))),
            Err(EvalError::NoSuchKey)
        );
        assert_eq!(
            run(&at(CExpr::Context, int(0))),
            Err(EvalError::TypeMismatch)
        );
        assert_eq!(
            run(&at(string("abc"), int(0))),
            Err(EvalError::TypeMismatch)
        );
    }

    #[test]
    fn has() {
        let has = |e: CExpr, k: &str| CExpr::Has(bx(e), bytes(k));
        assert_eq!(run(&has(CExpr::Context, "n")), Ok(Value::Bool(true)));
        assert_eq!(run(&has(CExpr::Context, "z")), Ok(Value::Bool(false)));
        assert_eq!(
            run(&has(sel(CExpr::Request, "none"), "x")),
            Err(EvalError::TypeMismatch)
        );
        assert_eq!(run(&has(int(1), "x")), Err(EvalError::TypeMismatch));
        assert_eq!(run(&has(error(), "x")), Err(EvalError::NoSuchKey));
    }

    #[test]
    fn size() {
        let size = |e: CExpr| CExpr::Size(bx(e));
        assert_eq!(run(&size(string(""))), Ok(Value::Int(0)));
        assert_eq!(run(&size(string("abc"))), Ok(Value::Int(3)));
        // Code points, not bytes: two two-byte characters and one four-byte one.
        assert_eq!(
            run(&size(string("\u{e9}\u{e9}\u{1F600}"))),
            Ok(Value::Int(3))
        );
        assert_eq!(run(&size(CExpr::Slot(1))), Ok(Value::Int(2)));
        assert_eq!(run(&size(CExpr::Context)), Ok(Value::Int(2)));
        assert_eq!(run(&size(int(1))), Err(EvalError::TypeMismatch));
        assert_eq!(run(&size(lit(Value::Null))), Err(EvalError::TypeMismatch));
        assert_eq!(run(&size(truth(true))), Err(EvalError::TypeMismatch));
    }

    #[test]
    fn starts_and_ends_with() {
        let starts = |a: CExpr, b: CExpr| CExpr::StartsWith(bx(a), bx(b));
        let ends = |a: CExpr, b: CExpr| CExpr::EndsWith(bx(a), bx(b));
        assert_eq!(
            run(&starts(string("abc"), string("ab"))),
            Ok(Value::Bool(true))
        );
        assert_eq!(
            run(&starts(string("abc"), string(""))),
            Ok(Value::Bool(true))
        );
        assert_eq!(
            run(&starts(string("abc"), string("abc"))),
            Ok(Value::Bool(true))
        );
        assert_eq!(
            run(&starts(string("abc"), string("bc"))),
            Ok(Value::Bool(false))
        );
        assert_eq!(
            run(&starts(string("a"), string("ab"))),
            Ok(Value::Bool(false))
        );
        assert_eq!(
            run(&ends(string("abc"), string("bc"))),
            Ok(Value::Bool(true))
        );
        assert_eq!(run(&ends(string("abc"), string(""))), Ok(Value::Bool(true)));
        assert_eq!(
            run(&ends(string("abc"), string("ab"))),
            Ok(Value::Bool(false))
        );
        assert_eq!(
            run(&ends(string("c"), string("bc"))),
            Ok(Value::Bool(false))
        );
        assert_eq!(
            run(&starts(int(1), string("a"))),
            Err(EvalError::TypeMismatch)
        );
        assert_eq!(
            run(&ends(string("a"), int(1))),
            Err(EvalError::TypeMismatch)
        );
        assert_eq!(run(&starts(error(), int(1))), Err(EvalError::NoSuchKey));
    }

    #[test]
    fn request_is_calls_the_host() {
        let is = |arg: CExpr| CExpr::RequestIs(bx(arg));
        let yes = TestHost(Ok(true));
        let no = TestHost(Ok(false));
        assert_eq!(
            with_env(|env| eval(&is(string("json")), env, &yes)),
            Ok(Value::Bool(true))
        );
        assert_eq!(
            with_env(|env| eval(&is(string("json")), env, &no)),
            Ok(Value::Bool(false))
        );
        assert_eq!(
            with_env(|env| eval(&is(string("boom")), env, &yes)),
            Err(EvalError::Host)
        );
        assert_eq!(
            with_env(|env| eval(&is(int(1)), env, &yes)),
            Err(EvalError::TypeMismatch)
        );
        assert_eq!(
            with_env(|env| eval(&is(error()), env, &yes)),
            Err(EvalError::NoSuchKey)
        );
    }

    #[test]
    fn not() {
        let not = |e: CExpr| CExpr::Not(bx(e));
        assert_eq!(run(&not(truth(true))), Ok(Value::Bool(false)));
        assert_eq!(run(&not(truth(false))), Ok(Value::Bool(true)));
        assert_eq!(run(&not(int(1))), Err(EvalError::TypeMismatch));
        assert_eq!(run(&not(lit(Value::Null))), Err(EvalError::TypeMismatch));
        assert_eq!(run(&not(error())), Err(EvalError::NoSuchKey));
    }

    #[test]
    fn and_truth_table() {
        let t = || truth(true);
        let f = || truth(false);
        assert_eq!(run(&and(t(), t())), Ok(Value::Bool(true)));
        assert_eq!(run(&and(t(), f())), Ok(Value::Bool(false)));
        assert_eq!(run(&and(f(), t())), Ok(Value::Bool(false)));
        assert_eq!(run(&and(f(), f())), Ok(Value::Bool(false)));
    }

    #[test]
    fn and_error_semantics_are_commutative() {
        assert_eq!(run(&and(error(), truth(false))), Ok(Value::Bool(false)));
        assert_eq!(run(&and(truth(false), error())), Ok(Value::Bool(false)));
        assert_eq!(run(&and(error(), truth(true))), Err(EvalError::NoSuchKey));
        assert_eq!(run(&and(truth(true), error())), Err(EvalError::NoSuchKey));
        assert_eq!(run(&and(error(), error())), Err(EvalError::NoSuchKey));
        // When both fail, the left error wins.
        assert_eq!(run(&and(error(), int(1))), Err(EvalError::NoSuchKey));
        assert_eq!(run(&and(int(1), error())), Err(EvalError::TypeMismatch));
    }

    #[test]
    fn and_treats_non_booleans_as_errors() {
        assert_eq!(run(&and(int(1), truth(false))), Ok(Value::Bool(false)));
        assert_eq!(run(&and(truth(false), int(1))), Ok(Value::Bool(false)));
        assert_eq!(run(&and(int(1), truth(true))), Err(EvalError::TypeMismatch));
        assert_eq!(run(&and(truth(true), int(1))), Err(EvalError::TypeMismatch));
    }

    #[test]
    fn or_truth_table() {
        let t = || truth(true);
        let f = || truth(false);
        assert_eq!(run(&or(t(), t())), Ok(Value::Bool(true)));
        assert_eq!(run(&or(t(), f())), Ok(Value::Bool(true)));
        assert_eq!(run(&or(f(), t())), Ok(Value::Bool(true)));
        assert_eq!(run(&or(f(), f())), Ok(Value::Bool(false)));
    }

    #[test]
    fn or_error_semantics_are_commutative() {
        assert_eq!(run(&or(error(), truth(true))), Ok(Value::Bool(true)));
        assert_eq!(run(&or(truth(true), error())), Ok(Value::Bool(true)));
        assert_eq!(run(&or(error(), truth(false))), Err(EvalError::NoSuchKey));
        assert_eq!(run(&or(truth(false), error())), Err(EvalError::NoSuchKey));
        assert_eq!(run(&or(error(), error())), Err(EvalError::NoSuchKey));
        assert_eq!(run(&or(int(1), truth(true))), Ok(Value::Bool(true)));
        assert_eq!(run(&or(truth(false), int(1))), Err(EvalError::TypeMismatch));
    }

    #[test]
    fn short_circuit_skips_the_right_side_errors() {
        // The right side would not even be an error here, but it is not needed.
        assert_eq!(run(&and(truth(false), error())), Ok(Value::Bool(false)));
        assert_eq!(run(&or(truth(true), error())), Ok(Value::Bool(true)));
    }

    #[test]
    fn equality() {
        let eq = |a: CExpr, b: CExpr| cmp(CmpOp::Eq, a, b);
        let ne = |a: CExpr, b: CExpr| cmp(CmpOp::Ne, a, b);
        assert_eq!(run(&eq(int(1), int(1))), Ok(Value::Bool(true)));
        assert_eq!(run(&eq(int(1), int(2))), Ok(Value::Bool(false)));
        assert_eq!(run(&ne(int(1), int(2))), Ok(Value::Bool(true)));
        // Different types are unequal, not an error.
        assert_eq!(run(&eq(int(1), string("1"))), Ok(Value::Bool(false)));
        assert_eq!(run(&ne(int(1), string("1"))), Ok(Value::Bool(true)));
        assert_eq!(
            run(&eq(lit(Value::Null), lit(Value::Null))),
            Ok(Value::Bool(true))
        );
        assert_eq!(
            run(&eq(lit(Value::Null), truth(false))),
            Ok(Value::Bool(false))
        );
        // Errors propagate, left to right.
        assert_eq!(run(&eq(error(), int(1))), Err(EvalError::NoSuchKey));
        assert_eq!(run(&ne(int(1), error())), Err(EvalError::NoSuchKey));
        assert_eq!(
            run(&eq(sel(int(1), "a"), error())),
            Err(EvalError::TypeMismatch)
        );
    }

    #[test]
    fn ordering_ints_strings_and_bools() {
        let check = |op: CmpOp, a: CExpr, b: CExpr, want: bool| {
            assert_eq!(run(&cmp(op, a, b)), Ok(Value::Bool(want)));
        };
        check(CmpOp::Lt, int(1), int(2), true);
        check(CmpOp::Lt, int(2), int(2), false);
        check(CmpOp::Le, int(2), int(2), true);
        check(CmpOp::Gt, int(3), int(2), true);
        check(CmpOp::Gt, int(2), int(2), false);
        check(CmpOp::Ge, int(2), int(2), true);
        check(CmpOp::Ge, int(1), int(2), false);
        check(CmpOp::Lt, int(i64::MIN), int(i64::MAX), true);
        check(CmpOp::Lt, int(-1), int(0), true);
        check(CmpOp::Lt, string("a"), string("b"), true);
        check(CmpOp::Lt, string("a"), string("ab"), true);
        check(CmpOp::Lt, string("B"), string("a"), true);
        check(CmpOp::Gt, string("b"), string("abc"), true);
        check(CmpOp::Le, string(""), string(""), true);
        check(CmpOp::Lt, truth(false), truth(true), true);
        check(CmpOp::Lt, truth(true), truth(false), false);
        check(CmpOp::Ge, truth(true), truth(true), true);
    }

    #[test]
    fn ordering_other_operands_is_a_type_mismatch() {
        for op in [CmpOp::Lt, CmpOp::Le, CmpOp::Gt, CmpOp::Ge] {
            let bad = |a: CExpr, b: CExpr| {
                assert_eq!(run(&cmp(op.clone(), a, b)), Err(EvalError::TypeMismatch));
            };
            bad(int(1), string("1"));
            bad(lit(Value::Null), lit(Value::Null));
            bad(CExpr::Slot(1), CExpr::Slot(1));
            bad(CExpr::Context, CExpr::Context);
            bad(truth(true), int(1));
            assert_eq!(run(&cmp(op, error(), int(1))), Err(EvalError::NoSuchKey));
        }
    }

    #[test]
    fn membership() {
        let in_ = |a: CExpr, b: CExpr| CExpr::In(bx(a), bx(b));
        assert_eq!(
            run(&in_(string("a"), CExpr::Slot(1))),
            Ok(Value::Bool(true))
        );
        assert_eq!(
            run(&in_(string("z"), CExpr::Slot(1))),
            Ok(Value::Bool(false))
        );
        assert_eq!(run(&in_(int(1), CExpr::Slot(1))), Ok(Value::Bool(false)));
        assert_eq!(
            run(&in_(int(1), CExpr::List(vec![]))),
            Ok(Value::Bool(false))
        );
        assert_eq!(
            run(&in_(string("n"), CExpr::Context)),
            Ok(Value::Bool(true))
        );
        assert_eq!(
            run(&in_(string("z"), CExpr::Context)),
            Ok(Value::Bool(false))
        );
        assert_eq!(
            run(&in_(int(1), CExpr::Context)),
            Err(EvalError::TypeMismatch)
        );
        assert_eq!(
            run(&in_(string("a"), string("abc"))),
            Err(EvalError::TypeMismatch)
        );
        assert_eq!(run(&in_(string("a"), int(1))), Err(EvalError::TypeMismatch));
        assert_eq!(
            run(&in_(error(), CExpr::Slot(1))),
            Err(EvalError::NoSuchKey)
        );
        assert_eq!(run(&in_(int(1), error())), Err(EvalError::NoSuchKey));
    }

    #[test]
    fn deep_expression_does_not_overflow() {
        let mut e = truth(true);
        let mut i = 0;
        while i < MAX_DEPTH {
            e = CExpr::Not(bx(e));
            i += 1;
        }
        assert_eq!(run(&e), Ok(Value::Bool(true)));
    }
}

mod combine_tests {
    use super::*;

    #[test]
    fn empty_is_deny() {
        assert_eq!(combine(&[]), Verdict::Deny);
    }

    #[test]
    fn any_granted_allows() {
        assert_eq!(combine(&[Outcome::Granted]), Verdict::Allow);
        assert_eq!(combine(&[Outcome::NotGranted]), Verdict::Deny);
        assert_eq!(
            combine(&[Outcome::NotGranted, Outcome::Granted]),
            Verdict::Allow
        );
        assert_eq!(
            combine(&[Outcome::Granted, Outcome::NotGranted]),
            Verdict::Allow
        );
        assert_eq!(
            combine(&[Outcome::NotGranted, Outcome::NotGranted]),
            Verdict::Deny
        );
    }

    #[test]
    fn order_does_not_matter_and_extra_denials_never_revoke() {
        // Exhaustive over all outcome lists of length up to 6.
        let mut len = 0;
        while len <= 6 {
            let mut mask = 0u32;
            while mask < (1 << len) {
                let mut outs = Vec::new();
                let mut i = 0;
                while i < len {
                    outs.push(if mask & (1 << i) != 0 {
                        Outcome::Granted
                    } else {
                        Outcome::NotGranted
                    });
                    i += 1;
                }
                let expected = if mask != 0 {
                    Verdict::Allow
                } else {
                    Verdict::Deny
                };
                assert_eq!(combine(&outs), expected);
                outs.reverse();
                assert_eq!(combine(&outs), expected);
                outs.push(Outcome::NotGranted);
                assert_eq!(combine(&outs), expected);
                mask += 1;
            }
            len += 1;
        }
    }
}

mod decide_tests {
    use super::*;

    struct NoHost;

    impl Host for NoHost {
        fn request_is(&self, _: &Value, _: &[u8]) -> Result<bool, EvalError> {
            Err(EvalError::Host)
        }
    }

    fn rule(parts: &[Option<&str>], rest: bool, allows: Vec<(u8, CExpr)>) -> Rule {
        Rule {
            pattern: Pattern {
                segs: parts
                    .iter()
                    .map(|p| match p {
                        Some(l) => Seg::Lit(bytes(l)),
                        None => Seg::Var,
                    })
                    .collect(),
                rest,
            },
            allows: allows
                .into_iter()
                .map(|(methods, cond)| CompiledAllow { methods, cond })
                .collect(),
        }
    }

    fn req(method: &str, path: &[&str]) -> Request {
        Request {
            method: method_bit(method.as_bytes()),
            path: segs(path),
            request: map(&[("method", st(method))]),
            context: map(&[]),
        }
    }

    fn lit(b: bool) -> CExpr {
        CExpr::Lit(Value::Bool(b))
    }

    fn error() -> CExpr {
        CExpr::Select(Box::new(CExpr::Context), bytes("missing"))
    }

    fn deny(r: DenyReason) -> Decision {
        Decision::Deny(r)
    }

    #[test]
    fn method_bits() {
        let names = ["GET", "HEAD", "OPTIONS", "POST", "PUT", "PATCH", "DELETE"];
        let mut i = 0;
        while i < names.len() {
            assert_eq!(method_bit(names[i].as_bytes()), 1 << i, "{}", names[i]);
            i += 1;
        }
        for other in ["", "get", "Get", "TRACE", "CONNECT", "GET ", " GET", "GETS"] {
            assert_eq!(method_bit(other.as_bytes()), 0, "{other:?}");
        }
    }

    #[test]
    fn default_is_deny_with_no_matching_rule() {
        let empty = Policy { rules: vec![] };
        assert_eq!(
            decide(&empty, &req("GET", &["a"]), &NoHost),
            deny(DenyReason::NoMatchingRule)
        );
        let p = Policy {
            rules: vec![rule(&[Some("a")], false, vec![(7, lit(true))])],
        };
        assert_eq!(
            decide(&p, &req("GET", &["b"]), &NoHost),
            deny(DenyReason::NoMatchingRule)
        );
    }

    #[test]
    fn matching_rule_without_the_method() {
        let p = Policy {
            rules: vec![rule(&[Some("a")], false, vec![(7, lit(true))])],
        };
        assert_eq!(
            decide(&p, &req("POST", &["a"]), &NoHost),
            deny(DenyReason::NoAllowForMethod)
        );
        // An unknown method has bit 0 and is never granted.
        assert_eq!(
            decide(&p, &req("TRACE", &["a"]), &NoHost),
            deny(DenyReason::NoAllowForMethod)
        );
    }

    #[test]
    fn conditions_not_met() {
        let p = Policy {
            rules: vec![rule(&[Some("a")], false, vec![(7, lit(false))])],
        };
        assert_eq!(
            decide(&p, &req("GET", &["a"]), &NoHost),
            deny(DenyReason::ConditionsNotMet)
        );
    }

    #[test]
    fn errors_and_non_booleans_do_not_grant() {
        let p = Policy {
            rules: vec![rule(
                &[Some("a")],
                false,
                vec![
                    (7, error()),
                    (7, CExpr::Lit(Value::Int(1))),
                    (7, CExpr::Lit(st("true"))),
                ],
            )],
        };
        assert_eq!(
            decide(&p, &req("GET", &["a"]), &NoHost),
            deny(DenyReason::ConditionsNotMet)
        );
    }

    #[test]
    fn any_true_condition_allows_in_any_order() {
        let a = Policy {
            rules: vec![rule(
                &[Some("a")],
                false,
                vec![(7, error()), (1, lit(true))],
            )],
        };
        let b = Policy {
            rules: vec![rule(
                &[Some("a")],
                false,
                vec![(1, lit(true)), (7, error())],
            )],
        };
        assert_eq!(decide(&a, &req("GET", &["a"]), &NoHost), Decision::Allow);
        assert_eq!(decide(&b, &req("GET", &["a"]), &NoHost), Decision::Allow);
    }

    #[test]
    fn allows_across_rules_combine() {
        let p = Policy {
            rules: vec![
                rule(&[Some("a")], false, vec![(1, lit(false))]),
                rule(&[None], false, vec![(1, lit(true))]),
            ],
        };
        assert_eq!(decide(&p, &req("GET", &["a"]), &NoHost), Decision::Allow);
    }

    #[test]
    fn a_non_applicable_allow_is_not_evaluated() {
        // The POST allow would be an error, but a GET request never reaches it.
        let p = Policy {
            rules: vec![rule(
                &[Some("a")],
                false,
                vec![(8, error()), (1, lit(true))],
            )],
        };
        assert_eq!(decide(&p, &req("GET", &["a"]), &NoHost), Decision::Allow);
    }

    #[test]
    fn captures_are_visible_to_conditions() {
        let cond = CExpr::Cmp(
            CmpOp::Eq,
            Box::new(CExpr::Slot(0)),
            Box::new(CExpr::Lit(st("alice"))),
        );
        let p = Policy {
            rules: vec![rule(&[Some("u"), None], false, vec![(7, cond)])],
        };
        assert_eq!(
            decide(&p, &req("GET", &["u", "alice"]), &NoHost),
            Decision::Allow
        );
        assert_eq!(
            decide(&p, &req("GET", &["u", "bob"]), &NoHost),
            deny(DenyReason::ConditionsNotMet)
        );
    }

    #[test]
    fn rules_do_not_cascade() {
        let p = Policy {
            rules: vec![
                rule(&[Some("a")], false, vec![(7, lit(true))]),
                rule(&[Some("a"), Some("b")], false, vec![(8, lit(true))]),
            ],
        };
        assert_eq!(
            decide(&p, &req("GET", &["a", "b"]), &NoHost),
            deny(DenyReason::NoAllowForMethod)
        );
        assert_eq!(
            decide(&p, &req("POST", &["a", "b"]), &NoHost),
            Decision::Allow
        );
        assert_eq!(
            decide(&p, &req("POST", &["a"]), &NoHost),
            deny(DenyReason::NoAllowForMethod)
        );
    }

    #[test]
    fn bound_rest_is_a_list() {
        let size = CExpr::Size(Box::new(CExpr::Slot(0)));
        let cond = CExpr::Cmp(
            CmpOp::Eq,
            Box::new(size),
            Box::new(CExpr::Lit(Value::Int(2))),
        );
        let p = Policy {
            rules: vec![rule(&[Some("f")], true, vec![(7, cond)])],
        };
        assert_eq!(
            decide(&p, &req("GET", &["f", "x", "y"]), &NoHost),
            Decision::Allow
        );
        assert_eq!(
            decide(&p, &req("GET", &["f"]), &NoHost),
            deny(DenyReason::ConditionsNotMet)
        );
    }
}

mod footprint_tests {
    use super::*;

    fn fp_of(e: CExpr) -> Footprint {
        let rule = Rule {
            pattern: Pattern {
                segs: vec![],
                rest: false,
            },
            allows: vec![CompiledAllow {
                methods: 1,
                cond: e,
            }],
        };
        footprint(&Policy { rules: vec![rule] })
    }

    fn fp(headers: bool, auth: bool, context: bool) -> Footprint {
        Footprint {
            headers,
            auth,
            context,
        }
    }

    fn field(name: &str) -> CExpr {
        CExpr::Select(Box::new(CExpr::Request), bytes(name))
    }

    fn lit_true() -> CExpr {
        CExpr::Lit(Value::Bool(true))
    }

    #[test]
    fn an_empty_policy_reads_nothing() {
        assert_eq!(
            footprint(&Policy { rules: vec![] }),
            fp(false, false, false)
        );
        assert_eq!(fp_of(lit_true()), fp(false, false, false));
    }

    #[test]
    fn method_and_path_are_free() {
        assert_eq!(fp_of(field("method")), fp(false, false, false));
        assert_eq!(fp_of(field("path")), fp(false, false, false));
    }

    #[test]
    fn headers_auth_and_context() {
        assert_eq!(fp_of(field("headers")), fp(true, false, false));
        assert_eq!(fp_of(field("auth")), fp(false, true, false));
        assert_eq!(fp_of(CExpr::Context), fp(false, false, true));
    }

    #[test]
    fn nested_reads_count_the_top_level_field() {
        let uid = CExpr::Select(Box::new(field("auth")), bytes("uid"));
        assert_eq!(fp_of(uid), fp(false, true, false));
        let size = CExpr::Size(Box::new(field("headers")));
        assert_eq!(fp_of(size), fp(true, false, false));
        let has = CExpr::Has(Box::new(CExpr::Request), bytes("auth"));
        assert_eq!(fp_of(has), fp(false, true, false));
    }

    #[test]
    fn request_is_reads_all_headers() {
        let is = CExpr::RequestIs(Box::new(CExpr::Lit(st("json"))));
        assert_eq!(fp_of(is), fp(true, false, false));
    }

    #[test]
    fn other_uses_of_request_are_conservative() {
        assert_eq!(fp_of(CExpr::Request), fp(true, true, false));
        assert_eq!(fp_of(field("unknown")), fp(true, true, false));
        let idx = CExpr::Index(Box::new(CExpr::Request), Box::new(CExpr::Lit(st("auth"))));
        assert_eq!(fp_of(idx), fp(true, true, false));
    }

    #[test]
    fn it_walks_every_operator() {
        let both = CExpr::And(
            Box::new(CExpr::Not(Box::new(field("auth")))),
            Box::new(CExpr::Or(
                Box::new(CExpr::List(vec![CExpr::Context])),
                Box::new(CExpr::Cmp(
                    CmpOp::Eq,
                    Box::new(CExpr::In(
                        Box::new(field("headers")),
                        Box::new(CExpr::Slot(0)),
                    )),
                    Box::new(CExpr::StartsWith(
                        Box::new(field("path")),
                        Box::new(CExpr::Slot(1)),
                    )),
                )),
            )),
        );
        assert_eq!(fp_of(both), fp(true, true, true));
    }

    #[test]
    fn it_covers_every_allow_of_every_rule() {
        let r = |cond| Rule {
            pattern: Pattern {
                segs: vec![],
                rest: false,
            },
            allows: vec![
                CompiledAllow {
                    methods: 1,
                    cond: lit_true(),
                },
                CompiledAllow { methods: 1, cond },
            ],
        };
        let p = Policy {
            rules: vec![r(lit_true()), r(field("auth")), r(CExpr::Context)],
        };
        assert_eq!(footprint(&p), fp(false, true, true));
    }
}

mod lower_tests {
    use super::*;

    const SP: Span = Span { start: 0, end: 0 };

    fn expr(kind: ExprKind) -> Expr {
        Expr { kind, span: SP }
    }

    fn ident(n: &str) -> Expr {
        expr(ExprKind::Ident(bytes(n)))
    }

    fn allow(cond: Option<Expr>) -> Item {
        Item::Allow(Allow {
            methods: 1,
            cond,
            span: SP,
        })
    }

    fn matcher(pattern: Vec<PatSeg>, body: Vec<Item>) -> Match {
        Match {
            pattern,
            body,
            span: SP,
        }
    }

    fn service(matches: Vec<Match>) -> Service {
        Service {
            name: bytes("http"),
            matches,
            span: SP,
        }
    }

    fn lit(s: &str) -> PatSeg {
        PatSeg::Lit(bytes(s))
    }

    fn var(s: &str) -> PatSeg {
        PatSeg::Var(bytes(s))
    }

    fn kind_of(s: &Service) -> LowerErrorKind {
        lower(s).expect_err("should fail").kind
    }

    #[test]
    fn nested_patterns_extend_the_parent() {
        let child = matcher(
            vec![lit("files"), PatSeg::Rest(bytes("p"))],
            vec![allow(None)],
        );
        let parent = matcher(
            vec![lit("users"), var("id")],
            vec![allow(None), Item::Match(child)],
        );
        let policy = lower(&service(vec![parent])).expect("lowers");
        assert_eq!(policy.rules.len(), 2);
        assert_eq!(policy.rules[0].pattern.segs.len(), 2);
        assert!(!policy.rules[0].pattern.rest);
        assert_eq!(
            policy.rules[1].pattern,
            Pattern {
                segs: vec![Seg::Lit(bytes("users")), Seg::Var, Seg::Lit(bytes("files"))],
                rest: true
            }
        );
    }

    #[test]
    fn a_missing_condition_lowers_to_true() {
        let m = matcher(vec![lit("a")], vec![allow(None)]);
        let policy = lower(&service(vec![m])).expect("lowers");
        assert_eq!(
            policy.rules[0].allows[0].cond,
            CExpr::Lit(Value::Bool(true))
        );
    }

    #[test]
    fn matches_without_allows_produce_no_rule() {
        let m = matcher(vec![lit("a")], vec![]);
        assert_eq!(lower(&service(vec![m])).expect("lowers").rules.len(), 0);
    }

    #[test]
    fn captures_resolve_to_slots() {
        let cond = expr(ExprKind::And(Box::new(ident("a")), Box::new(ident("b"))));
        let m = matcher(vec![var("a"), var("b")], vec![allow(Some(cond))]);
        let policy = lower(&service(vec![m])).expect("lowers");
        assert_eq!(
            policy.rules[0].allows[0].cond,
            CExpr::And(Box::new(CExpr::Slot(0)), Box::new(CExpr::Slot(1)))
        );
    }

    #[test]
    fn rejects_unknown_identifiers() {
        let m = matcher(vec![lit("a")], vec![allow(Some(ident("nope")))]);
        assert_eq!(
            kind_of(&service(vec![m])),
            LowerErrorKind::UnknownIdentifier
        );
        // A capture is not in scope in a sibling match.
        let a = matcher(vec![var("x")], vec![]);
        let b = matcher(vec![lit("b")], vec![allow(Some(ident("x")))]);
        assert_eq!(
            kind_of(&service(vec![a, b])),
            LowerErrorKind::UnknownIdentifier
        );
    }

    #[test]
    fn rejects_bad_capture_names() {
        let m = matcher(vec![var("request")], vec![allow(None)]);
        assert_eq!(
            kind_of(&service(vec![m])),
            LowerErrorKind::ReservedCaptureName
        );
        let m = matcher(vec![var("context")], vec![allow(None)]);
        assert_eq!(
            kind_of(&service(vec![m])),
            LowerErrorKind::ReservedCaptureName
        );
        let m = matcher(vec![var("a"), var("a")], vec![allow(None)]);
        assert_eq!(kind_of(&service(vec![m])), LowerErrorKind::DuplicateCapture);
        let inner = matcher(vec![var("a")], vec![allow(None)]);
        let outer = matcher(vec![var("a")], vec![Item::Match(inner)]);
        assert_eq!(
            kind_of(&service(vec![outer])),
            LowerErrorKind::DuplicateCapture
        );
    }

    #[test]
    fn rejects_misplaced_rest() {
        let m = matcher(vec![PatSeg::Rest(bytes("r")), lit("a")], vec![allow(None)]);
        assert_eq!(kind_of(&service(vec![m])), LowerErrorKind::RestNotLast);
        let child = matcher(vec![lit("a")], vec![allow(None)]);
        let m = matcher(vec![PatSeg::Rest(bytes("r"))], vec![Item::Match(child)]);
        assert_eq!(kind_of(&service(vec![m])), LowerErrorKind::RestWithChildren);
    }

    fn call(name: &str, args: Vec<Expr>) -> Expr {
        expr(ExprKind::Call(bytes(name), args))
    }

    fn method(target: Expr, name: &str, args: Vec<Expr>) -> Expr {
        expr(ExprKind::Method(Box::new(target), bytes(name), args))
    }

    fn lower_cond(cond: Expr) -> Result<CExpr, LowerErrorKind> {
        let m = matcher(vec![lit("a")], vec![allow(Some(cond))]);
        match lower(&service(vec![m])) {
            Ok(p) => Ok(p.rules[0].allows[0].cond.clone()),
            Err(e) => Err(e.kind),
        }
    }

    fn string(s: &str) -> Expr {
        expr(ExprKind::Str(bytes(s)))
    }

    #[test]
    fn lowers_functions() {
        let req = || ident("request");
        let size = lower_cond(call("size", vec![string("a")])).expect("size");
        assert_eq!(size, CExpr::Size(Box::new(CExpr::Lit(st("a")))));
        let size = lower_cond(method(string("a"), "size", vec![])).expect("size");
        assert_eq!(size, CExpr::Size(Box::new(CExpr::Lit(st("a")))));
        let has = call(
            "has",
            vec![expr(ExprKind::Select(Box::new(req()), bytes("auth")))],
        );
        let has = lower_cond(has).expect("has");
        assert_eq!(has, CExpr::Has(Box::new(CExpr::Request), bytes("auth")));
        let is = lower_cond(method(req(), "is", vec![string("json")])).expect("is");
        assert_eq!(is, CExpr::RequestIs(Box::new(CExpr::Lit(st("json")))));
        let sw = lower_cond(method(string("a"), "startsWith", vec![string("b")])).expect("sw");
        assert_eq!(
            sw,
            CExpr::StartsWith(Box::new(CExpr::Lit(st("a"))), Box::new(CExpr::Lit(st("b"))))
        );
        let ew = lower_cond(method(string("a"), "endsWith", vec![string("b")])).expect("ew");
        assert_eq!(
            ew,
            CExpr::EndsWith(Box::new(CExpr::Lit(st("a"))), Box::new(CExpr::Lit(st("b"))))
        );
    }

    #[test]
    fn rejects_bad_calls() {
        assert_eq!(
            lower_cond(call("nope", vec![])),
            Err(LowerErrorKind::UnknownFunction)
        );
        assert_eq!(
            lower_cond(call("size", vec![])),
            Err(LowerErrorKind::BadArity)
        );
        assert_eq!(
            lower_cond(call("size", vec![string("a"), string("b")])),
            Err(LowerErrorKind::BadArity)
        );
        assert_eq!(
            lower_cond(call("has", vec![string("a")])),
            Err(LowerErrorKind::BadTarget)
        );
        assert_eq!(
            lower_cond(method(string("a"), "nope", vec![])),
            Err(LowerErrorKind::UnknownFunction)
        );
        assert_eq!(
            lower_cond(method(string("a"), "size", vec![string("b")])),
            Err(LowerErrorKind::BadArity)
        );
        assert_eq!(
            lower_cond(method(string("a"), "startsWith", vec![])),
            Err(LowerErrorKind::BadArity)
        );
        assert_eq!(
            lower_cond(method(string("a"), "is", vec![string("json")])),
            Err(LowerErrorKind::BadTarget)
        );
        let ctx = method(ident("context"), "is", vec![string("json")]);
        assert_eq!(lower_cond(ctx), Err(LowerErrorKind::BadTarget));
    }

    #[test]
    fn enforces_the_depth_limit() {
        let nest = |n: u32| {
            let mut e = expr(ExprKind::Bool(true));
            let mut i = 1;
            while i < n {
                e = expr(ExprKind::Not(Box::new(e)));
                i += 1;
            }
            e
        };
        assert!(lower_cond(nest(MAX_DEPTH)).is_ok());
        assert_eq!(
            lower_cond(nest(MAX_DEPTH + 1)),
            Err(LowerErrorKind::TooDeep)
        );
    }

    #[test]
    fn enforces_the_match_depth_limit() {
        let nest = |n: u32| {
            let mut m = matcher(vec![lit("a")], vec![allow(None)]);
            let mut i = 1;
            while i < n {
                m = matcher(vec![lit("a")], vec![Item::Match(m)]);
                i += 1;
            }
            service(vec![m])
        };
        assert!(lower(&nest(MAX_DEPTH)).is_ok());
        assert_eq!(kind_of(&nest(MAX_DEPTH + 1)), LowerErrorKind::TooDeep);
    }
}
