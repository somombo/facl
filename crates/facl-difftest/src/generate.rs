use crate::syntax::{
    Allow, Block, Item, MATCH_DEPTH_LIMIT, METHODS, Rules, SPAN, action_mask, text,
};
use crate::wire::Case;
use facl::RequestFacts;
use facl_core::{CmpOp, Expr, ExprKind as E, PatSeg};
use serde_json::{Value as Json, json};

const ACTIONS: &[&str] = &[
    "read", "Write", "GET", "head", "OptIoNs", "post", "PUT", "patch", "delete",
];
const SEGMENTS: &[&str] = &["alice", "bob", "acme", "1", "a b", "é", "😀", "b.txt"];
const STRINGS: &[&str] = &[
    "",
    "abc",
    "ab-xyz",
    "y",
    "é😀",
    "e\u{301}",
    "\"'\\\n\r\t\u{0}\u{7f}",
];
const MEDIA: &[&str] = &[
    "json",
    "HTML",
    "text",
    "xml",
    "urlencoded",
    "multipart",
    "application/*",
    "text/csv",
    "bogus",
];
const CONTENT_TYPES: &[&str] = &[
    "  Application/JSON ; charset=utf-8",
    "application/problem+json",
    "text/html",
    "text/plain",
    "text/csv",
    "text/xml",
    "application/rss+xml",
    "application/x-www-form-urlencoded",
    "multipart/form-data; boundary=x",
];

struct SplitMix64(u64);

impl SplitMix64 {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e3779b97f4a7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58476d1ce4e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d049bb133111eb);
        z ^ (z >> 31)
    }

    fn below(&mut self, length: usize) -> usize {
        (self.next() % length as u64) as usize
    }

    fn pick<'a, T>(&mut self, items: &'a [T]) -> &'a T {
        &items[self.below(items.len())]
    }

    fn one_in(&mut self, n: usize) -> bool {
        self.below(n) == 0
    }

    fn integer(&mut self) -> i64 {
        match self.below(5) {
            0 => i64::MIN,
            1 => i64::MAX,
            2 => self.next() as i64,
            _ => self.below(11) as i64 - 5,
        }
    }
}

#[derive(Clone, Default)]
struct Route {
    segments: Vec<String>,
    bindings: Vec<(String, Expr)>,
}

impl Route {
    fn path(&self) -> String {
        format!("/{}", self.segments.join("/"))
    }
}

struct Target {
    route: Route,
    method: &'static str,
}

pub(crate) struct Generator {
    seed: u64,
    rng: SplitMix64,
}

impl Generator {
    pub(crate) fn new(seed: u64) -> Self {
        Self {
            seed,
            rng: SplitMix64(seed),
        }
    }

    pub(crate) fn case(&mut self, index: usize) -> Case {
        let (blocks, requests) = match self.rng.below(100) {
            0..=2 => self.deep_expression(),
            3 => self.deep_match(),
            4..=15 => (vec![self.invalid_block()], Vec::new()),
            _ => self.composed(),
        };
        let service = *self.rng.pick(&["http", "api.v1", "facl_test"]);
        Case {
            id: format!("s{}-{index}", self.seed),
            policy: Rules {
                service: service.into(),
                blocks,
            },
            requests,
        }
    }

    fn composed(&mut self) -> (Vec<Block>, Vec<RequestFacts>) {
        let mut targets = Vec::new();
        let blocks = (0..=self.rng.below(2))
            .map(|_| self.block(&Route::default(), 2, &mut targets))
            .collect();
        let target = self.rng.pick(&targets);
        let first = self.facts(target, target.route.path(), target.method);
        let mut requests = vec![first];
        for _ in 0..=self.rng.below(2) {
            let target = self.rng.pick(&targets);
            let path = mutate_path(&target.route.path(), self.rng.below(16));
            let method = match self.rng.below(12) {
                0 => target.method.to_ascii_lowercase(),
                1 => "TRACE".into(),
                2..=4 => (*self.rng.pick(&METHODS)).into(),
                _ => target.method.into(),
            };
            requests.push(self.facts(target, path, &method));
        }
        (blocks, requests)
    }

    fn block(&mut self, parent: &Route, remaining: usize, targets: &mut Vec<Target>) -> Block {
        let mut route = parent.clone();
        let mut pattern = Vec::new();
        let count = if self.rng.one_in(8) {
            0
        } else {
            1 + self.rng.below(3)
        };
        for i in 0..count {
            let label = format!("v{}", route.bindings.len());
            if i + 1 == count && self.rng.one_in(5) {
                let tail: Vec<_> = (0..self.rng.below(4))
                    .map(|_| *self.rng.pick(SEGMENTS))
                    .collect();
                route.segments.extend(tail.iter().map(|s| (*s).into()));
                route.bindings.push((
                    label.clone(),
                    node(E::List(tail.into_iter().map(string).collect())),
                ));
                pattern.push(PatSeg::Rest(label.into_bytes()));
            } else if self.rng.one_in(2) {
                let segment = *self.rng.pick(SEGMENTS);
                route.segments.push(segment.into());
                route.bindings.push((label.clone(), string(segment)));
                pattern.push(PatSeg::Var(label.into_bytes()));
            } else {
                let lit = *self
                    .rng
                    .pick(&["users", "public", "v1.0", "web-hook", "a~b", "X"]);
                route.segments.push(lit.into());
                pattern.push(PatSeg::Lit(lit.as_bytes().to_vec()));
            }
        }

        let actions = self.actions();
        let mask = actions
            .iter()
            .fold(0, |bits, a| bits | action_mask(a).unwrap());
        let methods: Vec<_> = METHODS
            .iter()
            .enumerate()
            .filter_map(|(i, m)| (mask & (1 << i) != 0).then_some(*m))
            .collect();
        targets.push(Target {
            route: route.clone(),
            method: self.rng.pick(&methods),
        });

        let mut body = vec![Item::Allow(Allow {
            actions,
            cond: (!self.rng.one_in(9)).then(|| self.condition(&route, 2)),
        })];
        if self.rng.one_in(3) {
            body.push(Item::Allow(Allow {
                actions: self.actions(),
                cond: Some(self.condition(&route, 2)),
            }));
        }
        if remaining != 0 && !matches!(pattern.last(), Some(PatSeg::Rest(_))) && self.rng.one_in(2)
        {
            let position = self.rng.below(body.len() + 1);
            body.insert(
                position,
                Item::Match(self.block(&route, remaining - 1, targets)),
            );
        }
        Block { pattern, body }
    }

    fn actions(&mut self) -> Vec<String> {
        (0..=self.rng.below(2))
            .map(|_| (*self.rng.pick(ACTIONS)).to_owned())
            .collect()
    }

    fn condition(&mut self, route: &Route, depth: usize) -> Expr {
        if depth != 0 {
            match self.rng.below(6) {
                0 => {
                    return binary(
                        E::And,
                        self.condition(route, depth - 1),
                        self.condition(route, depth - 1),
                    );
                }
                1 => {
                    return binary(
                        E::Or,
                        self.condition(route, depth - 1),
                        self.condition(route, depth - 1),
                    );
                }
                2 => return not(self.condition(route, depth - 1)),
                _ => {}
            }
        }
        match self.rng.below(24) {
            0 => node(E::Bool(self.rng.one_in(2))),
            1 => field("context", "ok"),
            2 => compare(self.op(), field("context", "n"), int(self.rng.integer())),
            3 => compare(
                self.op(),
                field("context", "s"),
                string(self.rng.pick(STRINGS)),
            ),
            4 => compare(self.op(), self.term(route), self.term(route)),
            5 => cmp(field("request", "path"), string(&route.path())),
            6 if !route.bindings.is_empty() => {
                let (label, sample) = self.rng.pick(&route.bindings);
                cmp(ident(label), sample.clone())
            }
            7 => cmp(select(field("request", "auth"), "uid"), self.term(route)),
            8 => call("has", vec![field("context", "flag")]),
            9 => call("has", vec![select(field("request", "auth"), "uid")]),
            10 => {
                let key = *self.rng.pick(&["s", "l", "m", "n"]);
                let value = field("context", key);
                let size = if self.rng.one_in(2) {
                    call("size", vec![value])
                } else {
                    method(value, "size", vec![])
                };
                let expected = self.rng.below(5) as i64;
                compare(self.op(), size, int(expected))
            }
            11 | 12 => {
                let fn_name = *self.rng.pick(&["startsWith", "endsWith"]);
                let prefix = *self.rng.pick(&["", "ab", "xyz", "é", "😀", "no"]);
                method(field("context", "s"), fn_name, vec![string(prefix)])
            }
            13 | 14 => {
                let arg = if self.rng.one_in(8) {
                    int(1)
                } else {
                    string(self.rng.pick(MEDIA))
                };
                let predicate = method(ident("request"), "is", vec![arg]);
                if self.rng.one_in(2) {
                    not(predicate)
                } else {
                    predicate
                }
            }
            15 => binary(
                E::In,
                string(self.rng.pick(&["x", "y", "missing"])),
                field("context", "l"),
            ),
            16 => binary(
                E::In,
                self.term(route),
                node(E::List(vec![self.term(route), self.term(route)])),
            ),
            17 => binary(
                E::In,
                string(self.rng.pick(&["k", "z", "missing"])),
                field("context", "m"),
            ),
            18 => cmp(
                index(field("context", "l"), field("context", "i")),
                string("y"),
            ),
            19 => cmp(
                index(field("request", "headers"), string("x-token")),
                string("one, two"),
            ),
            20 => cmp(field("context", "m"), field("context", "other")),
            21 => self.logical_error(),
            22 => cmp(field("request", "method"), string(self.rng.pick(&METHODS))),
            _ => self.term(route),
        }
    }

    fn logical_error(&mut self) -> Expr {
        let error = *self.rng.pick(&["not_supplied", "no_key"]);
        let mut a = field("context", error);
        let mut b = node(E::Bool(self.rng.one_in(2)));
        if self.rng.one_in(2) {
            std::mem::swap(&mut a, &mut b);
        }
        if self.rng.one_in(2) {
            not(binary(E::And, a, b))
        } else {
            binary(E::Or, a, b)
        }
    }

    fn op(&mut self) -> CmpOp {
        self.rng
            .pick(&[
                CmpOp::Eq,
                CmpOp::Ne,
                CmpOp::Lt,
                CmpOp::Le,
                CmpOp::Gt,
                CmpOp::Ge,
            ])
            .clone()
    }

    fn term(&mut self, route: &Route) -> Expr {
        match self.rng.below(14) {
            0 => node(E::Null),
            1 => node(E::Bool(self.rng.one_in(2))),
            2 => int(self.rng.integer()),
            3 => string(self.rng.pick(STRINGS)),
            4 => node(E::List(vec![
                int(self.rng.integer()),
                string(self.rng.pick(STRINGS)),
            ])),
            5 => ident("context"),
            6 => ident("request"),
            7 => field("request", "auth"),
            8 => field("request", "path"),
            9 if !route.bindings.is_empty() => ident(&self.rng.pick(&route.bindings).0),
            10 => index(field("context", "l"), int(self.rng.integer())),
            11 => index(
                field("context", "m"),
                string(self.rng.pick(&["k", "missing"])),
            ),
            _ => field(
                "context",
                self.rng.pick(&["n", "s", "l", "m", "ok", "missing"]),
            ),
        }
    }

    fn facts(&mut self, target: &Target, path: String, method: &str) -> RequestFacts {
        let mut headers = Vec::new();
        if !self.rng.one_in(4) {
            let key = *self
                .rng
                .pick(&["Content-Type", "content-type", "CONTENT-TYPE"]);
            headers.push((key.into(), (*self.rng.pick(CONTENT_TYPES)).into()));
        }
        if !self.rng.one_in(3) {
            headers.push(("X-Token".into(), "one".into()));
            if self.rng.one_in(2) {
                headers.push(("x-TOKEN".into(), "two".into()));
            }
        }
        let auth = (!self.rng.one_in(3)).then(|| {
            let capture = target
                .route
                .bindings
                .iter()
                .find_map(|(_, sample)| match &sample.kind {
                    E::Str(s) => Some(text(s)),
                    _ => None,
                });
            let uid = if self.rng.one_in(2) {
                capture.unwrap_or("alice")
            } else {
                "bob"
            };
            json!({"uid": uid, "token": {"admin": self.rng.one_in(2), "roles": ["reader"]}})
        });
        let context = (!self.rng.one_in(6)).then(|| self.context());
        RequestFacts {
            method: method.into(),
            path,
            headers,
            auth,
            context,
        }
    }

    fn context(&mut self) -> Json {
        let n = self.rng.integer();
        let mut map = json!({"k": n, "nested": {"z": null}, "z": true});
        let other = if self.rng.one_in(2) {
            map.clone()
        } else {
            json!({"k": n})
        };
        if self.rng.one_in(3) {
            map.as_object_mut().unwrap().remove("k");
        }
        let mut context = json!({
            "ok": self.rng.one_in(2),
            "n": n,
            "s": self.rng.pick(STRINGS),
            "l": self.rng.pick(&[json!([]), json!(["x", "y"]), json!([1, "y", null])]),
            "m": map,
            "other": other,
            "i": self.rng.below(5) as i64 - 1,
        });
        if self.rng.one_in(2) {
            context["flag"] = self
                .rng
                .pick(&[Json::Null, json!(false), json!(true)])
                .clone();
        }
        context
    }

    fn deep_expression(&mut self) -> (Vec<Block>, Vec<RequestFacts>) {
        let expr = if self.rng.one_in(3) {
            let mut list = node(E::Null);
            for _ in 0..60 + self.rng.below(3) {
                list = node(E::List(vec![list]));
            }
            cmp(method(list, "size", vec![]), int(1))
        } else {
            let depth = 62 + self.rng.below(5);
            let mut expr = field("context", "deep");
            for _ in 0..3 {
                expr = select(expr, "a");
            }
            let base_depth = if self.rng.one_in(2) {
                expr = call("has", vec![expr]);
                6
            } else {
                5
            };
            for _ in base_depth..depth {
                expr = not(expr);
            }
            expr
        };
        (
            vec![rule(Vec::new(), vec![allow("get", Some(expr))])],
            vec![RequestFacts {
                method: "GET".into(),
                path: "/".into(),
                headers: Vec::new(),
                auth: None,
                context: Some(json!({"deep": {"a": {"a": {"a": true}}}})),
            }],
        )
    }

    fn deep_match(&mut self) -> (Vec<Block>, Vec<RequestFacts>) {
        let count = MATCH_DEPTH_LIMIT - 2 + self.rng.below(5);
        let cond = self.rng.one_in(2).then(|| node(E::Bool(true)));
        let mut block = rule(vec![literal("v")], vec![allow("read", cond)]);
        for _ in 1..count {
            block = rule(vec![literal("v")], vec![Item::Match(block)]);
        }
        (
            vec![block],
            vec![RequestFacts {
                method: "HEAD".into(),
                path: "/v".repeat(count),
                headers: Vec::new(),
                auth: None,
                context: None,
            }],
        )
    }

    fn invalid_block(&mut self) -> Block {
        let var = |id: &str| PatSeg::Var(id.as_bytes().to_vec());
        let rest = || PatSeg::Rest(b"tail".to_vec());
        match self.rng.below(12) {
            0 => rule(vec![], vec![allow("unknownAction", None)]),
            1 => rule(
                vec![var(self.rng.pick(&["request", "context"]))],
                vec![allow("get", None)],
            ),
            2 => {
                let inner = rule(vec![var("id")], vec![allow("read", None)]);
                rule(vec![var("id")], vec![Item::Match(inner)])
            }
            3 => rule(vec![rest(), literal("x")], vec![allow("read", None)]),
            4 => {
                let inner = rule(vec![literal("x")], vec![allow("read", None)]);
                rule(vec![rest()], vec![Item::Match(inner)])
            }
            other => {
                let cond = match other {
                    5 => ident("unbound"),
                    6 => call("unknown", vec![int(1)]),
                    7 => method(ident("request"), "unknown", vec![]),
                    8 => call("size", vec![]),
                    9 => method(string("x"), "endsWith", vec![string(""), string("x")]),
                    10 => call("has", vec![index(ident("context"), string("k"))]),
                    _ => method(ident("context"), "is", vec![string("json")]),
                };
                rule(vec![literal("x")], vec![allow("read", Some(cond))])
            }
        }
    }
}

fn mutate_path(path: &str, variant: usize) -> String {
    let suffix = |segment: &str| format!("{}/{segment}", path.trim_end_matches('/'));
    match variant {
        0..=4 => path.into(),
        5 => match path.find(|c: char| c.is_ascii_alphanumeric()) {
            Some(i) => format!(
                "{}%{:02X}{}",
                &path[..i],
                path.as_bytes()[i],
                &path[i + 1..]
            ),
            None => path.into(),
        },
        6 => suffix("%2F"),
        7 => suffix("%00"),
        8 => suffix("%2e%2e"),
        9 => format!("/{path}"),
        10 => format!("{path}/"),
        11 => format!("{path}?key=value"),
        12 => format!("{path}#fragment"),
        13 => suffix("%G0"),
        14 => suffix("%FF"),
        _ => suffix("unmatched"),
    }
}

fn literal(s: &str) -> PatSeg {
    PatSeg::Lit(s.as_bytes().to_vec())
}

fn rule(pattern: Vec<PatSeg>, body: Vec<Item>) -> Block {
    Block { pattern, body }
}

fn allow(action: &str, cond: Option<Expr>) -> Item {
    Item::Allow(Allow {
        actions: vec![action.into()],
        cond,
    })
}

fn node(kind: E) -> Expr {
    Expr { kind, span: SPAN }
}

fn binary(make: impl FnOnce(Box<Expr>, Box<Expr>) -> E, l: Expr, r: Expr) -> Expr {
    node(make(Box::new(l), Box::new(r)))
}

fn not(arg: Expr) -> Expr {
    node(E::Not(Box::new(arg)))
}

fn int(i: i64) -> Expr {
    node(E::Int(i))
}

fn string(s: &str) -> Expr {
    node(E::Str(s.as_bytes().to_vec()))
}

fn ident(s: &str) -> Expr {
    node(E::Ident(s.as_bytes().to_vec()))
}

fn select(target: Expr, field: &str) -> Expr {
    node(E::Select(Box::new(target), field.as_bytes().to_vec()))
}

fn field(root: &str, key: &str) -> Expr {
    select(ident(root), key)
}

fn index(target: Expr, key: Expr) -> Expr {
    binary(E::Index, target, key)
}

fn call(name: &str, args: Vec<Expr>) -> Expr {
    node(E::Call(name.as_bytes().to_vec(), args))
}

fn method(target: Expr, name: &str, args: Vec<Expr>) -> Expr {
    node(E::Method(Box::new(target), name.as_bytes().to_vec(), args))
}

fn compare(op: CmpOp, a: Expr, b: Expr) -> Expr {
    binary(|l, r| E::Cmp(op, l, r), a, b)
}

fn cmp(a: Expr, b: Expr) -> Expr {
    compare(CmpOp::Eq, a, b)
}
