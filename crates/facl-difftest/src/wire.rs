//! The oracle accepts one case per line. A case has an id, a policy, and an
//! array of requests. The policy records the service name and a list of items
//! in source order. Each {"match":[segments]} opens a block, {"allow":{...}}
//! adds an allow to the current block, and "end" closes it. This keeps JSON
//! shallow even for policies with deeply nested matches.
//!
//! Segments have one key, lit, var, or rest. Allows contain action names and
//! an optional cond. Expressions use the "k" tag. Strings are UTF-8. Requests
//! carry method, raw path, ordered header pairs, and auth and context maps or
//! null. The response echoes the id with compile: "ok" and verdicts, or with
//! compile: {"error": "..."} on rejection. Verdicts are "allow" or {"deny":
//! "<facl reason>"}. A protocolError reports unreadable input.

use crate::syntax::{Allow, Block, Item, Rules, SPAN, cmp_op, text};
use facl::RequestFacts;
use facl_core::{CmpOp, Expr, ExprKind, PatSeg};
use serde_json::value::RawValue;
use serde_json::{Value as Json, json};
use std::collections::BTreeMap;

type Fields<'a> = BTreeMap<String, &'a RawValue>;

fn raw_field<'a>(fields: &Fields<'a>, key: &str) -> Result<&'a str, String> {
    fields
        .get(key)
        .map(|value| value.get())
        .ok_or_else(|| format!("missing {key}"))
}

#[derive(Clone)]
pub(crate) struct Case {
    pub id: String,
    pub policy: Rules,
    pub requests: Vec<RequestFacts>,
}

impl Case {
    pub(crate) fn json(&self) -> Json {
        let mut items = Vec::new();
        for block in &self.policy.blocks {
            block_items(block, &mut items);
        }
        json!({
            "id": self.id,
            "policy": {"service": self.policy.service, "items": items},
            "requests": self.requests.iter().map(request_json).collect::<Vec<_>>(),
        })
    }

    pub(crate) fn parse(input: &str) -> crate::Result<Self> {
        // Lists and call arguments can use two JSON containers per expression node.
        // Decode one nesting level at a time, here and in `read_expr`, so deep
        // policies stay within serde_json's nesting limit.
        let case: Fields = serde_json::from_str(input)?;
        let id = serde_json::from_str(raw_field(&case, "id")?)?;
        let policy: Fields = serde_json::from_str(raw_field(&case, "policy")?)?;
        let service = serde_json::from_str(raw_field(&policy, "service")?)?;
        let items: Vec<&RawValue> = serde_json::from_str(raw_field(&policy, "items")?)?;
        let mut open: Vec<Block> = Vec::new();
        let mut blocks = Vec::new();
        for raw in items {
            if raw.get().starts_with('"') {
                if serde_json::from_str::<String>(raw.get())? != "end" {
                    return Err("expected end of match".into());
                }
                let block = open.pop().ok_or("end without an open match")?;
                if let Some(parent) = open.last_mut() {
                    parent.body.push(Item::Match(block));
                } else {
                    blocks.push(block);
                }
                continue;
            }
            let item: Fields = serde_json::from_str(raw.get())?;
            if let Some(pattern) = item.get("match") {
                let pattern: Vec<Json> = serde_json::from_str(pattern.get())?;
                let pattern = pattern.iter().map(read_segment).collect::<Result<_, _>>()?;
                open.push(Block {
                    pattern,
                    body: Vec::new(),
                });
            } else {
                let block = open.last_mut().ok_or("allow outside a match")?;
                block
                    .body
                    .push(Item::Allow(read_allow(raw_field(&item, "allow")?)?));
            }
        }
        if !open.is_empty() {
            return Err("unclosed match".into());
        }
        let requests = serde_json::from_str::<Vec<Json>>(raw_field(&case, "requests")?)?
            .iter()
            .map(read_request)
            .collect::<Result<_, _>>()?;
        Ok(Self {
            id,
            policy: Rules { service, blocks },
            requests,
        })
    }
}

fn block_items(block: &Block, items: &mut Vec<Json>) {
    let pattern = block
        .pattern
        .iter()
        .map(|seg| match seg {
            PatSeg::Lit(s) => json!({"lit": text(s)}),
            PatSeg::Var(s) => json!({"var": text(s)}),
            PatSeg::Rest(s) => json!({"rest": text(s)}),
        })
        .collect::<Vec<_>>();
    items.push(json!({"match": pattern}));
    for item in &block.body {
        match item {
            Item::Match(child) => block_items(child, items),
            Item::Allow(allow) => {
                let mut stmt = json!({"actions": allow.actions});
                if let Some(cond) = &allow.cond {
                    stmt["cond"] = expr_json(cond);
                }
                items.push(json!({"allow": stmt}));
            }
        }
    }
    items.push(json!("end"));
}

fn expr_json(expr: &Expr) -> Json {
    let list = |args: &[Expr]| args.iter().map(expr_json).collect::<Vec<_>>();
    let binary = |tag, l, r| json!({"k": tag, "l": expr_json(l), "r": expr_json(r)});
    match &expr.kind {
        ExprKind::Null => json!({"k": "null"}),
        ExprKind::Bool(b) => json!({"k": "bool", "v": b}),
        ExprKind::Int(i) => json!({"k": "int", "v": i}),
        ExprKind::Str(s) => json!({"k": "str", "v": text(s)}),
        ExprKind::List(items) => json!({"k": "list", "items": list(items)}),
        ExprKind::Ident(id) => json!({"k": "ident", "name": text(id)}),
        ExprKind::Select(of, field) => {
            json!({"k": "select", "of": expr_json(of), "field": text(field)})
        }
        ExprKind::Index(of, key) => {
            json!({"k": "index", "of": expr_json(of), "key": expr_json(key)})
        }
        ExprKind::Call(fn_name, args) => {
            json!({"k": "call", "fn": text(fn_name), "args": list(args)})
        }
        ExprKind::Method(of, name, args) => {
            json!({"k": "method", "of": expr_json(of), "name": text(name), "args": list(args)})
        }
        ExprKind::Not(e) => json!({"k": "not", "e": expr_json(e)}),
        ExprKind::And(l, r) => binary("and", l, r),
        ExprKind::Or(l, r) => binary("or", l, r),
        ExprKind::Cmp(op, l, r) => {
            json!({"k": "cmp", "op": cmp_op(op), "l": expr_json(l), "r": expr_json(r)})
        }
        ExprKind::In(l, r) => binary("in", l, r),
    }
}

fn request_json(facts: &RequestFacts) -> Json {
    json!({
        "method": facts.method,
        "path": facts.path,
        "headers": facts.headers,
        "auth": facts.auth,
        "context": facts.context,
    })
}

fn field<'a>(j: &'a Json, key: &str) -> Result<&'a Json, String> {
    j.get(key).ok_or_else(|| format!("missing {key}"))
}

fn string<'a>(j: &'a Json, key: &str) -> Result<&'a str, String> {
    field(j, key)?
        .as_str()
        .ok_or_else(|| format!("{key} must be a string"))
}

fn array<'a>(j: &'a Json, key: &str) -> Result<&'a [Json], String> {
    field(j, key)?
        .as_array()
        .map(Vec::as_slice)
        .ok_or_else(|| format!("{key} must be an array"))
}

fn read_segment(j: &Json) -> Result<PatSeg, String> {
    let bytes = |key| string(j, key).map(|s| s.as_bytes().to_vec());
    let obj = j.as_object().ok_or("pattern segment must be an object")?;
    if obj.len() == 1 {
        match obj.keys().next().map(String::as_str) {
            Some("lit") => return bytes("lit").map(PatSeg::Lit),
            Some("var") => return bytes("var").map(PatSeg::Var),
            Some("rest") => return bytes("rest").map(PatSeg::Rest),
            _ => {}
        }
    }
    Err("invalid pattern segment".into())
}

fn read_allow(raw: &str) -> crate::Result<Allow> {
    let fields: Fields = serde_json::from_str(raw)?;
    let actions: Vec<String> = serde_json::from_str(raw_field(&fields, "actions")?)?;
    if actions.is_empty() {
        return Err("allow must name at least one action".into());
    }
    let cond = match fields.get("cond") {
        Some(raw) => Some(read_expr(raw.get())?),
        None => None,
    };
    Ok(Allow { actions, cond })
}

fn read_expr(raw: &str) -> crate::Result<Expr> {
    let fields: Fields = serde_json::from_str(raw)?;
    let value = |key| raw_field(&fields, key);
    let text = |key| -> crate::Result<String> { Ok(serde_json::from_str(value(key)?)?) };
    let bytes = |key| text(key).map(String::into_bytes);
    let boxed = |key| -> crate::Result<Box<Expr>> { Ok(Box::new(read_expr(value(key)?)?)) };
    let list = |key| -> crate::Result<Vec<Expr>> {
        serde_json::from_str::<Vec<&RawValue>>(value(key)?)?
            .into_iter()
            .map(|item| read_expr(item.get()))
            .collect()
    };
    let kind = match text("k")?.as_str() {
        "null" => ExprKind::Null,
        "bool" => ExprKind::Bool(serde_json::from_str(value("v")?)?),
        "int" => ExprKind::Int(serde_json::from_str(value("v")?)?),
        "str" => ExprKind::Str(bytes("v")?),
        "list" => ExprKind::List(list("items")?),
        "ident" => ExprKind::Ident(bytes("name")?),
        "select" => ExprKind::Select(boxed("of")?, bytes("field")?),
        "index" => ExprKind::Index(boxed("of")?, boxed("key")?),
        "call" => ExprKind::Call(bytes("fn")?, list("args")?),
        "method" => ExprKind::Method(boxed("of")?, bytes("name")?, list("args")?),
        "not" => ExprKind::Not(boxed("e")?),
        "and" => ExprKind::And(boxed("l")?, boxed("r")?),
        "or" => ExprKind::Or(boxed("l")?, boxed("r")?),
        "cmp" => {
            let op = match text("op")?.as_str() {
                "==" => CmpOp::Eq,
                "!=" => CmpOp::Ne,
                "<" => CmpOp::Lt,
                "<=" => CmpOp::Le,
                ">" => CmpOp::Gt,
                ">=" => CmpOp::Ge,
                op => return Err(format!("unknown comparison {op}").into()),
            };
            ExprKind::Cmp(op, boxed("l")?, boxed("r")?)
        }
        "in" => ExprKind::In(boxed("l")?, boxed("r")?),
        tag => return Err(format!("unknown expression form {tag}").into()),
    };
    Ok(Expr { kind, span: SPAN })
}

fn read_request(j: &Json) -> Result<RequestFacts, String> {
    let headers = array(j, "headers")?
        .iter()
        .map(|h| match h.as_array().map(Vec::as_slice) {
            Some([Json::String(key), Json::String(value)]) => Ok((key.clone(), value.clone())),
            _ => Err("header must be a pair of strings"),
        })
        .collect::<Result<Vec<_>, _>>()?;
    let mut facts = j.clone();
    facts
        .as_object_mut()
        .ok_or("request must be an object")?
        .remove("headers");
    let mut facts = RequestFacts::from_json(&facts).map_err(|e| e.to_string())?;
    facts.headers = headers;
    Ok(facts)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn replay_preserves_a_condition_at_the_depth_limit() {
        // Nested lists give the deepest JSON a valid condition can have.
        let mut cond = json!({"k": "list", "items": []});
        for _ in 1..facl_core::MAX_DEPTH {
            cond = json!({"k": "list", "items": [cond]});
        }
        let wire = json!({
            "id": "deep-lists",
            "policy": {"service": "http", "items": [
                {"match": []}, {"allow": {"actions": ["get"], "cond": cond}}, "end"
            ]},
            "requests": [],
        });
        let replay = Case::parse(&wire.to_string()).unwrap();
        assert_eq!(replay.json(), wire);
    }
}
