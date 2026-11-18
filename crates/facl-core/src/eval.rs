//! The condition evaluator, with CEL's error semantics.
//!
//! Errors are values. `false && error` is `false` and `true || error` is
//! `true`, whatever the order; otherwise errors propagate. A non-boolean
//! operand of a logical operator counts as an error.

use crate::ast::CmpOp;
use crate::ir::CExpr;
use crate::value::{EvalError, Value, bytes_eq, map_get, value_eq};
use alloc::vec::Vec;
use core::cmp::Ordering;

/// What a condition can see: the captures, `request` and `context`.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Env<'a> {
    /// The captured path values, numbered as in the pattern.
    pub slots: Vec<Value>,
    /// The `request` value.
    pub request: &'a Value,
    /// The `context` value.
    pub context: &'a Value,
}

/// Functions the engine cannot implement itself.
pub trait Host {
    /// Implements `request.is(media)`: whether the request's content type
    /// matches `media`.
    fn request_is(&self, request: &Value, media: &[u8]) -> Result<bool, EvalError>;
}

/// Evaluates an expression.
pub fn eval<H: Host>(e: &CExpr, env: &Env<'_>, host: &H) -> Result<Value, EvalError> {
    match e {
        CExpr::Lit(v) => Ok(v.clone()),
        CExpr::Slot(i) => eval_slot(env, *i),
        CExpr::Request => Ok(env.request.clone()),
        CExpr::Context => Ok(env.context.clone()),
        CExpr::List(items) => eval_list(items, env, host),
        CExpr::Select(a, key) => select(&eval(a, env, host)?, key),
        CExpr::Index(a, k) => {
            let target = eval(a, env, host)?;
            let key = eval(k, env, host)?;
            index(&target, &key)
        }
        CExpr::Has(a, key) => has(&eval(a, env, host)?, key),
        CExpr::Size(a) => size(&eval(a, env, host)?),
        CExpr::StartsWith(a, b) => {
            let (x, y) = two_strings(a, b, env, host)?;
            Ok(Value::Bool(starts_with(&x, &y)))
        }
        CExpr::EndsWith(a, b) => {
            let (x, y) = two_strings(a, b, env, host)?;
            Ok(Value::Bool(ends_with(&x, &y)))
        }
        CExpr::RequestIs(a) => match eval(a, env, host)? {
            Value::Str(media) => Ok(Value::Bool(host.request_is(env.request, &media)?)),
            _ => Err(EvalError::TypeMismatch),
        },
        CExpr::Not(a) => Ok(Value::Bool(!as_bool(eval(a, env, host))?)),
        CExpr::And(a, b) => eval_and(a, b, env, host),
        CExpr::Or(a, b) => eval_or(a, b, env, host),
        CExpr::Cmp(op, a, b) => {
            let x = eval(a, env, host)?;
            let y = eval(b, env, host)?;
            compare_op(op, &x, &y)
        }
        CExpr::In(a, b) => {
            let x = eval(a, env, host)?;
            let y = eval(b, env, host)?;
            contains(&x, &y)
        }
    }
}

fn eval_slot(env: &Env<'_>, i: u32) -> Result<Value, EvalError> {
    let i = i as usize;
    if i < env.slots.len() {
        Ok(env.slots[i].clone())
    } else {
        // Lowering never produces this; failing closed is the safe answer.
        Err(EvalError::BadArgument)
    }
}

fn eval_list<H: Host>(items: &[CExpr], env: &Env<'_>, host: &H) -> Result<Value, EvalError> {
    let mut out = Vec::new();
    let mut i = 0;
    while i < items.len() {
        out.push(eval(&items[i], env, host)?);
        i += 1;
    }
    Ok(Value::List(out))
}

/// Requires a `Bool`; anything else is a type mismatch.
fn as_bool(r: Result<Value, EvalError>) -> Result<bool, EvalError> {
    match r {
        Ok(Value::Bool(b)) => Ok(b),
        Ok(_) => Err(EvalError::TypeMismatch),
        Err(e) => Err(e),
    }
}

fn eval_and<H: Host>(a: &CExpr, b: &CExpr, env: &Env<'_>, host: &H) -> Result<Value, EvalError> {
    match as_bool(eval(a, env, host)) {
        Ok(false) => Ok(Value::Bool(false)),
        Ok(true) => Ok(Value::Bool(as_bool(eval(b, env, host))?)),
        Err(err) => match as_bool(eval(b, env, host)) {
            Ok(false) => Ok(Value::Bool(false)),
            _ => Err(err),
        },
    }
}

fn eval_or<H: Host>(a: &CExpr, b: &CExpr, env: &Env<'_>, host: &H) -> Result<Value, EvalError> {
    match as_bool(eval(a, env, host)) {
        Ok(true) => Ok(Value::Bool(true)),
        Ok(false) => Ok(Value::Bool(as_bool(eval(b, env, host))?)),
        Err(err) => match as_bool(eval(b, env, host)) {
            Ok(true) => Ok(Value::Bool(true)),
            _ => Err(err),
        },
    }
}

fn select(target: &Value, key: &[u8]) -> Result<Value, EvalError> {
    match target {
        Value::Map(entries) => match map_get(entries, key) {
            Some(v) => Ok(v.clone()),
            None => Err(EvalError::NoSuchKey),
        },
        _ => Err(EvalError::TypeMismatch),
    }
}

fn has(target: &Value, key: &[u8]) -> Result<Value, EvalError> {
    match target {
        Value::Map(entries) => Ok(Value::Bool(map_get(entries, key).is_some())),
        _ => Err(EvalError::TypeMismatch),
    }
}

fn index(target: &Value, key: &Value) -> Result<Value, EvalError> {
    match (target, key) {
        (Value::List(items), Value::Int(i)) => {
            if *i < 0 || *i >= items.len() as i64 {
                Err(EvalError::IndexOutOfRange)
            } else {
                Ok(items[*i as usize].clone())
            }
        }
        (Value::Map(entries), Value::Str(k)) => match map_get(entries, k) {
            Some(v) => Ok(v.clone()),
            None => Err(EvalError::NoSuchKey),
        },
        _ => Err(EvalError::TypeMismatch),
    }
}

fn size(v: &Value) -> Result<Value, EvalError> {
    match v {
        Value::Str(s) => Ok(Value::Int(code_points(s) as i64)),
        Value::List(items) => Ok(Value::Int(items.len() as i64)),
        Value::Map(entries) => Ok(Value::Int(entries.len() as i64)),
        _ => Err(EvalError::TypeMismatch),
    }
}

/// Counts code points: every byte except UTF-8 continuation bytes.
fn code_points(s: &[u8]) -> usize {
    let mut n = 0;
    let mut i = 0;
    while i < s.len() {
        if s[i] & 0xC0 != 0x80 {
            n += 1;
        }
        i += 1;
    }
    n
}

fn two_strings<H: Host>(
    a: &CExpr,
    b: &CExpr,
    env: &Env<'_>,
    host: &H,
) -> Result<(Vec<u8>, Vec<u8>), EvalError> {
    let x = eval(a, env, host)?;
    let y = eval(b, env, host)?;
    match (x, y) {
        (Value::Str(x), Value::Str(y)) => Ok((x, y)),
        _ => Err(EvalError::TypeMismatch),
    }
}

fn starts_with(s: &[u8], prefix: &[u8]) -> bool {
    if prefix.len() > s.len() {
        return false;
    }
    bytes_eq(&s[..prefix.len()], prefix)
}

fn ends_with(s: &[u8], suffix: &[u8]) -> bool {
    if suffix.len() > s.len() {
        return false;
    }
    bytes_eq(&s[s.len() - suffix.len()..], suffix)
}

fn compare_op(op: &CmpOp, x: &Value, y: &Value) -> Result<Value, EvalError> {
    let result = match op {
        CmpOp::Eq => value_eq(x, y),
        CmpOp::Ne => !value_eq(x, y),
        CmpOp::Lt => compare(x, y)? == Ordering::Less,
        CmpOp::Le => compare(x, y)? != Ordering::Greater,
        CmpOp::Gt => compare(x, y)? == Ordering::Greater,
        CmpOp::Ge => compare(x, y)? != Ordering::Less,
    };
    Ok(Value::Bool(result))
}

/// Orders two values of the same orderable type: `Int`, `Str` or `Bool`.
fn compare(x: &Value, y: &Value) -> Result<Ordering, EvalError> {
    match (x, y) {
        (Value::Int(a), Value::Int(b)) => Ok(a.cmp(b)),
        (Value::Bool(a), Value::Bool(b)) => Ok(a.cmp(b)),
        (Value::Str(a), Value::Str(b)) => Ok(compare_bytes(a, b)),
        _ => Err(EvalError::TypeMismatch),
    }
}

fn compare_bytes(a: &[u8], b: &[u8]) -> Ordering {
    let mut i = 0;
    while i < a.len() && i < b.len() {
        if a[i] != b[i] {
            return a[i].cmp(&b[i]);
        }
        i += 1;
    }
    a.len().cmp(&b.len())
}

fn contains(x: &Value, collection: &Value) -> Result<Value, EvalError> {
    match collection {
        Value::List(items) => {
            let mut i = 0;
            while i < items.len() {
                if value_eq(x, &items[i]) {
                    return Ok(Value::Bool(true));
                }
                i += 1;
            }
            Ok(Value::Bool(false))
        }
        Value::Map(entries) => match x {
            Value::Str(k) => Ok(Value::Bool(map_get(entries, k).is_some())),
            _ => Err(EvalError::TypeMismatch),
        },
        _ => Err(EvalError::TypeMismatch),
    }
}
