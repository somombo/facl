//! Runtime values and the helpers that compare them.

use alloc::vec::Vec;

/// A runtime value. Strings are UTF-8 bytes and map keys are strings.
///
/// The derived `PartialEq` is structural, so two maps with the same entries in
/// a different order differ. CEL equality, which ignores map order, is
/// [`value_eq`].
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Value {
    /// The null value.
    Null,
    /// A boolean.
    Bool(bool),
    /// A 64-bit signed integer.
    Int(i64),
    /// A UTF-8 string.
    Str(Vec<u8>),
    /// An ordered list.
    List(Vec<Value>),
    /// A map from string keys to values, stored as pairs.
    Map(Vec<(Vec<u8>, Value)>),
}

/// Why a condition failed to produce a value. Errors never grant access.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum EvalError {
    /// A map has no such key.
    NoSuchKey,
    /// A list index is negative or past the end.
    IndexOutOfRange,
    /// An operand has the wrong type for the operation.
    TypeMismatch,
    /// An argument is invalid, such as an unknown media type.
    BadArgument,
    /// The host function failed.
    Host,
}

/// Returns true when two byte strings are equal.
pub fn bytes_eq(a: &[u8], b: &[u8]) -> bool {
    if a.len() != b.len() {
        return false;
    }
    let mut i = 0;
    while i < a.len() {
        if a[i] != b[i] {
            return false;
        }
        i += 1;
    }
    true
}

/// Looks up the first entry with the given key.
pub fn map_get<'a>(entries: &'a [(Vec<u8>, Value)], key: &[u8]) -> Option<&'a Value> {
    let mut i = 0;
    while i < entries.len() {
        if bytes_eq(&entries[i].0, key) {
            return Some(&entries[i].1);
        }
        i += 1;
    }
    None
}

/// CEL equality: structural, values of different types are unequal, and map
/// entry order does not matter.
pub fn value_eq(a: &Value, b: &Value) -> bool {
    match (a, b) {
        (Value::Null, Value::Null) => true,
        (Value::Bool(x), Value::Bool(y)) => x == y,
        (Value::Int(x), Value::Int(y)) => x == y,
        (Value::Str(x), Value::Str(y)) => bytes_eq(x, y),
        (Value::List(x), Value::List(y)) => list_eq(x, y),
        (Value::Map(x), Value::Map(y)) => map_eq(x, y),
        _ => false,
    }
}

fn list_eq(a: &[Value], b: &[Value]) -> bool {
    if a.len() != b.len() {
        return false;
    }
    let mut i = 0;
    while i < a.len() {
        if !value_eq(&a[i], &b[i]) {
            return false;
        }
        i += 1;
    }
    true
}

fn map_eq(a: &[(Vec<u8>, Value)], b: &[(Vec<u8>, Value)]) -> bool {
    if a.len() != b.len() {
        return false;
    }
    let mut i = 0;
    while i < a.len() {
        match map_get(b, &a[i].0) {
            Some(v) => {
                if !value_eq(&a[i].1, v) {
                    return false;
                }
            }
            None => return false,
        }
        i += 1;
    }
    true
}
