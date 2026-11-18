//! Request path canonicalization and pattern matching.
//!
//! The engine does not trust the adapter's path. It splits the raw path,
//! decodes each segment exactly once and rejects anything ambiguous, so a
//! segment can never smuggle in a `/`, a dot segment or invalid UTF-8.

use crate::ir::{Pattern, Seg};
use crate::value::bytes_eq;
use alloc::vec::Vec;

/// Why a request path was rejected.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum PathError {
    /// The path is empty or does not start with `/`.
    NoLeadingSlash,
    /// The path contains `?` or `#`; the adapter must strip them.
    QueryOrFragment,
    /// The path has an empty segment, from `//` or a trailing `/`. Routers
    /// disagree about such paths, so only the root `/` may end in a slash.
    EmptySegment,
    /// A `%` is not followed by two hex digits.
    BadPercentEncoding,
    /// A segment decodes to `.` or `..`.
    DotSegment,
    /// A segment decodes to something containing `/` or NUL.
    ForbiddenByte,
    /// A segment decodes to bytes that are not valid UTF-8.
    InvalidUtf8,
}

/// Splits a raw path into decoded segments.
///
/// The path must start with `/`, contain no `?` or `#`, and have no empty
/// segments: `//` and a trailing `/` are rejected rather than collapsed,
/// because a router may not collapse them. Each segment is percent-decoded
/// exactly once. `/` gives zero segments.
pub fn canonicalize(raw: &[u8]) -> Result<Vec<Vec<u8>>, PathError> {
    let encoded = split_raw(raw)?;
    let mut out = Vec::new();
    let mut i = 0;
    while i < encoded.len() {
        out.push(decode_segment(&encoded[i])?);
        i += 1;
    }
    Ok(out)
}

/// Checks the path shape and splits it on `/`, skipping empty segments.
fn split_raw(raw: &[u8]) -> Result<Vec<Vec<u8>>, PathError> {
    if raw.is_empty() || raw[0] != b'/' {
        return Err(PathError::NoLeadingSlash);
    }
    let mut segments = Vec::new();
    let mut current: Vec<u8> = Vec::new();
    let mut i = 1;
    while i < raw.len() {
        let b = raw[i];
        if b == b'?' || b == b'#' {
            return Err(PathError::QueryOrFragment);
        }
        if b == b'/' {
            if current.is_empty() {
                return Err(PathError::EmptySegment);
            }
            segments.push(current);
            current = Vec::new();
        } else {
            current.push(b);
        }
        i += 1;
    }
    if !current.is_empty() {
        segments.push(current);
    } else if raw.len() > 1 {
        // A trailing `/`: only the root path may end in one.
        return Err(PathError::EmptySegment);
    }
    Ok(segments)
}

/// Percent-decodes one segment once and validates the result.
fn decode_segment(seg: &[u8]) -> Result<Vec<u8>, PathError> {
    let mut out = Vec::new();
    let mut i = 0;
    while i < seg.len() {
        if seg[i] == b'%' {
            if seg.len() - i < 3 {
                return Err(PathError::BadPercentEncoding);
            }
            match (hex_value(seg[i + 1]), hex_value(seg[i + 2])) {
                (Some(hi), Some(lo)) => out.push(hi * 16 + lo),
                _ => return Err(PathError::BadPercentEncoding),
            }
            i += 3;
        } else {
            out.push(seg[i]);
            i += 1;
        }
    }
    validate_segment(&out)?;
    Ok(out)
}

fn hex_value(b: u8) -> Option<u8> {
    match b {
        b'0'..=b'9' => Some(b - b'0'),
        b'a'..=b'f' => Some(b - b'a' + 10),
        b'A'..=b'F' => Some(b - b'A' + 10),
        _ => None,
    }
}

fn validate_segment(seg: &[u8]) -> Result<(), PathError> {
    if bytes_eq(seg, b".") || bytes_eq(seg, b"..") {
        return Err(PathError::DotSegment);
    }
    let mut i = 0;
    while i < seg.len() {
        if seg[i] == b'/' || seg[i] == 0 {
            return Err(PathError::ForbiddenByte);
        }
        i += 1;
    }
    if utf8_valid(seg) {
        Ok(())
    } else {
        Err(PathError::InvalidUtf8)
    }
}

/// Checks that the bytes are well-formed UTF-8: no overlong forms, no
/// surrogates, nothing above U+10FFFF.
fn utf8_valid(s: &[u8]) -> bool {
    let mut i = 0;
    while i < s.len() {
        let n = utf8_char_len(s, i);
        if n == 0 {
            return false;
        }
        i += n;
    }
    true
}

/// The length of the well-formed character starting at `i`, or 0 if there is
/// none. The caller guarantees `i < s.len()`.
fn utf8_char_len(s: &[u8], i: usize) -> usize {
    match s[i] {
        0x00..=0x7F => 1,
        0xC2..=0xDF => tail_ok(s, i, 1, 0x80, 0xBF),
        0xE0 => tail_ok(s, i, 2, 0xA0, 0xBF),
        0xED => tail_ok(s, i, 2, 0x80, 0x9F),
        0xE1..=0xEC | 0xEE..=0xEF => tail_ok(s, i, 2, 0x80, 0xBF),
        0xF0 => tail_ok(s, i, 3, 0x90, 0xBF),
        0xF1..=0xF3 => tail_ok(s, i, 3, 0x80, 0xBF),
        0xF4 => tail_ok(s, i, 3, 0x80, 0x8F),
        _ => 0,
    }
}

/// Checks the `tail` bytes after the lead byte at `i`: the first must be in
/// `lo..=hi`, the rest must be continuation bytes. Returns the character
/// length, or 0 when the bytes are malformed or missing.
fn tail_ok(s: &[u8], i: usize, tail: usize, lo: u8, hi: u8) -> usize {
    if s.len() - i <= tail {
        return 0;
    }
    if s[i + 1] < lo || s[i + 1] > hi {
        return 0;
    }
    let mut k = 2;
    while k <= tail {
        if s[i + k] & 0xC0 != 0x80 {
            return 0;
        }
        k += 1;
    }
    tail + 1
}

/// A value captured by a pattern.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Capture {
    /// The segment a `Var` matched.
    One(Vec<u8>),
    /// The segments the rest capture matched; empty for zero segments.
    Rest(Vec<Vec<u8>>),
}

/// Copies a byte string.
fn copy_bytes(s: &[u8]) -> Vec<u8> {
    let mut out = Vec::new();
    let mut i = 0;
    while i < s.len() {
        out.push(s[i]);
        i += 1;
    }
    out
}

/// Matches a canonical path against a pattern.
///
/// Without `rest` the path must have exactly as many segments as the pattern;
/// with `rest` the pattern must match a prefix. Returns the captures in
/// order: each `Var` as `One`, then `Rest` when the pattern has a rest,
/// empty when it matched zero segments.
pub fn match_pattern(p: &Pattern, segments: &[Vec<u8>]) -> Option<Vec<Capture>> {
    let wrong_length = if p.rest {
        segments.len() < p.segs.len()
    } else {
        segments.len() != p.segs.len()
    };
    if wrong_length {
        return None;
    }
    let mut captures = Vec::new();
    let mut i = 0;
    while i < p.segs.len() {
        match &p.segs[i] {
            Seg::Lit(lit) => {
                if !bytes_eq(lit, &segments[i]) {
                    return None;
                }
            }
            Seg::Var => captures.push(Capture::One(copy_bytes(&segments[i]))),
        }
        i += 1;
    }
    if p.rest {
        let mut tail = Vec::new();
        let mut j = p.segs.len();
        while j < segments.len() {
            tail.push(copy_bytes(&segments[j]));
            j += 1;
        }
        captures.push(Capture::Rest(tail));
    }
    Some(captures)
}
