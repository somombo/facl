//! Lexer-free recursive-descent parser for facl rules files.
//!
//! [`parse`] turns source text into the [`facl_core::Service`] tree. Errors
//! carry byte spans; [`line_col`] turns an offset into a 1-based line and
//! column.

mod parser;

pub use parser::{ParseError, parse};

/// The deepest nesting of `match` blocks and expressions the parser accepts.
pub const MAX_NESTING: u32 = 64;

/// Converts a byte offset into a 1-based `(line, column)`. Columns count
/// characters, not bytes. An offset past the end gives the position just after
/// the last character.
pub fn line_col(source: &str, offset: u32) -> (u32, u32) {
    let end = (offset as usize).min(source.len());
    let mut line = 1;
    let mut col = 1;
    for b in &source.as_bytes()[..end] {
        if *b == b'\n' {
            line += 1;
            col = 1;
        } else if b & 0xC0 != 0x80 {
            col += 1;
        }
    }
    (line, col)
}

#[cfg(test)]
mod tests;
