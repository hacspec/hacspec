//!
//! This crate can be used for tests that accompany hacspecs.
//!

pub mod prelude;
pub mod rand;
pub mod test_vectors;

/// Convert a hex string to a byte vector.
pub fn hex_to_bytes(hex: &str) -> Vec<u8> {
    assert!(hex.len() % 2 == 0);
    let mut bytes = Vec::new();
    for i in 0..(hex.len() / 2) {
        bytes.push(u8::from_str_radix(&hex[2 * i..2 * i + 2], 16).unwrap());
    }
    bytes
}
