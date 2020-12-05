mod chacha20poly1305;

pub use chacha20poly1305::Chacha20Poly1305;

#[derive(Debug, PartialEq)]
pub struct Error(pub String);
