
pub use crate::test_vectors::*;
pub use crate::*;
use rand::Rng;
// re-export serde and file IO
pub use serde::{self, Deserialize, Serialize, de::DeserializeOwned};
pub use serde_json::Value;
pub use std::fs::File;
pub use std::io::{BufReader, prelude::*};

 /// Random byte array
pub fn random_byte() -> usize {
    let random_byte = rand::thread_rng().gen::<usize>();
    random_byte
}
