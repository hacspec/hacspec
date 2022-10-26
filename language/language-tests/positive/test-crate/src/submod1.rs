mod another_submod1_file;
pub use another_submod1_file::*;

#[derive(Clone)]
pub struct MyTupleType(pub u16, pub u8);
