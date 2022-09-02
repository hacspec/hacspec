#![allow(dead_code)]

use hacspec_enum_default::*;

#[derive(Debug, HacspecDefault)]
enum Simple {
    A,
    B,
    C,
}

#[derive(Debug, HacspecDefault)]
enum Empty {}

#[derive(Debug, HacspecDefault)]
#[repr(u8)]
enum Values {
    A = 1,
    B = 5,
    C = 10,
}

#[derive(Debug, HacspecDefault)]
enum Complex {
    A(u8),
    B(String),
    C(u16),
}

#[derive(Debug, HacspecDefault)]
enum ComplexGenericInner {
    A(Vec::<u8>),
    B(String),
    C(u16),
}
