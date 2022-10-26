use hacspec_lib::*;

pub fn foo(x: Seq<U8>, y: Seq<U8>) -> Seq<U8> {
    x + y
}

pub fn bar(x: Seq<U8>, y: Seq<U8>) -> Seq<U8> {
    x | y
}
