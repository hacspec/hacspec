use hacspec_lib::*;

pub enum Foo {
    CaseX,
    CaseY(U8, Seq<u32>),
}

pub fn bar(x: Foo) -> Foo {
    let y = match x {
        Foo::CaseX => Foo::CaseX,
        Foo::CaseY(a, b) => Foo::CaseY(a + U8(1u8), b),
    };
    y
}
