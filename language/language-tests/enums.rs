use hacspec_lib::*;

pub enum Foo {
    CaseX,
    CaseY(U8, Seq<u32>),
}

pub struct Bar(pub u32);

pub fn baz(x: Foo) -> Bar {
    let z: Bar = Bar(0u32);
    let Bar(z) = z;
    let y = match x {
        Foo::CaseX => Foo::CaseY(U8(z as u8), Seq::<u32>::new(1)),
        Foo::CaseY(a, b) => Foo::CaseY(a + U8(1u8), b),
    };
    match y {
        Foo::CaseX => Bar(0u32),
        Foo::CaseY(a, _b) => Bar(U32_from_U8(a).declassify()),
    }
}
