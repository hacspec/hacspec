use hacspec_lib::*;

pub enum Baz {
    CaseX,
    CaseY(Result<u8, U8>),
}

pub enum Foo {
    CaseX(Baz),
    CaseY(u8, Seq<u32>),
}

pub struct Bar(pub u32);

pub fn baz(x: Foo) -> Bar {
    let z: Bar = Bar(0u32);
    let Bar(z) = z;
    let y = match x {
        Foo::CaseX(Baz::CaseY(Result::<u8, U8>::Ok(x))) => {
            Foo::CaseY(z as u8 + x, Seq::<u32>::new(1))
        }
        Foo::CaseX(_) => Foo::CaseX(Baz::CaseX),
        Foo::CaseY(0u8, b) => Foo::CaseY(1u8, b),
        Foo::CaseY(_, _) => Foo::CaseY(1u8, Seq::<u32>::new(1)),
    };
    match y {
        Foo::CaseX(_) => Bar(0u32),
        Foo::CaseY(a, _b) => Bar(a as u32),
    }
}

pub fn baz_im(x: Foo) {
    let z: Bar = Bar(0u32);
    let Bar(z) = z;
    let a = z as u8;
}
