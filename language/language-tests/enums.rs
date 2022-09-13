use hacspec_lib::*;

pub enum Foo {
    CaseX,
    CaseY(u8, Seq<u32>),
}

pub struct Bar(pub u32);

pub fn baz(x: Foo) -> Bar {
    let z: Bar = Bar(0u32);
    let Bar(z) = z;
    let y = match x {
        Foo::CaseX => Foo::CaseY(z as u8, Seq::<u32>::new(1)),
        Foo::CaseY(0u8, b) => Foo::CaseY(1u8, b),
        Foo::CaseY(_,_) => Foo::CaseY(1u8, Seq::<u32>::new(1)),
    };
    match y {
        Foo::CaseX => Bar(0u32),
        Foo::CaseY(a, _b) => Bar(a as u32),
    }
}

pub fn baz_im(x: Foo) {
    let z: Bar = Bar(0u32);
    let Bar(z) = z;
    let _a = z as u8;
}
