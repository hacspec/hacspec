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

pub fn match_literals(xu8: u8, xu32: u32, xi64: i64, flag: bool) -> (u8, u32, i64) {
    (
        match xu8 {
            0u8 => 1u8,
            1u8 => 2u8,
            _ => 0u8,
        },
        match xu32 {
            0u32 => 1u32,
            1u32 => 2u32,
            _ => 0u32,
        },
        match (xi64, xu8, flag) {
            (4i64, 4u8, true) => 1i64,
            // The following line is commented out because of
            // FStarLang/FStar#2415 (F*'s parser cannot handle
            // negative patterns)
            // (-1i64, _, false) => 2i64,
            (_, 12u8, _) => 12i64,
            _ => 0i64,
        },
    )
}

pub fn match_integers_usize(x: usize) -> usize {
    match x {
        0 => 1,
        1 => 2,
        _ => 0,
    }
}

pub fn match_integers_u8(x: u8) -> u8 {
    match x {
        0u8 => 1u8,
        1u8 => 2u8,
        _ => 0u8,
    }
}

pub fn baz_im(x: Foo) {
    let z: Bar = Bar(0u32);
    let Bar(z) = z;
    let a = z as u8;
}

struct Foobar(u8, u8, u8);

fn field_accessors() -> u8 {
    Foobar(0u8, 1u8, 2u8).0 + Foobar(0u8, 1u8, 2u8).1 + Foobar(0u8, 1u8, 2u8).2 + (10u8, 20u8).1
}
