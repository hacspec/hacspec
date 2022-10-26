use hacspec_lib::*;

pub fn foo(x: Option<u32>) -> bool {
    match x {
        Option::<u32>::None => {
            // hello, world!
            false
        }
        Option::<u32>::Some(_) => true,
    }
}

pub fn final_if(a: Seq<u8>) -> Seq<u8> {
    if true {
        a
    } else {
        a
    }
}
