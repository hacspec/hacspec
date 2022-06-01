// Import hacspec and all needed definitions.
use hacspec_lib::*;

// let, let mut, reassignment
pub fn let_test(st: usize) -> usize {
    let a = st;
    let mut st = a;
    st = 35usize;
    st
}

// conditional
pub fn if_cond(b: bool) -> u32 {
    if b {
        32u32
    } else {
        4u32
    }
}

pub fn for_loop(i : usize) -> usize {
    let mut sum = 0usize;
    for i in 0..i {
        sum = sum + i;
    }
    sum
}

pub fn result_test(i : usize) -> Result<u32, usize> {
    let mut sum = 0usize;
    for i in 0..i {
        sum = sum + i;
        for_loop(i);
        let_test(i);
        Result::<u32, usize>::Err (i)?;
    }
    Result::<u32, usize>::Ok (sum as u32)
}

// conditional
pub fn if_inlinecond(v: u32) -> Result<u32, bool> {
    let x = if v < 0u32 {
        Result::<u32, bool>::Ok (4u32)
    } else {
        Result::<u32, bool>::Err (true)
    }?;
    Result::<u32, bool>::Ok (v)
}

// conditional
pub fn if_inlinecond2(v: u32) -> Result<u32, bool> {
    if v < 0u32 {
        Result::<u32, bool>::Ok (4u32);
    } else {
        Result::<u32, bool>::Err (true)?;
    };
    Result::<u32, bool>::Ok (v)
}
