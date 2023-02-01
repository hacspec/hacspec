use hacspec_lib::*;

// Jasmin
fn xor(x_inp : u64, y_inp : u64) -> u64 {
    let mut x : u64 = x_inp;
    let mut y : u64 = y_inp;
    let v = x;
    let mut r : u64 = v;
    let v1 = r;
    let v2 = y;
    r = v1 ^ v2;
    r
}
