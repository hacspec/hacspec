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

// fn xor(x_inp : u64, y_inp : u64) -> u64 {
//     v1 ^ v2a
// }

// fn otp(x : Seq<u64>, y : Seq<u64>) -> Result<Seq<u64>, ()> {
//     if x.len() != y.len() {
//         Result::<Seq<u64>, ()>::Err (())?;
//     }
    
//     let mut z : Seq<u64> = Seq::<u64>::new(x.len());
//     for i in 1..x.len() {
//         z[i] = xor(x[i], y[i])
//     }
//     Result::<Seq<u64>, ()>::Ok(z)
// }

// fn xor2(x : u64, y : u64) -> u64 {
//    x ^ y
// }

// fn otp2(x : Seq<u64>, y : Seq<u64>) -> Seq<u64> {
//     let mut z : Seq<u64> = Seq::<u64>::new(x.len());
//     for i in 1..x.len() {
//         z[i] = xor(x[i], y[i])
//     }
//     z
// }
