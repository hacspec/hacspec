use hacspec_lib::*;

// Jasmin
fn xor(x : u64, y : u64) -> u64 {
   let mut r : u64 = x;
   r = r ^ y;
   r
}

fn otp(x : Seq<u64>, y : Seq<u64>) -> Result<Seq<u64>, ()> {
    if x.len() != y.len() {
        Result::<Seq<u64>, ()>::Err (())?;
    }
    
    let mut z : Seq<u64> = Seq::<u64>::new(x.len());
    for i in 1..x.len() {
        z[i] = xor(x[i], y[i])
    }
    Result::<Seq<u64>, ()>::Ok(z)
}
