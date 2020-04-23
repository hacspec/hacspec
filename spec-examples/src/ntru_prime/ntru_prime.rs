// Import hacspec and all needed definitions.
use hacspec::prelude::*;


/// Struct to decide NtruVersion
pub struct NtruVersion{
    pub p:i128,
    pub q:i128,
    pub w:i128,
}
#[macro_export]
macro_rules! ntru_v {
    ($t:expr)  => {
        {
        // TODO needs to be removed, just for demonstration
        if $t == -1{
            NtruVersion{p:191,q:397,w:68}
        }
        else if $t == 0{
            NtruVersion{p:761,q:4591,w:286}
        } else if $t == 1{
            NtruVersion{p:653,q:4621,w:288}
        } else {
            NtruVersion{p:857,q:5167,w:322}
        }

        }
    };

}


///This function creates a random polynom with w many -1 or 1 and with the highes degree of h_deg.
fn create_rand_poly(w: i128, h_deg: usize) -> Vec<(usize, i128)> {
    let mut counter = 0;
    let mut pos;
    let mut polynom: Vec<(usize, i128)> = Vec::new();
    while w != counter {
        pos = rand::thread_rng().gen_range(0, h_deg);
        let c_val = rand::thread_rng().gen_range(0, 2);
        if polynom.contains(&(pos, -1)) || polynom.contains(&(pos, 1)) {
            continue;
        }
        // if c_val = 0 -> polynom[pos] = -1, else 1
        polynom.push((pos, c_val * 2 - 1));
        counter = counter + 1;
    }

    return polynom;
}
///Creates a random polynom with the inverse, if there is no inverse this function return []
//TODO for tests pub

pub fn create_invertable_poly(n: NtruVersion, modulus: i128) -> ([(usize, u128); 288], Vec<u128>) /*-> Result<(),Box<dyn Error>>*/
{
    poly!(ZxN, u128, 653, 3, &[(0, 2), (1, 2), (653, 1)]);
    if n.q == modulus {
        poly!(ZxN, u128, 653, 4621, &[(0, 4620), (1, 4620), (653, 1)]);

    }
    let mut f_vec = create_rand_poly(n.w, 653);
    let mut f_array: [(usize, u128); 288] = [(0, 0); 288];
    let mut index = 0;
    for tmp in f_vec.iter() {
        if tmp.1 < 0 {
            f_array[index] = (tmp.0,(tmp.1 + modulus) as u128);
            index = index + 1;
            continue;
        }
        f_array[index] = (tmp.0,tmp.1 as u128);
        index = index + 1;
    }

    let m = ZxN::new(&f_array);
    return (
        f_array,
        extended_euclid(&m.poly, &m.irr, modulus as u128).unwrap_or_default(),
    );
}

pub fn key_gen() -> (Vec<u128>, (Vec<u128>, Vec<u128>)) {
    //TODO just for test
    let n_v = ntru_v!(1);
    let q = *(&n_v.q);
    println!("generating key...");
    let mut poly_g = create_invertable_poly(n_v, 3);
    while poly_g.1.len() == 0 {
        poly_g = create_invertable_poly(ntru_v!(1), 3);
    }
    let n_v = ntru_v!(1);
    let mut poly_f = create_invertable_poly(n_v, q);
    while poly_f.1.len() == 0 {
        poly_f = create_invertable_poly(ntru_v!(1), q);
    }
    let n_v = ntru_v!(1);
    //if n_v.p == 653 {
        poly!(ZxQ, u128, 653, 4621, [(0, 4620), (1, 4620), (653, 1)]);
        // TODO there may be an efficent alternativ
        let mut f_array:[u128;653] = [0;653];
        let mut index = 0;
        while index < 653{
            f_array[index] = poly_f.1[index];
            index = index + 1;
        }

        let f_inv = ZxQ::new_full(f_array);
        let g = ZxQ::new(&poly_g.0);
        let h = g.mul(f_inv.add(f_inv.add(f_inv)));
        let f = ZxQ::new(&poly_f.0);
        println!("key Gen done!");
        return (h.poly.to_vec(), (f.poly.to_vec(), poly_g.1));
    //}

}
