#![allow(dead_code)]
#![allow(non_snake_case)]

use hacspec_lib::prelude::*;

use rand::{Fill, Rng};

pub(crate) fn get_expected(op: &'static str, a: &String, b: &String) -> String {
    let expected = std::process::Command::new("python")
        .args(&["tests/math_helper.py", a, op, b])
        .output()
        .expect("failed to execute python test helper");
    let expected = String::from_utf8_lossy(&expected.stdout)
        .replace("\n", "")
        .replace("\r", "");
    // Python2 appends an L.
    expected.replace("L", "")
}

pub(crate) fn random_hex_string(len: usize) -> String {
    const HEX_CHARS: [char; 16] = [
        '0', '1', '2', '3', '4', '5', '6', '7', '8', '9', 'a', 'b', 'c', 'd', 'e', 'f',
    ];

    let mut res = "".to_string();
    let mut rng = rand::thread_rng();
    for _ in 0..len {
        res.push(HEX_CHARS[rng.gen_range(0..HEX_CHARS.len())]);
    }
    res = res.trim_start_matches('0').to_string();
    if res.len() == 0 {
        res.push('0');
    }
    let mut start = String::from("0x");
    start.push_str(&res);
    start
}

pub(crate) fn get_random_numbers<T: Integer>() -> (String, T, String, T) {
    let a = random_hex_string(T::NUM_BITS as usize >> 3);
    let b = random_hex_string(T::NUM_BITS as usize >> 3);
    let a_t = T::from_hex_string(&a);
    let b_t = T::from_hex_string(&b);
    (a, a_t, b, b_t)
}

pub(crate) fn random_bytes<A: Default + Fill>() -> A {
    let mut out = A::default();
    rand::thread_rng().fill(&mut out);
    out
}

macro_rules! implement_public_rand {
    ($t:ty, $name:ident) => {
        pub(crate) fn $name(len: usize) -> Vec<$t> {
            (0..len).map(|_| rand::random::<$t>()).collect()
        }
    };
}
implement_public_rand!(u8, get_random_vec_u8);
implement_public_rand!(u16, get_random_vec_u16);
implement_public_rand!(u32, get_random_vec_u32);
implement_public_rand!(u64, get_random_vec_u64);
implement_public_rand!(u128, get_random_vec_u128);

macro_rules! implement_rand {
    ($t:ty, $base:ty, $name:ident) => {
        pub(crate) fn $name(len: usize) -> Vec<$t> {
            (0..len).map(|_| rand::random::<$base>().into()).collect()
        }
    };
}
implement_rand!(U8, u8, get_random_vec_U8);
implement_rand!(U16, u16, get_random_vec_U16);
implement_rand!(U32, u32, get_random_vec_U32);
implement_rand!(U64, u64, get_random_vec_U64);
implement_rand!(U128, u128, get_random_vec_U128);
