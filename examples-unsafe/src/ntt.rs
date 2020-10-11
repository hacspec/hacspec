//! Number theoretic transform
//!
//! This implements NTT for fast polynomial multiplication as used in schemes
//! like Kyber.
//!
//! Let Rq denote the ring Zq[X]/(Xn+1).
//!
//! Polynomial multiplication on Rq has complexity O(n^2) (see hacspec lib for
//! an example).
//! NTT allows to implement the multiplication in O(n log(n)).
//!
//! Kyber parameters:
//! * q = 3329
//! * q−1 = 28·13
//!

use hacspec_lib::prelude::*;

// Kyber 1024
pub const MONT: i16 = 2285; // 2^16 % Q
pub const QINV: i64 = 62209; // q^(-1) mod 2^16
pub const KYBER_N: i16 = 256;
pub const KYBER_Q: i64 = 3329;
pub const KYBER_POLYBYTES: usize = 384;
pub const KYBER_SYMBYTES: usize = 32;
pub const KYBER_ROOT_OF_UNITY: i16 = 17;

// Polynomials
array!(Poly, 256, i16);

// Zetas constants
array!(Zetas, 128, i16);

fn get_zetas() -> (Zetas, Zetas) {
    let zetas: Zetas = Zetas::from_native_slice(&[
        2285, 2571, 2970, 1812, 1493, 1422, 287, 202, 3158, 622, 1577, 182, 962, 2127, 1855, 1468,
        573, 2004, 264, 383, 2500, 1458, 1727, 3199, 2648, 1017, 732, 608, 1787, 411, 3124, 1758,
        1223, 652, 2777, 1015, 2036, 1491, 3047, 1785, 516, 3321, 3009, 2663, 1711, 2167, 126,
        1469, 2476, 3239, 3058, 830, 107, 1908, 3082, 2378, 2931, 961, 1821, 2604, 448, 2264, 677,
        2054, 2226, 430, 555, 843, 2078, 871, 1550, 105, 422, 587, 177, 3094, 3038, 2869, 1574,
        1653, 3083, 778, 1159, 3182, 2552, 1483, 2727, 1119, 1739, 644, 2457, 349, 418, 329, 3173,
        3254, 817, 1097, 603, 610, 1322, 2044, 1864, 384, 2114, 3193, 1218, 1994, 2455, 220, 2142,
        1670, 2144, 1799, 2051, 794, 1819, 2475, 2459, 478, 3221, 3021, 996, 991, 958, 1869, 1522,
        1628,
    ]);
    let zetas_inv: Zetas = Zetas::from_native_slice(&[
        1701, 1807, 1460, 2371, 2338, 2333, 308, 108, 2851, 870, 854, 1510, 2535, 1278, 1530, 1185,
        1659, 1187, 3109, 874, 1335, 2111, 136, 1215, 2945, 1465, 1285, 2007, 2719, 2726, 2232,
        2512, 75, 156, 3000, 2911, 2980, 872, 2685, 1590, 2210, 602, 1846, 777, 147, 2170, 2551,
        246, 1676, 1755, 460, 291, 235, 3152, 2742, 2907, 3224, 1779, 2458, 1251, 2486, 2774, 2899,
        1103, 1275, 2652, 1065, 2881, 725, 1508, 2368, 398, 951, 247, 1421, 3222, 2499, 271, 90,
        853, 1860, 3203, 1162, 1618, 666, 320, 8, 2813, 1544, 282, 1838, 1293, 2314, 552, 2677,
        2106, 1571, 205, 2918, 1542, 2721, 2597, 2312, 681, 130, 1602, 1871, 829, 2946, 3065, 1325,
        2756, 1861, 1474, 1202, 2367, 3147, 1752, 2707, 171, 3127, 3042, 1907, 1836, 1517, 359,
        758, 1441,
    ]);

    (zetas, zetas_inv)
}

pub fn i64_to_i16(a: i64) -> i16 {
    let b = a.to_be_bytes();
    let mut out_b = [0u8; 2];
    out_b.clone_from_slice(&b[6..8]);
    i16::from_be_bytes(out_b)
}

pub fn i32_to_i16(a: i32) -> i16 {
    let b = a.to_be_bytes();
    let mut out_b = [0u8; 2];
    out_b.clone_from_slice(&b[2..4]);
    i16::from_be_bytes(out_b)
}

pub fn i64_to_i32(a: i64) -> i32 {
    let b = a.to_be_bytes();
    let mut out_b = [0u8; 4];
    out_b.clone_from_slice(&b[4..8]);
    i32::from_be_bytes(out_b)
}

pub fn montgomery_reduce(a: i32) -> i16 {
    let large_a = i64::from(a);
    let u = i64_to_i16(large_a * QINV);
    let large_u = i64::from(u);
    let t = large_u * KYBER_Q;
    let t = i32::from(a) - i64_to_i32(t);
    let t = t >> 16;
    t as i16
}

pub fn barrett_reduce(a: i16) -> i16 {
    const V: i32 = 20159;
    let large_a = i32::from(a);
    let t = (V * large_a) >> 26;
    let t = i32_to_i16(t) * (KYBER_Q as i16);
    let t = a - t;
    t as i16
}

pub fn fqmul(a: i16, b: i16) -> i16 {
    let a = i32::from(a);
    let b = i32::from(b);
    montgomery_reduce(a * b)
}

pub fn ntt(p: Poly) -> Poly {
    let (zetas, _zetas_inv) = get_zetas();

    let mut out = p.clone();
    let mut len = 128;
    let mut k = 1;
    loop {
        if len < 2 {
            break;
        }

        let mut start = 0;
        loop {
            if start >= 256 {
                break;
            }

            let zeta = zetas[k];
            k = k + 1;
            let mut j = start;
            loop {
                if j >= (start + len) {
                    break;
                }

                let t = fqmul(zeta, out[j + len]);
                let tmp: i16 = out[j];
                out[j + len] = tmp.wrapping_sub(t);
                out[j] = tmp.wrapping_add(t);

                j = j + 1;
            }

            start = j + len;
        }

        len = len >> 1;
    }

    out
}

pub fn ntt_inv(p: Poly) -> Poly {
    let (_zetas, zetas_inv) = get_zetas();

    let mut out = p.clone();

    let mut k = 0;
    let mut len = 2;
    loop {
        if len > 128 {
            break;
        }

        let mut start = 0;
        loop {
            if start >= 256 {
                break;
            }

            let zeta = zetas_inv[k];
            k = k + 1;
            let mut j = start;
            loop {
                if j >= (start + len) {
                    break;
                }

                let t = out[j];
                out[j] = barrett_reduce(t + out[j + len]);
                out[j + len] = t - out[j + len];
                out[j + len] = fqmul(zeta, out[j + len]);

                j = j + 1;
            }

            start = j + len;
        }

        len = len << 1;
    }

    for i in 0..256 {
        out[i] = fqmul(out[i], zetas_inv[127]);
    }

    out
}
