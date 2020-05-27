// Import hacspec and all needed definitions.
use hacspec::prelude::*;

// linked in from ../sha2/ example
use crate::sha2;
// linked in from ../hmac/ example
use crate::hmac;

use hmac::hmac;

const HASH_LEN: usize = sha2::HASH_SIZE;
bytes!(PRK, HASH_LEN);

// TODO: do we want to allow Option?
/// Extract a pseudo-random key from input key material (IKM) and optionally a salt.
/// Note that salt can be empty Bytes.
pub fn extract(salt: &ByteSeq, ikm: &ByteSeq) -> PRK {
    let mut salt_or_zero = ByteSeq::new(HASH_LEN);
    if salt.len() > 0 {
        salt_or_zero = ByteSeq::from_seq(salt)
    };
    PRK::from_seq(&hmac(&salt_or_zero, ikm))
}

fn build_hmac_txt(t: &ByteSeq, info: &ByteSeq, iteration: U8) -> ByteSeq {
    let mut out = ByteSeq::new(t.len() + info.len() + 1);
    out = out.update(0, t);
    out = out.update(t.len(), info);
    out[t.len() + info.len()] = iteration;
    out
}

// DM: determine if needed, this is impossible to formalize
/// Compute ceil(a/b), returning a u64.
/// Note that float-uint conversion might be lossy.
fn div_ceil(a: usize, b: usize) -> u64 {
    (f64::ceil((a as f64) / (b as f64))) as u64
}

/// Expand a key prk, using potentially empty info, and output length l.
/// Key prk must be at least of length HASH_LEN.
/// Output length l can be at most 255*HASH_LEN.
pub fn expand(prk: &ByteSeq, info: &ByteSeq, l: usize) -> ByteSeq {
    let n = div_ceil(l, HASH_LEN);
    debug_assert!(n < u8::max_value().into());
    let n = n as u8;

    let mut t_i = hmac::PRK::new();
    let mut t = ByteSeq::new(n as usize * PRK::capacity());
    for i in 0..n {
        let hmac_txt_in = if i == 0 {
            build_hmac_txt(&ByteSeq::new(0), info, U8(i + 1))
        } else {
            build_hmac_txt(&ByteSeq::from_seq(&t_i), info, U8(i + 1))
        };
        t_i = hmac(prk, &hmac_txt_in);
        t = t.update(i as usize * t_i.len(), &t_i);
    }
    // TODO: slice is overloaded (impl Sub and slice). This should get fixed ...
    t.slice(0, l)
}
