use hacspec_hmac::*;
use hacspec_lib::*;

// HASH_LEN for SHA256
// XXX: HMAC should probably expose this
const HASH_LEN: usize = 256 / 8;

#[derive(Debug)]
pub enum Error {
    InvalidOutputLength,
}

pub type ByteSeqResult = Result<ByteSeq, Error>;

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

/// Compute ceil(a/b), returning a usize.
fn div_ceil(a: usize, b: usize) -> usize {
    let mut q = a / b;
    if a % b != 0 {
        q = q + 1;
    }
    q
}

fn check_output_limit(l: usize) -> Result<usize, Error> {
    let n = div_ceil(l, HASH_LEN);
    if n <= 255 {
        Result::<usize, Error>::Ok(n)
    } else {
        Result::<usize, Error>::Err(Error::InvalidOutputLength)
    }
}

/// Expand a key prk, using potentially empty info, and output length l.
/// Key prk must be at least of length HASH_LEN.
/// Output length l can be at most 255*HASH_LEN.
pub fn expand(prk: &ByteSeq, info: &ByteSeq, l: usize) -> ByteSeqResult {
    let n = check_output_limit(l)?;
    let mut t_i = PRK::new();
    let mut t = ByteSeq::new(n * PRK::capacity());
    for i in 0..n {
        let hmac_txt_in = if i == 0 {
            build_hmac_txt(&ByteSeq::new(0), info, U8((i as u8) + 1u8))
        } else {
            build_hmac_txt(&ByteSeq::from_seq(&t_i), info, U8((i as u8) + 1u8))
        };
        t_i = hmac(prk, &hmac_txt_in);
        t = t.update(i * t_i.len(), &t_i);
    }
    ByteSeqResult::Ok(t.slice(0, l))
}
