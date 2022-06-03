// based on https://datatracker.ietf.org/doc/html/rfc8017
use hacspec_lib::*;
use hacspec_sha256::*;

pub const BIT_SIZE: u32  = 1024u32;
pub const BYTE_SIZE: u32 = 1024u32 / 8u32;
const HLEN: usize = 32usize; // sha256 / 8 = 32

unsigned_public_integer!(RSAInt, 1024);

#[derive(Debug)]
pub enum Error {
    InvalidLength,
    MessageTooLarge,
    MessageTooLargeVerify,
    InvalidProof,
}

pub type PK = (RSAInt, RSAInt);
pub type SK = (RSAInt, RSAInt);
pub type KeyPair = (PK, SK);
pub type ByteSeqResult = Result<ByteSeq, Error>;
pub type RSAIntResult = Result<RSAInt, Error>;

pub fn rsaep(pk: PK, m: RSAInt) -> RSAIntResult {
    let (n, e) = pk;
    if m > n - RSAInt::ONE() {
        RSAIntResult::Err(Error::MessageTooLarge)
    } else {
        RSAIntResult::Ok(m.pow_mod(e, n))
    }
}

pub fn rsadp(sk: SK, c: RSAInt) -> RSAIntResult {
    let (n, d) = sk;
    if c > n - RSAInt::ONE() {
        RSAIntResult::Err(Error::MessageTooLarge)
    } else {
        RSAIntResult::Ok(c.pow_mod(d, n))
    }
}

pub fn rsasp1(sk: SK, m: RSAInt) -> RSAIntResult {
    let (n, d) = sk;
    if m > n - RSAInt::ONE() {
        RSAIntResult::Err(Error::MessageTooLarge)
    } else {
        RSAIntResult::Ok(m.pow_mod(d, n))
    }
}

pub fn rsavp1(pk: PK, s: RSAInt) -> RSAIntResult {
    let (n, e) = pk;
    if s > n - RSAInt::ONE() {
        RSAIntResult::Err(Error::MessageTooLargeVerify)
    } else {
        RSAIntResult::Ok(s.pow_mod(e, n))
    }
}

pub fn i2osp(x: RSAInt, x_len: u32) -> ByteSeqResult {
    if x >= (RSAInt::exp(RSAInt::from_literal(256u128), x_len)) 
            && x_len != BYTE_SIZE {
        ByteSeqResult::Err(Error::InvalidLength)
    } else {
        ByteSeqResult::Ok(RSAInt::to_byte_seq_be(x)
            .slice((BYTE_SIZE - x_len) as usize, x_len as usize))
    }
}

pub fn os2ip(x: &ByteSeq) -> RSAInt {
    RSAInt::from_byte_seq_be(x)
}

// https://datatracker.ietf.org/doc/html/rfc8017#appendix-B.2.1
pub fn mgf1(mgf_seed: &ByteSeq, mask_len: usize) -> ByteSeqResult {
    let mut result = ByteSeqResult::Err(Error::InvalidLength);
    if mask_len < 2usize^32usize * HLEN {
        let mut t = ByteSeq::new(0);
        for i in 0..((mask_len + 32) / 32) {
            let x = i2osp(RSAInt::from_literal(i as u128), 4u32)?;
            t = t.concat(&sha256(&mgf_seed.concat(&x)));
        }
        result = ByteSeqResult::Ok(t.slice(0, mask_len))
    }
    result
}

#[cfg(test)]
extern crate quickcheck;
#[cfg(test)]
#[macro_use(quickcheck)]
extern crate quickcheck_macros;

#[cfg(test)]
extern crate glass_pumpkin;

#[cfg(test)]
mod tests {
    use super::*;
   
    #[cfg(test)]
    use num_bigint::{BigInt,Sign};
    
    #[cfg(test)]
    use glass_pumpkin::prime;
    
    #[cfg(test)]
    use quickcheck::*;
 
    // RSA key generation
    // Taken from https://asecuritysite.com/rust/rsa01/ 
    fn modinv(a0: BigInt, m0: BigInt) -> BigInt {
        if m0 == one() {return one()}
        let (mut a, mut m, mut x0, mut inv) = 
            (a0, m0.clone(), zero(), one());
        while a > one() {
            inv -= (&a / &m) * &x0;
            a = &a % &m;
            std::mem::swap(&mut a, &mut m);
            std::mem::swap(&mut x0, &mut inv)
        }
        if inv < zero() { inv += m0 }
        inv
    }

    fn rsa_key_gen() -> KeyPair {
        let p = BigInt::from_biguint(Sign::Plus,
            prime::new((BIT_SIZE / 2) as usize).unwrap());
        let q = BigInt::from_biguint(Sign::Plus,
            prime::new((BIT_SIZE / 2) as usize).unwrap());

        let n = RSAInt::from(p.clone()* q.clone());

        let e = BigInt::parse_bytes(b"65537", 10).unwrap();
        let totient = (p - BigInt::one()) * (q - BigInt::one());
        let d = modinv(e.clone(), totient.clone());
        
        ((n, RSAInt::from(e)), (n, RSAInt::from(d)))
    }

    // quickcheck generation
    #[derive(Clone, Copy, Debug)]
    struct Keyp {n: RSAInt, d: RSAInt, e: RSAInt}

    impl Arbitrary for RSAInt {
        fn arbitrary(g: &mut Gen) -> RSAInt {
            const NUM_BYTES: u32 = 127;
            let mut a: [u8; NUM_BYTES as usize] = [0; NUM_BYTES as usize];
            for i in 0..NUM_BYTES as usize {
                a[i] = u8::arbitrary(g);
            }
            RSAInt::from_byte_seq_be(&Seq::<U8>::from_public_slice(&a))
        }
    }

    impl Arbitrary for Keyp {
        fn arbitrary(_g: &mut Gen) -> Keyp {
            let ((n, e), (_n, d)) = rsa_key_gen();
            Keyp {n,d,e}
        }
    }

    // tests
    #[quickcheck]
    fn i2os2i(x: RSAInt) -> bool {
        let s = i2osp(x, 128).unwrap();
        let x_prime = os2ip(&s);
        x_prime == x
    }

    #[quickcheck]
    fn rsaeprsadp(x: RSAInt, kp: Keyp) -> bool {
        let c = rsaep((kp.n, kp.e), x).unwrap();
        let x_prime =  rsadp((kp.n, kp.d), c).unwrap();
        x_prime == x
    }

    #[quickcheck]
    fn rsasp1rsavp1(x: RSAInt, kp: Keyp) -> bool {
        let s = rsasp1((kp.n, kp.d), x).unwrap();
        let x_prime = rsavp1((kp.n, kp.e), s).unwrap();
        x_prime == x
    }

    #[quickcheck]
    fn neg_rsaeprsadp(x: RSAInt, y: RSAInt, kp: Keyp) -> bool {
        let x_prime = rsadp((kp.n, kp.d), y).unwrap();
        x_prime != x
    }

    #[quickcheck]
    fn neg_rsasp1rsavp1(x: RSAInt, y: RSAInt, kp: Keyp) -> bool {
        let x_prime = rsavp1((kp.n, kp.e), y).unwrap();
        x_prime != x
    }

    #[quickcheck]
    fn negkey_rsaeprsadp(x: RSAInt, kp: Keyp, fake: Keyp) -> bool {
        let c = rsaep((kp.n, kp.e), x).unwrap();
        let x_prime = rsadp((fake.n, fake.d), c).unwrap_or_default();
        x != x_prime
    }

    #[quickcheck]
    fn negkey_rsasp1rsavp1(x: RSAInt, kp: Keyp, fake: Keyp) -> bool {
        let s = rsasp1((kp.n, kp.d), x).unwrap();
        let x_prime = rsavp1((fake.n, fake.e), s).unwrap_or_default();
        x != x_prime
    }
}
