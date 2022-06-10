// This crate implements RSA-FDH-VRF based on section 4 of https://datatracker.ietf.org/doc/draft-irtf-cfrg-vrf/
// The ciphersuite is RSA-FDH-VRF-SHA256, suite string can be changed if other hash function is desired
// The step comments refer to the corresponding steps in the IETF pseudocode for comparison with hacspec

use hacspec_lib::*;
use hacspec_sha256::*;
use hacspec_rsa_pkcs1::*;

bytes!(IntByte, 1);

#[rustfmt::skip]
const ONE: IntByte = IntByte(secret_array!(U8,  [0x01u8]));
#[rustfmt::skip]
const TWO: IntByte = IntByte(secret_array!(U8,  [0x02u8]));

const SUITE_STRING: IntByte = ONE;

// Helper function used by prove and verify to compute mgf1 of alpha
// mgf_salt currently part of cipher suite, could be optional input
fn vrf_mgf1(n: RSAInt, alpha: &ByteSeq) -> ByteSeqResult {
    let mgf_salt1 = i2osp(RSAInt::from_literal(BYTE_SIZE as u128), 4u32)?;
    let mgf_salt2 = i2osp(n, BYTE_SIZE)?;
    let mgf_salt = mgf_salt1.concat(&mgf_salt2);

    let mgf_string = SUITE_STRING
        .concat(&ONE)
        .concat(&mgf_salt)
        .concat(alpha);
    let mgf = mgf1(&mgf_string, BYTE_SIZE as usize - 1usize)?;
    ByteSeqResult::Ok(mgf)
}

// Based on section 4.1 of https://datatracker.ietf.org/doc/draft-irtf-cfrg-vrf/
pub fn prove(sk: SK, alpha: &ByteSeq) -> ByteSeqResult {
    let (n, _d) = sk.clone();

    // STEP 1 and 2
    let em = vrf_mgf1(n, alpha)?;

    // STEP 3
    let m = os2ip(&em);

    // STEP 4
    let s = rsasp1(sk, m)?;

    // STEP 5 and 6
    i2osp(s, BYTE_SIZE)
}

// Based on section 4.2 of https://datatracker.ietf.org/doc/draft-irtf-cfrg-vrf/
pub fn proof_to_hash(pi_string: &ByteSeq) -> ByteSeqResult {
    // STEP 1 and 2
    let hash_string = SUITE_STRING.concat(&TWO.concat(pi_string));

    // STEP 3
    ByteSeqResult:: Ok(sha256(&hash_string).slice(0,32))
}

// Based on section 4.3 of https://datatracker.ietf.org/doc/draft-irtf-cfrg-vrf/
pub fn verify(pk: PK, alpha: &ByteSeq, pi_string: &ByteSeq) -> ByteSeqResult {
    let (n, _e) = pk.clone();

    // STEP 1
    let s = os2ip(pi_string);

    // STEP 2
    let m = rsavp1(pk, s)?;

    // STEP 3 and 4
    let em_prime = vrf_mgf1(n, alpha)?;

    // STEP 5
    let m_prime = os2ip(&em_prime);

    // STEP 6
    if m == m_prime {
        proof_to_hash(pi_string)
    } else {
        ByteSeqResult::Err(Error::VerificationFailed)
    }
}


#[cfg(test)]
mod tests {
    use super::*;
    use num_bigint::{BigInt,Sign};
    use glass_pumpkin::prime;
    use quickcheck::*;
    use quickcheck_macros::quickcheck;

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
    #[derive(Clone, Copy, Debug)]
    struct Wrapper(RSAInt);

    impl Arbitrary for Wrapper {
        fn arbitrary(g: &mut Gen) -> Wrapper {
            const NUM_BYTES: u32 = 127;
            let mut a: [u8; NUM_BYTES as usize] = [0; NUM_BYTES as usize];
            for i in 0..NUM_BYTES as usize {
                a[i] = u8::arbitrary(g);
            }
            Wrapper(RSAInt::from_byte_seq_be(&Seq::<U8>::from_public_slice(&a)))
        }
    }

    impl Arbitrary for Keyp {
        fn arbitrary(_g: &mut Gen) -> Keyp {
            let ((n, e), (_n, d)) = rsa_key_gen();
            Keyp {n,d,e}
        }
    }

    #[quickcheck]
    fn rsafhdvrf(kp: Keyp, alpha: Wrapper) -> bool {
        let alpha = i2osp(alpha.0, BYTE_SIZE).unwrap();
        let pi = prove((kp.n, kp.d), &alpha).unwrap();
        let beta = proof_to_hash(&pi).unwrap();
        let beta_prime = verify((kp.n, kp.e), &alpha, &pi).unwrap();
        beta_prime == beta
    }
    
    #[quickcheck]
    fn neg_rsafhdvrf(kp: Keyp, fake: Keyp, alpha: Wrapper) -> bool {
        let alpha = i2osp(alpha.0, BYTE_SIZE).unwrap();
        let pi = prove((kp.n, kp.d), &alpha).unwrap();
        match verify((fake.n, fake.e), &alpha, &pi) {
            Ok(_beta_prime) => false,
            Err(e) => matches!(e, Error::VerificationFailed
                                | Error::MessageTooLarge),
        }
    }

    #[quickcheck]
    fn neg_alpha_rsafhdvrf(
        kp: Keyp, alpha: Wrapper, fake_alpha: Wrapper
    ) -> bool {
        let alpha = i2osp(alpha.0, BYTE_SIZE).unwrap();
        let fake_alpha = i2osp(fake_alpha.0, BYTE_SIZE).unwrap();
        let pi = prove((kp.n, kp.d), &fake_alpha).unwrap();
        match verify((kp.n, kp.e), &alpha, &pi) {
            Ok(_beta_prime) => false,
            Err(e) => matches!(e, Error::VerificationFailed
                                | Error::MessageTooLarge),
        }
    }
}
