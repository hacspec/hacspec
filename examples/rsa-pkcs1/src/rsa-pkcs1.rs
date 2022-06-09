// This crate implements RSA primitives from PKCS #1 v2.2, as specified in RFC8017: https://datatracker.ietf.org/doc/html/rfc8017
// Secret keys are represented in the representation described in section 3.2 of https://datatracker.ietf.org/doc/html/rfc8017#section-3.2
// Note that the RSA primitives return a MessageTooLarge error if the message is larger than the RSA modulus n
use hacspec_lib::*;
use hacspec_sha256::*;

pub const BIT_SIZE: u32  = 2048u32;
pub const BYTE_SIZE: u32 = 2048u32 / 8u32;
const HLEN: usize = 32usize; // sha256 / 8 = 32

unsigned_public_integer!(RSAInt, 2048);

#[derive(Debug, PartialEq)]
pub enum Error {
    InvalidLength,
    MessageTooLarge,
}

pub type PK = (RSAInt, RSAInt);
pub type SK = (RSAInt, RSAInt);
pub type KeyPair = (PK, SK);
pub type ByteSeqResult = Result<ByteSeq, Error>;
pub type RSAIntResult = Result<RSAInt, Error>;

// Encryption primitive, see section 5.1.1 of https://datatracker.ietf.org/doc/html/rfc8017#section-5.1.1
pub fn rsaep(pk: PK, m: RSAInt) -> RSAIntResult {
    let (n, e) = pk;
    if m > n - RSAInt::ONE() {
        RSAIntResult::Err(Error::MessageTooLarge)
    } else {
        RSAIntResult::Ok(m.pow_mod(e, n))
    }
}

// Decryption primitive, see section 5.1.2 of https://datatracker.ietf.org/doc/html/rfc8017#section-5.1.2
pub fn rsadp(sk: SK, c: RSAInt) -> RSAIntResult {
    let (n, d) = sk;
    if c > n - RSAInt::ONE() {
        RSAIntResult::Err(Error::MessageTooLarge)
    } else {
        RSAIntResult::Ok(c.pow_mod(d, n))
    }
}

// Signature primitive, see section 5.2.1 of https://datatracker.ietf.org/doc/html/rfc8017#section-5.2.1
pub fn rsasp1(sk: SK, m: RSAInt) -> RSAIntResult {
    let (n, d) = sk;
    if m > n - RSAInt::ONE() {
        RSAIntResult::Err(Error::MessageTooLarge)
    } else {
        RSAIntResult::Ok(m.pow_mod(d, n))
    }
}

// Verification primitive, see section 5.2.2 of https://datatracker.ietf.org/doc/html/rfc8017#section-5.2.2
pub fn rsavp1(pk: PK, s: RSAInt) -> RSAIntResult {
    let (n, e) = pk;
    if s > n - RSAInt::ONE() {
        RSAIntResult::Err(Error::MessageTooLarge)
    } else {
        RSAIntResult::Ok(s.pow_mod(e, n))
    }
}

// RSA integer to octet string primitive, as described in section 4.1 of https://datatracker.ietf.org/doc/html/rfc8017#section-4.1
pub fn i2osp(x: RSAInt, x_len: u32) -> ByteSeqResult {
    if x >= (RSAInt::exp(RSAInt::from_literal(256u128), x_len)) 
            && x_len != BYTE_SIZE {
        ByteSeqResult::Err(Error::InvalidLength)
    } else {
        ByteSeqResult::Ok(RSAInt::to_byte_seq_be(x)
            .slice((BYTE_SIZE - x_len) as usize, x_len as usize))
    }
}

// Octet string to RSA integer primitive, as described in section 4.2 of https://datatracker.ietf.org/doc/html/rfc8017#section-4.2
pub fn os2ip(x: &ByteSeq) -> RSAInt {
    RSAInt::from_byte_seq_be(x)
}

// Mask generation function from appendix B.2.1, see https://datatracker.ietf.org/doc/html/rfc8017#appendix-B.2.1
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

    impl Arbitrary for RSAInt {
        fn arbitrary(g: &mut Gen) -> RSAInt {
            const NUM_BYTES: u32 = 255;
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

    // quickcheck tests
    #[quickcheck]
    fn i2os2i(x: RSAInt) -> bool {
        let s = i2osp(x, BYTE_SIZE).unwrap();
        let x_prime = os2ip(&s);
        x_prime == x
    }

    #[test]
    fn test_rsaepdp() {
        fn rsaepdp(x: RSAInt, kp: Keyp) -> bool {
            let c = rsaep((kp.n, kp.e), x).unwrap();
            let x_prime =  rsadp((kp.n, kp.d), c).unwrap();
            x_prime == x
        }
        QuickCheck::new().tests(5)
            .quickcheck(rsaepdp as fn(RSAInt, Keyp) -> bool);
    }

    #[test]
    fn test_rsasp1vp1() {
        fn rsasp1vp1(x: RSAInt, kp: Keyp) -> bool {
            let s = rsasp1((kp.n, kp.d), x).unwrap();
            let x_prime = rsavp1((kp.n, kp.e), s).unwrap();
            x_prime == x
        }
        QuickCheck::new().tests(5)
            .quickcheck(rsasp1vp1 as fn(RSAInt, Keyp) -> bool);
    }

    #[test]
    fn test_neg_rsaepdp() {
        fn neg_rsaepdp(x: RSAInt, y: RSAInt, kp: Keyp) -> bool {
            let x_prime = rsadp((kp.n, kp.d), y).unwrap();
            x_prime != x
        }
        QuickCheck::new().tests(5)
            .quickcheck(neg_rsaepdp as fn(RSAInt, RSAInt, Keyp) -> bool);
    }

    #[test]
    fn test_neg_rsasp1vp1() {
        fn neg_rsasp1vp1(x: RSAInt, y: RSAInt, kp: Keyp) -> bool {
            let x_prime = rsavp1((kp.n, kp.e), y).unwrap();
            x_prime != x
        }
        QuickCheck::new().tests(5)
            .quickcheck(neg_rsasp1vp1 as fn(RSAInt, RSAInt, Keyp) -> bool);
    }

    #[test]
    fn test_negkey_rsaepdp() {
        fn negkey_rsaepdp(x: RSAInt, kp: Keyp, fake: Keyp) -> bool {
            let c = rsaep((kp.n, kp.e), x).unwrap();
            let x_prime = rsadp((fake.n, fake.d), c).unwrap_or_default();
            x != x_prime
        }
        QuickCheck::new().tests(5)
            .quickcheck(negkey_rsaepdp as fn(RSAInt, Keyp, Keyp) -> bool);
    }

    #[test]
    fn test_negkey_rsasp1vp1() {
        fn negkey_rsasp1vp1(x: RSAInt, kp: Keyp, fake: Keyp) -> bool {
            let s = rsasp1((kp.n, kp.d), x).unwrap();
            let x_prime = rsavp1((fake.n, fake.e), s).unwrap_or_default();
            x != x_prime
        }
        QuickCheck::new().tests(5)
            .quickcheck(negkey_rsasp1vp1 as fn(RSAInt, Keyp, Keyp) -> bool)
    }

    // tests using test vectors from wycheproof: https://github.com/google/wycheproof/blob/master/testvectors/rsa_pkcs1_2048_test.json
    fn get_test_key() -> Keyp {
        let n = RSAInt::from_hex("00b3510a2bcd4ce644c5b594ae5059e12b2f054b658d5da5959a2fdf1871b808bc3df3e628d2792e51aad5c124b43bda453dca5cde4bcf28e7bd4effba0cb4b742bbb6d5a013cb63d1aa3a89e02627ef5398b52c0cfd97d208abeb8d7c9bce0bbeb019a86ddb589beb29a5b74bf861075c677c81d430f030c265247af9d3c9140ccb65309d07e0adc1efd15cf17e7b055d7da3868e4648cc3a180f0ee7f8e1e7b18098a3391b4ce7161e98d57af8a947e201a463e2d6bbca8059e5706e9dfed8f4856465ffa712ed1aa18e888d12dc6aa09ce95ecfca83cc5b0b15db09c8647f5d524c0f2e7620a3416b9623cadc0f097af573261c98c8400aa12af38e43cad84d");
        let d = RSAInt::from_hex("1a502d0eea6c7b69e21d5839101f705456ed0ef852fb47fe21071f54c5f33c8ceb066c62d727e32d26c58137329f89d3195325b795264c195d85472f7507dbd0961d2951f935a26b34f0ac24d15490e1128a9b7138915bc7dbfa8fe396357131c543ae9c98507368d9ceb08c1c6198a3eda7aea185a0e976cd42c22d00f003d9f19d96ea4c9afcbfe1441ccc802cfb0689f59d804c6a4e4f404c15174745ed6cb8bc88ef0b33ba0d2a80e35e43bc90f350052e72016e75b00d357a381c9c0d467069ca660887c987766349fcc43460b4aa516bce079edd87ba164307b752c277ed9528ad3ba0bf1877349ed3b7966a6c240110409bf4d0fade0c68fdadd847fd");
        let e = RSAInt::from_hex("010001");
        Keyp {n, d, e}
    }

    #[test]
    // tcId1
    fn test_empty() {
        let k = get_test_key();
        let m = RSAInt::from_hex("");
        let ct = RSAInt::from_hex("5999ccb0cfdd584a3fd9daf247b9cd7314323f8bba4864258f98c6bafc068fe672641bab25ef5b1a7a2b88f67f12af3ca4fe3c493b2062bbb11ad3b1ba0640025c814326ff50ed52b176bd7f606ea9e209bcdcc67c0a0c4b8ed30b9959c57e90fd1efdf99895e2608095f92caff9070dec900fb96d5ce5efd2b2e66b80cff27d482d242b307cb813e7dc818fce31b67ac9a94501b5bc4621b547ba9d81808dd297d600dfc1a7deeb061570cde8894e398453328740adfd77cf76075a109d41ad296651ac817382424a4907d5a342d06cf19c09d5b37a147dd69045bf7d378e19dbbbbfb25282e3d9a4dc9793c8c32ab5a45c0b43dba4daca367b6eb5f4432a62");
        let ct_prime = rsaep((k.n, k.e), m);
        assert_eq!(RSAIntResult::Ok(ct), ct_prime);
        let m_prime = rsadp((k.n, k.d), ct);
        assert_eq!(RSAIntResult::Ok(m), m_prime)
    }

    #[test]
    // tcId3
    fn test_54657374() {
        let k = get_test_key();
        let m = RSAInt::from_hex("54657374");
        let ct = RSAInt::from_hex("4501b4d669e01b9ef2dc800aa1b06d49196f5a09fe8fbcd037323c60eaf027bfb98432be4e4a26c567ffec718bcbea977dd26812fa071c33808b4d5ebb742d9879806094b6fbeea63d25ea3141733b60e31c6912106e1b758a7fe0014f075193faa8b4622bfd5d3013f0a32190a95de61a3604711bc62945f95a6522bd4dfed0a994ef185b28c281f7b5e4c8ed41176d12d9fc1b837e6a0111d0132d08a6d6f0580de0c9eed8ed105531799482d1e466c68c23b0c222af7fc12ac279bc4ff57e7b4586d209371b38c4c1035edd418dc5f960441cb21ea2bedbfea86de0d7861e81021b650a1de51002c315f1e7c12debe4dcebf790caaa54a2f26b149cf9e77d");
        let ct_prime = rsaep((k.n, k.e), m);
        assert_eq!(RSAIntResult::Ok(ct), ct_prime);
        let m_prime = rsadp((k.n, k.d), ct);
        assert_eq!(RSAIntResult::Ok(m), m_prime)
    }

    #[test]
    // tcId 5
    fn test_4d657373616765() {
        let k = get_test_key();
        let m = RSAInt::from_hex("4d657373616765");
        let ct = RSAInt::from_hex("1cf861ef8b6c29474666605d3ddb663a259a9ae838417abcc7f7dd42d471d5f3812cdf90e3041c4c5bfd38ac1e4d95fd71661bddac45f5f8e3e89629a335bbf2eff116030f1c5ace8336cf7e94c2e8bf5a1d6116e54ec42b9da5fc651a41ac8fd38194e5029489cfde1f7fc850c0dfb3dc00021f74ae3847327c69afdb1355c7587bb93d5f4d2cfb35a7f70bcabd43eb32300585b6ee32f14a68c2a08434e923adb76dfcdf3ea5133edffa5ca20425083b28ecb045e69562b44286d320d87285e7a2e3bedded083c010401ae22c8f278b080112c4264a3cad3ed9fa31cf19e052aabbda9f8ecef1d64786258202bb61128b3140a355d65b982b0239764d77d24");
        let ct_prime = rsaep((k.n, k.e), m);
        assert_eq!(RSAIntResult::Ok(ct), ct_prime);
        let m_prime = rsadp((k.n, k.d), ct);
        assert_eq!(RSAIntResult::Ok(m), m_prime)
    }
    
    #[test]
    // tcId 8
    fn test_longest() {
        let k = get_test_key();
        let m = RSAInt::from_hex("7878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878");
        let ct = RSAInt::from_hex("7e151b7b34e3b4abe045cf708640e61501c50fdca629aeca10259d45d15eeec6a2008b6336f57021ac6fdad9a6b29d65f098abff76f93722a8e23fb5e153db075005575dad6adccb7c020cd741c3419946b82d369a07fad5b0d55d51774f8991bd65e9e828d8f5a989c866a024a4a78434e9affd0af2c72f9185d450b627008a8a0968fc6373ca340410306a58921cce1207bb6f6c14e3d1f214304f9f6bb9199909e1610322e834b0ce9f55b1835d7623b82ef548545f984ea51466250159344dde902a0f021ba4baf26b16d8c6a42003f4d5dcae531187dc7e3f87c9e04470599eb623e04fca266e86f98cabb6866004e7fc80b36c3977456e51eb64f4b65f");
        let ct_prime = rsaep((k.n, k.e), m);
        assert_eq!(RSAIntResult::Ok(ct), ct_prime);
        let m_prime = rsadp((k.n, k.d), ct);
        assert_eq!(RSAIntResult::Ok(m), m_prime)
    }
}
