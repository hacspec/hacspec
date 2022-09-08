use hacspec_lib::prelude::*;

use hacspec_sha1::*;

#[test]
fn test_fips_examples() {
    // Examples from FIPS 180-1 Appendix A.
    {
        let msg = ByteSeq::from_public_slice(b"abc");
        let expect = "a9993e364706816aba3e25717850c26c9cd0d89d";
        assert_eq!(expect, sha1(&msg).to_hex());
    }
    {
        let msg = ByteSeq::from_public_slice(b"abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq");
        let expect = "84983e441c3bd26ebaae4aa1f95129e5e54670f1";
        assert_eq!(expect, sha1(&msg).to_hex());
    }
    {
        let a: u8 = b"a"[0];
        let msg = ByteSeq::from_public_slice(&[a; 1_000_000]);
        let expect = "34aa973cd4c4daa4f61eeb2bdbad27316534016f";
        assert_eq!(expect, sha1(&msg).to_hex());
    }
}
