// Import hacspec and all needed definitions.
use hacspec_lib::*;

pub const HASH_SIZE: usize = 160 / 8;

bytes!(Sha1Digest, HASH_SIZE);
array!(Hash, 5, U32);

const HASH_INIT: Hash = Hash(secret_array!(
    U32,
    [
        0x67452301u32,
        0xefcdab89u32,
        0x98badcfeu32,
        0x10325476u32,
        0xc3d2e1f0u32
    ]
));

pub fn hash(msg: &ByteSeq) -> Sha1Digest {
    let mut h = HASH_INIT;
    Sha1Digest::from_seq(&h.to_be_bytes())
}

pub fn sha1(msg: &ByteSeq) -> Sha1Digest {
    hash(msg)
}
