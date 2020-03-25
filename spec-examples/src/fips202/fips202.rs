// Import hacspec and all needed definitions.
use hacspec::prelude::*;

const ROUNDS: usize = 24;
pub const SHA3224_RATE: usize = 144;
pub const SHA3256_RATE: usize = 136;
pub const SHA3384_RATE: usize = 104;
pub const SHA3512_RATE: usize = 72;
pub const SHAKE128_RATE: usize = 168;
pub const SHAKE256_RATE: usize = 136;

array!(State, 25, U64);
array!(Row, 5, U64);
bytes!(Digest224, 28);
bytes!(Digest256, 32);
bytes!(Digest384, 48);
bytes!(Digest512, 64);

static ROUNDCONSTANTS: [u64; ROUNDS] = [
    0x0000_0000_0000_0001,
    0x0000_0000_0000_8082,
    0x8000_0000_0000_808a,
    0x8000_0000_8000_8000,
    0x0000_0000_0000_808b,
    0x0000_0000_8000_0001,
    0x8000_0000_8000_8081,
    0x8000_0000_0000_8009,
    0x0000_0000_0000_008a,
    0x0000_0000_0000_0088,
    0x0000_0000_8000_8009,
    0x0000_0000_8000_000a,
    0x0000_0000_8000_808b,
    0x8000_0000_0000_008b,
    0x8000_0000_0000_8089,
    0x8000_0000_0000_8003,
    0x8000_0000_0000_8002,
    0x8000_0000_0000_0080,
    0x0000_0000_0000_800a,
    0x8000_0000_8000_000a,
    0x8000_0000_8000_8081,
    0x8000_0000_0000_8080,
    0x0000_0000_8000_0001,
    0x8000_0000_8000_8008,
];

static ROTC: [u32; 25] = [
    0, 1, 62, 28, 27, 36, 44, 6, 55, 20, 3, 10, 43, 25, 39, 41, 45, 15, 21, 8, 18, 2, 61, 56, 14,
];

static PI: [usize; 25] = [
    0, 6, 12, 18, 24, 3, 9, 10, 16, 22, 1, 7, 13, 19, 20, 4, 5, 11, 17, 23, 2, 8, 14, 15, 21,
];

fn theta(mut s: State) -> State {
    let mut b = Row::new();
    for i in 0..5 {
        b[i] = s[i] ^ s[i + 5] ^ s[i + 10] ^ s[i + 15] ^ s[i + 20];
    }
    for i in 0..5 {
        let u: U64 = b[(i + 1) % 5];
        let t = b[(i + 4) % 5] ^ u.rotate_left(1);
        for j in 0..5 {
            s[5 * j + i] ^= t;
        }
    }
    s
}

fn rho(mut s: State) -> State {
    for i in 0..25 {
        let u: U64 = s[i];
        s[i] = u.rotate_left(ROTC[i]);
    }
    s
}

fn pi(s: State) -> State {
    let mut v = State::new();
    for i in 0..25 {
        v[i] = s[PI[i]];
    }
    v
}

fn chi(mut s: State) -> State {
    let mut b = Row::new();
    for i in 0..5 {
        for j in 0..5 {
            b[j] = s[5 * i + j];
        }
        for j in 0..5 {
            let u: U64 = b[(j + 1) % 5];
            s[5 * i + j] ^= (!u) & b[(j + 2) % 5];
        }
    }
    s
}

fn iota(mut s: State, rndconst: u64) -> State {
    s[0] ^= U64::classify(rndconst);
    s
}

fn keccakf1600(mut s: State) -> State {
    for i in 0..ROUNDS {
        s = theta(s);
        s = rho(s);
        s = pi(s);
        s = chi(s);
        s = iota(s, ROUNDCONSTANTS[i]);
    }
    s
}

fn absorb_block(mut s: State, block: ByteSeq) -> State {
    for (i, b) in block.iter().enumerate() {
        let w = i >> 3;
        let o = 8 * ((i & 7) as u32);
        s[w] ^= U64::from(*b) << o;
    }
    keccakf1600(s)
}

fn squeeze(mut s: State, nbytes: usize, rate: usize) -> ByteSeq {
    let mut out = ByteSeq::new(nbytes);
    for i in 0..nbytes {
        let pos = i % rate;
        let w = pos >> 3;
        let o = 8 * ((pos & 7) as u32);
        let b = (s[w] >> o) & U64::classify(0xffu64);
        out[i] = b.into();
        if ((i + 1) % rate) == 0 {
            s = keccakf1600(s);
        }
    }
    out
}

fn keccak(rate: usize, data: ByteSeq, p: u8, outbytes: usize) -> ByteSeq {
    let mut buf = ByteSeq::new(rate);
    let mut s = State::new();

    for (block_len, block) in data.chunks(rate) {
        if block_len == rate {
            s = absorb_block(s, block);
        } else {
            buf = buf.push(block);
        }
    }
    buf = buf.push(ByteSeq::from_array(&[U8::classify(p)]));
    buf[rate - 1] |= U8::classify(128);
    s = absorb_block(s, buf);

    squeeze(s, outbytes, rate)
}

pub fn sha3224(data: ByteSeq) -> Digest224 {
    let t = keccak(SHA3224_RATE, data, 0x06, 28);
    Digest224::from(t)
}

pub fn sha3256(data: ByteSeq) -> Digest256 {
    let t = keccak(SHA3256_RATE, data, 0x06, 32);
    Digest256::from(t)
}

pub fn sha3384(data: ByteSeq) -> Digest384 {
    let t = keccak(SHA3384_RATE, data, 0x06, 48);
    Digest384::from(t)
}

pub fn sha3512(data: ByteSeq) -> Digest512 {
    let t = keccak(SHA3512_RATE, data, 0x06, 64);
    Digest512::from(t)
}

pub fn shake128(data: ByteSeq, outlen: usize) -> ByteSeq {
    keccak(SHAKE128_RATE, data, 0x1f, outlen)
}

pub fn shake256(data: ByteSeq, outlen: usize) -> ByteSeq {
    keccak(SHAKE256_RATE, data, 0x1f, outlen)
}

#[test]
fn test_keccakf1600() {
    let s: State = State(secret_array!(
        U64,
        [
            0x5ba446eba89b9b78,
            0x6ef6eb8a586fb342,
            0x85cb3d1fcec58036,
            0xa59848fabf68003d,
            0x35fdce49db45e6c1,
            0x0cf8fad4b3c5a04c,
            0x9afa06a9884be9bc,
            0x1ff35d85c227b2e0,
            0x09ec8487110fc092,
            0xcdea358a32c0fafb,
            0x74241ac11e48073a,
            0x72f921a900982d03,
            0x676616072102dbbc,
            0x2638caacb8a3a5de,
            0xc603972154aa5dd8,
            0x68b2fefc9b5075e3,
            0x8373f072f138bdee,
            0xdff378a39b99a1a0,
            0x0b4bc139e9140556,
            0x19195e7735eb1c0a,
            0x056b896a9884cb04,
            0x68e821e02963121f,
            0xce7c280b9563ae2c,
            0xc88f8da33e4311d6,
            0xc67829e549219318
        ]
    ));

    let c: State = State(secret_array!(
        U64,
        [
            0x95bef5e1cff30a77,
            0x91857a255e178abd,
            0xbf8f4cef4c33fbe9,
            0xa40655d779ecdc92,
            0xb17af41f3c6a6d09,
            0x9f4e56cfd932c0c7,
            0x8dedfc2eb4c43a69,
            0x92e3a4f9f54bf903,
            0x51eca70f0657a075,
            0x690f9af199489ab5,
            0x718748b08fba9389,
            0x2d7349b2fd3c5cbe,
            0xc8e1c9f8a9b002aa,
            0x272dfd58ff1304ec,
            0x665d945446962fe5,
            0xdabb2fbc07dc0b57,
            0xc49e2cecb193b592,
            0x63c1c463f370e7a5,
            0xc643a20b2ffb0e52,
            0xee9f85afed7d708c,
            0xb031433c85642b6c,
            0xfbe4f94ffc73ddbe,
            0xfa2a02bb934e7bb3,
            0x38025c926f7136f5,
            0xf83d27a7f7ec241e
        ]
    ));
    let v = keccakf1600(s);

    assert_secret_array_eq!(c, v, U64);
}
