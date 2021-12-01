// Import hacspec and all needed definitions.
use hacspec_lib::*;

bytes!(DigestB, 64);

array!(Sigma, 16 * 12, usize);
generic_array!(State, 8);
generic_array!(DoubleState, 16);
generic_array!(Counter, 2);

const SIGMA: Sigma = Sigma([
    0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 14, 10, 4, 8, 9, 15, 13, 6, 1, 12, 0, 2,
    11, 7, 5, 3, 11, 8, 12, 0, 5, 2, 15, 13, 10, 14, 3, 6, 7, 1, 9, 4, 7, 9, 3, 1, 13, 12, 11, 14,
    2, 6, 5, 10, 4, 0, 15, 8, 9, 0, 5, 7, 2, 4, 10, 15, 14, 1, 11, 12, 6, 8, 3, 13, 2, 12, 6, 10,
    0, 11, 8, 3, 4, 13, 7, 5, 15, 14, 1, 9, 12, 5, 1, 15, 14, 13, 4, 10, 0, 7, 6, 3, 9, 2, 8, 11,
    13, 11, 7, 14, 12, 1, 3, 9, 5, 0, 15, 4, 8, 6, 2, 10, 6, 15, 14, 9, 11, 3, 0, 8, 12, 2, 13, 7,
    1, 4, 10, 5, 10, 2, 8, 4, 7, 6, 1, 5, 15, 11, 9, 14, 3, 12, 13, 0, 0, 1, 2, 3, 4, 5, 6, 7, 8,
    9, 10, 11, 12, 13, 14, 15, 14, 10, 4, 8, 9, 15, 13, 6, 1, 12, 0, 2, 11, 7, 5, 3,
]);

const IVS: State<U32> = State(secret_array!(
    U32,
    [
        0x6A09_E667,
        0xBB67_AE85,
        0x3C6E_F372,
        0xA54F_F53A,
        0x510E_527F,
        0x9B05_688C,
        0x1F83_D9AB,
        0x5BE0_CD19
    ]
));

const IVB: State<U64> = State(secret_array!(
    U64,
    [
        0x6a09_e667_f3bc_c908u64,
        0xbb67_ae85_84ca_a73bu64,
        0x3c6e_f372_fe94_f82bu64,
        0xa54f_f53a_5f1d_36f1u64,
        0x510e_527f_ade6_82d1u64,
        0x9b05_688c_2b3e_6c1fu64,
        0x1f83_d9ab_fb41_bd6bu64,
        0x5be0_cd19_137e_2179u64
    ]
));

fn mix<Word: SecretIntegerCopy>(
    v: DoubleState<Word>,
    a: usize,
    b: usize,
    c: usize,
    d: usize,
    x: Word,
    y: Word,
) -> DoubleState<Word> {
    let mut result = v;
    result[a] = result[a] + result[b] + x;
    result[d] = (result[d] ^ result[a]).rotate_right(32);

    result[c] = result[c] + result[d];
    result[b] = (result[b] ^ result[c]).rotate_right(24);

    result[a] = result[a] + result[b] + y;
    result[d] = (result[d] ^ result[a]).rotate_right(16);

    result[c] = result[c] + result[d];
    result[b] = (result[b] ^ result[c]).rotate_right(63);

    result
}

fn inc_counter<Word: PublicIntegerCopy>(t: Counter<Word>, x: Word) -> Counter<Word> {
    let mut result = Counter::new();
    let new_val: Word = t[0] + x;
    result[0] = new_val;
    if new_val.less_than(x) {
        result[1] = t[1] + Word::ONE();
    }
    result
}

fn make_array<Word: UnsignedSecretIntegerCopy>(h: &ByteSeq) -> DoubleState<Word> {
    assert_eq!(h.len() / ((Word::NUM_BITS as usize) / 8), 16);
    let mut result = DoubleState::new();
    for i in 0..16 {
        let (_, h_chunk) = h.get_chunk(Word::NUM_BITS as usize / 8, i);
        result[i] = Word::from_le_bytes(&h_chunk)
    }
    result
}

pub trait HasIV<Word: UnsignedSecretInteger> {
    fn iv() -> State<Word>;
}

impl HasIV<U64> for State<U64> {
    fn iv() -> State<U64> {
        IVB
    }
}

impl HasIV<U32> for State<U32> {
    fn iv() -> State<U32> {
        IVS
    }
}

#[derive(Clone, Copy)]
pub enum BlakeVariant {
    Blake2S,
    Blake2B,
}

fn compress<Word: UnsignedSecretIntegerCopy>(
    h: State<Word>,
    m: &ByteSeq,
    t: Counter<Word::PublicVersionCopy>,
    last_block: bool,
    alg: BlakeVariant,
) -> State<Word>
where
    State<Word>: HasIV<Word>,
{
    let mut v = DoubleState::new();

    // Read u8 data to u64.
    let m = make_array(m);

    // Prepare.
    v = v.update_slice(0, &h, 0, 8);
    v = v.update_slice(8, &State::iv(), 0, 8);
    let old_v12: Word = v[12];
    v[12] = old_v12 ^ SecretIntegerCopy::classify(t[0]);
    let old_v13: Word = v[13];
    v[13] = old_v13 ^ SecretIntegerCopy::classify(t[1]);
    if last_block {
        // TODO: why do we need the type here?
        let old_v14: Word = v[14];
        v[14] = !old_v14;
    }

    let num_rounds = match alg {
        BlakeVariant::Blake2S => 10,
        BlakeVariant::Blake2B => 12,
    };
    // Mixing.
    for i in 0..num_rounds {
        v = mix(v, 0, 4, 8, 12, m[SIGMA[i * 16 + 0]], m[SIGMA[i * 16 + 1]]);
        v = mix(v, 1, 5, 9, 13, m[SIGMA[i * 16 + 2]], m[SIGMA[i * 16 + 3]]);
        v = mix(v, 2, 6, 10, 14, m[SIGMA[i * 16 + 4]], m[SIGMA[i * 16 + 5]]);
        v = mix(v, 3, 7, 11, 15, m[SIGMA[i * 16 + 6]], m[SIGMA[i * 16 + 7]]);
        v = mix(v, 0, 5, 10, 15, m[SIGMA[i * 16 + 8]], m[SIGMA[i * 16 + 9]]);
        v = mix(
            v,
            1,
            6,
            11,
            12,
            m[SIGMA[i * 16 + 10]],
            m[SIGMA[i * 16 + 11]],
        );
        v = mix(v, 2, 7, 8, 13, m[SIGMA[i * 16 + 12]], m[SIGMA[i * 16 + 13]]);
        v = mix(v, 3, 4, 9, 14, m[SIGMA[i * 16 + 14]], m[SIGMA[i * 16 + 15]]);
    }

    let mut compressed = State::new();
    for i in 0..8 {
        compressed[i] = h[i] ^ v[i] ^ v[i + 8];
    }
    compressed
}

fn get_byte<Word: UnsignedSecretIntegerCopy>(x: Word, i: usize) -> U8 {
    let bytes = x.get_byte(i).to_le_bytes();
    bytes[0]
}

pub fn blake2<Word: UnsignedSecretIntegerCopy>(data: &ByteSeq, alg: BlakeVariant) -> ByteSeq
where
    State<Word>: HasIV<Word>,
{
    let mut h = State::iv();
    // This only supports the 512 version without key.
    h[0] = h[0] ^ Word::from_literal(0x0101_0000) ^ Word::from_literal(64);

    let dd = data.num_chunks(128);
    let mut t: Counter<Word::PublicVersionCopy> = Counter::new();
    if dd > 1 {
        for i in 0..dd - 1 {
            let (_, block) = data.get_chunk(128, i);
            t = inc_counter(t, Word::PublicVersionCopy::from_literal(128));
            h = compress(h, &ByteSeq::from_seq(&block), t, false, alg);
        }
    }
    let last_chunk = if dd == 0 { 0 } else { data.num_chunks(128) - 1 };
    let (block_len, block) = data.get_chunk(128, last_chunk);
    if block_len == 128 {
        t = inc_counter(t, Word::PublicVersionCopy::from_literal(128));
        h = compress(h, &ByteSeq::from_seq(&block), t, true, alg);
    } else {
        // Pad last bits of data to a full block.
        t = inc_counter(t, Word::PublicVersionCopy::from_literal(block_len as u128));
        let compress_input = ByteSeq::new(128).update_start(&block);
        h = compress(h, &compress_input, t, true, alg);
    }

    let digest_size = match alg {
        BlakeVariant::Blake2S => 32,
        BlakeVariant::Blake2B => 64,
    };
    // We transform 8*u64 into 64*u8
    let mut d = ByteSeq::new(digest_size);
    for i in 0..8 {
        for j in 0..8 {
            d[i * 8 + j] = get_byte(h[i], j);
        }
    }
    d
}

pub fn blake2b(data: &ByteSeq) -> DigestB {
    DigestB::from_seq(&blake2::<U64>(data, BlakeVariant::Blake2B))
}
