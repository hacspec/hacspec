use hacspec_lib::prelude::*;

#[test]
fn test_byte_sequences() {
    let msg = PublicByteSeq::from_hex("0388dace60b6a392f328c2b971b2fe78");
    let msg_u32 =
        PublicSeq::<u32>::from_native_slice(&[0x0388dace, 0x60b6a392, 0xf328c2b9, 0x71b2fe78]);
    for i in 0..msg.num_chunks(4) {
        let (l, chunk) = msg.clone().get_chunk(4, i);
        assert_eq!(l, 4);
        assert_eq!((msg_u32[i] & 0xFF) as u8, chunk[3]);
        assert_eq!(((msg_u32[i] & 0xFF00) >> 8) as u8, chunk[2]);
        assert_eq!(((msg_u32[i] & 0xFF0000) >> 16) as u8, chunk[1]);
        assert_eq!(((msg_u32[i] & 0xFF000000) >> 24) as u8, chunk[0]);
    }
}

#[test]
fn test_seq_poly() {
    let x = PublicSeq::<u128>::from_native_slice(&[5, 2, 7, 8, 9]);
    let y = PublicSeq::<u128>::from_native_slice(&[2, 1, 0, 2, 4]);
    let z = x.clone() + y.clone();
    let z = z.clone() - x.clone();
    assert_eq!(z[0..y.len()], y[0..y.len()]);
    assert_eq!(z.iter().skip(y.len()).fold(0, |acc, x| acc + x), 0);
    let _z = x.clone() * y.clone();
}

#[test]
fn test_sequences_comparison() {
    let a = PublicByteSeq::from_native_slice(&[1, 2, 3]);
    let b = PublicByteSeq::from_native_slice(&[1, 2, 3]);
    assert_eq!(a, b);
}

#[test]
fn test_public_not() {
    let seq = PublicByteSeq::from_hex("c59380b20ba8fcd203e447fd1c5c7b87");

    let not_output = !seq; // output of NOT to be checked for correctness
    let expected = PublicByteSeq::from_hex("3a6c7f4df457032dfc1bb802e3a38478");

    assert_eq!(expected, not_output);
}

#[test]
fn test_public_or() {
    let seq1 = PublicByteSeq::from_hex("c59380b20ba8fcd203e447fd1c5c7b87");
    let seq2 = PublicByteSeq::from_hex("3a6c7f4df457032dfc1bb802e3a38478");

    let or_output = seq1 | seq2; // output of OR to be checked for correctness
    let expected = PublicByteSeq::from_hex("ffffffffffffffffffffffffffffffff");

    assert_eq!(expected, or_output);
}

#[test]
fn test_public_xor() {
    let seq1 = PublicByteSeq::from_hex("3544de28f9d7d48ee7b318f6c541ff35");
    let seq2 = PublicByteSeq::from_hex("a4b13aa347b72f6c22870170fcb0cda3");

    let xor_output = seq1 ^ seq2; // output of XOR to be checked for correctness
    let expected = PublicByteSeq::from_hex("91f5e48bbe60fbe2c534198639f13296");

    assert_eq!(expected, xor_output);
}

#[test]
fn test_public_and() {
    let seq1 = PublicByteSeq::from_hex("c59380b20ba8fcd203e447fd1c5c7b87");
    let seq2 = PublicByteSeq::from_hex("3a6c7f4df457032dfc1bb802e3a38478");

    let and_output = seq1 & seq2; // output of AND to be checked for correctness
    let expected = PublicByteSeq::from_hex("00000000000000000000000000000000");

    assert_eq!(expected, and_output);
}
