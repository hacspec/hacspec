use hacspec_lib::prelude::*;

#[test]
fn test_byte_sequences() {
    let msg = ByteSeq::from_hex("0388dace60b6a392f328c2b971b2fe78");
    let msg_u32 = PublicSeq::<u32>::from_native_slice(&[0x0388dace, 0x60b6a392, 0xf328c2b9, 0x71b2fe78]);
    for i in 0..msg.num_chunks(4) {
        let (l, chunk) = msg.clone().get_chunk(4, i);
        assert_eq!(l, 4);
        assert_eq!((msg_u32[i] & 0xFF) as u8, U8::declassify(chunk[3]));
        assert_eq!(((msg_u32[i] & 0xFF00) >> 8) as u8, U8::declassify(chunk[2]));
        assert_eq!(((msg_u32[i] & 0xFF0000) >> 16) as u8, U8::declassify(chunk[1]));
        assert_eq!(((msg_u32[i] & 0xFF000000) >> 24) as u8, U8::declassify(chunk[0]));
    }
}

#[test]
fn test_seq_poly() {
    let x = PublicSeq::<u128>::from_native_slice(&[5, 2, 7, 8, 9]);
    let y = PublicSeq::<u128>::from_native_slice(&[2, 1, 0, 2, 4]);
    let z = x.clone() + y.clone();
    let z = z.clone() - x.clone();
    assert_eq!(z[0..y.len()], y[0..y.len()]);
    assert_eq!(z.iter().skip(y.len()).fold(0, |acc, x| acc+x), 0);
    let _z = x.clone() * y.clone();
    // let (zq, zr) = z.clone() / x.clone();
    // assert_eq!(zr.iter().fold(0, |acc, x| acc+x), 0);
    // assert_eq!(zq[0..y.len()], y[0..y.len()]);
    // assert_eq!(zq.iter().skip(y.len()).fold(0, |acc, x| acc+x), 0);
}

#[test]
fn test_seq_not() {
    let seq = ByteSeq::from_hex("ae125f62bd263edcc9");
    let expected = ByteSeq::from_hex("51eda09d42d9c12336");
    assert_eq!(expected, !seq);
}

#[test]
fn test_seq_or() {
    let seq1 = ByteSeq::from_hex("ae125f62bd263edcc9");
    let seq2 = ByteSeq::from_hex("51eda09d42d9c12336");
    let expected = ByteSeq::from_hex("ffffffffffffffffff");
    assert_eq!(expected, seq1 | seq2);
}

#[test]
fn test_seq_xor() {
    let seq1 = ByteSeq::from_hex("296519d609eb2ab27a");
    let seq2 = ByteSeq::from_hex("5a37737caae626c756");
    let expected = ByteSeq::from_hex("73526aaaa30d0c752c");
    assert_eq!(expected, seq1 ^ seq2);
}

#[test]
fn test_seq_and() {
    let seq1 = ByteSeq::from_hex("ae125f62bd263edcc9");
    let seq2 = ByteSeq::from_hex("51eda09d42d9c12336");
    let expected = ByteSeq::from_hex("000000000000000000");
    assert_eq!(expected, seq1 & seq2);
}
