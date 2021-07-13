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
