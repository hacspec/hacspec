use hacspec_lib::{buf::ByteBuffer, *};

#[test]
fn create() {
    let s1 = Bytes::from_hex("deadbeef");
    let s2 = Bytes::from_hex("02deadbeef");
    let s3 = Bytes::from_hex("03deadbeef");
    let s4 = Bytes::from_hex("04deadbeef");

    let buffer = ByteBuffer::from_seq(s1);
    let buffer = buffer.concat_owned(s2);
    let buffer = buffer.concat_owned(s3);
    let buffer = buffer.concat_owned(s4);

    assert_secret_seq_eq!(
        Bytes::from_hex("deadbeef02deadbeef03deadbeef04deadbeef"),
        buffer.to_bytes(),
        Byte
    );
}

#[test]
fn split() {
    let s1 = Bytes::from_hex("deadbeef");
    let s2 = Bytes::from_hex("02deadbeef");
    let s3 = Bytes::from_hex("03deadbeef");
    let s4 = Bytes::from_hex("04deadbeef");

    let buffer = ByteBuffer::from_seq(s1);
    let buffer = buffer.concat_owned(s2);
    let buffer = buffer.concat_owned(s3);
    let buffer = buffer.concat_owned(s4);

    // get something shorter than the first bytes
    let (l3_bytes, remainder) = buffer.clone().split_off(3);

    assert_secret_seq_eq!(
        Bytes::from_hex("ef02deadbeef03deadbeef04deadbeef"),
        remainder.to_bytes(),
        Byte
    );

    assert_secret_seq_eq!(Bytes::from_hex("deadbe"), l3_bytes, Byte);

    // get something equal to the length of the first bytes
    let (l4_bytes, remainder) = buffer.clone().split_off(4);

    assert_secret_seq_eq!(
        Bytes::from_hex("02deadbeef03deadbeef04deadbeef"),
        remainder.to_bytes(),
        Byte
    );

    assert_secret_seq_eq!(Bytes::from_hex("deadbeef"), l4_bytes, Byte);

    // get something larger than the first bytes
    let (l7_bytes, remainder) = buffer.clone().split_off(7);

    assert_secret_seq_eq!(
        Bytes::from_hex("beef03deadbeef04deadbeef"),
        remainder.to_bytes(),
        Byte
    );

    assert_secret_seq_eq!(Bytes::from_hex("deadbeef02dead"), l7_bytes, Byte);

    // get something larger than the first bytes
    let (l9_bytes, remainder) = buffer.clone().split_off(9);

    assert_secret_seq_eq!(
        Bytes::from_hex("03deadbeef04deadbeef"),
        remainder.to_bytes(),
        Byte
    );

    assert_secret_seq_eq!(Bytes::from_hex("deadbeef02deadbeef"), l9_bytes, Byte);
}
