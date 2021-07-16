use hacspec_dev::prelude::*;
use hacspec_lib::prelude::*;

use unsafe_hacspec_examples::blake2::blake2b::*;

static EXPECTED_ABC: [u8; 64] = [
    0xba, 0x80, 0xa5, 0x3f, 0x98, 0x1c, 0x4d, 0x0d, 0x6a, 0x27, 0x97, 0xb6, 0x9f, 0x12, 0xf6, 0xe9,
    0x4c, 0x21, 0x2f, 0x14, 0x68, 0x5a, 0xc4, 0xb7, 0x4b, 0x12, 0xbb, 0x6f, 0xdb, 0xff, 0xa2, 0xd1,
    0x7d, 0x87, 0xc5, 0x39, 0x2a, 0xab, 0x79, 0x2d, 0xc2, 0x52, 0xd5, 0xde, 0x45, 0x33, 0xcc, 0x95,
    0x18, 0xd3, 0x8a, 0xa8, 0xdb, 0xf1, 0x92, 0x5a, 0xb9, 0x23, 0x86, 0xed, 0xd4, 0x00, 0x99, 0x23,
];

#[test]
fn test_single_block() {
    let m = ByteSeq::from_native_slice(&[U8(0x61), U8(0x62), U8(0x63)]);
    let h = blake2b(&m);
    assert_eq!(
        EXPECTED_ABC.iter().map(|x| *x).collect::<Vec<_>>(),
        h.iter().map(|x| U8::declassify(*x)).collect::<Vec<_>>()
    );
}

#[test]
fn test_single_block_string() {
    let m = String::from("abc");
    let h = blake2b(&ByteSeq::from_native_slice(
        &m.into_bytes()
            .iter()
            .map(|x| U8::classify(*x))
            .collect::<Vec<_>>(),
    ));
    assert_eq!(
        EXPECTED_ABC.iter().map(|x| *x).collect::<Vec<_>>(),
        h.iter().map(|x| U8::declassify(*x)).collect::<Vec<_>>()
    );
}

#[test]
fn test_multi_block_string() {
    let m = String::from("qwertzuiopasdfghjklyxcvbnm123456789qwertzuiopasdfghjklyxcvbnm123456789qwertzuiopasdfghjklyxcvbnm123456789qwertzuiopasdfghjklyxcvbnm123456789");
    let h = blake2b(&ByteSeq::from_native_slice(
        &m.into_bytes()
            .iter()
            .map(|x| U8::classify(*x))
            .collect::<Vec<_>>(),
    ));

    let expected: [u8; 64] = [
        0x5c, 0xc9, 0x7c, 0x7f, 0x9f, 0xf2, 0x00, 0x8b, 0x40, 0x12, 0x6f, 0x37, 0x3f, 0x43, 0x33,
        0xfa, 0x34, 0x8d, 0x9f, 0x50, 0x06, 0xb8, 0x73, 0x57, 0xa6, 0xd8, 0x61, 0x12, 0xa1, 0xa0,
        0x43, 0x95, 0x4d, 0xa2, 0xe2, 0x8f, 0x01, 0xb2, 0xf9, 0x55, 0xa9, 0x32, 0xfb, 0x8a, 0x8d,
        0x0a, 0x17, 0x87, 0xd0, 0xc6, 0xd9, 0x62, 0x77, 0x9c, 0xbc, 0x58, 0xbf, 0xdf, 0x89, 0x48,
        0x1c, 0x87, 0x46, 0x96,
    ];
    assert_eq!(
        expected.iter().map(|x| *x).collect::<Vec<_>>(),
        h.iter().map(|x| U8::declassify(*x)).collect::<Vec<_>>()
    );
}

#[test]
fn test_multi_block_string_longer() {
    let m = String::from("qwertzuiopasdfghjklyxcvbnm123456789qwertzuiopasdfghjklyxcvbnm123456789qwertzuiopasdfghjklyxcvbnm123456789qwertzuiopasdfghjklyxcvbnm123456789qwertzuiopasdfghjklyxcvbnm123456789qwertzuiopasdfghjklyxcvbnm123456789qwertzuiopasdfghjklyxcvbnm123456789qwertzuiopasdfghjklyxcvbnm123456789");
    let h = blake2b(&ByteSeq::from_native_slice(
        &m.into_bytes()
            .iter()
            .map(|x| U8::classify(*x))
            .collect::<Vec<_>>(),
    ));

    let expected: [u8; 64] = [
        0x1f, 0x9e, 0xe6, 0x5a, 0xa0, 0x36, 0x05, 0xfc, 0x41, 0x0e, 0x2f, 0x55, 0x96, 0xfd, 0xb5,
        0x9d, 0x85, 0x95, 0x5e, 0x24, 0x37, 0xe7, 0x0d, 0xe4, 0xa0, 0x22, 0x4a, 0xe1, 0x59, 0x1f,
        0x97, 0x03, 0x57, 0x54, 0xf0, 0xca, 0x92, 0x75, 0x2f, 0x9e, 0x86, 0xeb, 0x82, 0x4f, 0x9c,
        0xf4, 0x02, 0x17, 0x7f, 0x76, 0x56, 0x26, 0x46, 0xf4, 0x07, 0xfd, 0x1f, 0x78, 0xdb, 0x7b,
        0x0d, 0x24, 0x43, 0xf0,
    ];
    assert_eq!(
        expected.iter().map(|x| *x).collect::<Vec<_>>(),
        h.iter().map(|x| U8::declassify(*x)).collect::<Vec<_>>()
    );
}

create_test_vectors!(
    OfficialKat,
    hash: String,
    r#in: String,
    key: String,
    out: String
);

#[test]
fn test_official_kat() {
    let kat: Vec<OfficialKat> = OfficialKat::from_file("tests/blake2-kat.json");

    for test in kat.iter() {
        if test.hash == "blake2b" && test.key == "" {
            println!("expected: {}", test.out);
            let h = blake2b(&ByteSeq::from_hex(&test.r#in));
            assert_secret_seq_eq!(
                ByteSeq::from_hex(&test.out),
                ByteSeq::from_slice(&h, 0, h.len()),
                U8
            );
        }
    }
}
