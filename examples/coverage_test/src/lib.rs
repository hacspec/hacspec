// Import hacspec and all needed definitions.
use hacspec_lib::*;

array!(ArrName, 8, U64);
bytes!(ByteArrName, 128);

// both_bytes!(BothType, BothTypeSecret, 8); // unknown hacspec macro ?
// both_arrays!(BothType, BothTypeSecret, 8, U8, u8); // unknown hacspec macro ?
pub fn array_test () {
    // Hash::from_hex("22");
    let hs = ArrName::new();
    hs.len();
    hs[2_usize];
    hs.declassify_eq(&hs);
    hs.to_be_bytes();
    hs.to_le_bytes();
    let hs = ByteArrName::new();
    hs.to_be_U32s();
    hs.to_le_U32s();
    hs.to_be_U64s();
    hs.to_le_U64s();    
    hs.to_U128s_be();
    hs.to_U128s_le();
    // BothTypeSecret::from_public(BothType::new());
    // BothType::from_secret_declassify(BothTypeSecret::new());

    ByteArrName::length();
    ByteArrName::from_slice(&hs,0,2);
    ByteArrName::from_slice(&ByteSeq::new(3),0,2);

    hs.concat(&hs);
    hs.concat(&ByteSeq::new(3));

    ByteArrName::from_slice_range(&hs,0..2);
    ByteArrName::from_slice_range(&ByteSeq::new(3),0..2);

    hs.num_chunks(2);
    hs.get_chunk_len(2, 2);
    hs.get_chunk(2, 2);

    hs.set_chunk(2, 2, &hs);
    hs.set_chunk(2, 2, &ByteSeq::new(3));

    ByteArrName::default();
    
    ByteArrName::create(128);
    hs.update_slice(0, &hs, 1, 2);
    hs.update_slice(0, &ByteSeq::new(3), 1, 2);

    hs.update(0, &hs);
    hs.update(0, &ByteSeq::new(3));

    hs.update_start(&hs);
    hs.update_start(&ByteSeq::new(3));

    ByteArrName::from_seq(&hs);
    ByteArrName::from_seq(&ByteSeq::new(3));
}

pub fn seq_test () {
    let mut ns = Seq::<u8>::new(5);
    ns = Seq::<u8>::with_capacity(5);
    ns = ns.reserve(10);
    ns.len();
    ns = ns.slice(0, 5);
    ns = ns.into_slice(2,3);
    ns = ns.slice_range(1..3);
    ns = ns.into_slice_range(2..3);
    let (mut ns1 , mut ns2) = ns.split_off(2);
    ns1 = ns1.truncate(2);
    ns2 = Seq::<u8>::from_slice(&ns1,0,2);
    let mut ns = ns1.concat(&ns2);
    ns = ns1.concat_owned(ns2);
    ns = ns.push(&2_u8);
    ns = ns.push_owned(4_u8);
    ns = Seq::<u8>::from_slice_range(&ns, 0..4);
    ns.num_chunks(2);
    ns.num_exact_chunks(2);
    let (l, mut ns) = ns.get_chunk(2, 0);
    ns = ns.get_exact_chunk(2, 1);
    ns = ns.get_remainder_chunk(2);
    ns = ns.set_chunk(2, 0, &Seq::<u8>::new(2));
    ns = ns.set_exact_chunk(2, 0, &Seq::<u8>::new(2));
    let mut us = Seq::<u8>::create(12);
    us = us.update_slice(0, &ns, 2, 4);
    us = us.update_start(&ns);
    us.index(3_u8);
    us.index_mut(3_u8);
    Seq::<u8>::from_seq(ns);
}
