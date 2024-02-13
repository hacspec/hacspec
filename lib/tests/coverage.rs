// Import hacspec and all needed definitions.
use hacspec_lib::*;

pub fn big_integer_test () {
    /////////////////////////
    // lib/big_integers.rs //
    /////////////////////////

    BigInt::ZERO();
    BigInt::ONE();
    BigInt::TWO();
    let mut bi = BigInt::from_literal(1238_u128);

    bi = bi.get_bit(3);
    bi = bi.set_bit(BigInt::ONE(), 3);
    bi = bi.set(4, BigInt::TWO(), 2);
    let mut bi = BigInt::from_literal(1238_u128);
    // bi = bi.rotate_left(1); // NUM_BITS is 0 resulting in error!
    // bi = bi.rotate_right(4); // NUM_BITS is 0 resulting in error!

    // BigInt::max_val(); // unimplemented!
    bi = bi.wrap_add(BigInt::TWO());
    bi = bi.wrap_sub(BigInt::TWO());
    bi = bi.wrap_mul(BigInt::TWO());
    // bi = bi.wrap_div(BigInt::TWO()); // unimplemented

    // bi = bi.exp(2_u32); // unimplemented
    // bi = bi.pow_self(BigInt::TWO()); // unimplemented
    // bi = bi.divide(BigInt::TWO()); // unimplemented
    // bi = bi.inv(BigInt::TWO()); // unimplemented
    let _ : bool = BigInt::ONE().equal(BigInt::TWO()); // unimplemented

    // let _ : bool = BigInt::ONE().greater_than(BigInt::TWO()); // unimplemented
    // let _ : bool = BigInt::ONE().greater_than_or_equal(BigInt::TWO()); // unimplemented
    let _ : bool = BigInt::ONE().less_than(BigInt::TWO()); // unimplemented
    // let _ : bool = BigInt::ONE().less_than_or_equal(BigInt::TWO()); // unimplemented

    // bi = bi.not_equal_bm(BigInt::TWO()); // unimplemented
    // bi = bi.equal_bm(BigInt::TWO()); // unimplemented
    // bi = bi.greater_than_bm(BigInt::TWO()); // unimplemented
    // bi = bi.greater_than_or_equal_bm(BigInt::TWO()); // unimplemented
    // bi = bi.less_than_bm(BigInt::TWO()); // unimplemented
    // bi = bi.less_than_or_equal_bm(BigInt::TWO()); // unimplemented

    bi = bi.sub_mod(BigInt::TWO(), BigInt::from_literal(4_u128));
    bi = bi.add_mod(BigInt::TWO(), BigInt::from_literal(4_u128));
    bi = bi.mul_mod(BigInt::TWO(), BigInt::from_literal(4_u128));
    // bi = bi.pow_mod(BigInt::TWO(), BigInt::from_literal(4_u128)); // unimplemented
    bi = bi.modulo(BigInt::from_literal(4_u128));
    bi = bi.absolute();
}

#[test]
fn test_big_integer () {
    big_integer_test();
    BigInt::from_hex_string(&String::from("528")); // expected type &string for function argument, got string
    let sbi = BigInt::classify(BigInt::from_literal(1238_u128)); // classify is known but its signature is not in Hacspec
}

fn machine_integer_test () {
    /////////////////////////////
    // lib/machine_integers.rs //
    /////////////////////////////
    u32::ZERO();
    u8::ONE();
    u128::TWO();
    let mut mi = u16::from_literal(1238_u128);
    // u16::from_hex_string(&String::from(""));
    mi = mi.get_bit(3);
    mi = mi.set_bit(u16::ONE(), 3);
    mi = mi.set(4, u16::TWO(), 2);
    mi = mi.rotate_left(4u32);
    mi = mi.rotate_right(4u32);

    u16::max_val();
    mi = mi.wrap_add(u16::TWO());
    mi = mi.wrap_sub(u16::TWO());
    mi = mi.wrap_mul(u16::TWO());
    // mi = mi.wrap_div(u16::TWO()); // unimplemented

    mi = mi.exp(2_u32);
    // mi = mi.pow_self(u16::TWO()); // unimplemented
    mi = mi.divide(u16::TWO());
    mi = u16::from_literal(79_u128).inv(u16::TWO());
    let _ : bool = u16::ONE().equal(u16::TWO());

    let _ : bool = u16::ONE().greater_than(u16::TWO());
    let _ : bool = u16::ONE().greater_than_or_equal(u16::TWO());
    let _ : bool = u16::ONE().less_than(u16::TWO());
    let _ : bool = u16::ONE().less_than_or_equal(u16::TWO());

    mi = mi.not_equal_bm(u16::TWO());
    mi = mi.equal_bm(u16::TWO());
    mi = mi.greater_than_bm(u16::TWO());
    mi = mi.greater_than_or_equal_bm(u16::TWO());
    mi = mi.less_than_bm(u16::TWO());
    mi = mi.less_than_or_equal_bm(u16::TWO());

    mi = mi.sub_mod(u16::TWO(), u16::from_literal(4_u128));
    mi = mi.add_mod(u16::TWO(), u16::from_literal(4_u128));
    mi = mi.mul_mod(u16::TWO(), u16::from_literal(4_u128));
    // mi = mi.pow_mod(u16::TWO(), u16::from_literal(4_u128)); // unimplemented!
    mi = mi.absolute();

    U64(12_u64);
}

#[test]
fn test_machine_integer () {
    machine_integer_test()
}

pub fn seq_test () {
    ////////////////
    // lib/seq.rs //
    ////////////////

    let mut ns = Seq::<u8>::with_capacity(5);
    ns = Seq::<u8>::new(5);
    ns = ns.reserve(10);
    ns.len();
    ns = ns.slice(0, 5);

    ns = ns.into_slice(1,3);
    ns = ns.slice_range(0..2);
    ns = ns.into_slice_range(0..1);
    let (mut ns1 , mut ns2) = ns.split_off(1);
    ns1 = ns1.truncate(2);
    ns2 = Seq::<u8>::from_slice(&ns1,0,1);
    let mut ns : Seq<u8> = ns1.concat(&ns2);
    ns = ns1.concat_owned(ns2);
    ns = ns.push(&2_u8);
    ns = ns.push_owned(4_u8);
    ns = Seq::<u8>::from_slice_range(&ns, 0..4);
    ns.num_chunks(2);
    ns.num_exact_chunks(2);
    let (l, mut ns) : (usize , Seq<u8>) = ns.get_chunk(2, 0);
    ns.get_exact_chunk(3, 0);
    ns = ns.get_exact_chunk(2, 0);
    Seq::<u8>::new(0).get_remainder_chunk(1);
    ns.get_remainder_chunk(2);
    ns = ns.get_remainder_chunk(3);
    ns = ns.set_chunk(8, 0, &Seq::<u8>::new(2));
    ns = ns.set_chunk(2, 0, &Seq::<u8>::new(2));
    ns = ns.set_exact_chunk(2, 0, &Seq::<u8>::new(2));
    let mut us = Seq::<u8>::create(12);
    us = us.update_slice(0, &ns, 1, 1);
    us = us.update(0, &ns);
    us = us.update_start(&ns);
    us[3_u8];
    us[3_u32];
    us[3_i32];

    let ps : PublicSeq<u8> = public_byte_seq!(8_u8, 5_u8, 18_u8);
    let secret_seq : Seq<U8> = byte_seq!(8_u8, 5_u8, 18_u8);

    let c = Seq::<u8>::from_seq(&ns);


    let ss = Seq::<U8>::from_public_seq(&ns);
    Seq::<U16>::from_public_seq(&Seq::<u16>::new(0));
    Seq::<U32>::from_public_seq(&Seq::<u32>::new(0));
    Seq::<U64>::from_public_seq(&Seq::<u64>::new(0));
    Seq::<U128>::from_public_seq(&Seq::<u128>::new(0));


    let e = PublicSeq::<u8>::new(5);

    ps.to_hex();
    ss.to_hex();
    let d : Seq<u8> = ss.clone().declassify();

    let _ = c == d;
    let _ = e == ps;
    // clone needed otherwise we get the error:
    // error[Hacspec]: the variable ss_4853 is not present in the context
    let _ = ss.clone() == secret_seq;

    ss.clone().into_native();
    ss.to_native();

    let ss = Seq::<U16>::new(2);
    ss.clone().declassify();
    ss.clone().into_native();
    ss.to_native();

    let ss = Seq::<U32>::new(2);
    ss.clone().declassify();
    ss.clone().into_native();
    ss.to_native();

    let ss = Seq::<U64>::new(2);
    ss.clone().declassify();
    ss.clone().into_native();
    ss.to_native();

    let ss = Seq::<U128>::new(2);
    ss.clone().declassify();
    ss.clone().into_native();
    ss.to_native();

    ////////////////////////////////
    // lib/vec_integers_public.rs //
    ////////////////////////////////

    let mut ps : PublicSeq<u8> = public_byte_seq!(8_u8, 5_u8, 18_u8);
    let a : PublicSeq<u8> = public_byte_seq!(8_u8, 5_u8, 18_u8);
    let n : PublicSeq<u8> = public_byte_seq!(5_u8, 18_u8);

    // ps = ps.sub_mod(a.clone(), n.clone()); // unimplemented!
    // ps = ps.add_mod(a.clone(), n.clone()); // unimplemented!
    // ps = ps.mul_mod(a.clone(), n.clone()); // unimplemented!
    // ps = ps.pow_mod(a.clone(), n.clone()); // unimplemented!
    // ps = ps.absolute(); // unimplemented!

    // PublicSeq::<u8>::max_val(); // unimplemented!
    ps = ps.wrap_add(a.clone());
    ps = ps.wrap_sub(a.clone());
    ps = ps.wrap_mul(a.clone());
    // ps = ps.wrap_div(a.clone()); // unimplemented!

    // ps = ps.exp(2_u32); // unimplemented!
    // ps = ps.pow_self(a.clone()); // unimplemented!
    // ps = ps.divide(a.clone()); // unimplemented!
    // ps = ps.inv(a.clone()); // unimplemented!
    // let _ : bool = ps.clone().equal(a.clone()); // unimplemented!

    // let _ : bool = ps.clone().greater_than(a.clone()); // unimplemented!
    // let _ : bool = ps.clone().greater_than_or_equal(a.clone()); // unimplemented!
    // let _ : bool = ps.clone().less_than(a.clone()); // unimplemented!
    // let _ : bool = ps.clone().less_than_or_equal(a.clone()); // unimplemented!

    // ps = ps.not_equal_bm(a.clone()); // unimplemented!
    // ps = ps.equal_bm(a.clone()); // unimplemented!
    // ps = ps.greater_than_bm(a.clone()); // unimplemented!
    // ps = ps.greater_than_or_equal_bm(a.clone()); // unimplemented!
    // ps = ps.less_than_bm(a.clone()); // unimplemented!
    // ps = ps.less_than_or_equal_bm(a.clone()); // unimplemented!

    ps = ps * a.clone();
    ps = ps - a.clone();
    ps = ps + a.clone();
    ps = !ps;
    ps = ps | a.clone();
    ps = ps ^ a.clone();
    ps = ps & a.clone();
    // ps = ps >> 3; // unimplemented!
    // ps = ps << 3; // unimplemented!

    ////////////////////////////////
    // lib/vec_integers_secret.rs //
    ////////////////////////////////

    let mut ss : Seq<U8> = byte_seq!(8_u8, 5_u8, 18_u8);
    let a : Seq<U8> = byte_seq!(8_u8, 5_u8, 18_u8);
    let n : Seq<U8> = byte_seq!(5_u8, 18_u8);

    // ss = ss.sub_mod(a.clone(), n.clone()); // unimplemented!
    // ss = ss.add_mod(a.clone(), n.clone()); // unimplemented!
    // ss = ss.mul_mod(a.clone(), n.clone()); // unimplemented!
    // ss = ss.pow_mod(a.clone(), n.clone()); // unimplemented!
    // ss = ss.absolute(); // unimplemented!

    // Seq::<U8>::max_val(); // unimplemented!
    ss = ss.wrap_add(a.clone());
    ss = ss.wrap_sub(a.clone());
    ss = ss.wrap_mul(a.clone());
    // ss = ss.wrap_div(a.clone()); // unimplemented!

    // ss = ss.exp(2_u32); // unimplemented!
    // ss = ss.pow_self(a.clone()); // unimplemented!
    // ss = ss.divide(a.clone()); // unimplemented!
    // ss = ss.inv(a.clone()); // unimplemented!
    // let _ : bool = ss.clone().equal(a.clone()); // unimplemented!

    // let _ : bool = ss.clone().greater_than(a.clone()); // unimplemented!
    // let _ : bool = ss.clone().greater_than_or_equal(a.clone()); // unimplemented!
    // let _ : bool = ss.clone().less_than(a.clone()); // unimplemented!
    // let _ : bool = ss.clone().less_than_or_equal(a.clone()); // unimplemented!

    // ss = ss.not_equal_bm(a.clone()); // unimplemented!
    // ss = ss.equal_bm(a.clone()); // unimplemented!
    // ss = ss.greater_than_bm(a.clone()); // unimplemented!
    // ss = ss.greater_than_or_equal_bm(a.clone()); // unimplemented!
    // ss = ss.less_than_bm(a.clone()); // unimplemented!
    // ss = ss.less_than_or_equal_bm(a.clone()); // unimplemented!

    ss = ss.clone() + a.clone();
    ss = ss.clone() * a.clone();

    ss = ss * a.clone();
    ss = ss - a.clone();
    ss = ss + a.clone();
    ss = !ss;
    ss = ss | a.clone();
    ss = ss ^ a.clone();
    ss = ss & a.clone();
    // ss = ss >> 3; // unimplemented!
    // ss = ss << 3; // unimplemented!


    /////////////////////////
    // lib/vec_integers.rs //
    /////////////////////////

    // TODO: Fill in examples !
}

#[test]
pub fn test_seq () {
    seq_test();

    //array values are not allowed in Hacspec
    Seq::<u8>::from_native_slice(&[1, 2, 3, 4]);
    Seq::<U8>::from_public_slice(&[1,2,3]);
    Seq::<U16>::from_public_slice(&[1,2,3]);
    Seq::<U32>::from_public_slice(&[1,2,3]);
    Seq::<U64>::from_public_slice(&[1,2,3]);
    Seq::<U128>::from_public_slice(&[1,2,3]);

    let mut us = Seq::<u8>::new(5);
    us.native_slice(); // native_slice is known but its signature is not in Hacspec

    us.index(3_u8); // index is known but its signature is not in Hacspec
    us.index(3_usize..5_usize);
    us.index_mut(3_u8); // index_mut is known but its signature is not in Hacspec
    us.index_mut(3_u32);
    us.index_mut(3_i32);

    Seq::<U8>::from_hex("ff"); // from_hex is known but its signature is not in Hacspec

    Seq::<U8>::from_string(String::from("4682"));
    PublicSeq::<u8>::from_hex("ff");
    PublicSeq::<u8>::from_string(String::from("4682"));
}

array!(ArrName, 8, U64);
bytes!(ByteArrName, 128);

// both_bytes!(BothType, BothTypeSecret, 8); // unknown hacspec macro ?
// both_arrays!(BothType, BothTypeSecret, 8, U8, u8); // unknown hacspec macro ?
pub fn array_test () {
    ////////////////////
    // lib/prelude.rs //
    ////////////////////

    let s_U16Word = U16Word::new();
    let s_U32Word = U32Word::new();
    let s_U64Word = U64Word::new();
    let s_U128Word = U128Word::new();

    let s_u16Word = u16Word::new();
    let s_u32Word = u32Word::new();
    let s_u64Word = u64Word::new();
    let s_u128Word = u128Word::new();

    //////////////////////
    // lib/transmute.rs //
    //////////////////////

    let x_U16 = U16(3_u16);
    let x_U32 = U32(3_u32);
    let x_U64 = U64(3_u64);
    let x_U128 = U128(3_u128);

    let _ : U16Word = U16_to_le_bytes(x_U16);
    let _ : U16Word = U16_to_be_bytes(x_U16);
    let _ : U16 = U16_from_be_bytes(s_U16Word);
    let _ : U16 = U16_from_le_bytes(s_U16Word);
    let _ : U32Word = U32_to_le_bytes(x_U32);
    let _ : U32Word = U32_to_be_bytes(x_U32);
    let _ : U32 = U32_from_be_bytes(s_U32Word);
    let _ : U32 = U32_from_le_bytes(s_U32Word);
    let _ : U64Word = U64_to_le_bytes(x_U64);
    let _ : U64Word = U64_to_be_bytes(x_U64);
    let _ : U64 = U64_from_be_bytes(s_U64Word);
    let _ : U64 = U64_from_le_bytes(s_U64Word);
    let _ : U128Word = U128_to_le_bytes(x_U128);
    let _ : U128Word = U128_to_be_bytes(x_U128);
    let _ : U128 = U128_from_be_bytes(s_U128Word);
    let _ : U128 = U128_from_le_bytes(s_U128Word);

    let x_u16 = 3_u16;
    let x_u32 = 3_u32;
    let x_u64 = 3_u64;
    let x_u128 = 3_u128;

    let _ : u16Word = u16_to_le_bytes(x_u16);
    let _ : u16Word = u16_to_be_bytes(x_u16);
    let _ : u16 = u16_from_be_bytes(s_u16Word);
    let _ : u16 = u16_from_le_bytes(s_u16Word);
    let _ : u32Word = u32_to_le_bytes(x_u32);
    let _ : u32Word = u32_to_be_bytes(x_u32);
    let _ : u32 = u32_from_be_bytes(s_u32Word);
    let _ : u32 = u32_from_le_bytes(s_u32Word);
    let _ : u64Word = u64_to_le_bytes(x_u64);
    let _ : u64Word = u64_to_be_bytes(x_u64);
    let _ : u64 = u64_from_be_bytes(s_u64Word);
    let _ : u64 = u64_from_le_bytes(s_u64Word);
    let _ : u128Word = u128_to_le_bytes(x_u128);
    let _ : u128Word = u128_to_be_bytes(x_u128);
    let _ : u128 = u128_from_be_bytes(s_u128Word);
    let _ : u128 = u128_from_le_bytes(s_u128Word);

    //////////////////
    // lib/array.rs //
    //////////////////

    // Hash::from_hex("22");
    let hs = ArrName::new();
    let _ = hs.clone();
    hs.len();
    hs[2_usize];
    hs.declassify_eq(&hs);
    hs.to_be_bytes();
    hs.to_le_bytes();
    let mut hs = ByteArrName::new();
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

    hs.slice_range(1..2);

    hs.num_chunks(2);
    hs.get_chunk_len(10, 12);
    hs.get_chunk_len(2, 2);
    hs.get_chunk(2, 2);

    hs.set_chunk(128, 0, &hs);
    hs.set_chunk(2, 2, &ByteSeq::new(2));

    ByteArrName::default();

    ByteArrName::create(128);
    hs.update_slice(0, &hs, 1, 2);
    hs.update_slice(0, &ByteSeq::new(3), 1, 2);

    hs.update(0, &hs);
    hs.update(0, &ByteSeq::new(3));

    hs.update_start(&hs);
    hs.update_start(&ByteSeq::new(3));

    ByteArrName::from_seq(&hs);
    ByteArrName::from_seq(&ByteSeq::new(128));

    let _ = hs[1_u8];

    let _ = hs[1_u32];

    let _ = hs[1_i32];

    // hs.into_le_bytes();
    let _ = s_u64Word == s_u64Word;
    hs.to_hex();

    s_u16Word.into_le_bytes();

    s_u32Word.to_be_u32s();
    s_u32Word.to_le_u32s();

    s_u64Word.to_be_u64s();
    s_u64Word.to_le_u64s();

    s_u128Word.to_u128s_be();
    s_u128Word.to_u128s_le();

    s_u16Word.to_hex();
}

#[test]
pub fn test_array () {
    array_test();

    let mut hs = ByteArrName::new();
    for i in hs.iter() { } // expected a non-inclusive range expression here in Hacspec
    let _ = hs[..]; // missing left bound of the range
    ByteArrName::from_public_slice(&[1; 128]); // repeat statements are not allowed in hacspec
    ByteArrName::from_public_array([0; 128]); // repeat statements are not allowed in hacspec

    let _ = hs.index_mut(1_u8); // index_mut is known but its signature is not in Hacspec
    let _ = hs.index_mut(1_u32);
    let _ = hs.index_mut(1_i32);

    ByteArrName::hex_string_to_vec("12345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678");  // hex_string_to_vec is known but its signature is not in Hacspec
    ByteArrName::from_hex("1234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567812345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678"); // from_hex  is known but its signature is not in Hacspec

    hs.to_public_array(); // to_public_array is known but its signature is not in Hacspec
}
