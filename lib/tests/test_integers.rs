#![allow(non_snake_case)]

use hacspec_lib::prelude::*;
mod test_util;
use test_util::*;

macro_rules! compare_secret {
    ($a:expr,$b:expr) => {
        assert_eq!($a.declassify(), $b);
    };
}

macro_rules! test_integer_macro {
    ($t:ty,$true_val:expr,$false_val:expr,$check:ident) => {
        let (a, a_t, b, b_t) = get_random_numbers::<$t>();
        println!("a:   {} | b:   {}", a, b);
        println!("a_t: {:x} | b_t: {:x}", a_t, b_t);

        println!(" Test modulo");
        if !b_t.equal(<$t>::default()) {
            let r = a_t.modulo(b_t);
            let expected = get_expected("%", &a, &b);
            assert_eq!(format!("0x{:x}", r), expected);
        }

        // Comparison functions returning bool.
        println!(" Test equal");
        assert_eq!(a_t.equal(b_t), a == b);
        assert!(a_t.equal(a_t));
        assert!(b_t.equal(b_t));
        let expected_gt = if get_expected(">", &a, &b) == "0x0" {
            false
        } else {
            true
        };
        println!(" Test greater_than");
        assert_eq!(a_t.greater_than(b_t), expected_gt);
        assert_eq!(a_t.greater_than(a_t), false);
        assert_eq!(b_t.greater_than(b_t), false);
        let expected_gte = if get_expected(">=", &a, &b) == "0x0" {
            false
        } else {
            true
        };
        println!(" Test greater_than_or_equal");
        assert_eq!(a_t.greater_than_or_qual(b_t), expected_gte);
        assert_eq!(a_t.greater_than_or_qual(a_t), true);
        assert_eq!(b_t.greater_than_or_qual(b_t), true);
        let expected_lt = if get_expected("<", &a, &b) == "0x0" {
            false
        } else {
            true
        };
        println!(" Test less_than");
        assert_eq!(a_t.less_than(b_t), expected_lt);
        assert_eq!(a_t.less_than(a_t), false);
        assert_eq!(b_t.less_than(b_t), false);
        let expected_lte = if get_expected("<=", &a, &b) == "0x0" {
            false
        } else {
            true
        };
        println!(" Test less_than_or_equal");
        assert_eq!(a_t.less_than_or_equal(b_t), expected_lte);
        assert_eq!(a_t.less_than_or_equal(a_t), true);
        assert_eq!(b_t.less_than_or_equal(b_t), true);

        // Comparison functions returning a bit mask (0x0..0 or 0xF..F).
        let expected = if a == b { $true_val } else { $false_val };
        println!(" Test equal_bm");
        $check!(a_t.equal_bm(b_t), expected);
        $check!(a_t.equal_bm(a_t), $true_val);
        $check!(b_t.equal_bm(b_t), $true_val);
        let expected = if expected_gt { $true_val } else { $false_val };
        println!(" Test greater_than_bm");
        $check!(a_t.greater_than_bm(b_t), expected);
        $check!(a_t.greater_than_bm(a_t), $false_val);
        $check!(b_t.greater_than_bm(b_t), $false_val);
        let expected = if expected_gte { $true_val } else { $false_val };
        println!(" Test greater_than_or_equal_bm");
        $check!(a_t.greater_than_or_equal_bm(b_t), expected);
        $check!(a_t.greater_than_or_equal_bm(a_t), $true_val);
        $check!(b_t.greater_than_or_equal_bm(b_t), $true_val);
        let expected = if expected_lt { $true_val } else { $false_val };
        println!(" Test less_than_bm");
        $check!(a_t.less_than_bm(b_t), expected);
        $check!(a_t.less_than_bm(a_t), $false_val);
        $check!(b_t.less_than_bm(b_t), $false_val);
        let expected = if expected_lte { $true_val } else { $false_val };
        println!(" Test less_than_or_equal_bm");
        $check!(a_t.less_than_or_equal_bm(b_t), expected);
        $check!(a_t.less_than_or_equal_bm(a_t), $true_val);
        $check!(b_t.less_than_or_equal_bm(b_t), $true_val);
    };
}

macro_rules! generate_test {
    ($t:ty,$name:ident,$true_val:expr,$false_val:expr,$check:ident) => {
        #[test]
        fn $name() {
            test_integer_macro!($t, $true_val, $false_val, $check);
        }
    };
}

// Public machine integers
generate_test!(u8, test_u8_integer, u8::max_value(), 0, assert_eq);
generate_test!(u16, test_u16_integer, u16::max_value(), 0, assert_eq);
generate_test!(u32, test_u32_integer, u32::max_value(), 0, assert_eq);
generate_test!(u64, test_u64_integer, u64::max_value(), 0, assert_eq);
generate_test!(u128, test_u128_integer, u128::max_value(), 0, assert_eq);
generate_test!(i8, test_i8_integer, -1, 0, assert_eq);
generate_test!(i16, test_i16_integer, -1, 0, assert_eq);
generate_test!(i32, test_i32_integer, -1, 0, assert_eq);
generate_test!(i64, test_i64_integer, -1, 0, assert_eq);
generate_test!(i128, test_i128_integer, -1, 0, assert_eq);

// Secret machine integers
generate_test!(
    U8,
    test_U8_integer,
    U8::max_value().declassify(),
    0,
    compare_secret
);
generate_test!(
    U16,
    test_U16_integer,
    U16::max_value().declassify(),
    0,
    compare_secret
);
generate_test!(
    U32,
    test_U32_integer,
    U32::max_value().declassify(),
    0,
    compare_secret
);
generate_test!(
    U64,
    test_U64_integer,
    U64::max_value().declassify(),
    0,
    compare_secret
);
generate_test!(
    U128,
    test_U128_integer,
    U128::max_value().declassify(),
    0,
    compare_secret
);
generate_test!(I8, test_I8_integer, -1, 0, compare_secret);
generate_test!(I16, test_I16_integer, -1, 0, compare_secret);
generate_test!(I32, test_I32_integer, -1, 0, compare_secret);
generate_test!(I64, test_I64_integer, -1, 0, compare_secret);
generate_test!(I128, test_I128_integer, -1, 0, compare_secret);

// Math integers

// Public natural numbers modulo p
public_nat_mod!(
    type_name: PublicP256Elem,
    type_of_canvas: PublicP256Canvas,
    bit_size_of_field: 256,
    modulo_value: "ffffffff00000001000000000000000000000000ffffffffffffffffffffffff"
);
generate_test!(
    PublicP256Elem,
    test_PublicNatMod_integer,
    PublicP256Elem::from_hex_string(
        &"0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff".to_string()
    ),
    PublicP256Elem::ZERO(),
    assert_eq
);

// Secret natural numbers modulo p
nat_mod!(
    type_name: P256Elem,
    type_of_canvas: P256Canvas,
    bit_size_of_field: 256,
    modulo_value: "ffffffff00000001000000000000000000000000ffffffffffffffffffffffff"
);
generate_test!(
    P256Elem,
    test_NatMod_integer,
    BigInt::from_str_radix(
        "7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
        16
    )
    .unwrap(),
    BigInt::from(0),
    compare_secret
);

// vec integer tests

#[test]
fn test_byte_array_integer() {
    bytes!(State, 8);
    fn test(a: [u8; 8], b: [u8; 8], result: bool) {
        let a = State::from_public_array(a);
        let b = State::from_public_array(b);
        assert_eq!(a.equal(b), result);
    }

    test(
        [0x12, 0x34, 0x56, 0x78, 0x90, 0xab, 0xcd, 0xef],
        [0x12, 0x34, 0x56, 0x78, 0x90, 0xab, 0xcd, 0xef],
        true,
    );
    test(
        [0x11, 0x34, 0x56, 0x78, 0x90, 0xab, 0xcd, 0xef],
        [0x12, 0x34, 0x56, 0x78, 0x90, 0xab, 0xcd, 0xef],
        false,
    );
    test(
        [0x12, 0x34, 0x56, 0x78, 0x90, 0xab, 0xcd, 0xef],
        [0x11, 0x34, 0x56, 0x78, 0x90, 0xab, 0xcd, 0xef],
        false,
    );
    test(
        [0x12, 0x34, 0x56, 0x78, 0x91, 0xab, 0xcd, 0xef],
        [0x12, 0x34, 0x56, 0x78, 0x90, 0xab, 0xcd, 0xef],
        false,
    );
    test(
        [0x12, 0x34, 0x56, 0x78, 0x90, 0xab, 0xcd, 0xef],
        [0x12, 0x34, 0x56, 0x78, 0x90, 0xab, 0xcd, 0xee],
        false,
    );
    test(
        [0x12, 0x34, 0x56, 0x78, 0x90, 0xab, 0xcd, 0xee],
        [0x12, 0x34, 0x56, 0x78, 0x90, 0xab, 0xcd, 0xef],
        false,
    );
}
