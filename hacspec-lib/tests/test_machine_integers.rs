use hacspec_lib::prelude::*;
mod test_util;
use test_util::*;

macro_rules! test_unsigned_public_macro {
    ($t:ty) => {
        assert_eq!(<$t>::max_val(), <$t>::max_value() as $t);
        assert_eq!((3 as $t).exp(5), 243);
        // assert_eq!((3 as $t).pow_self(5), 243);
        // ...
    };
}

#[test]
fn test_unsigned_public() {
    test_unsigned_public_macro!(u8);
    test_unsigned_public_macro!(u16);
    test_unsigned_public_macro!(u32);
    test_unsigned_public_macro!(u64);
    test_unsigned_public_macro!(u128);
}

macro_rules! test_signed_public_macro {
    ($t:ty) => {
        assert_eq!(<$t>::max_val(), <$t>::max_value());

        let (a, a_t, b, b_t) = get_random_numbers::<$t>();

        // multiplication operator might panic on overflow
        let res = std::panic::catch_unwind(|| a_t * b_t);
        match res {
            Ok(r) => {
                let expected = get_expected("*", &a, &b);
                let res_s = format!("0x{:x}", r);
                assert_eq!(res_s, expected);
            }
            Err(_) => (),
        }
        assert_eq!((6 as $t).pow_mod(8, 127), 41);

        // assert_eq!((2 as $t).pow_self(5), 32);
        // ...
    };
}

#[test]
fn test_signed_public() {
    test_signed_public_macro!(i8);
    test_signed_public_macro!(i16);
    test_signed_public_macro!(i32);
    test_signed_public_macro!(i64);
    test_signed_public_macro!(i128);
}

macro_rules! test_secret_macro {
    ($t:ty,$true_val:expr) => {
        assert!(<$t>::max_val().equal(<$t>::max_value()));

        let (a, a_t, b, b_t) = get_random_numbers::<$t>();

        // mod
        if !b_t.equal(<$t>::ZERO()) {
            let r = a_t.modulo(b_t);
            let expected = get_expected("%", &a, &b);
            assert_eq!(format!("0x{:x}", r), expected);
        }

        // Comparison functions returning bool.
        assert_eq!(a_t.equal(b_t), a == b);
        let expected_gt = if get_expected(">", &a, &b) == "0x0" {
            false
        } else {
            true
        };
        assert_eq!(a_t.greater_than(b_t), expected_gt);
        let expected_gte = if get_expected(">=", &a, &b) == "0x0" {
            false
        } else {
            true
        };
        assert_eq!(a_t.greater_than_or_qual(b_t), expected_gte);
        let expected_lt = if get_expected("<", &a, &b) == "0x0" {
            false
        } else {
            true
        };
        assert_eq!(a_t.less_than(b_t), expected_lt);
        let expected_lte = if get_expected("<=", &a, &b) == "0x0" {
            false
        } else {
            true
        };
        assert_eq!(a_t.less_than_or_equal(b_t), expected_lte);

        // Comparison functions returning a bit mask (0x0..0 or 0xF..F).
        let expected = if a == b { $true_val } else { 0 };
        assert_eq!(a_t.equal_bm(b_t).declassify(), expected);
        let expected = if expected_gt { $true_val } else { 0 };
        assert_eq!(a_t.greater_than_bm(b_t).declassify(), expected);
        let expected = if expected_gte { $true_val } else { 0 };
        assert_eq!(a_t.greater_than_or_equal_bm(b_t).declassify(), expected);
        let expected = if expected_lt { $true_val } else { 0 };
        assert_eq!(a_t.less_than_bm(b_t).declassify(), expected);
        let expected = if expected_lte { $true_val } else { 0 };
        assert_eq!(a_t.less_than_or_equal_bm(b_t).declassify(), expected);
    };
}

#[test]
fn test_unsigned_secret() {
    test_secret_macro!(U8, U8::max_value().declassify());
    test_secret_macro!(U16, U16::max_value().declassify());
    test_secret_macro!(U32, U32::max_value().declassify());
    test_secret_macro!(U64, U64::max_value().declassify());
    test_secret_macro!(U128, U128::max_value().declassify());
}

#[test]
fn test_signed_secret() {
    test_secret_macro!(I8, -1);
    test_secret_macro!(I16, -1);
    test_secret_macro!(I32, -1);
    test_secret_macro!(I64, -1);
    test_secret_macro!(I128, -1);
}

#[test]
fn test_secret_testing() {
    let (a, a_t, b, b_t) = get_random_numbers::<I8>();

    // mod
    if !b_t.equal(<I8>::ZERO()) {
        let r = a_t.modulo(b_t);
        let expected = get_expected("%", &a, &b);
        assert_eq!(format!("0x{:x}", r), expected);
    }

    // Comparison functions returning bool.
    assert_eq!(a_t.equal(b_t), a == b);
    let expected_gt = if get_expected(">", &a, &b) == "0x0" {
        false
    } else {
        true
    };
    assert_eq!(a_t.greater_than(b_t), expected_gt);
    let expected_gte = if get_expected(">=", &a, &b) == "0x0" {
        false
    } else {
        true
    };
    assert_eq!(a_t.greater_than_or_qual(b_t), expected_gte);
    let expected_lt = if get_expected("<", &a, &b) == "0x0" {
        false
    } else {
        true
    };
    assert_eq!(a_t.less_than(b_t), expected_lt);
    let expected_lte = if get_expected("<=", &a, &b) == "0x0" {
        false
    } else {
        true
    };
    assert_eq!(a_t.less_than_or_equal(b_t), expected_lte);

    // Comparison functions returning a bit mask (0x0..0 or 0xF..F).
    let expected = if a == b { -1 } else { 0 };
    assert_eq!(a_t.equal_bm(b_t).declassify(), expected);
    let expected = if expected_gt { -1 } else { 0 };
    assert_eq!(a_t.greater_than_bm(b_t).declassify(), expected);
    let expected = if expected_gte { -1 } else { 0 };
    assert_eq!(a_t.greater_than_or_equal_bm(b_t).declassify(), expected);
    let expected = if expected_lt { -1 } else { 0 };
    assert_eq!(a_t.less_than_bm(b_t).declassify(), expected);
    let expected = if expected_lte { -1 } else { 0 };
    assert_eq!(a_t.less_than_or_equal_bm(b_t).declassify(), expected);
}
