use hacspec::prelude::*;
mod test_util;
use test_util::*;

fn get_random_numbers<T: Integer>() -> (String, T, String, T) {
    let a = random_hex_string(T::NUM_BITS as usize >> 3);
    let b = random_hex_string(T::NUM_BITS as usize >> 3);
    let a_t = T::from_hex_string(&a);
    let b_t = T::from_hex_string(&b);
    (a, a_t, b, b_t)
}

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
                let expected = get_expected("mul", &a, &b);
                let res_s = format!("0x{:x}", r);
                assert_eq!(res_s, expected);
            }
            Err(_) => (),
        }
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

macro_rules! test_unsigned_secret_macro {
    ($t:ty) => {
        assert!(<$t>::max_val().equal(<$t>::max_value()));
        assert!(<$t>::from(3u8).exp(5).equal(<$t>::from(243u8)));
        // assert_eq!((3 as $t).pow_self(5), 243);
        // ...
    };
}

#[test]
fn test_unsigned_secret() {
    test_unsigned_secret_macro!(U8);
    test_unsigned_secret_macro!(U16);
    test_unsigned_secret_macro!(U32);
    test_unsigned_secret_macro!(U64);
    test_unsigned_secret_macro!(U128);
}

macro_rules! test_signed_secret_macro {
    ($t:ty) => {
        assert!(<$t>::max_val().equal(<$t>::max_value()));
        assert!(<$t>::from(2).exp(5).equal(<$t>::from(32)));
        // assert_eq!((2 as $t).pow_self(5), 32);
        // ...
    };
}

#[test]
fn test_signed_secret() {
    test_signed_secret_macro!(I8);
    test_signed_secret_macro!(I16);
    test_signed_secret_macro!(I32);
    test_signed_secret_macro!(I64);
    test_signed_secret_macro!(I128);
}
