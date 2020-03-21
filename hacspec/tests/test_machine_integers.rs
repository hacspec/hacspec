use hacspec::prelude::*;

macro_rules! test_unsigned_public_macro {
    ($t:ty) => {
        assert_eq!(<$t>::max_val(), <$t>::max_value() as $t);
        assert_eq!((3 as $t).pow(5), 243);
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
        assert_eq!((2 as $t).pow(5), 32);
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
        assert!(<$t>::from(3u8).pow(5).equal(<$t>::from(243u8)));
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

macro_rules! test_signed_secert_macro {
    ($t:ty) => {
        assert!(<$t>::max_val().equal(<$t>::max_value()));
        assert!(<$t>::from(2).pow(5).equal(<$t>::from(32)));
        // assert_eq!((2 as $t).pow_self(5), 32);
        // ...
    };
}

#[test]
fn test_signed_secret() {
    test_signed_secert_macro!(I8);
    test_signed_secert_macro!(I16);
    test_signed_secert_macro!(I32);
    test_signed_secert_macro!(I64);
    test_signed_secert_macro!(I128);
}
