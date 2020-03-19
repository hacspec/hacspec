use secret_integers::*;

#[test]
fn test_from_public() {
    U8(123u8);
    U16(1234u16);
    U32(123456u32);
    U64(123456u64);
    U128(123456u128);

    U8::from(123u8);
    U16::from(1234u16);
    U32::from(123456u32);
    U64::from(123456u64);
    U128::from(123456u128);

    U8::from(123u8);
    U16::from(123u8);
    U32::from(123u8);
    U64::from(123u8);
    U128::from(123u8);

    I8(123i8);
    I16(1234i16);
    I32(123456i32);
    I64(123456i64);
    I128(123456i128);

    I8::from(123i8);
    I16::from(1234i16);
    I32::from(123456i32);
    I64::from(123456i64);
    I128::from(123456i128);

    // TODO: not implemented
    // I8::from(123i8);
    // I16::from(123i8);
    // I32::from(123i8);
    // I64::from(123i8);
    // I128::from(123i8);
}
