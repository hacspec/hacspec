use secret_integers::*;

#[test]
fn test_from_public() {
    let a = U8(123u8);
    let a = U16(1234u16);
    let a = U32(123456u32);
    let a = U64(123456u64);
    let a = U128(123456u128);

    let a = U8::from(123u8);
    let a = U16::from(1234u16);
    let a = U32::from(123456u32);
    let a = U64::from(123456u64);
    let a = U128::from(123456u128);

    let a = U8::from(123u8);
    let a = U16::from(123u8);
    let a = U32::from(123u8);
    let a = U64::from(123u8);
    let a = U128::from(123u8);

    let a = I8(123i8);
    let a = I16(1234i16);
    let a = I32(123456i32);
    let a = I64(123456i64);
    let a = I128(123456i128);
    
    let a = I8::from(123i8);
    let a = I16::from(1234i16);
    let a = I32::from(123456i32);
    let a = I64::from(123456i64);
    let a = I128::from(123456i128);

    // TODO: not implemented
    // let a = I8::from(123i8);
    // let a = I16::from(123i8);
    // let a = I32::from(123i8);
    // let a = I64::from(123i8);
    // let a = I128::from(123i8);
}
