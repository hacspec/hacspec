use core::convert::TryInto;

use hacspec_lib::prelude::*;

mod test_util;
use test_util::*;

#[test]
#[allow(non_snake_case)]
fn test_array_U32() {
    array!(TestSeq, 64, U32);

    both_arrays!(PublicState, State, 73, U32, u32);
    let x = PublicState::new();
    let y: State = State::from_public(x);
    let _z: PublicState = PublicState::from_secret_declassify(y);
}

// ==== Test Array Numeric Implementation ==== //

#[test]
fn test_ops_u8() {
    array!(Array55, 55, U8);
    let x = Array55::from_native_slice(&get_random_vec_U8(55));
    let y = Array55::from_native_slice(&get_random_vec_U8(55));
    let _z = x + y;
    let _z = x - y;
    let _z = x * y;
}

#[test]
fn test_ops_u16() {
    array!(Array55, 55, U16);
    let x = Array55::from_native_slice(&get_random_vec_U16(55));
    let y = Array55::from_native_slice(&get_random_vec_U16(55));
    let _z = x + y;
    let _z = x - y;
    let _z = x * y;
}

#[test]
fn test_ops_u32() {
    array!(Array55, 55, U32);
    let x = Array55::from_native_slice(&get_random_vec_U32(55));
    let y = Array55::from_native_slice(&get_random_vec_U32(55));
    let _z = x + y;
    let _z = x - y;
    let _z = x * y;
}

#[test]
fn test_ops_u64() {
    array!(Array55, 55, U64);
    let x = Array55::from_native_slice(&get_random_vec_U64(55));
    let y = Array55::from_native_slice(&get_random_vec_U64(55));
    let _z = x + y;
    let _z = x - y;
    let _z = x * y;
}

#[test]
fn test_ops_u128() {
    array!(Array55, 55, U128);
    let x = Array55::from_native_slice(&get_random_vec_U128(55));
    let y = Array55::from_native_slice(&get_random_vec_U128(55));
    let _z = x + y;
    let _z = x - y;
    let _z = x * y;
}

#[test]
fn test_to_native() {
    bytes!(MyBytes, 78);
    let original: [u8; 78] = get_random_vec_u8(78).try_into().unwrap();
    let secret_bytes = MyBytes::from_public_slice(&original);
    let native_public_again = secret_bytes.to_public_array();
    assert_eq!(original, native_public_again);
}
