use hacspec::prelude::*;

#[test]
fn test_public_array_u32() {
    array!(TestSeq, 64, u32);

    both_arrays!(PublicState, State, 73, U32, u32);
    let x = PublicState::new();
    let y: State = x.into();
    let _z: PublicState = y.into();
}

// ==== Test Array Numeric Implementation ==== //

#[test]
fn test_ops_u8() {
    array!(Bytes55, 55, u8);
    let x = Bytes55::random();
    let y = Bytes55::random();
    let _z = x + y;
    let _z = x - y;
    let _z = x * y;
    let _z = x / y;
}

#[test]
fn test_ops_u16() {
    array!(Array55, 55, u16);
    let x = Array55::random();
    let y = Array55::random();
    let _z = x + y;
    let _z = x - y;
    let _z = x * y;
    let _z = x / y;
}

#[test]
fn test_ops_u32() {
    array!(Array55, 55, u32);
    let x = Array55::random();
    let y = Array55::random();
    let _z = x + y;
    let _z = x - y;
    let _z = x * y;
    let _z = x / y;
}

#[test]
fn test_ops_u64() {
    array!(Array55, 55, u64);
    let x = Array55::random();
    let y = Array55::random();
    let _z = x + y;
    let _z = x - y;
    let _z = x * y;
    let _z = x / y;
}

#[test]
fn test_ops_u128() {
    array!(Array55, 55, u128);
    let x = Array55::random();
    let y = Array55::random();
    let _z = x + y;
    let _z = x - y;
    let _z = x * y;
    let _z = x / y;
}
