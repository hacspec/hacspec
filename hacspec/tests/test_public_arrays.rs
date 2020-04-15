use hacspec::prelude::*;

#[test]
fn test_public_array_u32() {
    array!(TestSeq, 64, u32);

    both_arrays!(PublicState, State, 73, U32, u32);
    let x = PublicState::new();
    let y: State = State::from_public(x);
    let _z: PublicState = PublicState::from_secret_declassify(y);
}

// ==== Test Array Numeric Implementation ==== //


#[test]
fn test_ops_u8() {
    array!(Bytes55, 55, u8);
    let x = Bytes55::random();
    let y = Bytes55::random();
    let z1 = x + y;
    let z2 = x - z1;
    let mut z3 = x * z2;
    for i in 0..z3.len() {
        if z3[i] == 0 {
            z3[i] = 1
        }
    }
    let _z = x / z3;
}

#[test]
fn test_ops_u16() {
    array!(Array55, 55, u16);
    let x = Array55::random();
    let y = Array55::random();
    let z1 = x + y;
    let z2 = x - z1;
    let mut z3 = x * z2;
    for i in 0..z3.len() {
        if z3[i] == 0 {
            z3[i] = 1
        }
    }
    let _z = x / z3;
}

#[test]
fn test_ops_u32() {
    array!(Array55, 55, u32);
    let x = Array55::random();
    let y = Array55::random();
    let z1 = x + y;
    let z2 = x - z1;
    let mut z3 = x * z2;
    for i in 0..z3.len() {
        if z3[i] == 0 {
            z3[i] = 1
        }
    }
    let _z = x / z3;
}

#[test]
fn test_ops_u64() {
    array!(Array55, 55, u64);
    let x = Array55::random();
    let y = Array55::random();
    let z1 = x + y;
    let z2 = x - z1;
    let mut z3 = x * z2;
    for i in 0..z3.len() {
        if z3[i] == 0 {
            z3[i] = 1
        }
    }
    let _z = x / z3;
}

#[test]
fn test_ops_u128() {
    array!(Array55, 55, u128);
    let x = Array55::random();
    let y = Array55::random();
    let z1 = x + y;
    let z2 = x - z1;
    let mut z3 = x * z2;
    for i in 0..z3.len() {
        if z3[i] == 0 {
            z3[i] = 1
        }
    }
    let _z = x / z3;
}
