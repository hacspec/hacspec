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
    let mut x = Bytes55::random();
    let mut y = Bytes55::random();
    let _z = x + y;
    let _z = x - y;
    let _z = x * y;
    for i in 0..x.len() {
        if x[i] == 0 {
            x[i] = 1
        }
    }
    for i in 0..y.len() {
        if y[i] == 0 {
            y[i] = 1
        }
    }
    let _z = x / y;
}

#[test]
fn test_ops_u16() {
    array!(Array55, 55, u16);
    let mut x = Array55::random();
    let mut y = Array55::random();
    let _z = x + y;
    let _z = x - y;
    let _z = x * y;
    for i in 0..x.len() {
        if x[i] == 0 {
            x[i] = 1
        }
    }
    for i in 0..y.len() {
        if y[i] == 0 {
            y[i] = 1
        }
    }
    let _z = x / y;
}

#[test]
fn test_ops_u32() {
    array!(Array55, 55, u32);
    let mut x = Array55::random();
    let mut y = Array55::random();
    let _z = x + y;
    let _z = x - y;
    let _z = x * y;
    for i in 0..x.len() {
        if x[i] == 0 {
            x[i] = 1
        }
    }
    for i in 0..y.len() {
        if y[i] == 0 {
            y[i] = 1
        }
    }
    let _z = x / y;
}

#[test]
fn test_ops_u64() {
    array!(Array55, 55, u64);
    let mut x = Array55::random();
    let mut y = Array55::random();
    let _z = x + y;
    let _z = x - y;
    let _z = x * y;
    for i in 0..x.len() {
        if x[i] == 0 {
            x[i] = 1
        }
    }
    for i in 0..y.len() {
        if y[i] == 0 {
            y[i] = 1
        }
    }
    let _z = x / y;
}

#[test]
fn test_ops_u128() {
    array!(Array55, 55, u128);
    let mut x = Array55::random();
    let mut y = Array55::random();
    let _z = x + y;
    let _z = x - y;
    let _z = x * y;
    for i in 0..x.len() {
        if x[i] == 0 {
            x[i] = 1
        }
    }
    for i in 0..y.len() {
        if y[i] == 0 {
            y[i] = 1
        }
    }
    let _z = x / y;
}
