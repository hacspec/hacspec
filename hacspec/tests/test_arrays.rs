use hacspec::prelude::*;

#[test]
fn test_public_array_u32() {
    array!(TestSeq, 64, u32);

    both_arrays!(PublicState, State, 73, U32, u32);
    let x = PublicState::new();
    let y: State = x.into();
    let _z: PublicState = y.into();
}
