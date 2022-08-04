/*
* Unit tests for the Hacspec linear algebra library.
*/

use hacspec_lib::prelude::*;
use hacspec_linalg::*;

// === Helper functions ===

// Assert that two hacspec matrices are equal
fn assert_hacs(x: Matrix, y: Matrix) -> bool {
    if x.0 != y.0 {
        false
    } else {
        let zipped = x.1.iter().zip(y.1.iter());

        for z in zipped {
            if z.0 != z.1 {
                panic!(
                    "{:?} == {:?}, ({},{}) == ({},{})",
                    x.1.native_slice(),
                    y.1.native_slice(),
                    x.0.0,
                    x.0.1,
                    y.0.0,
                    y.0.1
                )
            }
        }

        true
    }
}

// === Tests ===

#[test]
fn test_unit_repeat() {
    let rs = vec![7, 7, 7, 7, 7, 7, 7, 7, 7, 7];

    let hac_op = repeat(5, 2, 7).unwrap();
    let hac_rs = new(5, 2, Seq::<Scalar>::from_vec(rs.clone())).unwrap();

    assert!(assert_hacs(hac_op, hac_rs));
}

#[test]
fn test_unit_zeros() {
    let rs = vec![0, 0, 0, 0, 0, 0, 0, 0, 0, 0];

    let hac_op = zeros(2, 5).unwrap();
    let hac_rs = new(2, 5, Seq::<Scalar>::from_vec(rs.clone())).unwrap();

    assert!(assert_hacs(hac_op, hac_rs));
}

#[test]
fn test_unit_ones() {
    let rs = vec![1, 1, 1, 1, 1, 1, 1, 1, 1, 1];

    let hac_op = ones(2, 5).unwrap();
    let hac_rs = new(2, 5, Seq::<Scalar>::from_vec(rs.clone())).unwrap();

    assert!(assert_hacs(hac_op, hac_rs));
}

#[test]
fn test_unit_identity() {
    let rs = vec![1, 0, 0, 0, 1, 0, 0, 0, 1];

    let hac_op = identity(3, 3).unwrap();
    let hac_rs = new(3, 3, Seq::<Scalar>::from_vec(rs.clone())).unwrap();

    assert!(assert_hacs(hac_op, hac_rs));
}

#[test]
fn test_unit_index() {
    let xs = vec![0, 1, 2, 3, 4, 5];
    let hac_xs = new(2, 3, Seq::<Scalar>::from_vec(xs.clone())).unwrap();

    assert!(index(hac_xs.clone(), 0, 0).unwrap() == 0.into());
    assert!(index(hac_xs.clone(), 0, 1).unwrap() == 1.into());
    assert!(index(hac_xs.clone(), 0, 2).unwrap() == 2.into());
    assert!(index(hac_xs.clone(), 1, 0).unwrap() == 3.into());
    assert!(index(hac_xs.clone(), 1, 1).unwrap() == 4.into());
    assert!(index(hac_xs.clone(), 1, 2).unwrap() == 5.into());
}

#[test]
fn test_unit_transpose() {
    let xs = vec![0, 1, 2, 3, 4, 5];
    let rs = vec![0, 3, 1, 4, 2, 5];

    let hac_xs = new(2, 3, Seq::<Scalar>::from_vec(xs.clone())).unwrap();
    let hac_rs = new(3, 2, Seq::<Scalar>::from_vec(rs.clone())).unwrap();

    let hac_op = transpose(hac_xs.clone());
    assert_hacs(hac_op, hac_rs);
}

#[test]
fn test_unit_slice() {
    let xs = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11];
    let rs = vec![5, 6, 7, 9, 10, 11];

    let hac_xs = new(3, 4, Seq::<Scalar>::from_vec(xs.clone())).unwrap();
    let hac_rs = new(2, 3, Seq::<Scalar>::from_vec(rs.clone())).unwrap();

    let hac_op = slice(hac_xs.clone(), (1, 1), (2, 3)).unwrap();

    assert!(assert_hacs(hac_op, hac_rs));
}

#[test]
fn test_unit_scale() {
    let x = 2;
    let xs = vec![0, 1, 2, 3, 4, 5];
    let rs = vec![0, 2, 4, 6, 8, 10];

    let hac_xs = new(2, 3, Seq::<Scalar>::from_vec(xs.clone())).unwrap();
    let hac_rs = new(2, 3, Seq::<Scalar>::from_vec(rs.clone())).unwrap();

    let hac_op = scale(hac_xs.clone(), x);
    assert_hacs(hac_op, hac_rs);
}

// === Negative Tests ===

#[test]
fn test_unit_neg_empty() {
    let xs = vec![];

    let hac_res = new(0, 0, Seq::<Scalar>::from_vec(xs.clone()));

    assert!(hac_res.is_err());
}
