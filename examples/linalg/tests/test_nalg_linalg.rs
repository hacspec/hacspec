/*
* QuickCheck testing for the linear algebra library against
* the Nalgebra rust library.
*/

extern crate nalgebra;
extern crate quickcheck;

use hacspec_lib::prelude::*;
use hacspec_linalg::*;

use nalgebra::DMatrix;
use quickcheck::*;

// === Helper functions ===

fn assert_matrices(x: Matrix, y: DMatrix<Scalar>) -> bool {
    if x.0 == (y.nrows(), y.ncols()) {
        let y = y.transpose();
        let zipped = x.1.iter().zip(y.iter());

        for z in zipped {
            if z.0 != z.1 {
                break;
            }
        }

        return true;
    }
    panic!(
        "({:?}) == ({:?}), ({},{}) == ({},{})",
        x.1.native_slice(),
        y.as_slice(),
        x.0.0,
        x.0.1,
        y.nrows(),
        y.ncols()
    );
}

fn quickcheck(helper: impl Testable) {
    QuickCheck::new()
        .tests(100)
        .min_tests_passed(100)
        .max_tests(1000000)
        .quickcheck(helper);
}

// === Test Functions ===

#[test]
fn test_nalg_repeat() {
    fn helper(n: u8, m: u8, s: i128) -> TestResult {
        let n = n as usize;
        let m = m as usize;

        if n * m == 0 {
            return TestResult::discard();
        }

        let hac = repeat(n, m, s).unwrap();
        let ext = DMatrix::repeat(n, m, s);

        TestResult::from_bool(assert_matrices(hac, ext))
    }
    quickcheck(helper as fn(u8, u8, i128) -> TestResult);
}

#[test]
fn test_nalg_zeros() {
    fn helper(n: u8, m: u8) -> TestResult {
        let n = n as usize;
        let m = m as usize;

        if n * m == 0 {
            return TestResult::discard();
        }

        let hac = zeros(n, m).unwrap();
        let ext = DMatrix::zeros(n, m);

        TestResult::from_bool(assert_matrices(hac, ext))
    }
    quickcheck(helper as fn(u8, u8) -> TestResult);
}

#[test]
fn test_nalg_ones() {
    fn helper(n: u8, m: u8) -> TestResult {
        let n = n as usize;
        let m = m as usize;

        if n * m == 0 {
            return TestResult::discard();
        }

        let hac = ones(n, m).unwrap();
        let mut ext = DMatrix::zeros(n, m);
        ext.fill(Scalar::ONE());

        TestResult::from_bool(assert_matrices(hac, ext.clone()))
    }
    quickcheck(helper as fn(u8, u8) -> TestResult);
}

#[test]
fn test_nalg_identity() {
    fn helper(n: u8, m: u8) -> TestResult {
        let n = n as usize;
        let m = m as usize;

        if n == 0 || m == 0 {
            return TestResult::discard();
        }

        let hac = identity(n, m).unwrap();
        let ext = DMatrix::identity(n, m);

        TestResult::from_bool(assert_matrices(hac, ext))
    }
    quickcheck(helper as fn(u8, u8) -> TestResult);
}
