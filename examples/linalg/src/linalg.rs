/*
* A hacspec library implementation modelled on the nalgebra rust library.
* Functions are modelled and tested against their nalgebra counterparts
* using Quickcheck.

* This ensures, with reasonable probability, that the
* these functions and the nalgebra functions works identically. With this
* assumption, properties about the nalgebra library can be proven in
* hacspec target languages, and allows hacspec implementations to use
* common linear algebra operations.
*
* Each matrix consists of a pair of dimensions and a Seq fx:
* ((2,3), [0,1,2,3,4,5,6])
* represents a 2x3 matrix
*
* Only matrices are supported, vectors can be modelled as dimension (x,1)
* matrices. Note that, unlike the nalgebra library, matrices are
* represented row-by-row instead of column-by-column.
*/

use hacspec_lib::*;

pub type DimType = usize;
pub type Scalar = i128;
pub type Dims = (DimType, DimType);
pub type Matrix = (Dims, Seq<Scalar>);
pub type MatRes = Result<Matrix, ()>;

// Generate new matrix using rows, cols and a seq.
pub fn new(rows: DimType, cols: DimType, seq: Seq<Scalar>) -> MatRes {
    if seq.len() > 0 && rows * cols == seq.len() {
        MatRes::Ok(((rows, cols), seq))
    } else {
        MatRes::Err(())
    }
}

// Generate a n*m matrix filled with a given scalar
pub fn repeat(n: DimType, m: DimType, scalar: Scalar) -> MatRes {
    let mut ret = Seq::<Scalar>::new(n * m);

    for i in 0..n * m {
        ret[i] = scalar;
    }

    new(n, m, ret)
}

// Generate a n*m matrix filled with zeros.
pub fn zeros(n: DimType, m: DimType) -> MatRes {
    repeat(n, m, Scalar::ZERO())
}

// Generate a n*m matrix filled with ones.
pub fn ones(n: DimType, m: DimType) -> MatRes {
    repeat(n, m, Scalar::ONE())
}

// Generates an identity matrix. If the matrix is not square,
// the largest square submatrix (starting at the first row and column)
// is set to the identity while all other entries are set to zero.
pub fn identity(n: DimType, m: DimType) -> MatRes {
    let mut ret = Seq::<Scalar>::new(n * m);

    for i in 0..min(n, m) {
        let index = i * min(n, m) + i;
        ret[index] = Scalar::ONE();
    }

    new(n, m, ret)
}
