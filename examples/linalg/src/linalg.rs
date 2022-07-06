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

type DimType = usize;
type Dims = (DimType, DimType);
type MatRes<T> = Result<Matrix<T>, u8>;
type ScalRes<T> = Result<T, u8>;

pub type Matrix<T> = (Dims, Seq<T>);

// === Errors === //

const DIMENSION_SEQUENCE_LENGTH_MISMATCH: u8 = 10u8;
const INDEX_OUT_OF_BOUNDS: u8 = 11u8;
const SLICE_OUT_OF_BOUNDS: u8 = 12u8;
const DIMENSION_MISMATCH: u8 = 13u8;

// === External Functions === //

/// Generate new matrix using rows, cols and a seq. Returns an error
/// if the product of the given dimensions is larger than the length
/// of the given Seq.
pub fn new<T>(rows: DimType, cols: DimType, seq: Seq<T>) -> MatRes<T>
where
    T: hacspec_lib::Integer,
{
    if seq.len() > 0 && rows * cols == seq.len() {
        MatRes::Ok(((rows, cols), seq))
    } else {
        MatRes::Err(DIMENSION_SEQUENCE_LENGTH_MISMATCH)
    }
}

/// Generate a n*m matrix filled with a given scalar.
pub fn repeat<T>(n: DimType, m: DimType, scalar: T) -> Matrix<T>
where
    T: hacspec_lib::Integer,
{
    let mut ret = Seq::<T>::new(n * m);

    for i in 0..n * m {
        ret[i] = scalar.clone();
    }

    ((n, m), ret)
}

/// Generate a n*m matrix filled with zeros.
pub fn zeros<T>(n: DimType, m: DimType) -> Matrix<T>
where
    T: hacspec_lib::Integer,
{
    repeat(n, m, T::ZERO())
}

/// Generate a n*m matrix filled with ones.
pub fn ones<T>(n: DimType, m: DimType) -> Matrix<T>
where
    T: hacspec_lib::Integer,
{
    repeat(n, m, T::ONE())
}

/// Generates an identity matrix. If the matrix is not square,
/// the largest square submatrix (starting at the first row and column)
/// is set to the identity while all other entries are set to zero.
pub fn identity<T>(n: DimType, m: DimType) -> Matrix<T>
where
    T: hacspec_lib::Integer,
{
    let mut ret = Seq::<T>::new(n * m);

    for i in 0..min(n, m) {
        let index = i * min(n, m) + i;
        ret[index] = T::ONE();
    }

    ((n, m), ret)
}

/// Gets the index of a matrix. Returns an Error if the given index is out of bounds.
pub fn index<T>(m: Matrix<T>, i: DimType, j: DimType) -> ScalRes<T>
where
    T: hacspec_lib::Integer,
{
    let (dim, seq) = m;
    let (rows, cols) = dim;
    let index = i * cols + j;

    if index >= rows * cols {
        ScalRes::Err(INDEX_OUT_OF_BOUNDS)
    } else {
        ScalRes::Ok(seq[index].clone())
    }
}

/// Transposes a matrix.
pub fn transpose<T>(matrix: Matrix<T>) -> Matrix<T>
where
    T: hacspec_lib::Integer,
{
    let (dim, seq) = matrix;
    let (rows, cols) = dim;
    let mut ret = Seq::<T>::new(seq.len());

    for i in 0..rows {
        for j in 0..cols {
            let seq_index = i * cols + j;
            let ret_index = j * rows + i;
            ret[ret_index] = seq[seq_index].clone()
        }
    }

    ((cols, rows), ret)
}

/// Returns a matrix slice, given a Matrix and two Dims (pairs of usize),
/// first Dims pair representing the starting point and second Dims
/// pair the dimensions. Returns an Error if the given slice is out of bounds.
pub fn slice<T>(matrix: Matrix<T>, start: Dims, len: Dims) -> MatRes<T>
where
    T: hacspec_lib::Integer,
{
    let (dim, seq) = matrix;
    let (rows, cols) = dim;
    let (start_row, start_col) = start;
    let (len_rows, len_cols) = len;
    let start_index = start_row * cols + start_col;
    let mut ret = Seq::<T>::new(len_rows * len_cols);
    let mut res = MatRes::Err(SLICE_OUT_OF_BOUNDS);

    if start_index + len_rows * len_cols <= rows * cols {
        for i in 0..len_rows {
            for j in 0..len_cols {
                let ret_index = i * len_cols + j;
                let seq_index = (start_row + i) * cols + (start_col + j);
                ret[ret_index] = seq[seq_index].clone()
            }
        }

        res = new(len_rows, len_cols, ret);
    }

    res
}

/// Scale a matrix with a given scalar.
pub fn scale<T>(matrix: Matrix<T>, scalar: T) -> Matrix<T>
where
    T: hacspec_lib::Integer,
{
    let (dim, seq) = matrix;
    let mut ret = Seq::<T>::new(seq.len());

    for i in 0..seq.len() {
        ret[i] = scalar.clone() * seq[i].clone()
    }

    (dim, ret)
}

/// Matrix addition. Returns an Error on dimension mismatch.
pub fn add<T>(matrix_1: Matrix<T>, matrix_2: Matrix<T>) -> MatRes<T>
where
    T: hacspec_lib::Integer,
{
    let (m1_dim, m1_s) = matrix_1;
    let (m2_dim, m2_s) = matrix_2;
    let mut ret = Seq::<T>::new(m1_s.len());
    let mut res = MatRes::Err(DIMENSION_MISMATCH);

    if m1_dim == m2_dim {
        for i in 0..m1_s.len() {
            ret[i] = m1_s[i].clone() + m2_s[i].clone()
        }
        res = MatRes::Ok((m1_dim, ret))
    }
    res
}

/// Matrix subtraction. Returns an Error on dimension mismatch.
pub fn sub<T>(matrix_1: Matrix<T>, matrix_2: Matrix<T>) -> MatRes<T>
where
    T: hacspec_lib::Integer,
{
    let (m1_dim, m1_s) = matrix_1;
    let (m2_dim, m2_s) = matrix_2;
    let mut ret = Seq::<T>::new(m1_s.len());
    let mut res = MatRes::Err(DIMENSION_MISMATCH);

    if m1_dim == m2_dim {
        for i in 0..m1_s.len() {
            ret[i] = m1_s[i].clone() - m2_s[i].clone()
        }
        res = MatRes::Ok((m1_dim, ret))
    }
    res
}

/// Component-wise multiplication (Hadamard product). Returns an Error on dimension mismatch.
pub fn component_mul<T>(matrix_1: Matrix<T>, matrix_2: Matrix<T>) -> MatRes<T>
where
    T: hacspec_lib::Integer,
{
    let (m1_dim, m1_s) = matrix_1;
    let (m2_dim, m2_s) = matrix_2;
    let mut ret = Seq::<T>::new(m1_s.len());
    let mut res = MatRes::Err(DIMENSION_MISMATCH);

    if m1_dim == m2_dim {
        for i in 0..m1_s.len() {
            ret[i] = m1_s[i].clone() * m2_s[i].clone()
        }
        res = MatRes::Ok((m1_dim, ret))
    }
    res
}

/// Matrix multiplication. Returns an Error on dimension mismatch.
pub fn mul<T>(matrix_1: Matrix<T>, matrix_2: Matrix<T>) -> MatRes<T>
where
    T: hacspec_lib::Integer,
{
    let (dim_1, seq_1) = matrix_1;
    let (dim_2, seq_2) = matrix_2;
    let (l, m) = dim_1;
    let (m_, n) = dim_2;
    let mut ret = Seq::<T>::new(l * n);
    let mut res = MatRes::Err(DIMENSION_MISMATCH);

    if m == m_ {
        for i in 0..l {
            for j in 0..n {
                let mut acc = T::ZERO();
                let index = i * n + j;

                for k in 0..m {
                    let index_1 = i * m + k;
                    let index_2 = k * n + j;

                    acc = acc + seq_1[index_1].clone() * seq_2[index_2].clone();
                }

                ret[index] = acc
            }
        }

        res = new(l, n, ret)
    }

    res
}
