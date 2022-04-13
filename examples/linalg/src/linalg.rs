use hacspec_lib::*;

pub type DimType = usize;
pub type Scalar = i128;
pub type Dims = (DimType, DimType);
pub type Matrix = (Dims, Seq<Scalar>);

// Generate new matrix using rows, cols and a seq.
pub fn new(rows: DimType, cols: DimType, seq: Seq<Scalar>) -> Result<Matrix, ()> {
    if seq.len() > 0 && rows * cols == seq.len() {
        Result::<Matrix, ()>::Ok(((rows, cols), seq))
    } else {
        Result::<Matrix, ()>::Err(())
    }
}

// Generate a n*m matrix filled with zeros.
pub fn zeros(n: DimType, m: DimType) -> Result<Matrix, ()> {
    new(n, m, Seq::<Scalar>::new(n * m))
}

// Generate a n*m matrix filled with ones.
pub fn ones(n: DimType, m: DimType) -> Result<Matrix, ()> {
    let mut ret = Seq::<Scalar>::new(n * m);

    for i in 0..n * m {
        ret[i] = Scalar::ONE();
    }

    new(n, m, ret)
}

// Generate the n*n identity matrix.
pub fn identity(n: DimType) -> Result<Matrix, ()> {
    let mut ret = Seq::<Scalar>::new(n * n);

    for i in 0..n {
        let index = i * n + i;
        ret[index] = Scalar::ONE();
    }

    new(n, n, ret)
}
