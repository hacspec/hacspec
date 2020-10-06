// Import hacspec and all needed definitions.
use hacspec_lib::*;

use crate::ec::arithmetic::{self, Affine};

public_nat_mod!(
    type_name: FieldElement,
    type_of_canvas: FieldCanvas,
    bit_size_of_field: 384,
    modulo_value: "FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFFFF0000000000000000FFFFFFFF"
);

unsigned_public_integer!(Scalar, 384);

pub fn point_mul_base(k: Scalar) -> Affine<FieldElement> {
    let base_point = Affine(
        FieldElement::from_hex("AA87CA22BE8B05378EB1C71EF320AD746E1D3B628BA79B9859F741E082542A385502F25DBF55296C3A545E3872760AB7"),
        FieldElement::from_hex("3617DE4A96262C6F5D9E98BF9292DC29F8F41DBD289A147CE9DA3113B5F0B8C00A60B1CE1D7E819D7A431D7C90EA0E5F")
    );
    arithmetic::point_mul(k, base_point)
}

pub fn point_mul(k: Scalar, p: Affine<FieldElement>) -> Affine<FieldElement> {
    arithmetic::point_mul(k, p)
}
