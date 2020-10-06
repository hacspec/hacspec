// Import hacspec and all needed definitions.
use hacspec_lib::*;

use crate::ec::arithmetic::{self, Affine};

public_nat_mod!(
    type_name: FieldElement,
    type_of_canvas: FieldCanvas,
    bit_size_of_field: 256,
    modulo_value: "ffffffff00000001000000000000000000000000ffffffffffffffffffffffff"
);

unsigned_public_integer!(Scalar, 256);

pub fn point_mul_base(k: Scalar) -> Affine<FieldElement> {
    let base_point = Affine(
        FieldElement::from_hex("6B17D1F2E12C4247F8BCE6E563A440F277037D812DEB33A0F4A13945D898C296"),
        FieldElement::from_hex("4FE342E2FE1A7F9B8EE7EB4A7C0F9E162BCE33576B315ECECBB6406837BF51F5"),
    );
    arithmetic::point_mul(k, base_point)
}

pub fn point_mul(k: Scalar, p: Affine<FieldElement>) -> Affine<FieldElement> {
    arithmetic::point_mul(k, p)
}
