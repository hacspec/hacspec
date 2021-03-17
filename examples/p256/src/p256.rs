use hacspec_lib::*;

type Affine = (FieldElement, FieldElement);
type Jacobian = (FieldElement, FieldElement, FieldElement);

public_nat_mod!(
    type_name: FieldElement,
    type_of_canvas: FieldCanvas,
    bit_size_of_field: 256,
    modulo_value: "ffffffff00000001000000000000000000000000ffffffffffffffffffffffff"
);

unsigned_public_integer!(Scalar, 256);

pub fn point_mul_base(k: Scalar) -> Affine {
    let base_point = (
        FieldElement::from_hex("6B17D1F2E12C4247F8BCE6E563A440F277037D812DEB33A0F4A13945D898C296"),
        FieldElement::from_hex("4FE342E2FE1A7F9B8EE7EB4A7C0F9E162BCE33576B315ECECBB6406837BF51F5"),
    );
    generic_point_mul(k, base_point)
}

pub fn point_mul(k: Scalar, p: Affine) -> Affine {
    generic_point_mul(k, p)
}

fn jacobian_to_affine(p: Jacobian) -> Affine {
    let (x, y, z) = p;
    let z2 = z.exp(2);
    let z2i = z2.inv();
    let z3 = z * z2;
    let z3i = z3.inv();
    let x = x * z2i;
    let y = y * z3i;
    (x, y)
}

fn affine_to_jacobian(p: Affine) -> Jacobian {
    let (x, y) = p;
    (x, y, FieldElement::from_literal(1))
}

fn point_double(p: Jacobian) -> Jacobian {
    let (x1, y1, z1) = p;
    let delta = z1.exp(2);
    let gamma = y1.exp(2);

    let beta = x1 * gamma;

    let alpha_1 = x1 - delta;
    let alpha_2 = x1 + delta;
    let alpha = FieldElement::from_literal(3) * (alpha_1 * alpha_2);

    let x3 = alpha.exp(2) - (FieldElement::from_literal(8) * beta);

    let z3_ = (y1 + z1).exp(2);
    let z3 = z3_ - (gamma + delta);

    let y3_1 = (FieldElement::from_literal(4) * beta) - x3;
    let y3_2 = FieldElement::from_literal(8) * (gamma * gamma);
    let y3 = (alpha * y3_1) - y3_2;
    (x3, y3, z3)
}

fn is_point_at_infinity(p: Jacobian) -> bool {
    let (_x, _y, z) = p;
    z.equal(FieldElement::from_literal(0))
}

fn point_add(p: Jacobian, q: Jacobian) -> (bool, Jacobian) {
    let mut result = (false, q);
    if is_point_at_infinity(p) {
        result = (true, q);
    // TODO: #85 needs to get fixed for this.
    // } else if is_point_at_infinity(q) {
    //     (true, p)
    } else {
        if is_point_at_infinity(q) {
            result = (true, p);
        } else {
            let (x1, y1, z1) = p;
            let (x2, y2, z2) = q;
            let z1z1 = z1.exp(2);
            let z2z2 = z2.exp(2);
            let u1 = x1 * z2z2;
            let u2 = x2 * z1z1;
            let s1 = (y1 * z2) * z2z2;
            let s2 = (y2 * z1) * z1z1;

            if u1.equal(u2) {
                // assert!(!s1.equal(s2));
                let success = if s1.equal(s2) { false } else { true };
                result = (
                    success,
                    (
                        FieldElement::from_literal(0),
                        FieldElement::from_literal(1),
                        FieldElement::from_literal(0),
                    ),
                )
            } else {
                let h = u2 - u1;
                let i = (FieldElement::from_literal(2) * h).exp(2);
                let j = h * i;
                let r = FieldElement::from_literal(2) * (s2 - s1);
                let v = u1 * i;

                let x3_1 = FieldElement::from_literal(2) * v;
                let x3_2 = r.exp(2) - j;
                let x3 = x3_2 - x3_1;

                let y3_1 = (FieldElement::from_literal(2) * s1) * j;
                let y3_2 = r * (v - x3);
                let y3 = y3_2 - y3_1;

                let z3_ = (z1 + z2).exp(2);
                let z3 = (z3_ - (z1z1 + z2z2)) * h;
                result = (true, (x3, y3, z3));
            }
        }
    };
    result
}

fn ltr_mul(k: Scalar, p: Jacobian) -> Jacobian {
    let mut q = (
        FieldElement::from_literal(0),
        FieldElement::from_literal(1),
        FieldElement::from_literal(0),
    );
    for i in 0..FieldElement::NUM_BITS {
        q = point_double(q);
        if k.get_bit(FieldElement::NUM_BITS - 1 - i)
            .equal(Scalar::ONE())
        {
            let (_success, result) = point_add(q, p); // TODO: check success
            q = result;
        }
    }
    q
}

pub fn generic_point_mul(k: Scalar, p: Affine) -> Affine {
    let jac = ltr_mul(k, affine_to_jacobian(p));
    jacobian_to_affine(jac)
}
