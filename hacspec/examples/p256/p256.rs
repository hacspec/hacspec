// Import hacspec and all needed definitions.
use hacspec::prelude::*;

public_nat_mod!(FieldElement, FieldCanvas, 256, "ffffffff00000001000000000000000000000000ffffffffffffffffffffffff");

unsigned_integer_old_public!(Scalar, 256);

// TODO: these two aren't cool
type Jacobian = (FieldElement, FieldElement, FieldElement);
type Affine = (FieldElement, FieldElement);

fn jacobian_to_affine(p: Jacobian) -> Affine {
    let (x, y, z) = (p.0, p.1, p.2);
    let z2 = z.pow(2);
    let z2i = z2.inv();
    let z3 = z * z2;
    let z3i = z3.inv();
    let x = x * z2i;
    let y = y * z3i;
    (x, y)
}

fn point_double(p: Jacobian) -> Jacobian {
    let (x1, y1, z1) = (p.0, p.1, p.2);
    let delta = z1.pow(2);
    let gamma = y1.pow(2);

    let beta = x1 * gamma;

    let alpha_1 = x1 - delta;
    let alpha_2 = x1 + delta;
    let alpha = FieldElement::from_literal(3) * (alpha_1 * alpha_2);

    let x3 = alpha.pow(2) - (FieldElement::from_literal(8) * beta);

    let z3_ = (y1 + z1).pow(2);
    let z3 = z3_ - (gamma + delta);

    let y3_1 = (FieldElement::from_literal(4) * beta) - x3;
    let y3_2 = FieldElement::from_literal(8) * (gamma * gamma);
    let y3 = (alpha * y3_1) - y3_2;
    (x3, y3, z3)
}

fn is_point_at_infinity(p: Jacobian) -> bool {
    p.2 == FieldElement::from_literal(0)
}

fn point_add(p: Jacobian, q: Jacobian) -> Jacobian {
    if is_point_at_infinity(p) {
        return q;
    }
    if is_point_at_infinity(q) {
        return p;
    }
    let (x1, y1, z1) = (p.0, p.1, p.2);
    let (x2, y2, z2) = (q.0, q.1, q.2);
    let z1z1 = z1.pow(2);
    let z2z2 = z2.pow(2);
    let u1 = x1 * z2z2;
    let u2 = x2 * z1z1;
    let s1 = (y1 * z2) * z2z2;
    let s2 = (y2 * z1) * z1z1;

    if u1 == u2 {
        assert_ne!(s1, s2);
        return (
            FieldElement::from_literal(0),
            FieldElement::from_literal(1),
            FieldElement::from_literal(0),
        );
    }

    let h = u2 - u1;
    let i = (FieldElement::from_literal(2) * h).pow(2);
    let j = h * i;
    let r = FieldElement::from_literal(2) * (s2 - s1);
    let v = u1 * i;

    let x3_1 = FieldElement::from_literal(2) * v;
    let x3_2 = r.pow(2) - j;
    let x3 = x3_2 - x3_1;

    let y3_1 = (FieldElement::from_literal(2) * s1) * j;
    let y3_2 = r * (v - x3);
    let y3 = y3_2 - y3_1;

    let z3_ = (z1 + z2).pow(2);
    let z3 = (z3_ - (z1z1 + z2z2)) * h;
    (x3, y3, z3)
}

fn montgomery_ladder(k: Scalar, init: Jacobian) -> Jacobian {
    let mut p_working = (
        (
            FieldElement::from_literal(0),
            FieldElement::from_literal(1),
            FieldElement::from_literal(0),
        ),
        init,
    );
    for i in 0..256 {
        if k.bit(255 - i) {
            p_working = (p_working.1, p_working.0);
        }
        let xx = point_double(p_working.0);
        let xp1 = point_add(p_working.0, p_working.1);
        if k.bit(255 - i) {
            p_working = (xp1, xx);
        } else {
            p_working = (xx, xp1);
        }
    }
    p_working.0
}

pub fn point_mul(k: Scalar) -> Affine {
    let base_point = (
        FieldElement::from_hex("6B17D1F2E12C4247F8BCE6E563A440F277037D812DEB33A0F4A13945D898C296"),
        FieldElement::from_hex("4FE342E2FE1A7F9B8EE7EB4A7C0F9E162BCE33576B315ECECBB6406837BF51F5"),
        FieldElement::from_literal(1),
    );
    let jac = montgomery_ladder(k, base_point);
    jacobian_to_affine(jac)
}
