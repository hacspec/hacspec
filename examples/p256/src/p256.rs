use hacspec_lib::*;

pub type Affine = (FieldElement, FieldElement);
type Jacobian = (FieldElement, FieldElement, FieldElement);

public_nat_mod!(
    type_name: FieldElement,
    type_of_canvas: FieldCanvas,
    bit_size_of_field: 256,
    modulo_value: "ffffffff00000001000000000000000000000000ffffffffffffffffffffffff"
);

public_nat_mod!(
    type_name: Scalar,
    type_of_canvas: ScalarCanvas,
    bit_size_of_field: 256,
    modulo_value: "ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551"
);

bytes!(Element, 32);

pub fn point_mul_base(k: Scalar) -> (bool, Affine) {
    let base_point = (
        FieldElement::from_byte_seq_be(Element(secret_bytes!([
            0x6Bu8, 0x17u8, 0xD1u8, 0xF2u8, 0xE1u8, 0x2Cu8, 0x42u8, 0x47u8, 0xF8u8, 0xBCu8, 0xE6u8,
            0xE5u8, 0x63u8, 0xA4u8, 0x40u8, 0xF2u8, 0x77u8, 0x03u8, 0x7Du8, 0x81u8, 0x2Du8, 0xEBu8,
            0x33u8, 0xA0u8, 0xF4u8, 0xA1u8, 0x39u8, 0x45u8, 0xD8u8, 0x98u8, 0xC2u8, 0x96u8
        ]))),
        FieldElement::from_byte_seq_be(Element(secret_bytes!([
            0x4Fu8, 0xE3u8, 0x42u8, 0xE2u8, 0xFEu8, 0x1Au8, 0x7Fu8, 0x9Bu8, 0x8Eu8, 0xE7u8, 0xEBu8,
            0x4Au8, 0x7Cu8, 0x0Fu8, 0x9Eu8, 0x16u8, 0x2Bu8, 0xCEu8, 0x33u8, 0x57u8, 0x6Bu8, 0x31u8,
            0x5Eu8, 0xCEu8, 0xCBu8, 0xB6u8, 0x40u8, 0x68u8, 0x37u8, 0xBFu8, 0x51u8, 0xF5u8
        ]))),
    );
    point_mul(k, base_point)
}

pub fn point_mul(k: Scalar, p: Affine) -> (bool, Affine) {
    let (success, jac) = ltr_mul(k, affine_to_jacobian(p));
    (success, jacobian_to_affine(jac))
}

fn jacobian_to_affine(p: Jacobian) -> Affine {
    let (x, y, z) = p;
    let z2 = z.exp(2u32);
    let z2i = z2.inv();
    let z3 = z * z2;
    let z3i = z3.inv();
    let x = x * z2i;
    let y = y * z3i;
    (x, y)
}

fn affine_to_jacobian(p: Affine) -> Jacobian {
    let (x, y) = p;
    (x, y, FieldElement::from_literal(1u128))
}

fn point_double(p: Jacobian) -> Jacobian {
    let (x1, y1, z1) = p;
    let delta = z1.exp(2u32);
    let gamma = y1.exp(2u32);

    let beta = x1 * gamma;

    let alpha_1 = x1 - delta;
    let alpha_2 = x1 + delta;
    let alpha = FieldElement::from_literal(3u128) * (alpha_1 * alpha_2);

    let x3 = alpha.exp(2u32) - (FieldElement::from_literal(8u128) * beta);

    let z3_ = (y1 + z1).exp(2u32);
    let z3 = z3_ - (gamma + delta);

    let y3_1 = (FieldElement::from_literal(4u128) * beta) - x3;
    let y3_2 = FieldElement::from_literal(8u128) * (gamma * gamma);
    let y3 = (alpha * y3_1) - y3_2;
    (x3, y3, z3)
}

fn is_point_at_infinity(p: Jacobian) -> bool {
    let (_x, _y, z) = p;
    z.equal(FieldElement::from_literal(0u128))
}

pub fn point_add(p: Affine, q: Affine) -> (bool, Affine) {
    // TODO: this is pretty ugly but everything else doesn't work in hacspec yet.
    let (mut success, mut result) = (false, p);
    if p != q {
        let (s, r) = point_add_jacob(affine_to_jacobian(p), affine_to_jacobian(q));
        result = jacobian_to_affine(r);
        success = s;
    } else {
        result = jacobian_to_affine(point_double(affine_to_jacobian(p)));
        success = true;
    };
    (success, result)
}

fn point_add_jacob(p: Jacobian, q: Jacobian) -> (bool, Jacobian) {
    let mut result = (true, q);
    if is_point_at_infinity(p) {
        // result = (true, q);
        // TODO: #85 needs to get fixed for this.
        // } else if is_point_at_infinity(q) {
        //     (true, p)
    } else {
        if is_point_at_infinity(q) {
            result = (true, p);
        } else {
            let (x1, y1, z1) = p;
            let (x2, y2, z2) = q;
            let z1z1 = z1.exp(2u32);
            let z2z2 = z2.exp(2u32);
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
                        FieldElement::from_literal(0u128),
                        FieldElement::from_literal(1u128),
                        FieldElement::from_literal(0u128),
                    ),
                )
            } else {
                let h = u2 - u1;
                let i = (FieldElement::from_literal(2u128) * h).exp(2u32);
                let j = h * i;
                let r = FieldElement::from_literal(2u128) * (s2 - s1);
                let v = u1 * i;

                let x3_1 = FieldElement::from_literal(2u128) * v;
                let x3_2 = r.exp(2u32) - j;
                let x3 = x3_2 - x3_1;

                let y3_1 = (FieldElement::from_literal(2u128) * s1) * j;
                let y3_2 = r * (v - x3);
                let y3 = y3_2 - y3_1;

                let z3_ = (z1 + z2).exp(2u32);
                let z3 = (z3_ - (z1z1 + z2z2)) * h;
                result = (true, (x3, y3, z3));
            }
        }
    };
    result
}

fn ltr_mul(k: Scalar, p: Jacobian) -> (bool, Jacobian) {
    let mut q = (
        FieldElement::from_literal(0u128),
        FieldElement::from_literal(1u128),
        FieldElement::from_literal(0u128),
    );
    let mut success = true;
    for i in 0..256 {
        q = point_double(q);
        if k.get_bit(256 - 1 - i).equal(Scalar::ONE()) {
            let (s, r) = point_add_jacob(q, p);
            q = r;
            success = success && s;
        }
    }
    (success, q)
}
