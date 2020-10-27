use hacspec_lib::*;

public_nat_mod!(
    type_name: FieldElement,
    type_of_canvas: FieldCanvas,
    bit_size_of_field: 256,
    modulo_value: "7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed"
);
public_nat_mod!(
    type_name: Scalar,
    type_of_canvas: ScalarCanvas,
    bit_size_of_field: 256,
    modulo_value: "8000000000000000000000000000000000000000000000000000000000000000"
);

bytes!(SerializedPoint, 32);
bytes!(SerializedScalar, 32);

fn mask_scalar(s: SerializedScalar) -> SerializedScalar {
    let mut k = s;
    k[0] = k[0] & U8(248);
    k[31] = k[31] & U8(127);
    k[31] = k[31] | U8(64);
    k
}

fn decode_scalar(s: SerializedScalar) -> Scalar {
    let k = mask_scalar(s);
    Scalar::from_byte_seq_le(k)
}

fn decode_point(u: SerializedPoint) -> (FieldElement, FieldElement) {
    let mut u_ = u;
    u_[31] = u_[31] & U8(127);
    (
        FieldElement::from_byte_seq_le(u_),
        FieldElement::from_literal(1),
    )
}

fn encode_point(p: (FieldElement, FieldElement)) -> SerializedPoint {
    let (x, y) = p;
    let b = x * y.inv();
    SerializedPoint::new().update_start(&b.to_byte_seq_le())
}

fn point_add_and_double(
    q: (FieldElement, FieldElement),
    (nq, nqp1): ((FieldElement, FieldElement), (FieldElement, FieldElement)),
) -> ((FieldElement, FieldElement), (FieldElement, FieldElement)) {
    let (x_1, _z_1) = q;
    let (x_2, z_2) = nq;
    let (x_3, z_3) = nqp1;
    let a = x_2 + z_2;
    let aa = a.pow(2);
    let b = x_2 - z_2;
    let bb = b * b;
    let e = aa - bb;
    let c = x_3 + z_3;
    let d = x_3 - z_3;
    let da = d * a;
    let cb = c * b;

    let x_3 = (da + cb).pow(2);
    let z_3 = x_1 * ((da - cb).pow(2));
    let x_2 = aa * bb;
    let e121665 = FieldElement::from_literal(121_665);
    let z_2 = e * (aa + (e121665 * e));
    ((x_2, z_2), (x_3, z_3))
}

fn swap(
    x: ((FieldElement, FieldElement), (FieldElement, FieldElement)),
) -> ((FieldElement, FieldElement), (FieldElement, FieldElement)) {
    (x.1, x.0)
}

fn montgomery_ladder(
    k: Scalar,
    init: (FieldElement, FieldElement),
) -> (FieldElement, FieldElement) {
    let inf = (FieldElement::from_literal(1), FieldElement::from_literal(0));
    let mut acc: ((FieldElement, FieldElement), (FieldElement, FieldElement)) = (inf, init);
    for i in 0..256 {
        if k.bit(255 - i) {
            acc = swap(acc);
            acc = point_add_and_double(init, acc);
            acc = swap(acc);
        } else {
            acc = point_add_and_double(init, acc);
        }
    }
    acc.0
}

pub fn scalarmult(s: SerializedScalar, p: SerializedPoint) -> SerializedPoint {
    let s_ = decode_scalar(s);
    let p_ = decode_point(p);
    let r = montgomery_ladder(s_, p_);
    encode_point(r)
}

pub fn secret_to_public(s: SerializedScalar) -> SerializedPoint {
    let base = SerializedPoint::from_hex("09");
    scalarmult(s, base)
}