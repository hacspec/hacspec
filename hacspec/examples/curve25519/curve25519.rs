// Import hacspec and all needed definitions.
use hacspec::prelude::*;

public_nat_mod!(
    FieldElement,
    FieldCanvas,
    256,
    "7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed"
);
public_nat_mod!(
    Scalar,
    ScalarCanvas,
    256,
    "8000000000000000000000000000000000000000000000000000000000000000"
);

type Point = (FieldElement, FieldElement);
bytes!(SerializedPoint, 32);
bytes!(SerializedScalar, 32);

fn mask_scalar(s: SerializedScalar) -> SerializedScalar {
    let mut k = s;
    k[0] &= U8(248);
    k[31] &= U8(127);
    k[31] |= U8(64);
    k
}

// TODO: drop raw where possible
fn decode_scalar(s: SerializedScalar) -> Scalar {
    let k = mask_scalar(s);
    Scalar::from_byte_seq_le(k)
}

fn decode_point(u: SerializedPoint) -> Point {
    let mut u_ = u;
    u_[31] &= U8(127);
    (
        FieldElement::from_byte_seq_le(u_),
        FieldElement::from_literal(1),
    )
}

fn encode_point(p: Point) -> SerializedPoint {
    let (x, y) = p;
    let b = x * y.inv();
    SerializedPoint::copy_pad(b.to_byte_seq_le())
}

fn point_add_and_double(q: Point, (nq, nqp1): (Point, Point)) -> (Point, Point) {
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

fn swap(x: (Point, Point)) -> (Point, Point) {
    (x.1, x.0)
}

fn montgomery_ladder(k: Scalar, init: Point) -> Point {
    // TODO: let inf = (FieldElement::one(), FieldElement::zero());
    let inf = (FieldElement::from_literal(1), FieldElement::from_literal(0));
    let mut acc: (Point, Point) = (inf, init);
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
    let base = SerializedPoint::from("09");
    scalarmult(s, base)
}

// Test some internal functions.

#[test]
fn test_encode_decode_scalar() {
    let s = SerializedScalar(secret_bytes!([
        0xa5, 0x46, 0xe3, 0x6b, 0xf0, 0x52, 0x7c, 0x9d, 0x3b, 0x16, 0x15, 0x4b, 0x82, 0x46, 0x5e,
        0xdd, 0x62, 0x14, 0x4c, 0x0a, 0xc1, 0xfc, 0x5a, 0x18, 0x50, 0x6a, 0x22, 0x44, 0xba, 0x44,
        0x9a, 0xc4
    ]));
    let s_expected =
        Scalar::from_hex("449a44ba44226a50185afcc10a4c1462dd5e46824b15163b9d7c52f06be346a0");
    let s_ = decode_scalar(s);
    assert_eq!(s_expected, s_);

    let u = SerializedPoint(secret_bytes!([
        0xe6, 0xdb, 0x68, 0x67, 0x58, 0x30, 0x30, 0xdb, 0x35, 0x94, 0xc1, 0xa4, 0x24, 0xb1, 0x5f,
        0x7c, 0x72, 0x66, 0x24, 0xec, 0x26, 0xb3, 0x35, 0x3b, 0x10, 0xa9, 0x03, 0xa6, 0xd0, 0xab,
        0x1c, 0x4c
    ]));
    let u_expected = (
        FieldElement::from_hex("4c1cabd0a603a9103b35b326ec2466727c5fb124a4c19435db3030586768dbe6"),
        FieldElement::from_literal(1),
    );
    let u_ = decode_point(u);
    assert_eq!(u_expected, u_);

    let u_encoded = encode_point(u_);
    assert_eq!(u, u_encoded);
}
