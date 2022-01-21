use hacspec_lib::*;
use hacspec_attributes::*;


bytes!(Sha512Digest, 512 / 8);

public_nat_mod!(
    type_name: Ed25519FieldElement,
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
public_nat_mod!(
    type_name: ScalarModL,
    type_of_canvas: ScalarModLCanvas,
    bit_size_of_field: 512,
    modulo_value: "1000000000000000000000000000000014def9dea2f79cd65812631a5cf5d3ed"
);

type EdPoint = (Ed25519FieldElement, Ed25519FieldElement, Ed25519FieldElement, Ed25519FieldElement);

bytes!(CompressedEdPoint, 32);
bytes!(SerializedScalar, 32);
bytes!(Signature, 64);

const BASE: CompressedEdPoint = CompressedEdPoint(secret_array!(U8, 
    [0x58u8, 0x66u8, 0x66u8, 0x66u8, 0x66u8, 0x66u8, 0x66u8, 0x66u8,
    0x66u8, 0x66u8, 0x66u8, 0x66u8, 0x66u8, 0x66u8, 0x66u8, 0x66u8,
    0x66u8, 0x66u8, 0x66u8, 0x66u8, 0x66u8, 0x66u8, 0x66u8, 0x66u8,
    0x66u8, 0x66u8, 0x66u8, 0x66u8, 0x66u8, 0x66u8, 0x66u8, 0x66u8 ]));

fn is_negative(x : Ed25519FieldElement) -> U8 {
    if x.bit(255) {
        U8(1u8) 
    }
    else {
        U8(0u8)
    }
}

pub fn compress(p : EdPoint) -> CompressedEdPoint {
    let (x, y, z, _) = p;
    let z_inv = z.inv();
    let x = x * z_inv;
    let y = y * z_inv;
    let mut s : ByteSeq = y.to_byte_seq_le();
    s[31usize] = s[31usize] ^ (is_negative(x) << 7); // setting top bit
    CompressedEdPoint::from_slice(&s, 0, 32)
}

pub fn sqrt(a : Ed25519FieldElement) -> Option<Ed25519FieldElement> {
    //constants -- should be moved to constants
    let p3_8 = (Ed25519FieldElement::ZERO() - Ed25519FieldElement::from_literal(5u128)) / Ed25519FieldElement::from_literal(8u128) + Ed25519FieldElement::ONE();
    let p1_4 = (Ed25519FieldElement::ZERO() - Ed25519FieldElement::ONE()) / Ed25519FieldElement::from_literal(4u128);
    
    let x_c = a.pow_self(p3_8);
    //println!("{}", x_c);
    let mut result : Option<Ed25519FieldElement> = Option::<Ed25519FieldElement>::None;
    if x_c * x_c == a {
        result = Some(x_c);
    };
    if x_c * x_c == Ed25519FieldElement::ZERO() - a {
        let x = Ed25519FieldElement::TWO().pow_self(p1_4) * x_c;
        result = Some(x);
    }
    result
}

fn correct_sign(x :Ed25519FieldElement, y: Ed25519FieldElement, z: Ed25519FieldElement, x_s: U8) -> EdPoint {
    let x_r = is_negative(x);
    let mut x = x;
    if x_r.declassify() != x_s.declassify() { // Could probably do without declassifying
        x = Ed25519FieldElement::ZERO() - x;
    }
    (x, y, z, x * y)
}

pub fn decompress(p: CompressedEdPoint) -> Option<EdPoint> {
    //constant -- should be moved to constants
    let d = Ed25519FieldElement::ZERO() - (Ed25519FieldElement::from_literal(121665u128) * Ed25519FieldElement::from_literal(121666u128).inv() );

    let x_s = p[31usize] & U8(128u8) >> 7;
    let mut y_s = p;
    y_s[31usize] = y_s[31usize] & U8(127u8);
    let y = Ed25519FieldElement::from_byte_seq_le(y_s); 
    let z = Ed25519FieldElement::ONE();
    let yy = y * y;
    let u = yy - z;
    let v = d * yy + z;
    let xx = u * v.inv();
    let x_o = sqrt(xx);
    match x_o {
        Option::<Ed25519FieldElement>::None => Option::<EdPoint>::None,
        Option::<Ed25519FieldElement>::Some(x) => Some(correct_sign(x, y, z, x_s))
    }
    
}

pub fn point_add(p: EdPoint, q: EdPoint) -> EdPoint {
    //constant -- should be moved to constants
    let d_c = Ed25519FieldElement::ZERO() - (Ed25519FieldElement::from_literal(121665u128) * Ed25519FieldElement::from_literal(121666u128).inv() );
    let two = Ed25519FieldElement::TWO();

    let (x1, y1, z1, t1) = p;
    let (x2, y2, z2, t2) = q;
    let a = (y1 - x1) * (y2 - x2);
    let b = (y1 + x1) * (y2 + x2);
    let c = t1 * two * d_c * t2;
    let d = z1 * two * z2;
    let e = b - a;
    let f = d - c;
    let g = d + c;
    let h = b + a;
    let x3 = e * f;
    let y3 = g * h;
    let t3 = e * h;
    let z3 = f * g;
    (x3, y3, z3, t3)
}

pub fn point_mul(s: Scalar, p: EdPoint) -> EdPoint {
    let mut p = p;
    let mut q = (Ed25519FieldElement::ZERO(), Ed25519FieldElement::ONE(), Ed25519FieldElement::ONE(), Ed25519FieldElement::ZERO());
    for i in 0..256 {
        if s.bit(i) {
            q = point_add(q, p);
        }
        p = point_add(p, p);
    }
    q
}

pub fn point_eq(p: EdPoint, q: EdPoint) -> bool {
    let (x1, y1, z1, _) = p;
    let (x2, y2, z2, _) = q;
    x1 * z2 == x2 * z1 && y1 * z2 == y2 * z1
}

fn secret_expand(sk: SerializedScalar) -> (SerializedScalar, SerializedScalar) {
    let h = sha512(&ByteSeq::from_slice(&sk, 0, 32));
    let h_d = SerializedScalar::from_slice(&h, 32, 32);
    let mut s = SerializedScalar::from_slice(&h, 0, 32);
    s[0usize] = s[0usize] & U8(248u8);
    s[31usize] = s[31usize] & U8(127u8);
    s[31usize] = s[31usize] | U8(64u8);
    (s, h_d)
}

pub fn secret_to_public(sk: SerializedScalar) -> CompressedEdPoint {
    let (s, _) = secret_expand(sk);
    let base = decompress(BASE).unwrap();
    let ss = Scalar::from_byte_seq_le(s);
    let a = point_mul(ss, base);
    compress(a)
}

pub fn sc_modl_to_sc(s: ScalarModL) -> Scalar {
    Scalar::from_byte_seq_le(s.to_byte_seq_le().slice(0, 32))
}

pub fn sc_to_sc_modl(s: Scalar) -> ScalarModL {
    ScalarModL::from_byte_seq_le(s.to_byte_seq_le().concat(&ByteSeq::new(32)))
}

pub fn sign(sk: SerializedScalar, msg: &ByteSeq) -> Signature {
    let (a, prefix) = secret_expand(sk);
    let a = Scalar::from_byte_seq_le(a);
    let b = decompress(BASE).unwrap();
    let a_p = compress(point_mul(a, b));
    let r_h = sha512(&prefix.concat(msg));
    let r = ScalarModL::from_byte_seq_le(r_h);
    let r_p = point_mul(sc_modl_to_sc(r), b);
    let r_s = compress(r_p);
    let h_h = sha512(&r_s.concat(&a_p).concat(msg));
    let h = ScalarModL::from_byte_seq_le(h_h);
    let s = r + h * sc_to_sc_modl(a);
    let s_bytes = s.to_byte_seq_le().slice(0, 32);
    Signature::new().update(0, &r_s).update(32, &s_bytes)
}

#[hacspec_unsafe]
pub fn sha512(msg: &ByteSeq) -> Sha512Digest {
    use ed25519_dalek::{Sha512, Digest};

    let mut h: Sha512 = Sha512::new();
    h.update(msg.to_native());
    let r = h.finalize();
    Sha512Digest::from_public_slice(r.as_slice())
}
