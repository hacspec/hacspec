#![allow(non_snake_case)]
/*
* A hacspec Ristretto implementation modelled on the curve25519_dalek rust library.
* Functions are modelled and tested against their dalek counterparts
* using Quickcheck.
*
* This ensures, with reasonable probability, that the
* these functions and the dalek functions work identically. With this
* assumption, properties about the dalek library can be proven in
* hacspec target languages, and allows hacspec implementations to use
* the defined ristretto operations.
*
* Each internal representation of a point is kept in its Twisted Edwards
* representation, while each encoded point is a byte-string of length 32.
*
* Each public function in the library is based on the IETF-standard for Ristretto
* while all helper functions are private. It is also important to note that
* the internal representation of each point is kept hidden and inaccessible
* to the outside in order to avoid giving incorrect encodings.
*
* For more information see the aforementioned IETF-standard here:
* https://www.ietf.org/archive/id/draft-irtf-cfrg-ristretto255-00.html#name-negative-field-elements/
* And the ristretto documentation:
* https://ristretto.group/ristretto.html/
*/

use hacspec_lib::*;

// Ristretto points are represented here by Extended Twisted Edwards Coordinates:
// https://eprint.iacr.org/2008/522.pdf
pub type RistrettoPoint = (FieldElement, FieldElement, FieldElement, FieldElement);

type DecodeResult = Result<RistrettoPoint, u8>;

// Ristretto points in their encoded form.
bytes!(RistrettoPointEncoded, 32);

// Bytestrings are used as the input of the one-way-map function.
bytes!(ByteString, 64);

public_nat_mod!(
    type_name: FieldElement,
    type_of_canvas: FieldCanvas,
    bit_size_of_field: 256,
    modulo_value: "7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed"
);

// The Scalar type is used for scaling Ristretto Points.
public_nat_mod!(
    type_name: Scalar,
    type_of_canvas: ScalarCanvas,
    bit_size_of_field: 256,
    modulo_value: "1000000000000000000000000000000014def9dea2f79cd65812631a5cf5d3ed"
);

// === Constants === //

fn P() -> FieldElement {
    FieldElement::from_byte_seq_be(&byte_seq!(
        0x7fu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8,
        0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8,
        0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xedu8
    ))
}

fn D() -> FieldElement {
    FieldElement::from_byte_seq_be(&byte_seq!(
        0x52u8, 0x03u8, 0x6cu8, 0xeeu8, 0x2bu8, 0x6fu8, 0xfeu8, 0x73u8, 0x8cu8, 0xc7u8, 0x40u8,
        0x79u8, 0x77u8, 0x79u8, 0xe8u8, 0x98u8, 0x00u8, 0x70u8, 0x0au8, 0x4du8, 0x41u8, 0x41u8,
        0xd8u8, 0xabu8, 0x75u8, 0xebu8, 0x4du8, 0xcau8, 0x13u8, 0x59u8, 0x78u8, 0xa3u8
    ))
}

fn SQRT_M1() -> FieldElement {
    FieldElement::from_byte_seq_be(&byte_seq!(
        0x2bu8, 0x83u8, 0x24u8, 0x80u8, 0x4fu8, 0xc1u8, 0xdfu8, 0x0bu8, 0x2bu8, 0x4du8, 0x00u8,
        0x99u8, 0x3du8, 0xfbu8, 0xd7u8, 0xa7u8, 0x2fu8, 0x43u8, 0x18u8, 0x06u8, 0xadu8, 0x2fu8,
        0xe4u8, 0x78u8, 0xc4u8, 0xeeu8, 0x1bu8, 0x27u8, 0x4au8, 0x0eu8, 0xa0u8, 0xb0u8
    ))
}

fn INVSQRT_A_MINUS_D() -> FieldElement {
    FieldElement::from_byte_seq_be(&byte_seq!(
        0x78u8, 0x6cu8, 0x89u8, 0x05u8, 0xcfu8, 0xafu8, 0xfcu8, 0xa2u8, 0x16u8, 0xc2u8, 0x7bu8,
        0x91u8, 0xfeu8, 0x01u8, 0xd8u8, 0x40u8, 0x9du8, 0x2fu8, 0x16u8, 0x17u8, 0x5au8, 0x41u8,
        0x72u8, 0xbeu8, 0x99u8, 0xc8u8, 0xfdu8, 0xaau8, 0x80u8, 0x5du8, 0x40u8, 0xeau8
    ))
}

fn SQRT_AD_MINUS_ONE() -> FieldElement {
    FieldElement::from_byte_seq_be(&byte_seq!(
        0x37u8, 0x69u8, 0x31u8, 0xbfu8, 0x2bu8, 0x83u8, 0x48u8, 0xacu8, 0x0fu8, 0x3cu8, 0xfcu8,
        0xc9u8, 0x31u8, 0xf5u8, 0xd1u8, 0xfdu8, 0xafu8, 0x9du8, 0x8eu8, 0x0cu8, 0x1bu8, 0x78u8,
        0x54u8, 0xbdu8, 0x7eu8, 0x97u8, 0xf6u8, 0xa0u8, 0x49u8, 0x7bu8, 0x2eu8, 0x1bu8
    ))
}

fn ONE_MINUS_D_SQ() -> FieldElement {
    FieldElement::from_byte_seq_be(&byte_seq!(
        0x02u8, 0x90u8, 0x72u8, 0xa8u8, 0xb2u8, 0xb3u8, 0xe0u8, 0xd7u8, 0x99u8, 0x94u8, 0xabu8,
        0xddu8, 0xbeu8, 0x70u8, 0xdfu8, 0xe4u8, 0x2cu8, 0x81u8, 0xa1u8, 0x38u8, 0xcdu8, 0x5eu8,
        0x35u8, 0x0fu8, 0xe2u8, 0x7cu8, 0x09u8, 0xc1u8, 0x94u8, 0x5fu8, 0xc1u8, 0x76u8
    ))
}

fn D_MINUS_ONE_SQ() -> FieldElement {
    FieldElement::from_byte_seq_be(&byte_seq!(
        0x59u8, 0x68u8, 0xb3u8, 0x7au8, 0xf6u8, 0x6cu8, 0x22u8, 0x41u8, 0x4cu8, 0xdcu8, 0xd3u8,
        0x2fu8, 0x52u8, 0x9bu8, 0x4eu8, 0xebu8, 0xd2u8, 0x9eu8, 0x4au8, 0x2cu8, 0xb0u8, 0x1eu8,
        0x19u8, 0x99u8, 0x31u8, 0xadu8, 0x5au8, 0xaau8, 0x44u8, 0xedu8, 0x4du8, 0x20u8
    ))
}

// === Helper functions === //

// Creates a field element from the given literal.
fn fe(x: usize) -> FieldElement {
    FieldElement::from_literal(x as u128)
}

// === Internal Utility Functions === //

// Checks if a given field element is negative. A negative field element is defined as an odd number.
fn is_negative(e: FieldElement) -> bool {
    e % fe(2) == fe(1)
}

// Checks if two given field elements are equal.
// Should run constant time, which will be possible if FieldElement is changed to Secret Ints
fn eq(u: FieldElement, v: FieldElement) -> bool {
    u == v
}

// Given a condition it selects u if the condition is true and v if it is false.
// Should run constant time, which will be possible if FieldElement is changed to Secret Ints
fn select(u: FieldElement, cond: bool, v: FieldElement) -> FieldElement {
    if cond {
        u
    } else {
        v
    }
}

// Computes the additive negation of the given field element.
fn neg_fe(u: FieldElement) -> FieldElement {
    fe(0) - u
}

// Returns the absolute value of the given field element.
// Should run constant time, which will be possible if FieldElement is changed to Secret Ints
fn abs(u: FieldElement) -> FieldElement {
    select(neg_fe(u), is_negative(u), u)
}

// Computes if the division of the two given field elements is square and returns said square.
// This function has four different cases, for which it returns different values:
// 1: if u, the numerator is 0 it returns (true,0).
// 2: if v, the denominator is 0 it returns (false, 0) as you cannot divide by 0.
// 3: if both are non-zero and u/v is square it returns (true, square).
// 4: if both are non-zero and u/v is not square it returns (false, SQRT_M1*(u/v)).
fn sqrt_ratio_m1(u: FieldElement, v: FieldElement) -> (bool, FieldElement) {
    let v3 = v.pow(2u128) * v;
    let v7 = v3.pow(2u128) * v;
    let mut r = (u * v3) * (u * v7).pow_felem((P() - fe(5)) / fe(8));
    let check = v * r.pow(2u128);

    let correct_sign_sqrt = eq(check, u);
    let flipped_sign_sqrt = eq(check, neg_fe(u));
    let flipped_sign_sqrt_i = eq(check, neg_fe(u) * SQRT_M1());

    let r_prime = SQRT_M1() * r;
    r = select(r_prime, flipped_sign_sqrt || flipped_sign_sqrt_i, r);

    // Choose the nonnegative square root.
    r = abs(r);

    let was_square = correct_sign_sqrt || flipped_sign_sqrt;

    (was_square, r)
}
