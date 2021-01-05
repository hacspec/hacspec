use hacspec_lib::prelude::*;

#[test]
fn test_unsigned_public_integers() {
    unsigned_public_integer!(LargeInteger, 233);
    let a = LargeInteger::from_literal(1);
    let b = LargeInteger::from_literal(2);
    let c = a + b;
    assert_eq!(c, LargeInteger::from_literal(3));
}

#[test]
#[should_panic]
fn test_unsigned_integer() {
    unsigned_integer!(LargeSecretInteger, 233);
    let a = LargeSecretInteger::from_literal(1);
    let b = LargeSecretInteger::from_literal(2);
    let c = a + b;
    // FIXME: Panics because equal is not implemented yet
    assert!(c.equal(LargeSecretInteger::from_literal(3)));
}
#[test]
fn test_signed_public_integers() {
    signed_public_integer!(LargeSignedInteger, 233);
    let a = LargeSignedInteger::from_literal(1);
    let b = LargeSignedInteger::from_literal(2);
    let c = a + b;
    assert_eq!(c, LargeSignedInteger::from_literal(3));
}

#[test]
#[should_panic]
fn test_signed_integer() {
    signed_integer!(LargeSecretSignedInteger, 233);
    let a = LargeSecretSignedInteger::from_literal(1);
    let b = LargeSecretSignedInteger::from_literal(2);
    let c = a + b;
    // FIXME: Panics because equal is not implemented yet
    assert!(c.equal(LargeSecretSignedInteger::from_literal(3)));
}

#[test]
fn test_public_nat_mod() {
    public_nat_mod!(
        type_name: Elem,
        type_of_canvas: P256Canvas,
        bit_size_of_field: 256,
        modulo_value: "ffffffff00000001000000000000000000000000ffffffffffffffffffffffff"
    );
    let g_x = Elem::from_hex("6B17D1F2E12C4247F8BCE6E563A440F277037D812DEB33A0F4A13945D898C296");
    let g_y = Elem::from_hex("4FE342E2FE1A7F9B8EE7EB4A7C0F9E162BCE33576B315ECECBB6406837BF51F5");
    let _g_g = g_x * g_y;
}

#[test]
fn test_secret_nat_mod() {
    nat_mod!(
        type_name: Elem,
        type_of_canvas: P256Canvas,
        bit_size_of_field: 256,
        modulo_value: "ffffffff00000001000000000000000000000000ffffffffffffffffffffffff"
    );
    let g_x = Elem::from_hex("6B17D1F2E12C4247F8BCE6E563A440F277037D812DEB33A0F4A13945D898C296");
    let g_y = Elem::from_hex("4FE342E2FE1A7F9B8EE7EB4A7C0F9E162BCE33576B315ECECBB6406837BF51F5");
    let _g_g = g_x * g_y;
}
