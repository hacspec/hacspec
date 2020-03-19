use hacspec::prelude::*;

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
fn test_unsigned_secret_integer() {
    unsigned_secret_integer!(LargeSecretInteger, 233);
    let a = LargeSecretInteger::from_literal(1);
    let b = LargeSecretInteger::from_literal(2);
    let c = a + b;
    // FIXME: Panics because equal is not implemented yet
    assert!(c.equal(LargeSecretInteger::from_literal(3)));
}
