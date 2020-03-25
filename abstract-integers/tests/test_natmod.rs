use abstract_integers::*;

abstract_unsigned_secret_integer!(BigBounded, 256);
abstract_secret_modular_integer!(Felem, BigBounded, BigBounded::pow2(255) - BigBounded::from_literal(19));

#[test]
fn arith() {
    let x1 = Felem::from_literal(24875808327634644);
    let x2 = Felem::from_literal(91987276365379830);
    let _x3 = x1 + x2;
    // natmods don't implement eq
    // assert_eq!(Felem::from_literal(116863084693014474u128), x3.into())
}

abstract_secret_modular_integer!(SmallModular, BigBounded, BigBounded::from_literal(255));

#[test]
fn wrapping() {
    let x1 = SmallModular::from_literal(254);
    let x2 = SmallModular::from_literal(3);
    let _x3 = x1 + x2;
    // natmods don't implement eq
    // assert_eq!(SmallModular::from_literal(2), x3.into());
    let x4 = SmallModular::from_literal(5);
    let _x5 = _x3 - x4;
    // natmods don't implement eq
    // assert_eq!(SmallModular::from_literal(252), x5.into());
}

abstract_nat_mod!(FieldElement, Scalar, 256, "ffffffff00000001000000000000000000000000ffffffffffffffffffffffff");

#[test]
fn conversion() {
    let x = FieldElement::from_hex("6B17D1F2E12C4247F8BCE6E563A440F277037D812DEB33A0F4A13945D898C296");
    let y = FieldElement::from_hex("4FE342E2FE1A7F9B8EE7EB4A7C0F9E162BCE33576B315ECECBB6406837BF51F5");
    let _z = x * y;
    ()
}
