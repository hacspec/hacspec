use abstract_integers::*;

abstract_unsigned_public_integer!(BigBounded, 256);
abstract_public_modular_integer!(
    Felem,
    BigBounded,
    BigBounded::pow2(255) - BigBounded::from_literal(19)
);

#[test]
fn arith() {
    let x1 = Felem::from_literal(24875808327634644);
    let x2 = Felem::from_literal(91987276365379830);
    let x3 = x1 + x2;
    assert_eq!(Felem::from_literal(116863084693014474u128), x3.into())
}

abstract_public_modular_integer!(SmallModular, BigBounded, BigBounded::from_literal(127));

#[test]
fn wrapping() {
    let x1 = SmallModular::from_literal(126);
    let x2 = SmallModular::from_literal(3);
    let x3 = x1 + x2;
    assert_eq!(SmallModular::from_literal(2), x3.into());
    let x4 = SmallModular::from_literal(5);
    let x5 = x3 - x4;
    assert_eq!(SmallModular::from_literal(124), x5.into());
    let x6 = x5 / SmallModular::from_literal(4);
    assert_eq!(SmallModular::from_literal(31), x6.into());
}

abstract_public_nat_mod!(
    FieldElement,
    Scalar,
    256,
    "ffffffff00000001000000000000000000000000ffffffffffffffffffffffff"
);

#[test]
fn conversion() {
    let x =
        FieldElement::from_hex("6B17D1F2E12C4247F8BCE6E563A440F277037D812DEB33A0F4A13945D898C296");
    let y =
        FieldElement::from_hex("4FE342E2FE1A7F9B8EE7EB4A7C0F9E162BCE33576B315ECECBB6406837BF51F5");
    let _z = x * y;
    ()
}
