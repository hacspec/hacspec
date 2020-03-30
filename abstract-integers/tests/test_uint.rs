use abstract_integers::*;

abstract_unsigned_secret_integer!(BigBounded, 256);

#[test]
#[should_panic]
fn bounded() {
    let y1 = (BigBounded::pow2(255) - BigBounded::from_literal(1)) * BigBounded::from_literal(2);
    let y2 = BigBounded::from_literal(4);
    let _y3 = y1 + y2;
}
