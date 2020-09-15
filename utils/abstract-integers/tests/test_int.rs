use abstract_integers::*;

abstract_signed_secret_integer!(BigBounded, 256);

#[test]
#[should_panic]
fn bounded() {
    println!("BigBounded::max(): {:x}", BigBounded::max());
    let y1 = (BigBounded::pow2(255) - BigBounded::from_literal(1)) * BigBounded::from_literal(2);
    let y2 = BigBounded::from_literal(4);
    let _y3 = y1 + y2;
}
