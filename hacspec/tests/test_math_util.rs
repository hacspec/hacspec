use hacspec::prelude::*;

#[test]
fn test_cswap() {
    let x = 123u8;
    let y = 234u8;

    let (xs, ys) = cswap(x, y, 0);
    assert_eq!(xs, x);
    assert_eq!(ys, y);
    let (xs, ys) = cswap_bit(x, y, 0);
    assert_eq!(xs, x);
    assert_eq!(ys, y);
    let (xs, ys) = cswap(x, y, u8::max_val());
    assert_eq!(xs, y);
    assert_eq!(ys, x);
    let (xs, ys) = cswap_bit(x, y, 1);
    assert_eq!(xs, y);
    assert_eq!(ys, x);
}
