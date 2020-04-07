use hacspec::prelude::*;

// XXX: Careful in here. The `test` functions use `Numeric` functions and hence
//      will end up being the same as what they test. Rewrite when merging!

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

#[test]
fn test_csub() {
    fn test<T: TempNumeric>(x: T, y: T) {
        let d = csub(x, y, T::default());
        assert!(d.equal(x));
        let d = csub(x, y, T::max_val());
        assert!(d.equal(x.wrap_sub(y)));
    }
    test(13u8, 234u8);
    test(827629u64, 16u64);
}

#[test]
fn test_cadd() {
    fn test<T: TempNumeric>(x: T, y: T) {
        let d = cadd(x, y, T::default());
        assert!(d.equal(x));
        let d = cadd(x, y, T::max_val());
        assert!(d.equal(x.wrap_add(y)));
    }
    test(13u8, 234u8);
    test(827629u64, 16u64);
}

#[test]
fn test_cmul() {
    fn test<T: TempNumeric>(x: T, y: T) {
        let d = cmul(x, y, T::default());
        assert!(d.equal(x));
        let d = cmul(x, y, T::max_val());
        assert!(d.equal(x.wrap_mul(y)));
    }
    test(13u8, 234u8);
    test(827629u64, 16u64);
}

#[test]
fn test_div() {
    fn test<T: TempNumeric>(x: T, y: T) {
        let (q, r) = ct_div(x, y);
        assert!(q.equal(x.div(y)));
        assert!(r.equal(x.rem(y)));
    }

    fn test_8(x: u8, y: u8) {
        test(x, y);
        test(U8(x), U8(y));
    }
    test_8(13, 234);

    fn test_16(x: u16, y: u16) {
        test(x, y);
        test(U16(x), U16(y));
    }
    test_16(13, 234);

    fn test_32(x: u32, y: u32) {
        test(x, y);
        test(U32(x), U32(y));
    }
    test_32(827629, 12);

    fn test_64(x: u64, y: u64) {
        test(x, y);
        test(U64(x), U64(y));
    }
    test_64(827629, 12);
    test_64(16, 827629);
}
