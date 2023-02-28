#![allow(unused_variables)]
use crate::prelude::*;

impl Integer for BigInt {
    /// `NUM_BITS` is arbitrary for `BigInt`, so this i `0`.
    fn NUM_BITS() -> usize { 0 }

    #[inline]
    #[cfg_attr(feature = "use_attributes", not_hacspec)]
    fn ZERO() -> Self {
        BigInt::from(0)
    }
    #[inline]
    #[cfg_attr(feature = "use_attributes", not_hacspec)]
    fn ONE() -> Self {
        BigInt::from(1)
    }
    #[inline]
    #[cfg_attr(feature = "use_attributes", not_hacspec)]
    fn TWO() -> Self {
        BigInt::from(2)
    }

    #[inline]
    #[cfg_attr(feature = "use_attributes", not_hacspec)]
    fn from_literal(val: u128) -> Self {
        BigInt::from(val)
    }

    #[inline]
    #[cfg_attr(feature = "use_attributes", not_hacspec)]
    #[trusted]
    fn from_hex_string(s: &String) -> Self {
        BigInt::from_str(s).unwrap()
    }

    /// Get bit `i` of this integer.
    #[inline]
    #[cfg_attr(feature = "use_attributes", in_hacspec)]
    fn get_bit(self, i: usize) -> Self {
        (self >> i) & Self::ONE()
    }

    /// Set bit `i` of this integer to `b` and return the result.
    /// Bit `b` has to be `0` or `1`.
    #[inline]
    #[cfg_attr(feature = "use_attributes", in_hacspec)]
    #[trusted]
    fn set_bit(self, b: Self, i: usize) -> Self {
        debug_assert!(b.clone().equal(Self::ONE()) || b.clone().equal(Self::ZERO()));
        let tmp1 = Self::from_literal(!(1 << i));
        let tmp2 = b << i;
        (self & tmp1) | tmp2
    }

    /// Set bit `pos` of this integer to bit `yi` of integer `y`.
    #[inline]
    #[cfg_attr(feature = "use_attributes", in_hacspec)]
    fn set(self, pos: usize, y: Self, yi: usize) -> Self {
        let b = y.get_bit(yi);
        self.set_bit(b, pos)
    }

    #[allow(arithmetic_overflow)]
    #[cfg_attr(feature = "use_attributes", in_hacspec)]
    #[trusted]
    fn rotate_left(self, n: usize) -> Self {
        // Taken from https://blog.regehr.org/archives/1063
        assert!(n < Self::NUM_BITS()); // TODO: , "not {} < {}", n, Self::NUM_BITS());
        (self.clone() << n) | (self >> ((-(n as i32) as usize) & (Self::NUM_BITS() - 1)))
    }

    #[allow(arithmetic_overflow)]
    #[cfg_attr(feature = "use_attributes", in_hacspec)]
    #[trusted]
    fn rotate_right(self, n: usize) -> Self {
        // Taken from https://blog.regehr.org/archives/1063
        assert!(n < Self::NUM_BITS());
        (self.clone() >> n) | (self << ((-(n as i32) as usize) & (Self::NUM_BITS() - 1)))
    }
}
// extern_spec! {
    impl DeepModel for BigInt {
        type DeepModelTy = creusot_contracts::Int;

        #[logic]
        #[trusted]
        // #[ensures(self.shallow_model().len() == result.len())]
        // #[ensures(forall<i: Int> 0 <= i && i < self.shallow_model().len()
        //           ==> result[i] == (@self)[i].deep_model())]
        fn deep_model(self) -> Self::DeepModelTy {
            pearlite! { absurd }
        }
    }
// }
impl OrdLogic for BigInt {
    #[logic]
    fn cmp_log(self, other: Self) -> Ordering {
        Ordering::Equal // TODO
    }

    #[logic]
    fn cmp_le_log(_: Self, _: Self) {
        ()
    }

    #[logic]
    fn cmp_lt_log(_: Self, _: Self) {
        ()
    }

    #[logic]
    fn cmp_ge_log(_: Self, _: Self) {
        ()
    }

    #[logic]
    fn cmp_gt_log(_: Self, _: Self) {
        ()
    }

    #[logic]
    fn refl(_: Self) {
        ()
    }

    #[logic]
    fn trans(_: Self, _: Self, _: Self, _: Ordering) {
        ()
    }

    #[logic]
    fn antisym1(_: Self, _: Self) {
        ()
    }

    #[logic]
    fn antisym2(_: Self, _: Self) {
        ()
    }

    #[logic]
    fn eq_cmp(_: Self, _: Self) {
        ()
    }
}
impl Numeric for BigInt {
    /// Return largest value that can be represented.
    #[cfg_attr(feature = "use_attributes", not_hacspec)]
    fn max_val() -> Self {
        unimplemented!();
    }

    #[cfg_attr(feature = "use_attributes", not_hacspec)]
    fn wrap_add(self, rhs: Self) -> Self {
        self + rhs
    }
    #[cfg_attr(feature = "use_attributes", not_hacspec)]
    fn wrap_sub(self, rhs: Self) -> Self {
        self - rhs
    }
    #[cfg_attr(feature = "use_attributes", not_hacspec)]
    fn wrap_mul(self, rhs: Self) -> Self {
        self * rhs
    }
    #[cfg_attr(feature = "use_attributes", not_hacspec)]
    fn wrap_div(self, rhs: Self) -> Self {
        unimplemented!();
    }

    /// `self ^ exp` where `exp` is a `u32`.
    #[cfg_attr(feature = "use_attributes", not_hacspec)]
    fn exp(self, exp: u32) -> Self {
        unimplemented!();
    }
    /// `self ^ exp` where `exp` is a `Self`.
    #[cfg_attr(feature = "use_attributes", not_hacspec)]
    fn pow_self(self, exp: Self) -> Self {
        unimplemented!();
    }
    /// Division.
    #[cfg_attr(feature = "use_attributes", not_hacspec)]
    fn divide(self, rhs: Self) -> Self {
        unimplemented!();
    }
    /// Invert self modulo n.
    #[cfg_attr(feature = "use_attributes", not_hacspec)]
    fn inv(self, n: Self) -> Self {
        unimplemented!();
    }

    // Comparison functions returning bool.
    #[cfg_attr(feature = "use_attributes", not_hacspec)]
    fn equal(self, other: Self) -> bool {
        self.eq(&other)
    }
    #[cfg_attr(feature = "use_attributes", not_hacspec)]
    fn greater_than(self, other: Self) -> bool {
        unimplemented!();
    }
    #[cfg_attr(feature = "use_attributes", not_hacspec)]
    fn greater_than_or_equal(self, other: Self) -> bool {
        unimplemented!();
    }
    #[cfg_attr(feature = "use_attributes", not_hacspec)]
    fn less_than(self, other: Self) -> bool {
        self.lt(&other)
    }
    #[cfg_attr(feature = "use_attributes", not_hacspec)]
    fn less_than_or_equal(self, other: Self) -> bool {
        unimplemented!();
    }

    // Comparison functions returning a bit mask (0x0..0 or 0xF..F).
    #[cfg_attr(feature = "use_attributes", not_hacspec)]
    fn not_equal_bm(self, other: Self) -> Self {
        unimplemented!();
    }
    #[cfg_attr(feature = "use_attributes", not_hacspec)]
    fn equal_bm(self, other: Self) -> Self {
        unimplemented!();
    }
    #[cfg_attr(feature = "use_attributes", not_hacspec)]
    fn greater_than_bm(self, other: Self) -> Self {
        unimplemented!();
    }
    #[cfg_attr(feature = "use_attributes", not_hacspec)]
    fn greater_than_or_equal_bm(self, other: Self) -> Self {
        unimplemented!();
    }
    #[cfg_attr(feature = "use_attributes", not_hacspec)]
    fn less_than_bm(self, other: Self) -> Self {
        unimplemented!();
    }
    #[cfg_attr(feature = "use_attributes", not_hacspec)]
    fn less_than_or_equal_bm(self, other: Self) -> Self {
        unimplemented!();
    }
}

impl ModNumeric for BigInt {
    /// (self - rhs) % n.
    #[cfg_attr(feature = "use_attributes", not_hacspec)]
    fn sub_mod(self, rhs: Self, n: Self) -> Self {
        (self - rhs) % n
    }
    /// `(self + rhs) % n`
    #[cfg_attr(feature = "use_attributes", not_hacspec)]
    fn add_mod(self, rhs: Self, n: Self) -> Self {
        (self + rhs) % n
    }
    /// `(self * rhs) % n`
    #[cfg_attr(feature = "use_attributes", not_hacspec)]
    fn mul_mod(self, rhs: Self, n: Self) -> Self {
        (self * rhs) % n
    }
    /// `(self ^ exp) % n`
    #[cfg_attr(feature = "use_attributes", not_hacspec)]
    fn pow_mod(self, exp: Self, n: Self) -> Self {
        unimplemented!();
    }
    /// `self % n`
    #[cfg_attr(feature = "use_attributes", not_hacspec)]
    fn modulo(self, n: Self) -> Self {
        self % n
    }
    /// `self % n` that always returns a positive integer
    #[cfg_attr(feature = "use_attributes", not_hacspec)]
    fn signed_modulo(self, n: Self) -> Self {
        unimplemented!();
    }
    /// `|self|`
    #[cfg_attr(feature = "use_attributes", not_hacspec)]
    #[trusted]
    fn absolute(self) -> Self {
        self.abs()
    }
}

impl PublicInteger for BigInt {
    type SecretVersion = BigInt;
}

impl SecretInteger for BigInt {
    type PublicVersion = BigInt;
    #[cfg_attr(feature = "use_attributes", not_hacspec)]
    fn classify(x: Self::PublicVersion) -> Self {
        x
    }
}
