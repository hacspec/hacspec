use core::ops::Mul;
/// This code is inspired from Dalek's field multiplication for 64-bits backends contained in the
/// file [`src/backend/u64/field.rs`](https://github.com/dalek-cryptography/curve25519-dalek/blob/master/src/backend/u64/field.rs)
use secret_integers::*;

/// A `FieldElement64` represents an element of the field
/// \\( \mathbb Z / (2\^{255} - 19)\\).
///
/// In the 64-bit implementation, a `FieldElement` is represented in
/// radix \\(2\^{51}\\) as five `u64`s; the coefficients are allowed to
/// grow up to \\(2\^{54}\\) between reductions modulo \\(p\\).
///
/// # Note
///
/// The `curve25519_dalek::field` module provides a type alias
/// `curve25519_dalek::field::FieldElement` to either `FieldElement64`
/// or `FieldElement32`.
///
/// The backend-specific type `FieldElement64` should not be used
/// outside of the `curve25519_dalek::field` module.
type Limb = U64;

#[derive(Copy, Clone)]
pub struct FieldElement64(pub(crate) [Limb; 5]);

impl<'a, 'b> Mul<&'b FieldElement64> for &'a FieldElement64 {
    type Output = FieldElement64;
    fn mul(self, _rhs: &'b FieldElement64) -> FieldElement64 {
        /// Helper function to multiply two 64-bit integers with 128
        /// bits of output.
        #[inline(always)]
        fn m(x: U64, y: U64) -> U128 {
            U128::from(x) * y.into()
        }

        // Alias self, _rhs for more readable formulas
        let a: &[Limb; 5] = &self.0;
        let b: &[Limb; 5] = &_rhs.0;

        // Precondition: assume input limbs a[i], b[i] are bounded as
        //
        // a[i], b[i] < 2^(51 + b)
        //
        // where b is a real parameter measuring the "bit excess" of the limbs.

        // 64-bit precomputations to avoid 128-bit multiplications.
        //
        // This fits into a u64 whenever 51 + b + lg(19) < 64.
        //
        // Since 51 + b + lg(19) < 51 + 4.25 + b
        //                       = 55.25 + b,
        // this fits if b < 8.75.
        let nineteen = 19u64.into();
        let b1_19 = b[1] * nineteen;
        let b2_19 = b[2] * nineteen;
        let b3_19 = b[3] * nineteen;
        let b4_19 = b[4] * nineteen;

        // Multiply to get 128-bit coefficients of output
        let c0: U128 =
            m(a[0], b[0]) + m(a[4], b1_19) + m(a[3], b2_19) + m(a[2], b3_19) + m(a[1], b4_19);
        let mut c1: U128 =
            m(a[1], b[0]) + m(a[0], b[1]) + m(a[4], b2_19) + m(a[3], b3_19) + m(a[2], b4_19);
        let mut c2: U128 =
            m(a[2], b[0]) + m(a[1], b[1]) + m(a[0], b[2]) + m(a[4], b3_19) + m(a[3], b4_19);
        let mut c3: U128 =
            m(a[3], b[0]) + m(a[2], b[1]) + m(a[1], b[2]) + m(a[0], b[3]) + m(a[4], b4_19);
        let mut c4: U128 =
            m(a[4], b[0]) + m(a[3], b[1]) + m(a[2], b[2]) + m(a[1], b[3]) + m(a[0], b[4]);

        // How big are the c[i]? We have
        //
        //    c[i] < 2^(102 + 2*b) * (1+i + (4-i)*19)
        //         < 2^(102 + lg(1 + 4*19) + 2*b)
        //         < 2^(108.27 + 2*b)
        //
        // The carry (c[i] >> 51) fits into a u64 when
        //    108.27 + 2*b - 51 < 64
        //    2*b < 6.73
        //    b < 3.365.
        //
        // So we require b < 3 to ensure this fits.
        debug_assert!(U64::declassify(a[0]) < (1 << 54));
        debug_assert!(U64::declassify(b[0]) < (1 << 54));
        debug_assert!(U64::declassify(a[1]) < (1 << 54));
        debug_assert!(U64::declassify(b[1]) < (1 << 54));
        debug_assert!(U64::declassify(a[2]) < (1 << 54));
        debug_assert!(U64::declassify(b[2]) < (1 << 54));
        debug_assert!(U64::declassify(a[3]) < (1 << 54));
        debug_assert!(U64::declassify(b[3]) < (1 << 54));
        debug_assert!(U64::declassify(a[4]) < (1 << 54));
        debug_assert!(U64::declassify(b[4]) < (1 << 54));

        // Casting to u64 and back tells the compiler that the carry is
        // bounded by 2^64, so that the addition is a u128 + u64 rather
        // than u128 + u128.

        const LOW_51_BIT_MASK: u64 = (1u64 << 51) - 1;
        let mut out = [U64::classify(0u64); 5];

        c1 += U64::from(c0 >> 51).into();
        out[0] = U64::from(c0) & LOW_51_BIT_MASK.into();

        c2 += U64::from(c1 >> 51).into();
        out[1] = U64::from(c1) & LOW_51_BIT_MASK.into();

        c3 += U64::from(c2 >> 51).into();
        out[2] = U64::from(c2) & LOW_51_BIT_MASK.into();

        c4 += U64::from(c3 >> 51).into();
        out[3] = U64::from(c3) & LOW_51_BIT_MASK.into();

        let carry: U64 = (c4 >> 51).into();
        out[4] = U64::from(c4) & LOW_51_BIT_MASK.into();

        // To see that this does not overflow, we need out[0] + carry * 19 < 2^64.
        //
        // c4 < a0*b4 + a1*b3 + a2*b2 + a3*b1 + a4*b0 + (carry from c3)
        //    < 5*(2^(51 + b) * 2^(51 + b)) + (carry from c3)
        //    < 2^(102 + 2*b + lg(5)) + 2^64.
        //
        // When b < 3 we get
        //
        // c4 < 2^110.33  so that carry < 2^59.33
        //
        // so that
        //
        // out[0] + carry * 19 < 2^51 + 19 * 2^59.33 < 2^63.58
        //
        // and there is no overflow.
        out[0] = out[0] + carry * nineteen;

        // Now out[1] < 2^51 + 2^(64 -51) = 2^51 + 2^13 < 2^(51 + epsilon).
        out[1] += out[0] >> 51;
        out[0] &= LOW_51_BIT_MASK.into();

        // Now out[i] < 2^(51 + epsilon) for all i.
        FieldElement64(out)
    }
}
