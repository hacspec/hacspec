use secret_integers::*;

#[test]
fn test_eq() {
    let a = U32(123456);
    let b = U32(123456);
    assert_eq!(U32::declassify(a.comp_eq(b)), u32::max_value());
    let b = U32(123457);
    assert_eq!(U32::declassify(a.comp_eq(b)), 0);
}

macro_rules! define_tests {
    // Note that the u8 here is necessary because the integers get interpreted
    // as i32 on Linux otherwise.
    ($modname:ident, $type:ident) => {
        #[cfg(test)]
        mod $modname {
            use crate::*;

            #[test]
            fn test_comp_eq_ok() {
                let a = $type::from(3u8);
                let b = $type::from(3u8);
                let eq = $type::comp_eq(a, b);
                assert_eq!(eq.declassify(), $type::ones().declassify());
            }

            #[test]
            fn test_comp_eq_fail() {
                let a = $type::from(3u8);
                let b = $type::from(42u8);
                let eq = $type::comp_eq(a, b);
                assert_eq!(eq.declassify(), $type::zero().declassify());
            }

            #[test]
            fn test_comp_neq_ok() {
                let a = $type::from(3u8);
                let b = $type::from(42u8);
                let eq = $type::comp_ne(a, b);
                assert_eq!(eq.declassify(), $type::ones().declassify());
            }

            #[test]
            fn test_comp_neq_fail() {
                let a = $type::from(3u8);
                let b = $type::from(3u8);
                let eq = $type::comp_ne(a, b);
                assert_eq!(eq.declassify(), $type::zero().declassify());
            }

            #[test]
            fn test_comp_gte_ok() {
                let a = $type::from(42u8);
                let b = $type::from(3u8);
                let eq = $type::comp_gte(a, b);
                assert_eq!(eq.declassify(), $type::ones().declassify());
            }

            #[test]
            fn test_comp_gte_fail() {
                let a = $type::from(3u8);
                let b = $type::from(42u8);
                let eq = $type::comp_gte(a, b);
                assert_eq!(eq.declassify(), $type::zero().declassify());

                let a = $type::from(0u8);
                let b = $type::from(3u8);
                let eq = $type::comp_gte(a, b);
                assert_eq!(eq.declassify(), $type::zero().declassify());
            }
        }
    };
}

define_tests!(tests_u8, U8);
define_tests!(tests_u32, U32);
define_tests!(tests_u64, U64);
define_tests!(tests_u128, U128);
