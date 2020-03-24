#![allow(unused_variables)]
///!
///! Implement the `Numeric` trait for arrays.
///!

#[macro_export]
macro_rules! _implement_numeric_unsigned_public {
    ($name:ident) => {
        impl PartialOrd for $name {
            fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
                Some(self.cmp(other))
            }
        }
        impl Ord for $name {
            fn cmp(&self, other: &Self) -> Ordering {
                self.0.cmp(&other.0)
            }
        }
        impl Eq for $name {}

        /// **Warning**: wraps on overflow.
        impl Add for $name {
            type Output = $name;
            fn add(self, rhs: $name) -> $name {
                debug_assert!(self.len() == rhs.len());
                if self.len() != rhs.len() {
                    panic!("Can't add two sequences that don't have the same length.");
                }
                let mut out = Self::new();
                for (a, (&b, &c)) in out.iter_mut().zip(self.iter().zip(rhs.iter())) {
                    *a = b.wrapping_add(c);
                }
                out
            }
        }

        /// **Warning**: wraps on underflow.
        impl Sub for $name {
            type Output = $name;
            fn sub(self, rhs: $name) -> $name {
                debug_assert!(self.len() == rhs.len());
                if self.len() != rhs.len() {
                    panic!("Can't add two sequences that don't have the same length.");
                }
                let mut out = Self::new();
                for (a, (&b, &c)) in out.iter_mut().zip(self.iter().zip(rhs.iter())) {
                    *a = b.wrapping_sub(c);
                }
                out
            }
        }

        /// **Warning**: wraps on overflow.
        impl Mul for $name {
            type Output = $name;
            fn mul(self, rhs: $name) -> $name {
                debug_assert!(self.len() == rhs.len());
                if self.len() != rhs.len() {
                    panic!("Can't add two sequences that don't have the same length.");
                }
                let mut out = Self::new();
                for (a, (&b, &c)) in out.iter_mut().zip(self.iter().zip(rhs.iter())) {
                    *a = b.wrapping_mul(c);
                }
                out
            }
        }

        /// **Warning**: panics on division by 0.
        impl Div for $name {
            type Output = $name;
            fn div(self, rhs: $name) -> $name {
                debug_assert!(self.len() == rhs.len());
                if self.len() != rhs.len() {
                    panic!("Can't add two sequences that don't have the same length.");
                }
                let mut out = Self::new();
                for (a, (&b, &c)) in out.iter_mut().zip(self.iter().zip(rhs.iter())) {
                    *a = b / c;
                }
                out
            }
        }

        /// **Warning**: panics on division by 0.
        impl Rem for $name {
            type Output = $name;
            fn rem(self, rhs: $name) -> $name {
                unimplemented!();
            }
        }

        impl Not for $name {
            type Output = $name;
            fn not(self) -> Self::Output {
                unimplemented!();
            }
        }

        impl BitOr for $name {
            type Output = $name;
            fn bitor(self, rhs: Self) -> Self::Output {
                unimplemented!();
            }
        }

        impl BitXor for $name {
            type Output = $name;
            fn bitxor(self, rhs: Self) -> Self::Output {
                let mut out = Self::new();
                for (a, (b, c)) in out.0.iter_mut().zip(self.0.iter().zip(rhs.0.iter())) {
                    *a = *b ^ *c;
                }
                out
            }
        }

        impl BitAnd for $name {
            type Output = $name;
            fn bitand(self, rhs: Self) -> Self::Output {
                unimplemented!();
            }
        }

        impl Shr<u32> for $name {
            type Output = $name;
            fn shr(self, rhs: u32) -> Self::Output {
                unimplemented!();
            }
        }

        impl Shl<u32> for $name {
            type Output = $name;
            fn shl(self, rhs: u32) -> Self::Output {
                unimplemented!();
            }
        }

        impl Numeric for $name {
            /// Return largest value that can be represented.
            fn max_val() -> Self {
                unimplemented!();
            }
        
            /// `self ^ exp` where `exp` is a `u32`.
            fn pow(self, exp: u32) -> Self {
                unimplemented!();
            }
            /// `self ^ exp` where `exp` is a `Self`.
            fn pow_self(self, exp: Self) -> Self {
                unimplemented!();
            }
            /// (self - rhs) % n.
            fn sub_mod(self, rhs: Self, n: Self) -> Self {
                unimplemented!();
            }
            /// `(self + rhs) % n`
            fn add_mod(self, rhs: Self, n: Self) -> Self {
                unimplemented!();
            }
            /// `(self * rhs) % n`
            fn mul_mod(self, rhs: Self, n: Self) -> Self {
                unimplemented!();
            }
            /// `(self ^ exp) % n`
            fn pow_mod(self, exp: Self, n: Self) -> Self {
                unimplemented!();
            }
            /// Division.
            fn div(self, rhs: Self) -> Self {
                unimplemented!();
            }
            /// `self % n`
            fn rem(self, n: Self) -> Self {
                unimplemented!();
            }
            /// Invert self modulo n.
            fn inv(self, n: Self) -> Self {
                unimplemented!();
            }
            /// `|self|`
            fn abs(self) -> Self {
                unimplemented!();
            }
        
            // Comparison functions returning bool.
            fn equal(self, other: Self) -> bool {
                unimplemented!();
            }
            fn greater_than(self, other: Self) -> bool {
                unimplemented!();
            }
            fn greater_than_or_qual(self, other: Self) -> bool {
                unimplemented!();
            }
            fn less_than(self, other: Self) -> bool {
                unimplemented!();
            }
            fn less_than_or_equal(self, other: Self) -> bool {
                unimplemented!();
            }
        
            // Comparison functions returning a bit mask (0x0..0 or 0xF..F).
            fn not_equal_bm(self, other: Self) -> Self {
                unimplemented!();
            }
            fn equal_bm(self, other: Self) -> Self {
                unimplemented!();
            }
            fn greater_than_bm(self, other: Self) -> Self {
                unimplemented!();
            }
            fn greater_than_or_qual_bm(self, other: Self) -> Self {
                unimplemented!();
            }
            fn less_than_bm(self, other: Self) -> Self {
                unimplemented!();
            }
            fn less_than_or_equal_bm(self, other: Self) -> Self {
                unimplemented!();
            }
        }
    };
}

#[macro_export]
macro_rules! _implement_numeric_signed_public {
    ($name:ident) => {
        impl PartialOrd for $name {
            fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
                Some(self.cmp(other))
            }
        }
        impl Ord for $name {
            fn cmp(&self, other: &Self) -> Ordering {
                self.0.cmp(&other.0)
            }
        }
        impl Eq for $name {}

        /// **Warning**: wraps on overflow.
        impl Add for $name {
            type Output = $name;
            fn add(self, rhs: $name) -> $name {
                unimplemented!();
            }
        }

        /// **Warning**: wraps on underflow.
        impl Sub for $name {
            type Output = $name;
            fn sub(self, rhs: $name) -> $name {
                unimplemented!();
            }
        }

        /// **Warning**: wraps on overflow.
        impl Mul for $name {
            type Output = $name;
            fn mul(self, rhs: $name) -> $name {
                unimplemented!();
            }
        }

        /// **Warning**: panics on division by 0.
        impl Div for $name {
            type Output = $name;
            fn div(self, rhs: $name) -> $name {
                unimplemented!();
            }
        }

        /// **Warning**: panics on division by 0.
        impl Rem for $name {
            type Output = $name;
            fn rem(self, rhs: $name) -> $name {
                unimplemented!();
            }
        }

        impl Not for $name {
            type Output = $name;
            fn not(self) -> Self::Output {
                unimplemented!();
            }
        }

        impl BitOr for $name {
            type Output = $name;
            fn bitor(self, rhs: Self) -> Self::Output {
                unimplemented!();
            }
        }

        impl BitXor for $name {
            type Output = $name;
            fn bitxor(self, rhs: Self) -> Self::Output {
                unimplemented!();
            }
        }

        impl BitAnd for $name {
            type Output = $name;
            fn bitand(self, rhs: Self) -> Self::Output {
                unimplemented!();
            }
        }

        impl Shr<u32> for $name {
            type Output = $name;
            fn shr(self, rhs: u32) -> Self::Output {
                unimplemented!();
            }
        }

        impl Shl<u32> for $name {
            type Output = $name;
            fn shl(self, rhs: u32) -> Self::Output {
                unimplemented!();
            }
        }

        impl Numeric for $name {
            /// Return largest value that can be represented.
            fn max_val() -> Self {
                unimplemented!();
            }
        
            /// `self ^ exp` where `exp` is a `u32`.
            fn pow(self, exp: u32) -> Self {
                unimplemented!();
            }
            /// `self ^ exp` where `exp` is a `Self`.
            fn pow_self(self, exp: Self) -> Self {
                unimplemented!();
            }
            /// (self - rhs) % n.
            fn sub_mod(self, rhs: Self, n: Self) -> Self {
                unimplemented!();
            }
            /// `(self + rhs) % n`
            fn add_mod(self, rhs: Self, n: Self) -> Self {
                unimplemented!();
            }
            /// `(self * rhs) % n`
            fn mul_mod(self, rhs: Self, n: Self) -> Self {
                unimplemented!();
            }
            /// `(self ^ exp) % n`
            fn pow_mod(self, exp: Self, n: Self) -> Self {
                unimplemented!();
            }
            /// Division.
            fn div(self, rhs: Self) -> Self {
                unimplemented!();
            }
            /// `self % n`
            fn rem(self, n: Self) -> Self {
                unimplemented!();
            }
            /// Invert self modulo n.
            fn inv(self, n: Self) -> Self {
                unimplemented!();
            }
            /// `|self|`
            fn abs(self) -> Self {
                unimplemented!();
            }
        
            // Comparison functions returning bool.
            fn equal(self, other: Self) -> bool {
                unimplemented!();
            }
            fn greater_than(self, other: Self) -> bool {
                unimplemented!();
            }
            fn greater_than_or_qual(self, other: Self) -> bool {
                unimplemented!();
            }
            fn less_than(self, other: Self) -> bool {
                unimplemented!();
            }
            fn less_than_or_equal(self, other: Self) -> bool {
                unimplemented!();
            }
        
            // Comparison functions returning a bit mask (0x0..0 or 0xF..F).
            fn not_equal_bm(self, other: Self) -> Self {
                unimplemented!();
            }
            fn equal_bm(self, other: Self) -> Self {
                unimplemented!();
            }
            fn greater_than_bm(self, other: Self) -> Self {
                unimplemented!();
            }
            fn greater_than_or_qual_bm(self, other: Self) -> Self {
                unimplemented!();
            }
            fn less_than_bm(self, other: Self) -> Self {
                unimplemented!();
            }
            fn less_than_or_equal_bm(self, other: Self) -> Self {
                unimplemented!();
            }
        }
    };
}

#[macro_export]
macro_rules! _implement_numeric_unsigned_secret {
    ($name:ident) => {
        /// **Warning**: wraps on overflow.
        impl Add for $name {
            type Output = $name;
            fn add(self, rhs: $name) -> $name {
                debug_assert!(self.len() == rhs.len());
                if self.len() != rhs.len() {
                    panic!("Can't add two sequences that don't have the same length.");
                }
                let mut out = Self::new();
                for (a, (&b, &c)) in out.iter_mut().zip(self.iter().zip(rhs.iter())) {
                    *a = b + c;
                }
                out
            }
        }

        /// **Warning**: wraps on underflow.
        impl Sub for $name {
            type Output = $name;
            fn sub(self, rhs: $name) -> $name {
                debug_assert!(self.len() == rhs.len());
                if self.len() != rhs.len() {
                    panic!("Can't add two sequences that don't have the same length.");
                }
                let mut out = Self::new();
                for (a, (&b, &c)) in out.iter_mut().zip(self.iter().zip(rhs.iter())) {
                    *a = b - c;
                }
                out
            }
        }

        /// **Warning**: wraps on overflow.
        impl Mul for $name {
            type Output = $name;
            fn mul(self, rhs: $name) -> $name {
                debug_assert!(self.len() == rhs.len());
                if self.len() != rhs.len() {
                    panic!("Can't add two sequences that don't have the same length.");
                }
                let mut out = Self::new();
                for (a, (&b, &c)) in out.iter_mut().zip(self.iter().zip(rhs.iter())) {
                    *a = b * c;
                }
                out
            }
        }

        /// **Warning**: panics on division by 0.
        impl Rem for $name {
            type Output = $name;
            fn rem(self, rhs: $name) -> $name {
                unimplemented!();
            }
        }

        impl Not for $name {
            type Output = $name;
            fn not(self) -> Self::Output {
                unimplemented!();
            }
        }

        impl BitOr for $name {
            type Output = $name;
            fn bitor(self, rhs: Self) -> Self::Output {
                unimplemented!();
            }
        }

        impl BitXor for $name {
            type Output = $name;
            fn bitxor(self, rhs: Self) -> Self::Output {
                let mut out = Self::new();
                for (a, (b, c)) in out.0.iter_mut().zip(self.0.iter().zip(rhs.0.iter())) {
                    *a = *b ^ *c;
                }
                out
            }
        }

        impl BitAnd for $name {
            type Output = $name;
            fn bitand(self, rhs: Self) -> Self::Output {
                unimplemented!();
            }
        }

        impl Shr<u32> for $name {
            type Output = $name;
            fn shr(self, rhs: u32) -> Self::Output {
                unimplemented!();
            }
        }

        impl Shl<u32> for $name {
            type Output = $name;
            fn shl(self, rhs: u32) -> Self::Output {
                unimplemented!();
            }
        }

        impl Numeric for $name {
            /// Return largest value that can be represented.
            fn max_val() -> Self {
                unimplemented!();
            }
        
            /// `self ^ exp` where `exp` is a `u32`.
            fn pow(self, exp: u32) -> Self {
                unimplemented!();
            }
            /// `self ^ exp` where `exp` is a `Self`.
            fn pow_self(self, exp: Self) -> Self {
                unimplemented!();
            }
            /// (self - rhs) % n.
            fn sub_mod(self, rhs: Self, n: Self) -> Self {
                unimplemented!();
            }
            /// `(self + rhs) % n`
            fn add_mod(self, rhs: Self, n: Self) -> Self {
                unimplemented!();
            }
            /// `(self * rhs) % n`
            fn mul_mod(self, rhs: Self, n: Self) -> Self {
                unimplemented!();
            }
            /// `(self ^ exp) % n`
            fn pow_mod(self, exp: Self, n: Self) -> Self {
                unimplemented!();
            }
            /// Division.
            fn div(self, rhs: Self) -> Self {
                unimplemented!();
            }
            /// `self % n`
            fn rem(self, n: Self) -> Self {
                unimplemented!();
            }
            /// Invert self modulo n.
            fn inv(self, n: Self) -> Self {
                unimplemented!();
            }
            /// `|self|`
            fn abs(self) -> Self {
                unimplemented!();
            }
        
            // Comparison functions returning bool.
            fn equal(self, other: Self) -> bool {
                unimplemented!();
            }
            fn greater_than(self, other: Self) -> bool {
                unimplemented!();
            }
            fn greater_than_or_qual(self, other: Self) -> bool {
                unimplemented!();
            }
            fn less_than(self, other: Self) -> bool {
                unimplemented!();
            }
            fn less_than_or_equal(self, other: Self) -> bool {
                unimplemented!();
            }
        
            // Comparison functions returning a bit mask (0x0..0 or 0xF..F).
            fn not_equal_bm(self, other: Self) -> Self {
                unimplemented!();
            }
            fn equal_bm(self, other: Self) -> Self {
                unimplemented!();
            }
            fn greater_than_bm(self, other: Self) -> Self {
                unimplemented!();
            }
            fn greater_than_or_qual_bm(self, other: Self) -> Self {
                unimplemented!();
            }
            fn less_than_bm(self, other: Self) -> Self {
                unimplemented!();
            }
            fn less_than_or_equal_bm(self, other: Self) -> Self {
                unimplemented!();
            }
        }
    };
}

#[macro_export]
macro_rules! _implement_numeric_signed_secret {
    ($name:ident) => {
        impl PartialOrd for $name {
            fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
                Some(self.cmp(other))
            }
        }
        impl Ord for $name {
            fn cmp(&self, other: &Self) -> Ordering {
                unimplemented!();
            }
        }
        impl Eq for $name {}

        /// **Warning**: wraps on overflow.
        impl Add for $name {
            type Output = $name;
            fn add(self, rhs: $name) -> $name {
                unimplemented!();
            }
        }

        /// **Warning**: wraps on underflow.
        impl Sub for $name {
            type Output = $name;
            fn sub(self, rhs: $name) -> $name {
                unimplemented!();
            }
        }

        /// **Warning**: wraps on overflow.
        impl Mul for $name {
            type Output = $name;
            fn mul(self, rhs: $name) -> $name {
                unimplemented!();
            }
        }

        /// **Warning**: panics on division by 0.
        impl Div for $name {
            type Output = $name;
            fn div(self, rhs: $name) -> $name {
                unimplemented!();
            }
        }

        /// **Warning**: panics on division by 0.
        impl Rem for $name {
            type Output = $name;
            fn rem(self, rhs: $name) -> $name {
                unimplemented!();
            }
        }

        impl Not for $name {
            type Output = $name;
            fn not(self) -> Self::Output {
                unimplemented!();
            }
        }

        impl BitOr for $name {
            type Output = $name;
            fn bitor(self, rhs: Self) -> Self::Output {
                unimplemented!();
            }
        }

        impl BitXor for $name {
            type Output = $name;
            fn bitxor(self, rhs: Self) -> Self::Output {
                unimplemented!();
            }
        }

        impl BitAnd for $name {
            type Output = $name;
            fn bitand(self, rhs: Self) -> Self::Output {
                unimplemented!();
            }
        }

        impl Shr<u32> for $name {
            type Output = $name;
            fn shr(self, rhs: u32) -> Self::Output {
                unimplemented!();
            }
        }

        impl Shl<u32> for $name {
            type Output = $name;
            fn shl(self, rhs: u32) -> Self::Output {
                unimplemented!();
            }
        }

        impl Numeric for $name {
            /// Return largest value that can be represented.
            fn max_val() -> Self {
                unimplemented!();
            }
        
            /// `self ^ exp` where `exp` is a `u32`.
            fn pow(self, exp: u32) -> Self {
                unimplemented!();
            }
            /// `self ^ exp` where `exp` is a `Self`.
            fn pow_self(self, exp: Self) -> Self {
                unimplemented!();
            }
            /// (self - rhs) % n.
            fn sub_mod(self, rhs: Self, n: Self) -> Self {
                unimplemented!();
            }
            /// `(self + rhs) % n`
            fn add_mod(self, rhs: Self, n: Self) -> Self {
                unimplemented!();
            }
            /// `(self * rhs) % n`
            fn mul_mod(self, rhs: Self, n: Self) -> Self {
                unimplemented!();
            }
            /// `(self ^ exp) % n`
            fn pow_mod(self, exp: Self, n: Self) -> Self {
                unimplemented!();
            }
            /// Division.
            fn div(self, rhs: Self) -> Self {
                unimplemented!();
            }
            /// `self % n`
            fn rem(self, n: Self) -> Self {
                unimplemented!();
            }
            /// Invert self modulo n.
            fn inv(self, n: Self) -> Self {
                unimplemented!();
            }
            /// `|self|`
            fn abs(self) -> Self {
                unimplemented!();
            }
        
            // Comparison functions returning bool.
            fn equal(self, other: Self) -> bool {
                unimplemented!();
            }
            fn greater_than(self, other: Self) -> bool {
                unimplemented!();
            }
            fn greater_than_or_qual(self, other: Self) -> bool {
                unimplemented!();
            }
            fn less_than(self, other: Self) -> bool {
                unimplemented!();
            }
            fn less_than_or_equal(self, other: Self) -> bool {
                unimplemented!();
            }
        
            // Comparison functions returning a bit mask (0x0..0 or 0xF..F).
            fn not_equal_bm(self, other: Self) -> Self {
                unimplemented!();
            }
            fn equal_bm(self, other: Self) -> Self {
                unimplemented!();
            }
            fn greater_than_bm(self, other: Self) -> Self {
                unimplemented!();
            }
            fn greater_than_or_qual_bm(self, other: Self) -> Self {
                unimplemented!();
            }
            fn less_than_bm(self, other: Self) -> Self {
                unimplemented!();
            }
            fn less_than_or_equal_bm(self, other: Self) -> Self {
                unimplemented!();
            }
        }
    };
}
