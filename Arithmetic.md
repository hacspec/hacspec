# Arithmetic in hacspec

The hacpsec library offers a set of tools to perform arithmetic operations on different objects.
All objects can be either secret or public.

Any arithmetic object must implement the following trait.
Objects might leave functions unimplemented.
```Rust
pub trait Numeric:
    Add<Self, Output = Self>
    + Sub<Self, Output = Self>
    + Mul<Self, Output = Self>
    + BitXor<Self, Output = Self>
    + BitOr<Self, Output = Self>
    + BitAnd<Self, Output = Self>
    + Shl<u32, Output = Self>
    + Shr<u32, Output = Self>
    + Not
    + Default
    + Copy
    + Debug
{
    /// Return largest value that can be represented.
    fn max() -> Self;

    /// `self ^ exp` where `exp` is a `u32`.
    fn pow(self, exp: u32) -> Self;
    /// `self ^ exp` where `exp` is a `Self`.
    fn pow_self(self, exp: Self) -> Self;
    /// (self - rhs) % n.
    fn sub_mod(self, rhs: Self, n: Self) -> Self;
    /// `(self + rhs) % n`
    fn add_mod(self, rhs: Self, n: Self) -> Self;
    /// `(self * rhs) % n`
    fn mul_mod(self, rhs: Self, n: Self) -> Self;
    /// `(self ^ exp) % n`
    fn pow_mod(self, exp: Self, n: Self) -> Self;
    /// Division.
    fn div(self, rhs: Self) -> Self;
    /// `self % n`
    fn rem(self, n: Self) -> Self;
    /// Invert self modulo n.
    fn inv(self, n: Self) -> Self;
    /// `|self|`
    fn abs(self) -> Self;

    // Comparison functions returning bool.
    fn equal(self, other: Self) -> bool;
    fn greater_than(self, other: Self) -> bool;
    fn greater_than_or_qual(self, other: Self) -> bool;
    fn less_than(self, other: Self) -> bool;
    fn less_than_or_equal(self, other: Self) -> bool;

    // Comparison functions returning a bit mask (0x0..0 or 0xF..F).
    fn not_equal_bm(self, other: Self) -> Self;
    fn equal_bm(self, other: Self) -> Self;
    fn greater_than_bm(self, other: Self) -> Self;
    fn greater_than_or_qual_bm(self, other: Self) -> Self;
    fn less_than_bm(self, other: Self) -> Self;
    fn less_than_or_equal_bm(self, other: Self) -> Self;
}
```

Further, every arithmetic object must implement direct instantiation options through `From` taking `u128` or `&[u128]`.

```Rust
impl From<u128> for U128 {
    fn from(v: u128) -> Self {
        U128(v)
    }
}
impl From<u128> for MySequence {
    fn from(v: &[u128]) -> Self {
        Self::from_slice(v)
    }
}
```

## Integers

### Machine Integers
Machine integers are either the public integers `u8, i8, u16, i16, u32, i32, u64, i64, u128, i128`, or secret integers `U8, I8, U16, I16, U32, I32, U64, I64, U128, I128` that represent integers with the according number of bits.

### Integers
These integers have arbitrary, but fixed size.

 ```Rust
 // 256-bit unsigned secret integer
 unsigned_integer!(Uint256, 256);

 // 256-bit signed secret integer
 signed_integer!(Int256, 256);

 // 256-bit unsigned public integer
 unsigned_public_integer!(PUint256, 256);

 // 256-bit signed public integer
 signed_public_integer!(PInt256, 256);
 ```

#### Natural Integers Modulo n
Natural integers that wraps modulo `n`.

 ```Rust
 // Natural integers modulo 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed
 // using an underlying integer canvas `FCanvas` with 256-bits.
 nat_mod!(F25519, FCanvas, 256, "7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed");
 ```

 Public natural integers are defined by `public_nat_mod`.

## Vectors
Vectors are ordered sets of numeric values.
There are two different types.

### Pointwise Vectors
There are numeric sequences `NumSeq<T: Numeric>` and numeric arrays `num_array!(MyArray, <length>, <NumericType>)` that implement pointwise numeric arithmetic for the `Numeric` trait.

### Polynomials
Polynomials are special numeric arrays that implement polynomial arithmetic over the array `poly!(MyPoly, <NumericType>, <length>, <Modulus Option>, <Irreducible Option>);`.
The last two arguments are option types.
If the polynomial is defined over ℤn, the modulus `n` is given as `Some(n)`, `None` otherwise.
If the polynomial is defined over ℤn/mℤ, the irreducible `irr` is given as `Some(irr)`, `None` otherwise.
