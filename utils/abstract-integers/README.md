This crate defines specification-friendly natural integers with an upper bound. Operations on
these integers can be defined as modular (modulo the upper bound) or regular (with a panic
on underflow or overflow).

As each integer gets its own Rust type, the compiler detects and prevent any mixing between
all the diffent integers you would have defined.

# Defining a new integer type

Here is the macro used to defined the `SizeNatExample` type of this crate:

```rust
define_abstract_integer_checked!(SizeNatExample, 64);
```

`SizeNat` is the name of the newly-created type. `64` is the number of bits of the machine
representation of the type. From the number of bits is derived an upper bound for the integer
for which all operations are checked for overflow.
The resulting integer type is copyable, and supports addition, substraction, multiplication,
integer division, remainder, comparison and equality. The `from_literal` method allows you to
convert integer literals into your new type.

# Refining an integer type for modular arithmetic

On top of a previously defined abstract integer, you can define another type that lets you
implement modular arithmetic. For instance, this crate defines the arithmetic field over the
9th Mersenne prime with:

```rust
define_refined_modular_integer!(
  SizeNatFieldExample,
  SizeNatExample,
  SizeNatExample::pow2(61) - SizeNatExample::from_literal(1)
);
```

The first argument of this new macro is the name of the newly defined refined type. The second
argument is the name of the base abstract integer that will act as the representation. The
third example is the modulo for all operations, defined as a value of the base type.
