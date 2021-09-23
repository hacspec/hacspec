# The hacspec compiler

## Rust nightly

To build and run the hacspec compiler, you will need to use nightly Rust with additional components.
This is managed by the [`rust-toolchain`](./rust-toolchain) automatically.
It picks the correct Rust nightly version and components.
Make sure you have at least `rustup 1.23.0`.
For manual installation please check the toolchain file.

## Usage

To build the compiler, simply launch `cargo build`.

Due to technical limitations of the exposed API of the Rust compiler and the point 
at which we divert the Rust AST into hacspec, only single-file crates are supported 
at the moment. This is why all the crates in [examples](../examples)
only consist of a single file.

Apart from this limitation, the hacspec compiler works as expected with imported 
crates, letting you build modular programs using several crates that depend on 
each other.

Please see the main [readme](../Readme.md) for details on usage.

## Known bugs

Because our compiler is not yet integrated into `cargo`, there will be 
weird error showing if you have different versions of your dependent crates 
already compiled in the `target/` folder. A simple `cargo clean` followed by 
`cargo build` of the hacspec project should clear the errors.

## Testing

The compiler can be tested by launching `cargo test`. It typechecks and compile to F* all 
the specs in [examples/](../examples/).

## Updating exported files
To be able to update exported files you should use the `--init` flag when you first 
build you files, this will create a `<output>_template` file with the historical view. 
Whenever you then make changes to the source and want to update the exported file with
just these changes, instead of overwriting it, you should add the `--update` flag. This
will use the git command `merge-file`, to update the file with the changes, and then 
overwrite the template file, with the new historical view.

