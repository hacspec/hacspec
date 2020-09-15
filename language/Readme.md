# The hacspec compiler

## Rust nightly

To build and run the hacspec compiler, you will need to use nightly Rust with 
additional components : 

```
rustup toolchain install nightly 
rustup component add --toolchain nightly rustc-dev
rustup component add --toolchain nightly llvm-tools-preview
```

## Usage

To build the compiler, simply launch `cargo build`.

Due to technical limitations of the exposed API of the Rust compiler and the point 
at which we divert the Rust AST into hacspec, only single-file crates are supported 
at the moment. This is why all the crates in [hacspec-examples](../hacspec-examples)
only consist of a single file.

Apart from this limitation, the hacspec compiler works as expected with imported 
crates, letting you build modular programs using several crates that depend on 
each other.

The hacspec compiler shares its CLI with the Rust compiler, so you need to pass in 
a lot of options. More importantly, because we rely on dependent crates being already
compiled (e.g. by `cargo`), you need to pass as a search folder the `target` directory
of the hacspec project you are doing.


Let us suppose that you are developping some hacspec crate in the folder `~/foo`.
Then, you should invoke the compiler from this folder ([hacspec/](./)) and this is what
your typechecking invocation should look like:

```
cargo run -- \
    -L ~/foo/target/debug/deps \
    --crate-type=lib --edition=2018 \
    --extern=hacspec_lib  \
    --extern=<name_of_dependent_crate> \
    -Zno-codegen \
    ~/foo/src/lib.rs
```

If you want to compile to F* on top of typechecking,
replace `-Zno-codegen` with `-o /path/to/Output.fst`.

This process is cumbersome and some `cargo` hacking is needed to streamline it.

## Known bugs

Because our compiler is not yet integrated into `cargo`, there will be 
weird error showing if you have different versions of your dependent crates 
already compiled in the `target/` folder. A simple `cargo clean` followed by 
`cargo build` of the hacspec project should clear the errors.

## Testing

The compiler can be tested by launching `cargo test`. It typechecks and compile to F* all 
the specs in [hacspec-examples/](hacspec-examples/).