pub(crate) const APP_USAGE: &'static str = "hacspec 0.1.0
hacspec Developers
Typechecker and compiler for the hacspec subset of Rust

USAGE:
    cargo hacspec [FLAGS] [OPTIONS] [CRATE]

FLAGS:
    -v               Verbosity
    --manifest-path  The cargo manifest path argument. The typechecker will analyze
                     the crate or workspace at the specified Cargo.toml.
                     Note that you have to specify the path including the Cargo.toml
                     file!

OPTIONS:
    -o <FILE_DIR>    The output directory (needed for output)
    -e <FILE_EXT>    File extension F* (fst), Easycrypt (ec), (json), or Coq (v)

ARGS:
    CRATE            The crate to analyse.
                     The crate name is required if there are multiple crates in the
                     workspace. If only one crate is present, the argument can be
                     omitted.
";

#[allow(dead_code)]
pub(crate) fn check_vec<T>(v: Vec<Result<T, ()>>) -> Result<Vec<T>, ()> {
    if v.iter().all(|t| t.is_ok()) {
        Ok(v.into_iter().map(|t| t.unwrap()).collect())
    } else {
        Err(())
    }
}
