pub(crate) const APP_USAGE: &'static str = "Hacspec 0.1.0
Hacspec Developers
Typechecker and compiler for the Hacspec subset of Rust

USAGE:
    cargo hacspec [FLAGS] [OPTIONS] <CRATE>

FLAGS:
    -v               Verbosity
    --init           Creates a '<output>_template' file along with the output
    --update         Merges changes into output file based on the template file

OPTIONS:
    -o <FILE>        Name of the F* (.fst), Easycrypt (.ec), or Coq (.v) output file

ARGS:
    CRATE            The crate to analyse
";

#[allow(dead_code)]
pub(crate) fn check_vec<T>(v: Vec<Result<T, ()>>) -> Result<Vec<T>, ()> {
    if v.iter().all(|t| t.is_ok()) {
        Ok(v.into_iter().map(|t| t.unwrap()).collect())
    } else {
        Err(())
    }
}
