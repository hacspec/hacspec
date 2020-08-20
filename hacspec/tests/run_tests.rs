use assert_cmd::prelude::*; // Add methods on commands
use std::process::Command; // Run programs

const DEPS_ARG: &'static str = "-L ../../target/debug/deps";
const CRATE_TYPE_ARG: &'static str = "--crate-type=lib";
const EDITION_ARG: &'static str = "--edition=2018";
const EXTERN_ARG: &'static str = "--extern=hacspec_lib";

fn run_test(input: &str, output: &str) -> Result<(), Box<dyn std::error::Error>> {
    println!(
        "Running: cargo run -- {} {} {} {} -o {} {}",
        DEPS_ARG, CRATE_TYPE_ARG, EDITION_ARG, EXTERN_ARG, output, input
    );
    let mut cmd = Command::cargo_bin("hacspec")?;
    cmd.arg(DEPS_ARG);
    cmd.arg(CRATE_TYPE_ARG);
    cmd.arg(EDITION_ARG);
    cmd.arg(EXTERN_ARG);
    cmd.arg(format!("-o {}", output));
    cmd.arg(format!("{}", input));
    cmd.assert().success();
    Ok(())
}

#[test]
fn run_test1() -> Result<(), Box<dyn std::error::Error>> {
    run_test("tests/test1.rs", "tests/Test1.fst")
}

#[test]
fn run_test_chacha_simplified() -> Result<(), Box<dyn std::error::Error>> {
    run_test("tests/test_chacha.rs", "tests/TestChacha.fst")
}

#[test]
fn run_test_chacha20() -> Result<(), Box<dyn std::error::Error>> {
    run_test(
        "../spec-examples/src/chacha20_poly1305/chacha20.rs",
        "tests/Chacha20.fst",
    )
}
