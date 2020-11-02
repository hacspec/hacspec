use assert_cmd::prelude::*; // Add methods on commands
use itertools::Itertools;
use std::process::Command; // Run programs

const DEPS_ARG: &'static str = "-L ../../target/debug/deps";
const CRATE_TYPE_ARG: &'static str = "--crate-type=lib";
const EDITION_ARG: &'static str = "--edition=2018";
const EXTERN_ARG: &'static str = "--extern=hacspec_lib";

fn run_test(
    input: &str,
    output: Option<&str>,
    dependencies: Vec<&str>,
) -> Result<(), Box<dyn std::error::Error>> {
    println!(
        "Running: cargo run -- {} {} {} {} {} {} {}",
        DEPS_ARG,
        CRATE_TYPE_ARG,
        EDITION_ARG,
        EXTERN_ARG,
        dependencies
            .iter()
            .map(|d| format!("--extern={}", d))
            .format(" "),
        match output {
            None => "-Zno-codegen".to_string(),
            Some(f) => format!("-o {}", f),
        },
        input
    );
    let mut cmd = Command::cargo_bin("hacspec")?;
    cmd.arg(DEPS_ARG);
    cmd.arg(CRATE_TYPE_ARG);
    cmd.arg(EDITION_ARG);
    cmd.arg(EXTERN_ARG);
    dependencies.iter().for_each(|d| {
        cmd.arg(format!("--extern={}", d));
    });
    match output {
        None => cmd.arg("-Zno-codegen".to_string()),
        Some(f) => cmd.arg(format!("-o {}", f)),
    };
    cmd.arg(format!("{}", input));
    cmd.assert().success();
    Ok(())
}

#[test]
fn run_simple_test() -> Result<(), Box<dyn std::error::Error>> {
    run_test("tests/test1.rs", Some("tests/Test1.fst"), vec![])
}

#[test]
fn run_chacha_simplified_test() -> Result<(), Box<dyn std::error::Error>> {
    run_test("tests/test_chacha.rs", Some("tests/TestChacha.fst"), vec![])
}

#[test]
fn run_chacha20_test() -> Result<(), Box<dyn std::error::Error>> {
    run_test(
        "../examples/hacspec-chacha20/src/chacha20.rs",
        Some("../fstar/Hacspec.Chacha20.fst"),
        vec![],
    )?;
    run_test(
        "../examples/hacspec-chacha20/src/chacha20.rs",
        Some("../easycrypt/Hacspec_Chacha20.ec"),
        vec![],
    )
}

#[test]
fn run_poly1305_test() -> Result<(), Box<dyn std::error::Error>> {
    run_test(
        "../examples/hacspec-poly1305/src/poly1305.rs",
        Some("../fstar/Hacspec.Poly1305.fst"),
        vec![""],
    )?;
    run_test(
        "../examples/hacspec-poly1305/src/poly1305.rs",
        Some("../easycrypt/Hacspec_Poly1305.ec"),
        vec![""],
    )
}

#[test]
fn run_chacha20poly1305_test() -> Result<(), Box<dyn std::error::Error>> {
    run_test(
        "../examples/hacspec-chacha20poly1305/src/chacha20poly1305.rs",
        Some("../fstar/Hacspec.Chacha20Poly1305.fst"),
        vec!["hacspec_chacha20", "hacspec_poly1305"],
    )
}

#[test]
fn run_ntru_prime_test() -> Result<(), Box<dyn std::error::Error>> {
    run_test(
        "../examples/hacspec-ntru-prime/src/ntru-prime.rs",
        None,
        vec![],
    )
}

#[test]
fn run_sha3_test() -> Result<(), Box<dyn std::error::Error>> {
    run_test("../examples/hacspec-sha3/src/sha3.rs", None, vec![])
}
