use assert_cmd::prelude::*; // Add methods on commands
use itertools::Itertools;
use std::process::Command; // Run programs

fn run_test(
    input: &str,
    output: Option<&str>,
    dependencies: Vec<&str>,
) -> Result<(), Box<dyn std::error::Error>> {
    println!(
        "Running: cargo run -- {} {} {}",
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
    let mut cmd = Command::cargo_bin("cargo-hacspec")?;
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

#[test]
fn run_sha256_test() -> Result<(), Box<dyn std::error::Error>> {
    run_test("../examples/hacspec-sha256/src/sha256.rs", None, vec![])
}

#[test]
fn run_curve25519_test() -> Result<(), Box<dyn std::error::Error>> {
    run_test("../examples/hacspec-curve25519/src/curve25519.rs", None, vec![])
}
