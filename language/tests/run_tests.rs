use assert_cmd::prelude::*; // Add methods on commands
use std::{env, process::Command}; // Run programs

fn run_test(package_name: &str, output: Option<&str>) -> Result<(), Box<dyn std::error::Error>> {
    let mut cmd = Command::cargo_bin("cargo-hacspec")?;
    cmd.envs(env::vars());
    if let Some(f) = output {
        cmd.arg(format!("-o {}", f));
    }
    cmd.arg(format!("{}", package_name));
    println!("Running: {:?}", cmd);
    cmd.assert().success();
    Ok(())
}

#[test]
fn run_chacha20_test() -> Result<(), Box<dyn std::error::Error>> {
    run_test("hacspec-chacha20", Some("../fstar/Hacspec.Chacha20.fst"))?;
    run_test("hacspec-chacha20", Some("../easycrypt/Hacspec_Chacha20.ec"))
}

#[test]
fn run_poly1305_test() -> Result<(), Box<dyn std::error::Error>> {
    run_test("hacspec-poly1305", Some("../fstar/Hacspec.Poly1305.fst"))?;
    run_test("hacspec-poly1305", Some("../easycrypt/Hacspec_Poly1305.ec"))
}

#[test]
fn run_chacha20poly1305_test() -> Result<(), Box<dyn std::error::Error>> {
    run_test(
        "hacspec-chacha20poly1305",
        Some("../fstar/Hacspec.Chacha20Poly1305.fst"),
    )
}

#[test]
fn run_ntru_prime_test() -> Result<(), Box<dyn std::error::Error>> {
    run_test("hacspec-ntru-prime", None)
}

#[test]
fn run_sha3_test() -> Result<(), Box<dyn std::error::Error>> {
    run_test("hacspec-sha3", None)
}

#[test]
fn run_sha256_test() -> Result<(), Box<dyn std::error::Error>> {
    run_test("hacspec-sha256", None)
}

#[test]
fn run_p256_test() -> Result<(), Box<dyn std::error::Error>> {
    run_test("hacspec-p256", None)
}

#[test]
fn run_curve25519_test() -> Result<(), Box<dyn std::error::Error>> {
    run_test("hacspec-curve25519", None)
}

#[test]
fn run_riot_test() -> Result<(), Box<dyn std::error::Error>> {
    run_test("hacspec-riot-bootloader", Some("../fstar/Hacspec.Riot.fst"))
}

#[test]
fn run_hmac_test() -> Result<(), Box<dyn std::error::Error>> {
    run_test("hacspec-hmac", Some("../fstar/Hacspec.Hmac.fst"))
}

#[test]
fn run_hkdf_test() -> Result<(), Box<dyn std::error::Error>> {
    run_test("hacspec-hkdf", Some("../fstar/Hacspec.Hkdf.fst"))
}

#[test]
fn run_bls12_381_test() -> Result<(), Box<dyn std::error::Error>> {
    run_test("hacspec-bls12-381", None)
}
