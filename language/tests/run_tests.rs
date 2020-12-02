use assert_cmd::prelude::*; // Add methods on commands
use std::{env, process::Command}; // Run programs

fn run_test(
    package_name: &str,
    output: Option<&str>,
    dependencies: Vec<&str>,
) -> Result<(), Box<dyn std::error::Error>> {
    let mut sysroot = std::process::Command::new("rustc")
        .arg("--print")
        .arg("sysroot")
        .output()
        .ok()
        .and_then(|out| String::from_utf8(out.stdout).ok())
        .expect("Couldn't get sysroot");
    sysroot.pop(); // get rid of line break

    let mut cmd = Command::cargo_bin("hacspec-driver")?;
    cmd.arg(format!("--sysroot={}", sysroot));
    cmd.args(env::args().skip(1));
    cmd.envs(env::vars());
    dependencies.iter().for_each(|d| {
        cmd.arg(format!("--extern={}", d));
    });
    match output {
        None => cmd.arg("-Zno-codegen".to_string()),
        Some(f) => cmd.arg(format!("-o {}", f)),
    };
    cmd.arg(format!("{}", package_name));
    println!("Running: {:?}", cmd);
    cmd.assert().success();
    Ok(())
}

#[test]
fn run_chacha20_test() -> Result<(), Box<dyn std::error::Error>> {
    run_test(
        "hacspec-chacha20",
        Some("../fstar/Hacspec.Chacha20.fst"),
        vec![],
    )?;
    run_test(
        "hacspec-chacha20",
        Some("../easycrypt/Hacspec_Chacha20.ec"),
        vec![],
    )
}

#[test]
fn run_poly1305_test() -> Result<(), Box<dyn std::error::Error>> {
    run_test(
        "hacspec-poly1305",
        Some("../fstar/Hacspec.Poly1305.fst"),
        vec![""],
    )?;
    run_test(
        "hacspec-poly1305",
        Some("../easycrypt/Hacspec_Poly1305.ec"),
        vec![""],
    )
}

#[test]
fn run_chacha20poly1305_test() -> Result<(), Box<dyn std::error::Error>> {
    run_test(
        "hacspec-chacha20poly1305",
        Some("../fstar/Hacspec.Chacha20Poly1305.fst"),
        vec!["hacspec_chacha20", "hacspec_poly1305"],
    )
}

#[test]
fn run_ntru_prime_test() -> Result<(), Box<dyn std::error::Error>> {
    run_test("hacspec-ntru-prime", None, vec![])
}

#[test]
fn run_sha3_test() -> Result<(), Box<dyn std::error::Error>> {
    run_test("hacspec-sha3", None, vec![])
}

#[test]
fn run_sha256_test() -> Result<(), Box<dyn std::error::Error>> {
    run_test("hacspec-sha256", None, vec![])
}

#[test]
fn run_curve25519_test() -> Result<(), Box<dyn std::error::Error>> {
    run_test("hacspec-curve25519", None, vec![])
}
