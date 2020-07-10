use assert_cmd::prelude::*; // Add methods on commands
use std::process::Command; // Run programs
use std::str::from_utf8;

#[test]
fn run_test1() -> Result<(), Box<dyn std::error::Error>> {
    let mut cmd = Command::cargo_bin("hacspec-lang")?;

    println!("==> Running test1.rs");
    cmd.arg("tests/test1.rs");
    let assertion = cmd.assert();
    let output =
        assertion.get_output();
    println!("==> Command output stdout:\n{}",from_utf8(&output.stdout).unwrap());
    println!("==> Command output sterr:\n{}",from_utf8(&output.stderr).unwrap());
    Ok(())
}
