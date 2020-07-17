use assert_cmd::prelude::*; // Add methods on commands
use std::process::Command; // Run programs

#[test]
fn run_test1() -> Result<(), Box<dyn std::error::Error>> {
    let mut cmd = Command::cargo_bin("hacspec-lang")?;
    cmd.arg("tests/test1.rs");
    cmd.assert().success();
    Ok(())
}


#[test]
#[ignore]
fn run_test_chacha() -> Result<(), Box<dyn std::error::Error>> {
    let mut cmd = Command::cargo_bin("hacspec-lang")?;
    cmd.arg("tests/test_chacha.rs");
    cmd.assert().success();
    Ok(())
}
