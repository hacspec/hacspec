use assert_cmd::prelude::*; // Add methods on commands
use std::{env, process::Command};

fn run_test(file_name: &str, output: Option<&str>) {
    let mut cmd = Command::cargo_bin("cargo-hacspec").expect("Error getting cargo hacspec command");
    cmd.envs(env::vars());
    if let Some(f) = output {
        cmd.args(&["-o", f]);
    }
    cmd.args(&["-f", file_name]);
    println!("Running: {:?}", cmd);
    let status = cmd.status();
    println!("Result: {:?}", status);
    let status = status.expect("Error running typechecker");
    assert!(status.success());
}

#[test]
fn positive() {
    run_test("language-tests/arrays.rs", None);
}

#[test]
#[should_panic]
fn negative() {
    run_test("negative-language-tests/arrays.rs", None);
}
