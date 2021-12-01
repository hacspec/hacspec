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
fn positive_question_mark() {
    run_test(
        "language-tests/question_mark.rs",
        Some("tests/QuestionMark.fst"),
    );
}

#[test]
fn positive_result() {
    run_test("language-tests/result.rs", Some("tests/Result.fst"));
}

#[test]
fn positive_enums() {
    run_test("language-tests/enums.rs", Some("tests/Enums.fst"));
}

#[test]
fn positive_option() {
    run_test("language-tests/option.rs", Some("tests/Option.fst"));
}

#[test]
fn positive_arrays() {
    run_test("language-tests/arrays.rs", None);
}

#[test]
fn positive_copy() {
    run_test("language-tests/copy.rs", None);
}

#[test]
fn positive_tuples() {
    run_test("language-tests/tuples.rs", None);
}

#[test]
fn positive_loops() {
    run_test("language-tests/loops.rs", None);
}

#[test]
fn positive_expr_block() {
    run_test("language-tests/expr_block.rs", None);
}

#[test]
fn positive_seq_ops() {
    run_test("language-tests/seq_ops.rs", None);
}

#[test]
#[should_panic]
fn negative_arrays() {
    run_test("negative-language-tests/arrays.rs", None);
}
