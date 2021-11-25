use assert_cmd::prelude::*; // Add methods on commands
use std::collections::HashMap;
use std::{env, process::Command};

fn run_test_option(file_name: &str, output: Option<&str>) {
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

fn run_test(file_name: &str) {
    run_test_option(file_name, None);
}

fn run_test_with_output(file_name: &str, output: &str) {
    run_test_option(file_name, Some(output));
}

fn run_tests(file_name: &str, output_name: &str, output: HashMap<&str, bool>) {
    let hacspec_targets = vec![("fstar", "tests/", ".fst"), ("coq", "tests/coq/", ".v")];

    hacspec_targets.iter().fold((), |(), (name, pre, post)| {
        if output.contains_key(name) && output[name] {
            run_test_with_output(file_name, (pre.to_string() + output_name + post).as_str());
        }
    });
}

#[test]
fn positive_question_mark() {
    run_tests(
        "language-tests/question_mark.rs",
        "QuestionMark",
        HashMap::from([("fstar", true), ("coq", true)]),
    );
}

#[test]
fn positive_result() {
    run_tests(
        "language-tests/result.rs",
        "Result",
        HashMap::from([("fstar", true), ("coq", true)]),
    );
}

#[test]
fn positive_enums() {
    run_tests(
        "language-tests/enums.rs",
        "Enums",
        HashMap::from([("fstar", true), ("coq", true)]),
    );
}

#[test]
fn positive_option() {
    run_tests(
        "language-tests/option.rs",
        "Option",
        HashMap::from([("fstar", true), ("coq", true)]),
    );
}

#[test]
fn positive_arrays() {
    run_test("language-tests/arrays.rs");
}

#[test]
fn positive_copy() {
    run_test("language-tests/copy.rs");
}

#[test]
fn positive_tuples() {
    run_test("language-tests/tuples.rs");
}

#[test]
fn positive_loops() {
    run_tests("language-tests/loops.rs",
              "Loops",
              HashMap::from([("coq", true)]));
}

#[test]
fn positive_expr_block() {
    run_test("language-tests/expr_block.rs");
}

#[test]
fn positive_seq_ops() {
    run_test("language-tests/seq_ops.rs");
}

#[test]
#[should_panic]
fn negative_arrays() {
    run_test("negative-language-tests/arrays.rs");
}
