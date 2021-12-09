use assert_cmd::prelude::*; // Add methods on commands
use std::collections::HashMap;
use std::{env, process::Command};

fn run_test_option(file_name: &str, output: &str) {
    let mut cmd = Command::cargo_bin("cargo-hacspec").expect("Error getting cargo hacspec command");
    cmd.envs(env::vars());
    cmd.args(&["-o", output]);
    cmd.args(&["-f", file_name]);
    println!("Running: {:?}", cmd);
    let status = cmd.status();
    println!("Result: {:?}", status);
    let status = status.expect("Error running typechecker");
    assert!(status.success());
}

fn run_tests(file_name: &str, output_name: &str, output: HashMap<&str, bool>) {
    let hacspec_targets = vec![("fstar", "tests/fstar/", ".fst"), ("coq", "tests/coq/", ".v")];

    hacspec_targets.iter().fold((), |(), (name, pre, post)| {
        if output.contains_key(name) && output[name] {
            run_test_option(file_name, (pre.to_string() + output_name + post).as_str());
        }
    });
}

#[test]
fn positive_question_mark() {
    run_tests(
        "backend-tests/question_mark.rs",
        "QuestionMark",
        HashMap::from([("fstar", true), ("coq", true)]),
    );
}

#[test]
fn positive_loops() {
    run_tests("backend-tests/loops.rs",
              "Loops",
              HashMap::from([("coq", true)]));
}

#[test]
fn positive_types() {
    run_tests("backend-tests/types.rs",
              "Types",
              HashMap::from([("coq", true)]));
}
