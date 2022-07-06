use assert_cmd::prelude::*; // Add methods on commands
use std::collections::HashMap;
use std::{env, process::Command};

fn run_test_option(
    file_name: &str,
    output: &str,
    output_type: &str,
    extra_commands: &Option<Vec<(&str, &str)>>,
) {
    let mut cmd = Command::cargo_bin("cargo-hacspec").expect("Error getting cargo hacspec command");
    cmd.envs(env::vars());
    cmd.args(&["--dir", output]);
    cmd.args(&["-e", output_type]);
    cmd.args(&["-f", file_name]);
    if let Some(v) = extra_commands {
        for (a, e) in v {
            cmd.args(&[a, e]);
        }
    }
    println!("Running: {:?}", cmd);
    let status = cmd.status();
    println!("Result: {:?}", status);
    let status = status.expect("Error running typechecker");
    assert!(status.success());
}

fn run_tests(
    file_name: &str,
    output: HashMap<&str, bool>,
    extra_commands: &Option<Vec<(&str, &str)>>,
) {
    let hacspec_targets = vec![("fstar", "tests/fstar/", "fst"), ("coq", "tests/coq/", "v")];

    hacspec_targets.iter().fold((), |(), (name, pre, post)| {
        if output.contains_key(name) && output[name] {
            run_test_option(file_name, pre, post, extra_commands);
        }
    });
}

#[test]
fn positive_question_mark() {
    run_tests(
        "backend-tests/question_mark.rs",
        HashMap::from([("fstar", true), ("coq", true)]),
        &None,
    );
}

#[test]
fn positive_version_control() {
    println!("VC init");
    run_tests(
        "backend-tests/question_mark.rs",
        HashMap::from([("fstar", true), ("coq", true)]),
        &Some(vec![("--vc-init", "")]),
    );
    
    println!("VC update");
    run_tests(
        "backend-tests/question_mark.rs",
        HashMap::from([("fstar", true), ("coq", true)]),
        &Some(vec![("--vc-update", "")]),
    );
}

#[test]
fn positive_loops() {
    run_tests(
        "backend-tests/loops.rs",
        HashMap::from([("coq", true)]),
        &None,
    );
}

#[test]
fn positive_types() {
    run_tests(
        "backend-tests/types.rs",
        HashMap::from([("coq", true)]),
        &None,
    );
}
