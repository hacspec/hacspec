use assert_cmd::prelude::*; // Add methods on commands
use std::{env, process::Command, path::Path};

#[test]
fn positive_question_mark() {
    let mut cmd = Command::cargo_bin("cargo-hacspec").expect("Error getting cargo hacspec command");
    cmd.envs(env::vars());
    cmd.args(&["-e", "fst"]);
    cmd.args(&["--dir", "tests/"]);
    cmd.args(&["-f", "language-tests/question_mark.rs"]);
    cmd.args(&["--vc-init"]);

    let status = cmd.status();
    let status = status.expect("Error running typechecker");
    assert!(status.success());

    assert!(Path::new("tests/_vc/Question.Mark.fst").exists());
    
}
