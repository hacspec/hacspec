use std::{env, process::Command};

#[test]
fn run_coq_backend() {
    let mut cmd = Command::new("make");
    cmd.current_dir("./tests/coq/");
    cmd.envs(env::vars());
    let status = cmd.status();
    let status = status.expect("Error running coq backend");
    assert!(status.success());
}
