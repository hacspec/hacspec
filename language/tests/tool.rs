use assert_cmd::prelude::*; // Add methods on commands
use std::{env, path::Path, process::Command};

mod utils;
use utils::*;

// #[test]
// fn positive_question_mark() {
//     // let mut cmd = Command::cargo_bin("cargo-hacspec").expect("Error getting cargo hacspec command");
//     let mut cmd = hacspec_extract_one_file(
//         format!("../{}", file_name),
//         PathBuf::from(file_name).file_stem().unwrap(),
//         output,
//         output_type,
//         extra_commands,
//     );
//     cmd.envs(env::vars());
//     cmd.args(&["-e", "fst"]);
//     cmd.args(&["--dir", "tests/"]);
//     cmd.args(&["-f", "language-tests/question_mark.rs"]);
//     cmd.args(&["--vc-init"]);

//     let status = cmd.status();
//     let status = status.expect("Error running typechecker");
//     assert!(status.success());

//     assert!(Path::new("tests/_vc/Question.Mark.fst").exists());

// }
