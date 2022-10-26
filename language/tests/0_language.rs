use assert_cmd::prelude::*; // Add methods on commands
use itertools::Itertools;
use std::{env, process::Command};

// use assert_cmd::cargo::cargo_bin;
// enum Backend {
//     FStar,
//     Coq,
//     EasyCrypt,
// }

// impl Backend {
//     fn ext(&self) -> &str {
//         match self {
//             FStar => "fst",
//             Coq => "v",
//             EasyCrypt => "ec",
//         }
//     }
// }

// const OUTPUT_DIR: &str = "tests/";

// fn lookup_binary_directory(name: &str) -> String {
//     cargo_bin(name)
//         .parent()
//         .and_then(|p| p.to_str().map(|s| s.to_string()))
//         .expect(&*format!("error looking up path of `{}` binary", name))
// }

// fn hacspec_command<'a>() -> Command {
//     fn non_empty(s: &String) -> bool {
//         !s.is_empty()
//     }
//     let mut cmd = Command::new("cargo");
//     let paths = vec![
//         lookup_binary_directory("cargo-hacspec"),
//         lookup_binary_directory("hacspec-driver"),
//         std::env::var("PATH").unwrap_or("".to_string()),
//     ];
//     let paths: Vec<_> = paths.into_iter().filter(non_empty).unique().collect();
//     cmd.env_clear()
//         .envs(env::vars())
//         .env_remove("PATH")
//         .env("PATH", paths.join(":"))
//         .arg("hacspec");
//     cmd
// }

// fn hacspec(opts: hacspec::HacspecArgs) {
//     let mut cmd = hacspec_command();
//     cmd.args(opts.to_args());
//     println!("Running: {:?}", cmd);
//     let status = cmd.status();
//     println!("Result: {:?}", status);
//     let status = status.expect("Error running typechecker");
//     assert!(status.success());
// }

// fn with_filename(input_filename: String) -> hacspec::HacspecArgs {
//     hacspec::HacspecArgs {
//         input_filename: Some(input_filename),
//         cargo_extra_flags: vec![
//             "--manifest-path".to_string(),
//             "language-tests/Cargo.toml".to_string(),
//         ],
//         ..Default::default()
//     }
// }

// macro_rules! make_tests_aux {
//     (
//         {$($positives: tt)*},
//         {$($negatives: tt)*},
//     ) => {
//         pub mod positive {
//             use super::*;
//             $($positives)*
//         }
//         pub mod negative {
//             use super::*;
//             $($negatives)*
//         }
//     };
//     ({$($positives: tt)*}, $negatives: tt, positive $filename:ident$(,)? $($rest:tt)*) => {
//         make_tests_aux!(
//             {
//                 $($positives)*
//                 #[test]
//                 pub fn $filename() {
//                     hacspec(with_filename(format!("positive/{}.rs", stringify!($filename))));
//                 }
//             },
//             $negatives,
//             $($rest)*
//         );
//     };
//     ($positives:tt, {$($negatives: tt)*}, negative $filename:ident$(,)? $($rest:tt)*) => {
//         make_tests_aux!(
//             $positives,
//             {
//                 $(negatives)*
//                 #[test]
//                 #[should_panic]
//                 pub fn $filename() {
//                     hacspec(with_filename(format!("negative/{}.rs", stringify!($filename))));
//                 }
//             },
//             $($rest)*
//         );
//     }
// }

// // macro_rules! make_tests {
// //     ($($rest:tt)*) => {
// //         make_tests_aux!({}, {}, $($rest)*);
// //     }
// // }

// // make_tests!(
// //     positive enums,
// // );

// pub mod positive {
//     use super::*;
//     #[test]
//     pub fn enums() {
//         hacspec(with_filename("positive/enums.rs".into()));
//     }
// }

// // // #[test]
// // // fn positive_option() {
// // //     run_test("src/option.rs", Some("tests/"));
// // // }

// // // #[test]
// // // fn positive_arrays() {
// // //     run_test("src/arrays.rs", None);
// // // }

// // // #[test]
// // // fn positive_copy() {
// // //     run_test("src/copy.rs", None);
// // // }

// // // #[test]
// // // fn positive_tuples() {
// // //     run_test("src/tuples.rs", None);
// // // }

// // // #[test]
// // // fn positive_loops() {
// // //     run_test("src/loops.rs", None);
// // // }

// // // #[test]
// // // fn positive_expr_block() {
// // //     run_test("src/expr_block.rs", None);
// // // }

// // // #[test]
// // // fn positive_seq_ops() {
// // //     run_test("src/seq_ops.rs", None);
// // // }

// // // #[test]
// // // #[should_panic]
// // // fn negative_arrays() {
// // //     run_test("../negative-language-tests/arrays.rs", None);
// // // }

// // // fn run_crate_test(crate_dir: &str, output: Option<&str>) {
// // //     let mut cmd = Command::cargo_bin("cargo-hacspec").expect("Error getting cargo hacspec command");
// // //     cmd.envs(env::vars());
// // //     if let Some(f) = output {
// // //         cmd.args(&["-e", "fst"]);
// // //         cmd.args(&["--dir", f]);
// // //     }
// // //     cmd.current_dir(crate_dir);
// // //     println!("Running: {:?}", cmd);
// // //     let status = cmd.status();
// // //     println!("Result: {:?}", status);
// // //     let status = status.expect("Error running typechecker");
// // //     assert!(status.success());
// // // }

// // // #[test]
// // // fn positive_crate_structure() {
// // //     run_crate_test("test-crate", None);
// // // }
