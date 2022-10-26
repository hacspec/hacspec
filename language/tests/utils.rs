use assert_cmd::cargo::cargo_bin;
use itertools::Itertools;
use std::ffi::OsStr;
use std::path::PathBuf;
use std::{env, process::Command};

pub const TEST_DIRECTORY: &str = "language-tests";

pub fn lookup_binary_directory(name: &str) -> String {
    cargo_bin(name)
        .parent()
        .and_then(|p| p.to_str().map(|s| s.to_string()))
        .expect(&*format!("error looking up path of `{}` binary", name))
}

pub fn cargo_manifest_dir() -> String {
    std::env::var("CARGO_MANIFEST_DIR")
        .expect("Could not read environment variable `CARGO_MANIFEST_DIR`")
}

pub fn cargo_toml_path() -> String {
    PathBuf::from(cargo_manifest_dir())
        .join(TEST_DIRECTORY)
        .join("Cargo.toml")
        .to_str()
        .expect("Bad UTF8 in path")
        .to_string()
}

pub fn hacspec_command<'a>() -> Command {
    fn non_empty(s: &String) -> bool {
        !s.is_empty()
    }
    let mut cmd = Command::new("cargo");
    let paths = vec![
        lookup_binary_directory("cargo-hacspec"),
        lookup_binary_directory("hacspec-driver"),
        std::env::var("PATH").unwrap_or("".to_string()),
    ];
    let paths: Vec<_> = paths.into_iter().filter(non_empty).unique().collect();
    cmd.env_clear()
        .envs(env::vars())
        .env_remove("PATH")
        .env("PATH", paths.join(":"))
        .arg("hacspec");
    cmd
}

pub fn hacspec_extract_one_file<IF: AsRef<OsStr>, OF: AsRef<OsStr>, D: AsRef<OsStr>>(
    input_filename: IF,
    output_filename: OF,
    output_dir: D,
    extension: &str,
    extra_commands: &Option<Vec<(&str, &str)>>,
) -> Command {
    let mut cmd = hacspec_command();
    cmd.arg("--input-filename")
        .arg(input_filename)
        .args(["-e", extension])
        .arg("--dir")
        .arg(output_dir)
        .arg("--output-filename")
        .arg(output_filename)
        .args(["--", "--manifest-path", &*cargo_toml_path()]);
    // .args(extra_commands.into_iter().flatten());
    cmd
}

pub fn hacspec_test_one_file<IF: AsRef<OsStr>>(input_filename: IF) -> Command {
    let mut cmd = hacspec_command();
    cmd.arg("--input-filename").arg(input_filename).args([
        "--",
        "--manifest-path",
        &*cargo_toml_path(),
    ]);
    cmd
}
