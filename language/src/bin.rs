mod util;
use util::APP_USAGE;

use std::{collections::HashMap, env, path::PathBuf};

fn driver() -> PathBuf {
    let mut driver = env::current_exe()
        .expect("invalid path for cargo hacspec")
        .with_file_name("hacspec-driver");

    if cfg!(windows) {
        driver.set_extension("exe");
    }

    driver
}

fn main() {
    let mut sysroot = std::process::Command::new("rustc")
        .arg("--print")
        .arg("sysroot")
        .output()
        .ok()
        .and_then(|out| String::from_utf8(out.stdout).ok())
        .expect("Couldn't get sysroot");
    sysroot.pop(); // get rid of line break
    let sysroot_lib = sysroot.clone() + "/lib";

    let library_path_variable = if cfg!(target_os = "linux") {
        "LD_LIBRARY_PATH"
    } else if cfg!(target_os = "macos") {
        "DYLD_LIBRARY_PATH"
    } else if cfg!(target_os = "windows") {
        "PATH"
    } else {
        panic!("Unsupported target OS: {}", cfg!(target_os))
    };

    let mut args: Vec<String> = env::args().skip(1).collect();

    if !args.is_empty() && args[0] == "hacspec" {
        args.remove(0);
    };

    if let Some(arg0) = args.get(0) {
        if arg0 == "--help" || arg0 == "-h" {
            println!("{}", APP_USAGE);
            std::process::exit(1);
        }
    }

    let environment: HashMap<String, String> = env::vars().collect();

    let hacspec_out = std::process::Command::new(driver())
        .env(library_path_variable, sysroot_lib)
        .envs(&environment)
        .arg(format!("--sysroot={}", sysroot))
        .args(args)
        .status()
        .expect("Couldn't run hacspec");

    std::process::exit(hacspec_out.code().unwrap());
}
