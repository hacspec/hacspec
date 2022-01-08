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

    let file_paths = match args.iter().position(|a| a == "-o") {
        Some(j) => match args.get(j + 1).cloned() {
            Some(file) => {
                let file_parent = std::path::Path::new(&file).parent().unwrap();
                let file_stem = std::path::Path::new(&file).file_stem().unwrap();
                let file_extension = std::path::Path::new(&file)
                    .extension()
                    .and_then(std::ffi::OsStr::to_str)
                    .unwrap();

                let file_prefix = file_parent.join(file_stem);
                let file_prefix = file_prefix.to_str().unwrap();

                let template_path = file_prefix.to_string() + "_template." + file_extension;
                let temp_path = file_prefix.to_string() + "_temp." + file_extension;

                match args.iter().position(|a| a == "--init") {
                    Some(i) => {
                        args.remove(i);
                        Some((file, temp_path, template_path, true))
                    }
                    None => match args.iter().position(|a| a == "--update") {
                        Some(i) => {
                            args.remove(i);
                            args.remove(j + 1);
                            args.insert(j + 1, temp_path.clone());
                            Some((file, temp_path, template_path, false))
                        }
                        None => None,
                    },
                }
            }
            None => None,
        },
        None => None,
    };

    let hacspec_out = std::process::Command::new(driver())
        .env(library_path_variable, sysroot_lib)
        .envs(&environment)
        .arg(format!("--sysroot={}", sysroot))
        .args(args)
        .status()
        .expect("Couldn't run hacspec");

    match file_paths {
        Some((file, _, template, true)) => {
            std::fs::copy(file.clone(), template.clone()).expect(
                format!(
                    "Failed to copy file '{}' to '{}'",
                    file.clone(),
                    template.clone()
                )
                .as_str(),
            );
            ()
        }
        Some((file, temp, template, false)) => {
            std::process::Command::new("git")
                .output()
                .expect("Could not find 'git'. Please install git and try again.");
            std::process::Command::new("git")
                .arg("merge-file")
                .arg(file.clone())
                .arg(template.clone())
                .arg(temp.clone())
                .output()
                .expect("git-merge failed");
            std::fs::copy(temp.clone(), template.clone()).expect(
                format!(
                    "Failed to copy file '{}' to '{}'",
                    temp.clone(),
                    template.clone()
                )
                .as_str(),
            );
            std::fs::remove_file(temp.clone())
                .expect(format!("Failed to remove file '{}'", file.clone()).as_str());
            ()
        }
        None => (),
    };

    std::process::exit(hacspec_out.code().unwrap());
}
