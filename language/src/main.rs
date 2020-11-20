#![feature(rustc_private)]
extern crate rustc_ast;
extern crate rustc_driver;
extern crate rustc_errors;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_metadata;
extern crate rustc_middle;
extern crate rustc_session;
extern crate rustc_span;
#[macro_use]
extern crate clap;
extern crate im;
extern crate pretty;

mod ast_to_rustspec;
mod hir_to_rustspec;
mod rustspec;
mod rustspec_to_easycrypt;
mod rustspec_to_fstar;
mod typechecker;

use clap::App;
use hacspec_sig::Signature;
use rustc_driver::{Callbacks, Compilation, RunCompiler};
use rustc_errors::emitter::{ColorConfig, HumanReadableErrorType};
use rustc_errors::DiagnosticId;
use rustc_interface::{
    interface::{Compiler, Config},
    Queries,
};
use rustc_session::Session;
use rustc_session::{config::ErrorOutputType, search_paths::SearchPath};
use rustc_span::MultiSpan;
use serde::Deserialize;
use serde_json;
use std::collections::{HashMap, HashSet};
use std::env;
use std::ffi::OsStr;
use std::fs::OpenOptions;
use std::path::Path;
use walkdir::WalkDir;

struct HacspecCallbacks {
    output_file: Option<String>,
    typecheck_only: bool,
}

const ITEM_LIST_LOCATION: &'static str = "/tmp/allowed_item_list.json";

const ERROR_OUTPUT_CONFIG: ErrorOutputType =
    ErrorOutputType::HumanReadable(HumanReadableErrorType::Default(ColorConfig::Auto));

trait HacspecErrorEmitter {
    fn span_rustspec_err<S: Into<MultiSpan>>(&self, s: S, msg: &str);
}

impl HacspecErrorEmitter for Session {
    fn span_rustspec_err<S: Into<MultiSpan>>(&self, s: S, msg: &str) {
        self.span_err_with_code(s, msg, DiagnosticId::Error(String::from("Hacspec")));
    }
}

impl Callbacks for HacspecCallbacks {
    fn config(&mut self, config: &mut Config) {
        let libraries_string = if cfg!(target_os = "linux") {
            option_env!("LD_LIBRARY_PATH")
        } else if cfg!(target_os = "macos") {
            option_env!("DYLD_FALLBACK_LIBRARY_PATH")
        } else if cfg!(target_os = "windows") {
            option_env!("PATH")
        } else {
            panic!("Unsupported target OS: {}", cfg!(target_os))
        };
        println!(" >>> shared libs: {:?}", libraries_string);
        let shared_libraries = libraries_string.unwrap_or("").trim().split(":");
        for shared_library in shared_libraries {
            if shared_library != "" {
                config.opts.search_paths.push(SearchPath::from_cli_opt(
                    shared_library,
                    ERROR_OUTPUT_CONFIG,
                ));
                for entry in WalkDir::new(shared_library) {
                    let entry = match entry {
                        Ok(e) => e,
                        Err(_) => continue,
                    };
                    if entry.metadata().unwrap().is_dir() {
                        config.opts.search_paths.push(SearchPath::from_cli_opt(
                            entry.path().to_str().unwrap(),
                            ERROR_OUTPUT_CONFIG,
                        ));
                    }
                }
            }
        }
        config.crate_cfg.insert((
            String::from("feature"),
            Some(String::from("\"hacspec_attributes\"")),
        ));
    }

    fn after_analysis<'tcx>(
        &mut self,
        compiler: &Compiler,
        queries: &'tcx Queries<'tcx>,
    ) -> Compilation {
        let krate = queries.parse().unwrap().take();
        let krate = match ast_to_rustspec::translate(&compiler.session(), &krate) {
            Ok(krate) => krate,
            Err(_) => {
                &compiler
                    .session()
                    .err("unable to translate to Hacspec due to out-of-language errors");
                return Compilation::Stop;
            }
        };
        let file = OpenOptions::new()
            .read(true)
            .open(ITEM_LIST_LOCATION)
            .unwrap();
        let key_s = String::from("primitive");
        let crate_s = String::from("hacspec");
        let item_list: HashMap<String, HashMap<String, HashSet<Signature>>> =
            serde_json::from_reader(&file).unwrap_or(HashMap::new());
        let empty_set = &HashSet::new();
        let empty_map = &HashMap::new();
        let hacspec_items = item_list
            .get(&key_s)
            .unwrap_or(empty_map)
            .get(&crate_s)
            .unwrap_or(empty_set);
        let external_funcs = |imported_crates: &Vec<rustspec::Spanned<String>>| {
            queries.global_ctxt().unwrap().peek_mut().enter(|tcx| {
                hir_to_rustspec::retrieve_external_functions(
                    &compiler.session(),
                    &tcx,
                    imported_crates,
                )
            })
        };
        let (krate, typ_dict) = match typechecker::typecheck_program(
            &compiler.session(),
            &krate,
            &external_funcs,
            hacspec_items,
        ) {
            Ok(krate) => krate,
            Err(_) => {
                &compiler
                    .session()
                    .err("found some Hacspec typechecking errors");
                return Compilation::Stop;
            }
        };
        if self.typecheck_only {
            return Compilation::Stop;
        }
        match &self.output_file {
            None => (),
            Some(file) => match Path::new(file).extension().and_then(OsStr::to_str).unwrap() {
                "fst" => rustspec_to_fstar::translate_and_write_to_file(
                    &compiler.session(),
                    &krate,
                    &file,
                    &typ_dict,
                ),
                "ec" => rustspec_to_easycrypt::translate_and_write_to_file(
                    &compiler.session(),
                    &krate,
                    &file,
                    &typ_dict,
                ),
                _ => {
                    &compiler
                        .session()
                        .err("unknown backend extension for output file");
                    return Compilation::Stop;
                }
            },
        }
        Compilation::Stop
    }
}

#[derive(Debug, Default, Deserialize)]
struct Dependency {
    name: String,
    kind: Option<String>,
}

#[derive(Debug, Default, Deserialize)]
struct Target {
    name: String,
    kind: Vec<String>,
    crate_types: Vec<String>,
    src_path: String,
}

#[derive(Debug, Default, Deserialize)]
struct Package {
    name: String,
    targets: Vec<Target>,
    dependencies: Vec<Dependency>,
}

#[derive(Debug, Default, Deserialize)]
struct Manifest {
    packages: Vec<Package>,
    target_directory: String,
}

fn read_crate(crate_ta: String, package_name: String, args: &mut Vec<String>) {
    let manifest: Manifest = {
        let mut output = std::process::Command::new("cargo");
        let output = output
            .arg("metadata")
            .args(&["--manifest-path", &format!("{}/Cargo.toml", crate_ta)])
            .args(&["--no-deps", "--format-version", "1"]);
        // println!("Commend: {:?}", output);
        let output = output.output().expect("Error reading cargo manifest.");
        let stdout = output.stdout;
        if !output.status.success() {
            let error =
                String::from_utf8(output.stderr).expect("Failed reading cargo stderr output");
            panic!("Error running cargo metadata: {:?}", error);
        }
        let json_string = String::from_utf8(stdout).expect("Failed reading cargo output");
        serde_json::from_str(&json_string).expect("Error reading to manifest")
    };
    println!("Manifest: {:?}", manifest);
    // Pick the package of the given name.
    let package = manifest
        .packages
        .iter()
        .find(|p| p.name == package_name)
        .expect(&format!(
            "Can't find the package {} in the Cargo.toml",
            package_name
        ));
    // Take the first lib target we find. There should be only one really.
    let target = package
        .targets
        .iter()
        .find(|p| p.crate_types.contains(&"lib".to_string()))
        .expect("No target in the Cargo.toml");

    // Add the target source file to the arguments
    args.push(target.src_path.clone());

    // Add dependencies to link path.
    // This only works with debug builds.
    let deps = manifest.target_directory + "/debug/deps";
    args.push(format!("-L dependency={}", deps));
}

fn main() -> Result<(), ()> {
    let yaml = load_yaml!("cli.yml");
    let matches = App::from_yaml(yaml).get_matches();
    let mut callbacks = HacspecCallbacks {
        output_file: matches.value_of("output").map(|s| s.into()),
        typecheck_only: matches
            .value_of("unstable_flag")
            .map_or(false, |s| match s {
                "no-codegen" => true,
                _ => false,
            }),
    };
    let mut args = env::args().collect::<Vec<String>>();
    if args[1] == "hacspec" {
        // Remove the first arg if it is hacspec.
        // This is the case when running this through `cargo hacspec` instead of
        // the binary directly.
        args.remove(1);
    }
    let package_name = args.pop().expect("No package to analyze.");
    let crate_to_process = args.pop().expect("No crate to analyze.");

    read_crate(crate_to_process, package_name, &mut args);
    args.push("--crate-type=lib".to_string());
    args.push("--edition=2018".to_string());
    args.push("--extern=hacspec_lib".to_string());

    let mut sysroot = std::process::Command::new("rustc")
        .arg("--print")
        .arg("sysroot")
        .output()
        .ok()
        .and_then(|out| String::from_utf8(out.stdout).ok())
        .expect("Couldn't get sysroot");
    sysroot.pop(); // get rid of line break
    args.push("--sysroot=".to_string() + &sysroot + "/lib");

    let mut target_libdir = std::process::Command::new("rustc")
        .arg("--print")
        .arg("target-libdir")
        .output()
        .ok()
        .and_then(|out| String::from_utf8(out.stdout).ok())
        .expect("Couldn't get target-libdir");
    target_libdir.pop(); // get rid of line break
    args.push("-L ".to_string() + &target_libdir);

    println!(" >>> args: {:?}", args);
    RunCompiler::new(&args, &mut callbacks)
        .run()
        .map_err(|_| ())
}
