#![feature(rustc_private)]
extern crate im;
extern crate pretty;
extern crate rustc_ast;
extern crate rustc_driver;
extern crate rustc_errors;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_metadata;
extern crate rustc_middle;
extern crate rustc_session;
extern crate rustc_span;

mod ast_to_rustspec;
mod hir_to_rustspec;
mod rustspec;
mod rustspec_to_easycrypt;
mod rustspec_to_fstar;
mod typechecker;
mod util;

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
use std::path::{Path, PathBuf};
use std::process::Command;
use util::APP_USAGE;

struct HacspecCallbacks {
    output_file: Option<String>,
    target_directory: String,
}

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
        config.opts.search_paths.push(SearchPath::from_cli_opt(
            &self.target_directory,
            ERROR_OUTPUT_CONFIG,
        ));
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
        let mut item_list: PathBuf = std::env::temp_dir();
        item_list.push("allowed_list_items.json");
        let file = OpenOptions::new()
            .read(true)
            .write(true)
            .create(true)
            .open(item_list.as_path())
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

        match &self.output_file {
            None => return Compilation::Stop,
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

// === Cargo Metadata Helpers ===

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

// ===

/// Read the crate metadata and use the information for the build.
fn read_crate(package_name: String, args: &mut Vec<String>, callbacks: &mut HacspecCallbacks) {
    let manifest: Manifest = {
        let mut output = Command::new("cargo");
        let output = output
            .arg("metadata")
            .args(&["--no-deps", "--format-version", "1"]);
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
    callbacks.target_directory = deps;
}

fn main() -> Result<(), ()> {
    let mut args = env::args().collect::<Vec<String>>();
    let output_file_index = args.iter().position(|a| a == "-o");
    let output_file = match output_file_index {
        Some(i) => args.get(i + 1).cloned(),
        None => None,
    };

    let mut callbacks = HacspecCallbacks {
        output_file,
        target_directory: String::new(),
    };

    let package_name = args
        .pop()
        .expect(&format!("No package to analyze.\n\n{}", APP_USAGE));

    read_crate(package_name, &mut args, &mut callbacks);
    args.push("--crate-type=lib".to_string());
    args.push("--edition=2018".to_string());
    args.push("--extern=hacspec_lib".to_string());

    match RunCompiler::new(&args, &mut callbacks).run() {
        Ok(_) => {
            println!(" > Successfully verified.");
            Ok(())
        }
        Err(_) => Err(()),
    }
}
