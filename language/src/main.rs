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
mod name_resolution;
mod rustspec;
mod rustspec_to_easycrypt;
mod rustspec_to_fstar;
mod rustspec_to_coq;
mod typechecker;
mod util;

use itertools::Itertools;
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
use std::env;
use std::ffi::OsStr;
use std::fs::File;
use std::path::Path;
use std::process::Command;
use util::APP_USAGE;

struct HacspecCallbacks {
    output_file: Option<String>,
    output_template_file: Option<String>,
    target_directory: String,
}

const ERROR_OUTPUT_CONFIG: ErrorOutputType =
    ErrorOutputType::HumanReadable(HumanReadableErrorType::Default(ColorConfig::Auto));

trait HacspecErrorEmitter {
    fn span_rustspec_err<S: Into<MultiSpan>>(&self, s: S, msg: &str);

    fn span_rustspec_warn<S: Into<MultiSpan>>(&self, s: S, msg: &str);
}

impl HacspecErrorEmitter for Session {
    fn span_rustspec_err<S: Into<MultiSpan>>(&self, s: S, msg: &str) {
        self.span_err_with_code(s, msg, DiagnosticId::Error(String::from("Hacspec")));
    }

    fn span_rustspec_warn<S: Into<MultiSpan>>(&self, s: S, msg: &str) {
        self.span_warn_with_code(s, msg, DiagnosticId::Error(String::from("Hacspec")));
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
        let external_data = |imported_crates: &Vec<rustspec::Spanned<String>>| {
            queries.global_ctxt().unwrap().peek_mut().enter(|tcx| {
                hir_to_rustspec::retrieve_external_data(&compiler.session(), &tcx, imported_crates)
            })
        };
        let krate = match ast_to_rustspec::translate(&compiler.session(), &krate, &external_data) {
            Ok(krate) => krate,
            Err(_) => {
                &compiler
                    .session()
                    .err("unable to translate to Hacspec due to out-of-language errors");
                return Compilation::Stop;
            }
        };
        let (krate, mut top_ctx) =
            match name_resolution::resolve_crate(&compiler.session(), krate, &external_data) {
                Ok(krate) => krate,
                Err(_) => {
                    &compiler
                        .session()
                        .err("found some Hacspec name resolution errors");
                    return Compilation::Stop;
                }
            };
        let krate = match typechecker::typecheck_program(&compiler.session(), &krate, &mut top_ctx)
        {
            Ok(krate) => krate,
            Err(_) => {
                &compiler
                    .session()
                    .err("found some Hacspec typechecking errors");
                return Compilation::Stop;
            }
        };
        let imported_crates = name_resolution::get_imported_crates(&krate);
        let imported_crates = imported_crates
            .into_iter()
            .filter(|(x, _)| x != "hacspec_lib")
            .map(|(x, _)| x)
            .collect::<Vec<_>>();
        println!(
            " > Successfully typechecked{}",
            if imported_crates.len() == 0 {
                ".".to_string()
            } else {
                format!(
                    ", assuming that the code in crates {} has also been Hacspec-typechecked",
                    imported_crates.iter().format(", ")
                )
            }
        );

	let do_merge = match &self.output_template_file {
	    None => false,
	    Some(_) => true,
	};

        match &self.output_file {
            None => return Compilation::Stop,
            Some(file) =>
	    {
		let write_file = if do_merge {file.clone() + "_temp"} else {file.clone()};
		match Path::new(&file).extension().and_then(OsStr::to_str).unwrap() {
                "fst" => rustspec_to_fstar::translate_and_write_to_file(
                    &compiler.session(),
                    &krate,
                    &write_file,
                    &top_ctx,
                ),
                "ec" => rustspec_to_easycrypt::translate_and_write_to_file(
                    &compiler.session(),
                    &krate,
                    &write_file,
                    &top_ctx,
                ),
                "json" => {
                    let file = write_file.trim();
                    let path = Path::new(file);
                    let file = match File::create(&path) {
                        Err(why) => {
                            &compiler.session().err(
                                format!("Unable to write to output file {}: \"{}\"", file, why)
                                    .as_str(),
                            );
                            return Compilation::Stop;
                        }
                        Ok(file) => file,
                    };
                    match serde_json::to_writer_pretty(file, &krate) {
                        Err(why) => {
                            &compiler
                                .session()
                                .err(format!("Unable to serialize program: \"{}\"", why).as_str());
                            return Compilation::Stop;
                        }
                        Ok(_) => (),
                    };
                },
                "v" => rustspec_to_coq::translate_and_write_to_file(
                    &compiler.session(),
                    &krate,
                    &write_file,
                    &top_ctx,
                ),
                _ => {
                    &compiler
                        .session()
                        .err("unknown backend extension for output file");
                    return Compilation::Stop;
                }
		};
		
		match &self.output_template_file {
		    None => Command::new("cp")
			.arg(write_file.clone())
			.arg(write_file.clone() + "_template")
			.spawn()
			.expect("Failed copy to template"),
		    Some(template_file) => {
			Command::new("git")
			    .arg("merge-file")
			    .arg(file)
			    .arg(template_file)
			    .arg(&write_file)
			    .spawn()
			    .expect("Failed git-merge");
			Command::new("mv")
			    .arg(&write_file)
			    .arg(template_file)
			    .spawn()
			    .expect("Failed overwriting template")
		    },
		};
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

    // Add build artifact path.
    // This only works with debug builds.
    let deps = manifest.target_directory + "/debug/deps";
    callbacks.target_directory = deps;

    // Add the dependencies as --extern for the hacpsec typechecker.
    for dependency in package.dependencies.iter() {
        args.push(format!("--extern={}", dependency.name.replace("-", "_")));
    }
}

fn main() -> Result<(), ()> {
    let mut args = env::args().collect::<Vec<String>>();
    let output_file_index = args.iter().position(|a| a == "-o");
    let output_file = match output_file_index {
        Some(i) => args.get(i + 1).cloned(),
        None => None,
    };
    
    let output_template_file_index = args.iter().position(|a| a == "--update");
    let output_template_file = match output_template_file_index {
        Some(i) => {
	    args.remove(i);
	    match &output_file {
		Some (file) => Some (file.clone() + "_template"),
		None => None, // Error?
	    }
	},
        None => None,
    };
    
    // Optionally an input file can be passed in. This should be mostly used for
    // testing.
    let input_file = match args.iter().position(|a| a == "-f") {
        Some(i) => {
            args.remove(i);
            true
        }
        None => false,
    };

    let mut callbacks = HacspecCallbacks {
        output_file,
	output_template_file,
        // This defaults to the default target directory.
        target_directory: env::current_dir().unwrap().to_str().unwrap().to_owned()
            + "/../target/debug/deps",
    };

    if !input_file {
        let package_name = args
            .pop()
            .expect(&format!("No package to analyze.\n\n{}", APP_USAGE));

        read_crate(package_name, &mut args, &mut callbacks);
    } else {
        // If only a file is provided we add the default dependencies only.
        args.extend_from_slice(&[
            "--extern=abstract_integers".to_string(),
            "--extern=hacspec_derive".to_string(),
            "--extern=hacspec_lib".to_string(),
            "--extern=secret_integers".to_string(),
        ]);
    }

    args.push("--crate-type=lib".to_string());
    args.push("--edition=2018".to_string());

    match RunCompiler::new(&args, &mut callbacks).run() {
        Ok(_) =>  Ok(()),
        Err(_) => Err(()),
    }
}
