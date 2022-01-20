#![feature(rustc_private)]
extern crate im;
extern crate pretty;
extern crate rustc_ast;
extern crate rustc_ast_pretty;
extern crate rustc_driver;
extern crate rustc_errors;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_metadata;
extern crate rustc_middle;
extern crate rustc_session;
extern crate rustc_span;

extern crate rustc_parse;

mod ast_to_rustspec;
mod hir_to_rustspec;
mod name_resolution;
mod rustspec;
mod rustspec_to_coq;
mod rustspec_to_easycrypt;
mod rustspec_to_fstar;
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

use im::{HashMap, HashSet};
use rustc_ast_pretty::pprust::item_to_string;
use heck::{SnakeCase, TitleCase};

struct HacspecCallbacks {
    output_file: Option<String>,
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

pub fn handle_crate<'tcx>(
    output_file: &Option<String>,
    compiler: &Compiler,
    queries: &'tcx Queries<'tcx>,
    handled: &mut HashSet<String>,
    ast_crates: &HashMap<String, rustc_ast::ast::Crate>,
    krate_path: String,
    top_ctx: &mut name_resolution::TopLevelContext,
) -> Compilation {
    if handled.contains(&krate_path) {
        return Compilation::Continue;
    }

    // Look at path/mod_name.rs and path/mod_name/mod.rs for module
    let krate = ast_crates[&(if ast_crates.contains_key(&krate_path.clone()) {
        krate_path.clone()
    } else if ast_crates.contains_key(&(krate_path.clone() + "/mod")) {
        krate_path.clone() + "/mod"
    } else {
        compiler
            .session()
            .err(format!("There is no module with name {}", krate_path.clone()).as_str());
        return Compilation::Stop;
    })]
        .clone();

    let krate = match krate {
        rustc_ast::ast::Crate { attrs, items, span } => {
            let mut v = vec![];
            for x in items.into_iter().clone() {
                match x.kind {
                    rustc_ast::ast::ItemKind::Mod(
                        rustc_ast::ast::Unsafe::No,
                        rustc_ast::ast::ModKind::Unloaded,
                    ) => {
                        if handle_crate(
                            output_file,
                            compiler,
                            queries,
                            handled,
                            ast_crates,
                            x.ident.name.to_ident_string(),
                            top_ctx,
                        ) == Compilation::Stop
                        {
                            return Compilation::Stop;
                        }

                        // TODO: Include items in some way ?
                        // v.push(rustc_ast::ast::Item {
                        //     kind: rustc_ast::ast::ItemKind::Mod(
                        //         rustc_ast::ast::Unsafe::No,
                        //         rustc_ast::ast::ModKind::Loaded(
                        //             vec![],
                        //             rustc_ast::ast::Inline::No,
                        //             rustc_span::DUMMY_SP,
                        //         ),
                        //     ),
                        //     ..(*x).clone()
                        // });
                    }
                    _ => v.push((*x).clone()),
                }
            }

            rustc_ast::ast::Crate {
                attrs,
                items: v.into_iter().map(|x| rustc_ast::ptr::P(x)).collect(),
                span,
            }
        }
    };

    // Start of actual translation

    let external_data = |imported_crates: &Vec<rustspec::Spanned<String>>| {
        queries.global_ctxt().unwrap().peek_mut().enter(|tcx| {
            hir_to_rustspec::retrieve_external_data(&compiler.session(), &tcx, imported_crates)
        })
    };

    let krate = match ast_to_rustspec::translate(&compiler.session(), &krate, &external_data) {
        Ok(krate) => krate,
        Err(_) => {
            compiler
                .session()
                .err("unable to translate to Hacspec due to out-of-language errors");
            return Compilation::Stop;
        }
    };

    let krate = match name_resolution::resolve_crate(
        &compiler.session(),
        krate,
        &external_data,
        top_ctx,
    ) {
        Ok(krate) => krate,
        Err(_) => {
            compiler
                .session()
                .err("found some Hacspec name resolution errors");
            return Compilation::Stop;
        }
    };

    let krate = match typechecker::typecheck_program(&compiler.session(), &krate, top_ctx) {
        Ok(krate) => krate,
        Err(_) => {
            compiler
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

    match &output_file {
        None => return Compilation::Stop,
        Some(file_str) => {
            let original_file = Path::new(file_str);
            let extension = original_file.extension().unwrap();

            let oe = if krate_path != "".to_string() {
                (original_file.parent().unwrap())
                    .join(Path::new(krate_path.clone().as_str()))
                    .with_extension(extension)
            } else {
                original_file.to_path_buf()
            };

            let file = &(oe.to_str().unwrap().to_title_case().replace("-", "_"));
            match extension.to_str().unwrap() {
                "fst" => rustspec_to_fstar::translate_and_write_to_file(
                    &compiler.session(),
                    &krate,
                    &file,
                    &top_ctx,
                ),
                "ec" => rustspec_to_easycrypt::translate_and_write_to_file(
                    &compiler.session(),
                    &krate,
                    &file,
                    &top_ctx,
                ),
                "json" => {
                    let file = file.trim();
                    let path = Path::new(file);
                    let file = match File::create(&path) {
                        Err(why) => {
                            compiler.session().err(
                                format!("Unable to write to output file {}: \"{}\"", file, why)
                                    .as_str(),
                            );
                            return Compilation::Stop;
                        }
                        Ok(file) => file,
                    };
                    match serde_json::to_writer_pretty(file, &krate) {
                        Err(why) => {
                            compiler
                                .session()
                                .err(format!("Unable to serialize program: \"{}\"", why).as_str());
                            return Compilation::Stop;
                        }
                        Ok(_) => (),
                    };
                }
                "v" => rustspec_to_coq::translate_and_write_to_file(
                    &compiler.session(),
                    &krate,
                    &file,
                    &top_ctx,
                ),
                _ => {
                    compiler
                        .session()
                        .err("unknown backend extension for output file");
                    return Compilation::Stop;
                }
            }
        }
    }

    handled.insert(krate_path);

    Compilation::Continue
}

impl Callbacks for HacspecCallbacks {
    fn config(&mut self, config: &mut Config) {
        log::debug!(" --- hacspec config callback");
        log::trace!("     target directory {}", self.target_directory);
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
        log::debug!(" --- hacspec after_analysis callback");
        let krate: rustc_ast::ast::Crate = queries.parse().unwrap().take();

        let mut analysis_crates = HashMap::new(); // [krate]
        analysis_crates.insert("".to_string(), krate);

        // Find module location using hir
        queries.global_ctxt().unwrap().peek_mut().enter(|tcx| {
            // .take() instead of peek_mut ?
            let hir_krate = tcx.hir();
            for item in hir_krate.items() {
                if let rustc_hir::ItemKind::Mod(_m) = &item.kind {
                    let (expra, exprb, _exprc) = &tcx.hir().get_module(item.def_id); // expra == m

                    let sm: &rustc_span::source_map::SourceMap =
                        (compiler.session()).parse_sess.source_map();
                    if let rustc_span::FileName::Real(rustc_span::RealFileName::LocalPath(s)) =
                        sm.span_to_filename(expra.inner)
                    {
                        if let rustc_span::FileName::Real(rustc_span::RealFileName::LocalPath(
                            root,
                        )) = sm.span_to_filename(*exprb)
                        {
                            let mut parser = rustc_parse::new_parser_from_file(
                                &(&compiler.session()).parse_sess,
                                s.as_path(),
                                None,
                            );

                            let parse_mod_krate_items: Vec<rustc_ast::ptr::P<rustc_ast::Item>> =
                                parser.parse_crate_mod().unwrap().items;

                            let new_crate: rustc_ast::ast::Crate = rustc_ast::ast::Crate {
                                attrs: vec![],
                                items: parse_mod_krate_items,
                                span: rustc_span::DUMMY_SP,
                            };

                            let crate_local_path = s
                                .strip_prefix(root.parent().unwrap())
                                .unwrap()
                                .with_extension("")
                                .to_str()
                                .unwrap()
                                .to_string();
                            analysis_crates.insert(crate_local_path, new_crate);
                        }
                    }
                }
            }
        });

        handle_crate(
            &self.output_file,
            compiler,
            queries,
            &mut HashSet::new(),
            &analysis_crates,
            "".to_string(),
            &mut name_resolution::TopLevelContext {
                consts: HashMap::new(),
                functions: HashMap::new(),
                typ_dict: HashMap::new(),
            },
        );

        Compilation::Stop
    }
}

// === Cargo Metadata Helpers ===

#[derive(Debug, Default, Deserialize)]
struct Dependency {
    name: String,
    #[allow(dead_code)]
    kind: Option<String>,
}

#[derive(Debug, Default, Deserialize)]
struct Target {
    #[allow(dead_code)]
    name: String,
    #[allow(dead_code)]
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
fn read_crate(
    manifest: Option<String>,
    package_name: Option<String>,
    args: &mut Vec<String>,
    callbacks: &mut HacspecCallbacks,
) {
    let manifest: Manifest = {
        let mut output = Command::new("cargo");
        let mut output_args = if let Some(manifest_path) = manifest {
            vec!["--manifest-path".to_string(), manifest_path]
        } else {
            Vec::<String>::new()
        };
        output_args.extend_from_slice(&[
            "--no-deps".to_string(),
            "--format-version".to_string(),
            "1".to_string(),
        ]);
        let output = output.arg("metadata").args(&output_args);
        let output = output.output().expect(" ⚠️  Error reading cargo manifest.");
        let stdout = output.stdout;
        if !output.status.success() {
            let error =
                String::from_utf8(output.stderr).expect(" ⚠️  Failed reading cargo stderr output");
            panic!("Error running cargo metadata: {:?}", error);
        }
        let json_string = String::from_utf8(stdout).expect(" ⚠️  Failed reading cargo output");
        serde_json::from_str(&json_string).expect(" ⚠️  Error reading to manifest")
    };

    // Pick the package of the given name or the only package available.
    let package = if let Some(package_name) = package_name {
        manifest
            .packages
            .iter()
            .find(|p| p.name == package_name)
            .expect(&format!(
                " ⚠️  Can't find the package {} in the Cargo.toml\n\n{}",
                package_name, APP_USAGE,
            ))
    } else {
        &manifest.packages[0]
    };
    log::trace!("Typechecking '{:?}' ...", package);

    // Take the first lib target we find. There should be only one really.
    // log::trace!("crate types: {:?}", package.targets);
    // log::trace!("package targets {:?}", package.targets);
    let target = package
        .targets
        .iter()
        .find(|p| {
            p.crate_types.contains(&"lib".to_string())
                || p.crate_types.contains(&"rlib".to_string())
        })
        .expect(&format!(" ⚠️  No target in the Cargo.toml\n\n{}", APP_USAGE));

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

fn main() -> Result<(), usize> {
    pretty_env_logger::init();
    log::debug!(" --- hacspec");
    let mut args = env::args().collect::<Vec<String>>();
    log::trace!("     args: {:?}", args);

    // Args to pass to the compiler
    let mut compiler_args = Vec::new();

    // Drop and pass along binary name.
    compiler_args.push(args.remove(0));

    // Optionally get output file.
    let output_file_index = args.iter().position(|a| a == "-o");
    let output_file = match output_file_index {
        Some(i) => {
            args.remove(i);
            Some(args.remove(i))
        }
        None => None,
    };

    // Optionally an input file can be passed in. This should be mostly used for
    // testing.
    let input_file = match args.iter().position(|a| a == "-f") {
        Some(i) => {
            args.remove(i);
            Some(args.remove(i))
        }
        None => None,
    };

    // Read the --manifest-path argument if present.
    let manifest = match args.iter().position(|a| a == "--manifest-path") {
        Some(i) => {
            args.remove(i);
            Some(args.remove(i))
        }
        None => None,
    };

    // Read the --sysroot. It must be present
    log::trace!("args: {:?}", args);
    match args.iter().position(|a| a.starts_with("--sysroot")) {
        Some(i) => {
            compiler_args.push(args.remove(i));
        }
        None => panic!(" ⚠️  --sysroot is missing. Please report this issue."),
    }

    let mut callbacks = HacspecCallbacks {
        output_file,
        // This defaults to the default target directory.
        target_directory: env::current_dir().unwrap().to_str().unwrap().to_owned()
            + "/../target/debug/deps",
    };

    match input_file {
        Some(input_file) => {
            compiler_args.push(input_file);
            // If only a file is provided we add the default dependencies only.
            compiler_args.extend_from_slice(&[
                "--extern=abstract_integers".to_string(),
                "--extern=hacspec_derive".to_string(),
                "--extern=hacspec_lib".to_string(),
                "--extern=secret_integers".to_string(),
            ]);
        }
        None => {
            let package_name = args.pop();
            log::trace!("package name to analyze: {:?}", package_name);
            read_crate(manifest, package_name, &mut compiler_args, &mut callbacks);
        }
    }

    compiler_args.push("--crate-type=lib".to_string());
    compiler_args.push("--edition=2021".to_string());
    log::trace!("compiler_args: {:?}", compiler_args);
    let compiler = RunCompiler::new(&compiler_args, &mut callbacks);

    match compiler.run() {
        Ok(_) => Ok(()),
        Err(_) => Err(1),
    }
}
