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
extern crate rustc_parse;
extern crate rustc_session;
extern crate rustc_span;

mod ast_to_rustspec;
mod elab_monadic_lets;
mod hir_to_rustspec;
mod name_resolution;
mod rustspec;

mod rustspec_to_coq;
mod rustspec_to_coq_base;
mod rustspec_to_coq_ssprove;
mod rustspec_to_coq_ssprove_pure;
mod rustspec_to_coq_ssprove_state;

mod rustspec_to_easycrypt;
mod rustspec_to_fstar;
mod typechecker;
mod util;

use glob::Pattern;
use heck::TitleCase;
use im::{HashMap, HashSet};
use itertools::Itertools;
use rustc_driver::{Callbacks, Compilation, RunCompiler};
use rustc_errors::emitter::{ColorConfig, HumanReadableErrorType};
use rustc_errors::DiagnosticId;
use rustc_errors::MultiSpan;
use rustc_interface::{
    interface::{Compiler, Config},
    Queries,
};
use rustc_session::Session;
use rustc_session::{config::ErrorOutputType, search_paths::SearchPath};
use serde::Deserialize;
use serde_json;
use std::env;
use std::fs::File;
use std::path::Path;
use std::process::Command;
use util::APP_USAGE;

#[derive(Clone, PartialEq)]
enum VersionControlArg {
    Initialize,
    Update,
    None,
}

#[derive(Clone)]
struct HacspecCallbacks {
    output_filename: Option<String>,
    output_directory: Option<String>,
    output_type: Option<String>,
    target_directory: String,
    version_control: VersionControlArg,
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

fn construct_module_string<T>(
    krate_path: String,
    krate_dir: String,
    ast_crates_map: &HashMap<String, T>,
) -> Option<String> {
    if ast_crates_map.contains_key(&krate_path.clone()) {
        Some(krate_path.clone())
    } else if ast_crates_map.contains_key(&(krate_path.clone() + "/mod")) {
        Some(krate_path.clone() + "/mod")
    } else if ast_crates_map.contains_key(&(krate_dir.clone() + "/" + krate_path.clone().as_str()))
    {
        Some(krate_dir.clone() + "/" + krate_path.clone().as_str())
    } else if ast_crates_map
        .contains_key(&(krate_dir.clone() + "/" + krate_path.clone().as_str() + "/mod"))
    {
        Some(krate_dir.clone() + "/" + krate_path.clone().as_str() + "/mod")
    } else {
        None
    }
}

fn construct_handle_crate_queue<'tcx>(
    compiler: &Compiler,
    handled: &mut HashSet<String>,
    ast_crates_map: &HashMap<String, rustc_ast::ast::Crate>,
    krate_path: String,
    krate_dir: String,
) -> Result<Vec<((String, String, String), rustc_ast::ast::Crate)>, bool> {
    // Compute the crate module string, based on local path (krate_path)
    // Look at path/mod_name.rs and path/mod_name/mod.rs for module
    let krate_module_string =
        match construct_module_string(krate_path.clone(), krate_dir.clone(), ast_crates_map) {
            Some(s) => s,
            None => {
                compiler
                    .session()
                    .err(format!("There is no module with name {}", krate_path.clone()).as_str());
                return Err(false);
            }
        };

    // Depth first handling, skip module if already visited
    if handled.contains(&krate_module_string) {
        return Err(true);
    }

    let krate = ast_crates_map[&krate_module_string].clone();

    let mut krates = Vec::new();

    // Parse over the crate, loading modules and filling top_level_ctx
    for x in krate.items.clone().into_iter() {
        match x.kind {
            // Whenever a module statement is encountered, add it to the queue
            rustc_ast::ast::ItemKind::Mod(
                rustc_ast::ast::Unsafe::No,
                rustc_ast::ast::ModKind::Unloaded,
            ) => {
                match construct_handle_crate_queue(
                    compiler,
                    handled,
                    ast_crates_map,
                    x.ident.name.to_ident_string(),
                    krate_path.clone(),
                ) {
                    Ok(v) => krates.extend(v),
                    Err(false) => {
                        // If not able to handle module, stop compilation.
                        return Err(false);
                    }
                    Err(true) => (),
                }
            }
            _ => (),
        }
    }

    let krate =
        // Remove the modules statements from the crate
        rustc_ast::ast::Crate {
            items: krate.items
                .clone()
                .into_iter()
                .filter(|x| match x.kind {
                    rustc_ast::ast::ItemKind::Mod(
                        rustc_ast::ast::Unsafe::No,
                        rustc_ast::ast::ModKind::Unloaded,
                    ) => false,
                    _ => true,
                })
                .collect(),
            ..krate
        };

    krates.push((
        (
            krate_path.clone(),
            krate_dir.clone(),
            krate_module_string.clone(),
        ),
        krate,
    ));

    handled.insert(krate_module_string.clone());

    Ok(krates)
}

fn handle_crate<'tcx>(
    callback: &HacspecCallbacks,
    compiler: &Compiler,
    queries: &'tcx Queries<'tcx>,
    ast_crates_map: &HashMap<String, rustc_ast::ast::Crate>,
    root_krate_path: String,
) -> Compilation {
    // Construct a queue of files to handle
    let krate_queue = match construct_handle_crate_queue(
        compiler,
        &mut HashSet::new(),
        ast_crates_map,
        root_krate_path.clone(),
        "".to_string(),
    ) {
        Ok(v) => v,
        Err(false) => {
            // If not able to handle crate, stop compilation.
            return Compilation::Stop;
        }
        Err(true) => return Compilation::Continue, // Nothing at all, should probably never happen
    };

    let top_ctx_map: &mut HashMap<String, name_resolution::TopLevelContext> = &mut HashMap::new();
    let special_names_map: &mut HashMap<String, ast_to_rustspec::SpecialNames> =
        &mut HashMap::new();

    let krate_use_paths: &mut HashMap<String, Vec<String>> = &mut HashMap::new();

    // Get all 'use' dependencies per module
    let mut krate_queue_no_module_statements = Vec::new();
    for ((krate_path, krate_dir, krate_module_string), krate) in krate_queue {
        krate_use_paths.insert(krate_path.clone(), Vec::new());

        // Parse over the crate, loading modules and filling top_level_ctx
        for x in krate.items.clone().into_iter() {
            match x.kind {
                // Load the top_ctx from the module specified in the use statement
                rustc_ast::ast::ItemKind::Use(ref tree) => {
                    match tree.kind {
                        rustc_ast::ast::UseTreeKind::Glob => {
                            krate_use_paths[&krate_path].push(
                                (&tree.prefix)
                                    .segments
                                    .last()
                                    .unwrap()
                                    .ident
                                    .name
                                    .to_ident_string(),
                            );
                        }
                        _ => (),
                    };
                }
                _ => (),
            }
        }

        // Remove the modules statements from the crate
        krate_queue_no_module_statements.push((
            (krate_path, krate_dir, krate_module_string),
            rustc_ast::ast::Crate {
                items: krate
                    .items
                    .clone()
                    .into_iter()
                    .filter(|x| match x.kind {
                        rustc_ast::ast::ItemKind::Mod(
                            rustc_ast::ast::Unsafe::No,
                            rustc_ast::ast::ModKind::Unloaded,
                        ) => false,
                        _ => true,
                    })
                    .collect(),
                ..krate
            },
        ));
    }

    /////////////////////////////////
    // Start of actual translation //
    /////////////////////////////////

    let external_data = |imported_crates: &Vec<rustspec::Spanned<String>>| {
        queries.global_ctxt().unwrap().peek_mut().enter(|tcx| {
            hir_to_rustspec::retrieve_external_data(&compiler.session(), &tcx, imported_crates)
        })
    };

    ///////////////////////////////////////////////////////////////////////////
    // Translate all modules from ast to rustspec (modules becomes programs) //
    ///////////////////////////////////////////////////////////////////////////

    let mut krate_queue_programs = Vec::new();
    for ((krate_path, krate_dir, krate_module_string), krate) in krate_queue_no_module_statements {
        // Generate an empty context then fill it whenever an Use statement is encountered
        let new_specials = &mut ast_to_rustspec::SpecialNames {
            arrays: HashSet::new(),
            enums: HashSet::new(),
            aliases: HashMap::new(),
        };

        for krate_use_path_string in &krate_use_paths[&krate_path] {
            if let Some(krate_use_string) = construct_module_string(
                krate_use_path_string.clone(),
                krate_dir.clone(),
                special_names_map,
            ) {
                new_specials
                    .arrays
                    .extend(special_names_map[&krate_use_string].arrays.clone());
                new_specials
                    .enums
                    .extend(special_names_map[&krate_use_string].enums.clone());
                new_specials
                    .aliases
                    .extend(special_names_map[&krate_use_string].aliases.clone());
            }
        }

        let krate = match ast_to_rustspec::translate(
            &compiler.session(),
            &krate,
            &external_data,
            new_specials,
        ) {
            Ok(krate) => krate,
            Err(_) => {
                compiler
                    .session()
                    .err("unable to translate to Hacspec due to out-of-language errors");
                return Compilation::Stop;
            }
        };

        (*special_names_map).insert(krate_path.clone(), new_specials.clone());

        krate_queue_programs.push(((krate_path, krate_dir, krate_module_string), krate));
    }

    ///////////////////////////////
    // Typecheck all the modules //
    ///////////////////////////////

    let mut krate_queue_typechecked = Vec::new();
    for ((krate_path, krate_dir, krate_module_string), krate) in krate_queue_programs {
        log::trace!("   typechecking {:#?}", krate);
        let new_top_ctx = &mut name_resolution::TopLevelContext {
            consts: HashMap::new(),
            functions: HashMap::new(),
            typ_dict: HashMap::new(),
        };

        for krate_use_path_string in &krate_use_paths[&krate_path] {
            if let Some(krate_use_string) = construct_module_string(
                krate_use_path_string.clone(),
                krate_dir.clone(),
                top_ctx_map,
            ) {
                new_top_ctx
                    .consts
                    .extend(top_ctx_map[&krate_use_string].consts.clone());
                new_top_ctx
                    .functions
                    .extend(top_ctx_map[&krate_use_string].functions.clone());
                new_top_ctx
                    .typ_dict
                    .extend(top_ctx_map[&krate_use_string].typ_dict.clone());
            }
        }

        let krate = match name_resolution::resolve_crate(
            &compiler.session(),
            krate,
            &external_data,
            new_top_ctx,
        ) {
            Ok(krate) => krate,
            Err(_) => {
                compiler
                    .session()
                    .err("found some Hacspec name resolution errors");
                return Compilation::Stop;
            }
        };

        let krate = match typechecker::typecheck_program(&compiler.session(), &krate, new_top_ctx) {
            Ok(krate) => krate,
            Err(_) => {
                compiler
                    .session()
                    .err("found some Hacspec typechecking errors");
                return Compilation::Stop;
            }
        };

        (*top_ctx_map).insert(krate_path.clone(), new_top_ctx.clone());
        krate_queue_typechecked.push(((krate_path, krate_dir, krate_module_string), krate));
    }

    let imported_crates = (&krate_queue_typechecked).into_iter().fold(
        Vec::new(),
        |mut all_imported_crates, (_, krate)| {
            all_imported_crates.extend(name_resolution::get_imported_crates(&krate));
            all_imported_crates
        },
    );
    let imported_crates = imported_crates
        .into_iter()
        .filter(|(x, _)| x != "hacspec_lib" && x != "crate")
        .map(|(x, _)| x)
        .collect::<Vec<_>>();

    println!(
        " > Successfully typechecked{}{}",
        match &callback.output_filename {
            Some(file_name) => " ".to_string() + file_name,
            None => "".to_string(),
        },
        if imported_crates.len() == 0 {
            ".".to_string()
        } else {
            format!(
                ", assuming that the code in {} has also been Hacspec-typechecked",
                imported_crates.iter().format(", ")
            )
        }
    );

    ///////////////////////////////////
    // Generate all the output files //
    ///////////////////////////////////

    if let (Some(extension), Some(file_str)) = (&callback.output_type, &callback.output_directory) {
        let original_file = Path::new(file_str);

        for ((krate_path, _, _), krate) in krate_queue_typechecked {
            let file_name = if krate_path == root_krate_path {
                if let Some(file_name) = &callback.output_filename {
                    Path::new(&file_name.clone())
                        .with_extension("")
                        .to_str()
                        .unwrap()
                        .to_string()
                } else {
                    krate_path.clone() // TODO: Should this throw an error instead (needs default for programs run with -f)
                }
            } else {
                krate_path.clone()
            };

            let join_path = match extension.clone().as_str() {
                "fst" | "ec" | "json" => {
                    // Compute file name as output directory with crate local path (file_name)
                    file_name.clone().to_title_case().replace(" ", ".") + "." + extension
                }
                "v" | "v_ssprove_state" | "v_ssprove_pure" | "v_ssprove" => {
                    // Compute file name as output directory with crate local path (file_name)
                    file_name.clone().to_title_case().replace(" ", "_") + ".v"
                }
                _ => {
                    compiler
                        .session()
                        .err("unknown backend extension for output files");
                    return Compilation::Stop;
                }
            };

            let file = match &callback.version_control {
                VersionControlArg::Update => {
                    let file_temp_dir = original_file.join("_temp");
                    let file_temp_dir = file_temp_dir.to_str().unwrap();

                    std::fs::create_dir_all(file_temp_dir.clone()).expect("Failed to create dir");

                    original_file.join("_temp").join(join_path.clone())
                }
                _ => {
                    std::fs::create_dir_all(original_file.clone()).expect("Failed to create dir");
                    original_file.join(join_path.clone())
                }
            };
            let file = file.to_str().unwrap();

            match extension.as_str() {
                "fst" => rustspec_to_fstar::translate_and_write_to_file(
                    &compiler.session(),
                    &krate,
                    &file,
                    &top_ctx_map[&krate_path],
                ),
                "ec" => rustspec_to_easycrypt::translate_and_write_to_file(
                    &compiler.session(),
                    &krate,
                    &file,
                    &top_ctx_map[&krate_path],
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
                    &top_ctx_map[&krate_path],
                ),
                "v_ssprove_pure" => rustspec_to_coq_ssprove_pure::translate_and_write_to_file(
                    &compiler.session(),
                    &krate,
                    &file,
                    &top_ctx_map[&krate_path],
                ),
                "v_ssprove" => rustspec_to_coq_ssprove::translate_and_write_to_file(
                    &compiler.session(),
                    &krate,
                    &file,
                    &top_ctx_map[&krate_path],
                ),
                "v_ssprove_state" => rustspec_to_coq_ssprove_state::translate_and_write_to_file(
                    &compiler.session(),
                    &krate,
                    &file,
                    &top_ctx_map[&krate_path],
                ),
                _ => {
                    compiler
                        .session()
                        .err("unknown backend extension for output file");
                    return Compilation::Stop;
                }
            }

            if callback.version_control != VersionControlArg::None {
                let file_destination = original_file.join(join_path.clone());
                let file_destination = file_destination.to_str().unwrap();

                let file_vc = original_file.join("_vc").join(join_path.clone());
                let file_vc = file_vc.to_str().unwrap();

                let file_vc_dir = original_file.join("_vc");
                let file_vc_dir = file_vc_dir.to_str().unwrap();
                std::fs::create_dir_all(file_vc_dir.clone()).expect("Failed to crate dir");

                match callback.version_control {
                    VersionControlArg::Initialize => {
                        std::fs::copy(file_destination.clone(), file_vc.clone()).expect(
                            format!(
                                "Failed to copy file '{}' to '{}'",
                                file_destination.clone(),
                                file_vc.clone()
                            )
                            .as_str(),
                        );
                    }
                    VersionControlArg::Update => {
                        let file_temp = original_file.join("_temp").join(join_path.clone());
                        let file_temp = file_temp.to_str().unwrap();

                        std::process::Command::new("git")
                            .output()
                            .expect("Could not find 'git'. Please install git and try again.");
                        std::process::Command::new("git")
                            .arg("merge-file")
                            .arg(file_destination.clone())
                            .arg(file_vc.clone())
                            .arg(file_temp.clone())
                            .output()
                            .expect("git-merge failed");
                        std::fs::copy(file_temp.clone(), file_vc.clone()).expect(
                            format!(
                                "Failed to copy file '{}' to '{}'",
                                file_temp.clone(),
                                file_vc.clone()
                            )
                            .as_str(),
                        );
                        std::fs::remove_file(file_temp.clone()).expect(
                            format!("Failed to remove file '{}'", file_destination.clone())
                                .as_str(),
                        );
                    }
                    VersionControlArg::None => panic!(),
                }
            }
        }
    }

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
        let crate_origin_file = compiler
            .build_output_filenames(compiler.session(), &[])
            .with_extension("")
            .to_str()
            .unwrap()
            .to_string();

        let mut analysis_crates = HashMap::new();
        analysis_crates.insert(crate_origin_file.clone(), krate);

        // Find module location using hir
        queries.global_ctxt().unwrap().peek_mut().enter(|tcx| {
            for item_id in tcx.hir().items() {
                let item = tcx.hir().item(item_id);

                if let rustc_hir::ItemKind::Mod(_m) = &item.kind {
                    let (module, mod_span, _hir_id) = &tcx.hir().get_module(item.def_id);

                    // locate the file from a module using the span
                    let sm: &rustc_span::source_map::SourceMap =
                        (compiler.session()).parse_sess.source_map();
                    if let (
                        rustc_span::FileName::Real(rustc_span::RealFileName::LocalPath(
                            module_path,
                        )),
                        rustc_span::FileName::Real(rustc_span::RealFileName::LocalPath(root)),
                    ) = (
                        sm.span_to_filename(module.spans.inner_span),
                        sm.span_to_filename(*mod_span), // = module.spans.inject_use_span ?
                    ) {
                        // parse the file for the module
                        let mut parser = rustc_parse::new_parser_from_file(
                            &(&compiler.session()).parse_sess,
                            module_path.as_path(),
                            None,
                        );

                        // Get the items of the module and
                        // make new crate with the parsed items
                        let new_crate: rustc_ast::ast::Crate = parser.parse_crate_mod().unwrap();

                        // Calculate the local path from the crate root file
                        let crate_local_path = module_path
                            .strip_prefix(root.parent().unwrap())
                            .unwrap()
                            .with_extension("")
                            .to_str()
                            .unwrap()
                            .to_string();

                        // Add to map from module path to crate data
                        analysis_crates.insert(crate_local_path, new_crate);
                    }
                }
            }
        });

        // Do depth first handling of modules starting search at crate root
        handle_crate(
            &self,
            compiler,
            queries,
            &analysis_crates,
            crate_origin_file,
        );

        Compilation::Stop
    }
}

// === Cargo Metadata Helpers ===

#[derive(Debug, Default, Deserialize, Clone)]
struct Dependency {
    name: String,
    #[allow(dead_code)]
    kind: Option<String>,
}

#[derive(Debug, Default, Deserialize, Clone)]
struct Target {
    #[allow(dead_code)]
    name: String,
    #[allow(dead_code)]
    kind: Vec<String>,
    crate_types: Vec<String>,
    src_path: String,
}

#[derive(Debug, Default, Deserialize, Clone)]
struct Package {
    name: String,
    targets: Vec<Target>,
    dependencies: Vec<Dependency>,
}

#[derive(Debug, Default, Deserialize, Clone)]
struct Manifest {
    packages: Vec<Package>,
    target_directory: String,
}

// ===

/// Read the crate metadata and use the information for the build.
fn read_crate_pre(
    manifest: Option<String>,
    package_name: Option<String>,
) -> (Manifest, Vec<Package>) {
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
    let package: Vec<Package> = if let Some(package_name) = package_name {
        let glob_pattern = Pattern::new(package_name.as_str()).unwrap();
        let p: Vec<Package> = manifest
            .clone()
            .packages
            .into_iter()
            .filter(|p| glob_pattern.matches(&p.name))
            .collect();

        if p.is_empty() {
            panic!(
                " ⚠️  Can't find the package matching {} in the Cargo.toml\n\n{}",
                package_name, APP_USAGE
            );
        }

        p.clone()
        // }
    } else {
        vec![(&manifest.packages[0]).clone()]
    };

    (manifest, package)
}

/// Read the crate metadata and use the information for the build.
fn read_crate(package: Package, args: &mut Vec<String>, callbacks: &mut HacspecCallbacks) {
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

    // Add the dependencies as --extern for the hacpsec typechecker.
    for dependency in package.dependencies.iter() {
        args.push(format!("--extern={}", dependency.name.replace("-", "_")));
    }

    if callbacks.output_filename == None {
        callbacks.output_filename = Some(package.name.clone())
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

    // Optionally get output directory.
    let output_filename_index = args.iter().position(|a| a == "-o");
    let output_filename = match output_filename_index {
        Some(i) => {
            args.remove(i);
            Some(args.remove(i))
        }
        None => None,
    };

    // Optionally get output directory.
    let output_directory_index = args.iter().position(|a| a == "--dir");
    let output_directory = match output_directory_index {
        Some(i) => {
            args.remove(i);
            Some(args.remove(i))
        }
        None => None,
    };

    // Optionally get output file extension.
    let output_type_index = args.iter().position(|a| a == "-e");
    let output_type = match output_type_index {
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

    let vc = match args.iter().position(|a| a == "--vc-init") {
        Some(i) => {
            args.remove(i);
            VersionControlArg::Initialize
        }
        None => VersionControlArg::None,
    };
    let vc = match args.iter().position(|a| a == "--vc-update") {
        Some(i) => {
            args.remove(i);
            VersionControlArg::Update
        }
        None => vc,
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
        output_filename,
        output_directory: if match output_type {
            Some(_) => None == output_directory,
            _ => false,
        } {
            Some(env::current_dir().unwrap().to_str().unwrap().to_owned())
        } else {
            output_directory
        },
        output_type,
        // This defaults to the default target directory.
        target_directory: env::current_dir().unwrap().to_str().unwrap().to_owned()
            + "/../target/debug/deps",
        version_control: vc,
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

            compiler_args.push("--crate-type=lib".to_string());
            compiler_args.push("--edition=2021".to_string());
            log::trace!("compiler_args: {:?}", compiler_args);
            let compiler = RunCompiler::new(&compiler_args, &mut callbacks);

            match compiler.run() {
                Ok(_) => Ok(()),
                Err(_) => Err(1usize),
            }?;
        }
        None => {
            let package_name = args.pop();
            let (manifest, package_vec) = read_crate_pre(manifest, package_name);

            // Add build artifact path.
            // This only works with debug builds.
            let deps = manifest.target_directory + "/debug/deps";
            callbacks.target_directory = deps;

            println!("{:?}", package_vec);
            for package in package_vec {
                let pkg_name = package.name.clone();

                let mut compiler_args_run = compiler_args.clone();
                let mut callbacks_run = callbacks.clone();

                log::trace!("package name to analyze: {:?}", pkg_name);
                read_crate(package, &mut compiler_args_run, &mut callbacks_run);

                compiler_args_run.push("--crate-type=lib".to_string());
                compiler_args_run.push("--edition=2021".to_string());
                log::trace!("compiler_args: {:?}", compiler_args_run);
                let compiler = RunCompiler::new(&compiler_args_run, &mut callbacks_run);

                match compiler.run() {
                    Ok(_) => Ok(()),
                    Err(_) => Err(1usize),
                }?;

            }
        }
    };

    Ok(())
}
