#![feature(rustc_private)]
extern crate rustc_ast;
extern crate rustc_driver;
extern crate rustc_errors;
extern crate rustc_hir;
extern crate rustc_interface;
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
mod rustspec_to_fstar;
mod typechecker;

use clap::App;
use hacspec_dev::external_sig::Signature;
use rustc_driver::{run_compiler, Callbacks, Compilation};
use rustc_errors::emitter::{ColorConfig, HumanReadableErrorType};
use rustc_interface::{
    interface::{Compiler, Config},
    Queries,
};
use rustc_session::{config::ErrorOutputType, search_paths::SearchPath};
use serde_json;
use std::collections::{HashMap, HashSet};
use std::env;
use std::fs::OpenOptions;
use walkdir::WalkDir;

struct HacspecCallbacks {
    output_file: Option<String>,
}

const ITEM_LIST_LOCATION: &'static str = "../allowed_item_list.json";

const ERROR_OUTPUT_CONFIG: ErrorOutputType =
    ErrorOutputType::HumanReadable(HumanReadableErrorType::Default(ColorConfig::Auto));

impl Callbacks for HacspecCallbacks {
    fn config(&mut self, config: &mut Config) {
        let libraries_string = if cfg!(target_os = "linux") {
            option_env!("LD_LIBRARY_PATH")
        } else if cfg!(target_os = "macos") {
            option_env!("DYLD_FALLBACK_LIBRARY_PATH")
        } else if cfg!(target_os = "windows") {
            option_env!("PATH")
        } else {
            panic!("Unsuported target OS: {}", cfg!(target_os))
        };
        let shared_libraries = libraries_string.unwrap_or("").trim().split(":");
        for shared_library in shared_libraries {
            if shared_library != "" {
                config.opts.search_paths.push(SearchPath::from_cli_opt(
                    shared_library,
                    ERROR_OUTPUT_CONFIG,
                ));
                for entry in WalkDir::new(shared_library) {
                    let entry = match entry {
                        Some(e) => e,
                        None => continue,
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
                    .err("unable to translate to Rustspec due to out-of-language errors");
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
        let external_funcs = queries.global_ctxt().unwrap().peek_mut().enter(|tcx| {
            hir_to_rustspec::retrieve_external_functions(
                &compiler.session(),
                &tcx,
                &krate.imported_crates,
            )
        });
        let krate = match typechecker::typecheck_program(
            &compiler.session(),
            krate,
            &external_funcs,
            hacspec_items,
        ) {
            Ok(krate) => krate,
            Err(_) => {
                &compiler
                    .session()
                    .err("unable to translate to Rustspec due to typechecking errors");
                return Compilation::Stop;
            }
        };
        match &self.output_file {
            None => (),
            Some(file) => {
                rustspec_to_fstar::translate_and_write_to_file(&compiler.session(), &krate, &file)
            }
        }
        Compilation::Stop
    }
}

fn main() -> Result<(), ()> {
    let yaml = load_yaml!("cli.yml");
    let matches = App::from_yaml(yaml).get_matches();
    let mut callbacks = HacspecCallbacks {
        output_file: matches.value_of("output").map(|s| s.into()),
    };
    let args = env::args().collect::<Vec<String>>();
    run_compiler(&args, &mut callbacks, None, None).map_err(|_| ())
}
