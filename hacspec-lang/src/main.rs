#![feature(rustc_private)]
extern crate rustc_driver;
extern crate rustc_errors;
extern crate rustc_ast;
extern crate rustc_interface;
extern crate rustc_session;
extern crate rustc_span;
#[macro_use]
extern crate clap;

mod rustspec;
mod ast_to_rustspec;
mod rustspec_to_fstar;

use clap::App;
use rustc_driver::{run_compiler, Callbacks, Compilation};
use rustc_errors::emitter::{ColorConfig, HumanReadableErrorType};
use rustc_interface::{
    interface::{Compiler, Config},
    Queries,
};
use rustc_session::{config::ErrorOutputType, search_paths::SearchPath};
use std::env;

struct HacspecCallbacks {
    output_file: Option<String>
}

const ERROR_OUTPUT_CONFIG: ErrorOutputType =
    ErrorOutputType::HumanReadable(HumanReadableErrorType::Default(ColorConfig::Auto));

impl Callbacks for HacspecCallbacks {
    fn config(&mut self, config: &mut Config) {
        let shared_libraries = env!("LD_LIBRARY_PATH").trim().split(":");
        for shared_library in shared_libraries {
            if shared_library != "" {
                config.opts.search_paths.push(SearchPath::from_cli_opt(
                    shared_library,
                    ERROR_OUTPUT_CONFIG,
                ));
            }
        }
    }

    fn after_parsing<'tcx>(
        &mut self,
        compiler: &Compiler,
        queries: &'tcx Queries<'tcx>,
    ) -> Compilation {
        let krate = queries.parse().unwrap().take();
        let krate = match ast_to_rustspec::translate(&compiler.session(), &krate) {
            Ok(krate) => krate,
            Err(_) => {
                &compiler.session().err("unable to translate to Rustspec due to previous errors");
                return Compilation::Stop
            }
        };
        match &self.output_file {
            None => (),
            Some(file) => rustspec_to_fstar::translate_and_write_to_file(&krate, &file)
        }
        Compilation::Stop
    }
}

fn main() -> Result<(), ()> {
    let yaml = load_yaml!("cli.yml");
    let matches = App::from_yaml(yaml).get_matches();
    let mut callbacks = HacspecCallbacks {
        output_file: matches.value_of("output").map(|s| s.into())
    };
    let args = env::args().collect::<Vec<String>>();
    run_compiler(&args, &mut callbacks, None, None).map_err(|_| ())
}
