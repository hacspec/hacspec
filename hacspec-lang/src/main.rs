#![feature(rustc_private)]
extern crate rustc_driver;
extern crate rustc_errors;
#[macro_use]
extern crate clap;

use clap::App;
use rustc_driver::{run_compiler, Callbacks};

struct HacspecCallbacks {}

impl Callbacks for HacspecCallbacks {}

fn main() -> Result<(), ()> {
    let yaml = load_yaml!("cli.yml");
    let matches = App::from_yaml(yaml).get_matches();
    let source_file = matches.value_of("INPUT").unwrap();
    run_compiler(
        &["-v".to_string(), source_file.to_string()],
        &mut HacspecCallbacks {},
        None,
        None,
    )
    .map_err(|_| ())
}
