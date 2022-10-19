#[allow(dead_code)]
pub(crate) fn check_vec<T>(v: Vec<Result<T, ()>>) -> Result<Vec<T>, ()> {
    if v.iter().all(|t| t.is_ok()) {
        Ok(v.into_iter().map(|t| t.unwrap()).collect())
    } else {
        Err(())
    }
}

pub(crate) const HACSPEC_ARGS: &str = "HACSPEC_ARGS";

use clap::{Parser, Subcommand};
use serde::{Deserialize, Serialize};
#[derive(Parser, Clone, Debug, Serialize, Deserialize)]
#[command(
    author,
    version,
    about,
    bin_name = "cargo",
    long_about = "Typechecker and compiler for the hacspec subset of Rust"
)]
pub(crate) struct Args {
    #[command(subcommand)]
    pub hacspec: HacspecArgs,
}

#[derive(Subcommand, Clone, Debug, Serialize, Deserialize)]
pub(crate) enum HacspecArgs {
    Hacspec {
        /// The output filename (defaults to crate name)
        #[arg(short = 'o', long = "output-filename")]
        output_filename: Option<String>,

        /// The output directory (default to current dir)
        #[arg(short = 'd', long = "dir")]
        output_directory: Option<String>,

        /// File extension F* (fst), Easycrypt (ec), (json), or Coq (v)
        ///
        /// If just -e is supplied, then current directory is used as output.
        /// If neither -e nor --dir are supplied, then we only run the typechecker.
        #[arg(short = 'e', long = "extension")]
        output_type: Option<String>,

        /// Initialize version control in '<FILE_DIR>/_vc'
        #[arg(long = "vc-init")]
        vc_init: bool,

        /// Uses git merge to update the files only with changes, may result in merge conflicts
        #[arg(long = "vc-update")]
        vc_update: bool,

        /// Set the directory for outputting, otherwise '<VC_DIR> = <FILE_DIR>/_vc'.
        #[arg(long = "--vc-dir")]
        pub vc_dir: Option<String>,

        // /// Specify extra Cargo flags.
        // #[arg(long = "cargo-extra-flags")]

        // /// An input file can be passed in, this should be mostly used for testing.
        // #[arg(short = 'f', long = "--input-filename")]
        // input_filename: Option<String>,
        /// The crate to analyse. The crate name is required if there are multiple crates in the workspace. If only one crate is present, the argument can be omitted.
        crate_name: Option<String>,

        #[arg(raw = true)]
        cargo_extra_flags: Vec<String>,
    },
}
