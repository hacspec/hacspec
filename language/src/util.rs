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
    pub hacspec: SubcommandArgs,
}
#[derive(Subcommand, Clone, Debug, Serialize, Deserialize)]
pub(crate) enum SubcommandArgs {
    Hacspec(HacspecArgs),
}

#[derive(Parser, Clone, Debug, Serialize, Deserialize)]
pub struct HacspecArgs {
    /// The output filename (defaults to crate name)
    #[arg(short = 'o', long = "output-filename")]
    pub output_filename: Option<String>,

    /// The output directory (default to current dir)
    #[arg(short = 'd', long = "dir")]
    pub output_directory: Option<String>,

    /// File extension F* (fst), Easycrypt (ec), (json), or Coq (v)
    ///
    /// If just -e is supplied, then current directory is used as output.
    /// If neither -e nor --dir are supplied, then we only run the typechecker.
    #[arg(short = 'e', long = "extension")]
    pub output_type: Option<String>,

    /// Initialize version control in '<FILE_DIR>/_vc'
    #[arg(long = "vc-init")]
    pub vc_init: bool,

    /// Uses git merge to update the files only with changes, may result in merge conflicts
    #[arg(long = "vc-update")]
    pub vc_update: bool,

    /// Set the directory for outputting, otherwise '<VC_DIR> = <FILE_DIR>/_vc'.
    #[arg(long = "vc-dir")]
    pub vc_dir: Option<String>,

    /// An input file can be passed in, this should be mostly used for testing.
    #[arg(short = 'f', long = "input-filename")]
    pub input_filename: Option<String>,

    /// The crate to analyse. The crate name is required if there are multiple crates in the workspace. If only one crate is present, the argument can be omitted.
    pub crate_name: Option<String>,

    #[arg(raw = true)]
    pub cargo_extra_flags: Vec<String>,
}

impl Into<HacspecArgs> for Args {
    fn into(self) -> HacspecArgs {
        let SubcommandArgs::Hacspec(hacspec_args) = self.hacspec;
        hacspec_args
    }
}
impl Into<Args> for HacspecArgs {
    fn into(self) -> Args {
        Args {
            hacspec: SubcommandArgs::Hacspec(self),
        }
    }
}

impl Default for HacspecArgs {
    fn default() -> Self {
        HacspecArgs {
            output_filename: None,
            output_directory: None,
            output_type: None,
            vc_init: false,
            vc_update: false,
            vc_dir: None,
            input_filename: None,
            crate_name: None,
            cargo_extra_flags: vec![],
        }
    }
}

impl HacspecArgs {
    pub fn to_args(&self) -> Vec<String> {
        let flags = vec![
            ("-o", &self.output_filename),
            ("-d", &self.output_directory),
            ("-e", &self.output_type),
            ("-f", &self.input_filename),
        ];

        flags
            .into_iter()
            .flat_map(|(flag, val)| val.as_ref().map(|val| [flag.to_string(), val.clone()]))
            .flatten()
            // add crate name, if any
            .chain(self.crate_name.clone().into_iter())
            // // appends extra flags
            .chain(std::iter::once("--".to_string()))
            .chain(self.cargo_extra_flags.clone().into_iter())
            .collect()
    }
}
