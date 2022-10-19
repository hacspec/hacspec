mod util;
use clap::Parser;
use std::process::Command;

fn main() {
    let args = util::Args::parse();

    Command::new("cargo")
        .arg("build")
        .args(match &args.crate_name {
            Some(krate) => vec!["-p".to_string(), krate.clone()],
            _ => vec![],
        })
        .args(&args.cargo_extra_flags)
        .env("RUSTC_WORKSPACE_WRAPPER", "hacspec-driver")
        .env("HACSPEC_ARGS", serde_json::to_string(&args).unwrap())
        .spawn()
        .unwrap();
}
