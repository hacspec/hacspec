mod util;
use clap::Parser;
use std::process::Command;

fn main() {
    let args = util::Args::parse();
    let util::HacspecArgs::Hacspec {
        cargo_extra_flags,
        crate_name,
        ..
    } = &args.hacspec;

    Command::new("cargo")
        .arg("build")
        .args(match crate_name {
            Some(krate) => vec!["-p".to_string(), krate.clone()],
            _ => vec![],
        })
        .args(cargo_extra_flags)
        .env("RUSTC_WORKSPACE_WRAPPER", "hacspec-driver")
        .env("HACSPEC_ARGS", serde_json::to_string(&args).unwrap())
        .spawn()
        .expect("could not run cargo")
        .wait()
        .expect("failed to wait for cargo?");
}
