mod util;
use clap::Parser;
use std::process::Command;

fn main() {
    let args = util::Args::parse();
    let util::HacspecArgs {
        cargo_extra_flags,
        crate_name,
        ..
    } = args.clone().into();

    let exit_status = Command::new("cargo")
        .arg("build")
        .args(match crate_name {
            Some(krate) => vec!["-p".to_string(), krate.clone()],
            _ => vec![],
        })
        .args(cargo_extra_flags)
        .env(
            "RUSTC_WORKSPACE_WRAPPER",
            std::env::current_exe()
                .ok()
                .as_ref()
                .and_then(|p| p.parent())
                .map(|p| format!("{}/hacspec-driver", p.display()))
                .unwrap_or("hacspec-driver".to_string()),
        )
        .env(util::HACSPEC_ARGS, serde_json::to_string(&args).unwrap())
        .spawn()
        .expect("could not run cargo")
        .wait()
        .expect("failed to wait for cargo?");

    std::process::exit(exit_status.code().unwrap_or(-1));
}
