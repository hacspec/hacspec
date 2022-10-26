use glob::glob;
use libtest_mimic::{Arguments, Failed, Trial};
use std::fmt;
use std::path::PathBuf;
mod utils;
use std::fs;
use std::{env, process::Command};
use utils::*;

#[derive(Copy, Clone)]
enum Polarity {
    Positive,
    Negative,
}

impl std::convert::Into<bool> for Polarity {
    fn into(self) -> bool {
        match self {
            Self::Positive => true,
            Self::Negative => false,
        }
    }
}
impl std::string::ToString for Polarity {
    fn to_string(&self) -> String {
        match self {
            Self::Positive => "positive".into(),
            Self::Negative => "negative".into(),
        }
    }
}

fn test_command(cmd: &mut Command, kind: Polarity) -> Result<(), Failed> {
    let status = cmd.status().expect("Error running Hacspec");
    if status.success() == <Polarity as Into<_>>::into(kind) {
        Ok(())
    } else {
        Err(Failed::from(status))
    }
}

#[derive(Clone)]
enum TrialKind {
    File,
    Crate,
}
#[derive(Clone)]
struct TrialDesc {
    path: PathBuf, // points either to crate root dir or a file
    polarity: Polarity,
    kind: TrialKind,
    name: String,
}

use phf::{phf_map, phf_set, Map, Set};
static EXPLICIT_BACKENDS: Map<&'static str, Set<&'static str>> = phf_map! {
    "positive/question_mark.rs" => phf_set! {"fst"},
};

impl TrialDesc {
    fn as_command(self, root: PathBuf, extract: Option<&str>) -> Command {
        match (self.kind, extract) {
            (TrialKind::Crate, Some(e)) => {
                let mut cmd = hacspec_command();
                cmd.current_dir(self.path.clone())
                    .args(["-e", e])
                    .arg("--dir")
                    .arg(root.join("extracted").join(self.name.clone()))
                    .arg("--output-filename")
                    .arg(self.name.clone());
                cmd
            }
            (TrialKind::Crate, None) => {
                let mut cmd = hacspec_command();
                cmd.current_dir(self.path.clone());
                cmd
            }
            (TrialKind::File, Some(e)) => hacspec_extract_one_file(
                self.path.clone(),
                self.path.clone().file_stem().unwrap(),
                root.join("extracted"),
                e,
                &None,
            ),
            (TrialKind::File, None) => hacspec_test_one_file(self.path.clone()),
        }
    }
    fn as_trials(&self, root: PathBuf) -> Vec<Trial> {
        let mut mk = |e| -> Trial {
            let d = self.clone();
            let mut cmd = d.clone().as_command(root.clone(), e);
            Trial::test(d.clone().name, move || test_command(&mut cmd, d.polarity)).with_kind(
                match e {
                    Some(e) => e,
                    None => "typecheck",
                },
            )
        };
        std::iter::once(None)
            .chain(
                EXPLICIT_BACKENDS
                    .get(&*self.name)
                    .unwrap_or(&phf_set! {"fst", "v"})
                    .into_iter()
                    .map(Some),
            )
            .map(|e| mk(e.clone().cloned()))
            .collect()
    }
}

fn collect_trials_desc(root: &PathBuf, kind: Polarity) -> Vec<TrialDesc> {
    fn is_rust_module(path: &PathBuf) -> bool {
        path.extension().and_then(|s| s.to_str()).unwrap_or("") == "rs"
    }
    fn aux(root: &PathBuf, subdir: &PathBuf, polarity: Polarity) -> Vec<TrialDesc> {
        if subdir.ends_with(PathBuf::from("target")) {
            return vec![];
        }
        let path = &root.join(subdir);
        let err = &*format!("Could not read path `{}`", path.display());
        let make_desc = |kind| {
            vec![TrialDesc {
                path: path.clone(),
                polarity,
                kind,
                name: format!("{}", subdir.display()),
            }]
        };
        if fs::metadata(path).expect(err).file_type().is_dir() {
            let entries = fs::read_dir(path)
                .expect(err)
                .flat_map(|path| path.ok())
                .collect::<Vec<_>>();
            if entries.iter().any(|f| f.file_name() == "Cargo.toml") {
                make_desc(TrialKind::Crate)
            } else {
                entries
                    .iter()
                    .map(|sub| aux(root, &subdir.join(sub.file_name()), polarity))
                    .flatten()
                    .collect()
            }
        } else if is_rust_module(&path) {
            make_desc(TrialKind::File)
        } else {
            vec![]
        }
    }
    aux(root, &PathBuf::from(kind.to_string()), kind)
}

fn collect_trials(root: &PathBuf, kind: Polarity) -> Vec<Trial> {
    collect_trials_desc(root, kind)
        .iter()
        .cloned()
        .map(|d| d.as_trials(root.clone()))
        .flatten()
        .collect()
    // fn is_rust_module(path: &PathBuf) -> bool {
    //     path.extension().and_then(|s| s.to_str()).unwrap_or("") == "rs"
    // }
    // fn aux(root: &PathBuf, subdir: &PathBuf, kind: Polarity) -> Vec<Trial> {
    //     let directory = &root.join(subdir);
    //     if directory.ends_with(PathBuf::from("target")) {
    //         return vec![];
    //     }
    //     let err = &*format!("Could not read directory `{}`", directory.display());
    //     let subdir_str = subdir.clone().into_os_string().into_string().unwrap();
    //     let test_name = subdir_str.clone();
    //     if fs::metadata(directory).expect(err).file_type().is_dir() {
    //         let entries = fs::read_dir(directory)
    //             .expect(&*format!(
    //                 "Could not read directory `{}`",
    //                 directory.display()
    //             ))
    //             .flat_map(|path| path.ok())
    //             .collect::<Vec<_>>();
    //         if entries.iter().any(|f| f.file_name() == "Cargo.toml") {
    //             let mut cmd = hacspec_command();
    //             let crate_name = directory.file_stem().unwrap();
    //             cmd.current_dir(directory)
    //                 .args(["-e", "fst"])
    //                 .arg("--dir")
    //                 .arg(root.join("extracted").join(crate_name))
    //                 .arg("--output-filename")
    //                 .arg(crate_name);
    //             vec![Trial::test(test_name, move || test_command(&mut cmd, kind))]
    //         } else {
    //             entries
    //                 .iter()
    //                 .map(|sub| aux(root, &subdir.join(sub.file_name()), kind))
    //                 .flatten()
    //                 .collect()
    //         }
    //     } else if is_rust_module(directory) {
    //         let mut cmd = hacspec_extract_one_file(
    //             subdir_str.clone(),
    //             directory.file_stem().unwrap(),
    //             root.join("extracted"),
    //             "fst",
    //             &None,
    //         );
    //         vec![Trial::test(test_name.clone(), move || {
    //             test_command(&mut cmd, kind)
    //         })]
    //     } else {
    //         vec![]
    //     }
    // }
    // aux(root, &PathBuf::from(kind.to_string()), kind)
}

fn main() {
    let test_crate_root = &PathBuf::from(cargo_manifest_dir()).join(TEST_DIRECTORY);
    libtest_mimic::run(
        &Arguments::from_args(),
        collect_trials(test_crate_root, Polarity::Positive)
            .into_iter()
            .chain(collect_trials(test_crate_root, Polarity::Negative).into_iter())
            .collect(),
    )
    .exit();
}
