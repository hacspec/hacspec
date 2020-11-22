use std::env;

fn main() {
    let mut sysroot = std::process::Command::new("rustc")
        .arg("--print")
        .arg("sysroot")
        .output()
        .ok()
        .and_then(|out| String::from_utf8(out.stdout).ok())
        .expect("Couldn't get sysroot");
    sysroot.pop(); // get rid of line break
    let sysroot_lib = sysroot + "/lib";

    let hacspec_out = std::process::Command::new("hacspec")
        .env("DYLD_LIBRARY_PATH", sysroot_lib)
        .args(env::args().skip(1))
        .status()
        .expect("Couldn't run hacspec");
    println!("hacspec out: {}", hacspec_out);
}
