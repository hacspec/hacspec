#![allow(dead_code)]

use hacspec::prelude::*;

pub(crate) fn get_expected(op: &'static str, a: &String, b: &String) -> String {
    let expected = std::process::Command::new("python")
        .args(&["tests/math_helper.py", a, op, b])
        .output()
        .expect("failed to execute python test helper");
    let expected = String::from_utf8_lossy(&expected.stdout)
        .replace("\n", "")
        .replace("\r", "");
    // Python2 appends an L.
    expected.replace("L", "")
}

pub(crate) fn random_hex_string(len: usize) -> String {
    const HEX_CHARS: [char; 16] = [
        '0', '1', '2', '3', '4', '5', '6', '7', '8', '9', 'a', 'b', 'c', 'd', 'e', 'f',
    ];

    let mut res = "".to_string();
    let mut rng = rand::thread_rng();
    for _ in 0..len {
        res.push(HEX_CHARS[rng.gen_range(0, HEX_CHARS.len())]);
    }
    res = res.trim_start_matches('0').to_string();
    if res.len() == 0 {
        res.push('0');
    }
    let mut start = String::from("0x");
    start.push_str(&res);
    start
}
