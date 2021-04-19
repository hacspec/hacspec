#![allow(dead_code)]
#![allow(unused_variables)]
#![allow(non_camel_case_types)]
#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(unused_imports)]
#![allow(unused_parens)]
//#![feature(backtrace)]

pub mod formats;
use formats::*;
pub mod cryptolib;
use cryptolib::*;
pub mod handshake;
use handshake::*;

// Import hacspec and all needed definitions.
use hacspec_lib::*;
use rand::*;
use std::env;
use std::time::Duration;

use hex::*;
use std::io;
use std::io::prelude::*;
use std::net::TcpStream;
use std::str;

fn main() {
    let args: Vec<String> = env::args().collect();
    println!("TODO");
}
