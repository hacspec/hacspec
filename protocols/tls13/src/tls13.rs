#![allow(dead_code)]
#![allow(unused_variables)]
#![allow(non_camel_case_types)]
#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(unused_imports)]
#![allow(unused_parens)]

pub mod tls13formats;
use tls13formats::*;
pub mod cryptolib;
use cryptolib::*;
pub mod tls13record;
use tls13record::*;
pub mod tls13handshake;
use tls13handshake::*;
pub mod tls13api;
use tls13api::*;

// Import hacspec and all needed definitions.
use hacspec_lib::*;
use rand::*;
use std::env;

// A Simple TLS 1.3 HTTP Client Implementation
// It connects to a give host at port 443, sends an HTTP "GET /", and prints a prefix of the HTTP response
// WARNING: This code is not in hacspec since it need to use TCP etc.

use std::io;
use std::io::prelude::*;
use std::net::TcpStream;
use std::str;
use hex::*;

const algs: ALGS = ALGS(
    HashAlgorithm::SHA256,
    AEADAlgorithm::CHACHA20_POLY1305,
    SignatureScheme::ECDSA_SECP256r1_SHA256,
    NamedGroup::X25519,
    false,
    false,
);

pub fn tls13client(host:&str) -> Res<()> {
    let mut entropy = [0 as u8;64];
    thread_rng().fill(&mut entropy);
    let ent_c = Entropy::from_public_slice(&entropy);
    let sni = Bytes::from_public_slice(&host.as_bytes());
    let http_get_str = format!("GET / HTTP/1.1\r\nHost: {}\r\n\r\n",host);
    let http_get = Bytes::from_public_slice(http_get_str.as_bytes());
    let (ch,cstate) = client_init(algs,&sni,None,None,ent_c)?;
    let addr = [host,"443"].join(":");
    let mut stream = TcpStream::connect(&addr).unwrap();
    println!("Initiating connection to {}", addr);
    let ch_wire = hex::decode(&ch.to_hex()).expect("Client Hello Decoding Failed");
    let len = stream.write(&ch_wire).unwrap();
    if len != ch_wire.len() {println!("TCP send failed to send full client hello"); return Err(0);};
    let mut in_buf = [0; 4096];
    let len0 = stream.read(&mut in_buf).unwrap();
    let len1 = len0 + stream.read(&mut in_buf[len0..4096]).unwrap();
//   let len2 = len1 + stream.read(&mut in_buf[len1..4096]).unwrap();
    let len2 = len1;
    if len2 <= 0 {println!("Received 0 bytes from {}",host);return Err(0)};
    let sf = Bytes::from_public_slice(&in_buf[0..len2]);
    let (cf,cstate) = client_finish(&sf,cstate)?;
    println!("Connected to {}:443", host);
    let ccs = hex::decode("140303000101").expect("CCS Decoding failed");
    let _ = stream.write(&ccs);
    let cf_wire = hex::decode(&cf.to_hex()).expect("Client Finished Decoding Failed");
    let len = stream.write(&cf_wire).unwrap();
    if len != cf_wire.len() {println!("TCP send failed to send full client finished"); return Err(0);};
    let (ap,cstate) = client_send1(cstate,&http_get)?;
    let http_get_wire = hex::decode(&ap.to_hex()).expect("HTTP GET Decoding Failed");
    let len = stream.write(&http_get_wire).unwrap();
    println!("Sent HTTP GET to {}:443", host);
    if len != http_get_wire.len() {println!("TCP send failed to send full HTTP GET"); return Err(0);};
    let len0 = stream.read(&mut in_buf).unwrap();
 //   let len1 = len0 + stream.read(&mut in_buf[len0..4096]).unwrap();
 //   let len2 = len1 + stream.read(&mut in_buf[len1..4096]).unwrap();
    let len2 = len0;
    if len2 <= 0 {println!("Received 0 bytes from {}",host);return Err(0)};
    let http_resp_wire = Bytes::from_public_slice(&in_buf[0..len2]);
    let (http_resp,cstate) = client_recv1(cstate,&http_resp_wire)?;
    let html_by = hex::decode(&http_resp.to_hex()).expect("Decoding HTTP Response failed");
    let html = str::from_utf8(&html_by).unwrap();
    println!("Received HTTP Response from {}\n\n{}", host, html);
    Ok(())
}

fn main () {
    let args: Vec<String> = env::args().collect();
    let target = if args.len() <= 1 {"www.google.com"} else {&args[1]};
    match tls13client(target) {
        Err(x) => {println!("Connection to {} failed\n",target);}
        Ok(x) => {println!("Connection to {} succeeded\n",target);}
    }
}