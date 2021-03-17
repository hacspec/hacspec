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
pub mod tls13handshake;
use tls13handshake::*;
pub mod tls13record;
use tls13record::*;
pub mod tls13api;
use tls13api::*;

// Import hacspec and all needed definitions.
use hacspec_lib::*;
use rand::*;
use std::env;
use std::time::Duration;

// A Simple TLS 1.3 HTTP Client Implementation
// It connects to a give host at port 443, sends an HTTP "GET /", and prints a prefix of the HTTP response
// WARNING: This code is not in hacspec since it need to use TCP etc.

use hex::*;
use std::io;
use std::io::prelude::*;
use std::net::TcpStream;
use std::str;


fn read_bytes(stream: &mut TcpStream, buf: &mut [u8], nbytes: usize) -> Res<usize> {
    match stream.read(&mut buf[..]) {
        Ok(len) => {
            if len >= nbytes {
                Ok(len - nbytes)
            } else {
                read_bytes(stream, &mut buf[len..], nbytes - len)
            }
        }
        Err(_) => Err(parse_failed),
    }
}

fn read_record(stream: &mut TcpStream, buf: &mut [u8]) -> Res<usize> {
    let mut b: [u8; 5] = [0; 5];
    let mut len = 0;
    while (len < 5) {
        len = stream.peek(&mut b).unwrap();
    }
    let l0 = b[3] as usize;
    let l1 = b[4] as usize;
    let len = l0 * 256 + l1;
    if len + 5 > buf.len() {
        Err(parse_failed)
    } else {
        let extra = read_bytes(stream, &mut buf[0..len + 5], len + 5)?;
        if extra > 0 {
            Err(parse_failed)
        } else {
            Ok(len + 5)
        }
    }
}

fn get_handshake_message(stream: &mut TcpStream, buf: &mut [u8]) -> Res<(Bytes, usize)> {
    let len = read_record(stream, buf)?;
    let rec = Bytes::from_public_slice(&buf[0..len]);
    let (msg, len_) = check_handshake_record(&rec)?;
    check_eq_size(len, len_)?;
    Ok((msg, len))
}

fn put_record(stream: &mut TcpStream, rec: &Bytes) -> Res<()> {
    let wire = hex::decode(&rec.to_hex()).expect("Record Decoding Failed");
    match stream.write(&wire) {
        Err(_) => Err(parse_failed),
        Ok(len) => {
            if len < wire.len() {
                Err(parse_failed)
            } else {
                Ok(())
            }
        }
    }
}

fn get_ccs_message(stream: &mut TcpStream, buf: &mut [u8]) -> Res<()> {
    let len = read_record(stream, buf)?;
    if len == 6
        && buf[0] == 0x14
        && buf[1] == 0x03
        && buf[2] == 0x03
        && buf[3] == 0x00
        && buf[4] == 0x01
        && buf[5] == 0x01
    {
        Ok(())
    } else {
        Err(parse_failed)
    }
}

fn put_ccs_message(stream: &mut TcpStream) -> Res<()> {
    let ccs_rec = Bytes::from_hex("140303000101");
    put_record(stream, &ccs_rec)
}

fn decrypt_handshake_flight(
    stream: &mut TcpStream,
    buf: &mut [u8],
    cipherH: DuplexCipherStateH,
) -> Res<(Bytes, DuplexCipherStateH)> {
    let mut payload = Bytes::new(0);
    let mut finished = false;
    let mut cipherH = cipherH;
    while !finished {
        let len = read_record(stream, buf)?;
        let rec = Bytes::from_public_slice(&buf[0..len]);
        let (plain, cip) = decrypt_handshake(&rec, cipherH)?;
        payload = payload.concat(&plain);
        cipherH = cip;
        finished = find_handshake_message(ty_finished,&payload);
    }
    Ok((payload, cipherH))
}

fn decrypt_tickets_and_data(
    stream: &mut TcpStream,
    buf: &mut [u8],
    cipher1: DuplexCipherState1,
) -> Res<(Bytes, DuplexCipherState1)> {
    let mut payload = Bytes::new(0);
    let mut data = false;
    let mut cipher1 = cipher1;
    while !data {
        let len = read_record(stream, buf)?;
        let rec = Bytes::from_public_slice(&buf[0..len]);
        let (ct, pl, cip) = decrypt_data_or_hs(&rec, cipher1)?;
        payload = pl;
        cipher1 = cip;
        if eq1(ct, U8(ct_app_data)) {
            data = true;
        } else {
            println!("Received Session Ticket");
        }
    }
    Ok((payload, cipher1))
}

const algs: ALGS = ALGS(
    HashAlgorithm::SHA256,
    AEADAlgorithm::CHACHA20_POLY1305,
    //    SignatureScheme::ECDSA_SECP256r1_SHA256,
    SignatureScheme::RSA_PSS_RSAE_SHA256,
    NamedGroup::X25519,
    false,
    false,
);

pub fn tls13client(host: &str, port: &str) -> Res<()> {
    let mut entropy = [0 as u8; 64];
    let d = Duration::new(1, 0);
    thread_rng().fill(&mut entropy);
    let ent_c = Entropy::from_public_slice(&entropy);
    let sni = Bytes::from_public_slice(&host.as_bytes());
    let http_get_str = format!("GET / HTTP/1.1\r\nHost: {}\r\n\r\n", host);
    let http_get = Bytes::from_public_slice(http_get_str.as_bytes());

    /* Initiate TCP Connection */
    let addr = [host, port].join(":");
    let mut stream = TcpStream::connect(&addr).unwrap();
    stream
        .set_read_timeout(Some(d))
        .expect("set_read_timeout call failed");
    println!("Initiating connection to {}", addr);

    /* Initialize TLS 1.3. Client */
    let (ch, cstate, _) = client_init(algs, &sni, None, None, ent_c)?;
    let mut ch_rec = handshake_record(&ch)?;
    ch_rec[2] = U8(0x01);
    put_record(&mut stream, &ch_rec)?;

    /* Process Server Response  */
    let mut in_buf = [0; 4096];
    let (sh, len1_) = get_handshake_message(&mut stream, &mut in_buf)?;
    let (cstate, cipherH) = client_set_params(&sh, cstate)?;
    get_ccs_message(&mut stream, &mut in_buf)?;
    let (sf, cipherH) = decrypt_handshake_flight(&mut stream, &mut in_buf, cipherH)?;
    let (cf, cstate, cipher1) = client_finish(&sf, cstate)?;

    /* Complete Connection */
    put_ccs_message(&mut stream)?;
    let (cf_rec, cipherH) = encrypt_handshake(&cf, 0, cipherH)?;
    put_record(&mut stream, &cf_rec)?;
    println!("Connected to {}:443", host);
    /* Send HTTP GET  */
    let (ap, cipher1) = encrypt_data(&http_get, 0, cipher1)?;
    put_record(&mut stream, &ap)?;
    println!("Sent HTTP GET to {}:443", host);

    /* Process HTTP Response */
    let (http_resp, cipher1) = decrypt_tickets_and_data(&mut stream, &mut in_buf, cipher1)?;
    let html_by = hex::decode(&http_resp.to_hex()).expect("Decoding HTTP Response failed");
    let html = str::from_utf8(&html_by).unwrap();
    println!("Received HTTP Response from {}\n\n{}", host, html);
    Ok(())
}

fn main() {
    let args: Vec<String> = env::args().collect();
    let host = if args.len() <= 1 {
        "www.google.com"
    } else {
        &args[1]
    };
    let port = if args.len() <= 2 { "443" } else { &args[2] };
    match tls13client(host, port) {
        Err(x) => {
            println!("Connection to {} failed\n", host);
        }
        Ok(x) => {
            println!("Connection to {} succeeded\n", host);
        }
    }
}
