use hacspec_dev::prelude::*;
use hacspec_lib::prelude::*;

use bertie::*;
use bertie::tls13formats::*;
use bertie::tls13handshake::*;
use bertie::tls13record::*;
use bertie::cryptolib::*;
use bertie::cryptolib::HashAlgorithm::*;
use bertie::cryptolib::AEADAlgorithm::*;
use bertie::cryptolib::NamedGroup::*;
use bertie::cryptolib::SignatureScheme::*;

// These are the sample TLS 1.3 traces taken from RFC 8448
use bertie::cryptolib::*;

fn load_hex(s:&str) -> Bytes {
    let s_no_ws : String = s.split_whitespace().collect();
    (Bytes::from_hex(&s_no_ws))
}

/* Server's RSA Private Key */ 
const modulus : &str = "b4 bb 49 8f 82 79 30 3d 98 08 36 39 9b 36 c6 98 8c
0c 68 de 55 e1 bd b8 26 d3 90 1a 24 61 ea fd 2d e4 9a 91 d0 15 ab
bc 9a 95 13 7a ce 6c 1a f1 9e aa 6a f9 8c 7c ed 43 12 09 98 e1 87
a8 0e e0 cc b0 52 4b 1b 01 8c 3e 0b 63 26 4d 44 9a 6d 38 e2 2a 5f
da 43 08 46 74 80 30 53 0e f0 46 1c 8c a9 d9 ef bf ae 8e a6 d1 d0
3e 2b d1 93 ef f0 ab 9a 80 02 c4 74 28 a6 d3 5a 8d 88 d7 9f 7f 1e
3f";

const public_exponent: &str = "01 00 01";

const private_exponent: &str = "04 de a7 05 d4 3a 6e a7 20 9d d8 07 21 11 a8 3c 81
e3 22 a5 92 78 b3 34 80 64 1e af 7c 0a 69 85 b8 e3 1c 44 f6 de 62
e1 b4 c2 30 9f 61 26 e7 7b 7c 41 e9 23 31 4b bf a3 88 13 05 dc 12
17 f1 6c 81 9c e5 38 e9 22 f3 69 82 8d 0e 57 19 5d 8c 84 88 46 02
07 b2 fa a7 26 bc f7 08 bb d7 db 7f 67 9f 89 34 92 fc 2a 62 2e 08
97 0a ac 44 1c e4 e0 c3 08 8d f2 5a e6 79 23 3d f8 a3 bd a2 ff 99
41";

const prime1: &str = "e4 35 fb 7c c8 37 37 75 6d ac ea 96 ab 7f 59 a2 cc 10 69 db
7d eb 19 0e 17 e3 3a 53 2b 27 3f 30 a3 27 aa 0a aa bc 58 cd 67 46
6a f9 84 5f ad c6 75 fe 09 4a f9 2c 4b d1 f2 c1 bc 33 dd 2e 05 15";

const prime2: &str = "ca bd 3b c0 e0 43 86 64 c8 d4 cc 9f 99 97 7a 94 d9 bb fe ad
8e 43 87 0a ba e3 f7 eb 8b 4e 0e ee 8a f1 d9 b4 71 9b a6 19 6c f2
cb ba ee eb f8 b3 49 0a fe 9e 9f fa 74 a8 8a a5 1f c6 45 62 93 03";

const exponent1: &str = "3f 57 34 5c 27 fe 1b 68 7e 6e 76 16 27 b7 8b 1b 82 64 33
dd 76 0f a0 be a6 a6 ac f3 94 90 aa 1b 47 cd a4 86 9d 68 f5 84 dd
5b 50 29 bd 32 09 3b 82 58 66 1f e7 15 02 5e 5d 70 a4 5a 08 d3 d3
19";

const exponent2: &str = "18 3d a0 13 63 bd 2f 28 85 ca cb dc 99 64 bf 47 64 f1 51
76 36 f8 64 01 28 6f 71 89 3c 52 cc fe 40 a6 c2 3d 0d 08 6b 47 c6
fb 10 d8 fd 10 41 e0 4d ef 7e 9a 40 ce 95 7c 41 77 94 e1 04 12 d1
39";

const coefficient: &str = "83 9c a9 a0 85 e4 28 6b 2c 90 e4 66 99 7a 2c 68 1f 21
33 9a a3 47 78 14 e4 de c1 18 33 05 0e d5 0d d1 3c c0 38 04 8a 43
c5 9b 2a cc 41 68 89 c0 37 66 5f e5 af a6 05 96 9f 8c 01 df a5 ca
96 9d";

// ECDH keys

const client_x25519_priv: &str = "49 af 42 ba 7f 79 94 85 2d 71 3e f2 78
4b cb ca a7 91 1d e2 6a dc 56 42 cb 63 45 40 e7 ea 50 05";

const client_x25519_pub: &str = "99 38 1d e5 60 e4 bd 43 d2 3d 8e 43 5a 7d
ba fe b3 c0 6e 51 c1 3c ae 4d 54 13 69 1e 52 9a af 2c";

const server_x25519_priv: &str = "b1 58 0e ea df 6d d5 89 b8 ef 4f 2d 56
52 57 8c c8 10 e9 98 01 91 ec 8d 05 83 08 ce a2 16 a2 1e";

const server_x25519_pub : &str = "c9 82 88 76 11 20 95 fe 66 76 2b db f7 c6
72 e1 56 d6 cc 25 3b 83 3d f1 dd 69 b1 b0 4e 75 1f 0f";

//Simple 1-RTT Handshake Transcript

const client_hello: &str = "01 00 00 c0 03 03 cb 34 ec b1 e7 81 63
ba 1c 38 c6 da cb 19 6a 6d ff a2 1a 8d 99 12 ec 18 a2 ef 62 83
02 4d ec e7 00 00 06 13 01 13 03 13 02 01 00 00 91 00 00 00 0b
00 09 00 00 06 73 65 72 76 65 72 ff 01 00 01 00 00 0a 00 14 00
12 00 1d 00 17 00 18 00 19 01 00 01 01 01 02 01 03 01 04 00 23
00 00 00 33 00 26 00 24 00 1d 00 20 99 38 1d e5 60 e4 bd 43 d2
3d 8e 43 5a 7d ba fe b3 c0 6e 51 c1 3c ae 4d 54 13 69 1e 52 9a
af 2c 00 2b 00 03 02 03 04 00 0d 00 20 00 1e 04 03 05 03 06 03
02 03 08 04 08 05 08 06 04 01 05 01 06 01 02 01 04 02 05 02 06
02 02 02 00 2d 00 02 01 01 00 1c 00 02 40 01";

const client_hello_record: &str = "16 03 01 00 c4 01 00 00 c0 03 03 cb
34 ec b1 e7 81 63 ba 1c 38 c6 da cb 19 6a 6d ff a2 1a 8d 99 12
ec 18 a2 ef 62 83 02 4d ec e7 00 00 06 13 01 13 03 13 02 01 00
00 91 00 00 00 0b 00 09 00 00 06 73 65 72 76 65 72 ff 01 00 01
00 00 0a 00 14 00 12 00 1d 00 17 00 18 00 19 01 00 01 01 01 02
01 03 01 04 00 23 00 00 00 33 00 26 00 24 00 1d 00 20 99 38 1d
e5 60 e4 bd 43 d2 3d 8e 43 5a 7d ba fe b3 c0 6e 51 c1 3c ae 4d
54 13 69 1e 52 9a af 2c 00 2b 00 03 02 03 04 00 0d 00 20 00 1e
04 03 05 03 06 03 02 03 08 04 08 05 08 06 04 01 05 01 06 01 02
01 04 02 05 02 06 02 02 02 00 2d 00 02 01 01 00 1c 00 02 40 01";

const server_hello : &str = "02 00 00 56 03 03 a6 af 06 a4 12 18 60
dc 5e 6e 60 24 9c d3 4c 95 93 0c 8a c5 cb 14 34 da c1 55 77 2e
d3 e2 69 28 00 13 01 00 00 2e 00 33 00 24 00 1d 00 20 c9 82 88
76 11 20 95 fe 66 76 2b db f7 c6 72 e1 56 d6 cc 25 3b 83 3d f1
dd 69 b1 b0 4e 75 1f 0f 00 2b 00 02 03 04";

const server_hello_record : &str = "16 03 03 00 5a 02 00 00 56 03 03 a6
af 06 a4 12 18 60 dc 5e 6e 60 24 9c d3 4c 95 93 0c 8a c5 cb 14
34 da c1 55 77 2e d3 e2 69 28 00 13 01 00 00 2e 00 33 00 24 00
1d 00 20 c9 82 88 76 11 20 95 fe 66 76 2b db f7 c6 72 e1 56 d6
cc 25 3b 83 3d f1 dd 69 b1 b0 4e 75 1f 0f 00 2b 00 02 03 04";

const encrypted_extensions : & str = "08 00 00 24 00 22 00 0a 00 14 00
12 00 1d 00 17 00 18 00 19 01 00 01 01 01 02 01 03 01 04 00 1c
00 02 40 01 00 00 00 00";

const server_certificate : & str = "0b 00 01 b9 00 00 01 b5 00 01 b0 30 82
01 ac 30 82 01 15 a0 03 02 01 02 02 01 02 30 0d 06 09 2a 86 48
86 f7 0d 01 01 0b 05 00 30 0e 31 0c 30 0a 06 03 55 04 03 13 03
72 73 61 30 1e 17 0d 31 36 30 37 33 30 30 31 32 33 35 39 5a 17
0d 32 36 30 37 33 30 30 31 32 33 35 39 5a 30 0e 31 0c 30 0a 06
03 55 04 03 13 03 72 73 61 30 81 9f 30 0d 06 09 2a 86 48 86 f7
0d 01 01 01 05 00 03 81 8d 00 30 81 89 02 81 81 00 b4 bb 49 8f
82 79 30 3d 98 08 36 39 9b 36 c6 98 8c 0c 68 de 55 e1 bd b8 26
d3 90 1a 24 61 ea fd 2d e4 9a 91 d0 15 ab bc 9a 95 13 7a ce 6c
1a f1 9e aa 6a f9 8c 7c ed 43 12 09 98 e1 87 a8 0e e0 cc b0 52
4b 1b 01 8c 3e 0b 63 26 4d 44 9a 6d 38 e2 2a 5f da 43 08 46 74
80 30 53 0e f0 46 1c 8c a9 d9 ef bf ae 8e a6 d1 d0 3e 2b d1 93
ef f0 ab 9a 80 02 c4 74 28 a6 d3 5a 8d 88 d7 9f 7f 1e 3f 02 03
01 00 01 a3 1a 30 18 30 09 06 03 55 1d 13 04 02 30 00 30 0b 06
03 55 1d 0f 04 04 03 02 05 a0 30 0d 06 09 2a 86 48 86 f7 0d 01
01 0b 05 00 03 81 81 00 85 aa d2 a0 e5 b9 27 6b 90 8c 65 f7 3a
72 67 17 06 18 a5 4c 5f 8a 7b 33 7d 2d f7 a5 94 36 54 17 f2 ea
e8 f8 a5 8c 8f 81 72 f9 31 9c f3 6b 7f d6 c5 5b 80 f2 1a 03 01
51 56 72 60 96 fd 33 5e 5e 67 f2 db f1 02 70 2e 60 8c ca e6 be
c1 fc 63 a4 2a 99 be 5c 3e b7 10 7c 3c 54 e9 b9 eb 2b d5 20 3b
1c 3b 84 e0 a8 b2 f7 59 40 9b a3 ea c9 d9 1d 40 2d cc 0c c8 f8
96 12 29 ac 91 87 b4 2b 4d e1 00 00";

const server_certificate_verify : & str = "0f 00 00 84 08 04 00 80 5a 74 7c
5d 88 fa 9b d2 e5 5a b0 85 a6 10 15 b7 21 1f 82 4c d4 84 14 5a
b3 ff 52 f1 fd a8 47 7b 0b 7a bc 90 db 78 e2 d3 3a 5c 14 1a 07
86 53 fa 6b ef 78 0c 5e a2 48 ee aa a7 85 c4 f3 94 ca b6 d3 0b
be 8d 48 59 ee 51 1f 60 29 57 b1 54 11 ac 02 76 71 45 9e 46 44
5c 9e a5 8c 18 1e 81 8e 95 b8 c3 fb 0b f3 27 84 09 d3 be 15 2a
3d a5 04 3e 06 3d da 65 cd f5 ae a2 0d 53 df ac d4 2f 74 f3";

const server_finished : &str = "14 00 00 20 9b 9b 14 1d 90 63 37 fb d2 cb
dc e7 1d f4 de da 4a b4 2c 30 95 72 cb 7f ff ee 54 54 b7 8f 07
18";

const server_finished_record : &str = "17 03 03 02 a2 d1 ff 33 4a 56 f5 bf
f6 59 4a 07 cc 87 b5 80 23 3f 50 0f 45 e4 89 e7 f3 3a f3 5e df
78 69 fc f4 0a a4 0a a2 b8 ea 73 f8 48 a7 ca 07 61 2e f9 f9 45
cb 96 0b 40 68 90 51 23 ea 78 b1 11 b4 29 ba 91 91 cd 05 d2 a3
89 28 0f 52 61 34 aa dc 7f c7 8c 4b 72 9d f8 28 b5 ec f7 b1 3b
d9 ae fb 0e 57 f2 71 58 5b 8e a9 bb 35 5c 7c 79 02 07 16 cf b9
b1 18 3e f3 ab 20 e3 7d 57 a6 b9 d7 47 76 09 ae e6 e1 22 a4 cf
51 42 73 25 25 0c 7d 0e 50 92 89 44 4c 9b 3a 64 8f 1d 71 03 5d
2e d6 5b 0e 3c dd 0c ba e8 bf 2d 0b 22 78 12 cb b3 60 98 72 55
cc 74 41 10 c4 53 ba a4 fc d6 10 92 8d 80 98 10 e4 b7 ed 1a 8f
d9 91 f0 6a a6 24 82 04 79 7e 36 a6 a7 3b 70 a2 55 9c 09 ea d6
86 94 5b a2 46 ab 66 e5 ed d8 04 4b 4c 6d e3 fc f2 a8 94 41 ac
66 27 2f d8 fb 33 0e f8 19 05 79 b3 68 45 96 c9 60 bd 59 6e ea
52 0a 56 a8 d6 50 f5 63 aa d2 74 09 96 0d ca 63 d3 e6 88 61 1e
a5 e2 2f 44 15 cf 95 38 d5 1a 20 0c 27 03 42 72 96 8a 26 4e d6
54 0c 84 83 8d 89 f7 2c 24 46 1a ad 6d 26 f5 9e ca ba 9a cb bb
31 7b 66 d9 02 f4 f2 92 a3 6a c1 b6 39 c6 37 ce 34 31 17 b6 59
62 22 45 31 7b 49 ee da 0c 62 58 f1 00 d7 d9 61 ff b1 38 64 7e
92 ea 33 0f ae ea 6d fa 31 c7 a8 4d c3 bd 7e 1b 7a 6c 71 78 af
36 87 90 18 e3 f2 52 10 7f 24 3d 24 3d c7 33 9d 56 84 c8 b0 37
8b f3 02 44 da 8c 87 c8 43 f5 e5 6e b4 c5 e8 28 0a 2b 48 05 2c
f9 3b 16 49 9a 66 db 7c ca 71 e4 59 94 26 f7 d4 61 e6 6f 99 88
2b d8 9f c5 08 00 be cc a6 2d 6c 74 11 6d bd 29 72 fd a1 fa 80
f8 5d f8 81 ed be 5a 37 66 89 36 b3 35 58 3b 59 91 86 dc 5c 69
18 a3 96 fa 48 a1 81 d6 b6 fa 4f 9d 62 d5 13 af bb 99 2f 2b 99
2f 67 f8 af e6 7f 76 91 3f a3 88 cb 56 30 c8 ca 01 e0 c6 5d 11
c6 6a 1e 2a c4 c8 59 77 b7 c7 a6 99 9b bf 10 dc 35 ae 69 f5 51
56 14 63 6c 0b 9b 68 c1 9e d2 e3 1c 0b 3b 66 76 30 38 eb ba 42
f3 b3 8e dc 03 99 f3 a9 f2 3f aa 63 97 8c 31 7f c9 fa 66 a7 3f
60 f0 50 4d e9 3b 5b 84 5e 27 55 92 c1 23 35 ee 34 0b bc 4f dd
d5 02 78 40 16 e4 b3 be 7e f0 4d da 49 f4 b4 40 a3 0c b5 d2 af
93 98 28 fd 4a e3 79 4e 44 f9 4d f5 a6 31 ed e4 2c 17 19 bf da
bf 02 53 fe 51 75 be 89 8e 75 0e dc 53 37 0d 2b";

const client_finished : &str = "14 00 00 20 a8 ec 43 6d 67 76 34 ae 52 5a
c1 fc eb e1 1a 03 9e c1 76 94 fa c6 e9 85 27 b6 42 f2 ed d5 ce
61";

const client_finished_record : &str = "17 03 03 00 35 75 ec 4d c2 38 cc e6
0b 29 80 44 a7 1e 21 9c 56 cc 77 b0 51 7f e9 b9 3c 7a 4b fc 44
d8 7f 38 f8 03 38 ac 98 fc 46 de b3 84 bd 1c ae ac ab 68 67 d7
26 c4 05 46";

const algs : ALGS = ALGS(SHA256,AES_128_GCM,RSA_PSS_RSAE_SHA256,X25519,false,false);



#[test]
fn test_parse_client_hello() {
    let ch:Bytes = load_hex(client_hello);
 //   let algs = ALGS(SHA256,CHACHA20_POLY1305,ECDSA_SECP256r1_SHA256,X25519,false,false);
    let res = parse_client_hello(&algs, &ch);
    let b = res.is_ok();
    match res{
	    Err(x) => {println!("Error: {}",x);},
	    Ok((cr,sid,sn,gx,tkto,bo,l)) => {
            println!("Parsed CH!");
            println!("cr: {}", cr.to_hex());
            println!("sid: {}", sid.to_hex());
            println!("sn: {}", sn.to_hex());
            println!("gx: {}", gx.to_hex());
            println!("trunc_len: {}", l);}
    }
    assert!(b);
}

#[test]
fn test_parse_client_hello_record() {
    let ch:Bytes = load_hex(client_hello_record);
 //   let algs = ALGS(SHA256,CHACHA20_POLY1305,ECDSA_SECP256r1_SHA256,X25519,false,false);
    let mut b = true;
    match check_handshake_record(&ch) {
        Err(x) => {println!("Error: {}",x);b = false;},
        Ok ((hs,len)) => {
            match parse_client_hello(&algs, &ch) {
                Err(x) => {println!("Error: {}",x);b = false;},
                Ok((cr,sid,sn,gx,tkto,bo,l)) => {
                    println!("Parsed CH!");
                    println!("cr: {}", cr.to_hex());
                    println!("sid: {}", sid.to_hex());
                    println!("sn: {}", sn.to_hex());
                    println!("gx: {}", gx.to_hex());
                    println!("trunc_len: {}", l);}
            }}
    }
    assert!(true);
}

#[test]
fn test_parse_server_hello() {
    let sh:Bytes = load_hex(server_hello);
 //   let algs = ALGS(SHA256,AES_128_GCM,ECDSA_SECP256r1_SHA256,X25519,false,false);
    let res = parse_server_hello(&algs, &sh);
    let b = res.is_ok();
    match res {
	    Err(x) => {println!("Error: {}",x);},
	    Ok((sr,gy)) => {
            println!("Parsed SH!");
            println!("sr: {}", sr.to_hex());
            println!("gy: {}", gy.to_hex());}
    }
    assert!(b);
}

#[test]
fn test_parse_encrypted_extensions() {
    let ee:Bytes = load_hex(encrypted_extensions);
    let res = parse_encrypted_extensions(&algs, &ee);
    let b = res.is_ok();
    match res {
	    Err(x) => {println!("Error: {}",x);},
	    Ok(()) => {println!("Parsed EE!");}
        }
    assert!(b);
    }

#[test]
fn test_parse_server_certificate() {
    let sc:Bytes = load_hex(server_certificate);
    let res = parse_server_certificate(&algs, &sc);
    let b = res.is_ok();
    match res {
	    Err(x) => {println!("Error: {}",x);},
	    Ok(_) => {println!("Parsed SC!");}
        }
    assert!(b);
    }

#[test]
fn test_parse_server_certificate_verify() {
    let cv:Bytes = load_hex(server_certificate_verify);  
    let res = parse_certificate_verify(&algs, &cv);
    let b = res.is_ok();
    match res {
	    Err(x) => {println!("Error: {}",x);},
	    Ok(_) => {println!("Parsed CV!");}
        }
    assert!(b);
    }

#[test]
fn test_parse_server_finished() {
        let sf:Bytes = load_hex(server_finished);  
        let res = parse_finished(&algs, &sf);
        let b = res.is_ok();
        match res {
            Err(x) => {println!("Error: {}",x);},
            Ok(_) => {println!("Parsed SF!");}
            }
        assert!(b);
        }

#[test]
fn test_parse_client_finished() {
        let cf:Bytes = load_hex(client_finished);  
        let res = parse_finished(&algs, &cf);
        let b = res.is_ok();
        match res {
            Err(x) => {println!("Error: {}",x);},
            Ok(_) => {println!("Parsed CF!");}
            }
        assert!(b);
        }