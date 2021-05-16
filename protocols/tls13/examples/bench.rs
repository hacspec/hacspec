// This program does assorted benchmarking of rustls.
//
// Note: we don't use any of the standard 'cargo bench', 'test::Bencher',
// etc. because it's unstable at the time of writing.

// This file is taken from https://github.com/ctz/rustls and adapted to also work
// with our TLS implementation.

use std::fs;
use std::io::{self, Read, Write};
use std::sync::Arc;
use std::time::{Duration, Instant};
use std::{env, io::ErrorKind};

use bertie::{
    client_finish, client_init, client_set_params, decrypt_data, encrypt_data, server_finish,
    server_init, AEADAlgorithm, Algorithms, AppData, Bytes, DuplexCipherState1, Entropy,
    HashAlgorithm, NamedGroup, Random, ServerDB, SignatureScheme, SIGK,
};
use hacspec_dev::prelude::*;
use hacspec_lib::prelude::*;
use rustls::ClientSessionMemoryCache;
use rustls::Connection;
use rustls::NoClientSessionStorage;
use rustls::NoServerSessionStorage;
use rustls::ProtocolVersion;
use rustls::ServerSessionMemoryCache;
use rustls::Ticketer;
use rustls::{self, CipherSuite};
use rustls::{AllowAnyAuthenticatedClient, NoClientAuth, RootCertStore};
use rustls::{ClientConfig, ClientConnection};
use rustls::{ServerConfig, ServerConnection};
use rustls_pemfile;

use webpki;

fn duration_nanos(d: Duration) -> f64 {
    (d.as_secs() as f64) + f64::from(d.subsec_nanos()) / 1e9
}

fn _bench<Fsetup, Ftest, S>(count: usize, name: &'static str, f_setup: Fsetup, f_test: Ftest)
where
    Fsetup: Fn() -> S,
    Ftest: Fn(S),
{
    let mut times = Vec::new();

    for _ in 0..count {
        let state = f_setup();
        let start = Instant::now();
        f_test(state);
        times.push(duration_nanos(Instant::now().duration_since(start)));
    }

    println!("{}", name);
    println!("{:?}", times);
}

fn time<F, I, R>(input: I, mut f: F, acc: &mut f64) -> R
where
    F: FnMut(I) -> R,
{
    let start = Instant::now();
    let r = f(input);
    let end = Instant::now();
    let dur = duration_nanos(end.duration_since(start));
    *acc = *acc + f64::from(dur);
    r
}

fn transfer(left: &mut dyn Connection, right: &mut dyn Connection) -> f64 {
    let mut buf = [0u8; 262144];
    let mut read_time = 0f64;

    loop {
        let mut sz = 0;

        while left.wants_write() {
            let written = left.write_tls(&mut buf[sz..].as_mut()).unwrap();
            if written == 0 {
                break;
            }

            sz += written;
        }

        if sz == 0 {
            return read_time;
        }

        let mut offs = 0;
        loop {
            let start = Instant::now();
            offs += right.read_tls(&mut buf[offs..sz].as_ref()).unwrap();
            let end = Instant::now();
            read_time += f64::from(duration_nanos(end.duration_since(start)));
            if sz == offs {
                break;
            }
        }
    }
}

// fn send(sender: &mut dyn Connection) -> Vec<u8> {
//     let mut buf = [0u8; 262144];
//     let mut sz = 0;

//     while sender.wants_write() {
//         let written = sender.write_tls(&mut buf[sz..].as_mut()).unwrap();
//         if written == 0 {
//             break;
//         }

//         sz += written;
//     }
//     buf.into()
// }

// /// XXX: we don't measure the read here. It's done in rustls originally.
// /// I'm not sure why and if it makes a difference.
// fn receive(receiver: &mut dyn Connection, stream: &[u8]) {
//     let mut offs = 0;
//     loop {
//         offs += receiver.read_tls(&mut stream[offs..].as_ref()).unwrap();
//         if offs == stream.len() {
//             break;
//         }
//     }
// }

#[derive(PartialEq, Clone, Copy)]
enum ClientAuth {
    No,
    Yes,
}

#[derive(PartialEq, Clone, Copy)]
enum Resumption {
    No,
    SessionID,
    Tickets,
}

impl Resumption {
    fn label(&self) -> &'static str {
        match *self {
            Resumption::No => "no-resume",
            Resumption::SessionID => "sessionid",
            Resumption::Tickets => "tickets",
        }
    }
}

// copied from tests/api.rs
#[derive(PartialEq, Clone, Copy, Debug)]
enum KeyType {
    RSA,
    ECDSA,
    ED25519,
}

struct BenchmarkParam {
    key_type: KeyType,
    ciphersuite: &'static rustls::SupportedCipherSuite,
    version: ProtocolVersion,
}

impl BenchmarkParam {
    const fn new(
        key_type: KeyType,
        ciphersuite: &'static rustls::SupportedCipherSuite,
        version: ProtocolVersion,
    ) -> BenchmarkParam {
        BenchmarkParam {
            key_type,
            ciphersuite,
            version,
        }
    }
}

static ALL_BENCHMARKS: &[BenchmarkParam] = &[
    BenchmarkParam::new(
        KeyType::ECDSA,
        &rustls::cipher_suites::TLS13_CHACHA20_POLY1305_SHA256,
        ProtocolVersion::TLSv1_3,
    ),
    // BenchmarkParam::new(
    //     KeyType::RSA,
    //     &rustls::cipher_suites::TLS13_AES_256_GCM_SHA384,
    //     ProtocolVersion::TLSv1_3,
    // ),
    // BenchmarkParam::new(
    //     KeyType::RSA,
    //     &rustls::cipher_suites::TLS13_AES_128_GCM_SHA256,
    //     ProtocolVersion::TLSv1_3,
    // ),
    BenchmarkParam::new(
        KeyType::ECDSA,
        &rustls::cipher_suites::TLS13_AES_128_GCM_SHA256,
        ProtocolVersion::TLSv1_3,
    ),
    // BenchmarkParam::new(
    //     KeyType::ED25519,
    //     &rustls::cipher_suites::TLS13_AES_128_GCM_SHA256,
    //     ProtocolVersion::TLSv1_3,
    // ),
];

impl KeyType {
    fn path_for(&self, part: &str) -> String {
        match self {
            KeyType::RSA => format!("protocols/tls13/examples/test-ca/rsa/{}", part),
            KeyType::ECDSA => format!("protocols/tls13/examples/test-ca/ecdsa/{}", part),
            KeyType::ED25519 => format!("protocols/tls13/examples/test-ca/eddsa/{}", part),
        }
    }

    fn get_chain(&self) -> Vec<rustls::Certificate> {
        rustls_pemfile::certs(&mut io::BufReader::new(
            fs::File::open(self.path_for("end.fullchain")).unwrap(),
        ))
        .unwrap()
        .iter()
        .map(|v| rustls::Certificate(v.clone()))
        .collect()
    }

    fn get_key(&self) -> rustls::PrivateKey {
        rustls::PrivateKey(
            rustls_pemfile::pkcs8_private_keys(&mut io::BufReader::new(
                fs::File::open(self.path_for("end.key")).unwrap(),
            ))
            .unwrap()[0]
                .clone(),
        )
    }

    fn get_client_chain(&self) -> Vec<rustls::Certificate> {
        rustls_pemfile::certs(&mut io::BufReader::new(
            fs::File::open(self.path_for("client.fullchain")).unwrap(),
        ))
        .unwrap()
        .iter()
        .map(|v| rustls::Certificate(v.clone()))
        .collect()
    }

    fn get_client_key(&self) -> rustls::PrivateKey {
        rustls::PrivateKey(
            rustls_pemfile::pkcs8_private_keys(&mut io::BufReader::new(
                fs::File::open(self.path_for("client.key")).unwrap(),
            ))
            .unwrap()[0]
                .clone(),
        )
    }
}

fn make_server_config(
    params: &BenchmarkParam,
    client_auth: ClientAuth,
    resume: Resumption,
    mtu: Option<usize>,
) -> ServerConfig {
    let client_auth = match client_auth {
        ClientAuth::Yes => {
            let roots = params.key_type.get_chain();
            let mut client_auth_roots = RootCertStore::empty();
            for root in roots {
                client_auth_roots.add(&root).unwrap();
            }
            AllowAnyAuthenticatedClient::new(client_auth_roots)
        }
        ClientAuth::No => NoClientAuth::new(),
    };

    let mut cfg = ServerConfig::new(client_auth);
    cfg.set_single_cert(params.key_type.get_chain(), params.key_type.get_key())
        .expect("bad certs/private key?");

    if resume == Resumption::SessionID {
        cfg.set_persistence(ServerSessionMemoryCache::new(128));
    } else if resume == Resumption::Tickets {
        cfg.ticketer = Ticketer::new().unwrap();
    } else {
        cfg.set_persistence(Arc::new(NoServerSessionStorage {}));
    }

    cfg.versions.clear();
    cfg.versions.push(params.version);

    cfg.mtu = mtu;

    cfg
}

fn make_client_config(
    params: &BenchmarkParam,
    clientauth: ClientAuth,
    resume: Resumption,
) -> ClientConfig {
    let mut root_store = RootCertStore::empty();
    let mut rootbuf =
        io::BufReader::new(fs::File::open(params.key_type.path_for("ca.cert")).unwrap());
    root_store.add_parsable_certificates(&rustls_pemfile::certs(&mut rootbuf).unwrap());

    let mut cfg = ClientConfig::new(root_store, &[], &[params.ciphersuite]);
    cfg.versions.clear();
    cfg.versions.push(params.version);

    if clientauth == ClientAuth::Yes {
        cfg.set_single_client_cert(
            params.key_type.get_client_chain(),
            params.key_type.get_client_key(),
        )
        .unwrap();
    }

    if resume != Resumption::No {
        cfg.set_persistence(ClientSessionMemoryCache::new(128));
    } else {
        cfg.set_persistence(Arc::new(NoClientSessionStorage {}));
    }

    cfg
}

fn apply_work_multiplier(work: u64) -> u64 {
    let mul = match env::var("BENCH_MULTIPLIER") {
        Ok(val) => val.parse::<f64>().expect("invalid BENCH_MULTIPLIER value"),
        Err(_) => 1.,
    };

    ((work as f64) * mul).round() as u64
}

fn bench_handshake(params: &BenchmarkParam, clientauth: ClientAuth, resume: Resumption) {
    // let client_config = Arc::new(make_client_config(params, clientauth, resume));
    // let server_config = Arc::new(make_server_config(params, clientauth, resume, None));

    // assert!(params.ciphersuite.usable_for_version(params.version));

    // let rounds = apply_work_multiplier(if resume == Resumption::No { 512 } else { 4096 });
    // let mut client_time = 0f64;
    // let mut server_time = 0f64;

    // for _ in 0..rounds {
    //     let dns_name = webpki::DnsNameRef::try_from_ascii_str("localhost").unwrap();
    //     let mut client = ClientConnection::new(&client_config, dns_name).unwrap();
    //     let mut server = ServerConnection::new(&server_config);

    //     time(
    //         || {
    //             transfer(&mut client, &mut server);
    //             server.process_new_packets().unwrap();
    //         },
    //         &mut server_time,
    //     );
    //     time(
    //         || {
    //             transfer(&mut server, &mut client);
    //             client.process_new_packets().unwrap();
    //         },
    //         &mut client_time,
    //     );
    //     time(
    //         || {
    //             transfer(&mut client, &mut server);
    //             server.process_new_packets().unwrap();
    //         },
    //         &mut client_time,
    //     );
    //     time(
    //         || {
    //             transfer(&mut server, &mut client);
    //             client.process_new_packets().unwrap();
    //         },
    //         &mut client_time,
    //     );
    // }

    // println!(
    //     "handshakes\t{:?}\t{:?}\t{:?}\tclient\t{}\t{}\t{:.2}\thandshake/s",
    //     params.version,
    //     params.key_type,
    //     params.ciphersuite.suite,
    //     if clientauth == ClientAuth::Yes {
    //         "mutual"
    //     } else {
    //         "server-auth"
    //     },
    //     resume.label(),
    //     (rounds as f64) / client_time
    // );
    // println!(
    //     "handshakes\t{:?}\t{:?}\t{:?}\tserver\t{}\t{}\t{:.2}\thandshake/s",
    //     params.version,
    //     params.key_type,
    //     params.ciphersuite.suite,
    //     if clientauth == ClientAuth::Yes {
    //         "mutual"
    //     } else {
    //         "server-auth"
    //     },
    //     resume.label(),
    //     (rounds as f64) / server_time
    // );
}

fn do_handshake_step(client: &mut ClientConnection, server: &mut ServerConnection) -> bool {
    if server.is_handshaking() || client.is_handshaking() {
        transfer(client, server);
        server.process_new_packets().unwrap();
        transfer(server, client);
        client.process_new_packets().unwrap();
        true
    } else {
        false
    }
}

fn do_handshake(client: &mut ClientConnection, server: &mut ServerConnection) {
    while do_handshake_step(client, server) {}
}

fn rounds(plaintext_size: u64) -> u64 {
    let total_data = apply_work_multiplier(if plaintext_size < 8192 {
        64 * 1024 * 1024
    } else {
        1024 * 1024 * 1024
    });
    total_data / plaintext_size
}

fn drain(d: &mut dyn Connection, expect_len: usize) {
    let mut left = expect_len;
    let mut buf = [0u8; 8192];
    loop {
        let sz = d.reader().read(&mut buf);
        if let Ok(sz) = sz {
            left -= sz;
            if left == 0 {
                break;
            }
        } else {
            // WouldBlock error
            return;
        }
    }
}

fn bench_bulk_rustls(params: &BenchmarkParam, plaintext_size: u64) {
    let client_config = Arc::new(make_client_config(params, ClientAuth::No, Resumption::No));
    let server_config = Arc::new(make_server_config(
        params,
        ClientAuth::No,
        Resumption::No,
        None,
    ));

    let dns_name = webpki::DnsNameRef::try_from_ascii_str("localhost").unwrap();
    let mut client = ClientConnection::new(&client_config, dns_name).unwrap();
    let mut server = ServerConnection::new(&server_config);

    do_handshake(&mut client, &mut server);

    let rounds = rounds(plaintext_size);
    let mut time_send = 0f64;
    let mut time_recv = 0f64;

    for _ in 0..rounds {
        let buf = vec![0u8; plaintext_size as usize];
        time(
            buf,
            |buf| {
                server.writer().write_all(&buf).unwrap();
            },
            &mut time_send,
        );
        // XXX: time_send is ignored here ...
        time_recv += transfer(&mut server, &mut client);
        let _ = time(
            (),
            |_| {
                client.process_new_packets().unwrap();
            },
            &mut time_recv,
        );
        drain(&mut client, plaintext_size as usize);
    }

    let total_mbs = ((plaintext_size * rounds) as f64) / (1024. * 1024.);
    println!(
        "rustls bulk\t{:?}\t{:?}\tsend\t{:.2}\tMB/s",
        params.version,
        params.ciphersuite.suite,
        total_mbs / time_send
    );
    println!(
        "rustls bulk\t{:?}\t{:?}\trecv\t{:.2}\tMB/s",
        params.version,
        params.ciphersuite.suite,
        total_mbs / time_recv
    );
}

fn load_hex(s: &str) -> Bytes {
    let s_no_ws: String = s.split_whitespace().collect();
    Bytes::from_hex(&s_no_ws)
}

const CLIENT_X25519_PRIV: &str = "49 af 42 ba 7f 79 94 85 2d 71 3e f2 78
4b cb ca a7 91 1d e2 6a dc 56 42 cb 63 45 40 e7 ea 50 05";

const SERVER_X25519_PRIV: &str = "b1 58 0e ea df 6d d5 89 b8 ef 4f 2d 56
52 57 8c c8 10 e9 98 01 91 ec 8d 05 83 08 ce a2 16 a2 1e";

const ECDSA_P256_SHA256_CERT: [u8; 522] = [
    0x30, 0x82, 0x02, 0x06, 0x30, 0x82, 0x01, 0xAC, 0x02, 0x09, 0x00, 0xD1, 0xA2, 0xE4, 0xD5, 0x78,
    0x05, 0x08, 0x61, 0x30, 0x0A, 0x06, 0x08, 0x2A, 0x86, 0x48, 0xCE, 0x3D, 0x04, 0x03, 0x02, 0x30,
    0x81, 0x8A, 0x31, 0x0B, 0x30, 0x09, 0x06, 0x03, 0x55, 0x04, 0x06, 0x13, 0x02, 0x44, 0x45, 0x31,
    0x0F, 0x30, 0x0D, 0x06, 0x03, 0x55, 0x04, 0x08, 0x0C, 0x06, 0x42, 0x65, 0x72, 0x6C, 0x69, 0x6E,
    0x31, 0x0F, 0x30, 0x0D, 0x06, 0x03, 0x55, 0x04, 0x07, 0x0C, 0x06, 0x42, 0x65, 0x72, 0x6C, 0x69,
    0x6E, 0x31, 0x10, 0x30, 0x0E, 0x06, 0x03, 0x55, 0x04, 0x0A, 0x0C, 0x07, 0x68, 0x61, 0x63, 0x73,
    0x70, 0x65, 0x63, 0x31, 0x0F, 0x30, 0x0D, 0x06, 0x03, 0x55, 0x04, 0x0B, 0x0C, 0x06, 0x62, 0x65,
    0x72, 0x74, 0x69, 0x65, 0x31, 0x17, 0x30, 0x15, 0x06, 0x03, 0x55, 0x04, 0x03, 0x0C, 0x0E, 0x62,
    0x65, 0x72, 0x74, 0x69, 0x65, 0x2E, 0x68, 0x61, 0x63, 0x73, 0x70, 0x65, 0x63, 0x31, 0x1D, 0x30,
    0x1B, 0x06, 0x09, 0x2A, 0x86, 0x48, 0x86, 0xF7, 0x0D, 0x01, 0x09, 0x01, 0x16, 0x0E, 0x62, 0x65,
    0x72, 0x74, 0x69, 0x65, 0x40, 0x68, 0x61, 0x63, 0x73, 0x70, 0x65, 0x63, 0x30, 0x1E, 0x17, 0x0D,
    0x32, 0x31, 0x30, 0x34, 0x32, 0x39, 0x31, 0x31, 0x34, 0x37, 0x34, 0x35, 0x5A, 0x17, 0x0D, 0x33,
    0x31, 0x30, 0x34, 0x32, 0x37, 0x31, 0x31, 0x34, 0x37, 0x34, 0x35, 0x5A, 0x30, 0x81, 0x8A, 0x31,
    0x0B, 0x30, 0x09, 0x06, 0x03, 0x55, 0x04, 0x06, 0x13, 0x02, 0x44, 0x45, 0x31, 0x0F, 0x30, 0x0D,
    0x06, 0x03, 0x55, 0x04, 0x08, 0x0C, 0x06, 0x42, 0x65, 0x72, 0x6C, 0x69, 0x6E, 0x31, 0x0F, 0x30,
    0x0D, 0x06, 0x03, 0x55, 0x04, 0x07, 0x0C, 0x06, 0x42, 0x65, 0x72, 0x6C, 0x69, 0x6E, 0x31, 0x10,
    0x30, 0x0E, 0x06, 0x03, 0x55, 0x04, 0x0A, 0x0C, 0x07, 0x68, 0x61, 0x63, 0x73, 0x70, 0x65, 0x63,
    0x31, 0x0F, 0x30, 0x0D, 0x06, 0x03, 0x55, 0x04, 0x0B, 0x0C, 0x06, 0x62, 0x65, 0x72, 0x74, 0x69,
    0x65, 0x31, 0x17, 0x30, 0x15, 0x06, 0x03, 0x55, 0x04, 0x03, 0x0C, 0x0E, 0x62, 0x65, 0x72, 0x74,
    0x69, 0x65, 0x2E, 0x68, 0x61, 0x63, 0x73, 0x70, 0x65, 0x63, 0x31, 0x1D, 0x30, 0x1B, 0x06, 0x09,
    0x2A, 0x86, 0x48, 0x86, 0xF7, 0x0D, 0x01, 0x09, 0x01, 0x16, 0x0E, 0x62, 0x65, 0x72, 0x74, 0x69,
    0x65, 0x40, 0x68, 0x61, 0x63, 0x73, 0x70, 0x65, 0x63, 0x30, 0x59, 0x30, 0x13, 0x06, 0x07, 0x2A,
    0x86, 0x48, 0xCE, 0x3D, 0x02, 0x01, 0x06, 0x08, 0x2A, 0x86, 0x48, 0xCE, 0x3D, 0x03, 0x01, 0x07,
    0x03, 0x42, 0x00, 0x04, 0xD8, 0xE0, 0x74, 0xF7, 0xCB, 0xEF, 0x19, 0xC7, 0x56, 0xA4, 0x52, 0x59,
    0x0C, 0x02, 0x70, 0xCC, 0x9B, 0xFC, 0x45, 0x8D, 0x73, 0x28, 0x39, 0x1D, 0x3B, 0xF5, 0x26, 0x17,
    0x8B, 0x0D, 0x25, 0x04, 0x91, 0xE8, 0xC8, 0x72, 0x22, 0x59, 0x9A, 0x2C, 0xBB, 0x26, 0x31, 0xB1,
    0xCC, 0x6B, 0x6F, 0x5A, 0x10, 0xD9, 0x7D, 0xD7, 0x86, 0x56, 0xFB, 0x89, 0x39, 0x9E, 0x0A, 0x91,
    0x9F, 0x35, 0x81, 0xE7, 0x30, 0x0A, 0x06, 0x08, 0x2A, 0x86, 0x48, 0xCE, 0x3D, 0x04, 0x03, 0x02,
    0x03, 0x48, 0x00, 0x30, 0x45, 0x02, 0x21, 0x00, 0xA1, 0x81, 0xB3, 0xD6, 0x8C, 0x9F, 0x62, 0x66,
    0xC6, 0xB7, 0x3F, 0x26, 0xE7, 0xFD, 0x88, 0xF9, 0x4B, 0xD8, 0x15, 0xD1, 0x45, 0xC7, 0x66, 0x69,
    0x40, 0xC2, 0x55, 0x21, 0x84, 0x9F, 0xE6, 0x8C, 0x02, 0x20, 0x10, 0x7E, 0xEF, 0xF3, 0x1D, 0x58,
    0x32, 0x6E, 0xF7, 0xCB, 0x0A, 0x47, 0xF2, 0xBA, 0xEB, 0xBC, 0xB7, 0x8F, 0x46, 0x56, 0xF1, 0x5B,
    0xCC, 0x2E, 0xD5, 0xB3, 0xC4, 0x0F, 0x5B, 0x22, 0xBD, 0x02,
];
const ECDSA_P256_SHA256_KEY: [u8; 32] = [
    0xA6, 0xDE, 0x48, 0x21, 0x0E, 0x56, 0x12, 0xDD, 0x95, 0x3A, 0x91, 0x4E, 0x9F, 0x56, 0xC3, 0xA2,
    0xDB, 0x7A, 0x36, 0x20, 0x08, 0xE9, 0x52, 0xEE, 0xDB, 0xCE, 0xAC, 0x3B, 0x26, 0xF9, 0x20, 0xBD,
];

fn init_tls_session(ciphersuite: Algorithms) -> (DuplexCipherState1, DuplexCipherState1) {
    let cr = Random::from_public_slice(&random_byte_vec(Random::length()));
    let x = load_hex(CLIENT_X25519_PRIV);
    let ent_c = Entropy::from_seq(&cr.concat(&x));
    let sn = load_hex("6c 6f 63 61 6c 68 6f 73 74");
    let sn_ = load_hex("6c 6f 63 61 6c 68 6f 73 74");
    let sr = Random::from_public_slice(&random_byte_vec(Random::length()));
    let y = load_hex(SERVER_X25519_PRIV);
    let ent_s = Entropy::from_seq(&sr.concat(&y));

    let db = ServerDB(
        sn_,
        Bytes::from_public_slice(&ECDSA_P256_SHA256_CERT),
        SIGK::from_public_slice(&ECDSA_P256_SHA256_KEY),
        None,
    );

    let (ch, cstate, _) = client_init(ciphersuite, &sn, None, None, ent_c).unwrap();
    let (sh, sf, sstate, _, server_cipher) = server_init(ciphersuite, db, &ch, ent_s).unwrap();
    let (cstate, _) = client_set_params(&sh, cstate).unwrap();
    let (cf, _cstate, client_cipher) = client_finish(&sf, cstate).unwrap();
    let _sstate = server_finish(&cf, sstate).unwrap();

    (client_cipher, server_cipher)
}

fn bench_bulk_hacspec(params: &BenchmarkParam, plaintext_size: u64) {
    const TLS_AES_128_GCM_SHA256_X25519: Algorithms = Algorithms(
        HashAlgorithm::SHA256,
        AEADAlgorithm::AES_128_GCM,
        SignatureScheme::ECDSA_SECP256r1_SHA256,
        NamedGroup::X25519,
        false,
        false,
    );
    const TLS_CHACHA20_POLY1305_SHA256_X25519: Algorithms = Algorithms(
        HashAlgorithm::SHA256,
        AEADAlgorithm::CHACHA20_POLY1305,
        SignatureScheme::ECDSA_SECP256r1_SHA256,
        NamedGroup::X25519,
        false,
        false,
    );
    const MAX_CHUNK_SIZE: usize = 65536 - 32;

    let rounds = rounds(plaintext_size);
    let mut time_send = 0f64;
    let mut time_recv = 0f64;

    for _ in 0..rounds {
        let buf = Bytes::from_public_slice(&vec![0u8; plaintext_size as usize]);
        let (client_cipher, server_cipher) = match params.ciphersuite.suite {
            CipherSuite::TLS13_CHACHA20_POLY1305_SHA256 => {
                init_tls_session(TLS_CHACHA20_POLY1305_SHA256_X25519)
            }
            CipherSuite::TLS13_AES_128_GCM_SHA256 => {
                init_tls_session(TLS_AES_128_GCM_SHA256_X25519)
            }
            _ => unimplemented!("Please disable these cipher suites."),
        };

        let stream = time(
            (buf.clone(), client_cipher),
            |(payload, mut client_cipher)| {
                let mut stream = Vec::new();
                for chunk in payload.native_slice().chunks(MAX_CHUNK_SIZE) {
                    let chunk = Bytes::from_native_slice(chunk);
                // NOTE: the hacspec native chunks are way too slow.
                // for i in 0..payload.num_chunks(MAX_CHUNK_SIZE) {
                //     let (_chunk_len, chunk) = buf.get_chunk(MAX_CHUNK_SIZE, i);
                    let (stream_chunk, new_cipher_state) =
                        encrypt_data(AppData(chunk), 0, client_cipher)
                            .unwrap();
                    stream.push(stream_chunk);
                    client_cipher = new_cipher_state;
                }
                stream
            },
            &mut time_send,
        );
        let _ = time(
            (stream, server_cipher),
            |(mut stream, mut server_cipher)| {
                for chunk in stream.drain(..) {
                    let (_ap, new_cipher_state) = decrypt_data(chunk, server_cipher).unwrap();
                    server_cipher = new_cipher_state;
                }
            },
            &mut time_recv,
        );
    }

    let total_mbs = ((plaintext_size * rounds) as f64) / (1024. * 1024.);
    println!(
        "hacspec bulk\t{:?}\t{:?}\tsend\t{:.2}\tMB/s",
        params.version,
        params.ciphersuite.suite,
        total_mbs / time_send
    );
    println!(
        "hacspec bulk\t{:?}\t{:?}\trecv\t{:.2}\tMB/s",
        params.version,
        params.ciphersuite.suite,
        total_mbs / time_recv
    );
}

fn bench_memory(params: &BenchmarkParam, conn_count: u64) {
    let client_config = Arc::new(make_client_config(params, ClientAuth::No, Resumption::No));
    let server_config = Arc::new(make_server_config(
        params,
        ClientAuth::No,
        Resumption::No,
        None,
    ));

    // The target here is to end up with conn_count post-handshake
    // server and client sessions.
    let conn_count = (conn_count / 2) as usize;
    let mut servers = Vec::with_capacity(conn_count);
    let mut clients = Vec::with_capacity(conn_count);

    for _i in 0..conn_count {
        servers.push(ServerConnection::new(&server_config));
        let dns_name = webpki::DnsNameRef::try_from_ascii_str("localhost").unwrap();
        clients.push(ClientConnection::new(&client_config, dns_name).unwrap());
    }

    for _step in 0..5 {
        for (mut client, mut server) in clients.iter_mut().zip(servers.iter_mut()) {
            do_handshake_step(&mut client, &mut server);
        }
    }

    for client in clients.iter_mut() {
        client.writer().write_all(&[0u8; 1024]).unwrap();
    }

    for (client, server) in clients.iter_mut().zip(servers.iter_mut()) {
        transfer(client, server);
        let mut buf = [0u8; 1024];
        server.reader().read(&mut buf).unwrap();
    }
}

fn lookup_matching_benches(name: &str) -> Vec<&BenchmarkParam> {
    let r: Vec<&BenchmarkParam> = ALL_BENCHMARKS
        .iter()
        .filter(|params| {
            format!("{:?}", params.ciphersuite.suite).to_lowercase() == name.to_lowercase()
        })
        .collect();

    if r.is_empty() {
        panic!("unknown suite {:?}", name);
    }

    r
}

fn selected_tests(mut args: env::Args) {
    let mode = args.next().expect("first argument must be mode");

    match mode.as_ref() {
        "bulk" => match args.next() {
            Some(suite) => {
                let len = args
                    .next()
                    .map(|arg| {
                        arg.parse::<u64>()
                            .expect("3rd arg must be plaintext size integer")
                    })
                    .unwrap_or(1048576);
                for param in lookup_matching_benches(&suite).iter() {
                    bench_bulk_rustls(param, len);
                }
            }
            None => {
                panic!("bulk needs ciphersuite argument");
            }
        },

        "handshake" | "handshake-resume" | "handshake-ticket" => match args.next() {
            Some(suite) => {
                let resume = if mode == "handshake" {
                    Resumption::No
                } else if mode == "handshake-resume" {
                    Resumption::SessionID
                } else {
                    Resumption::Tickets
                };

                for param in lookup_matching_benches(&suite).iter() {
                    bench_handshake(param, ClientAuth::No, resume);
                }
            }
            None => {
                panic!("handshake* needs ciphersuite argument");
            }
        },

        "memory" => match args.next() {
            Some(suite) => {
                let count = args
                    .next()
                    .map(|arg| {
                        arg.parse::<u64>()
                            .expect("3rd arg must be connection count integer")
                    })
                    .unwrap_or(1000000);
                for param in lookup_matching_benches(&suite).iter() {
                    bench_memory(param, count);
                }
            }
            None => {
                panic!("memory needs ciphersuite argument");
            }
        },

        _ => {
            panic!("unsupported mode {:?}", mode);
        }
    }
}

fn all_tests() {
    for test in ALL_BENCHMARKS.iter() {
        bench_bulk_rustls(test, 1024 * 1024);
        bench_bulk_hacspec(test, 1024 * 1024);
        // bench_handshake(test, ClientAuth::No, Resumption::No);
        // bench_handshake(test, ClientAuth::Yes, Resumption::No);
        // bench_handshake(test, ClientAuth::No, Resumption::SessionID);
        // bench_handshake(test, ClientAuth::Yes, Resumption::SessionID);
        // bench_handshake(test, ClientAuth::No, Resumption::Tickets);
        // bench_handshake(test, ClientAuth::Yes, Resumption::Tickets);
    }
}

fn main() {
    let mut args = env::args();
    if args.len() > 1 {
        args.next();
        selected_tests(args);
    } else {
        all_tests();
    }
}
