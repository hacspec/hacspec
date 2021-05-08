extern crate bertie;
extern crate rand;

use bertie::*;
use criterion::{criterion_group, criterion_main, BatchSize, Criterion};
use hacspec_dev::prelude::*;
use hacspec_lib::prelude::*;

// 1MB
const PAYLOAD_SIZE: usize = 0x100000;

fn bench(c: &mut Criterion) {
    const CIPHERSUITES: [AEADAlgorithm; 1] = [
        AEADAlgorithm::AES_128_GCM,
        // AEADAlgorithm::CHACHA20_POLY1305,
    ];

    for &ciphersuite in CIPHERSUITES.iter() {
        c.bench_function(
            &format!("AEAD performance encrypt: {:?}", ciphersuite),
            |b| {
                b.iter_batched(
                    || {
                        let nonce = random_byte_vec(12);
                        let key = match ciphersuite {
                            AEADAlgorithm::AES_128_GCM => random_byte_vec(16),
                            AEADAlgorithm::AES_256_GCM | AEADAlgorithm::CHACHA20_POLY1305 => {
                                random_byte_vec(32)
                            }
                        };
                        let data = random_byte_vec(PAYLOAD_SIZE);
                        let aad = random_byte_vec(100);
                        (
                            ByteSeq::from_public_slice(&key),
                            ByteSeq::from_public_slice(&nonce),
                            ByteSeq::from_public_slice(&data),
                            ByteSeq::from_public_slice(&aad),
                        )
                    },
                    |(key, nonce, data, aad)| {
                        let _ctxt_tag =
                            aead_encrypt(&ciphersuite, &key, &nonce, &data, &aad).unwrap();
                    },
                    BatchSize::SmallInput,
                );
            },
        );

        c.bench_function(
            &format!("AEAD performance decrypt: {:?}", &ciphersuite),
            |b| {
                b.iter_batched(
                    || {
                        let nonce = random_byte_vec(12);
                        let key = match ciphersuite {
                            AEADAlgorithm::AES_128_GCM => random_byte_vec(16),
                            AEADAlgorithm::AES_256_GCM | AEADAlgorithm::CHACHA20_POLY1305 => {
                                random_byte_vec(32)
                            }
                        };
                        let data = random_byte_vec(PAYLOAD_SIZE);
                        let aad = random_byte_vec(100);
                        let key = ByteSeq::from_public_slice(&key);
                        let nonce = ByteSeq::from_public_slice(&nonce);
                        let data = ByteSeq::from_public_slice(&data);
                        let aad = ByteSeq::from_public_slice(&aad);
                        let ctxt_tag =
                            aead_encrypt(&ciphersuite, &key, &nonce, &data, &aad).unwrap();
                        (ctxt_tag, key, nonce, aad)
                    },
                    |(ctxt_tag, key, nonce, aad)| {
                        let _ctxt_tag =
                            aead_decrypt(&ciphersuite, &key, &nonce, &ctxt_tag, &aad).unwrap();
                    },
                    BatchSize::SmallInput,
                );
            },
        );
    }
}

criterion_group!(benches, bench);
criterion_main!(benches);
