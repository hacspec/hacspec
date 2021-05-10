extern crate bertie;
extern crate rand;

use bertie::*;
use criterion::{criterion_group, criterion_main, BatchSize, Criterion};
use hacspec_dev::prelude::*;
use hacspec_lib::prelude::*;

// 1MB
const PAYLOAD_SIZE: usize = 0x100000;

fn bench(c: &mut Criterion) {
    const AEAD_CIPHERSUITES: [AEADAlgorithm; 2] =
        [AEADAlgorithm::AES_128_GCM, AEADAlgorithm::CHACHA20_POLY1305];

    for &ciphersuite in AEAD_CIPHERSUITES.iter() {
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
                            aead_decrypt(&ciphersuite, &key, &nonce, ctxt_tag, &aad).unwrap();
                    },
                    BatchSize::SmallInput,
                );
            },
        );
    }

    const ECDH_CIPHERSUITES: [NamedGroup; 2] = [NamedGroup::X25519, NamedGroup::SECP256r1];

    const P256_PK1_HEX: &str = "0462d5bd3372af75fe85a040715d0f502428e07046868b0bfdfa61d731afe44f26ac333a93a9e70a81cd5a95b5bf8d13990eb741c8c38872b4a07d275a014e30cf";
    const P256_SK1_HEX: &str = "0612465c89a023ab17855b0a6bcebfd3febb53aef84138647b5352e02c10c346";
    const P256_SK2_HEX: &str = "809c461d8b39163537ff8f5ef5b977e4cdb980e70e38a7ee0b37cc876729e9ff";
    const P256_NONCE: &str = "A6E3C57DD01ABE90086538398355DD4C3B17AA873382B0F24D6129493D8AAD60";

    for ciphersuite in ECDH_CIPHERSUITES.iter() {
        c.bench_function(&format!("ECDH base {:?}", ciphersuite), |b| {
            let sk1 = match ciphersuite {
                NamedGroup::X25519 => random_byte_vec(32),
                NamedGroup::SECP256r1 => hex_to_bytes(P256_SK1_HEX),
            };
            let sk1 = ByteSeq::from_public_slice(&sk1);
            b.iter(|| {
                let _pk = secret_to_public(ciphersuite, &sk1).unwrap();
            });
        });
        c.bench_function(&format!("ECDH {:?}", ciphersuite), |b| {
            let pk1 = match ciphersuite {
                NamedGroup::X25519 => random_byte_vec(32),
                NamedGroup::SECP256r1 => hex_to_bytes(P256_PK1_HEX),
            };
            let pk1 = ByteSeq::from_public_slice(&pk1);
            let sk2 = match ciphersuite {
                NamedGroup::X25519 => random_byte_vec(32),
                NamedGroup::SECP256r1 => hex_to_bytes(P256_SK2_HEX),
            };
            let sk2 = ByteSeq::from_public_slice(&sk2);
            b.iter(|| {
                let _zz = ecdh(ciphersuite, &sk2, &pk1).unwrap();
            });
        });
    }
    c.bench_function(&format!("P256 SHA256 Sign"), |b| {
        let sk1 = hex_to_bytes(P256_SK1_HEX);
        let sk1 = ByteSeq::from_public_slice(&sk1);
        let nonce = hex_to_bytes(P256_NONCE);
        let nonce = ByteSeq::from_public_slice(&nonce);
        let payload = random_byte_vec(1_000);
        let payload = ByteSeq::from_public_slice(&payload);
        b.iter_batched(
            || nonce.clone(),
            |nonce| {
                let _sig = sign(
                    &SignatureScheme::ECDSA_SECP256r1_SHA256,
                    &sk1,
                    &payload,
                    nonce,
                )
                .unwrap();
            },
            BatchSize::SmallInput,
        );
    });
}

criterion_group!(benches, bench);
criterion_main!(benches);
