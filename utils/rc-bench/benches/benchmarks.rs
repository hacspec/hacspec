#[macro_use]
extern crate criterion;
use criterion::{BatchSize, Criterion};

use chacha20poly1305::ChaCha20Poly1305 as RustCrypto_ChaCha20Poly1305;
use evercrypt_provider::Chacha20Poly1305 as Evercrypt_Chacha20Poly1305;
use hacspec_provider::{
    aead::consts::{U12, U16, U32},
    Aead, Chacha20Poly1305 as Hacspec_Chacha20Poly1305, Key, NewAead, Nonce, Payload,
};

fn random_bytes(n: usize) -> Vec<u8> {
    use rand::rngs::OsRng;
    use rand::RngCore;

    let mut bytes = vec![0u8; n];
    OsRng.fill_bytes(&mut bytes);
    bytes
}

fn criterion_chacha_poly<T>(c: &mut Criterion, provider_desc: &str)
where
    T: Aead<NonceSize = U12, TagSize = U16> + NewAead<KeySize = U32>,
{
    c.bench_function(
        &format!("{}: ChaCha20Poly1305 encrypt", provider_desc),
        |b| {
            b.iter_batched(
                || {
                    let key = Key::clone_from_slice(&random_bytes(32));
                    let nonce = Nonce::clone_from_slice(&random_bytes(12));
                    let data = random_bytes(10_000);
                    let aad = random_bytes(1_000);
                    (data, nonce, aad, key)
                },
                |(data, nonce, aad, key)| {
                    let cipher = T::new(&key);
                    let _ciphertext = cipher.encrypt(
                        &nonce,
                        Payload {
                            msg: &data,
                            aad: &aad,
                        },
                    );
                },
                BatchSize::SmallInput,
            )
        },
    );

    c.bench_function(
        &format!("{}: ChaCha20Poly1305 decrypt", provider_desc),
        |b| {
            b.iter_batched(
                || {
                    let key = Key::clone_from_slice(&random_bytes(32));
                    let nonce = Nonce::clone_from_slice(&random_bytes(12));
                    let data = random_bytes(10_000);
                    let aad = random_bytes(1_000);
                    let cipher = Hacspec_Chacha20Poly1305::new(&key);
                    let ciphertext = cipher
                        .encrypt(
                            &nonce,
                            Payload {
                                msg: &data,
                                aad: &aad,
                            },
                        )
                        .unwrap();
                    (nonce, aad, key, ciphertext)
                },
                |(nonce, aad, key, ciphertext)| {
                    let cipher = Hacspec_Chacha20Poly1305::new(&key);
                    let _msg = cipher.decrypt(
                        &nonce,
                        Payload {
                            msg: &ciphertext,
                            aad: &aad,
                        },
                    );
                },
                BatchSize::SmallInput,
            )
        },
    );
}

fn criterion_benchmark(c: &mut Criterion) {
    criterion_chacha_poly::<Hacspec_Chacha20Poly1305>(c, "Hacspec");
    criterion_chacha_poly::<Evercrypt_Chacha20Poly1305>(c, "Evercrypt");
    criterion_chacha_poly::<RustCrypto_ChaCha20Poly1305>(c, "RustCrypto");
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
