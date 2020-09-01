#[macro_use]
extern crate criterion;
use criterion::{BatchSize, Criterion};

use hacspec_examples::chacha20_poly1305::{chacha20::*, *};
use hacspec_lib::prelude::*;

fn randombytes(n: usize) -> Vec<u8> {
    use rand::rngs::OsRng;
    use rand::RngCore;

    let mut bytes = vec![0u8; n];
    OsRng.fill_bytes(&mut bytes);
    bytes
}

fn criterion_chacha_poly(c: &mut Criterion) {
    c.bench_function("ChaCha20Poly1305 encrypt", |b| {
        let key = Key::from_public_slice(&randombytes(32));
        b.iter_batched(
            || {
                let nonce = IV::from_public_slice(&randombytes(12));
                let data = Seq::<U8>::from_public_slice(&randombytes(1_000));
                let aad = Seq::<U8>::from_public_slice(&randombytes(1_000));
                (data, nonce, aad, key)
            },
            |(data, nonce, aad, key)| {
                let (_cipher, _mac) = encrypt(key, nonce, &aad, &data).unwrap();
            },
            BatchSize::SmallInput,
        )
    });
}

fn criterion_benchmark(c: &mut Criterion) {
    criterion_chacha_poly(c);
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
