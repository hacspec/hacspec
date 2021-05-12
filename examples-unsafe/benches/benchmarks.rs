#[macro_use]
extern crate criterion;
use criterion::{BatchSize, Criterion};

use hacspec_chacha20::*;
use hacspec_chacha20poly1305::*;
use hacspec_lib::prelude::*;
use hacspec_poly1305::*;
use hacspec_sha3::*;
use unsafe_hacspec_examples::aes_gcm::{
    aes::{aes128_decrypt, aes128_encrypt, aes256_decrypt, aes256_encrypt, Key128, Key256, Nonce},
    gf128::{gmac, Key as GcmKey},
    *,
};
use unsafe_hacspec_examples::blake2::blake2b::*;
use unsafe_hacspec_examples::curve25519::*;
use unsafe_hacspec_examples::ec::{
    p256::{point_mul as p256_point_mul, FieldElement as P256FieldElement, Scalar as P256Scalar},
    p384::{point_mul as p384_point_mul, FieldElement as P384FieldElement, Scalar as P384Scalar},
    Affine,
};
use unsafe_hacspec_examples::sha2::hash as sha256;

fn randombytes(n: usize) -> Vec<u8> {
    use rand::rngs::OsRng;
    use rand::RngCore;

    let mut bytes = vec![0u8; n];
    OsRng.fill_bytes(&mut bytes);
    bytes
}

fn criterion_aes_gcm(c: &mut Criterion) {
    c.bench_function("GCM", |b| {
        b.iter_batched(
            || {
                let key = GcmKey::from_public_slice(&randombytes(16));
                let data = ByteSeq::from_public_slice(&randombytes(1_000));
                (data, key)
            },
            |(data, key)| {
                let _tag = gmac(&data, key);
            },
            BatchSize::SmallInput,
        )
    });

    c.bench_function("AES 128 encrypt", |b| {
        b.iter_batched(
            || {
                let key = Key128::from_public_slice(&randombytes(16));
                let nonce = Nonce::from_public_slice(&randombytes(12));
                let data = ByteSeq::from_public_slice(&randombytes(10_000));
                (data, nonce, key)
            },
            |(data, nonce, key)| {
                let _c = aes128_encrypt(key, nonce, U32(0), &data);
            },
            BatchSize::SmallInput,
        )
    });

    c.bench_function("AES 128 decrypt", |b| {
        b.iter_batched(
            || {
                let key = Key128::from_public_slice(&randombytes(16));
                let nonce = Nonce::from_public_slice(&randombytes(12));
                let data = ByteSeq::from_public_slice(&randombytes(10_000));
                let ctxt = aes128_encrypt(key, nonce, U32(0), &data);
                (ctxt, nonce, key)
            },
            |(ctxt, nonce, key)| {
                let _m = aes128_decrypt(key, nonce, U32(0), &ctxt);
            },
            BatchSize::SmallInput,
        )
    });

    c.bench_function("AES 256 encrypt", |b| {
        b.iter_batched(
            || {
                let key = Key256::from_public_slice(&randombytes(32));
                let nonce = Nonce::from_public_slice(&randombytes(12));
                let data = ByteSeq::from_public_slice(&randombytes(10_000));
                (data, nonce, key)
            },
            |(data, nonce, key)| {
                let _c = aes256_encrypt(key, nonce, U32(0), &data);
            },
            BatchSize::SmallInput,
        )
    });

    c.bench_function("AES 256 decrypt", |b| {
        b.iter_batched(
            || {
                let key = Key256::from_public_slice(&randombytes(32));
                let nonce = Nonce::from_public_slice(&randombytes(12));
                let data = ByteSeq::from_public_slice(&randombytes(10_000));
                let ctxt = aes256_encrypt(key, nonce, U32(0), &data);
                (ctxt, nonce, key)
            },
            |(ctxt, nonce, key)| {
                let _m = aes256_decrypt(key, nonce, U32(0), &ctxt);
            },
            BatchSize::SmallInput,
        )
    });

    c.bench_function("AES GCM 128 encrypt", |b| {
        b.iter_batched(
            || {
                let key = Key128::from_public_slice(&randombytes(16));
                let nonce = Nonce::from_public_slice(&randombytes(12));
                let data = Seq::<U8>::from_public_slice(&randombytes(1_000));
                let aad = Seq::<U8>::from_public_slice(&randombytes(1_000));
                (data, nonce, aad, key)
            },
            |(data, nonce, aad, key)| {
                let (_cipher, _tag) = encrypt_aes128(key, nonce, &aad, &data);
            },
            BatchSize::SmallInput,
        )
    });

    c.bench_function("AES GCM 128 decrypt", |b| {
        b.iter_batched(
            || {
                let key = Key128::from_public_slice(&randombytes(16));
                let nonce = Nonce::from_public_slice(&randombytes(12));
                let data = Seq::<U8>::from_public_slice(&randombytes(1_000));
                let aad = Seq::<U8>::from_public_slice(&randombytes(1_000));
                let (cipher, tag) = encrypt_aes128(key, nonce, &aad, &data);
                (cipher, tag, nonce, aad, key)
            },
            |(cipher, tag, nonce, aad, key)| {
                let _decrypted_msg = decrypt_aes128(key, nonce, &aad, &cipher, tag).unwrap();
            },
            BatchSize::SmallInput,
        )
    });

    c.bench_function("AES GCM 256 encrypt", |b| {
        b.iter_batched(
            || {
                let key = Key256::from_public_slice(&randombytes(32));
                let nonce = Nonce::from_public_slice(&randombytes(12));
                let data = Seq::<U8>::from_public_slice(&randombytes(1_000));
                let aad = Seq::<U8>::from_public_slice(&randombytes(1_000));
                (data, nonce, aad, key)
            },
            |(data, nonce, aad, key)| {
                let (_cipher, _tag) = encrypt_aes256(key, nonce, &aad, &data);
            },
            BatchSize::SmallInput,
        )
    });

    c.bench_function("AES GCM 256 decrypt", |b| {
        b.iter_batched(
            || {
                let key = Key256::from_public_slice(&randombytes(16));
                let nonce = Nonce::from_public_slice(&randombytes(12));
                let data = Seq::<U8>::from_public_slice(&randombytes(1_000));
                let aad = Seq::<U8>::from_public_slice(&randombytes(1_000));
                let (cipher, tag) = encrypt_aes256(key, nonce, &aad, &data);
                (cipher, tag, nonce, aad, key)
            },
            |(cipher, tag, nonce, aad, key)| {
                let _decrypted_msg = decrypt_aes256(key, nonce, &aad, &cipher, tag).unwrap();
            },
            BatchSize::SmallInput,
        )
    });
}

fn criterion_blake2(c: &mut Criterion) {
    c.bench_function("Blake2b", |b| {
        b.iter_batched(
            || {
                let data = Seq::<U8>::from_public_slice(&randombytes(10_000));
                data
            },
            |data| {
                let _h = blake2b(&data);
            },
            BatchSize::SmallInput,
        )
    });
}

fn criterion_p256(c: &mut Criterion) {
    // TODO: allow key generation and make these random
    c.bench_function("P256 ECDH", |b| {
        b.iter_batched(
            || {
                let k = P256Scalar::from_hex(
                    "0612465c89a023ab17855b0a6bcebfd3febb53aef84138647b5352e02c10c346",
                );
                let p = Affine(
                    P256FieldElement::from_hex(
                        "62d5bd3372af75fe85a040715d0f502428e07046868b0bfdfa61d731afe44f26",
                    ),
                    P256FieldElement::from_hex(
                        "ac333a93a9e70a81cd5a95b5bf8d13990eb741c8c38872b4a07d275a014e30cf",
                    ),
                );
                (k, p)
            },
            |(k, p)| {
                let _r = p256_point_mul(k, p);
            },
            BatchSize::SmallInput,
        )
    });
}

fn criterion_p384(c: &mut Criterion) {
    // TODO: allow key generation and make these random
    c.bench_function("P384 ECDH", |b| {
        b.iter_batched(
            || {
                let k = P384Scalar::from_hex(
                    "766e61425b2da9f846c09fc3564b93a6f8603b7392c785165bf20da948c49fd1fb1dee4edd64356b9f21c588b75dfd81",
                );
                let p = Affine(
                    P384FieldElement::from_hex(
                        "790a6e059ef9a5940163183d4a7809135d29791643fc43a2f17ee8bf677ab84f791b64a6be15969ffa012dd9185d8796",
                    ),
                    P384FieldElement::from_hex(
                        "d9b954baa8a75e82df711b3b56eadff6b0f668c3b26b4b1aeb308a1fcc1c680d329a6705025f1c98a0b5e5bfcb163caa",
                    ),
                );
                (k, p)
            },
            |(k, p)| {
                let _r = p384_point_mul(k, p);
            },
            BatchSize::SmallInput,
        )
    });
}

fn criterion_fips202(c: &mut Criterion) {
    c.bench_function("FIPS 202 (SHA 3 224)", |b| {
        b.iter_batched(
            || ByteSeq::from_public_slice(&randombytes(10_000)),
            |data| {
                let _h = sha3224(&data);
            },
            BatchSize::SmallInput,
        )
    });

    c.bench_function("FIPS 202 (SHA 3 256)", |b| {
        b.iter_batched(
            || ByteSeq::from_public_slice(&randombytes(10_000)),
            |data| {
                let _h = sha3256(&data);
            },
            BatchSize::SmallInput,
        )
    });

    c.bench_function("FIPS 202 (SHA 3 384)", |b| {
        b.iter_batched(
            || ByteSeq::from_public_slice(&randombytes(10_000)),
            |data| {
                let _h = sha3384(&data);
            },
            BatchSize::SmallInput,
        )
    });

    c.bench_function("FIPS 202 (SHA 3 512)", |b| {
        b.iter_batched(
            || ByteSeq::from_public_slice(&randombytes(10_000)),
            |data| {
                let _h = sha3512(&data);
            },
            BatchSize::SmallInput,
        )
    });
}

fn criterion_sha2(c: &mut Criterion) {
    c.bench_function("SHA 2 256", |b| {
        b.iter_batched(
            || ByteSeq::from_public_slice(&randombytes(10_000)),
            |data| {
                let _h = sha256(&data);
            },
            BatchSize::SmallInput,
        )
    });
}

fn criterion_benchmark(c: &mut Criterion) {
    criterion_aes_gcm(c);
    criterion_blake2(c);
    criterion_fips202(c);
    criterion_p256(c);
    criterion_p384(c);
    criterion_sha2(c);
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
