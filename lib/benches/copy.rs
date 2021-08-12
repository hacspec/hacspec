#[macro_use]
extern crate criterion;

use criterion::{BatchSize, Criterion};
use hacspec_dev::prelude::*;
use hacspec_lib::prelude::*;

fn bench(c: &mut Criterion) {
    for chunk_size in (10..2000).step_by(500) {
        c.bench_function(&format!("Seq slice no-copy {}", chunk_size), |b| {
            b.iter_batched(
                || ByteSeq::from_public_slice(&random_byte_vec(2048)),
                |seq| {
                    let _new_seq_slice = seq.into_slice_range(40..40 + chunk_size);
                },
                BatchSize::SmallInput,
            );
        });
        c.bench_function(&format!("Seq slice copy {}", chunk_size), |b| {
            b.iter_batched(
                || ByteSeq::from_public_slice(&random_byte_vec(2048)),
                |seq| {
                    let _new_seq_slice = seq.slice_range(40..40 + chunk_size);
                },
                BatchSize::SmallInput,
            );
        });
    }
    c.bench_function(&format!("Seq concat no-copy"), |b| {
        b.iter_batched(
            || {
                let seq1 = ByteSeq::from_public_slice(&random_byte_vec(2048));
                let seq2 = ByteSeq::from_public_slice(&random_byte_vec(2048));
                (seq1, seq2)
            },
            |(seq1, seq2)| {
                let _new_seq = seq1.concat_owned(seq2);
            },
            BatchSize::SmallInput,
        );
    });
    c.bench_function(&format!("Seq concat copy"), |b| {
        b.iter_batched(
            || {
                let seq1 = ByteSeq::from_public_slice(&random_byte_vec(2048));
                let seq2 = ByteSeq::from_public_slice(&random_byte_vec(2048));
                (seq1, seq2)
            },
            |(seq1, seq2)| {
                let _new_seq = seq1.concat(&seq2);
            },
            BatchSize::SmallInput,
        );
    });
}

criterion_group!(benches, bench);
criterion_main!(benches);
