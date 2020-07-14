// Import hacspec and all needed definitions.
use hacspec::prelude::*;
use hacspec_derive::*;

// array!(IrrPos, 3, u32);
// array!(IrrCoeff, 3, i32);
// /// Struct to use for irreducible polynomials.
// #[derive(Default, Clone, Debug, Numeric)]
// struct SparseIrrPoly(IrrPos, IrrCoeff);

/// Struct to use for sparse polynomials.
#[derive(Default, Clone, Debug, Numeric)]
struct SparsePoly(PublicSeq<u32>, PublicSeq<i32>);

struct NtruPrime {
    p: u32,
    q: u32,
    w: usize,
    irr: SparsePoly,
}

enum Mode {
    NtruPrime653 = 0,
    NtruPrime761 = 1,
    NtruPrime857 = 2,
}

fn get_ntru_prime(mode: Mode) -> NtruPrime {
    match mode {
        NtruPrime653 => NtruPrime {
            p: 653,
            q: 4621,
            w: 288,
            irr: SparsePoly(
                PublicSeq::from_vec(vec![0, 1, 653]),
                PublicSeq::from_native_slice(&[-1, -1, 1]),
            ),
        },
        NtruPrime761 => NtruPrime {
            p: 761,
            q: 4591,
            w: 286,
            irr: SparsePoly(
                PublicSeq::from_native_slice(&[0, 1, 761]),
                PublicSeq::from_native_slice(&[-1, -1, 1]),
            ),
        },
        NtruPrime857 => NtruPrime {
            p: 857,
            q: 5167,
            w: 322,
            irr: SparsePoly(
                PublicSeq::from_native_slice(&[0, 1, 857]),
                PublicSeq::from_native_slice(&[-1, -1, 1]),
            ),
        },
    }
}

// FIXME: Where should this go?
fn rand_coefficients(num: usize) -> PublicSeq<i32> {
    let mut out = PublicSeq::<i32>::new(num);
    const vals: [i32; 2] = [-1, 1];
    for i in 0..num {
        out[i] = vals[rand::thread_rng().gen_range(0, 2)];
    }
    out
}

// FIXME: Where should this go? Requires while loop or other weird construction.
fn rand_pos(num: usize, deg: u32) -> PublicSeq<u32> {
    let mut out = PublicSeq::<u32>::new(num);
    let mut done = false;
    let mut pos = 0;
    while !done {
        let mut tmp: u32 = rand::thread_rng().gen_range(0, deg);
        for i in 0..pos {
            if out[i] == tmp {
                continue;
            }
        }
        out[pos] = tmp;
        if pos == num - 1 {
            done = true;
        }
        pos += 1;
    }
    out
}

/// Create a random polynomial of degree at most `h_deg` with `w` non-zero coefficents (-1 or 1).
/// XXX: This isn't sorted
fn rand_poly(w: usize, h_deg: u32) -> SparsePoly {
    let coefficients = rand_coefficients(w);
    let positions = rand_pos(w, h_deg);

    SparsePoly(positions, coefficients)
}

// fn invertible_array(alg: NtruPrime, )

#[test]
fn test_rand_poly() {
    let ntru = get_ntru_prime(Mode::NtruPrime653);
    let rand_sparse = rand_poly(ntru.w, ntru.q);
    println!("{:?}", rand_sparse);
}
