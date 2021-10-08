use hacspec_derive::*;
use hacspec_lib::prelude::*;

#[allow(dead_code)]
#[derive(Default, Clone, Debug, Numeric)]
struct NumericStruct {
    fst: PublicSeq<u8>,
    snd: PublicSeq<u8>,
}

#[allow(dead_code)]
#[derive(Default, Clone, Debug, Numeric)]
struct NumericPair(PublicSeq<u8>, PublicSeq<u8>);

#[allow(dead_code)]
#[derive(Default, Clone, Debug, Numeric)]
struct NumericEmpty {}

#[test]
fn test_struct() -> () {
    let s1 = NumericStruct {
        fst: PublicSeq::from_vec(vec![1, 2]),
        snd: PublicSeq::from_vec(vec![0, 1, 2]),
    };
    let s2 = NumericStruct {
        fst: PublicSeq::from_vec(vec![1, 2]),
        snd: PublicSeq::from_vec(vec![0, 1, 2]),
    };
    let s3 = s1.clone() + s2.clone();
    let s4 = s3 - s1;
    let _ = s2 * s4;
}

#[test]
fn test_pair() -> () {
    let s1 = NumericPair(
        PublicSeq::from_vec(vec![1, 2]),
        PublicSeq::from_vec(vec![0, 1, 2]),
    );
    let s2 = NumericPair(
        PublicSeq::from_vec(vec![1, 2]),
        PublicSeq::from_vec(vec![0, 1, 2]),
    );
    let s3 = s1.clone() + s2.clone();
    let s4 = s3 - s1;
    let _ = s2 * s4;
}

#[test]
fn test_empty() -> () {
    let s1 = NumericEmpty {};
    let s2 = NumericEmpty {};
    let s3 = s1.clone() + s2.clone();
    let s4 = s3 - s1;
    let _ = s2 * s4;
}
