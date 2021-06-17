use hacspec_lib::*;
use hacspec_p256::*;
use hacspec_sha256::*;

pub type PublicKey = Affine;
pub type SecretKey = Scalar;
pub type Signature = (Scalar, Scalar); // (r, s)
pub type SignatureResult = Result<Signature, u8>;
pub type VerifyResult = Result<(), u8>;

pub const ZERO_NONCE: u8 = 1;
pub const INVALID_NONCE: u8 = 2;
pub const INVALID_SIGNATURE: u8 = 3;

pub fn sign(payload: &ByteSeq, sk: SecretKey, nonce: Scalar) -> SignatureResult {
    if nonce.equal(Scalar::ZERO()) {
        // We should really return here.
        // success = false;
        return SignatureResult::Err(ZERO_NONCE);
    }
    let (k_x, _k_y) = point_mul_base(nonce)?;
    let r = Scalar::from_byte_seq_be(k_x.to_byte_seq_be());
    if r.equal(Scalar::ZERO()) {
        // We should really return here.
        // success = false;
        return SignatureResult::Err(INVALID_NONCE);
    }
    let payload_hash = hash(payload);
    let payload_hash = Scalar::from_byte_seq_be(payload_hash);
    let rsk = r * sk;
    let hash_rsk = payload_hash + rsk;
    let nonce_inv = nonce.inv();
    let s = nonce_inv * hash_rsk;

    SignatureResult::Ok((r, s))
}

pub fn verify(payload: &ByteSeq, pk: PublicKey, signature: Signature) -> VerifyResult {
    // signature = (r, s) must be in [1, n-1] because they are Scalars
    let (r, s) = signature;
    let payload_hash = hash(payload);
    let payload_hash = Scalar::from_byte_seq_be(payload_hash);
    let s_inv = s.inv();

    // R' = (h * s1) * G + (r * s1) * pubKey
    let u1 = payload_hash * s_inv;
    let u1 = point_mul_base(u1)?;

    let u2 = r * s_inv;
    let u2 = point_mul(u2, pk)?;
    let (x, _y) = point_add(u1, u2)?;
    let x = Scalar::from_byte_seq_be(x.to_byte_seq_be());
    if x == r {
        VerifyResult::Ok(())
    } else {
        VerifyResult::Err(INVALID_SIGNATURE)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn self_test() {
        let sk =
            Scalar::from_hex("ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632550");
        let pk = (
            FieldElement::from_hex(
                "6B17D1F2E12C4247F8BCE6E563A440F277037D812DEB33A0F4A13945D898C296",
            ),
            FieldElement::from_hex(
                "B01CBD1C01E58065711814B583F061E9D431CCA994CEA1313449BF97C840AE0A",
            ),
        );
        let msg = ByteSeq::from_public_slice(b"hacspec ecdsa p256 sha256 self test");
        let nonce = Scalar::from_be_bytes(&[1, 2, 3, 4, 5, 6, 7, 8, 9, 0]);

        let signature = sign(&msg, sk, nonce).expect("Error signing");
        assert!(verify(&msg, pk, signature).is_ok());
    }

    #[test]
    fn kat_sign() {
        let pk = (
            FieldElement::from_hex(
                "2927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838",
            ),
            FieldElement::from_hex(
                "c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
            ),
        );
        let msg = ByteSeq::from_hex("313233343030");
        let sig = (
            Scalar::from_hex("2ba3a8be6b94d5ec80a6d9d1190a436effe50d85a1eee859b8cc6af9bd5c2e18"),
            Scalar::from_hex("b329f479a2bbd0a5c384ee1493b1f5186a87139cac5df4087c134b49156847db"),
        );
        assert!(verify(&msg, pk, sig).is_ok());
    }
}
