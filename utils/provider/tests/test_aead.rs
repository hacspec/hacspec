mod test_util;
use test_util::*;

use hacspec_provider::chacha20poly1305_trait::{Chacha20Poly1305, Error};
use hacspec_provider::evercrypt_provider::Chacha20Poly1305Evercrypt;
use hacspec_provider::hacspec_provider::Chacha20Poly1305Hacspec;
use rand::Rng;
// use evercrypt::aead::{self, Aead, Error, Mode, Nonce, Tag};

#[derive(Serialize, Deserialize, Debug, Clone)]
#[allow(non_snake_case)]
struct AeadTestVector {
    algorithm: String,
    generatorVersion: String,
    numberOfTests: usize,
    notes: Option<Value>, // text notes (might not be present), keys correspond to flags
    header: Vec<Value>,   // not used
    testGroups: Vec<TestGroup>,
}

#[derive(Serialize, Deserialize, Debug, Clone)]
#[allow(non_snake_case)]
struct TestGroup {
    ivSize: usize,
    keySize: usize,
    tagSize: usize,
    r#type: String,
    tests: Vec<Test>,
}

#[derive(Serialize, Deserialize, Debug, Clone)]
#[allow(non_snake_case)]
struct Test {
    tcId: usize,
    comment: String,
    key: String,
    iv: String,
    aad: String,
    msg: String,
    ct: String,
    tag: String,
    result: String,
    flags: Vec<String>,
}

impl ReadFromFile for AeadTestVector {}

#[allow(non_snake_case)]
#[test]
fn test_wycheproof() {
    let chacha_poly_tests: AeadTestVector =
        AeadTestVector::from_file("tests/chacha20_poly1305_test.json");

    let num_tests = chacha_poly_tests.numberOfTests;
    let mut skipped_tests = 0;
    let mut tests_run = 0;
    assert_eq!(chacha_poly_tests.algorithm, "CHACHA20-POLY1305");

    test_group(chacha_poly_tests, &mut skipped_tests, &mut tests_run);

    fn test_group(test_vec: AeadTestVector, skipped_tests: &mut usize, tests_run: &mut usize) {
        for testGroup in test_vec.testGroups.iter() {
            assert_eq!(testGroup.r#type, "AeadTest");
            assert_eq!(testGroup.keySize, 256);
            let invalid_iv = if testGroup.ivSize != 96 { true } else { false };

            for test in testGroup.tests.iter() {
                let valid = test.result.eq("valid");
                if invalid_iv {
                    // AEAD requires input of a 12-byte nonce.
                    let result = std::panic::catch_unwind(|| {
                        let _nonce: [u8; 12] = hex_str_to_array(&test.iv);
                    });
                    assert!(result.is_err());
                    *skipped_tests += 1;
                    continue;
                }
                let invalid_iv = if test.comment == "invalid nonce size" || invalid_iv {
                    true
                } else {
                    false
                };
                println!("Test {:?}: {:?}", test.tcId, test.comment);
                let nonce: [u8; 12] = hex_str_to_array(&test.iv);
                let msg = hex_str_to_bytes(&test.msg);
                let aad = hex_str_to_bytes(&test.aad);
                let exp_cipher = hex_str_to_bytes(&test.ct);
                let exp_tag: [u8; 16] = hex_str_to_array(&test.tag);
                let key: [u8; 32] = hex_str_to_array(&test.key);

                let cipher = Chacha20Poly1305Hacspec::new();

                // let cipher = Aead::new(algorithm, &key).unwrap();
                let (ctxt, tag) = match cipher.encrypt(&key, &nonce, &aad, &msg) {
                    Ok(v) => v,
                    Err(e) => {
                        if invalid_iv {
                            assert_eq!(e, Error(format!("Error")));
                        } else {
                            println!("Encrypt failed unexpectedly {:?}", e);
                            assert!(false);
                        }
                        *tests_run += 1;
                        continue;
                    }
                };
                if valid {
                    assert_eq!(tag, exp_tag);
                } else {
                    assert_ne!(tag, exp_tag);
                }
                assert_eq!(ctxt, exp_cipher);
                let msg_decrypted = match cipher.decrypt(&key, &nonce, &aad, &ctxt, &tag) {
                    Ok(m) => m,
                    Err(_) => {
                        assert!(!valid);
                        msg.clone()
                    }
                };
                assert_eq!(msg, msg_decrypted);
                *tests_run += 1;
            }
        }
    }
    // Check that we ran all tests.
    println!(
        "Ran {} out of {} tests and skipped {}.",
        tests_run, num_tests, skipped_tests
    );
    assert_eq!(num_tests - skipped_tests, tests_run);
}

#[test]
fn self_test() {
    fn chachapoly_enc_dec(cipher: &dyn Chacha20Poly1305) {
        let key = cipher.key_gen();
        let nonce = cipher.nonce_gen();
        let aad = rand::thread_rng().gen::<[u8; 10]>();
        let m = rand::thread_rng().gen::<[u8; 32]>();

        let (c, tag) = cipher.encrypt(&key, &nonce, &aad, &m).unwrap();
        let m_dec = match cipher.decrypt(&key, &nonce, &aad, &c, &tag) {
            Err(e) => {
                println!("Error decrypting {:?}", e);
                vec![]
            }
            Ok(v) => v,
        };
        assert_eq!(m[..], m_dec[..]);
    }
    chachapoly_enc_dec(&Chacha20Poly1305Evercrypt::new());
    chachapoly_enc_dec(&Chacha20Poly1305Hacspec::new());
}

#[test]
fn evercrypt_test() {
    let evercrypt_cipher = Chacha20Poly1305Evercrypt::new();
    let hacspec_cipher = Chacha20Poly1305Hacspec::new();

    let key = evercrypt_cipher.key_gen();
    let nonce = evercrypt_cipher.nonce_gen();
    let aad = rand::thread_rng().gen::<[u8; 10]>();
    let mut m = [0u8; 345];
    rand::thread_rng().fill(&mut m[..]);

    let (c, tag) = evercrypt_cipher.encrypt(&key, &nonce, &aad, &m).unwrap();
    let m_dec = match hacspec_cipher.decrypt(&key, &nonce, &aad, &c, &tag) {
        Err(e) => {
            println!("Error decrypting {:?}", e);
            vec![]
        }
        Ok(v) => v,
    };
    assert_eq!(m[..], m_dec[..]);
}
