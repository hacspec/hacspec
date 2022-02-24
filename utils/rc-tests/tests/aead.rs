mod test_util;
use test_util::*;

use chacha20poly1305::ChaCha20Poly1305 as RustCrypto_ChaCha20Poly1305;
use evercrypt_provider::Chacha20Poly1305 as Evercrypt_Chacha20Poly1305;
use hacspec_provider::{
    aead::consts::U12, Aead, AeadCore, Chacha20Poly1305 as Hacspec_Chacha20Poly1305, Key, NewAead,
    Nonce, Payload,
};

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

    // let providers: [T] = vec![Hacspec_Chacha20Poly1305, Evercrypt_Chacha20Poly1305];

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

                fn test_case<T: Aead>(
                    cipher: T,
                    nonce: &[u8; 12],
                    msg: &[u8],
                    aad: &[u8],
                    exp_tag: [u8; 16],
                    exp_cipher: &[u8],
                    tests_run: &mut usize,
                    invalid_iv: bool,
                    valid: bool,
                ) where
                    T: AeadCore<NonceSize = U12>,
                {
                    let nonce = Nonce::from_slice(nonce);
                    let ctxt = match cipher.encrypt(
                        nonce,
                        Payload {
                            msg: &msg,
                            aad: &aad,
                        },
                    ) {
                        Ok(v) => v,
                        Err(_) => {
                            assert!(invalid_iv);
                            *tests_run += 1;
                            return;
                        }
                    };
                    if valid {
                        assert_eq!(ctxt[ctxt.len() - 16..], exp_tag);
                    } else {
                        assert_ne!(ctxt[ctxt.len() - 16..], exp_tag);
                    }
                    assert_eq!(&ctxt[..ctxt.len() - 16], exp_cipher);
                    let msg_decrypted = match cipher.decrypt(
                        nonce,
                        Payload {
                            msg: &ctxt,
                            aad: &aad,
                        },
                    ) {
                        Ok(m) => m,
                        Err(_) => {
                            assert!(!valid);
                            msg.to_vec()
                        }
                    };
                    assert_eq!(&msg[..], &msg_decrypted[..msg.len()]);
                    *tests_run += 1;
                }

                test_case(
                    Hacspec_Chacha20Poly1305::new(Key::from_slice(&key)),
                    &nonce,
                    &msg,
                    &aad,
                    exp_tag,
                    &exp_cipher,
                    tests_run,
                    invalid_iv,
                    valid,
                );
                test_case(
                    Evercrypt_Chacha20Poly1305::new(Key::from_slice(&key)),
                    &nonce,
                    &msg,
                    &aad,
                    exp_tag,
                    &exp_cipher,
                    tests_run,
                    invalid_iv,
                    valid,
                );
                test_case(
                    RustCrypto_ChaCha20Poly1305::new(Key::from_slice(&key)),
                    &nonce,
                    &msg,
                    &aad,
                    exp_tag,
                    &exp_cipher,
                    tests_run,
                    invalid_iv,
                    valid,
                );
            }
        }
    }
    // Check that we ran all tests.
    println!(
        "Ran {} out of {} tests and skipped {}.",
        tests_run, num_tests, skipped_tests
    );
    assert_eq!((num_tests - skipped_tests) * 3, tests_run);
}
