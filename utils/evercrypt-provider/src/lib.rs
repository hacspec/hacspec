mod provider;
pub use aead::Error;
pub use provider::{
    Aead, AeadCore, AeadInPlace, Chacha20Poly1305, Key, NewAead, Nonce, Payload, Tag,
};

#[test]
fn test_rc_provider() {
    let key = Chacha20Poly1305::key_gen();
    let nonce = Chacha20Poly1305::nonce_gen();
    let cipher = Chacha20Poly1305::new(&key);
    const MESSAGE: [u8; 10] = [1, 2, 3, 4, 5, 6, 7, 8, 9, 0];
    let mut message = MESSAGE;
    let tag = cipher
        .encrypt_in_place_detached(&nonce, &[], &mut message)
        .unwrap();
    cipher
        .decrypt_in_place_detached(&nonce, &[], &mut message, &tag)
        .unwrap();
    assert_eq!(MESSAGE, message);

    let payload = Payload {
        msg: &message,
        aad: &[],
    };
    let ctxt_tag = cipher.encrypt(&nonce, payload).unwrap();
    let payload = Payload {
        msg: &ctxt_tag,
        aad: &[],
    };
    let ptxt = cipher.decrypt(&nonce, payload).unwrap();
    assert_eq!(&MESSAGE[..], &ptxt[..]);
}
