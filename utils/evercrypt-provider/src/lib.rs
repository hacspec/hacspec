mod provider;
use aead::Payload;
pub use provider::Chacha20Poly1305Evercrypt;

pub mod rc_provider;

fn clone_into_array<A, T>(slice: &[T]) -> A
where
    A: Default + AsMut<[T]>,
    T: Clone,
{
    let mut a = Default::default();
    A::as_mut(&mut a).clone_from_slice(slice);
    a
}

#[test]
fn test_rc_provider() {
    use rc_provider::*;
    let key = Chacha20Poly1305RC::key_gen();
    let nonce = Chacha20Poly1305RC::nonce_gen();
    let cipher = Chacha20Poly1305RC::new(&key);
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
