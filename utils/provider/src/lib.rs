mod chacha20poly1305_trait;
mod evercrypt_provider;
mod hacspec_provider;


fn clone_into_array<A, T>(slice: &[T]) -> A
where
    A: Default + AsMut<[T]>,
    T: Clone,
{
    let mut a = Default::default();
    A::as_mut(&mut a).clone_from_slice(slice);
    a
}

#[cfg(test)]
mod tests {
    use rand::Rng;
    use crate::chacha20poly1305_trait::Chacha20Poly1305;
    use crate::evercrypt_provider::Chacha20Poly1305_Evercrypt;
    use crate::hacspec_provider::Chacha20Poly1305_Hacspec;

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

    #[test]
    fn it_works() {
        chachapoly_enc_dec(&Chacha20Poly1305_Evercrypt::new());
        chachapoly_enc_dec(&Chacha20Poly1305_Hacspec::new());
    }
}
