// TLS 1.3 Record Layer Computations

use super::*;

// Import hacspec and all needed definitions.
use hacspec_lib::*;

pub fn derive_iv_ctr(ae: &AEADAlgorithm, iv: &AEIV, n:u64) -> AEIV {
    let counter = bytes(&U64_to_be_bytes(U64(n)));
    let mut iv_ctr = AEIV::new(iv.len());
    for i in 0..iv.len()-8 {
        iv_ctr[i] = iv[i];
    }
    for i in 0..8 {
        iv_ctr[i+iv.len()-8] = iv[i+iv.len()-8] ^ counter[i];
    }
    iv_ctr
}

pub fn encrypt_record_payload(ae:&AEADAlgorithm, kiv: &AEKIV, n:u64, ct:ContentType, payload: Bytes, pad:usize) -> Res<Bytes> {
    let (k,iv) = kiv;
    let iv_ctr = derive_iv_ctr(&ae,&iv,n);
    let inner_plaintext = payload.concat_owned(bytes1(content_type(ct))).concat_owned(zeros(pad));
    let clen = inner_plaintext.len() + 16;
    if clen <= 65536 {
        let clen0 = clen as u8;
        let clen1 = (clen / 256) as u8;
        let ad = bytes5(23, 3, 3, clen1, clen0);
        let cip = aead_encrypt(&ae, &k, &iv_ctr, &inner_plaintext, &ad)?;
        let rec = ad.concat_owned(cip);
        Ok(rec)
    } else {
        Err(payload_too_long)
    }
}

pub fn padlen(b:&Bytes,n:usize) -> usize {
    if n > 0 && b[n-1].declassify() == 0 {1 + padlen(&b,n-1)}
    else {0}
}
pub fn decrypt_record_payload(ae:&AEADAlgorithm, kiv:&AEKIV, n:u64, ciphertext: Bytes) -> Res<(ContentType,Bytes)> {
    let (k,iv) = kiv;
    let iv_ctr = derive_iv_ctr(&ae, &iv, n);
    let clen = ciphertext.len() - 5;
    if clen <= 65536 && clen > 16 {
        let clen0 = clen as u8;
        let clen1 = (clen / 256) as u8;
        let ad = bytes5(23, 3, 3, clen1, clen0);
        check_eq(&ad,&ciphertext.slice_range(0..5))?;
        let (_,cip) = ciphertext.split_off(5);
        let plain = aead_decrypt(&ae, &k, &iv_ctr, &cip, &ad)?;
        let payload_len = plain.len() - padlen(&plain,plain.len()) - 1;
        let ct = get_content_type(plain[payload_len].declassify())?;
        let (payload,_) = plain.split_off(payload_len);       
        Ok((ct,payload))
    } else {
        Err(payload_too_long)
    }
}

