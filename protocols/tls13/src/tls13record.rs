/* TLS 1.3 Record Layer Encryption: See RFC 8446 Section 5 */
use crate::cryptolib::*;
use crate::tls13formats::*;
use hacspec_lib::*;
// Using newtype pattern below, but the same thing works with tuples too
pub struct CipherState(pub AEADAlgorithm, pub AEKIV, pub u64);

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

pub const ct_app_data : u8 = 0x17; 
pub const ct_handshake: u8 = 0x16; 

pub fn encrypt_record(ct:u8, payload: &Bytes, pad:usize, st: CipherState) -> Res<(Bytes,CipherState)> {
    let CipherState(ae, (k, iv), n) = st;
    let iv_ctr = derive_iv_ctr(&ae,&iv,n);
    let inner_plaintext = payload.concat(&bytes1(ct)).concat(&zeros(pad));
    let clen = inner_plaintext.len() + 16;
    if clen <= 65536 {
        let clenb = u16_to_be_bytes(clen as u16);
        let ad = bytes5(23, 3, 3, clenb[0], clenb[1]);
        let cip = aead_encrypt(&ae, &k, &iv_ctr, &inner_plaintext, &ad)?;
        let rec = ad.concat(&cip);
        Ok((rec,CipherState(ae,(k,iv),n+1)))
    } else {
        Err(payload_too_long)
    }
}

pub fn padlen(b:&Bytes,n:usize) -> usize {
    if n > 0 && b[n-1].declassify() == 0 {1 + padlen(&b,n-1)}
    else {0}
}

pub fn decrypt_record(ciphertext: &Bytes, st: CipherState) -> Res<(u8,Bytes,CipherState)> {
    let CipherState(ae, (k, iv), n) = st;
    let iv_ctr = derive_iv_ctr(&ae, &iv, n);
    let clen = ciphertext.len() - 5;
    if clen <= 65536 && clen > 16 {
        let clenb = u16_to_be_bytes(clen as u16);
        let ad = bytes5(23, 3, 3, clenb[0], clenb[1]);
        check_eq(&ad,&ciphertext.slice_range(0..5))?;
        let cip = ciphertext.slice_range(5..ciphertext.len());
        let plain = aead_decrypt(&ae, &k, &iv_ctr, &cip, &ad)?;
        let payload_len = plain.len() - padlen(&plain,plain.len()) - 1;
        let ct = plain[payload_len].declassify();
        let payload = plain.slice_range(0..payload_len);       
        Ok((ct,payload,CipherState(ae, (k, iv), n+1)))
    } else {
        Err(payload_too_long)
    }
}

pub fn handshake_record(p:&Bytes) -> Res<Bytes> {
    let ty = bytes1(0x16);
    let ver = bytes2(3,3);
    Ok(ty.concat(&ver).concat(&lbytes2(p)?))
}

pub fn check_handshake_record(p:&Bytes) -> Res<(Bytes,usize)> {
    let ty = bytes1(0x16);
    let ver = bytes2(3,3);
    check_eq(&ty,&p.slice_range(0..1))?;
    check_eq(&ver,&p.slice_range(1..3))?;
    let len = check_lbytes2(&p.slice_range(3..p.len()))?;
    Ok((p.slice_range(5..5+len),5+len))
}

pub fn check_ccs_record(p:&Bytes) -> Res<usize> {
    let pref = bytes3(0x14,3,3);
    check_eq(&pref,&p.slice_range(0..3))?;
    let len = check_lbytes2(&p.slice_range(3..p.len()))?;
    Ok(len+5)
}

pub fn check_encrypted_record(p:&Bytes) -> Res<usize> {
    let pref = bytes3(0x17,3,3);
    check_eq(&pref,&p.slice_range(0..3))?;
    let len = check_lbytes2(&p.slice_range(3..p.len()))?;
    Ok(len+5)
}

pub fn check_handshake_message(p:&Bytes) -> Res<(Bytes,usize)> {
    let len = check_lbytes3(&p.slice_range(1..p.len()))?;
    Ok((p.slice_range(0..4+len),4+len))
}
