/* TLS 1.3 Record Layer Encryption: See RFC 8446 Section 5 */
use crate::cryptolib::*;
use crate::tls13formats::*;
use hacspec_lib::*;
// Using newtype pattern below, but the same thing works with tuples too

pub struct ClientCipherState0(pub AEADAlgorithm, pub AEKIV, pub u64, pub KEY);
pub struct ServerCipherState0(pub AEADAlgorithm, pub AEKIV, pub u64, pub KEY);
pub struct DuplexCipherStateH(pub AEADAlgorithm, pub AEKIV, pub u64, pub AEKIV, pub u64);
pub struct DuplexCipherState1(pub AEADAlgorithm, pub AEKIV, pub u64, pub AEKIV, pub u64, pub KEY);

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
pub const ct_alert: u8 = 0x15; 

pub fn encrypt_record_payload(ae:&AEADAlgorithm, kiv: &AEKIV, n:u64, ct:u8, payload: &Bytes, pad:usize) -> Res<Bytes> {
    let (k,iv) = kiv;
    let iv_ctr = derive_iv_ctr(&ae,&iv,n);
    let inner_plaintext = payload.concat(&bytes1(ct)).concat(&zeros(pad));
    let clen = inner_plaintext.len() + 16;
    if clen <= 65536 {
        let clenb = u16_to_be_bytes(clen as u16);
        let ad = bytes5(23, 3, 3, clenb[0], clenb[1]);
        let cip = aead_encrypt(&ae, &k, &iv_ctr, &inner_plaintext, &ad)?;
        let rec = ad.concat(&cip);
        Ok(rec)
    } else {
        Err(payload_too_long)
    }
}

pub fn padlen(b:&Bytes,n:usize) -> usize {
    if n > 0 && b[n-1].declassify() == 0 {1 + padlen(&b,n-1)}
    else {0}
}
pub fn decrypt_record_payload(ae:&AEADAlgorithm, kiv:&AEKIV, n:u64, ciphertext: &Bytes) -> Res<(U8,Bytes)> {
    let (k,iv) = kiv;
    let iv_ctr = derive_iv_ctr(&ae, &iv, n);
    let clen = ciphertext.len() - 5;
    if clen <= 65536 && clen > 16 {
        let clenb = u16_to_be_bytes(clen as u16);
        let ad = bytes5(23, 3, 3, clenb[0], clenb[1]);
        check_eq(&ad,&ciphertext.slice_range(0..5))?;
        let cip = ciphertext.slice_range(5..ciphertext.len());
        let plain = aead_decrypt(&ae, &k, &iv_ctr, &cip, &ad)?;
        let payload_len = plain.len() - padlen(&plain,plain.len()) - 1;
        let ct = plain[payload_len];
        let payload = plain.slice_range(0..payload_len);       
        Ok((ct,payload))
    } else {
        Err(payload_too_long)
    }
}

pub fn encrypt_zerortt(payload:&Bytes, pad:usize, st: ClientCipherState0) -> Res<(Bytes,ClientCipherState0)> {
    let ClientCipherState0(ae, kiv, n, exp) = st;
    let rec = encrypt_record_payload(&ae,&kiv,n,ct_app_data,payload,pad)?;
    Ok((rec,ClientCipherState0(ae,kiv,n+1, exp)))
}

pub fn decrypt_zerortt(ciphertext:&Bytes, st: ServerCipherState0) -> Res<(Bytes,ServerCipherState0)> {
    let ServerCipherState0(ae, kiv, n, exp) = st;
    let (ct,payload) = decrypt_record_payload(&ae,&kiv,n,ciphertext)?;
    check_eq1(ct,U8(ct_app_data))?;
    Ok((payload,ServerCipherState0(ae,kiv,n+1,exp)))
}

pub fn encrypt_handshake(payload:&Bytes, pad:usize, st: DuplexCipherStateH) -> Res<(Bytes,DuplexCipherStateH)> {
    let DuplexCipherStateH(ae, kiv, n, x, y) = st;
    let rec = encrypt_record_payload(&ae,&kiv,n,ct_handshake,payload,pad)?;
    Ok((rec,DuplexCipherStateH(ae,kiv,n+1, x, y)))
}

pub fn decrypt_handshake(ciphertext:&Bytes, st: DuplexCipherStateH) -> Res<(Bytes,DuplexCipherStateH)> {
    let DuplexCipherStateH(ae, x, y, kiv, n) = st;
    let (ct,payload) = decrypt_record_payload(&ae,&kiv,n,ciphertext)?;
    check_eq1(ct,U8(ct_handshake))?;
    Ok((payload,DuplexCipherStateH(ae, x, y, kiv, n+1)))
}

pub fn encrypt_data(payload:&Bytes, pad:usize, st: DuplexCipherState1) -> Res<(Bytes,DuplexCipherState1)> {
    let DuplexCipherState1(ae, kiv, n, x, y, exp) = st;
    let rec = encrypt_record_payload(&ae,&kiv,n,ct_app_data,payload,pad)?;
    Ok((rec,DuplexCipherState1(ae,kiv,n+1,x,y,exp)))
}

pub fn decrypt_data_or_hs(ciphertext:&Bytes, st: DuplexCipherState1) -> Res<(U8,Bytes,DuplexCipherState1)> {
    let DuplexCipherState1(ae, x, y, kiv, n, exp) = st;
    let (ct,payload) = decrypt_record_payload(&ae,&kiv,n,ciphertext)?;
    Ok((ct,payload,DuplexCipherState1(ae, x, y, kiv, n+1, exp)))
}
pub fn decrypt_data(ciphertext:&Bytes, st: DuplexCipherState1) -> Res<(Bytes,DuplexCipherState1)> {
    let DuplexCipherState1(ae, x, y, kiv, n, exp) = st;
    let (ct,payload) = decrypt_record_payload(&ae,&kiv,n,ciphertext)?;
    check_eq1(ct,U8(ct_app_data))?;
    Ok((payload,DuplexCipherState1(ae, x, y, kiv, n+1, exp)))
}

pub fn handshake_record(p:&Bytes) -> Res<Bytes> {
    let ty = bytes1(0x16);
    let ver = bytes2(3,3);
    Ok(ty.concat(&ver).concat(&lbytes2(p)?))
}

pub fn check_handshake_record(p:&Bytes) -> Res<(Bytes,usize)> {
    if p.len() < 5 {Err(parse_failed)}
    else {
        let ty = bytes1(0x16);
        let ver = bytes2(3,3);
        check_eq(&ty,&p.slice_range(0..1))?;
        check_eq(&ver,&p.slice_range(1..3))?;
        let len = check_lbytes2(&p.slice_range(3..p.len()))?;
        Ok((p.slice_range(5..5+len),5+len))
    }
}

pub fn check_handshake_message(p:&Bytes) -> Res<(Bytes,usize)> {
    if p.len() < 3 {Err(parse_failed)}
    else {
        let len = check_lbytes3(&p.slice_range(1..p.len()))?;
        Ok((p.slice_range(0..4+len),4+len))
    }
}

pub fn has_finished_message(payload:&Bytes) -> bool {
    match check_handshake_message(payload) {
        Err(_) => false,
        Ok((_,len)) => {
            if eq1(payload[0],U8(ty_finished)) {true}
            else {has_finished_message(&payload.slice_range(len..payload.len()))}
        }
    }
}