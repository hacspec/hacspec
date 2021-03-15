use crate::tls13crypto::*;
use crate::tls13formats::*;
use crate::tls13record::*;

// Import hacspec and all needed definitions.
use hacspec_lib::*;

/* TLS 1.3 Key Schedule: See RFC 8446 Section 7 */

pub fn hkdf_expand_label(
    ha: &HashAlgorithm,
    k: &KEY,
    label: &Bytes,
    context: &Bytes,
    len: usize,
) -> Res<KEY> {
    if len >= 65536 {Err(payload_too_long)}
    else {
        let lenb = bytes(&U16_to_be_bytes(U16(len as u16)));
        let tls13_label = label_tls13.concat(label);
        let info = lenb
            .concat(&lbytes1(&tls13_label)?)
            .concat(&lbytes1(context)?);
        return hkdf_expand(ha, k, &info, len as usize);
    }
}

pub fn derive_secret(ha: &HashAlgorithm, k: &KEY, label: &Bytes, tx: &HASH) -> Res<KEY> {
    return hkdf_expand_label(ha, k, label, &bytes(tx), hash_len(ha));
}

pub fn derive_binder_key(ha: &HashAlgorithm, k: &KEY) -> Res<MACK> {
    let early_secret = hkdf_extract(ha, k, &zero_key(ha))?;
    let mk = derive_secret(ha, &early_secret, &bytes(&label_res_binder), &hash_empty(ha)?)?;
    return Ok(MACK::from_seq(&mk));
}

pub fn derive_aead_key_iv(ha: &HashAlgorithm, ae: &AEADAlgorithm, k: &KEY) -> Res<AEKIV> {
    let sender_write_key = hkdf_expand_label(ha, k, &bytes(&label_key), &empty(), ae_key_len(ae))?;
    let sender_write_iv = hkdf_expand_label(ha, k, &bytes(&label_iv), &empty(), ae_iv_len(ae))?;
    return Ok((
        AEK::from_seq(&sender_write_key),
        AEIV::from_seq(&sender_write_iv),
    ));
}

pub fn derive_0rtt_keys(ha: &HashAlgorithm, ae: &AEADAlgorithm, k: &KEY, tx: &HASH) -> Res<(AEKIV, KEY)> {
    let early_secret = hkdf_extract(ha, k, &zero_key(ha))?;
    let client_early_traffic_secret =
        derive_secret(ha, &early_secret, &bytes(&label_c_e_traffic), tx)?;
    let early_exporter_master_secret =
        derive_secret(ha, &early_secret, &bytes(&label_c_e_traffic), tx)?;
    let sender_write_key_iv = derive_aead_key_iv(ha, ae, &client_early_traffic_secret)?;
    return Ok((sender_write_key_iv, early_exporter_master_secret));
}

pub fn derive_finished_key(ha: &HashAlgorithm, k: &KEY) -> Res<MACK> {
    Ok(hkdf_expand_label(ha,k,&bytes(&label_finished),&empty(),hmac_key_len(ha))?)
}

pub fn derive_hk_ms(
    ha: &HashAlgorithm,
    ae: &AEADAlgorithm,
    gxy: &KEY,
    psko: &Option<PSK>,
    tx: &HASH,
) -> Res<(AEKIV, AEKIV, MACK, MACK, KEY)> {
    let psk = if let Some(k) = psko {KEY::from_seq(k)} else {zero_key(ha)};
    let early_secret = hkdf_extract(ha, &psk, &zero_key(ha))?;
    let handshake_secret = hkdf_extract(ha, gxy, &early_secret)?;
    let client_handshake_traffic_secret =
        derive_secret(ha, &handshake_secret, &bytes(&label_c_hs_traffic), tx)?;
    let server_handshake_traffic_secret =
        derive_secret(ha, &handshake_secret, &bytes(&label_s_hs_traffic), tx)?;
    let client_finished_key = derive_finished_key(ha, &client_handshake_traffic_secret)?;
    let server_finished_key = derive_finished_key(ha, &server_handshake_traffic_secret)?;
    let client_write_key_iv = derive_aead_key_iv(ha, ae, &client_handshake_traffic_secret)?;
    let server_write_key_iv = derive_aead_key_iv(ha, ae, &server_handshake_traffic_secret)?;
    let master_secret_ =
        derive_secret(ha, &handshake_secret, &bytes(&label_derived), &hash_empty(ha)?)?;
    let master_secret = hkdf_extract(ha, &zero_key(ha), &master_secret_)?;
    return Ok((
        client_write_key_iv,
        server_write_key_iv,
        client_finished_key,
        server_finished_key,
        master_secret,
    ));
}

pub fn derive_app_keys(
    ha: &HashAlgorithm,
    ae: &AEADAlgorithm,
    master_secret: &KEY,
    tx: &HASH,
) -> Res<(AEKIV, AEKIV, KEY)> {
    let client_application_traffic_secret_0 =
        derive_secret(ha, &master_secret, &bytes(&label_c_ap_traffic), tx)?;
    let server_application_traffic_secret_0 =
        derive_secret(ha, &master_secret, &bytes(&label_s_ap_traffic), tx)?;
    let client_write_key_iv = derive_aead_key_iv(ha, ae, &client_application_traffic_secret_0)?;
    let server_write_key_iv = derive_aead_key_iv(ha, ae, &server_application_traffic_secret_0)?;
    let exporter_master_secret = derive_secret(ha, master_secret, &bytes(&label_exp_master), tx)?;
    return Ok((
        client_write_key_iv,
        server_write_key_iv,
        exporter_master_secret,
    ));
}

pub fn derive_rms(ha: &HashAlgorithm, master_secret: &KEY, tx: &HASH) -> Res<KEY> {
    let resumption_master_secret = derive_secret(ha, master_secret, &bytes(&label_res_master), tx)?;
    return Ok(resumption_master_secret);
}

/*
/* TLS 1.3 Record Layer Encryption: See RFC 8446 Section 5 */

// Using newtype pattern below, but the same thing works with tuples too
pub struct CipherState(AEADAlgorithm, AEKIV, u64);

pub fn derive_iv_ctr(ae: &AEADAlgorithm, iv: &AEIV, n:u64) -> AEIV {
    let counter = bytes(&U64_to_be_bytes(U64(n)));
    let mut iv_ctr = AEIV::new(iv.len());
    for i in 0..iv.len()-8 {
        iv_ctr[i] = iv[i];
    }
    for i in 0..8 {
        iv_ctr[i+iv.len()-8] = iv[i+iv.len()-8] ^ counter[i];
    }
    return iv_ctr;
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
        let cip = aead_encrypt(&ae, &k, &iv_ctr, payload, &ad)?;
        let rec = ad.concat(&cip);
        Ok((cip,CipherState(ae,(k,iv),n+1)))
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
        let clenb = u16_to_be_bytes(ciphertext.len() as u16);
        let ad = bytes5(23, 3, 3, clenb[0], clenb[1]);
        check_eq(&ad,&ciphertext.slice_range(0..5))?;
        let cip = ciphertext.slice_range(5..5+ciphertext.len());
        let plain = aead_decrypt(&ae, &k, &iv_ctr, &cip, &ad)?;
        let payload_len = plain.len() - padlen(&plain,plain.len()) - 1;
        let ct = plain[payload_len].declassify();
        let payload = plain.slice_range(0..payload_len);
        Ok((ct,payload,CipherState(ae, (k, iv), n+1)))
    } else {
        Err(payload_too_long)
    }
}
*/
/* Incremental Transcript Construction 
   For simplicity, we store the full transcript, but an internal hash state would suffice. */

pub struct TranscriptTruncatedClientHello(pub HashAlgorithm, pub HASH);
pub struct TranscriptClientHello(pub HashAlgorithm, pub bool, pub Bytes, pub HASH);
pub struct TranscriptServerHello(pub HashAlgorithm, pub bool, pub Bytes, pub HASH);
pub struct TranscriptServerCertificate(pub HashAlgorithm, pub bool, pub Bytes, pub HASH);
pub struct TranscriptServerCertificateVerify(pub HashAlgorithm, pub bool, pub Bytes, pub HASH);
pub struct TranscriptServerFinished(pub HashAlgorithm, pub bool, pub Bytes, pub HASH);
pub struct TranscriptClientFinished(pub HashAlgorithm, pub bool, pub Bytes, pub HASH);

pub fn transcript_truncated_client_hello(algs:ALGS,ch:&Bytes,trunc_len:usize) ->
    Res<TranscriptTruncatedClientHello> {
        let ALGS(ha, ae, sa, gn, psk_mode, zero_rtt) = algs;
        let th = hash(&ha,&ch.slice_range(0..trunc_len))?;
        Ok(TranscriptTruncatedClientHello(ha,th))
    }

pub fn transcript_client_hello(algs:ALGS,ch:&Bytes) -> Res<TranscriptClientHello> {
        let ALGS(ha, ae, sa, gn, psk_mode, zero_rtt) = algs;
        let transcript = empty().concat(ch);
        let th = hash(&ha,&transcript)?;
        Ok(TranscriptClientHello(ha,psk_mode,transcript,th))
    }

pub fn transcript_server_hello(tx:TranscriptClientHello,sh:&Bytes) -> Res<TranscriptServerHello> {
        let TranscriptClientHello(ha,psk_mode,transcript,_) = tx;
        let transcript = transcript.concat(sh);
        let th = hash(&ha,&transcript)?;
        Ok(TranscriptServerHello(ha,psk_mode,transcript,th))
    }

pub fn transcript_server_certificate(tx:TranscriptServerHello,ee:&Bytes,sc:&Bytes) -> Res<TranscriptServerCertificate> {
        let TranscriptServerHello(ha,psk_mode,transcript,_) = tx;
        if psk_mode {Err(psk_mode_mismatch)}
        else {
            let transcript = transcript.concat(ee);
            let transcript = transcript.concat(sc);
            let th = hash(&ha,&transcript)?;
            Ok(TranscriptServerCertificate(ha,psk_mode,transcript,th))
        }
    }

pub fn transcript_server_certificate_verify(tx:TranscriptServerCertificate,cv:&Bytes) -> Res<TranscriptServerCertificateVerify> {
        let TranscriptServerCertificate(ha,psk_mode,transcript,_) = tx;
        if psk_mode {Err(psk_mode_mismatch)}
        else {
            let transcript = transcript.concat(cv);
            let th = hash(&ha,&transcript)?;
            Ok(TranscriptServerCertificateVerify(ha,psk_mode,transcript,th))
        }
    }

pub fn transcript_skip_server_certificate_verify(tx:TranscriptServerHello,ee:&Bytes) -> Res<TranscriptServerCertificateVerify> {
        let TranscriptServerHello(ha,psk_mode,transcript,_) = tx;
        if !psk_mode {Err(psk_mode_mismatch)}
        else {
            let transcript = transcript.concat(ee);
            let th = hash(&ha,&transcript)?;
            Ok(TranscriptServerCertificateVerify(ha,psk_mode,transcript,th))
        }
    }

pub fn transcript_server_finished(tx:TranscriptServerCertificateVerify,sf:&Bytes) -> Res<TranscriptServerFinished> {
        let TranscriptServerCertificateVerify(ha,psk_mode,transcript,_) = tx;
        let transcript = transcript.concat(sf);
        let th = hash(&ha,&transcript)?;
        Ok(TranscriptServerFinished(ha,psk_mode,transcript,th))
    }

pub fn transcript_client_finished(tx:TranscriptServerFinished,cf:&Bytes) -> Res<TranscriptClientFinished> {
        let TranscriptServerFinished(ha,psk_mode,transcript,_) = tx;
        let transcript = transcript.concat(cf);
        let th = hash(&ha,&transcript)?;
        Ok(TranscriptClientFinished(ha,psk_mode,transcript,th))
    }

/* Handshake State Machine */
/* We implement a simple linear state machine:
PostClientHello -> PostServerHello -> PostCertificateVerify ->
PostServerFinished -> PostClientFinished -> Complete
There are no optional steps, all states must be traversed, even if the traversals are NOOPS.
See "put_skip_server_signature" below */

pub struct ClientPostClientHello(Random, ALGS, DHSK, Option<PSK>);
pub struct ClientPostServerHello(Random, Random, ALGS, KEY, MACK, MACK);
pub struct ClientPostCertificateVerify(Random, Random, ALGS, KEY, MACK, MACK);
pub struct ClientPostServerFinished(Random, Random, ALGS, KEY, MACK);
pub struct ClientPostClientFinished(Random, Random, ALGS, KEY);
pub struct ClientComplete(Random, Random, ALGS, KEY);

pub struct ServerPostClientHello(Random, Random, ALGS, KEY, Option<PSK>);
pub struct ServerPostServerHello(Random, Random, ALGS, KEY, MACK, MACK);
pub struct ServerPostCertificateVerify(Random, Random, ALGS, KEY, MACK, MACK);
pub struct ServerPostServerFinished(Random, Random, ALGS, KEY, MACK);
pub struct ServerPostClientFinished(Random, Random, ALGS, KEY);
pub struct ServerComplete(Random, Random, ALGS, KEY);

/* Handshake Core Functions: See RFC 8446 Section 4 */
/* We delegate all details of message formatting and transcript hashes to the caller */

/* TLS 1.3 Client Side Handshake Functions */

pub fn get_client_hello(
    algs0:ALGS,
    psk: Option<PSK>,
    ent: Entropy,
) -> Res<(Random, DHPK, ClientPostClientHello)> {
    let ALGS(ha, ae, sa, gn, psk_mode, zero_rtt) = &algs0;
    if ent.len() < 32 + dh_priv_len(gn) {Err(insufficient_entropy)}
    else {
        let cr = Random::from_seq(&ent.slice_range(0..32));
        let x = DHSK::from_seq(&ent.slice_range(32..32+dh_priv_len(gn)));
        let gx = secret_to_public(gn, &x)?;
        Ok((cr, gx, ClientPostClientHello(cr, algs0, x, psk)))
    }
}

pub fn get_client_hello_binder(
    tx: &TranscriptTruncatedClientHello,
    st: &ClientPostClientHello,
) -> Res<Option<HMAC>> {
    let ClientPostClientHello(cr, algs0, x, psk) = st;
    let ALGS(ha, ae, sa, gn, psk_mode, zero_rtt) = algs0;
    let TranscriptTruncatedClientHello(_,tx_hash) = tx;
    match (psk_mode, psk) {
        (true,Some(k)) => {
            let mk = derive_binder_key(ha, &k)?;
            let mac = hmac(ha, &mk, &bytes(tx_hash))?;
            Ok(Some(mac))},
        (false,None) => Ok(None),
        _ => Err(psk_mode_mismatch)
     }
}

pub fn client_get_0rtt_keys(
    tx: &TranscriptClientHello,
    st: &ClientPostClientHello,
) -> Res<Option<(CipherState, KEY)>> {
    let ClientPostClientHello(cr, algs0, x, psk) = st;
    let TranscriptClientHello(_,_,_,tx_hash) = tx;
    let ALGS(ha, ae, sa, gn, psk_mode, zero_rtt) = algs0;
    match (psk_mode, zero_rtt, psk) {
        (true,true,Some(k)) => {
            let (aek, key) = derive_0rtt_keys(ha, ae, &k, tx_hash)?;
            Ok(Some((CipherState(*ae, aek, 0), key)))},
        (false,false,None) => Ok(None),
        (true,false,Some(k)) => Ok(None),
        _ => Err(psk_mode_mismatch)
    }
}

pub fn put_server_hello(
    sr: Random,
    gy: DHPK,
    algs: ALGS,
    tx: &TranscriptServerHello,
    st: ClientPostClientHello,
) -> Res<(CipherState, CipherState, ClientPostServerHello)> {
    let ClientPostClientHello(cr, algs0, x, psk) = st;
    let TranscriptServerHello(_,_,_,tx_hash) = tx;
    if algs == algs0 {
        let ALGS(ha, ae, sa, gn, psk_mode, zero_rtt) = &algs;
        let gxy = ecdh(gn, &x, &gy)?;
        let (chk, shk, cfk, sfk, ms) = derive_hk_ms(ha, ae, &gxy, &psk, tx_hash)?;
        Ok((
            CipherState(*ae, chk, 0),
            CipherState(*ae, shk, 0),
            ClientPostServerHello(cr, sr, algs, ms, cfk, sfk),
        ))
    } else {
        Err(negotiation_mismatch)
    }
}

pub fn put_server_signature(
    pk: &VERK,
    sig: &Bytes,
    tx: &TranscriptServerCertificate,
    st: ClientPostServerHello,
) -> Res<ClientPostCertificateVerify> {
    let ClientPostServerHello(cr, sr, algs, ms, cfk, sfk) = st;
    let TranscriptServerCertificate(_,_,_,tx_hash) = tx;
    if let ALGS(ha, ae, sa, gn, false, zero_rtt) = &algs {
        verify(sa, &pk, &bytes(tx_hash), &sig)?;
        Ok(ClientPostCertificateVerify(cr, sr, algs, ms, cfk, sfk))
    } else {
        Err(psk_mode_mismatch)
    }
}

pub fn put_skip_server_signature(st: ClientPostServerHello) -> Res<ClientPostCertificateVerify> {
    let ClientPostServerHello(cr, sr, algs, ms, cfk, sfk) = st;
    if let ALGS(ha, ae, sa, gn, true, zero_rtt) = &algs {
        Ok(ClientPostCertificateVerify(cr, sr, algs, ms, cfk, sfk))
    } else {
        Err(psk_mode_mismatch)
    }
}

pub fn put_server_finished(
    vd: &HMAC,
    tx: &TranscriptServerCertificateVerify,
    st: ClientPostCertificateVerify,
) -> Res<ClientPostServerFinished> {
    let ClientPostCertificateVerify(cr, sr, algs, ms, cfk, sfk) = st;
    let TranscriptServerCertificateVerify(_,_,_,tx_hash) = tx;
    let ALGS(ha, ae, sa, gn, psk_mode, zero_rtt) = &algs;
    hmac_verify(ha, &sfk, &bytes(tx_hash), &vd)?;
    return Ok(ClientPostServerFinished(cr, sr, algs, ms, cfk));
}
pub fn client_get_1rtt_keys(
    tx: &TranscriptServerFinished,
    st: &ClientPostServerFinished,
) -> Res<(CipherState, CipherState, KEY)> {
    let ClientPostServerFinished(_, _, algs, ms, cfk) = st;
    let TranscriptServerFinished(_,_,_,tx_hash) = tx;
    let ALGS(ha, ae, sa, gn, psk_mode, zero_rtt) = algs;
    let (cak, sak, exp) = derive_app_keys(ha, ae, &ms, tx_hash)?;
    return Ok((CipherState(*ae, cak, 0), 
               CipherState(*ae, sak, 0), exp));
}

pub fn get_client_finished(
    tx: &TranscriptServerFinished,
    st: ClientPostServerFinished,
) -> Res<(HMAC, ClientPostClientFinished)> {
    let ClientPostServerFinished(cr, sr, algs, ms, cfk) = st;
    let TranscriptServerFinished(_,_,_,tx_hash) = tx;
    let ALGS(ha, ae, sa, gn, psk_mode, zero_rtt) = &algs;
    let m = hmac(ha, &cfk, &bytes(tx_hash))?;
    return Ok((m, ClientPostClientFinished(cr, sr, algs, ms)));
}

pub fn client_complete(
    tx: &TranscriptClientFinished,
    st: ClientPostClientFinished,
) -> Res<ClientComplete> {
    let ClientPostClientFinished(cr, sr, algs, ms) = st;
    let TranscriptClientFinished(_,_,_,tx_hash) = tx;
    let ALGS(ha, ae, sa, gn, psk_mode, zero_rtt) = &algs;
    let rms = derive_rms(ha, &ms, tx_hash)?;
    Ok(ClientComplete(cr,sr,algs,rms))
}

/* TLS 1.3 Server Side Handshake Functions */

pub fn put_client_hello(
    cr: Random,
    algs: ALGS,
    gx: &DHPK,
    psk: Option<PSK>,
    tx: TranscriptTruncatedClientHello,
    binder: Option<HMAC>,
    ent: Entropy,
) -> Res<(Random, DHPK, ServerPostClientHello)> {
    let ALGS(ha, ae, sa, gn, psk_mode, zero_rtt) = &algs;
    if ent.len() < 32 + dh_priv_len(gn) {Err(insufficient_entropy)}
    else {
        let sr = Random::from_seq(&ent.slice_range(0..32));
        let y = DHSK::from_seq(&ent.slice_range(32..32+dh_priv_len(gn)));
        let gy = secret_to_public(gn, &y)?;
        let gxy = ecdh(gn, &y, &gx)?;
        match (psk_mode, psk, binder) {
            (true, Some(k), Some(binder)) => {
                let mk = derive_binder_key(ha, &k)?;
                let TranscriptTruncatedClientHello(_,tx_hash) = tx;
                hmac_verify(ha, &mk, &bytes(&tx_hash), &binder)?;
                Ok((sr, gy, ServerPostClientHello(cr, sr, algs, gxy, Some(k))))
            }
            (false, None, None) => Ok((sr, gy, ServerPostClientHello(cr, sr, algs, gxy, None))),
            _ => Err(psk_mode_mismatch),
        }
    }
}

pub fn server_get_0rtt_keys(
    tx: &TranscriptClientHello,
    st: &ServerPostClientHello,
) -> Res<Option<(CipherState, KEY)>> {
    let ServerPostClientHello(cr, sr, algs, gxy, psk) = st;
    let TranscriptClientHello(_,_,_,tx_hash) = tx;
    let ALGS(ha, ae, sa, gn, psk_mode, zero_rtt) = algs;
    match (psk_mode, zero_rtt, psk) {
        (true,true,Some(k)) => {
            let (aek, key) = derive_0rtt_keys(ha, ae, &k, tx_hash)?;
            Ok(Some((CipherState(*ae, aek, 0), key)))},
        (false,false,None) => Ok(None),
        (true,false,Some(k)) => Ok(None),
        _ => Err(psk_mode_mismatch)    
        }
}

pub fn get_server_hello(
    tx: &TranscriptServerHello,
    st: ServerPostClientHello,
) -> Res<(CipherState, CipherState, ServerPostServerHello)> {
    let ServerPostClientHello(cr, sr, algs, gxy, psk) = st;
    let TranscriptServerHello(_,_,_,tx_hash) = tx;
    let ALGS(ha, ae, sa, gn, psk_mode, zero_rtt) = &algs;
    let (chk, shk, cfk, sfk, ms) = derive_hk_ms(ha, ae, &gxy, &psk, tx_hash)?;
    Ok((
        CipherState(*ae, chk, 0),
        CipherState(*ae, shk, 0),
        ServerPostServerHello(cr, sr, algs, ms, cfk, sfk),
    ))
}

pub fn get_server_signature(
    sk: &SIGK,
    tx: &TranscriptServerCertificate,
    st: ServerPostServerHello,
) -> Res<(SIG, ServerPostCertificateVerify)> {
    let ServerPostServerHello(cr, sr, algs, ms, cfk, sfk) = st;
    let TranscriptServerCertificate(_,_,_,tx_hash) = tx;
    if let ALGS(ha, ae, sa, gn, false, zero_rtt) = &algs {
        let sig = sign(sa, &sk, &bytes(tx_hash))?;
        Ok((sig, ServerPostCertificateVerify(cr, sr, algs, ms, cfk, sfk)))
    } else {
        Err(psk_mode_mismatch)
    }
}

pub fn get_skip_server_signature(st: ServerPostServerHello) -> Res<ServerPostCertificateVerify> {
    let ServerPostServerHello(cr, sr, algs, ms, cfk, sfk) = st;
    if let ALGS(ha, ae, sa, gn, true, zero_rtt) = algs {
        Ok(ServerPostCertificateVerify(cr, sr, algs, ms, cfk, sfk))
    } else {
        Err(psk_mode_mismatch)
    }
}

pub fn get_server_finished(
    tx: &TranscriptServerCertificateVerify,
    st: ServerPostCertificateVerify,
) -> Res<(HMAC, ServerPostServerFinished)> {
    let ServerPostCertificateVerify(cr, sr, algs, ms, cfk, sfk) = st;
    let TranscriptServerCertificateVerify(_,_,_,tx_hash) = tx;
    let ALGS(ha, ae, sa, gn, psk_mode, zero_rtt) = &algs;
    let m = hmac(ha, &sfk, &bytes(tx_hash))?;
    Ok((m, ServerPostServerFinished(cr, sr, algs, ms, cfk)))
}

pub fn server_get_1rtt_keys(
    tx: &TranscriptServerFinished,
    st: &ServerPostServerFinished,
) -> Res<(CipherState, CipherState, KEY)> {
    let ServerPostServerFinished(_, _, algs, ms, cfk) = st;
    let TranscriptServerFinished(_,_,_,tx_hash) = tx;
    let ALGS(ha, ae, sa, gn, psk_mode, zero_rtt) = algs;
    let (cak, sak, exp) = derive_app_keys(ha, ae, &ms, tx_hash)?;
    return Ok((CipherState(*ae, cak, 0),
               CipherState(*ae, sak, 0), exp));
}

pub fn put_client_finished(
    mac: HMAC,
    tx: &TranscriptServerFinished,
    st: ServerPostServerFinished,
) -> Res<ServerPostClientFinished> {
    let ServerPostServerFinished(cr, sr, algs, ms, cfk) = st;
    let TranscriptServerFinished(_,_,_,tx_hash) = tx;
    let ALGS(ha, ae, sa, gn, psk_mode, zero_rtt) = &algs;
    hmac_verify(ha, &cfk, &bytes(tx_hash), &mac)?;
    return Ok(ServerPostClientFinished(cr, sr, algs, ms));
}

pub fn server_complete(
    tx: &TranscriptClientFinished,
    st: ServerPostClientFinished,
) -> Res<ClientComplete> {
    let TranscriptClientFinished(_,_,_,tx_hash) = tx;
    let ServerPostClientFinished(cr, sr, algs, ms) = st;
    let ALGS(ha, ae, sa, gn, psk_mode, zero_rtt) = &algs;
    let rms = derive_rms(ha, &ms, tx_hash)?;
    Ok(ClientComplete(cr,sr,algs,rms))
}
