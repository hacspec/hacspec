// Import hacspec and all needed definitions.
use hacspec_lib::*;
use crate::cryptolib::*;
use crate::tls13formats::*;
use crate::tls13handshake::*;
use crate::tls13record::*;

// Client-Side Handshake API for TLS 1.3 Applications
// client_init -> (encrypt_zerortt)* -> client_set_params ->
// (decrypt_handshake)* -> client_finish -> (encrypt_handhsake) ->
// (encrypt_data | decrypt_data)*

pub struct Client0(ALGS,TranscriptClientHello,ClientPostClientHello);
pub struct ClientH(ALGS,TranscriptServerHello,ClientPostServerHello);
pub struct Client1(ALGS,TranscriptClientFinished,ClientPostClientFinished);
    
pub fn client_init(algs:ALGS,sn:&Bytes,tkt:Option<Bytes>,psk:Option<KEY>,ent:Entropy) -> Res<(HandshakeData,Client0,Option<ClientCipherState0>)> {
    let ALGS(ha, ae, sa, gn, psk_mode, zero_rtt) = &algs;
    let (crand,gx,cstate) = get_client_hello(algs,psk,ent)?;
    let (ch,trunc_len) = client_hello(&algs,&crand,&gx,sn,&tkt)?;
    let tx_trunc = transcript_truncated_client_hello(algs,&ch,trunc_len)?;
    let binder = get_client_hello_binder(&tx_trunc,&cstate)?;
    let nch = set_client_hello_binder(&algs,&binder,ch)?;
    let tx_ch = transcript_client_hello(algs,&nch)?;
    let c2s0 = client_get_0rtt_keys(&tx_ch,&cstate)?;
    let st = Client0(algs,tx_ch,cstate);
    Ok((nch,st,c2s0))  
}

pub fn client_set_params(sh:&HandshakeData,st:Client0) -> Res<(ClientH,DuplexCipherStateH)> {
    let Client0(algs,tx_ch,cstate) = st;
    let ALGS(ha, ae, sa, gn, psk_mode, zero_rtt) = &algs;
    let (sr,gy) = parse_server_hello(&algs,&sh)?;    
    let tx_sh = transcript_server_hello(tx_ch,&sh)?;
    let (cipher,cstate) = put_server_hello(sr, gy, algs, &tx_sh, cstate)?;
    Ok((ClientH(algs,tx_sh,cstate),cipher))
}

pub fn client_finish(payload:&HandshakeData,st:ClientH) -> Res<(HandshakeData,Client1,DuplexCipherState1)> {
    let ClientH(algs,tx_sh,cstate) = st;
    let ALGS(ha, ae, sa, gn, psk_mode, zero_rtt) = &algs;
    let mut next = 0;
    let (ee,len_ee) = check_handshake_message(&payload,0)?;
    parse_encrypted_extensions(&algs,&ee)?;
    next = next + len_ee;
    let tx_cv:TranscriptServerCertificateVerify;
    let cstate_cv:ClientPostCertificateVerify;
    match psk_mode {
        false => {  
            let (sc,len_sc) = check_handshake_message(&payload,next)?;
            let cert = parse_server_certificate(&algs,&sc)?;
            next = next + len_sc;
            let (cv,len_cv) = check_handshake_message(&payload,next)?;
            let sig = parse_certificate_verify(&algs,&cv)?;
            next = next + len_cv; 
            let pk = verk_from_cert(&cert)?;
            let tx_sc = transcript_server_certificate(tx_sh,&ee,&sc)?;
            cstate_cv = put_server_signature(&pk, &sig, &tx_sc, cstate)?;
            tx_cv = transcript_server_certificate_verify(tx_sc,&cv)?;}
        true => {
            cstate_cv = put_skip_server_signature(cstate)?;
            tx_cv = transcript_skip_server_certificate_verify(tx_sh,&ee)?;}
    };    
    let (sfin,len_fin) = check_handshake_message(&payload,next)?;
    let vd = parse_finished(&algs,&sfin)?;
    next = next + len_fin;
    if !has_handshake_message(payload,next) {
        let cstate = put_server_finished(&vd,&tx_cv,cstate_cv)?;
        let tx_sf = transcript_server_finished(tx_cv,&sfin)?;
        let cipher = client_get_1rtt_keys(&tx_sf,&cstate)?;
        let (vd,cstate) = get_client_finished(&tx_sf,cstate)?;
        let cfin = finished(&algs,&vd)?;
        let tx_cf = transcript_client_finished(tx_sf,&cfin)?;
        Ok((cfin,Client1(algs,tx_cf,cstate),cipher))
    } else {err(parse_failed)}
}

// Server-Side Handshake API for TLS 1.3 Applications
// server_init -> (encrypt_handshake)* -> (decrypt_zerortt)* ->
// (decrypt_handshake) -> server_finish ->
// (encrypt data | decrypt data)*

pub struct Server0(ALGS,TranscriptServerFinished,ServerPostServerFinished);
pub struct Server1(ALGS,TranscriptClientFinished,ServerPostClientFinished);

pub struct ServerDB(pub Bytes,pub Bytes,pub SIGK,pub Option<(Bytes,PSK)>);

fn lookup_db(algs:ALGS, db:&ServerDB,sni:&Bytes,tkt:&Option<Bytes>) ->
             Res<(Bytes,SIGK,Option<PSK>)> {
    let ALGS(ha, ae, sa, gn, psk_mode, zero_rtt) = &algs;
    let ServerDB(server_name,cert,sk,psk_opt) = db;
    check_eq(sni,server_name)?;
    match (psk_mode,tkt, psk_opt) {
        (true, Some(ctkt), Some((stkt,psk))) => {
            check_eq(&ctkt,&stkt)?;
            Ok((cert.clone(),sk.clone(),Some(psk.clone())))},
        (false, _, _) => Ok((cert.clone(),sk.clone(),None)),
        _ => Err(psk_mode_mismatch)
    }
}

pub fn server_init(algs:ALGS,db:ServerDB,ch:&HandshakeData,ent:Entropy) -> Res<(HandshakeData,HandshakeData,Server0,DuplexCipherStateH,DuplexCipherState1)> {
    let ALGS(ha, ae, sa, gn, psk_mode, zero_rtt) = &algs;
    let (cr,sid,sni,gx,tkto, bindero, trunc_len) = parse_client_hello(&algs,&ch)?;
    let tx_trunc = transcript_truncated_client_hello(algs,&ch,trunc_len)?;
    let (cert,sigk,psk_opt) = lookup_db(algs,&db,&sni,&tkto)?;
    let (sr,gy,sstate) = put_client_hello(cr,algs,&gx,psk_opt,tx_trunc,bindero,ent.clone())?; // FIXME: don't clone entropy
    let tx_ch = transcript_client_hello(algs,&ch)?;
    let c2s0 = server_get_0rtt_keys(&tx_ch,&sstate)?;
    let sh = server_hello(&algs,&sr,&sid,&gy)?;
    let tx_sh = transcript_server_hello(tx_ch,&sh)?;
    let (cipherH,sstate) = get_server_hello(&tx_sh,sstate)?;
    let ee = encrypted_extensions(&algs)?;
    let mut payload = HandshakeData(empty());
    payload = handshake_concat(payload,&ee);
    let mut tx_cv : Option<TranscriptServerCertificateVerify> = None;
    let mut sstate_cv : Option<ServerPostCertificateVerify> = None;
    match psk_mode {
        false => {
            let sc = server_certificate(&algs,&cert)?;
            payload = handshake_concat(payload,&sc);
            let tx_sc = transcript_server_certificate(tx_sh,&ee,&sc)?;
            let (sig,sstate) = get_server_signature(&sigk,&tx_sc,sstate, ent)?;
            let cv = certificate_verify(&algs,&sig)?;
            payload = handshake_concat(payload,&cv);
            tx_cv = Some(transcript_server_certificate_verify(tx_sc,&cv)?);
            sstate_cv = Some(sstate);},
        true => {
            let tx_cv = Some(transcript_skip_server_certificate_verify(tx_sh,&ee)?);
            let sstate_cv = Some(get_skip_server_signature(sstate)?);}
    };
    let tx_cv = tx_cv.unwrap();
    let sstate_cv = sstate_cv.unwrap();
    let (vd,sstate) = get_server_finished(&tx_cv,sstate_cv)?;
    let sfin = finished(&algs,&vd)?;
    payload = handshake_concat(payload,&sfin);
    let tx_sf = transcript_server_finished(tx_cv,&sfin)?;
    let cipher1 = server_get_1rtt_keys(&tx_sf, &sstate)?;
    let st = Server0(algs,tx_sf,sstate);
    Ok((sh,payload,st,cipherH,cipher1))
}
    
pub fn server_finish(payload:&HandshakeData,st:Server0) -> Res<Server1> {
    let Server0(algs,tx_sf,sstate) = st;
    let (cfin,flen) = check_handshake_message(payload,0)?;
    let vd = parse_finished(&algs,&cfin)?;
    let sstate = put_client_finished(vd,&tx_sf,sstate)?;
    let tx_cf = transcript_client_finished(tx_sf,&cfin)?;
    if !has_handshake_message(payload,flen) {
        Ok(Server1(algs,tx_cf,sstate))
    } else {err(parse_failed)}
}

/* Record Encryption/Decryption API */

pub struct AppData(pub Bytes);

pub fn encrypt_zerortt(payload:&AppData, pad:usize, st: ClientCipherState0) -> Res<(Bytes,ClientCipherState0)> {
    let ClientCipherState0(ae, kiv, n, exp) = st;
    let AppData(payload) = payload;
    let rec = encrypt_record_payload(&ae,&kiv,n,ContentType::ApplicationData,payload,pad)?;
    Ok((rec,ClientCipherState0(ae,kiv,n+1, exp)))
}

pub fn decrypt_zerortt(ciphertext:&Bytes, st: ServerCipherState0) -> Res<(AppData,ServerCipherState0)> {
    let ServerCipherState0(ae, kiv, n, exp) = st;
    let (ct,payload) = decrypt_record_payload(&ae,&kiv,n,ciphertext)?;
    check(ct == ContentType::ApplicationData)?;
    Ok((AppData(payload),ServerCipherState0(ae,kiv,n+1,exp)))
}

pub fn encrypt_handshake(payload:&HandshakeData, pad:usize, st: DuplexCipherStateH) -> Res<(Bytes,DuplexCipherStateH)> {
    let DuplexCipherStateH(ae, kiv, n, x, y) = st;
    let HandshakeData(payload) = payload;
    let rec = encrypt_record_payload(&ae,&kiv,n,ContentType::Handshake,payload,pad)?;
    Ok((rec,DuplexCipherStateH(ae,kiv,n+1, x, y)))
}

pub fn decrypt_handshake(ciphertext:&Bytes, st: DuplexCipherStateH) -> Res<(HandshakeData,DuplexCipherStateH)> {
    let DuplexCipherStateH(ae, x, y, kiv, n) = st;
    let (ct,payload) = decrypt_record_payload(&ae,&kiv,n,ciphertext)?;
    check(ct == ContentType::Handshake)?;
    Ok((HandshakeData(payload),DuplexCipherStateH(ae, x, y, kiv, n+1)))
}

pub fn encrypt_data(payload:&AppData, pad:usize, st: DuplexCipherState1) -> Res<(Bytes,DuplexCipherState1)> {
    let DuplexCipherState1(ae, kiv, n, x, y, exp) = st;
    let AppData(payload) = payload;
    let rec = encrypt_record_payload(&ae,&kiv,n,ContentType::ApplicationData,payload,pad)?;
    Ok((rec,DuplexCipherState1(ae,kiv,n+1,x,y,exp)))
}

pub fn decrypt_data_or_hs(ciphertext:&Bytes, st: DuplexCipherState1) -> Res<(ContentType,Bytes,DuplexCipherState1)> {
    let DuplexCipherState1(ae, x, y, kiv, n, exp) = st;
    let (ct,payload) = decrypt_record_payload(&ae,&kiv,n,ciphertext)?;
    Ok((ct,payload,DuplexCipherState1(ae, x, y, kiv, n+1, exp)))
}
pub fn decrypt_data(ciphertext:&Bytes, st: DuplexCipherState1) -> Res<(AppData,DuplexCipherState1)> {
    let DuplexCipherState1(ae, x, y, kiv, n, exp) = st;
    let (ct,payload) = decrypt_record_payload(&ae,&kiv,n,ciphertext)?;
    check(ct == ContentType::ApplicationData)?;
    Ok((AppData(payload),DuplexCipherState1(ae, x, y, kiv, n+1, exp)))
}
