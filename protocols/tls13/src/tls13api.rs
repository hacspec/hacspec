// Import hacspec and all needed definitions.
use hacspec_lib::*;
use crate::cryptolib::*;
use crate::tls13formats::*;
use crate::tls13record::*;
use crate::tls13handshake::*;
// Client-Side API for TLS 1.3 Applications
// client_init -> (client_send0)* -> client_finish -> (client_send1|client_recv1)* */

pub struct Client0(ALGS,TranscriptClientHello,ClientPostClientHello,Option<(CipherState,KEY)>);
pub struct Client1(ALGS,TranscriptClientFinished,ClientPostClientFinished,CipherState,CipherState,KEY);
    
pub fn client_init(algs:ALGS,sn:&Bytes,tkt:Option<Bytes>,psk:Option<KEY>,ent:Entropy) -> Res<(Bytes,Client0)> {
    let ALGS(ha, ae, sa, gn, psk_mode, zero_rtt) = &algs;
    let (crand,gx,cstate) = get_client_hello(algs,psk,ent)?;
    let (ch,trunc_len) = client_hello(&algs,&crand,&gx,sn,&tkt)?;
    let tx_trunc = transcript_truncated_client_hello(algs,&ch,trunc_len)?;
    let binder = get_client_hello_binder(&tx_trunc,&cstate)?;
    let nch = set_client_hello_binder(&algs,&binder,ch)?;
    let tx_ch = transcript_client_hello(algs,&nch)?;
    let mut rec = handshake_record(&nch)?;
    rec[2] = U8(0x01);
    let c2s0 = client_get_0rtt_keys(&tx_ch,&cstate)?;
    let st = Client0(algs,tx_ch,cstate,c2s0);
    Ok((rec,st))  
}

pub fn client_send0(st:Client0,msg:&Bytes) -> Res<(Bytes,Client0)> {
    let Client0(algs,transcript,cstate,c2s0) = st;
    if let Some((c2s,exp)) = c2s0 {
        let (cip,c2s) = encrypt_record(ct_app_data,msg,0,c2s)?;
        Ok((cip,Client0(algs,transcript,cstate,Some((c2s,exp)))))
    } else {Err(psk_mode_mismatch)}
}

pub fn client_finish(msg:&Bytes,st:Client0) -> Res<(Bytes,Client1)> {
    let Client0(algs,tx_ch,cstate,_) = st;
    let ALGS(ha, ae, sa, gn, psk_mode, zero_rtt) = &algs;
    let mut next = 0;
    let (sh,len1) = check_handshake_record(&msg)?;
    let (sr,gy) = parse_server_hello(&algs,&sh)?;    
    let tx_sh = transcript_server_hello(tx_ch,&sh)?;
    let (c2s,s2c,cstate) = put_server_hello(sr, gy, algs, &tx_sh, cstate)?;
    next = next + len1;
    let len2 = check_ccs_record(&msg.slice_range(next..msg.len()))?;
    next = next + len2;
    let len3 = check_encrypted_record(&msg.slice_range(next..msg.len()))?;
    let (ct,payload,s2c) = decrypt_record(&msg.slice_range(next..next+len3),s2c)?;   
    if ct == ct_handshake {
        next = 0;
        let (ee,len4) = check_handshake_message(&payload)?;
        parse_encrypted_extensions(&algs,&ee)?;
        next = next + len4;
        let (tx_cv,cstate) =
            match psk_mode {
                false => {  
                    let (sc,len5) = check_handshake_message(&payload.slice_range(next..payload.len()))?;
                    let cert = parse_server_certificate(&algs,&sc)?;
                    next = next + len5;
                   // println!("HERE len {}, {}",payload.len() - next, &payload.slice_range(next..payload.len()).to_hex());  
                    let (cv,len6) = check_handshake_message(&payload.slice_range(next..payload.len()))?;
                    let sig = parse_certificate_verify(&algs,&cv)?;


                    next = next + len6; 
                    let pk = verk_from_cert(&cert)?;
         
                    let tx_sc = transcript_server_certificate(tx_sh,&ee,&sc)?;
                    let cstate = put_server_signature(&pk, &sig, &tx_sc, cstate)?;
                    let tx_cv = transcript_server_certificate_verify(tx_sc,&cv)?;
                    (tx_cv,cstate)}
                true => {
                    let cstate = put_skip_server_signature(cstate)?;
                    let tx_cv = transcript_skip_server_certificate_verify(tx_sh,&ee)?;
                    (tx_cv,cstate)
                }
            };    
        let (sfin,len6) = check_handshake_message(&payload.slice_range(next..payload.len()))?;
        let vd = parse_finished(&algs,&sfin)?;
        next = next + len6;
        if next == payload.len() {
            let cstate = put_server_finished(&vd,&tx_cv,cstate)?;
            let tx_sf = transcript_server_finished(tx_cv,&sfin)?;
            let (c2sa,s2ca,exp) = client_get_1rtt_keys(&tx_sf,&cstate)?;
            let (vd,cstate) = get_client_finished(&tx_sf,cstate)?;
            let cfin = finished(&algs,&vd)?;
            let tx_cf = transcript_client_finished(tx_sf,&cfin)?;
            let (cfin_rec,c2s) = encrypt_record(ct_handshake,&cfin,0,c2s)?;
            Ok((cfin_rec,Client1(algs,tx_cf,cstate,c2sa,s2ca,exp)))
        } else {Err(parse_failed)}
    } else {Err(parse_failed)}
}


pub fn client_send1(st:Client1,msg:&Bytes) -> Res<(Bytes,Client1)> {
    let Client1(algs,transcript,cstate,c2sa,s2ca,exp) = st;
    let (cip,c2sa) = encrypt_record(ct_app_data,msg,0,c2sa)?;
    Ok((cip,Client1(algs,transcript,cstate,c2sa,s2ca,exp)))
}

pub fn client_recv1(st:Client1,msg:&Bytes) -> Res<(Bytes,usize,Client1)> {
    let Client1(algs,transcript,cstate,c2sa,s2ca,exp) = st;
    let len = check_encrypted_record(&msg)?;
    let (ct,plain,s2ca) = decrypt_record(&msg.slice_range(0..len),s2ca)?;
    if ct == ct_app_data {
        Ok((plain,len,Client1(algs,transcript,cstate,c2sa,s2ca,exp)))
    } else {Err(parse_failed)}
}

// Server-Side API for TLS 1.3 Applications
// server_init -> (server_recv0)* -> server_finish -> (server_recv1|server_send1)* */

pub struct Server0(ALGS,TranscriptServerFinished,ServerPostServerFinished,Option<(CipherState,KEY)>,CipherState,CipherState,CipherState,KEY);
pub struct Server1(ALGS,TranscriptClientFinished,ServerPostClientFinished,CipherState,CipherState,KEY);

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

pub fn server_init(algs:ALGS,db:ServerDB,msg:&Bytes,ent:Entropy) -> Res<(Bytes,Server0)> {
    let ALGS(ha, ae, sa, gn, psk_mode, zero_rtt) = &algs;
    let (ch,len1) = check_handshake_record(&msg)?;
    let (cr,sid,sni,gx,tkto, bindero, trunc_len) = parse_client_hello(&algs,&ch)?;
    let tx_trunc = transcript_truncated_client_hello(algs,&ch,trunc_len)?;
    let (cert,sigk,psk_opt) = lookup_db(algs,&db,&sni,&tkto)?;
    let (sr,gy,sstate) = put_client_hello(cr,algs,&gx,psk_opt,tx_trunc,bindero,ent)?;
    let tx_ch = transcript_client_hello(algs,&ch)?;
    let c2s0 = server_get_0rtt_keys(&tx_ch,&sstate)?;
    let sh = server_hello(&algs,&sr,&sid,&gy)?;
    
    let tx_sh = transcript_server_hello(tx_ch,&sh)?;
    let (c2s,s2c,sstate) = get_server_hello(&tx_sh,sstate)?;
    let ee = encrypted_extensions(&algs)?;
    let mut payload = empty();
    payload = payload.concat(&ee);
    let (tx_cv,sstate) =
        match psk_mode {
            false => {
                let sc = server_certificate(&algs,&cert)?;
                payload = payload.concat(&sc);
                let tx_sc = transcript_server_certificate(tx_sh,&ee,&sc)?;
                let (sig,sstate) = get_server_signature(&sigk,&tx_sc,sstate)?;
                let cv = certificate_verify(&algs,&sig)?;
                payload = payload.concat(&cv);
                let tx_cv = transcript_server_certificate_verify(tx_sc,&cv)?;
                (tx_cv,sstate)},
            true => {
                let tx_cv = transcript_skip_server_certificate_verify(tx_sh,&ee)?;
                let sstate = get_skip_server_signature(sstate)?;
                (tx_cv,sstate)}
        };
    let (vd,sstate) = get_server_finished(&tx_cv,sstate)?;
    let sfin = finished(&algs,&vd)?;
    payload = payload.concat(&sfin);
    let tx_sf = transcript_server_finished(tx_cv,&sfin)?;
    let (c2sa,s2ca,exp) = server_get_1rtt_keys(&tx_sf, &sstate)?;
    let rec0 = handshake_record(&sh)?;
    let (rec1,s2c) = encrypt_record(ct_handshake,&payload,0,s2c)?;
    Ok((rec0.concat(&rec1),Server0(algs,tx_sf,sstate,c2s0,c2s,c2sa,s2ca,exp)))
}
    
pub fn server_finish(msg:&Bytes,st:Server0) -> Res<Server1> {
    let Server0(algs,tx_sf,sstate,c2s0,c2sh,c2sa,s2ca,exp) = st;
     let len = check_encrypted_record(&msg)?;
    let (ct,payload,s2c) = decrypt_record(&msg.slice_range(0..len),c2sh)?;
    if ct == ct_handshake {
        let (cfin,flen) = check_handshake_message(&payload)?;
        let vd = parse_finished(&algs,&cfin)?;
        let sstate = put_client_finished(vd,&tx_sf,sstate)?;
        let tx_cf = transcript_client_finished(tx_sf,&cfin)?;
        Ok(Server1(algs,tx_cf,sstate,c2sa,s2ca,exp))
    } else {Err(parse_failed)}
}

pub fn server_recv0(st:Server0,msg:&Bytes) -> Res<(Bytes,usize,Server0)> {
    let Server0(algs,transcript,sstate,c2szero,c2sh,c2sa,s2ca,exp) = st;
    let len = check_encrypted_record(&msg)?;
    if let Some((c2s0,exp0)) = c2szero {
        let (ct,plain,c2s0) = decrypt_record(&msg.slice_range(0..len),c2s0)?;
        if ct == ct_app_data {
           Ok((plain,len,Server0(algs,transcript,sstate,Some((c2s0,exp0)),c2sh,c2sa,s2ca,exp)))
        } else {Err(parse_failed)}
    } else {Err(psk_mode_mismatch)}
}
pub fn server_send1(st:Server1,msg:&Bytes) -> Res<(Bytes,Server1)> {
    let Server1(algs,transcript,sstate,c2sa,s2ca,exp) = st;
    let (cip,s2ca) = encrypt_record(ct_app_data,msg,0,s2ca)?;
    Ok((cip,Server1(algs,transcript,sstate,c2sa,s2ca,exp)))
}

pub fn server_recv1(st:Server1,msg:&Bytes) -> Res<(Bytes,usize,Server1)> {
    let Server1(algs,transcript,sstate,c2sa,s2ca,exp) = st;
    let len = check_encrypted_record(&msg)?;
    let (ct,plain,c2sa) = decrypt_record(&msg.slice_range(0..len),c2sa)?;
    if ct == ct_app_data {
        Ok((plain,len,Server1(algs,transcript,sstate,c2sa,s2ca,exp)))
    } else {Err(parse_failed)}
}
