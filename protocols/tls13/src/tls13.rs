#![allow(dead_code)]
#![allow(unused_variables)]
#![allow(non_camel_case_types)]
#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(unused_imports)]
#![allow(unused_parens)]

mod tls13formats;
use tls13formats::*;
mod tls13crypto;
use tls13crypto::*;
mod tls13core;
use tls13core::*;

// Import hacspec and all needed definitions.
use hacspec_lib::*;

pub fn handshake_record(p:&Bytes) -> Res<Bytes> {
    let ty = bytes1(0x16);
    let ver = bytes2(3,1);
    Ok(ty.concat(&ver).concat(&lbytes2(p)?))
}

pub fn check_handshake_record(p:&Bytes) -> Res<(Bytes,usize)> {
    let ty = bytes1(0x16);
    let ver = bytes2(3,1);
    check_eq(&ty,&p.slice_range(0..1))?;
    check_eq(&ver,&p.slice_range(1..3))?;
    let len = check_lbytes2(&p.slice_range(3..p.len()))?;
    Ok((p.slice_range(5..5+len),5+len))
}

pub fn first_application_record(p:&Bytes) -> Res<usize> {
    let pref = bytes3(0x17,3,3);
    check_eq(&pref,&p.slice_range(0..3))?;
    let len = check_lbytes2(&p.slice_range(3..p.len()))?;
    Ok(len+5)
}

pub fn check_handshake_message(p:&Bytes) -> Res<(Bytes,usize)> {
    let len = check_lbytes3(&p.slice_range(1..p.len()))?;
    Ok((p.slice_range(0..4+len),4+len))
}

pub struct Client0(ALGS,Bytes,ClientPostClientHello,Option<(CipherState,KEY)>);
pub struct Client1(ALGS,Bytes,ClientPostClientFinished,CipherState,CipherState,KEY);

pub fn client_init(algs:ALGS,sn:&Bytes,tkt_psk:Option<(&Bytes,KEY)>,ent:Entropy) -> Res<(Bytes,Client0)> {
    let ALGS(ha, ae, sa, gn, psk_mode, zero_rtt) = &algs;
    let mut transcript = empty();
    match (psk_mode,tkt_psk) {
        (true,Some((tkt,psk))) => {
            let (crand,gx,cstate) = get_client_hello(algs,Some(psk),ent)?;
            let (ch,trunc_len) = client_hello(&algs,&crand,&gx,sn,Some(tkt))?;
            let trunc_hash = TranscriptTruncatedClientHello(hash(ha,&ch.slice_range(0..trunc_len))?);
            let binder = get_client_hello_binder(&trunc_hash,&cstate)?;
            let nch = ch.update_slice(trunc_len,&binder,0,hash_len(ha));
            transcript = transcript.concat(&nch);
            let rec = handshake_record(&nch)?;
            match zero_rtt {
                true => {let tx0 = TranscriptClientHello(hash(ha,&nch)?);
                         let (cip,exp) = client_get_0rtt_keys(&tx0,&cstate)?;
                         let st = Client0(algs,transcript,cstate,Some((cip,exp)));
                         Ok((rec,st))},
                false => Ok((rec,Client0(algs,transcript,cstate,None)))
            }            
        },
        (false, None) => {
            let (crand,gx,cstate) = get_client_hello(algs,None,ent)?;
            let (ch,_) = client_hello(&algs,&crand,&gx,sn,None)?;
            transcript = transcript.concat(&ch);
            let rec = handshake_record(&ch)?;
            let st = Client0(algs,transcript,cstate,None);
            Ok((rec,st))
        },
        _ => Err(psk_mode_mismatch)
    }
}

pub fn pk_from_cert(cert:&Bytes) -> Res<VERK> {
    Ok(VERK::new(64))
}

pub fn client_finish(msg:&Bytes,st:Client0) -> Res<(Bytes,Client1)> {
    let Client0(algs,transcript,cstate,_) = st;
    let ALGS(ha, ae, sa, gn, psk_mode, zero_rtt) = &algs;
    let (sh,len1) = check_handshake_record(&msg)?;
    let (sr,gy) = parse_server_hello(&algs,&sh)?;
    let mut transcript = transcript.concat(&sh);    
    let tx = TranscriptServerHello(hash(ha,&transcript)?); 
    let (c2s,s2c,cstate) = put_server_hello(sr, gy, algs, &tx, cstate)?;
    let len2 = first_application_record(&msg.slice_range(len1..msg.len()))?;
    let (ct,payload,s2c) = decrypt_record(&msg.slice_range(len1..len1+len2),s2c)?;
    if ct == ct_handshake {
        let mut next = 0;
        let (ee,len3) = check_handshake_message(&payload)?;
        parse_encrypted_extensions(&algs,&ee)?;
        transcript = transcript.concat(&payload.slice_range(next..next+len3));
        next = next + len3;
        let (sc,len4) = check_handshake_message(&payload.slice_range(next..payload.len()))?;
        let cert = parse_server_certificate(&algs,&sc)?;
        transcript = transcript.concat(&payload.slice_range(next..next+len4));
        let tx1 = TranscriptServerCertificate(hash(ha,&transcript)?);
        next = next + len4;
        let (cv,len5) = check_handshake_message(&payload.slice_range(next..payload.len()))?;
        let sig = parse_certificate_verify(&algs,&cv)?;
        transcript = transcript.concat(&payload.slice_range(next..next+len5));
        let tx2 = TranscriptServerCertificateVerify(hash(ha,&transcript)?);
        next = next + len5;       
        let (fin,len6) = check_handshake_message(&payload.slice_range(next..payload.len()))?;
        let vd = parse_finished(&algs,&fin)?;
        transcript = transcript.concat(&payload.slice_range(next..next+len6));
        let tx3 = TranscriptServerFinished(hash(ha,&transcript)?);
        next = next + len6;
        if next == payload.len() {
            let pk = pk_from_cert(&cert)?;
            let cstate = put_server_signature(&pk, &sig, &tx1, cstate)?;
            let cstate = put_server_finished(&vd,&tx2,cstate)?;
            let (c2sa,s2ca,exp) = client_get_1rtt_keys(&tx3,&cstate)?;
            let (vd,cstate) = get_client_finished(&tx3,cstate)?;
            let cfin = finished(&algs,&vd)?;
            transcript = transcript.concat(&cfin);
            let (cfin_rec,c2s) = encrypt_record(ct_handshake,&cfin,0,c2s)?;
            Ok((cfin_rec,Client1(algs,transcript,cstate,c2sa,s2ca,exp)))
        } else {Err(parse_failed)}
    } else {Err(parse_failed)}
}

pub struct Server0(ALGS,Bytes,ServerPostServerFinished,Option<(CipherState,KEY)>,CipherState,CipherState,CipherState,KEY);
pub struct Server1(ALGS,Bytes,ServerPostClientFinished,CipherState,CipherState,KEY);

fn get_psk_opts(ha: &HashAlgorithm, psk_mode:&bool,client_tkt_psk:Option<(Bytes,HMAC,usize)>,
                server_tkt_psk:Option<(&Bytes,KEY)>, tx:&Bytes) -> 
                Res<Option<(PSK, TranscriptTruncatedClientHello, HMAC)>> {
    match (psk_mode,client_tkt_psk, server_tkt_psk) {
        (true, Some((tktc,binder,trunc_len)), Some((tkts,psk))) => {
                check_eq(&tktc,&tkts)?;
                let trunc_hash = TranscriptTruncatedClientHello(hash(ha,&tx.slice_range(0..trunc_len))?);          
                Ok(Some((psk,trunc_hash,binder)))},
        (false, None, None) => Ok(None),
        _ => {return(Err(parse_failed))}
    }             
}

pub fn server_init(algs:ALGS,msg:&Bytes,sn:&Bytes,cert:&Bytes,sk:&SIGK,tkt_psks:Option<(&Bytes,KEY)>,ent:Entropy) -> Res<(Bytes,Server0)> {
    let ALGS(ha, ae, sa, gn, psk_mode, zero_rtt) = &algs;
    let mut transcript = empty();
    let (ch,len1) = check_handshake_record(&msg)?;
    let (cr,sid,snc,gx,tkt_pskc) = parse_client_hello(&algs,&ch)?;
    check_eq(&snc,sn)?;
    let psk_opt = get_psk_opts(ha,psk_mode,tkt_pskc,tkt_psks,&ch)?;        
    transcript = transcript.concat(&ch);
    let (sr,gy,sstate) = put_client_hello(cr,algs,&gx,psk_opt,ent)?;
    let mut c2s0 = None;
    match zero_rtt {
        true => {let tx0 = TranscriptClientHello(hash(ha,&transcript)?);
                 let (cip,exp) = server_get_0rtt_keys(&tx0,&sstate)?;
                 c2s0 = Some((cip,exp))},
        false => ()
    }           
    let sh = server_hello(&algs,&sr,&sid,&gy)?;
    transcript = transcript.concat(&sh);
    let tx1 = TranscriptServerHello(hash(ha,&transcript)?);
    let (c2s,s2c,sstate) = get_server_hello(&tx1,sstate)?;
    let ee = encrypted_extensions(&algs)?;
    let mut payload = empty();
    payload = payload.concat(&ee);
    transcript = transcript.concat(&ee);
    let sc = server_certificate(&algs,&cert)?;
    payload = payload.concat(&sc);
    transcript = transcript.concat(&sc);
    let tx2 = TranscriptServerCertificate(hash(ha,&transcript)?);
    let (sig,sstate) = get_server_signature(sk,&tx2,sstate)?;
    let cv = certificate_verify(&algs,&sig)?;
    payload = payload.concat(&cv);
    transcript = transcript.concat(&cv);
    let tx3 = TranscriptServerCertificateVerify(hash(ha,&transcript)?);
    let (vd,sstate) = get_server_finished(&tx3,sstate)?;
    let fin = finished(&algs,&vd)?;
    payload = payload.concat(&fin);
    transcript = transcript.concat(&fin);
    let tx3 = TranscriptServerFinished(hash(ha,&transcript)?);
    let (c2sa,s2ca,exp) = server_get_1rtt_keys(&tx3, &sstate)?;
    let rec0 = handshake_record(&sh)?;
    let (rec1,s2c) = encrypt_record(ct_handshake,&payload,0,s2c)?;
    Ok((rec0.concat(&rec1),Server0(algs,transcript,sstate,c2s0,c2s,c2sa,s2ca,exp)))
}
    
pub fn server_finish(msg:&Bytes,st:Server0) -> Res<Server1> {
    let Server0(algs,transcript,sstate,c2s0,c2sh,c2sa,s2ca,exp) = st;
    let ALGS(ha, ae, sa, gn, psk_mode, zero_rtt) = &algs;
    let len = first_application_record(&msg)?;
    let (ct,payload,s2c) = decrypt_record(&msg.slice_range(0..len),c2sh)?;
    if ct == ct_handshake {
        let (cfin,flen) = check_handshake_message(&payload)?;
        let vd = parse_finished(&algs,&cfin)?;
        let tx = TranscriptServerFinished(hash(ha,&transcript)?);
        let sstate = put_client_finished(vd,&tx,sstate)?;
        let transcript = transcript.concat(&cfin);
        Ok(Server1(algs,transcript,sstate,c2sa,s2ca,exp))
    } else {Err(parse_failed)}
}

pub fn client_send0(st:Client0,msg:&Bytes) -> Res<(Bytes,Client0)> {
    let Client0(algs,transcript,cstate,c2s0) = st;
    if let Some((c2s,exp)) = c2s0 {
        let (cip,c2s) = encrypt_record(ct_app_data,msg,0,c2s)?;
        Ok((cip,Client0(algs,transcript,cstate,Some((c2s,exp)))))
    } else {Err(psk_mode_mismatch)}
}

pub fn client_send1(st:Client1,msg:&Bytes) -> Res<(Bytes,Client1)> {
    let Client1(algs,transcript,cstate,c2sa,s2ca,exp) = st;
    let (cip,c2sa) = encrypt_record(ct_app_data,msg,0,c2sa)?;
    Ok((cip,Client1(algs,transcript,cstate,c2sa,s2ca,exp)))
}

pub fn client_recv1(st:Client1,msg:&Bytes) -> Res<(Bytes,Client1)> {
    let Client1(algs,transcript,cstate,c2sa,s2ca,exp) = st;
    let (ct,plain,s2ca) = decrypt_record(msg,s2ca)?;
    if ct == ct_app_data {
        Ok((plain,Client1(algs,transcript,cstate,c2sa,s2ca,exp)))
    } else {Err(parse_failed)}
}

pub fn server_recv0(st:Server0,msg:&Bytes) -> Res<(Bytes,Server0)> {
    let Server0(algs,transcript,sstate,c2szero,c2sh,c2sa,s2ca,exp) = st;
    if let Some((c2s0,exp0)) = c2szero {
        let (ct,plain,c2s0) = decrypt_record(msg,c2s0)?;
        if ct == ct_app_data {
           Ok((plain,Server0(algs,transcript,sstate,Some((c2s0,exp0)),c2sh,c2sa,s2ca,exp)))
        } else {Err(parse_failed)}
    } else {Err(psk_mode_mismatch)}
}
pub fn server_send1(st:Server1,msg:&Bytes) -> Res<(Bytes,Server1)> {
    let Server1(algs,transcript,sstate,c2sa,s2ca,exp) = st;
    let (cip,s2ca) = encrypt_record(ct_app_data,msg,0,s2ca)?;
    Ok((cip,Server1(algs,transcript,sstate,c2sa,s2ca,exp)))
}

pub fn server_recv1(st:Server1,msg:&Bytes) -> Res<(Bytes,Server1)> {
    let Server1(algs,transcript,sstate,c2sa,s2ca,exp) = st;
    let (ct,plain,c2sa) = decrypt_record(msg,c2sa)?;
    if ct == ct_app_data {
        Ok((plain,Server1(algs,transcript,sstate,c2sa,s2ca,exp)))
    } else {Err(parse_failed)}
}