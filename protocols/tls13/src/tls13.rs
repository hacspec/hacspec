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

pub struct Client0(ALGS,Bytes,ClientPostClientHello,Option<(CipherState,KEY)>);
pub struct Client1(ALGS,Bytes,ClientPostClientFinished,CipherState,CipherState,KEY);

pub fn client_init(algs0:ALGS,sn:&Bytes,tkt_psk:Option<(&Bytes,KEY)>,ent:Entropy) -> Res<(Bytes,Client0)> {
    let ALGS(ha, ae, sa, gn, psk_mode, zero_rtt) = &algs0;
    let mut transcript = empty();
    match (psk_mode,tkt_psk) {
        (true,Some((tkt,psk))) => {
            let (crand,gx,cstate) = get_client_hello(algs0,Some(psk),ent)?;
            let (ch,trunc_len) = client_hello(&algs0,&crand,&gx,sn,Some(tkt))?;
            let trunc_hash = TranscriptTruncatedClientHello(hash(ha,&ch.slice_range(0..trunc_len))?);
            let binder = get_client_hello_binder(&trunc_hash,&cstate)?;
            let nch = ch.update_slice(trunc_len,&binder,0,hash_len(ha));
            transcript = transcript.concat(&nch);
            let rec = handshake_record(&nch)?;
            let tx0 = TranscriptClientHello(hash(ha,&nch)?);
            let (cip,exp) = client_get_0rtt_keys(&tx0,&cstate)?;
            let st = Client0(algs0,transcript,cstate,Some((cip,exp)));
            Ok((rec,st))
        },
        (false, None) => {
            let (crand,gx,cstate) = get_client_hello(algs0,None,ent)?;
            let (ch,_) = client_hello(&algs0,&crand,&gx,sn,None)?;
            transcript = transcript.concat(&ch);
            let rec = handshake_record(&ch)?;
            let st = Client0(algs0,transcript,cstate,None);
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
        let (ee,len3) = check_handshake_record(&payload)?;
        parse_encrypted_extensions(&algs,&ee)?;
        transcript = transcript.concat(&payload.slice_range(next..next+len3));
        next = next + len3;
        let (sc,len4) = check_handshake_record(&payload.slice_range(next..payload.len()))?;
        let cert = parse_server_certificate(&algs,&sc)?;
        transcript = transcript.concat(&payload.slice_range(next..next+len4));
        let tx1 = TranscriptServerCertificate(hash(ha,&transcript)?);
        next = next + len4;
        let (cv,len5) = check_handshake_record(&payload.slice_range(next..payload.len()))?;
        let sig = parse_certificate_verify(&algs,&cv)?;
        transcript = transcript.concat(&payload.slice_range(next..next+len5));
        let tx2 = TranscriptServerCertificateVerify(hash(ha,&transcript)?);
        next = next + len5;       
        let (fin,len6) = check_handshake_record(&payload.slice_range(next..payload.len()))?;
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