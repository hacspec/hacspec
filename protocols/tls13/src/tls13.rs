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

pub struct Client0(ALGS,Bytes,ClientPostClientHello,Option<(CipherState,KEY)>);
pub struct Client1(ALGS,Bytes,ClientPostClientHello,Option<(CipherState,KEY)>);

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

pub fn client_finish(msg:&Bytes,st:Client0) -> Res<(Bytes,Client1)> {
    let Client0(algs,transcript,cstate,_) = st;
    let ALGS(ha, ae, sa, gn, psk_mode, zero_rtt) = &algs;
    let (sh,len) = check_handshake_record(&msg)?;
    let (sr,gy) = parse_server_hello(&algs,&sh)?;
    let transcript = transcript.concat(&sh);    
    let tx = TranscriptServerHello(hash(ha,&transcript)?); 
    let (c2s,s2c,cstate) = put_server_hello(sr, gy, algs, &tx, cstate)?;
    Err(0)
}