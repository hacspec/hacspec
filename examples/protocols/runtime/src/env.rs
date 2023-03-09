use hacspec_lib::*;
use crate::*;
use rand::prelude::*;
use rand_chacha::ChaCha20Rng;
use std::collections::HashMap;

// This is a naive implementation of a Protocol Runtime.
// We should be using better data structures and avoiding so many clones/copies

pub type SessionId = usize;
pub type MessageId = usize;

pub struct Env {
    rng: ChaCha20Rng,
    log: Seq<(Principal,Bytes)>,
    sessions: Seq<(Principal,Bytes)>,
    msgs_in: Seq<(Principal,Principal,Bytes)>,
    msgs_out: Seq<(Principal,Principal,Bytes)>
}

pub fn init_env() -> Env {
    Env {rng : ChaCha20Rng::from_entropy(),
         log: Seq::new(0),
         sessions: Seq::new(0),
         msgs_in: Seq::new(0),
         msgs_out: Seq::new(0),
        }
}

pub fn rand_gen(len:usize,env:&mut Env) -> Bytes{
    let random_bytes: Vec<U8> = (0..len).map(|_| { U8(env.rng.gen::<u8>()) }).collect();
    Seq::from_vec(random_bytes)
}

pub fn trigger_event(a:Principal,ev:Bytes,env:&mut Env) {
    env.log = env.log.push(&(a,ev));
}

pub fn new_session(a:Principal,s:Bytes,env:&mut Env) -> SessionId {
    let sid = env.sessions.len();
    env.sessions = env.sessions.push(&(a,s));
    sid    
}

pub fn read_session(a:Principal,sid:SessionId,env:&mut Env) -> Option<Bytes> {
    if sid >= env.sessions.len() {None}
    else {
        let (aa,st) = env.sessions[sid].clone();
        if a.declassify_eq(&aa) {
            Some(st)
        } else {None}   
    }
}

pub fn update_session(a:Principal,sid:SessionId,s:Bytes,env:&mut Env) -> Option<()> {
    if sid >= env.sessions.len() {None}
    else {
        let (aa,_) = env.sessions[sid];
        if a.declassify_eq(&aa) {
            env.sessions[sid] = (a,s);
            Some(())
        } else {None}  
    }
}

pub fn find_session<F>(a:Principal,filter:F,env:&mut Env) -> Option<Bytes>
                 where F: Fn (&Bytes) -> bool {
    let mut st = None;
    for i in 0..env.sessions.len() {
        let (aa,pst) = env.sessions[i].clone(); 
        if a.declassify_eq(&aa) && filter(&pst) {
                st = Some(pst.clone());
                break;
        } else {}
    }
    st                  
}

pub fn send(a:Principal,b:Principal,m:Bytes,env:&mut Env) -> MessageId {
    let msgid = env.msgs_out.len();
    env.msgs_out = env.msgs_out.push(&(a,b,m));
    msgid 
}

pub fn receive_next(b:Principal,env:&mut Env) -> Option<(Principal,Bytes)> {
    if env.msgs_in.len() == 0 {None}
    else {
        let ((aa,bb,m),msgs) = env.msgs_in.clone().pop();
        if b.declassify_eq(&bb) {
            env.msgs_in = msgs;
            Some((aa,m.clone()))
        } else {None}   
    }
}

pub fn receive(b:Principal,msgid:MessageId,env:&mut Env) -> Option<(Principal,Bytes)> {
    if env.msgs_in.len() <= msgid {None}
    else {
        let (msgs0,msgs1) = env.msgs_in.clone().split_off(msgid);
        let ((aa,bb,m),msgs1) = msgs1.pop();
        if b.declassify_eq(&bb) {
            env.msgs_in = msgs0.concat(&msgs1);
            Some((aa,m))
        } else {None}   
    }
}

/*
pub trait Env: Sized {
  type SessionId: Copy+Clone;
  type MessageId: Copy+Clone;
  fn rand_gen(len:usize,env:&mut Self) -> Bytes;
  fn trigger_event(a:Principal,ev:Bytes,env:&mut Self);
  fn new_session(a:Principal,s:Bytes,env:&mut Self) -> Self::SessionId;
  fn read_session(a:Principal,sid:Self::SessionId,env:&mut Self) -> Option<Bytes>;
  fn find_session<F>(a:Principal,filter:F,env:&mut Self) -> Option<Bytes>
                 where F: Fn (&Bytes) -> bool;
  fn update_session(a:Principal,sid:Self::SessionId,s:Bytes,env:&mut Self);
  fn send(a:Principal,b:Principal,m:Bytes,env:&mut Self) -> Self::MessageId;
  fn receive(a:Principal,msgid:Self::MessageId,env:&mut Self) -> Option<(Principal,Bytes)>;
  fn pke_encrypt(pk_b:Pubkey,m:Bytes,env:&mut Self) -> Bytes;
  fn pke_decrypt(sk_b:Privkey,m:Bytes,env:&mut Self) -> Option<Bytes>;
}
 */