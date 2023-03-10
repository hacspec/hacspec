use hacspec_lib::*;
use crate::*;
use rand::prelude::*;
use rand_chacha::ChaCha20Rng;


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
    let random_bytes: Vec<u8> = (0..len).map(|_| { env.rng.gen::<u8>()}).collect();
    Bytes::from_vec(random_bytes)
}

pub fn trigger_event(a:Principal,ev:Bytes,env:&mut Env) {
    env.log = env.log.push(&(a,ev));
}

pub fn new_session(a:Principal,s:Bytes,env:&mut Env) -> SessionId {
    let sid = env.sessions.len();
    env.sessions = env.sessions.push(&(a,s));
    sid    
}

pub fn read_session(a:Principal,sid:SessionId,env:&mut Env) -> Result<Bytes,Error> {
    if sid >= env.sessions.len() {Err(Error::SessionNotFound)}
    else {
        let (aa,st) = env.sessions[sid].clone();
        if a.eq(&aa) {
            Ok(st)
        } else {Err(Error::SessionNotFound)}   
    }
}

pub fn update_session(a:Principal,sid:SessionId,s:Bytes,env:&mut Env) -> Result<(),Error> {
    if sid >= env.sessions.len() {Err(Error::SessionNotFound)}
    else {
        let (aa,_) = env.sessions[sid].clone();
        if a.eq(&aa) {
            env.sessions[sid] = (a,s);
            Ok(())
        } else {Err(Error::SessionNotFound)}  
    }
}

pub fn find_session<F>(a:Principal,filter:F,env:&mut Env) -> Result<Bytes,Error>
                 where F: Fn (&Bytes) -> bool {
    let mut st = Err(Error::SessionNotFound);
    for i in 0..env.sessions.len() {
        let (aa,pst) = env.sessions[i].clone(); 
        if a.eq(&aa) && filter(&pst) {
                st = Ok(pst.clone());
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

pub fn receive_next(b:Principal,env:&mut Env) -> Result<(Principal,Bytes),Error> {
    if env.msgs_in.len() == 0 {Err(Error::MessageNotFound)}
    else {
        let ((aa,bb,m),msgs) = env.msgs_in.clone().pop();
        if b.eq(&bb) {
            env.msgs_in = msgs;
            Ok((aa,m.clone()))
        } else {Err(Error::MessageNotFound)}   
    }
}

pub fn receive(b:Principal,msgid:MessageId,env:&mut Env) -> Result<(Principal,Bytes),Error> {
    if env.msgs_in.len() <= msgid {Err(Error::MessageNotFound)}
    else {
        let (msgs0,msgs1) = env.msgs_in.clone().split_off(msgid);
        let ((aa,bb,m),msgs1) = msgs1.pop();
        if b.eq(&bb) {
            env.msgs_in = msgs0.concat(&msgs1);
            Ok((aa,m))
        } else {Err(Error::MessageNotFound)}   
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