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

pub type EnvResult<T> = Result<(T,Env),Error>;

pub fn rand_gen(len:usize,mut env:Env) -> EnvResult<Bytes> {
    let random_bytes: Vec<u8> = (0..len).map(|_| { env.rng.gen::<u8>()}).collect();
    Ok((Bytes::from_vec(random_bytes), env))
}

pub fn trigger_event(a:Principal,ev:Bytes,mut env:Env) -> EnvResult<()> {
    env.log = env.log.push(&(a,ev));
    Ok(((),env))
}

pub fn new_session(a:Principal,s:Bytes,mut env:Env) -> EnvResult<SessionId> {
    let sid = env.sessions.len();
    env.sessions = env.sessions.push(&(a,s));
    Ok((sid,env))
}

pub fn read_session(a:Principal,sid:SessionId,env:Env) -> EnvResult<Bytes> {
    if sid >= env.sessions.len() {Err(Error::SessionNotFound)}
    else {
        let (aa,st) = env.sessions[sid].clone();
        if a.eq(&aa) {
            Ok((st,env))
        } else {Err(Error::SessionNotFound)}   
    }
}

pub fn update_session(a:Principal,sid:SessionId,s:Bytes,mut env:Env) -> EnvResult<()> {
    if sid >= env.sessions.len() {Err(Error::SessionNotFound)}
    else {
        let (aa,_) = env.sessions[sid].clone();
        if a.eq(&aa) {
            env.sessions[sid] = (a,s);
            Ok(((),env))
        } else {Err(Error::SessionNotFound)}  
    }
}

pub fn find_session<F>(a:Principal,filter:F,env:Env) -> EnvResult<Bytes>
                 where F: Fn (&Bytes) -> bool {
    let mut st = Err(Error::SessionNotFound);
    for i in 0..env.sessions.len() {
        let (aa,pst) = env.sessions[i].clone(); 
        if a.eq(&aa) && filter(&pst) {
                st = Ok((pst.clone(),env));
                break;
        } else {}
    }
    st                  
}

pub fn send(a:Principal,b:Principal,m:Bytes,mut env:Env) -> EnvResult<MessageId> {
    let msgid = env.msgs_out.len();
    env.msgs_out = env.msgs_out.push(&(a,b,m));
    Ok((msgid,env))
}

pub fn receive_next(b:Principal,mut env:Env) -> EnvResult<(Principal,Bytes)> {
    if env.msgs_in.len() == 0 {Err(Error::MessageNotFound)}
    else {
        let ((aa,bb,m),msgs) = env.msgs_in.clone().pop();
        if b.eq(&bb) {
            env.msgs_in = msgs;
            Ok(((aa,m.clone()),env))
        } else {Err(Error::MessageNotFound)}   
    }
}

pub fn receive(b:Principal,msgid:MessageId,mut env:Env) -> EnvResult<(Principal,Bytes)> {
    if env.msgs_in.len() <= msgid {Err(Error::MessageNotFound)}
    else {
        let (msgs0,msgs1) = env.msgs_in.clone().split_off(msgid);
        let ((aa,bb,m),msgs1) = msgs1.pop();
        if b.eq(&bb) {
            env.msgs_in = msgs0.concat(&msgs1);
            Ok(((aa,m),env))
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
