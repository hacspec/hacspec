use hacspec_lib::*;
use crate::*;

#[derive(Clone,Default)]
pub enum Entry {
    #[default]
    Init,
    Fresh{rnd:Bytes},
    Event{a:Principal,ev:Bytes},
    Session{a:Principal,sid:usize,st:Bytes},
    Message{a:Principal,b:Principal,m:Bytes}
}

pub struct Trace(Seq<Entry>);

impl Env for Trace {
    type SessionId = usize;
    type MessageId = usize;
    
    fn rand_gen(len:usize,env:&mut Self) -> Bytes {
        let mut rnd = Seq::new(len);
        rnd[0] = U8(env.0.len() as u8);
        rnd[1] = U8((env.0.len() >> 8) as u8);
        rnd[2] = U8((env.0.len() >> 16) as u8);
        rnd[2] = U8((env.0.len() >> 24) as u8);
        (*env).0 = env.0.push(&Entry::Fresh{rnd:rnd.clone()});
        rnd
    }

    fn trigger_event(a:Principal,ev:Bytes,env:&mut Self) {
        (*env).0 = env.0.push(&Entry::Event{a,ev});
    }

    fn new_session(a:Principal,st:Bytes,env:&mut Self) -> usize{
        let sid = env.0.len();
        (*env).0 = env.0.push(&Entry::Session{a,sid,st});
        sid
    }

    fn read_session(a:Principal,sid:Self::SessionId,env:&mut Self) -> Option<Bytes> {
        let mut st = None;
        for i in 0..env.0.len() {
            let j = env.0.len() - 1 - i;
            match &env.0[j] {
                Entry::Session{a:p,sid:psid,st:pst} =>
                    if a.declassify_eq(&p) && sid == *psid {
                    st = Some(pst.clone());
                    },
                _ => {}
            }
        }
        st
    }

    fn find_session<F>(a:Principal,filter:F,env:&mut Self) -> Option<Bytes> 
        where F: Fn (Bytes) -> bool {
        let mut st = None;
        for i in 0..env.0.len() {
            let j = env.0.len() - 1 - i;
            match &env.0[j] {
                Entry::Session{a:p,sid:psid,st:pst} =>
                    if a.declassify_eq(&p) && filter(pst.clone()) {
                    st = Some(pst.clone());
                    },
                _ => {}
            }
        }
        st
    }

    fn update_session(a:Principal,sid:Self::SessionId,st:Bytes,env:&mut Self) {
        (*env).0 = env.0.push(&Entry::Session{a,sid,st}); 
    }

    fn send(a:Principal,b:Principal,m:Bytes,env:&mut Self) -> usize{
        let msgid = env.0.len();
        (*env).0 = env.0.push(&Entry::Message{a,b,m});
        msgid
    }

    fn receive(a:Principal,msgid:Self::MessageId,env:&mut Self) -> Option<(Principal,Bytes)> {
        if msgid >= env.0.len() {None}
        else {
            match &env.0[msgid] {
                Entry::Message{a:_,b:q,m:msg} => {
                    if a.declassify_eq(&q) {
                        Some ((a,msg.clone()))
                    }
                    else {None}
                },
                _ => None
        }}
    }

    fn pke_encrypt(pk_b:Pubkey,m:Bytes,env:&mut Self) -> Bytes {
        Seq::new(32+16)
    }

    fn pke_decrypt(sk_b:Privkey,m:Bytes,env:&mut Self) -> Option<Bytes> {
        Some(Seq::new(32+16))
    }
}
