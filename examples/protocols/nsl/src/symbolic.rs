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

impl Trace for Seq<Entry> {
    type SessionId = usize;
    type MessageId = usize;
    
    fn rand_gen(&mut self,len:usize) -> Bytes {
        let mut rnd = Seq::new(len);
        rnd[0] = U8(self.len() as u8);
        rnd[1] = U8((self.len() >> 8) as u8);
        rnd[2] = U8((self.len() >> 16) as u8);
        rnd[2] = U8((self.len() >> 24) as u8);
        *self = self.push(&Entry::Fresh{rnd:rnd.clone()});
        rnd
    }

    fn trigger_event(&mut self,a:Principal,ev:Bytes) {
        *self = self.push(&Entry::Event{a,ev});
    }

    fn new_session(&mut self,a:Principal,st:Bytes) -> usize{
        let sid = self.len();
        *self = self.push(&Entry::Session{a,sid,st});
        sid
    }

    fn read_session(&mut self,a:Principal,sid:Self::SessionId) -> Option<Bytes> {
        let mut st = None;
        for i in 0..self.len() {
            let j = self.len() - 1 - i;
            match &self[j] {
                Entry::Session{a:p,sid:psid,st:pst} =>
                    if a.declassify_eq(&p) && sid == *psid {
                    st = Some(pst.clone());
                    },
                _ => {}
            }
        }
        st
    }

    fn update_session(&mut self,a:Principal,sid:Self::SessionId,st:Bytes) {
        *self = self.push(&Entry::Session{a,sid,st}); 
    }

    fn send(&mut self,a:Principal,b:Principal,m:Bytes) -> usize{
        let msgid = self.len();
        *self = self.push(&Entry::Message{a,b,m});
        msgid
    }

    fn receive(&mut self,a:Principal,msgid:Self::MessageId) -> Option<(Principal,Bytes)> {
        if msgid >= self.len() {None}
        else {
            match &self[msgid] {
                Entry::Message{a:_,b:q,m:msg} => {
                    if a.declassify_eq(&q) {
                        Some ((a,msg.clone()))
                    }
                    else {None}
                },
                _ => None
        }}
    }

    fn pke_encrypt(&mut self,pk_b:Pubkey,m:Bytes) -> Bytes {
        Seq::new(32+16)
    }
}