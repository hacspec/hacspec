use hacspec_lib::*;
type bytes = ByteSeq;
use crate::*;

#[derive(Clone,Default)]
pub enum Entry {
    #[default]
    Init,
    Fresh{rnd:bytes},
    Event{a:principal,ev:ProtocolEvent},
    Session{a:principal,sid:usize,st:SessionState},
    Message{a:principal,b:principal,m:bytes}
}

impl Trace for Seq<Entry> {
    type session_id = usize;
    type message_id = usize;
    
    fn rand_gen(&mut self,len:usize) -> bytes {
        let mut rnd = Seq::new(len);
        rnd[0] = U8(self.len() as u8);
        rnd[1] = U8((self.len() >> 8) as u8);
        rnd[2] = U8((self.len() >> 16) as u8);
        rnd[2] = U8((self.len() >> 24) as u8);
        *self = self.push(&Entry::Fresh{rnd:rnd.clone()});
        rnd
    }

    fn trigger_event(&mut self,a:principal,ev:ProtocolEvent) {
        *self = self.push(&Entry::Event{a,ev});
    }

    fn new_session(&mut self,a:principal,st:SessionState) -> usize{
        let sid = self.len();
        *self = self.push(&Entry::Session{a,sid,st});
        sid
    }

    fn read_session(&mut self,a:principal,sid:Self::session_id) -> Option<SessionState> {
        let mut st = None;
        for i in 0..self.len() {
            let j = self.len() - 1 - i;
            match &self[j] {
                Entry::Session{a:p,sid:psid,st:pst} =>
                    if a.declassify_eq(&p) && sid == *psid {
                    st = Some(*pst);
                    },
                _ => {}
            }
        }
        st
    }

    fn update_session(&mut self,a:principal,sid:Self::session_id,st:SessionState) {
        *self = self.push(&Entry::Session{a,sid,st}); 
    }

    fn send(&mut self,a:principal,b:principal,m:bytes) -> usize{
        let msgid = self.len();
        *self = self.push(&Entry::Message{a,b,m});
        msgid
    }

    fn receive(&mut self,a:principal,msgid:Self::message_id) -> Option<(principal,bytes)> {
        if msgid >= self.len() {None}
        else {
            match &self[msgid] {
                Entry::Message{a:p,b:q,m:msg} => {
                    if a.declassify_eq(&q) {
                        Some ((a,msg.clone()))
                    }
                    else {None}
                },
                _ => None
        }}
    }

    fn pke_encrypt(&mut self,pk_b:pubkey,m:ProtocolMessage) -> bytes {
        Seq::new(32+16)
    }
}