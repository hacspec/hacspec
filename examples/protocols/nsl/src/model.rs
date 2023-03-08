use hacspec_lib::*;
pub type bytes = ByteSeq;
use crate::*;


bytes!(nonce,32);
bytes!(principal,32);
bytes!(privkey,32);
bytes!(pubkey,32);
pub trait Trace: Sized {
  type session_id;
  type message_id;
  fn rand_gen(&mut self,len:usize) -> bytes;
  fn trigger_event(&mut self,a:principal,ev:ProtocolEvent);
  fn new_session(&mut self,a:principal,s:SessionState) -> Self::session_id;
  fn read_session(&mut self,a:principal,sid:Self::session_id) -> Option<SessionState>;
  fn update_session(&mut self,a:principal,sid:Self::session_id,s:SessionState);
  fn send(&mut self,a:principal,b:principal,m:bytes) -> Self::message_id;
  fn receive(&mut self,a:principal,msgid:Self::message_id) -> Option<(principal,bytes)>;
  fn pke_encrypt(&mut self,pk_b:pubkey,m:ProtocolMessage) -> bytes;
}
