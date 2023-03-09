use hacspec_lib::*;


bytes!(Nonce,32);
bytes!(Principal,32);
bytes!(Privkey,32);
bytes!(Pubkey,32);

pub trait Trace: Sized {
  type SessionId;
  type MessageId;
  fn rand_gen(&mut self,len:usize) -> Bytes;
  fn trigger_event(&mut self,a:Principal,ev:Bytes);
  fn new_session(&mut self,a:Principal,s:Bytes) -> Self::SessionId;
  fn read_session(&mut self,a:Principal,sid:Self::SessionId) -> Option<Bytes>;
  fn update_session(&mut self,a:Principal,sid:Self::SessionId,s:Bytes);
  fn send(&mut self,a:Principal,b:Principal,m:Bytes) -> Self::MessageId;
  fn receive(&mut self,a:Principal,msgid:Self::MessageId) -> Option<(Principal,Bytes)>;
  fn pke_encrypt(&mut self,pk_b:Pubkey,m:Bytes) -> Bytes;
}

pub trait Codec : Sized{
    fn encode(self) -> Bytes;
    fn decode(b:Bytes) -> Option<Self>;
  }
