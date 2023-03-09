use hacspec_lib::*;


bytes!(Nonce,32);
bytes!(Principal,32);
bytes!(Privkey,32);
bytes!(Pubkey,32);

pub trait Env: Sized {
  type SessionId: Copy+Clone;
  type MessageId: Copy+Clone;
  fn rand_gen(len:usize,env:&mut Self) -> Bytes;
  fn trigger_event(a:Principal,ev:Bytes,env:&mut Self);
  fn new_session(a:Principal,s:Bytes,env:&mut Self) -> Self::SessionId;
  fn read_session(a:Principal,sid:Self::SessionId,env:&mut Self) -> Option<Bytes>;
  fn find_session<F>(a:Principal,filter:F,env:&mut Self) -> Option<Bytes>
                 where F: Fn (Bytes) -> bool;
  fn update_session(a:Principal,sid:Self::SessionId,s:Bytes,env:&mut Self);
  fn send(a:Principal,b:Principal,m:Bytes,env:&mut Self) -> Self::MessageId;
  fn receive(a:Principal,msgid:Self::MessageId,env:&mut Self) -> Option<(Principal,Bytes)>;
  fn pke_encrypt(pk_b:Pubkey,m:Bytes,env:&mut Self) -> Bytes;
  fn pke_decrypt(sk_b:Privkey,m:Bytes,env:&mut Self) -> Option<Bytes>;
}

pub trait Codec : Sized{
    fn encode(self) -> Bytes;
    fn decode(b:Bytes) -> Option<Self>;
  }

pub trait Protocol {
    type Config: Copy+Clone+Codec;
    type Command: Copy+Clone+Codec;
    type Message: Copy+Clone+Codec;
    type Session: Copy+Clone+Codec;
    type Env;
    fn init(cfg:Self::Config, env:&mut Self::Env) -> Self::Session;
    fn process_cmd(st:Self::Session, in_cmd:Self::Command, env:&mut Self::Env) 
        -> Result<Option<Self::Message>,usize>;
    fn process_msg(st:Self::Session, in_msg:Self::Message, env:&mut Self::Env) 
        -> Result<Option<Self::Message>,usize>;
}
