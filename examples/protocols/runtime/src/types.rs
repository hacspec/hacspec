use hacspec_lib::*;

public_bytes!(Principal,32);
pub type Nonce = Bytes;
pub type Pubkey = Bytes;
pub type Privkey = Bytes;

/*
impl PartialEq for Principal {
  fn eq(&self,other:&Self)->bool {
    self.declassify_eq(other)
  }
}
impl Eq for Principal {}
*/

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
