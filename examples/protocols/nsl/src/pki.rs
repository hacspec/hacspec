// This is where the PKI stuff should go
use hacspec_lib::*;
use runtime::types::*;
use runtime::env::*;
use crate::*;

// Would be nice to separate out the PKI state over here

pub fn get_public_key(a:Principal, b:Principal, env:&mut Env) -> Result<Pubkey,Error> {
    let filter = |st:&Bytes| (
      match SessionState::decode(st.clone()) {
          Ok(SessionState::PublicKey {b:bb,pk_b:_}) => 
               if b.eq(&bb) {true} else {false},
          _ => false, 
      } 
    );
    match SessionState::decode(find_session(a,filter,env)?)? {
      SessionState::PublicKey {b:_,pk_b} => Ok (pk_b),
      _ => Err(Error::SessionNotFound),
    }
  }

pub fn get_private_key(a:Principal, env:&mut Env) -> Result<Privkey,Error> {
    let filter = |st:&Bytes| (
      match SessionState::decode(st.clone()) {
          Ok(SessionState::PrivateKey {sk_my:_}) => true,
          _ => false, 
      } 
    );
    match SessionState::decode(find_session(a,filter,env)?)? {
      SessionState::PrivateKey {sk_my} => Ok (sk_my),
      _ => Err(Error::SessionNotFound),
    } 
}