// This is where the PKI stuff should go
use hacspec_lib::*;
use runtime::types::*;
use runtime::env::*;
use crate::*;

// Would be nice to separate out the PKI state over here

pub fn get_public_key(a:Principal, b:Principal, env:Env) -> EnvResult<Pubkey> {
    let filter = |st:&Bytes| (
      match SessionState::decode(st.clone()) {
          Ok(SessionState::PublicKey {b:bb,pk_b:_}) => 
               if b.eq(&bb) {true} else {false},
          _ => false, 
      } 
    );
    let (st,env) = find_session(a,filter,env)?;
    match SessionState::decode(st)? {
      SessionState::PublicKey {b:_,pk_b} => Ok ((pk_b,env)),
      _ => Err(Error::SessionNotFound),
    }
  }

pub fn get_private_key(a:Principal, env:Env) -> EnvResult<Privkey> {
    let filter = |st:&Bytes| (
      match SessionState::decode(st.clone()) {
          Ok(SessionState::PrivateKey {sk_my:_}) => true,
          _ => false, 
      } 
    );
    let (st,env) = find_session(a,filter,env)?;
    match SessionState::decode(st)? {
      SessionState::PrivateKey {sk_my} => Ok ((sk_my,env)),
      _ => Err(Error::SessionNotFound),
    } 
}
