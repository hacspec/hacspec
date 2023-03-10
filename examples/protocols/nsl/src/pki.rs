// This is where the PKI stuff should go
use hacspec_lib::*;
use runtime::types::*;
use runtime::env::*;
use crate::*;

// Would be nice to separate out the PKI state over here

pub fn get_public_key(a:Principal, b:Principal, env:&mut Env) -> Option<Pubkey> {
    let filter = |st:&Bytes| (
      match SessionState::decode(st.clone()) {
          Some(SessionState::PublicKey {b:bb,pk_b:_}) => 
               if b.eq(&bb) {true} else {false},
          _ => false, 
      } 
    );
    match SessionState::decode(find_session(a,filter,env)?)? {
      SessionState::PublicKey {b:_,pk_b} => Some (pk_b),
      _ => None,
    }
  }

pub fn get_private_key(a:Principal, env:&mut Env) -> Option<Privkey> {
    let filter = |st:&Bytes| (
      match SessionState::decode(st.clone()) {
          Some(SessionState::PrivateKey {sk_my:_}) => true,
          _ => false, 
      } 
    );
    match SessionState::decode(find_session(a,filter,env)?)? {
      SessionState::PrivateKey {sk_my} => Some (sk_my),
      _ => None,
    }
  
}