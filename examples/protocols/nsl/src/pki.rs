// This is where the PKI stuff should go
use hacspec_lib::*;
use runtime::model::*;
use crate::*;

// Would be nice to separate out the PKI state over here

pub fn get_public_key(a:Principals, b:Principal, env:&mut impl Env) -> Option<Pubkey> {
    let filter = |st| (
      match SessionState::decode(st) {
          Some(SessionState::PublicKey {b:bb,pk_b}) => 
               if b.declassify_eq(&bb) {true} else {false},
          _ => false, 
      } 
    );
    match SessionState::decode(Env::find_session(a,filter,env)?)? {
      SessionState::PublicKey {b:bb,pk_b} => Some (pk_b),
      _ => None,
    }
  }

pub fn get_private_key(a:Principal, env:&mut impl Env) -> Option<Privkey> {
    let filter = |st| (
      match SessionState::decode(st) {
          Some(SessionState::PrivateKey {sk_my}) => true,
          _ => false, 
      } 
    );
    match SessionState::decode(Env::find_session(a,filter,env)?)? {
      SessionState::PrivateKey {sk_my} => Some (sk_my),
      _ => None,
    }
  }
  