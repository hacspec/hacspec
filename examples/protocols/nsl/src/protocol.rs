// Import hacspec and all needed definitions.
use hacspec_lib::*;
use codec::*;

use crate::*;


#[derive(Clone,Copy,Codec)]
pub enum ProtocolMessage{
     Msg1 { n_a: Nonce, a: Principal },
     Msg2 { n_a: Nonce, n_b:Nonce, b: Principal },
     Msg3 { n_b: Nonce, a: Principal },
}

#[derive(Clone,Copy,Codec)]
pub enum SessionState{
    PrivateKey {sk_my:Privkey},
    PublicKey {b:Principal, pk_b:Pubkey},
    InitiatorSentMsg1 { b: Principal, n_a: Nonce },
    ResponderSentMsg2 { a: Principal, n_a: Nonce, n_b: Nonce},
    InitiatorSentMsg3 { b: Principal, n_a: Nonce, n_b: Nonce },
    ResponderReceivedMsg3 {a: Principal, n_b: Nonce}
}


#[derive(Clone,Copy,Codec)]
pub enum ProtocolEvent {
    Initiate {a:Principal, b:Principal, n_a:Nonce},
    Respond {a:Principal, b:Principal, n_a:Nonce, n_b:Nonce},
    InitiatorFinished {a:Principal, b:Principal, n_a:Nonce, n_b:Nonce},
    ResponderFinished {a:Principal, b:Principal, n_a:Nonce, n_b:Nonce},
    }



pub fn get_public_key<T:Trace>(a:Principal, b:Principal, pk_b_sid: T::SessionId, tr:&mut T) -> Option<Pubkey> {
  match SessionState::decode(tr.read_session(a,pk_b_sid)?)? {
    SessionState::PublicKey {b:bb,pk_b} => 
      if b.declassify_eq(&bb) {Some (pk_b)} else {None},
    _ => None,
  }
}

pub fn initiator_send_msg_1<T:Trace>(a:Principal, b:Principal, pk_b_sid:T::SessionId, mut tr:T) -> Option<(T::SessionId,T::MessageId)> {
  let rnd = tr.rand_gen(32);
  let n_a = Nonce::from_seq(&rnd);
  tr.trigger_event(a, ProtocolEvent::Initiate {a,b,n_a}.encode());
  let sid = tr.new_session(a,SessionState::InitiatorSentMsg1 {b,n_a}.encode()); 
  let pk_b = get_public_key(a, b, pk_b_sid, &mut tr)?;
  let c_msg1 = tr.pke_encrypt(pk_b, ProtocolMessage::Msg1 {a,n_a}.encode());
  let msg_id = tr.send(a,b,c_msg1);
  Some((sid,msg_id))
} 

