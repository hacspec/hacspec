// Import hacspec and all needed definitions.
use hacspec_lib::*;

use crate::*;


/*
noeq type message =
  | Msg1: n_a: bytes -> a:string -> message
  | Msg2: n_a: bytes -> n_b:bytes -> b:string -> message
  | Msg3: n_b: bytes -> a:string -> message
*/

#[derive(Clone,Copy)]
pub enum ProtocolMessage{
     Msg1 { n_a: nonce, a: principal },
     Msg2 { n_a: nonce, n_b:nonce, b: principal },
     Msg3 { n_b: nonce, a: principal },
}

/*
noeq type session_st =
  |InitiatorSentMsg1: b:principal -> n_a:bytes -> session_st
  |ResponderSentMsg2: a:principal -> n_a:bytes -> n_b:bytes -> session_st
  |InitiatorSentMsg3: b:principal -> n_a:bytes -> n_b:bytes -> session_st
  |ResponderReceivedMsg3: a:principal -> n_b:bytes -> session_st
   */
  #[derive(Clone,Copy)]
  pub enum SessionState{
  PrivateKey {sk_my:privkey},
  PublicKey {b:principal, pk_b:pubkey},
  InitiatorSentMsg1 { b: principal, n_a: nonce },
  ResponderSentMsg2 { a: principal, n_a: nonce, n_b: nonce},
  InitiatorSentMsg3 { b: principal, n_a: nonce, n_b: nonce },
  ResponderReceivedMsg3 {a: principal, n_b: nonce}
}

/*
let initiate (a:principal) (b:principal) (n_a:bytes) : event =
  ("Initiate",[(string_to_bytes a);(string_to_bytes b);n_a])
let respond (a:principal) (b:principal) (n_a:bytes) (n_b:bytes) : event =
  ("Respond",[(string_to_bytes a);(string_to_bytes b);n_a;n_b])
let finishI (a:principal) (b:principal) (n_a:bytes) (n_b:bytes) : event =
  ("FinishI",[(string_to_bytes a);(string_to_bytes b);n_a;n_b])
let finishR (a:principal) (b:principal) (n_a:bytes) (n_b:bytes) : event =
  ("FinishR",[(string_to_bytes a);(string_to_bytes b);n_a;n_b])
   */
  #[derive(Clone,Copy)]
  pub enum ProtocolEvent {
  Initiate {a:principal, b:principal, n_a:nonce},
  Respond {a:principal, b:principal, n_a:nonce, n_b:nonce},
  InitiatorFinished {a:principal, b:principal, n_a:nonce, n_b:nonce},
  ResponderFinished {a:principal, b:principal, n_a:nonce, n_b:nonce},
}


/*
let initiator_send_msg_1 a b =
  let si = new_session_number #nsl a in
  let (|t0, n_a|) = rand_gen #nsl (readers [P a; P b]) (nonce_usage "NSL.nonce") in
  let ev = initiate a b n_a in 
  trigger_event #nsl a ev;
  let t1 = global_timestamp () in
  let new_ss_st = InitiatorSentMsg1 b n_a in
  let new_ss = serialize_valid_session_st t1 a si 0 new_ss_st in 
  new_session #nsl #t1 a si 0 new_ss;
  let t2 = global_timestamp () in
  let m = Msg1 n_a a in
  let l = readers [P a; P b] in
  let msg1' : msg t2 l = serialize_valid_message t2 m l in
  let msg1'' = restrict msg1' (readers [P b]) in
  let msg1''' = restrict msg1' (readers [P a]) in
  assert (get_label nsl_key_usages msg1''' == get_label nsl_key_usages msg1');
  let pkb = get_public_key #nsl #t2 a b PKE "NSL.key" in 
  sk_label_lemma nsl_global_usage t2 pkb (readers [P b]);
  let (|t3,n_pke|) = rand_gen #nsl (readers [P a]) (nonce_usage "PKE_NONCE") in
  let c_msg1 = pke_enc #nsl_global_usage #t3 #(readers [P a]) pkb n_pke msg1'' in
  let now = send #nsl #t3 a b c_msg1 in
  (si, now)
   */

pub fn get_public_key<T:Trace>(a:principal, b:principal, pk_b_sid: T::session_id, tr:&mut T) -> Option<pubkey> {
  match tr.read_session(a,pk_b_sid)? {
    SessionState::PublicKey {b:bb,pk_b} => 
      if b.declassify_eq(&bb) {Some (pk_b)} else {None},
    _ => None,
  }
}

pub fn initiator_send_msg_1<T:Trace>(a:principal, b:principal, pk_b_sid:T::session_id, mut tr:T) -> Option<(T::session_id,T::message_id)> {
  let rnd = tr.rand_gen(32);
  let n_a = nonce::from_seq(&rnd);
  tr.trigger_event(a, ProtocolEvent::Initiate {a,b,n_a});
  let sid = tr.new_session(a,SessionState::InitiatorSentMsg1 {b,n_a});
  let msg1 = ProtocolMessage::Msg1 {a,n_a};
  let pk_b = get_public_key(a, b, pk_b_sid, &mut tr)?;
  let c_msg1 = tr.pke_encrypt(pk_b, msg1);
  let msg_id = tr.send(a,b,c_msg1);
  Some((sid,msg_id))
} 

