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
    PublicKey {b: Principal, pk_b:Pubkey},
    InitiatorInit{b: Principal},
    ResponderInit,
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

pub fn init_initiator<E:Env>(a:Principal, b:Principal, env:&mut E) 
    -> Option<E::SessionId> {
  let sid = E::new_session(a, SessionState::InitiatorInit {b}.encode(), env); 
  Some(sid)
} 

pub fn init_responderr<E:Env>(b:Principal, env:&mut E) 
    -> Option<E::SessionId> {
  let sid = E::new_session(b, SessionState::ResponderInit.encode(),env); 
  Some(sid)
} 

pub fn initiator_send_msg_1<E:Env>(a:Principal, sid:E::SessionId,  env:&mut E) 
    -> Option<E::MessageId> {
  if let SessionState::InitiatorInit { b } = SessionState::decode(E::read_session(a, sid, env)?)? {
    let n_a = Nonce::from_seq(&E::rand_gen(32,env));
    E::trigger_event(a, ProtocolEvent::Initiate {a,b,n_a}.encode(),env);
    E::update_session(a, sid, SessionState::InitiatorSentMsg1 {b,n_a}.encode(),env); 
    let pk_b = get_public_key(a, b, env)?;
    let c_msg1 = E::pke_encrypt(pk_b, ProtocolMessage::Msg1 {n_a,a}.encode(),env);
    let msg_id = E::send(a,b,c_msg1,env);
    Some(msg_id)
  } else {None}
} 

pub fn responder_send_msg_2<E:Env>(b: Principal, sid: E::SessionId, msgid: E::MessageId,  env:&mut E)
    -> Option<E::MessageId> {
    if let SessionState::ResponderInit = SessionState::decode(E::read_session(b, sid,env)?)? {
       let sk_b = get_private_key(b, env)?;
       let (a,msg) = E::receive(b, msgid, env)?;
       if let ProtocolMessage::Msg1 {n_a,a} = ProtocolMessage::decode(E::pke_decrypt(sk_b,msg,env)?)? {
        let n_b = Nonce::from_seq(&E::rand_gen(32,env));
        E::trigger_event(a, ProtocolEvent::Respond {a,b,n_a,n_b}.encode(),env);
        E::update_session(a, sid, SessionState::ResponderSentMsg2 {a,n_a,n_b}.encode(),env); 
        let pk_b = get_public_key(b, a, env)?;
        let c_msg1 = E::pke_encrypt(pk_b, ProtocolMessage::Msg2 {n_a,n_b,b}.encode(),env);
        let msg_id = E::send(a,b,c_msg1,env);
        Some(msg_id)
       } else {None}
    } else {None}
}


/* 
let responder_send_msg_2 b msg_idx =
  let (|now,_,c_msg1|) = receive_i #nsl msg_idx b in
  let (|_, skb|) = get_private_key #nsl #now b PKE "NSL.key" in
  let (a, n_a) = responder_receive_msg_1_helper #now b c_msg1 skb in
  let pka = get_public_key #nsl #now b a PKE "NSL.key" in
  let (|t0, n_b|) = rand_gen #nsl (readers [P a; P b]) (nonce_usage "NSL.nonce") in
  let ev = respond a b n_a n_b in
  trigger_event #nsl b ev;
  let t1 = global_timestamp () in
  let si = new_session_number #nsl b in
  let new_ss_st = ResponderSentMsg2 a n_a n_b in
  let new_ss = serialize_valid_session_st t1 b si 0 new_ss_st in
  new_session #nsl #t1 b si 0 new_ss;
  let (|t2,n_pke|) = rand_gen #nsl (readers [P b]) (nonce_usage "PKE_NONCE") in
  let c_msg2 = responder_send_msg_2_helper #t2 b a pka n_a n_b n_pke in
  let now = send #nsl #t2 b a c_msg2 in
  (si, now)
*/
