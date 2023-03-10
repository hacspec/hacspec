// Import hacspec and all needed definitions.
use hacspec_lib::*;
use runtime::types::*;
use runtime::env::*;
use runtime::crypto::*;
use codec::*;
use crate::*;


#[derive(Clone,Copy,Codec)]
pub enum ProtocolMessage{
     Msg1 { n_a: Nonce, a: Principal },
     Msg2 { n_a: Nonce, n_b:Nonce, b: Principal },
     Msg3 { n_b: Nonce },
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

pub fn init_initiator(a:Principal, b:Principal, env:&mut Env) 
    -> Option<SessionId> {
  let sid = new_session(a, SessionState::InitiatorInit {b}.encode(), env); 
  Some(sid)
} 

pub fn init_responderr(b:Principal, env:&mut Env) 
    -> Option<SessionId> {
  let sid = new_session(b, SessionState::ResponderInit.encode(),env); 
  Some(sid)
} 

pub fn initiator_send_msg_1(a:Principal, sid:SessionId,  env:&mut Env) 
    -> Option<MessageId> {
  if let SessionState::InitiatorInit { b } = SessionState::decode(read_session(a, sid, env)?)? {
    let n_a = Nonce::from_seq(&rand_gen(32,env));
    trigger_event(a, ProtocolEvent::Initiate {a,b,n_a}.encode(),env);
    update_session(a, sid, SessionState::InitiatorSentMsg1 {b,n_a}.encode(),env); 
    let pk_b = get_public_key(a, b, env)?;
    let c_msg1 = pke_encrypt(pk_b, ProtocolMessage::Msg1 {n_a,a}.encode(),env);
    let msg_id = send(a,b,c_msg1,env);
    Some(msg_id)
  } else {None}
} 

pub fn responder_send_msg_2(b: Principal, sid: SessionId, msgid: MessageId,  env:&mut Env)
    -> Option<MessageId> {
    if let SessionState::ResponderInit = SessionState::decode(read_session(b, sid,env)?)? {
       let sk_b = get_private_key(b, env)?;
       let (_a,msg) = receive(b, msgid, env)?;
       if let ProtocolMessage::Msg1 {n_a,a} = ProtocolMessage::decode(pke_decrypt(sk_b,msg,env)?)? {
        let n_b = Nonce::from_seq(&rand_gen(32,env));
        trigger_event(a, ProtocolEvent::Respond {a,b,n_a,n_b}.encode(),env);
        update_session(a, sid, SessionState::ResponderSentMsg2 {a,n_a,n_b}.encode(),env); 
        let pk_b = get_public_key(b, a, env)?;
        let c_msg1 = pke_encrypt(pk_b, ProtocolMessage::Msg2 {n_a,n_b,b}.encode(),env);
        let msg_id = send(a,b,c_msg1,env);
        Some(msg_id)
       } else {None}
    } else {None}
}

pub fn initiator_send_msg_3(a:Principal, sid:SessionId, msgid:MessageId, env:&mut Env) 
    -> Option<MessageId> {
  if let SessionState::InitiatorSentMsg1 { b,n_a } = SessionState::decode(read_session(a, sid, env)?)? {
    let sk_a = get_private_key(a, env)?;
    let (_b,msg) = receive(b, msgid, env)?;
    if let ProtocolMessage::Msg2 {n_a:recv_n_a,n_b,b:recv_b} = ProtocolMessage::decode(pke_decrypt(sk_a,msg,env)?)? {
       if b.eq(&recv_b) && n_a.eq(&recv_n_a) {
         trigger_event(a, ProtocolEvent::InitiatorFinished {a,b,n_a,n_b}.encode(),env);
         update_session(a, sid, SessionState::InitiatorSentMsg3 {b,n_a,n_b}.encode(),env); 
        let pk_b = get_public_key(a, b, env)?;
        let c_msg3 = pke_encrypt(pk_b, ProtocolMessage::Msg3 {n_b}.encode(),env);
        let msg_id = send(a,b,c_msg3,env);
        Some(msg_id)
       } else {None}
    } else {None}
  } else {None}
} 


pub fn responder_receive_msg3(b: Principal, sid: SessionId, msgid: MessageId,  env:&mut Env)
    -> Option<()> {
    if let SessionState::ResponderSentMsg2 { a, n_a, n_b } = SessionState::decode(read_session(b, sid,env)?)? {
       let sk_b = get_private_key(b, env)?;
       let (_a,msg) = receive(b, msgid, env)?;
       if let ProtocolMessage::Msg3 {n_b:recv_n_b} = ProtocolMessage::decode(pke_decrypt(sk_b,msg,env)?)? {
        if n_b.eq(&recv_n_b) {
            trigger_event(a, ProtocolEvent::ResponderFinished {a,b,n_a,n_b}.encode(),env);
            update_session(a, sid, SessionState::ResponderReceivedMsg3 {a,n_b}.encode(),env); 
            Some(())
        } else {None}
       } else {None}
    } else {None}
}