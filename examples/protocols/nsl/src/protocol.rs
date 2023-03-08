// Import hacspec and all needed definitions.
use hacspec_lib::*;

use crate::*;


/*
noeq type message =
  | Msg1: n_a: Bytes -> a:string -> message
  | Msg2: n_a: Bytes -> n_b:Bytes -> b:string -> message
  | Msg3: n_b: Bytes -> a:string -> message
*/

#[derive(Clone,Copy)]
pub enum ProtocolMessage{
     Msg1 { n_a: Nonce, a: Principal },
     Msg2 { n_a: Nonce, n_b:Nonce, b: Principal },
     Msg3 { n_b: Nonce, a: Principal },
}

// I would like to derive the following from a macro without writing it out
impl Codec for ProtocolMessage {
    fn encode(self) -> Bytes {
        match self {
            ProtocolMessage::Msg1 {n_a,a} => n_a.concat(&a).push(&U8(0)),
            ProtocolMessage::Msg2 {n_a,n_b,b} => n_a.concat(&n_b).concat(&b).push(&U8(1)),
            ProtocolMessage::Msg3 {n_b,a} => n_b.concat(&a).push(&U8(2)),
        }     
    }
    fn decode(b:Bytes) -> Option<ProtocolMessage> {
        if b.len() < 1 {None}
        else
         {if b[b.len()-1].declassify() == 0 && b.len() == 65 {
            Some(ProtocolMessage::Msg1{n_a:Nonce::from_slice(&b,0,32),a:Principal::from_slice(&b,32,32)})}
          else {if b[b.len()-1].declassify() == 1 && b.len() == 97 {
                    Some(ProtocolMessage::Msg2{n_a:Nonce::from_slice(&b,0,32),n_b:Nonce::from_slice(&b,32,32),b:Principal::from_slice(&b,64,32)})}
                else {if b[b.len()-1].declassify() == 2 && b.len() == 65 {
                            Some(ProtocolMessage::Msg3{n_b:Nonce::from_slice(&b,0,32),a:Principal::from_slice(&b,32,32)})}
                      else {None}}}}
    }
}

/*
noeq type session_st =
  |InitiatorSentMsg1: b:Principal -> n_a:Bytes -> session_st
  |ResponderSentMsg2: a:Principal -> n_a:Bytes -> n_b:Bytes -> session_st
  |InitiatorSentMsg3: b:Principal -> n_a:Bytes -> n_b:Bytes -> session_st
  |ResponderReceivedMsg3: a:Principal -> n_b:Bytes -> session_st
   */
  #[derive(Clone,Copy)]
  pub enum SessionState{
    PrivateKey {sk_my:Privkey},
    PublicKey {b:Principal, pk_b:Pubkey},
    InitiatorSentMsg1 { b: Principal, n_a: Nonce },
    ResponderSentMsg2 { a: Principal, n_a: Nonce, n_b: Nonce},
    InitiatorSentMsg3 { b: Principal, n_a: Nonce, n_b: Nonce },
    ResponderReceivedMsg3 {a: Principal, n_b: Nonce}
}

// I would like to derive the following from a macro without writing it out
impl Codec for SessionState {
    fn encode(self) -> Bytes {
        Seq::new(32)
    }
    fn decode(b:Bytes) -> Option<SessionState> {
        None
    }
}
/*
let initiate (a:Principal) (b:Principal) (n_a:Bytes) : event =
  ("Initiate",[(string_to_Bytes a);(string_to_Bytes b);n_a])
let respond (a:Principal) (b:Principal) (n_a:Bytes) (n_b:Bytes) : event =
  ("Respond",[(string_to_Bytes a);(string_to_Bytes b);n_a;n_b])
let finishI (a:Principal) (b:Principal) (n_a:Bytes) (n_b:Bytes) : event =
  ("FinishI",[(string_to_Bytes a);(string_to_Bytes b);n_a;n_b])
let finishR (a:Principal) (b:Principal) (n_a:Bytes) (n_b:Bytes) : event =
  ("FinishR",[(string_to_Bytes a);(string_to_Bytes b);n_a;n_b])
   */
  #[derive(Clone,Copy)]
  pub enum ProtocolEvent {
    Initiate {a:Principal, b:Principal, n_a:Nonce},
    Respond {a:Principal, b:Principal, n_a:Nonce, n_b:Nonce},
    InitiatorFinished {a:Principal, b:Principal, n_a:Nonce, n_b:Nonce},
    ResponderFinished {a:Principal, b:Principal, n_a:Nonce, n_b:Nonce},
    }

// I would like to derive the following from a macro without writing it out
impl Codec for ProtocolEvent {
    fn encode(self) -> Bytes {
        Seq::new(32)
    }
    fn decode(b:Bytes) -> Option<ProtocolEvent> {
        None
    }
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

