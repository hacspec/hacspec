// Import hacspec and all needed definitions.
use crate::*;
use codec::*;
use hacspec_lib::*;
use runtime::crypto::*;
use runtime::env::*;
use runtime::types::*;

#[derive(Clone, Copy, Codec)]
pub enum ProtocolMessage {
    Msg1 {
        n_a: Nonce,
        a: Principal,
    },
    Msg2 {
        n_a: Nonce,
        n_b: Nonce,
        b: Principal,
    },
    Msg3 {
        n_b: Nonce,
    },
}

#[derive(Clone, Copy, Codec)]
pub enum SessionState {
    PrivateKey {
        sk_my: Privkey,
    },
    PublicKey {
        b: Principal,
        pk_b: Pubkey,
    },
    InitiatorInit {
        b: Principal,
    },
    ResponderInit,
    InitiatorSentMsg1 {
        b: Principal,
        n_a: Nonce,
    },
    ResponderSentMsg2 {
        a: Principal,
        n_a: Nonce,
        n_b: Nonce,
    },
    InitiatorSentMsg3 {
        b: Principal,
        n_a: Nonce,
        n_b: Nonce,
    },
    ResponderReceivedMsg3 {
        a: Principal,
        n_b: Nonce,
    },
}

#[derive(Clone, Copy, Codec)]
pub enum ProtocolEvent {
    Initiate {
        a: Principal,
        b: Principal,
        n_a: Nonce,
    },
    Respond {
        a: Principal,
        b: Principal,
        n_a: Nonce,
        n_b: Nonce,
    },
    InitiatorFinished {
        a: Principal,
        b: Principal,
        n_a: Nonce,
        n_b: Nonce,
    },
    ResponderFinished {
        a: Principal,
        b: Principal,
        n_a: Nonce,
        n_b: Nonce,
    },
}

pub fn init_initiator(a: Principal, b: Principal, env: &mut Env) -> Result<SessionId,Error> {
    let sid = new_session(a, SessionState::InitiatorInit { b }.encode(), env);
    Ok(sid)
}

pub fn init_responder(b: Principal, env: &mut Env) -> Result<SessionId,Error> {
    let sid = new_session(b, SessionState::ResponderInit.encode(), env);
    Ok(sid)
}

pub fn initiator_send_msg_1(a: Principal, sid: SessionId, env: &mut Env) -> Result<MessageId,Error> {
    if let SessionState::InitiatorInit { b } = SessionState::decode(read_session(a, sid, env)?)? {
        let n_a = Nonce::from_seq(&rand_gen(32, env));
        trigger_event(a, ProtocolEvent::Initiate { a, b, n_a }.encode(), env);
        let st = SessionState::InitiatorSentMsg1 { b, n_a }.encode();
        update_session(a, sid, st, env)?;
        let pk_b = get_public_key(a, b, env)?;
        let c_msg1 = pke_encrypt(pk_b, ProtocolMessage::Msg1 { n_a, a }.encode(), env);
        let msg_id = send(a, b, c_msg1, env);
        Ok(msg_id)
    } else {
        Err(Error::IncorrectState)
    }
}

pub fn responder_send_msg_2(
    b: Principal,
    sid: SessionId,
    msgid: MessageId,
    env: &mut Env,
) -> Result<MessageId,Error> {
    if let SessionState::ResponderInit = SessionState::decode(read_session(b, sid, env)?)? {
        let sk_b = get_private_key(b, env)?;
        let (_a, msg) = receive(b, msgid, env)?;
        if let ProtocolMessage::Msg1 { n_a, a } =
            ProtocolMessage::decode(pke_decrypt(sk_b, msg, env)?)?
        {
            let n_b = Nonce::from_seq(&rand_gen(32, env));
            trigger_event(a, ProtocolEvent::Respond { a, b, n_a, n_b }.encode(), env);
            let st = SessionState::ResponderSentMsg2 { a, n_a, n_b }.encode();
            update_session(a, sid, st, env)?;
            let pk_b = get_public_key(b, a, env)?;
            let c_msg1 = pke_encrypt(pk_b, ProtocolMessage::Msg2 { n_a, n_b, b }.encode(), env);
            let msg_id = send(a, b, c_msg1, env);
            Ok(msg_id)
        } else {
            Err(Error::IncorrectState)
        }
    } else {
        Err(Error::IncorrectState)
    }
}

pub fn initiator_send_msg_3(
    a: Principal,
    sid: SessionId,
    msgid: MessageId,
    env: &mut Env,
) -> Result<MessageId,Error> {
    if let SessionState::InitiatorSentMsg1 { b, n_a } =
        SessionState::decode(read_session(a, sid, env)?)?
    {
        let sk_a = get_private_key(a, env)?;
        let (_b, msg) = receive(b, msgid, env)?;
        if let ProtocolMessage::Msg2 {
            n_a: recv_n_a,
            n_b,
            b: recv_b,
        } = ProtocolMessage::decode(pke_decrypt(sk_a, msg, env)?)?
        {
            if b.eq(&recv_b) && n_a.eq(&recv_n_a) {
                let ev = ProtocolEvent::InitiatorFinished { a, b, n_a, n_b }.encode();
                trigger_event(a, ev, env);
                let st = SessionState::InitiatorSentMsg3 { b, n_a, n_b }.encode();
                update_session(a, sid, st, env)?;
                let pk_b = get_public_key(a, b, env)?;
                let c_msg3 = pke_encrypt(pk_b, ProtocolMessage::Msg3 { n_b }.encode(), env);
                let msg_id = send(a, b, c_msg3, env);
                Ok(msg_id)
            } else {
                Err(Error::IncorrectState)
            }
        } else {
            Err(Error::IncorrectState)
        }
    } else {
        Err(Error::IncorrectState)
    }
}

pub fn responder_receive_msg3(
    b: Principal,
    sid: SessionId,
    msgid: MessageId,
    env: &mut Env,
) -> Result<(),Error> {
    if let SessionState::ResponderSentMsg2 { a, n_a, n_b } =
        SessionState::decode(read_session(b, sid, env)?)?
    {
        let sk_b = get_private_key(b, env)?;
        let (_a, msg) = receive(b, msgid, env)?;
        if let ProtocolMessage::Msg3 { n_b: recv_n_b } =
            ProtocolMessage::decode(pke_decrypt(sk_b, msg, env)?)?
        {
            if n_b.eq(&recv_n_b) {
                let ev = ProtocolEvent::ResponderFinished { a, b, n_a, n_b }.encode();
                trigger_event(a, ev, env);
                let st = SessionState::ResponderReceivedMsg3 { a, n_b }.encode();
                update_session(a, sid, st, env)?;
                Ok(())
            } else {
                Err(Error::IncorrectState)
            }
        } else {
            Err(Error::IncorrectState)
        }
    } else {
        Err(Error::IncorrectState)
    }
}
