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

pub fn init_initiator(a: Principal, b: Principal, env: Env) -> EnvResult<SessionId> {
    new_session(a, SessionState::InitiatorInit { b }.encode(), env)
}

pub fn init_responder(b: Principal, env: Env) -> EnvResult<SessionId> {
    new_session(b, SessionState::ResponderInit.encode(), env)
}

pub fn initiator_send_msg_1(a: Principal, sid: SessionId, env: Env) -> EnvResult<MessageId> {
    let (st,env) = read_session(a, sid, env)?;
    if let SessionState::InitiatorInit { b } = SessionState::decode(st)? {
        let (n_a,env) = rand_gen(32, env)?;
        let n_a = Nonce::from_seq(&n_a);
        let ((),env) = trigger_event(a, ProtocolEvent::Initiate { a, b, n_a }.encode(), env)?;
        let st = SessionState::InitiatorSentMsg1 { b, n_a }.encode();
        let ((),env) = update_session(a, sid, st, env)?;
        let (pk_b,env) = get_public_key(a, b, env)?;
        let (c_msg1,env) = pke_encrypt(pk_b, ProtocolMessage::Msg1 { n_a, a }.encode(), env)?;
        let (msg_id,env) = send(a, b, c_msg1, env)?;
        Ok((msg_id,env))
    } else {
        Err(Error::IncorrectState)
    }
}

pub fn responder_send_msg_2(
    b: Principal,
    sid: SessionId,
    msgid: MessageId,
    env: Env,
) -> EnvResult<MessageId> {
    let (st,env) = read_session(b, sid, env)?;
    if let SessionState::ResponderInit = SessionState::decode(st)? {
        let (sk_b,env) = get_private_key(b, env)?;
        let ((_a, msg),env) = receive(b, msgid, env)?;
        let (plaintext,env) = pke_decrypt(sk_b, msg, env)?;
        if let ProtocolMessage::Msg1 { n_a, a } =
            ProtocolMessage::decode(plaintext)?
        {
            let (n_b,env) = rand_gen(32, env)?;
            let n_b = Nonce::from_seq(&n_b);
            let ((),env) = trigger_event(a, ProtocolEvent::Respond { a, b, n_a, n_b }.encode(), env)?;
            let st = SessionState::ResponderSentMsg2 { a, n_a, n_b }.encode();
            let ((),env) = update_session(a, sid, st, env)?;
            let (pk_b,env) = get_public_key(b, a, env)?;
            let (c_msg1,env) = pke_encrypt(pk_b, ProtocolMessage::Msg2 { n_a, n_b, b }.encode(), env)?;
            let (msg_id,env) = send(a, b, c_msg1, env)?;
            Ok((msg_id,env))
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
    env: Env,
) -> EnvResult<MessageId> {
    let (st,env) = read_session(a, sid, env)?;
    if let SessionState::InitiatorSentMsg1 { b, n_a } =
        SessionState::decode(st)?
    {
        let (sk_a,env) = get_private_key(a, env)?;
        let ((_b, msg),env) = receive(b, msgid, env)?;
        let (plaintext,env) = pke_decrypt(sk_a, msg, env)?;
        if let ProtocolMessage::Msg2 {
            n_a: recv_n_a,
            n_b,
            b: recv_b,
        } = ProtocolMessage::decode(plaintext)?
        {
            if b.eq(&recv_b) && n_a.eq(&recv_n_a) {
                let ev = ProtocolEvent::InitiatorFinished { a, b, n_a, n_b }.encode();
                let ((),env) = trigger_event(a, ev, env)?;
                let st = SessionState::InitiatorSentMsg3 { b, n_a, n_b }.encode();
                let ((),env) = update_session(a, sid, st, env)?;
                let (pk_b,env) = get_public_key(a, b, env)?;
                let (c_msg3,env) = pke_encrypt(pk_b, ProtocolMessage::Msg3 { n_b }.encode(), env)?;
                let (msg_id,env) = send(a, b, c_msg3, env)?;
                Ok((msg_id,env))
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
    env: Env,
) -> EnvResult<()> {
    let (st,env) = read_session(b, sid, env)?;
    if let SessionState::ResponderSentMsg2 { a, n_a, n_b } =
        SessionState::decode(st)?
    {
        let (sk_b,env) = get_private_key(b, env)?;
        let ((_a, msg),env) = receive(b, msgid, env)?;
        let (plaintext,env) = pke_decrypt(sk_b, msg, env)?;
        if let ProtocolMessage::Msg3 { n_b: recv_n_b } =
            ProtocolMessage::decode(plaintext)?
        {
            if n_b.eq(&recv_n_b) {
                let ev = ProtocolEvent::ResponderFinished { a, b, n_a, n_b }.encode();
                let ((),env) = trigger_event(a, ev, env)?;
                let st = SessionState::ResponderReceivedMsg3 { a, n_b }.encode();
                let ((),env) = update_session(a, sid, st, env)?;
                Ok(((),env))
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
