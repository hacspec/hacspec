use crate::cryptolib::*;
use crate::formats::*;

// Import hacspec and all needed definitions.
use hacspec_lib::*;

pub struct Transcript_Msg1(pub HashAlgorithm, pub Bytes);
pub struct Transcript_TH_2(pub HashAlgorithm, pub Bytes, pub HASH);
pub struct Transcript_TH_3(pub HashAlgorithm, pub Bytes, pub HASH);
pub struct Transcript_TH_4(pub HashAlgorithm, pub Bytes, pub HASH);

pub struct InitiatorPostMsg1(pub CONNID, pub ALGS, pub KEMSK, pub KEMPK, Transcript_Msg1); //May need Responder Identifier
pub struct ResponderPostMsg2(pub CONNID, pub CONNID, pub ALGS, pub KEMPK, pub KEMPK, pub KEY, Transcript_TH_2); 
pub struct InitiatorPostMsg3(pub CONNID, pub CONNID, pub ALGS, pub KEMPK, pub KEMPK); 
pub struct ResponderPostMsg3(pub CONNID, pub CONNID, pub ALGS, pub KEMPK, pub KEMPK);

pub fn get_msg1(algs:ALGS, entropy:Bytes32) -> Res<(Bytes , InitiatorPostMsg1)> {

    Err(parse_failed)
}

pub fn put_msg1(algs:ALGS, skR:SIGK, msg1:&Bytes, entropy:Bytes32) -> Res<(Bytes , ResponderPostMsg2)> {

    Err(parse_failed)
}

pub fn put_msg2(st:InitiatorPostMsg1, skI:SIGK, vkR:VERK, msg2:&Bytes) -> Res<(Bytes , InitiatorPostMsg3)> {

    Err(parse_failed)
}

pub fn put_msg3(st:ResponderPostMsg2, vkI:VERK, msg3:&Bytes) -> Res<(Bytes , ResponderPostMsg3)> {

    Err(parse_failed)
}
