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