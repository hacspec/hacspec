(** This file was automatically generated using Hacspec **)
Set Warnings "-notation-overridden,-ambiguous-paths".
Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
Require Import Hacspec_Lib.

Require Import Strobe.

Notation "'transcript_t'" := (strobe_t) : hacspec_scope.

Definition merlin_protocol_label  : seq uint8 :=
  [
    secret (@repr WORDSIZE8 77) : int8;
    secret (@repr WORDSIZE8 101) : int8;
    secret (@repr WORDSIZE8 114) : int8;
    secret (@repr WORDSIZE8 108) : int8;
    secret (@repr WORDSIZE8 105) : int8;
    secret (@repr WORDSIZE8 110) : int8;
    secret (@repr WORDSIZE8 32) : int8;
    secret (@repr WORDSIZE8 118) : int8;
    secret (@repr WORDSIZE8 49) : int8;
    secret (@repr WORDSIZE8 46) : int8;
    secret (@repr WORDSIZE8 48) : int8
  ].

Definition new_ (label_1037 : seq uint8) : transcript_t :=
  let transcript_1038 : (state_uint8_t × int8 × int8 × int8) :=
    new_strobe (merlin_protocol_label ) in 
  let dom_sep_1039 : seq uint8 :=
    [
      secret (@repr WORDSIZE8 100) : int8;
      secret (@repr WORDSIZE8 111) : int8;
      secret (@repr WORDSIZE8 109) : int8;
      secret (@repr WORDSIZE8 45) : int8;
      secret (@repr WORDSIZE8 115) : int8;
      secret (@repr WORDSIZE8 101) : int8;
      secret (@repr WORDSIZE8 112) : int8
    ] in 
  append_message (transcript_1038) (dom_sep_1039) (label_1037).

Definition append_message
  (transcript_1040 : transcript_t)
  (label_1041 : seq uint8)
  (message_1042 : seq uint8)
  : transcript_t :=
  let data_len_1043 : seq uint8 :=
    array_to_be_bytes (uint32_to_le_bytes (uint32_classify (pub_u32 (seq_len (
              message_1042))))) in 
  let transcript_1040 :=
    meta_ad (transcript_1040) (label_1041) (false) in 
  let transcript_1040 :=
    meta_ad (transcript_1040) (data_len_1043) (true) in 
  let transcript_1040 :=
    ad (transcript_1040) (message_1042) (false) in 
  transcript_1040.

