(** This file was automatically generated using Hacspec **)
Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
Require Import Hacspec_Lib.

Definition block_t := nseq (uint32) (usize 8).

Definition shuffle (b_0 : block_t) : block_t :=
  let b_1 : block_t :=
    b_0 in 
  let tmp_2 : uint32 :=
    array_index (b_1) (usize 0) in 
  let b_1 :=
    array_upd b_1 (usize 0) (array_index (b_1) (usize 1)) in 
  let b_1 :=
    array_upd b_1 (usize 1) (tmp_2) in 
  b_1.

Definition linear_manipulations (a_3 : seq int8) : seq int8 :=
  let b_4 : seq int8 :=
    (if (true):bool then (a_3) else (a_3)) in 
  let c_5 : seq int8 :=
    (b_4) in 
  let '(c_5) :=
    if false:bool then (let c_5 :=
        seq_update_start (c_5) (b_4) in 
      (c_5)) else (let c_5 :=
        b_4 in 
      (c_5)) in 
  c_5.

Definition creating_public_byte_seq  : seq int8 :=
  [@repr WORDSIZE8 0; @repr WORDSIZE8 1; @repr WORDSIZE8 2; @repr WORDSIZE8 3].

Definition creating_byte_seq  : seq uint8 :=
  [
    secret (@repr WORDSIZE8 0) : int8;
    secret (@repr WORDSIZE8 1) : int8;
    secret (@repr WORDSIZE8 2) : int8;
    secret (@repr WORDSIZE8 3) : int8
  ].

