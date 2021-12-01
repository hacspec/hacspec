(** This file was automatically generated using Hacspec **)
Require Import Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
Require Import Hacspec.Lib.

Definition foo (x_0 : bool) : (result int64 uint8) :=
  (if (x_0):bool then (@Ok int64 uint8 (@repr WORDSIZE64 42)) else (
      @Err int64 uint8 (secret (@repr WORDSIZE8 0)))).

Definition bar  : (result int64 uint8) :=
  bind (foo (false)) (fun x_1 => @Ok int64 uint8 ((x_1) .+ (
        @repr WORDSIZE64 1))).

Definition fizzbaz  : (result int64 uint8) :=
  bind (foo (false)) (fun x_2 => bind (foo (true)) (fun y_3 => @Ok int64 uint8 (
        (x_2) .+ (y_3)))).

Definition fizzbazbaz  : (result int64 uint8) :=
  bind (foo (false)) (fun x_4 => bind (foo (true)) (fun y_5 => let x_4 :=
        (x_4) .+ (y_5) in 
      bind (foo (false)) (fun y_5  => @Ok int64 uint8 ((x_4) .+ (y_5))))).

Definition fizzbazbazbar (s_6 : seq int64) : (result int64 uint8) :=
  bind (foo (false)) (fun y_7 => bind (foo (true)) (fun _temp => let s_6 :=
        seq_upd s_6 (usize 0) _temp in 
      @Ok int64 uint8 ((seq_index (s_6) (usize 0)) .+ (y_7)))).

Definition baz  : (result int32 uint8) :=
  bind (foo (false)) (fun x_8 => let out_9 : int32 :=
      @repr WORDSIZE32 0 in 
    ifbnd (true) || (false) : bool
    thenbnd (bind (foo (true)) (fun y_10 => bind (foo ((false) || (true))) (
          fun _ => Ok ((out_9)))))
    elsebnd(bind (foo ((false) && (true))) (fun _ => let out_9 :=
          (@cast _ uint32 _ (x_8)) .+ (@repr WORDSIZE32 1) in 
        Ok ((out_9)))) >> (fun '(out_9) =>
    @Ok int32 uint8 (out_9))).

Definition fizzbar  : (result int32 uint8) :=
  bind (foo (false)) (fun x_11 => let out_12 : int32 :=
      @repr WORDSIZE32 0 in 
    bind (foldibnd (usize 0) to (usize 200) for out_12>> (fun i_13 out_12 =>
      bind (foo (true)) (fun y_14 => let out_12 :=
          ((pub_u32 (i_13)) .+ (@cast _ uint32 _ (y_14))) .+ (out_12) in 
        Ok ((out_12))))) (fun out_12 => @Ok int32 uint8 (out_12))).

Definition fizzbarbuzz  : (result int32 uint8) :=
  bind (foo (false)) (fun x_15 => let out_16 : int32 :=
      @repr WORDSIZE32 0 in 
    bind (foldibnd (usize 0) to (usize 200) for out_16>> (fun i_17 out_16 =>
      ifbnd (true) || (false) : bool
      thenbnd (bind (foo (true)) (fun y_18 => let out_16 :=
            (@cast _ uint32 _ (y_18)) .+ (out_16) in 
          bind (foo ((false) || (true))) (fun _ => Ok ((out_16)))))
      elsebnd(bind (foo ((false) && (true))) (fun _ => let out_16 :=
            (@cast _ uint32 _ (x_15)) .+ (pub_u32 (i_17)) in 
          Ok ((out_16)))) >> (fun '(out_16) =>
      Ok ((out_16))))) (fun out_16 => @Ok int32 uint8 (out_16))).

