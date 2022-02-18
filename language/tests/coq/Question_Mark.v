(** This file was automatically generated using Hacspec **)
Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
Require Import Hacspec_Lib.

Definition foo_option (x_0 : bool) : (option int64) :=
  (if (x_0):bool then (@Some int64 (@repr WORDSIZE64 42)) else (@None int64)).

Definition bar_option  : (option int64) :=
  bind (foo_option (false)) (fun x_1 => @Some int64 ((x_1) .+ (
        @repr WORDSIZE64 1))).

Definition foo (x_2 : bool) : (result int64 uint8) :=
  (if (x_2):bool then (@Ok int64 uint8 (@repr WORDSIZE64 42)) else (
      @Err int64 uint8 (secret (@repr WORDSIZE8 0) : int8))).

Definition bar  : (result int64 uint8) :=
  bind (foo (false)) (fun x_3 => @Ok int64 uint8 ((x_3) .+ (
        @repr WORDSIZE64 1))).

Definition fizzbaz  : (result int64 uint8) :=
  bind (foo (false)) (fun x_4 => bind (foo (true)) (fun y_5 => @Ok int64 uint8 (
        (x_4) .+ (y_5)))).

Definition fizzbazbaz  : (result int64 uint8) :=
  bind (foo (false)) (fun x_6 => bind (foo (true)) (fun y_7 => let x_6 :=
        (x_6) .+ (y_7) in 
      bind (foo (false)) (fun y_7  => @Ok int64 uint8 ((x_6) .+ (y_7))))).

Definition fizzbazbazbar (s_8 : seq int64) : (result int64 uint8) :=
  bind (foo (false)) (fun y_9 => bind (foo (true)) (fun _temp => let s_8 :=
        seq_upd s_8 (usize 0) _temp in 
      @Ok int64 uint8 ((seq_index (s_8) (usize 0)) .+ (y_9)))).

Definition baz  : (result int32 uint8) :=
  bind (foo (false)) (fun x_10 => let out_11 : int32 :=
      @repr WORDSIZE32 0 in 
    ifbnd (true) || (false) : bool
    thenbnd (bind (foo (true)) (fun y_12 => bind (foo ((false) || (true))) (
          fun _ => Ok ((out_11)))))
    elsebnd(bind (foo ((false) && (true))) (fun _ => let out_11 :=
          (@cast _ uint32 _ (x_10)) .+ (@repr WORDSIZE32 1) in 
        Ok ((out_11)))) >> (fun '(out_11) =>
    @Ok int32 uint8 (out_11))).

Definition fizzbar  : (result int32 uint8) :=
  bind (foo (false)) (fun x_13 => let out_14 : int32 :=
      @repr WORDSIZE32 0 in 
    bind (foldibnd (usize 0) to (usize 200) for out_14 >> (fun i_15 out_14 =>
      bind (foo (true)) (fun y_16 => let out_14 :=
          ((pub_u32 (i_15)) .+ (@cast _ uint32 _ (y_16))) .+ (out_14) in 
        Ok ((out_14))))) (fun out_14 => @Ok int32 uint8 (out_14))).

Definition fizzbarbuzz  : (result int32 uint8) :=
  bind (foo (false)) (fun x_17 => let out_18 : int32 :=
      @repr WORDSIZE32 0 in 
    bind (foldibnd (usize 0) to (usize 200) for out_18 >> (fun i_19 out_18 =>
      ifbnd (true) || (false) : bool
      thenbnd (bind (foo (true)) (fun y_20 => let out_18 :=
            (@cast _ uint32 _ (y_20)) .+ (out_18) in 
          bind (foo ((false) || (true))) (fun _ => Ok ((out_18)))))
      elsebnd(bind (foo ((false) && (true))) (fun _ => let out_18 :=
            (@cast _ uint32 _ (x_17)) .+ (pub_u32 (i_19)) in 
          Ok ((out_18)))) >> (fun '(out_18) =>
      Ok ((out_18))))) (fun out_18 => @Ok int32 uint8 (out_18))).

Notation "'alias_t'" := ((result int32 uint8)) : hacspec_scope.

Definition alias_test  : alias_t :=
  ifbnd true : bool
  thenbnd (bind (@Err int32 uint8 (secret (@repr WORDSIZE8 0) : int8)) (fun _ =>
      Ok (tt)))
  else (tt) >> (fun 'tt =>
  @Ok int32 uint8 (@repr WORDSIZE32 1)).

