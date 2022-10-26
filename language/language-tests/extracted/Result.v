(** This file was automatically generated using Hacspec **)
Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
Require Import Hacspec_Lib.

Definition simple_output_t := nseq (uint8) (usize 3).

Notation "'simple_output_result_t'" := ((
  result simple_output_t int8)) : hacspec_scope.

Notation "'s_result_t'" := (simple_output_result_t) : hacspec_scope.

Definition foo (x_0 : (result (result uint32 uint_size) uint_size)) : uint32 :=
  let y_1 : (result uint32 uint_size) :=
    @Ok uint32 uint_size (secret (@repr WORDSIZE32 1) : int32) in 
  let z_2 : (result uint32 uint_size) :=
    @Err uint32 uint_size (usize 8) in 
  match x_0 with
  | Ok _ => secret (@repr WORDSIZE32 0) : int32
  | Err x_3 => secret (pub_u32 (x_3)) : int32
  end.

Definition other  : (result simple_output_t int8) :=
  @Err simple_output_t int8 (@repr WORDSIZE8 1).

Definition other_result_alias  : simple_output_result_t :=
  @Err simple_output_t int8 (@repr WORDSIZE8 1).

Definition type_confusion  : (result simple_output_t int8) :=
  other .

Definition return_type_alias  : (result simple_output_t int8) :=
  @Err simple_output_t int8 (@repr WORDSIZE8 1).

Definition type_alias_question_mark  : (result simple_output_t int8) :=
  bind (other_result_alias ) (fun other_result_4 => @Err simple_output_t int8 (
      @repr WORDSIZE8 1)).

Definition type_alias_question_mark_return  : simple_output_result_t :=
  bind (other ) (fun other_result_5 => @Err simple_output_t int8 (
      @repr WORDSIZE8 1)).

Definition type_double_alias_question_mark_return  : s_result_t :=
  bind (other ) (fun other_result_6 => @Err simple_output_t int8 (
      @repr WORDSIZE8 1)).

Definition unwrap_result  : simple_output_t :=
  result_unwrap (other ).

Definition match_result  : simple_output_t :=
  let result_value_7 : (result simple_output_t int8) :=
    type_double_alias_question_mark_return  in 
  match result_value_7 with
  | Ok r_8 => r_8
  | Err _ => array_new_ (default) (3)
  end.

