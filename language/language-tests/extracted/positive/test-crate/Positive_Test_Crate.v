(** This file was automatically generated using Hacspec **)
Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
Require Import Submod1.

Require Import Submod2.

Definition test_simpl_fails  : res_t :=
  match Ok ((usize 42, usize 42)) with | Ok res_0 => res_0 end.

Definition test_tuple_destructuring  : unit :=
  let tuple_1 : my_tuple_type_t :=
    (MyTupleType ((@repr WORDSIZE16 1, @repr WORDSIZE8 2))) in 
  let 'MyTupleType ((a_2, b_3)) :=
    tuple_1 in 
  tt.

