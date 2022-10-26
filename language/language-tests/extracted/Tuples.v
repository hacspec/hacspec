(** This file was automatically generated using Hacspec **)
Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
Notation "'res_t'" := ((uint_size × uint_size)) : hacspec_scope.

Inductive res_typ_t :=
| Ok : res_t -> res_typ_t.

Definition test_simpl_fails  : res_t :=
  match Ok ((usize 42, usize 42)) with | Ok res_0 => res_0 end.

Inductive my_tuple_type_t :=
| MyTupleType : (int16 × int8) -> my_tuple_type_t.

Definition test_tuple_destructuring  : unit :=
  let tuple_1 : my_tuple_type_t :=
    (MyTupleType ((@repr WORDSIZE16 1, @repr WORDSIZE8 2))) in 
  let 'MyTupleType ((a_2, b_3)) :=
    tuple_1 in 
  tt.

Definition unit_type  : unit :=
  let 'tt :=
    if true:bool then (tt) else (tt) in 
  tt.

Inductive empty_tuple_t :=
| EmptyTuple : unit -> empty_tuple_t.

Definition test_empty_tuple  : empty_tuple_t :=
  EmptyTuple (tt).

