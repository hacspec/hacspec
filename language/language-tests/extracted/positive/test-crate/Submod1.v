(** This file was automatically generated using Hacspec **)
Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
Require Import Another_Submod1_File.

Inductive my_tuple_type_t :=
| MyTupleType : (int16 × int8) -> my_tuple_type_t.

