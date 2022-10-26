(** This file was automatically generated using Hacspec **)
Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
Require Import Hacspec_Lib.

Inductive my_struct_t :=
| MyStruct : uint_size -> my_struct_t.

Definition other (x_0 : my_struct_t) : my_struct_t :=
  x_0.

Definition first  : my_struct_t :=
  let s_1 : my_struct_t :=
    MyStruct (usize 0) in 
  let s_copy_2 : my_struct_t :=
    other (s_1) in 
  let 'MyStruct (s_copy2_3) :=
    s_1 in 
  other (s_1).

