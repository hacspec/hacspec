(** This file was automatically generated using Hacspec **)
Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
Require Import Hacspec_Lib.

Notation "'my_integer_type_t'" := (uint_size) : hacspec_scope.

Definition foo (x_0 : my_integer_type_t) : uint_size :=
  let x_0 :=
    foldi (usize 0) (x_0) (fun i_1 x_0 =>
      let x_0 :=
        i_1 in 
      (x_0))
    x_0 in 
  x_0.

Notation "'my_uint32_integer_type_t'" := (int32) : hacspec_scope.

Definition baz (x_2 : my_uint32_integer_type_t) : my_uint32_integer_type_t :=
  let x_2 :=
    foldi (usize 0) (@cast _ uint32 _ (x_2)) (fun i_3 x_2 =>
      let x_2 :=
        pub_u32 (i_3) in 
      (x_2))
    x_2 in 
  x_2.

Definition bar (x_4 : uint32) : uint32 :=
  let y_5 : uint32 :=
    x_4 in 
  let y_5 :=
    foldi (usize 0) (usize 5) (fun _ y_5 =>
      let y_5 :=
        (y_5) .+ (secret (@repr WORDSIZE32 1) : int32) in 
      (y_5))
    y_5 in 
  y_5.

Definition foobar (x_6 : int32) : (result int32 int32) :=
  let y_7 : int32 :=
    x_6 in 
  bind (foldibnd (usize 0) to (usize 5) for y_7 >> (fun _ y_7 =>
    ifbnd (y_7) >.? (@repr WORDSIZE32 100) : bool
    thenbnd (bind (@Err int32 int32 (y_7)) (fun _ => Ok (tt)))
    else (tt) >> (fun 'tt =>
    let y_7 :=
      (y_7) .+ (@repr WORDSIZE32 1) in 
    Ok ((y_7))))) (fun y_7 => @Ok int32 int32 (y_7)).

