(** This file was automatically generated using Hacspec **)
Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
Require Import Hacspec_Lib.

Definition bool_true  : bool :=
  true.

Definition bool_false  : bool :=
  false.

Definition num_u8  : int8 :=
  @repr WORDSIZE8 100.

Definition num_u16  : int16 :=
  @repr WORDSIZE16 100.

Definition num_u32  : int32 :=
  @repr WORDSIZE32 100.

Definition num_u64  : int64 :=
  @repr WORDSIZE64 100.

Definition num_u128  : int128 :=
  @repr WORDSIZE128 100.

Definition num_usize  : uint_size :=
  usize 100.

Definition num_i8  : int8 :=
  @repr WORDSIZE8 100.

Definition num_i16  : int16 :=
  @repr WORDSIZE16 100.

Definition num_i32  : int32 :=
  @repr WORDSIZE32 100.

Definition num_i64  : int64 :=
  @repr WORDSIZE64 100.

Definition num_i128  : int128 :=
  @repr WORDSIZE128 100.

Definition num_isize  : int_size :=
  isize 100.

Definition tuple  : (bool × int64 × unit) :=
  (false, num_i64 , tt).

Definition my_array_t := nseq (int64) (usize 5).

Definition array  : my_array_t :=
  array_from_list int64 (let l :=
      [
        @repr WORDSIZE64 0;
        @repr WORDSIZE64 1;
        @repr WORDSIZE64 2;
        @repr WORDSIZE64 3;
        @repr WORDSIZE64 4
      ] in  l).

Definition sequence  : seq int64 :=
  seq_new_ (default) (usize 0).

Inductive my_tuple_struct_t :=
| MyTupleStruct : (bool × seq int64) -> my_tuple_struct_t.

Definition my_tuple_struct_fn  : my_tuple_struct_t :=
  MyTupleStruct ((true, sequence )).

Inductive my_enum_t :=
| First : my_enum_t
| Second : int64 -> my_enum_t
| Third : bool -> my_enum_t.

Definition my_enum_fn (inp_0 : my_enum_t) : my_enum_t :=
  match inp_0 with
  | First => Second (@repr WORDSIZE64 0)
  | Second _ => Third (false)
  | Third _ => First
  end.

