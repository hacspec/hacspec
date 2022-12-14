(** This file was automatically generated using Hacspec **)
Set Warnings "-notation-overridden,-ambiguous-paths".
From Crypt Require Import choice_type Package Prelude.
Import PackageNotation.
From extructures Require Import ord fset.
From mathcomp.word Require Import ssrZ word.
From Jasmin Require Import word.

From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope list_scope.
Open Scope Z_scope.
Open Scope bool_scope.

Require Import ChoiceEquality.
Require Import LocationUtility.
Require Import Hacspec_Lib_Comparable.
Require Import Hacspec_Lib_Pre.
Require Import Hacspec_Lib.

Open Scope hacspec_scope.

Obligation Tactic := try timeout 8 solve_ssprove_obligations.


Definition bi_3316_loc : ChoiceEqualityLocation :=
  (big_int_t ; 3317%nat).
Notation "'big_integer_test_inp'" :=(
  unit_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'big_integer_test_inp'" :=(
  unit_ChoiceEquality : ChoiceEquality) (at level 2).
Notation "'big_integer_test_out'" :=(
  unit_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'big_integer_test_out'" :=(
  unit_ChoiceEquality : ChoiceEquality) (at level 2).
Definition BIG_INTEGER_TEST : nat :=
  3318.
Program Definition big_integer_test 
  : both (CEfset ([bi_3316_loc])) [interface] (unit_ChoiceEquality) :=
  ((letb _ : big_int_t := big_int_zero  in
      letb _ : big_int_t := big_int_one  in
      letb _ : big_int_t := big_int_two  in
      letbm bi_3316 : big_int_t loc( bi_3316_loc ) :=
        big_int_from_literal (lift_to_both0 (@repr U128 1238)) in
      letbm bi_3316 loc( bi_3316_loc ) :=
        big_int_get_bit (lift_to_both0 bi_3316) (lift_to_both0 (usize 3)) in
      letbm bi_3316 loc( bi_3316_loc ) :=
        big_int_set_bit (lift_to_both0 bi_3316) (big_int_one ) (lift_to_both0 (
            usize 3)) in
      letbm bi_3316 loc( bi_3316_loc ) :=
        big_int_set (lift_to_both0 bi_3316) (lift_to_both0 (usize 4)) (
          big_int_two ) (lift_to_both0 (usize 2)) in
      letbm bi_3316 loc( bi_3316_loc ) :=
        big_int_wrap_add (lift_to_both0 bi_3316) (big_int_two ) in
      letbm bi_3316 loc( bi_3316_loc ) :=
        big_int_wrap_sub (lift_to_both0 bi_3316) (big_int_two ) in
      letbm bi_3316 loc( bi_3316_loc ) :=
        big_int_wrap_mul (lift_to_both0 bi_3316) (big_int_two ) in
      letb _ : bool_ChoiceEquality :=
        big_int_equal (big_int_one ) (big_int_two ) in
      letbm bi_3316 loc( bi_3316_loc ) :=
        big_int_sub_mod (lift_to_both0 bi_3316) (big_int_two ) (
          big_int_from_literal (lift_to_both0 (@repr U128 4))) in
      letbm bi_3316 loc( bi_3316_loc ) :=
        big_int_add_mod (lift_to_both0 bi_3316) (big_int_two ) (
          big_int_from_literal (lift_to_both0 (@repr U128 4))) in
      letbm bi_3316 loc( bi_3316_loc ) :=
        big_int_mul_mod (lift_to_both0 bi_3316) (big_int_two ) (
          big_int_from_literal (lift_to_both0 (@repr U128 4))) in
      letbm bi_3316 loc( bi_3316_loc ) :=
        big_int_absolute (lift_to_both0 bi_3316) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 (
          (tt : unit_ChoiceEquality)))
      ) : both (CEfset ([bi_3316_loc])) [interface] (unit_ChoiceEquality)).
Fail Next Obligation.

Definition mi_3319_loc : ChoiceEqualityLocation :=
  (int16 ; 3320%nat).
Notation "'machine_integer_test_inp'" :=(
  unit_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'machine_integer_test_inp'" :=(
  unit_ChoiceEquality : ChoiceEquality) (at level 2).
Notation "'machine_integer_test_out'" :=(
  unit_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'machine_integer_test_out'" :=(
  unit_ChoiceEquality : ChoiceEquality) (at level 2).
Definition MACHINE_INTEGER_TEST : nat :=
  3321.
Program Definition machine_integer_test 
  : both (CEfset ([mi_3319_loc])) [interface] (unit_ChoiceEquality) :=
  ((letb _ : int32 := pub_uint32_zero  in
      letb _ : int8 := pub_uint8_one  in
      letb _ : int128 := pub_uint128_two  in
      letbm mi_3319 : int16 loc( mi_3319_loc ) :=
        pub_uint16_from_literal (lift_to_both0 (@repr U128 1238)) in
      letbm mi_3319 loc( mi_3319_loc ) :=
        pub_uint16_get_bit (lift_to_both0 mi_3319) (lift_to_both0 (usize 3)) in
      letbm mi_3319 loc( mi_3319_loc ) :=
        pub_uint16_set_bit (lift_to_both0 mi_3319) (pub_uint16_one ) (
          lift_to_both0 (usize 3)) in
      letbm mi_3319 loc( mi_3319_loc ) :=
        pub_uint16_set (lift_to_both0 mi_3319) (lift_to_both0 (usize 4)) (
          pub_uint16_two ) (lift_to_both0 (usize 2)) in
      letbm mi_3319 loc( mi_3319_loc ) :=
        pub_uint16_rotate_left (lift_to_both0 mi_3319) (lift_to_both0 (
            @repr U32 4)) in
      letbm mi_3319 loc( mi_3319_loc ) :=
        pub_uint16_rotate_right (lift_to_both0 mi_3319) (lift_to_both0 (
            @repr U32 4)) in
      letb _ : int16 := pub_uint16_max_val  in
      letbm mi_3319 loc( mi_3319_loc ) :=
        pub_uint16_wrap_add (lift_to_both0 mi_3319) (pub_uint16_two ) in
      letbm mi_3319 loc( mi_3319_loc ) :=
        pub_uint16_wrap_sub (lift_to_both0 mi_3319) (pub_uint16_two ) in
      letbm mi_3319 loc( mi_3319_loc ) :=
        pub_uint16_wrap_mul (lift_to_both0 mi_3319) (pub_uint16_two ) in
      letbm mi_3319 loc( mi_3319_loc ) :=
        pub_uint16_exp (lift_to_both0 mi_3319) (lift_to_both0 (@repr U32 2)) in
      letbm mi_3319 loc( mi_3319_loc ) :=
        pub_uint16_divide (lift_to_both0 mi_3319) (pub_uint16_two ) in
      letbm mi_3319 loc( mi_3319_loc ) :=
        pub_uint16_inv (pub_uint16_from_literal (lift_to_both0 (
              @repr U128 79))) (pub_uint16_two ) in
      letb _ : bool_ChoiceEquality :=
        pub_uint16_equal (pub_uint16_one ) (pub_uint16_two ) in
      letb _ : bool_ChoiceEquality :=
        pub_uint16_greater_than (pub_uint16_one ) (pub_uint16_two ) in
      letb _ : bool_ChoiceEquality :=
        pub_uint16_greater_than_or_equal (pub_uint16_one ) (pub_uint16_two ) in
      letb _ : bool_ChoiceEquality :=
        pub_uint16_less_than (pub_uint16_one ) (pub_uint16_two ) in
      letb _ : bool_ChoiceEquality :=
        pub_uint16_less_than_or_equal (pub_uint16_one ) (pub_uint16_two ) in
      letbm mi_3319 loc( mi_3319_loc ) :=
        pub_uint16_not_equal_bm (lift_to_both0 mi_3319) (pub_uint16_two ) in
      letbm mi_3319 loc( mi_3319_loc ) :=
        pub_uint16_equal_bm (lift_to_both0 mi_3319) (pub_uint16_two ) in
      letbm mi_3319 loc( mi_3319_loc ) :=
        pub_uint16_greater_than_bm (lift_to_both0 mi_3319) (pub_uint16_two ) in
      letbm mi_3319 loc( mi_3319_loc ) :=
        pub_uint16_greater_than_or_equal_bm (lift_to_both0 mi_3319) (
          pub_uint16_two ) in
      letbm mi_3319 loc( mi_3319_loc ) :=
        pub_uint16_less_than_bm (lift_to_both0 mi_3319) (pub_uint16_two ) in
      letbm mi_3319 loc( mi_3319_loc ) :=
        pub_uint16_less_than_or_equal_bm (lift_to_both0 mi_3319) (
          pub_uint16_two ) in
      letbm mi_3319 loc( mi_3319_loc ) :=
        pub_uint16_sub_mod (lift_to_both0 mi_3319) (pub_uint16_two ) (
          pub_uint16_from_literal (lift_to_both0 (@repr U128 4))) in
      letbm mi_3319 loc( mi_3319_loc ) :=
        pub_uint16_add_mod (lift_to_both0 mi_3319) (pub_uint16_two ) (
          pub_uint16_from_literal (lift_to_both0 (@repr U128 4))) in
      letbm mi_3319 loc( mi_3319_loc ) :=
        pub_uint16_mul_mod (lift_to_both0 mi_3319) (pub_uint16_two ) (
          pub_uint16_from_literal (lift_to_both0 (@repr U128 4))) in
      letbm mi_3319 loc( mi_3319_loc ) :=
        pub_uint16_absolute (lift_to_both0 mi_3319) in
      letb _ : uint64 := secret (lift_to_both0 (@repr U64 12)) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 (
          (tt : unit_ChoiceEquality)))
      ) : both (CEfset ([mi_3319_loc])) [interface] (unit_ChoiceEquality)).
Fail Next Obligation.

Definition ns2_3324_loc : ChoiceEqualityLocation :=
  (seq int8 ; 3326%nat).
Definition ns_3325_loc : ChoiceEqualityLocation :=
  (seq int8 ; 3327%nat).
Definition ns_3322_loc : ChoiceEqualityLocation :=
  (seq int8 ; 3328%nat).
Definition ns1_3323_loc : ChoiceEqualityLocation :=
  (seq int8 ; 3329%nat).
Notation "'seq_test_inp'" :=(
  unit_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'seq_test_inp'" :=(unit_ChoiceEquality : ChoiceEquality) (at level 2).
Notation "'seq_test_out'" :=(
  unit_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'seq_test_out'" :=(unit_ChoiceEquality : ChoiceEquality) (at level 2).
Definition SEQ_TEST : nat :=
  3330.
Program Definition seq_test 
  : both (CEfset (
      [ns_3322_loc ; ns1_3323_loc ; ns2_3324_loc ; ns_3325_loc])) [interface] (
    unit_ChoiceEquality) :=
  ((letbm ns_3322 : seq int8 loc( ns_3322_loc ) :=
        seq_with_capacity (lift_to_both0 (usize 5)) in
      letbm ns_3322 loc( ns_3322_loc ) :=
        seq_new_ (default : int8) (lift_to_both0 (usize 5)) in
      letbm ns_3322 loc( ns_3322_loc ) :=
        seq_reserve (lift_to_both0 ns_3322) (lift_to_both0 (usize 10)) in
      letb _ : uint_size := seq_len (lift_to_both0 ns_3322) in
      letbm ns_3322 loc( ns_3322_loc ) :=
        seq_slice (lift_to_both0 ns_3322) (lift_to_both0 (usize 0)) (
          lift_to_both0 (usize 5)) in
      letbm ns_3322 loc( ns_3322_loc ) :=
        seq_into_slice (lift_to_both0 ns_3322) (lift_to_both0 (usize 1)) (
          lift_to_both0 (usize 3)) in
      letbm ns_3322 loc( ns_3322_loc ) :=
        seq_slice_range (lift_to_both0 ns_3322) (prod_b(
            lift_to_both0 (usize 0),
            lift_to_both0 (usize 2)
          )) in
      letbm ns_3322 loc( ns_3322_loc ) :=
        seq_into_slice_range (lift_to_both0 ns_3322) (prod_b(
            lift_to_both0 (usize 0),
            lift_to_both0 (usize 1)
          )) in
      letb '(ns1_3323, ns2_3324) : (seq int8 '× seq int8) :=
        seq_split_off (lift_to_both0 ns_3322) (lift_to_both0 (usize 1)) in
      letbm ns1_3323 loc( ns1_3323_loc ) :=
        seq_truncate (lift_to_both0 ns1_3323) (lift_to_both0 (usize 2)) in
      letbm ns2_3324 loc( ns2_3324_loc ) :=
        seq_from_slice (lift_to_both0 ns1_3323) (lift_to_both0 (usize 0)) (
          lift_to_both0 (usize 1)) in
      letbm ns_3325 : seq int8 loc( ns_3325_loc ) :=
        seq_concat (lift_to_both0 ns1_3323) (lift_to_both0 ns2_3324) in
      letbm ns_3325 loc( ns_3325_loc ) :=
        seq_concat_owned (lift_to_both0 ns1_3323) (lift_to_both0 ns2_3324) in
      letbm ns_3325 loc( ns_3325_loc ) :=
        seq_push (lift_to_both0 ns_3325) (lift_to_both0 (@repr U8 2)) in
      letbm ns_3325 loc( ns_3325_loc ) :=
        seq_push_owned (lift_to_both0 ns_3325) (lift_to_both0 (@repr U8 4)) in
      letbm ns_3325 loc( ns_3325_loc ) :=
        seq_from_slice_range (lift_to_both0 ns_3325) (prod_b(
            lift_to_both0 (usize 0),
            lift_to_both0 (usize 4)
          )) in
      letb _ : uint_size :=
        seq_num_chunks (lift_to_both0 ns_3325) (lift_to_both0 (usize 2)) in
      letb _ : uint_size :=
        seq_num_exact_chunks (lift_to_both0 ns_3325) (lift_to_both0 (
            usize 2)) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 (
          (tt : unit_ChoiceEquality)))
      ) : both (CEfset (
        [ns_3322_loc ; ns1_3323_loc ; ns2_3324_loc ; ns_3325_loc])) [interface] (
      unit_ChoiceEquality)).
Fail Next Obligation.

Definition arr_name_t := nseq (uint64) (usize 8).

Definition byte_arr_name_t := nseq (uint8) (usize 128).


Notation "'array_test_inp'" :=(
  unit_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'array_test_inp'" :=(
  unit_ChoiceEquality : ChoiceEquality) (at level 2).
Notation "'array_test_out'" :=(
  unit_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'array_test_out'" :=(
  unit_ChoiceEquality : ChoiceEquality) (at level 2).
Definition ARRAY_TEST : nat :=
  3331.
Program Definition array_test 
  : both (fset.fset0) [interface] (unit_ChoiceEquality) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 (
          (tt : unit_ChoiceEquality)))
      ) : both (fset.fset0) [interface] (unit_ChoiceEquality)).
Fail Next Obligation.

