(** This file was automatically generated using Hacspec **)
Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
Require Import Hacspec_Lib.

Definition big_integer_test  : unit :=
  let _ : big_int_t :=
    big_int_zero  in 
  let _ : big_int_t :=
    big_int_one  in 
  let _ : big_int_t :=
    big_int_two  in 
  let bi_2514 : big_int_t :=
    big_int_from_literal (@repr WORDSIZE128 1238) in 
  let bi_2514 :=
    big_int_get_bit (bi_2514) (usize 3) in 
  let bi_2514 :=
    big_int_set_bit (bi_2514) (big_int_one ) (usize 3) in 
  let bi_2514 :=
    big_int_set (bi_2514) (usize 4) (big_int_two ) (usize 2) in 
  let bi_2514 :=
    big_int_wrap_add (bi_2514) (big_int_two ) in 
  let bi_2514 :=
    big_int_wrap_sub (bi_2514) (big_int_two ) in 
  let bi_2514 :=
    big_int_wrap_mul (bi_2514) (big_int_two ) in 
  let _ : bool :=
    big_int_equal (big_int_one ) (big_int_two ) in 
  let bi_2514 :=
    big_int_sub_mod (bi_2514) (big_int_two ) (big_int_from_literal (
        @repr WORDSIZE128 4)) in 
  let bi_2514 :=
    big_int_add_mod (bi_2514) (big_int_two ) (big_int_from_literal (
        @repr WORDSIZE128 4)) in 
  let bi_2514 :=
    big_int_mul_mod (bi_2514) (big_int_two ) (big_int_from_literal (
        @repr WORDSIZE128 4)) in 
  let bi_2514 :=
    big_int_absolute (bi_2514) in 
  tt.

Definition machine_integer_test  : unit :=
  let _ : int32 :=
    pub_uint32_zero  in 
  let _ : int8 :=
    pub_uint8_one  in 
  let _ : int128 :=
    pub_uint128_two  in 
  let mi_2515 : int16 :=
    pub_uint16_from_literal (@repr WORDSIZE128 1238) in 
  let mi_2515 :=
    pub_uint16_get_bit (mi_2515) (usize 3) in 
  let mi_2515 :=
    pub_uint16_set_bit (mi_2515) (pub_uint16_one ) (usize 3) in 
  let mi_2515 :=
    pub_uint16_set (mi_2515) (usize 4) (pub_uint16_two ) (usize 2) in 
  let mi_2515 :=
    pub_uint16_rotate_left (mi_2515) (@repr WORDSIZE32 4) in 
  let mi_2515 :=
    pub_uint16_rotate_right (mi_2515) (@repr WORDSIZE32 4) in 
  let _ : int16 :=
    pub_uint16_max_val  in 
  let mi_2515 :=
    pub_uint16_wrap_add (mi_2515) (pub_uint16_two ) in 
  let mi_2515 :=
    pub_uint16_wrap_sub (mi_2515) (pub_uint16_two ) in 
  let mi_2515 :=
    pub_uint16_wrap_mul (mi_2515) (pub_uint16_two ) in 
  let mi_2515 :=
    pub_uint16_exp (mi_2515) (@repr WORDSIZE32 2) in 
  let mi_2515 :=
    pub_uint16_divide (mi_2515) (pub_uint16_two ) in 
  let mi_2515 :=
    pub_uint16_inv (pub_uint16_from_literal (@repr WORDSIZE128 79)) (
      pub_uint16_two ) in 
  let _ : bool :=
    pub_uint16_equal (pub_uint16_one ) (pub_uint16_two ) in 
  let _ : bool :=
    pub_uint16_greater_than (pub_uint16_one ) (pub_uint16_two ) in 
  let _ : bool :=
    pub_uint16_greater_than_or_equal (pub_uint16_one ) (pub_uint16_two ) in 
  let _ : bool :=
    pub_uint16_less_than (pub_uint16_one ) (pub_uint16_two ) in 
  let _ : bool :=
    pub_uint16_less_than_or_equal (pub_uint16_one ) (pub_uint16_two ) in 
  let mi_2515 :=
    pub_uint16_not_equal_bm (mi_2515) (pub_uint16_two ) in 
  let mi_2515 :=
    pub_uint16_equal_bm (mi_2515) (pub_uint16_two ) in 
  let mi_2515 :=
    pub_uint16_greater_than_bm (mi_2515) (pub_uint16_two ) in 
  let mi_2515 :=
    pub_uint16_greater_than_or_equal_bm (mi_2515) (pub_uint16_two ) in 
  let mi_2515 :=
    pub_uint16_less_than_bm (mi_2515) (pub_uint16_two ) in 
  let mi_2515 :=
    pub_uint16_less_than_or_equal_bm (mi_2515) (pub_uint16_two ) in 
  let mi_2515 :=
    pub_uint16_sub_mod (mi_2515) (pub_uint16_two ) (pub_uint16_from_literal (
        @repr WORDSIZE128 4)) in 
  let mi_2515 :=
    pub_uint16_add_mod (mi_2515) (pub_uint16_two ) (pub_uint16_from_literal (
        @repr WORDSIZE128 4)) in 
  let mi_2515 :=
    pub_uint16_mul_mod (mi_2515) (pub_uint16_two ) (pub_uint16_from_literal (
        @repr WORDSIZE128 4)) in 
  let mi_2515 :=
    pub_uint16_absolute (mi_2515) in 
  let _ : uint64 :=
    secret (@repr WORDSIZE64 12) : int64 in 
  tt.

Definition seq_test  : unit :=
  let ns_2516 : seq int8 :=
    seq_with_capacity (usize 5) in 
  let ns_2516 :=
    seq_new_ (default) (usize 5) in 
  let ns_2516 :=
    seq_reserve (ns_2516) (usize 10) in 
  let _ : uint_size :=
    seq_len (ns_2516) in 
  let ns_2516 :=
    seq_slice (ns_2516) (usize 0) (usize 5) in 
  let ns_2516 :=
    seq_into_slice (ns_2516) (usize 1) (usize 3) in 
  let ns_2516 :=
    seq_slice_range (ns_2516) ((usize 0, usize 2)) in 
  let ns_2516 :=
    seq_into_slice_range (ns_2516) ((usize 0, usize 1)) in 
  let '(ns1_2517, ns2_2518) :=
    seq_split_off (ns_2516) (usize 1) in 
  let ns1_2517 :=
    seq_truncate (ns1_2517) (usize 2) in 
  let ns2_2518 :=
    seq_from_slice (ns1_2517) (usize 0) (usize 1) in 
  let ns_2519 : seq int8 :=
    seq_concat (ns1_2517) (ns2_2518) in 
  let ns_2519 :=
    seq_concat_owned (ns1_2517) (ns2_2518) in 
  let ns_2519 :=
    seq_push (ns_2519) (@repr WORDSIZE8 2) in 
  let ns_2519 :=
    seq_push_owned (ns_2519) (@repr WORDSIZE8 4) in 
  let ns_2519 :=
    seq_from_slice_range (ns_2519) ((usize 0, usize 4)) in 
  let _ : uint_size :=
    seq_num_chunks (ns_2519) (usize 2) in 
  let _ : uint_size :=
    seq_num_exact_chunks (ns_2519) (usize 2) in 
  tt.

Definition arr_name_t := nseq (uint64) (usize 8).

Definition byte_arr_name_t := nseq (uint8) (usize 128).

Definition array_test  : unit :=
  tt.

