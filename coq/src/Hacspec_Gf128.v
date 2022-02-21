(** This file was automatically generated using Hacspec **)
Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
Require Import Hacspec_Lib.

Definition blocksize_v : uint_size :=
  usize 16.

Definition gf128_block_t := nseq (uint8) (blocksize_v).

Definition gf128_key_t := nseq (uint8) (blocksize_v).

Definition gf128_tag_t := nseq (uint8) (blocksize_v).

Notation "'element_t'" := (uint128) : hacspec_scope.

Definition irred_v : element_t :=
  secret (@repr WORDSIZE128 299076299051606071403356588563077529600) : int128.

Definition fadd (x_0 : element_t) (y_1 : element_t) : element_t :=
  (x_0) .^ (y_1).

Definition fmul (x_2 : element_t) (y_3 : element_t) : element_t :=
  let res_4 : element_t :=
    secret (@repr WORDSIZE128 0) : int128 in 
  let sh_5 : uint128 :=
    x_2 in 
  let '(res_4, sh_5) :=
    foldi (usize 0) (usize 128) (fun i_6 '(res_4, sh_5) =>
      let '(res_4) :=
        if (uint128_declassify ((y_3) .& ((secret (
                  @repr WORDSIZE128 1) : int128) shift_left ((usize 127) - (
                  i_6))))) !=.? (uint128_declassify (secret (
              @repr WORDSIZE128 0) : int128)):bool then (let res_4 :=
            (res_4) .^ (sh_5) in 
          (res_4)) else ((res_4)) in 
      let '(sh_5) :=
        if (uint128_declassify ((sh_5) .& (secret (
                @repr WORDSIZE128 1) : int128))) !=.? (uint128_declassify (
            secret (@repr WORDSIZE128 0) : int128)):bool then (let sh_5 :=
            ((sh_5) shift_right (usize 1)) .^ (irred_v) in 
          (sh_5)) else (let sh_5 :=
            (sh_5) shift_right (usize 1) in 
          (sh_5)) in 
      (res_4, sh_5))
    (res_4, sh_5) in 
  res_4.

Definition encode (block_7 : gf128_block_t) : element_t :=
  uint128_from_be_bytes (array_from_seq (16) (block_7)).

Definition decode (e_8 : element_t) : gf128_block_t :=
  array_from_seq (blocksize_v) (uint128_to_be_bytes (e_8)).

Definition update
  (r_9 : element_t)
  (block_10 : gf128_block_t)
  (acc_11 : element_t)
  : element_t :=
  fmul (fadd (encode (block_10)) (acc_11)) (r_9).

Definition poly (msg_12 : byte_seq) (r_13 : element_t) : element_t :=
  let l_14 : uint_size :=
    seq_len (msg_12) in 
  let n_blocks_15 : uint_size :=
    (l_14) / (blocksize_v) in 
  let rem_16 : uint_size :=
    (l_14) %% (blocksize_v) in 
  let acc_17 : uint128 :=
    secret (@repr WORDSIZE128 0) : int128 in 
  let acc_17 :=
    foldi (usize 0) (n_blocks_15) (fun i_18 acc_17 =>
      let k_19 : uint_size :=
        (i_18) * (blocksize_v) in 
      let block_20 : gf128_block_t :=
        array_new_ (default) (blocksize_v) in 
      let block_20 :=
        array_update_start (block_20) (seq_slice_range (msg_12) ((
              k_19,
              (k_19) + (blocksize_v)
            ))) in 
      let acc_17 :=
        update (r_13) (block_20) (acc_17) in 
      (acc_17))
    acc_17 in 
  let '(acc_17) :=
    if (rem_16) !=.? (usize 0):bool then (let k_21 : uint_size :=
        (n_blocks_15) * (blocksize_v) in 
      let last_block_22 : gf128_block_t :=
        array_new_ (default) (blocksize_v) in 
      let last_block_22 :=
        array_update_slice (last_block_22) (usize 0) (msg_12) (k_21) (
          rem_16) in 
      let acc_17 :=
        update (r_13) (last_block_22) (acc_17) in 
      (acc_17)) else ((acc_17)) in 
  acc_17.

Definition gmac (text_23 : byte_seq) (k_24 : gf128_key_t) : gf128_tag_t :=
  let s_25 : gf128_block_t :=
    array_new_ (default) (blocksize_v) in 
  let r_26 : uint128 :=
    encode (array_from_seq (blocksize_v) (k_24)) in 
  let a_27 : uint128 :=
    poly (text_23) (r_26) in 
  array_from_seq (blocksize_v) (decode (fadd (a_27) (encode (s_25)))).

