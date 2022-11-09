(** This file was automatically generated using Hacspec **)
Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
Require Import Hacspec_Lib.

Definition schedule_t := nseq (uint32) (usize 80).

Definition block_words_v : uint_size :=
  (usize 512) / (usize 32).

Definition hash_words_v : uint_size :=
  (usize 160) / (usize 32).

Definition block_t := nseq (uint32) (block_words_v).

Definition hash_t := nseq (uint32) (hash_words_v).

Definition block_bytes_v : uint_size :=
  (usize 512) / (usize 8).

Definition hash_bytes_v : uint_size :=
  (usize 160) / (usize 8).

Definition block_bytes_t := nseq (uint8) (block_bytes_v).

Definition sha1_digest_t := nseq (uint8) (hash_bytes_v).

Definition bitlength_bytes_v : uint_size :=
  (usize 64) / (usize 8).

Definition ch (x_1084 : uint32) (y_1085 : uint32) (z_1086 : uint32) : uint32 :=
  ((x_1084) .& (y_1085)) .^ ((not (x_1084)) .& (z_1086)).

Definition parity
  (x_1087 : uint32)
  (y_1088 : uint32)
  (z_1089 : uint32)
  : uint32 :=
  ((x_1087) .^ (y_1088)) .^ (z_1089).

Definition maj (x_1090 : uint32) (y_1091 : uint32) (z_1092 : uint32) : uint32 :=
  (((x_1090) .& (y_1091)) .^ ((x_1090) .& (z_1092))) .^ ((y_1091) .& (z_1092)).

Definition hash_init_v : hash_t :=
  array_from_list uint32 (let l :=
      [
        secret (@repr WORDSIZE32 1732584193) : int32;
        secret (@repr WORDSIZE32 4023233417) : int32;
        secret (@repr WORDSIZE32 2562383102) : int32;
        secret (@repr WORDSIZE32 271733878) : int32;
        secret (@repr WORDSIZE32 3285377520) : int32
      ] in  l).

Definition compress (m_bytes_1093 : block_bytes_t) (h_1094 : hash_t) : hash_t :=
  let m_1095 : seq uint32 :=
    array_to_be_uint32s (m_bytes_1093) in 
  let w_1096 : schedule_t :=
    array_new_ (default) (80) in 
  let w_1096 :=
    foldi (usize 0) (usize 80) (fun t_1097 w_1096 =>
      let '(w_1096) :=
        if (t_1097) <.? (usize 16):bool then (let w_1096 :=
            array_upd w_1096 (t_1097) (seq_index (m_1095) (t_1097)) in 
          (w_1096)) else (let w_1096 :=
            array_upd w_1096 (t_1097) (uint32_rotate_left ((((array_index (
                        w_1096) ((t_1097) - (usize 3))) .^ (array_index (
                        w_1096) ((t_1097) - (usize 8)))) .^ (array_index (
                      w_1096) ((t_1097) - (usize 14)))) .^ (array_index (
                    w_1096) ((t_1097) - (usize 16)))) (usize 1)) in 
          (w_1096)) in 
      (w_1096))
    w_1096 in 
  let a_1098 : uint32 :=
    array_index (h_1094) (usize 0) in 
  let b_1099 : uint32 :=
    array_index (h_1094) (usize 1) in 
  let c_1100 : uint32 :=
    array_index (h_1094) (usize 2) in 
  let d_1101 : uint32 :=
    array_index (h_1094) (usize 3) in 
  let e_1102 : uint32 :=
    array_index (h_1094) (usize 4) in 
  let '(a_1098, b_1099, c_1100, d_1101, e_1102) :=
    foldi (usize 0) (usize 80) (fun t_1103 '(
        a_1098,
        b_1099,
        c_1100,
        d_1101,
        e_1102
      ) =>
      let t_1104 : uint32 :=
        uint32_zero  in 
      let '(t_1104) :=
        if ((usize 0) <=.? (t_1103)) && ((t_1103) <.? (usize 20)):bool then (
          let t_1104 :=
            ((((uint32_rotate_left (a_1098) (usize 5)) .+ (ch (b_1099) (
                      c_1100) (d_1101))) .+ (e_1102)) .+ (secret (
                  @repr WORDSIZE32 1518500249) : int32)) .+ (array_index (
                w_1096) (t_1103)) in 
          (t_1104)) else ((t_1104)) in 
      let '(t_1104) :=
        if ((usize 20) <=.? (t_1103)) && ((t_1103) <.? (usize 40)):bool then (
          let t_1104 :=
            ((((uint32_rotate_left (a_1098) (usize 5)) .+ (parity (b_1099) (
                      c_1100) (d_1101))) .+ (e_1102)) .+ (secret (
                  @repr WORDSIZE32 1859775393) : int32)) .+ (array_index (
                w_1096) (t_1103)) in 
          (t_1104)) else ((t_1104)) in 
      let '(t_1104) :=
        if ((usize 40) <=.? (t_1103)) && ((t_1103) <.? (usize 60)):bool then (
          let t_1104 :=
            ((((uint32_rotate_left (a_1098) (usize 5)) .+ (maj (b_1099) (
                      c_1100) (d_1101))) .+ (e_1102)) .+ (secret (
                  @repr WORDSIZE32 2400959708) : int32)) .+ (array_index (
                w_1096) (t_1103)) in 
          (t_1104)) else ((t_1104)) in 
      let '(t_1104) :=
        if ((usize 60) <=.? (t_1103)) && ((t_1103) <.? (usize 80)):bool then (
          let t_1104 :=
            ((((uint32_rotate_left (a_1098) (usize 5)) .+ (parity (b_1099) (
                      c_1100) (d_1101))) .+ (e_1102)) .+ (secret (
                  @repr WORDSIZE32 3395469782) : int32)) .+ (array_index (
                w_1096) (t_1103)) in 
          (t_1104)) else ((t_1104)) in 
      let e_1102 :=
        d_1101 in 
      let d_1101 :=
        c_1100 in 
      let c_1100 :=
        uint32_rotate_left (b_1099) (usize 30) in 
      let b_1099 :=
        a_1098 in 
      let a_1098 :=
        t_1104 in 
      (a_1098, b_1099, c_1100, d_1101, e_1102))
    (a_1098, b_1099, c_1100, d_1101, e_1102) in 
  let h_1094 :=
    array_upd h_1094 (usize 0) ((a_1098) .+ (array_index (h_1094) (
          usize 0))) in 
  let h_1094 :=
    array_upd h_1094 (usize 1) ((b_1099) .+ (array_index (h_1094) (
          usize 1))) in 
  let h_1094 :=
    array_upd h_1094 (usize 2) ((c_1100) .+ (array_index (h_1094) (
          usize 2))) in 
  let h_1094 :=
    array_upd h_1094 (usize 3) ((d_1101) .+ (array_index (h_1094) (
          usize 3))) in 
  let h_1094 :=
    array_upd h_1094 (usize 4) ((e_1102) .+ (array_index (h_1094) (
          usize 4))) in 
  h_1094.

Definition hash (msg_1105 : byte_seq) : sha1_digest_t :=
  let h_1106 : hash_t :=
    hash_init_v in 
  let h_1106 :=
    foldi (usize 0) (seq_num_exact_chunks (msg_1105) (
          block_bytes_v)) (fun i_1107 h_1106 =>
      let raw_bytes_1108 : seq uint8 :=
        seq_get_exact_chunk (msg_1105) (block_bytes_v) (i_1107) in 
      let block_bytes_1109 : block_bytes_t :=
        array_from_seq (block_bytes_v) (raw_bytes_1108) in 
      let h_1106 :=
        compress (block_bytes_1109) (h_1106) in 
      (h_1106))
    h_1106 in 
  let raw_bytes_1110 : seq uint8 :=
    seq_get_remainder_chunk (msg_1105) (block_bytes_v) in 
  let block_bytes_1111 : block_bytes_t :=
    array_update_start (array_new_ (default) (block_bytes_v)) (
      raw_bytes_1110) in 
  let block_bytes_1111 :=
    array_upd block_bytes_1111 (seq_len (raw_bytes_1110)) (secret (
        @repr WORDSIZE8 128) : int8) in 
  let message_bitlength_1112 : uint64 :=
    secret (pub_u64 ((seq_len (msg_1105)) * (usize 8))) : int64 in 
  let '(h_1106, block_bytes_1111) :=
    if (seq_len (raw_bytes_1110)) <.? ((block_bytes_v) - (
        bitlength_bytes_v)):bool then (let block_bytes_1111 :=
        array_update (block_bytes_1111) ((block_bytes_v) - (
            bitlength_bytes_v)) (array_to_seq (uint64_to_be_bytes (
            message_bitlength_1112))) in 
      let h_1106 :=
        compress (block_bytes_1111) (h_1106) in 
      (h_1106, block_bytes_1111)) else (let h_1106 :=
        compress (block_bytes_1111) (h_1106) in 
      let pad_block_1113 : block_bytes_t :=
        array_new_ (default) (block_bytes_v) in 
      let pad_block_1113 :=
        array_update (pad_block_1113) ((block_bytes_v) - (bitlength_bytes_v)) (
          array_to_seq (uint64_to_be_bytes (message_bitlength_1112))) in 
      let h_1106 :=
        compress (pad_block_1113) (h_1106) in 
      (h_1106, block_bytes_1111)) in 
  array_from_seq (hash_bytes_v) (array_to_be_bytes (h_1106)).

Definition sha1 (msg_1114 : byte_seq) : sha1_digest_t :=
  hash (msg_1114).

