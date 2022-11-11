(** This file was automatically generated using Hacspec **)
Set Warnings "-notation-overridden,-ambiguous-paths".
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

Definition ch (x_1201 : uint32) (y_1202 : uint32) (z_1203 : uint32) : uint32 :=
  ((x_1201) .& (y_1202)) .^ ((not (x_1201)) .& (z_1203)).

Definition parity
  (x_1204 : uint32)
  (y_1205 : uint32)
  (z_1206 : uint32)
  : uint32 :=
  ((x_1204) .^ (y_1205)) .^ (z_1206).

Definition maj (x_1207 : uint32) (y_1208 : uint32) (z_1209 : uint32) : uint32 :=
  (((x_1207) .& (y_1208)) .^ ((x_1207) .& (z_1209))) .^ ((y_1208) .& (z_1209)).

Definition hash_init_v : hash_t :=
  array_from_list uint32 (let l :=
      [
        secret (@repr WORDSIZE32 1732584193) : int32;
        secret (@repr WORDSIZE32 4023233417) : int32;
        secret (@repr WORDSIZE32 2562383102) : int32;
        secret (@repr WORDSIZE32 271733878) : int32;
        secret (@repr WORDSIZE32 3285377520) : int32
      ] in  l).

Definition compress (m_bytes_1210 : block_bytes_t) (h_1211 : hash_t) : hash_t :=
  let m_1212 : seq uint32 :=
    array_to_be_uint32s (m_bytes_1210) in 
  let w_1213 : schedule_t :=
    array_new_ (default : uint32) (80) in 
  let w_1213 :=
    foldi (usize 0) (usize 80) (fun t_1214 w_1213 =>
      let '(w_1213) :=
        if (t_1214) <.? (usize 16):bool then (let w_1213 :=
            array_upd w_1213 (t_1214) (seq_index (m_1212) (t_1214)) in 
          (w_1213)) else (let w_1213 :=
            array_upd w_1213 (t_1214) (uint32_rotate_left ((((array_index (
                        w_1213) ((t_1214) - (usize 3))) .^ (array_index (
                        w_1213) ((t_1214) - (usize 8)))) .^ (array_index (
                      w_1213) ((t_1214) - (usize 14)))) .^ (array_index (
                    w_1213) ((t_1214) - (usize 16)))) (usize 1)) in 
          (w_1213)) in 
      (w_1213))
    w_1213 in 
  let a_1215 : uint32 :=
    array_index (h_1211) (usize 0) in 
  let b_1216 : uint32 :=
    array_index (h_1211) (usize 1) in 
  let c_1217 : uint32 :=
    array_index (h_1211) (usize 2) in 
  let d_1218 : uint32 :=
    array_index (h_1211) (usize 3) in 
  let e_1219 : uint32 :=
    array_index (h_1211) (usize 4) in 
  let '(a_1215, b_1216, c_1217, d_1218, e_1219) :=
    foldi (usize 0) (usize 80) (fun t_1220 '(
        a_1215,
        b_1216,
        c_1217,
        d_1218,
        e_1219
      ) =>
      let t_1221 : uint32 :=
        uint32_zero  in 
      let '(t_1221) :=
        if ((usize 0) <=.? (t_1220)) && ((t_1220) <.? (usize 20)):bool then (
          let t_1221 :=
            ((((uint32_rotate_left (a_1215) (usize 5)) .+ (ch (b_1216) (
                      c_1217) (d_1218))) .+ (e_1219)) .+ (secret (
                  @repr WORDSIZE32 1518500249) : int32)) .+ (array_index (
                w_1213) (t_1220)) in 
          (t_1221)) else ((t_1221)) in 
      let '(t_1221) :=
        if ((usize 20) <=.? (t_1220)) && ((t_1220) <.? (usize 40)):bool then (
          let t_1221 :=
            ((((uint32_rotate_left (a_1215) (usize 5)) .+ (parity (b_1216) (
                      c_1217) (d_1218))) .+ (e_1219)) .+ (secret (
                  @repr WORDSIZE32 1859775393) : int32)) .+ (array_index (
                w_1213) (t_1220)) in 
          (t_1221)) else ((t_1221)) in 
      let '(t_1221) :=
        if ((usize 40) <=.? (t_1220)) && ((t_1220) <.? (usize 60)):bool then (
          let t_1221 :=
            ((((uint32_rotate_left (a_1215) (usize 5)) .+ (maj (b_1216) (
                      c_1217) (d_1218))) .+ (e_1219)) .+ (secret (
                  @repr WORDSIZE32 2400959708) : int32)) .+ (array_index (
                w_1213) (t_1220)) in 
          (t_1221)) else ((t_1221)) in 
      let '(t_1221) :=
        if ((usize 60) <=.? (t_1220)) && ((t_1220) <.? (usize 80)):bool then (
          let t_1221 :=
            ((((uint32_rotate_left (a_1215) (usize 5)) .+ (parity (b_1216) (
                      c_1217) (d_1218))) .+ (e_1219)) .+ (secret (
                  @repr WORDSIZE32 3395469782) : int32)) .+ (array_index (
                w_1213) (t_1220)) in 
          (t_1221)) else ((t_1221)) in 
      let e_1219 :=
        d_1218 in 
      let d_1218 :=
        c_1217 in 
      let c_1217 :=
        uint32_rotate_left (b_1216) (usize 30) in 
      let b_1216 :=
        a_1215 in 
      let a_1215 :=
        t_1221 in 
      (a_1215, b_1216, c_1217, d_1218, e_1219))
    (a_1215, b_1216, c_1217, d_1218, e_1219) in 
  let h_1211 :=
    array_upd h_1211 (usize 0) ((a_1215) .+ (array_index (h_1211) (
          usize 0))) in 
  let h_1211 :=
    array_upd h_1211 (usize 1) ((b_1216) .+ (array_index (h_1211) (
          usize 1))) in 
  let h_1211 :=
    array_upd h_1211 (usize 2) ((c_1217) .+ (array_index (h_1211) (
          usize 2))) in 
  let h_1211 :=
    array_upd h_1211 (usize 3) ((d_1218) .+ (array_index (h_1211) (
          usize 3))) in 
  let h_1211 :=
    array_upd h_1211 (usize 4) ((e_1219) .+ (array_index (h_1211) (
          usize 4))) in 
  h_1211.

Definition hash (msg_1222 : byte_seq) : sha1_digest_t :=
  let h_1223 : hash_t :=
    hash_init_v in 
  let h_1223 :=
    foldi (usize 0) (seq_num_exact_chunks (msg_1222) (
          block_bytes_v)) (fun i_1224 h_1223 =>
      let raw_bytes_1225 : seq uint8 :=
        seq_get_exact_chunk (msg_1222) (block_bytes_v) (i_1224) in 
      let block_bytes_1226 : block_bytes_t :=
        array_from_seq (block_bytes_v) (raw_bytes_1225) in 
      let h_1223 :=
        compress (block_bytes_1226) (h_1223) in 
      (h_1223))
    h_1223 in 
  let raw_bytes_1227 : seq uint8 :=
    seq_get_remainder_chunk (msg_1222) (block_bytes_v) in 
  let block_bytes_1228 : block_bytes_t :=
    array_update_start (array_new_ (default : uint8) (block_bytes_v)) (
      raw_bytes_1227) in 
  let block_bytes_1228 :=
    array_upd block_bytes_1228 (seq_len (raw_bytes_1227)) (secret (
        @repr WORDSIZE8 128) : int8) in 
  let message_bitlength_1229 : uint64 :=
    secret (pub_u64 ((seq_len (msg_1222)) * (usize 8))) : int64 in 
  let '(h_1223, block_bytes_1228) :=
    if (seq_len (raw_bytes_1227)) <.? ((block_bytes_v) - (
        bitlength_bytes_v)):bool then (let block_bytes_1228 :=
        array_update (block_bytes_1228) ((block_bytes_v) - (
            bitlength_bytes_v)) (array_to_seq (uint64_to_be_bytes (
            message_bitlength_1229))) in 
      let h_1223 :=
        compress (block_bytes_1228) (h_1223) in 
      (h_1223, block_bytes_1228)) else (let h_1223 :=
        compress (block_bytes_1228) (h_1223) in 
      let pad_block_1230 : block_bytes_t :=
        array_new_ (default : uint8) (block_bytes_v) in 
      let pad_block_1230 :=
        array_update (pad_block_1230) ((block_bytes_v) - (bitlength_bytes_v)) (
          array_to_seq (uint64_to_be_bytes (message_bitlength_1229))) in 
      let h_1223 :=
        compress (pad_block_1230) (h_1223) in 
      (h_1223, block_bytes_1228)) in 
  array_from_seq (hash_bytes_v) (array_to_be_bytes (h_1223)).

Definition sha1 (msg_1231 : byte_seq) : sha1_digest_t :=
  hash (msg_1231).

