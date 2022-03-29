(** This file was automatically generated using Hacspec **)
Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
Require Import Hacspec_Lib.

Definition block_size_v : uint_size :=
  usize 64.

Definition len_size_v : uint_size :=
  usize 8.

Definition k_size_v : uint_size :=
  usize 64.

Definition hash_size_v : uint_size :=
  (usize 256) / (usize 8).

Definition block_t := nseq (uint8) (block_size_v).

Definition op_table_type_t := nseq (uint_size) (usize 12).

Definition sha256_digest_t := nseq (uint8) (hash_size_v).

Definition round_constants_table_t := nseq (uint32) (k_size_v).

Definition hash_t := nseq (uint32) (usize 8).

Definition ch (x_0 : uint32) (y_1 : uint32) (z_2 : uint32) : uint32 :=
  ((x_0) .& (y_1)) .^ ((not (x_0)) .& (z_2)).

Definition maj (x_3 : uint32) (y_4 : uint32) (z_5 : uint32) : uint32 :=
  ((x_3) .& (y_4)) .^ (((x_3) .& (z_5)) .^ ((y_4) .& (z_5))).

Definition op_table_v : op_table_type_t :=
  array_from_list uint_size (let l :=
      [
        usize 2;
        usize 13;
        usize 22;
        usize 6;
        usize 11;
        usize 25;
        usize 7;
        usize 18;
        usize 3;
        usize 17;
        usize 19;
        usize 10
      ] in  l).

Definition k_table_v : round_constants_table_t :=
  array_from_list uint32 (let l :=
      [
        secret (@repr WORDSIZE32 1116352408) : int32;
        secret (@repr WORDSIZE32 1899447441) : int32;
        secret (@repr WORDSIZE32 3049323471) : int32;
        secret (@repr WORDSIZE32 3921009573) : int32;
        secret (@repr WORDSIZE32 961987163) : int32;
        secret (@repr WORDSIZE32 1508970993) : int32;
        secret (@repr WORDSIZE32 2453635748) : int32;
        secret (@repr WORDSIZE32 2870763221) : int32;
        secret (@repr WORDSIZE32 3624381080) : int32;
        secret (@repr WORDSIZE32 310598401) : int32;
        secret (@repr WORDSIZE32 607225278) : int32;
        secret (@repr WORDSIZE32 1426881987) : int32;
        secret (@repr WORDSIZE32 1925078388) : int32;
        secret (@repr WORDSIZE32 2162078206) : int32;
        secret (@repr WORDSIZE32 2614888103) : int32;
        secret (@repr WORDSIZE32 3248222580) : int32;
        secret (@repr WORDSIZE32 3835390401) : int32;
        secret (@repr WORDSIZE32 4022224774) : int32;
        secret (@repr WORDSIZE32 264347078) : int32;
        secret (@repr WORDSIZE32 604807628) : int32;
        secret (@repr WORDSIZE32 770255983) : int32;
        secret (@repr WORDSIZE32 1249150122) : int32;
        secret (@repr WORDSIZE32 1555081692) : int32;
        secret (@repr WORDSIZE32 1996064986) : int32;
        secret (@repr WORDSIZE32 2554220882) : int32;
        secret (@repr WORDSIZE32 2821834349) : int32;
        secret (@repr WORDSIZE32 2952996808) : int32;
        secret (@repr WORDSIZE32 3210313671) : int32;
        secret (@repr WORDSIZE32 3336571891) : int32;
        secret (@repr WORDSIZE32 3584528711) : int32;
        secret (@repr WORDSIZE32 113926993) : int32;
        secret (@repr WORDSIZE32 338241895) : int32;
        secret (@repr WORDSIZE32 666307205) : int32;
        secret (@repr WORDSIZE32 773529912) : int32;
        secret (@repr WORDSIZE32 1294757372) : int32;
        secret (@repr WORDSIZE32 1396182291) : int32;
        secret (@repr WORDSIZE32 1695183700) : int32;
        secret (@repr WORDSIZE32 1986661051) : int32;
        secret (@repr WORDSIZE32 2177026350) : int32;
        secret (@repr WORDSIZE32 2456956037) : int32;
        secret (@repr WORDSIZE32 2730485921) : int32;
        secret (@repr WORDSIZE32 2820302411) : int32;
        secret (@repr WORDSIZE32 3259730800) : int32;
        secret (@repr WORDSIZE32 3345764771) : int32;
        secret (@repr WORDSIZE32 3516065817) : int32;
        secret (@repr WORDSIZE32 3600352804) : int32;
        secret (@repr WORDSIZE32 4094571909) : int32;
        secret (@repr WORDSIZE32 275423344) : int32;
        secret (@repr WORDSIZE32 430227734) : int32;
        secret (@repr WORDSIZE32 506948616) : int32;
        secret (@repr WORDSIZE32 659060556) : int32;
        secret (@repr WORDSIZE32 883997877) : int32;
        secret (@repr WORDSIZE32 958139571) : int32;
        secret (@repr WORDSIZE32 1322822218) : int32;
        secret (@repr WORDSIZE32 1537002063) : int32;
        secret (@repr WORDSIZE32 1747873779) : int32;
        secret (@repr WORDSIZE32 1955562222) : int32;
        secret (@repr WORDSIZE32 2024104815) : int32;
        secret (@repr WORDSIZE32 2227730452) : int32;
        secret (@repr WORDSIZE32 2361852424) : int32;
        secret (@repr WORDSIZE32 2428436474) : int32;
        secret (@repr WORDSIZE32 2756734187) : int32;
        secret (@repr WORDSIZE32 3204031479) : int32;
        secret (@repr WORDSIZE32 3329325298) : int32
      ] in  l).

Definition hash_init_v : hash_t :=
  array_from_list uint32 (let l :=
      [
        secret (@repr WORDSIZE32 1779033703) : int32;
        secret (@repr WORDSIZE32 3144134277) : int32;
        secret (@repr WORDSIZE32 1013904242) : int32;
        secret (@repr WORDSIZE32 2773480762) : int32;
        secret (@repr WORDSIZE32 1359893119) : int32;
        secret (@repr WORDSIZE32 2600822924) : int32;
        secret (@repr WORDSIZE32 528734635) : int32;
        secret (@repr WORDSIZE32 1541459225) : int32
      ] in  l).

Definition sigma (x_6 : uint32) (i_7 : uint_size) (op_8 : uint_size) : uint32 :=
  let tmp_9 : uint32 :=
    uint32_rotate_right (x_6) (array_index (op_table_v) (((usize 3) * (i_7)) + (
          usize 2))) in 
  let '(tmp_9) :=
    if (op_8) =.? (usize 0):bool then (let tmp_9 :=
        (x_6) shift_right (array_index (op_table_v) (((usize 3) * (i_7)) + (
              usize 2))) in 
      (tmp_9)) else ((tmp_9)) in 
  ((uint32_rotate_right (x_6) (array_index (op_table_v) ((usize 3) * (
            i_7)))) .^ (uint32_rotate_right (x_6) (array_index (op_table_v) (((
              usize 3) * (i_7)) + (usize 1))))) .^ (tmp_9).

Definition schedule (block_10 : block_t) : round_constants_table_t :=
  let b_11 : seq uint32 :=
    array_to_be_uint32s (block_10) in 
  let s_12 : round_constants_table_t :=
    array_new_ (default) (k_size_v) in 
  let s_12 :=
    foldi (usize 0) (k_size_v) (fun i_13 s_12 =>
      let '(s_12) :=
        if (i_13) <.? (usize 16):bool then (let s_12 :=
            array_upd s_12 (i_13) (seq_index (b_11) (i_13)) in 
          (s_12)) else (let t16_14 : uint32 :=
            array_index (s_12) ((i_13) - (usize 16)) in 
          let t15_15 : uint32 :=
            array_index (s_12) ((i_13) - (usize 15)) in 
          let t7_16 : uint32 :=
            array_index (s_12) ((i_13) - (usize 7)) in 
          let t2_17 : uint32 :=
            array_index (s_12) ((i_13) - (usize 2)) in 
          let s1_18 : uint32 :=
            sigma (t2_17) (usize 3) (usize 0) in 
          let s0_19 : uint32 :=
            sigma (t15_15) (usize 2) (usize 0) in 
          let s_12 :=
            array_upd s_12 (i_13) ((((s1_18) .+ (t7_16)) .+ (s0_19)) .+ (
                t16_14)) in 
          (s_12)) in 
      (s_12))
    s_12 in 
  s_12.

Definition shuffle
  (ws_20 : round_constants_table_t)
  (hashi_21 : hash_t)
  : hash_t :=
  let h_22 : hash_t :=
    hashi_21 in 
  let h_22 :=
    foldi (usize 0) (k_size_v) (fun i_23 h_22 =>
      let a0_24 : uint32 :=
        array_index (h_22) (usize 0) in 
      let b0_25 : uint32 :=
        array_index (h_22) (usize 1) in 
      let c0_26 : uint32 :=
        array_index (h_22) (usize 2) in 
      let d0_27 : uint32 :=
        array_index (h_22) (usize 3) in 
      let e0_28 : uint32 :=
        array_index (h_22) (usize 4) in 
      let f0_29 : uint32 :=
        array_index (h_22) (usize 5) in 
      let g0_30 : uint32 :=
        array_index (h_22) (usize 6) in 
      let h0_31 : uint32 :=
        array_index (h_22) (usize 7) in 
      let t1_32 : uint32 :=
        ((((h0_31) .+ (sigma (e0_28) (usize 1) (usize 1))) .+ (ch (e0_28) (
                f0_29) (g0_30))) .+ (array_index (k_table_v) (i_23))) .+ (
          array_index (ws_20) (i_23)) in 
      let t2_33 : uint32 :=
        (sigma (a0_24) (usize 0) (usize 1)) .+ (maj (a0_24) (b0_25) (c0_26)) in 
      let h_22 :=
        array_upd h_22 (usize 0) ((t1_32) .+ (t2_33)) in 
      let h_22 :=
        array_upd h_22 (usize 1) (a0_24) in 
      let h_22 :=
        array_upd h_22 (usize 2) (b0_25) in 
      let h_22 :=
        array_upd h_22 (usize 3) (c0_26) in 
      let h_22 :=
        array_upd h_22 (usize 4) ((d0_27) .+ (t1_32)) in 
      let h_22 :=
        array_upd h_22 (usize 5) (e0_28) in 
      let h_22 :=
        array_upd h_22 (usize 6) (f0_29) in 
      let h_22 :=
        array_upd h_22 (usize 7) (g0_30) in 
      (h_22))
    h_22 in 
  h_22.

Definition compress (block_34 : block_t) (h_in_35 : hash_t) : hash_t :=
  let s_36 : round_constants_table_t :=
    schedule (block_34) in 
  let h_37 : hash_t :=
    shuffle (s_36) (h_in_35) in 
  let h_37 :=
    foldi (usize 0) (usize 8) (fun i_38 h_37 =>
      let h_37 :=
        array_upd h_37 (i_38) ((array_index (h_37) (i_38)) .+ (array_index (
              h_in_35) (i_38))) in 
      (h_37))
    h_37 in 
  h_37.

Definition hash (msg_39 : byte_seq) : sha256_digest_t :=
  let h_40 : hash_t :=
    hash_init_v in 
  let last_block_41 : block_t :=
    array_new_ (default) (block_size_v) in 
  let last_block_len_42 : uint_size :=
    usize 0 in 
  let '(h_40, last_block_41, last_block_len_42) :=
    foldi (usize 0) (seq_num_chunks (msg_39) (block_size_v)) (fun i_43 '(
        h_40,
        last_block_41,
        last_block_len_42
      ) =>
      let '(block_len_44, block_45) :=
        seq_get_chunk (msg_39) (block_size_v) (i_43) in 
      let '(h_40, last_block_41, last_block_len_42) :=
        if (block_len_44) <.? (block_size_v):bool then (let last_block_41 :=
            array_update_start (array_new_ (default) (block_size_v)) (
              block_45) in 
          let last_block_len_42 :=
            block_len_44 in 
          (h_40, last_block_41, last_block_len_42)) else (
          let compress_input_46 : block_t :=
            array_from_seq (block_size_v) (block_45) in 
          let h_40 :=
            compress (compress_input_46) (h_40) in 
          (h_40, last_block_41, last_block_len_42)) in 
      (h_40, last_block_41, last_block_len_42))
    (h_40, last_block_41, last_block_len_42) in 
  let last_block_41 :=
    array_upd last_block_41 (last_block_len_42) (secret (
        @repr WORDSIZE8 128) : int8) in 
  let len_bist_47 : uint64 :=
    secret (pub_u64 ((seq_len (msg_39)) * (usize 8))) : int64 in 
  let '(h_40, last_block_41) :=
    if (last_block_len_42) <.? ((block_size_v) - (len_size_v)):bool then (
      let last_block_41 :=
        array_update (last_block_41) ((block_size_v) - (len_size_v)) (
          uint64_to_be_bytes (len_bist_47)) in 
      let h_40 :=
        compress (last_block_41) (h_40) in 
      (h_40, last_block_41)) else (let pad_block_48 : block_t :=
        array_new_ (default) (block_size_v) in 
      let pad_block_48 :=
        array_update (pad_block_48) ((block_size_v) - (len_size_v)) (
          uint64_to_be_bytes (len_bist_47)) in 
      let h_40 :=
        compress (last_block_41) (h_40) in 
      let h_40 :=
        compress (pad_block_48) (h_40) in 
      (h_40, last_block_41)) in 
  array_from_seq (hash_size_v) (array_to_be_bytes (h_40)).

Definition sha256 (msg_49 : byte_seq) : sha256_digest_t :=
  hash (msg_49).

