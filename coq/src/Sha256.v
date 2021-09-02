Require Import Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
Require Import Hacspec.Lib.

Definition block_size : uint_size :=
  usize 64.

Definition len_size : uint_size :=
  usize 8.

Definition k_size : uint_size :=
  usize 64.

Definition hash_size : uint_size :=
  (usize 256) / (usize 8).

Definition block := nseq (uint8) (block_size).

Definition op_table_type := nseq (uint_size) (usize 12).

Definition digest := nseq (uint8) (hash_size).

Definition round_constants_table := nseq (uint32) (k_size).

Definition hash := nseq (uint32) (usize 8).

Definition ch (x_0 : uint32) (y_1 : uint32) (z_2 : uint32) : uint32 :=
  ((x_0) .& (y_1)) .^ ((not (x_0)) .& (z_2)).

Definition maj (x_3 : uint32) (y_4 : uint32) (z_5 : uint32) : uint32 :=
  ((x_3) .& (y_4)) .^ (((x_3) .& (z_5)) .^ ((y_4) .& (z_5))).

Definition op_table : op_table_type :=
  array_from_list uint_size (
    let l :=
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

Definition k_table : round_constants_table :=
  array_from_list uint32 (
    let l :=
      [
        secret (repr 1116352408);
        secret (repr 1899447441);
        secret (repr 3049323471);
        secret (repr 3921009573);
        secret (repr 961987163);
        secret (repr 1508970993);
        secret (repr 2453635748);
        secret (repr 2870763221);
        secret (repr 3624381080);
        secret (repr 310598401);
        secret (repr 607225278);
        secret (repr 1426881987);
        secret (repr 1925078388);
        secret (repr 2162078206);
        secret (repr 2614888103);
        secret (repr 3248222580);
        secret (repr 3835390401);
        secret (repr 4022224774);
        secret (repr 264347078);
        secret (repr 604807628);
        secret (repr 770255983);
        secret (repr 1249150122);
        secret (repr 1555081692);
        secret (repr 1996064986);
        secret (repr 2554220882);
        secret (repr 2821834349);
        secret (repr 2952996808);
        secret (repr 3210313671);
        secret (repr 3336571891);
        secret (repr 3584528711);
        secret (repr 113926993);
        secret (repr 338241895);
        secret (repr 666307205);
        secret (repr 773529912);
        secret (repr 1294757372);
        secret (repr 1396182291);
        secret (repr 1695183700);
        secret (repr 1986661051);
        secret (repr 2177026350);
        secret (repr 2456956037);
        secret (repr 2730485921);
        secret (repr 2820302411);
        secret (repr 3259730800);
        secret (repr 3345764771);
        secret (repr 3516065817);
        secret (repr 3600352804);
        secret (repr 4094571909);
        secret (repr 275423344);
        secret (repr 430227734);
        secret (repr 506948616);
        secret (repr 659060556);
        secret (repr 883997877);
        secret (repr 958139571);
        secret (repr 1322822218);
        secret (repr 1537002063);
        secret (repr 1747873779);
        secret (repr 1955562222);
        secret (repr 2024104815);
        secret (repr 2227730452);
        secret (repr 2361852424);
        secret (repr 2428436474);
        secret (repr 2756734187);
        secret (repr 3204031479);
        secret (repr 3329325298)
      ] in  l).

Definition hash_init : hash :=
  array_from_list uint32 (
    let l :=
      [
        secret (repr 1779033703);
        secret (repr 3144134277);
        secret (repr 1013904242);
        secret (repr 2773480762);
        secret (repr 1359893119);
        secret (repr 2600822924);
        secret (repr 528734635);
        secret (repr 1541459225)
      ] in  l).

Definition sigma (x_6 : uint32) (i_7 : uint_size) (op_8 : uint_size) : uint32 :=
  let tmp_9 : uint32 :=
    uint32_rotate_right (x_6) (
      array_index (op_table) (((usize 3) * (i_7)) + (usize 2))) in 
  let '(tmp_9) :=
    if (op_8) =.? (usize 0):bool then (
      let tmp_9 :=
        (x_6) shift_right (
          array_index (op_table) (((usize 3) * (i_7)) + (usize 2))) in 
      (tmp_9)
    ) else ( (tmp_9)
    ) in 
  (
    (
      uint32_rotate_right (x_6) (
        array_index (op_table) ((usize 3) * (i_7)))) .^ (
      uint32_rotate_right (x_6) (
        array_index (op_table) (((usize 3) * (i_7)) + (usize 1))))) .^ (tmp_9).

Definition schedule (block_10 : block) : round_constants_table :=
  let b_11 :=
    array_to_be_uint32s (block_10) in 
  let s_12 :=
    array_new_ (secret (repr 0)) (k_size) in 
  let s_12 :=
    foldi (usize 0) (k_size) (fun i_13 s_12 =>
      let '(s_12) :=
        if (i_13) <.? (usize 16):bool then (
          let s_12 :=
            array_upd s_12 (i_13) (seq_index (b_11) (i_13)) in 
          (s_12)
        ) else (
          let t16_14 :=
            array_index (s_12) ((i_13) - (usize 16)) in 
          let t15_15 :=
            array_index (s_12) ((i_13) - (usize 15)) in 
          let t7_16 :=
            array_index (s_12) ((i_13) - (usize 7)) in 
          let t2_17 :=
            array_index (s_12) ((i_13) - (usize 2)) in 
          let s1_18 :=
            sigma (t2_17) (usize 3) (usize 0) in 
          let s0_19 :=
            sigma (t15_15) (usize 2) (usize 0) in 
          let s_12 :=
            array_upd s_12 (i_13) (
              (((s1_18) .+ (t7_16)) .+ (s0_19)) .+ (t16_14)) in 
          (s_12)
        ) in 
      (s_12))
    s_12 in 
  s_12.

Definition shuffle (ws_20 : round_constants_table) (hashi_21 : hash) : hash :=
  let h_22 :=
    hashi_21 in 
  let h_22 :=
    foldi (usize 0) (k_size) (fun i_23 h_22 =>
      let a0_24 :=
        array_index (h_22) (usize 0) in 
      let b0_25 :=
        array_index (h_22) (usize 1) in 
      let c0_26 :=
        array_index (h_22) (usize 2) in 
      let d0_27 :=
        array_index (h_22) (usize 3) in 
      let e0_28 :=
        array_index (h_22) (usize 4) in 
      let f0_29 :=
        array_index (h_22) (usize 5) in 
      let g0_30 :=
        array_index (h_22) (usize 6) in 
      let h0_31 : uint32 :=
        array_index (h_22) (usize 7) in 
      let t1_32 :=
        (
          (
            ((h0_31) .+ (sigma (e0_28) (usize 1) (usize 1))) .+ (
              ch (e0_28) (f0_29) (g0_30))) .+ (
            array_index (k_table) (i_23))) .+ (array_index (ws_20) (i_23)) in 
      let t2_33 :=
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

Definition compress (block_34 : block) (h_in_35 : hash) : hash :=
  let s_36 :=
    schedule (block_34) in 
  let h_37 :=
    shuffle (s_36) (h_in_35) in 
  let h_37 :=
    foldi (usize 0) (usize 8) (fun i_38 h_37 =>
      let h_37 :=
        array_upd h_37 (i_38) (
          (array_index (h_37) (i_38)) .+ (array_index (h_in_35) (i_38))) in 
      (h_37))
    h_37 in 
  h_37.

Definition hash_ (msg_39 : byte_seq) : digest :=
  let h_40 :=
    hash_init in 
  let last_block_41 :=
    array_new_ (secret (repr 0)) (block_size) in 
  let last_block_len_42 :=
    usize 0 in 
  let '(h_40, last_block_41, last_block_len_42) :=
    foldi (usize 0) (seq_num_chunks (msg_39) (block_size)) (fun i_43 '(
        h_40,
        last_block_41,
        last_block_len_42
      ) =>
      let '(block_len_44, block_45) :=
        seq_get_chunk (msg_39) (block_size) (i_43) in 
      let '(h_40, last_block_41, last_block_len_42) :=
        if (block_len_44) <.? (block_size):bool then (
          let last_block_41 :=
            array_update_start (array_new_ (secret (repr 0)) (block_size)) (
              block_45) in 
          let last_block_len_42 :=
            block_len_44 in 
          (h_40, last_block_41, last_block_len_42)
        ) else (
          let compress_input_46 :=
            array_from_seq (block_size) (block_45) in 
          let h_40 :=
            compress (compress_input_46) (h_40) in 
          (h_40, last_block_41, last_block_len_42)
        ) in 
      (h_40, last_block_41, last_block_len_42))
    (h_40, last_block_41, last_block_len_42) in 
  let last_block_41 :=
    array_upd last_block_41 (last_block_len_42) (secret (repr 128)) in 
  let len_bist_47 :=
    secret (pub_u64 ((seq_len (msg_39)) * (usize 8))) in 
  let '(h_40, last_block_41) :=
    if (last_block_len_42) <.? ((block_size) - (len_size)):bool then (
      let last_block_41 :=
        array_update (last_block_41) ((block_size) - (len_size)) (
          uint64_to_be_bytes (len_bist_47)) in 
      let h_40 :=
        compress (last_block_41) (h_40) in 
      (h_40, last_block_41)
    ) else (
      let pad_block_48 :=
        array_new_ (secret (repr 0)) (block_size) in 
      let pad_block_48 :=
        array_update (pad_block_48) ((block_size) - (len_size)) (
          uint64_to_be_bytes (len_bist_47)) in 
      let h_40 :=
        compress (last_block_41) (h_40) in 
      let h_40 :=
        compress (pad_block_48) (h_40) in 
      (h_40, last_block_41)
    ) in 
  array_from_seq (hash_size) (array_to_be_bytes (h_40)).

