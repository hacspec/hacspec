module Hacspec.Sha256

#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"

open FStar.Mul

open Hacspec.Lib

let block_size_v:uint_size = usize 64

let len_size_v:uint_size = usize 8

let k_size_v:uint_size = usize 64

let hash_size_v:uint_size = (usize 256) / (usize 8)

type block_t = lseq (uint8) (block_size_v)

type op_table_type_t = lseq (uint_size) (usize 12)

type sha256_digest_t = lseq (uint8) (hash_size_v)

type round_constants_table_t = lseq (uint32) (k_size_v)

type hash_t = lseq (uint32) (usize 8)

let ch (x_0 y_1 z_2: uint32) : uint32 = ((x_0) &. (y_1)) ^. ((~.(x_0)) &. (z_2))

let maj (x_3 y_4 z_5: uint32) : uint32 = ((x_3) &. (y_4)) ^. (((x_3) &. (z_5)) ^. ((y_4) &. (z_5)))

let op_table_v:op_table_type_t =
  array_from_list (let l =
        [
          usize 2; usize 13; usize 22; usize 6; usize 11; usize 25; usize 7; usize 18; usize 3;
          usize 17; usize 19; usize 10
        ]
      in
      assert_norm (List.Tot.length l == 12);
      l)

let k_table_v:round_constants_table_t =
  array_from_list (let l =
        [
          secret (pub_u32 0x428a2f98); secret (pub_u32 0x71374491); secret (pub_u32 0xb5c0fbcf);
          secret (pub_u32 0xe9b5dba5); secret (pub_u32 0x3956c25b); secret (pub_u32 0x59f111f1);
          secret (pub_u32 0x923f82a4); secret (pub_u32 0xab1c5ed5); secret (pub_u32 0xd807aa98);
          secret (pub_u32 0x12835b01); secret (pub_u32 0x243185be); secret (pub_u32 0x550c7dc3);
          secret (pub_u32 0x72be5d74); secret (pub_u32 0x80deb1fe); secret (pub_u32 0x9bdc06a7);
          secret (pub_u32 0xc19bf174); secret (pub_u32 0xe49b69c1); secret (pub_u32 0xefbe4786);
          secret (pub_u32 0xfc19dc6); secret (pub_u32 0x240ca1cc); secret (pub_u32 0x2de92c6f);
          secret (pub_u32 0x4a7484aa); secret (pub_u32 0x5cb0a9dc); secret (pub_u32 0x76f988da);
          secret (pub_u32 0x983e5152); secret (pub_u32 0xa831c66d); secret (pub_u32 0xb00327c8);
          secret (pub_u32 0xbf597fc7); secret (pub_u32 0xc6e00bf3); secret (pub_u32 0xd5a79147);
          secret (pub_u32 0x6ca6351); secret (pub_u32 0x14292967); secret (pub_u32 0x27b70a85);
          secret (pub_u32 0x2e1b2138); secret (pub_u32 0x4d2c6dfc); secret (pub_u32 0x53380d13);
          secret (pub_u32 0x650a7354); secret (pub_u32 0x766a0abb); secret (pub_u32 0x81c2c92e);
          secret (pub_u32 0x92722c85); secret (pub_u32 0xa2bfe8a1); secret (pub_u32 0xa81a664b);
          secret (pub_u32 0xc24b8b70); secret (pub_u32 0xc76c51a3); secret (pub_u32 0xd192e819);
          secret (pub_u32 0xd6990624); secret (pub_u32 0xf40e3585); secret (pub_u32 0x106aa070);
          secret (pub_u32 0x19a4c116); secret (pub_u32 0x1e376c08); secret (pub_u32 0x2748774c);
          secret (pub_u32 0x34b0bcb5); secret (pub_u32 0x391c0cb3); secret (pub_u32 0x4ed8aa4a);
          secret (pub_u32 0x5b9cca4f); secret (pub_u32 0x682e6ff3); secret (pub_u32 0x748f82ee);
          secret (pub_u32 0x78a5636f); secret (pub_u32 0x84c87814); secret (pub_u32 0x8cc70208);
          secret (pub_u32 0x90befffa); secret (pub_u32 0xa4506ceb); secret (pub_u32 0xbef9a3f7);
          secret (pub_u32 0xc67178f2)
        ]
      in
      assert_norm (List.Tot.length l == 64);
      l)

let hash_init_v:hash_t =
  array_from_list (let l =
        [
          secret (pub_u32 0x6a09e667);
          secret (pub_u32 0xbb67ae85);
          secret (pub_u32 0x3c6ef372);
          secret (pub_u32 0xa54ff53a);
          secret (pub_u32 0x510e527f);
          secret (pub_u32 0x9b05688c);
          secret (pub_u32 0x1f83d9ab);
          secret (pub_u32 0x5be0cd19)
        ]
      in
      assert_norm (List.Tot.length l == 8);
      l)

let sigma (x_6: uint32) (i_7 op_8: uint_size) : uint32 =
  let tmp_9:uint32 =
    uint32_rotate_right (x_6) (array_index (op_table_v) (((usize 3) * (i_7)) + (usize 2)))
  in
  let tmp_9 =
    if (op_8) = (usize 0)
    then
      let tmp_9 =
        (x_6) `shift_right` (array_index (op_table_v) (((usize 3) * (i_7)) + (usize 2)))
      in
      (tmp_9)
    else (tmp_9)
  in
  ((uint32_rotate_right (x_6) (array_index (op_table_v) ((usize 3) * (i_7)))) ^.
    (uint32_rotate_right (x_6) (array_index (op_table_v) (((usize 3) * (i_7)) + (usize 1))))) ^.
  (tmp_9)

let schedule (block_10: block_t) : round_constants_table_t =
  let b_11 = array_to_be_uint32s (block_10) in
  let s_12 = array_new_ (secret (pub_u32 0x0)) (k_size_v) in
  let s_12 =
    foldi (usize 0)
      (k_size_v)
      (fun i_13 s_12 ->
          let s_12 =
            if (i_13) < (usize 16)
            then
              let s_12 = array_upd s_12 (i_13) (seq_index (b_11) (i_13)) in
              (s_12)
            else
              let t16_14 = array_index (s_12) ((i_13) - (usize 16)) in
              let t15_15 = array_index (s_12) ((i_13) - (usize 15)) in
              let t7_16 = array_index (s_12) ((i_13) - (usize 7)) in
              let t2_17 = array_index (s_12) ((i_13) - (usize 2)) in
              let s1_18 = sigma (t2_17) (usize 3) (usize 0) in
              let s0_19 = sigma (t15_15) (usize 2) (usize 0) in
              let s_12 = array_upd s_12 (i_13) ((((s1_18) +. (t7_16)) +. (s0_19)) +. (t16_14)) in
              (s_12)
          in
          (s_12))
      (s_12)
  in
  s_12

let shuffle (ws_20: round_constants_table_t) (hashi_21: hash_t) : hash_t =
  let h_22 = hashi_21 in
  let h_22 =
    foldi (usize 0)
      (k_size_v)
      (fun i_23 h_22 ->
          let a0_24 = array_index (h_22) (usize 0) in
          let b0_25 = array_index (h_22) (usize 1) in
          let c0_26 = array_index (h_22) (usize 2) in
          let d0_27 = array_index (h_22) (usize 3) in
          let e0_28 = array_index (h_22) (usize 4) in
          let f0_29 = array_index (h_22) (usize 5) in
          let g0_30 = array_index (h_22) (usize 6) in
          let h0_31:uint32 = array_index (h_22) (usize 7) in
          let t1_32 =
            ((((h0_31) +. (sigma (e0_28) (usize 1) (usize 1))) +. (ch (e0_28) (f0_29) (g0_30))) +.
              (array_index (k_table_v) (i_23))) +.
            (array_index (ws_20) (i_23))
          in
          let t2_33 = (sigma (a0_24) (usize 0) (usize 1)) +. (maj (a0_24) (b0_25) (c0_26)) in
          let h_22 = array_upd h_22 (usize 0) ((t1_32) +. (t2_33)) in
          let h_22 = array_upd h_22 (usize 1) (a0_24) in
          let h_22 = array_upd h_22 (usize 2) (b0_25) in
          let h_22 = array_upd h_22 (usize 3) (c0_26) in
          let h_22 = array_upd h_22 (usize 4) ((d0_27) +. (t1_32)) in
          let h_22 = array_upd h_22 (usize 5) (e0_28) in
          let h_22 = array_upd h_22 (usize 6) (f0_29) in
          let h_22 = array_upd h_22 (usize 7) (g0_30) in
          (h_22))
      (h_22)
  in
  h_22

let compress (block_34: block_t) (h_in_35: hash_t) : hash_t =
  let s_36 = schedule (block_34) in
  let h_37 = shuffle (s_36) (h_in_35) in
  let h_37 =
    foldi (usize 0)
      (usize 8)
      (fun i_38 h_37 ->
          let h_37 =
            array_upd h_37 (i_38) ((array_index (h_37) (i_38)) +. (array_index (h_in_35) (i_38)))
          in
          (h_37))
      (h_37)
  in
  h_37

let hash (msg_39: byte_seq) : sha256_digest_t =
  let h_40 = hash_init_v in
  let last_block_41 = array_new_ (secret (pub_u8 0x0)) (block_size_v) in
  let last_block_len_42 = usize 0 in
  let h_40, last_block_41, last_block_len_42 =
    foldi (usize 0)
      (seq_num_chunks (msg_39) (block_size_v))
      (fun i_43 (h_40, last_block_41, last_block_len_42) ->
          let block_len_44, block_45 = seq_get_chunk (msg_39) (block_size_v) (i_43) in
          let h_40, last_block_41, last_block_len_42 =
            if (block_len_44) < (block_size_v)
            then
              let last_block_41 =
                array_update_start (array_new_ (secret (pub_u8 0x0)) (block_size_v)) (block_45)
              in
              let last_block_len_42 = block_len_44 in
              (h_40, last_block_41, last_block_len_42)
            else
              let compress_input_46 = array_from_seq (block_size_v) (block_45) in
              let h_40 = compress (compress_input_46) (h_40) in
              (h_40, last_block_41, last_block_len_42)
          in
          (h_40, last_block_41, last_block_len_42))
      (h_40, last_block_41, last_block_len_42)
  in
  let last_block_41 = array_upd last_block_41 (last_block_len_42) (secret (pub_u8 0x80)) in
  let len_bist_47 = secret (pub_u64 ((seq_len (msg_39)) * (usize 8))) in
  let h_40, last_block_41 =
    if (last_block_len_42) < ((block_size_v) - (len_size_v))
    then
      let last_block_41 =
        array_update (last_block_41)
          ((block_size_v) - (len_size_v))
          (uint64_to_be_bytes (len_bist_47))
      in
      let h_40 = compress (last_block_41) (h_40) in
      (h_40, last_block_41)
    else
      let pad_block_48 = array_new_ (secret (pub_u8 0x0)) (block_size_v) in
      let pad_block_48 =
        array_update (pad_block_48)
          ((block_size_v) - (len_size_v))
          (uint64_to_be_bytes (len_bist_47))
      in
      let h_40 = compress (last_block_41) (h_40) in
      let h_40 = compress (pad_block_48) (h_40) in
      (h_40, last_block_41)
  in
  array_from_seq (hash_size_v) (array_to_be_bytes (h_40))

let sha256 (msg_49: byte_seq) : sha256_digest_t = hash (msg_49)

