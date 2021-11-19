module Hacspec.Sha3

#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"

open FStar.Mul

open Hacspec.Lib

let rounds_v:uint_size = usize 24

let sha3224_rate_v:uint_size = usize 144

let sha3256_rate_v:uint_size = usize 136

let sha3384_rate_v:uint_size = usize 104

let sha3512_rate_v:uint_size = usize 72

let shake128_rate_v:uint_size = usize 168

let shake256_rate_v:uint_size = usize 136

type state_t = lseq (uint64) (usize 25)

type row_t = lseq (uint64) (usize 5)

type digest224_t = lseq (uint8) (usize 28)

type digest256_t = lseq (uint8) (usize 32)

type digest384_t = lseq (uint8) (usize 48)

type digest512_t = lseq (uint8) (usize 64)

type round_constants_t = lseq (pub_uint64) (rounds_v)

type rotation_constants_t = lseq (uint_size) (usize 25)

let roundconstants_v:round_constants_t =
  array_from_list (let l =
        [
          pub_u64 0x1; pub_u64 0x8082; pub_u64 0x800000000000808a; pub_u64 0x8000000080008000;
          pub_u64 0x808b; pub_u64 0x80000001; pub_u64 0x8000000080008081; pub_u64 0x8000000000008009;
          pub_u64 0x8a; pub_u64 0x88; pub_u64 0x80008009; pub_u64 0x8000000a; pub_u64 0x8000808b;
          pub_u64 0x800000000000008b; pub_u64 0x8000000000008089; pub_u64 0x8000000000008003;
          pub_u64 0x8000000000008002; pub_u64 0x8000000000000080; pub_u64 0x800a;
          pub_u64 0x800000008000000a; pub_u64 0x8000000080008081; pub_u64 0x8000000000008080;
          pub_u64 0x80000001; pub_u64 0x8000000080008008
        ]
      in
      assert_norm (List.Tot.length l == 24);
      l)

let rotc_v:rotation_constants_t =
  array_from_list (let l =
        [
          usize 0; usize 1; usize 62; usize 28; usize 27; usize 36; usize 44; usize 6; usize 55;
          usize 20; usize 3; usize 10; usize 43; usize 25; usize 39; usize 41; usize 45; usize 15;
          usize 21; usize 8; usize 18; usize 2; usize 61; usize 56; usize 14
        ]
      in
      assert_norm (List.Tot.length l == 25);
      l)

let pi_v:rotation_constants_t =
  array_from_list (let l =
        [
          usize 0; usize 6; usize 12; usize 18; usize 24; usize 3; usize 9; usize 10; usize 16;
          usize 22; usize 1; usize 7; usize 13; usize 19; usize 20; usize 4; usize 5; usize 11;
          usize 17; usize 23; usize 2; usize 8; usize 14; usize 15; usize 21
        ]
      in
      assert_norm (List.Tot.length l == 25);
      l)

let theta (s_0: state_t) : state_t =
  let b_1 = array_new_ (secret (pub_u64 0x0)) (5) in
  let b_1 =
    foldi (usize 0)
      (usize 5)
      (fun i_2 b_1 ->
          let b_1 =
            array_upd b_1
              (i_2)
              (((((array_index (s_0) (i_2)) ^. (array_index (s_0) ((i_2) + (usize 5)))) ^.
                    (array_index (s_0) ((i_2) + (usize 10)))) ^.
                  (array_index (s_0) ((i_2) + (usize 15)))) ^.
                (array_index (s_0) ((i_2) + (usize 20))))
          in
          (b_1))
      (b_1)
  in
  let s_0 =
    foldi (usize 0)
      (usize 5)
      (fun i_3 s_0 ->
          let u_4:uint64 = array_index (b_1) (((i_3) + (usize 1)) % (usize 5)) in
          let t_5 =
            (array_index (b_1) (((i_3) + (usize 4)) % (usize 5))) ^.
            (uint64_rotate_left (u_4) (usize 1))
          in
          let s_0 =
            foldi (usize 0)
              (usize 5)
              (fun j_6 s_0 ->
                  let s_0 =
                    array_upd s_0
                      (((usize 5) * (j_6)) + (i_3))
                      ((array_index (s_0) (((usize 5) * (j_6)) + (i_3))) ^. (t_5))
                  in
                  (s_0))
              (s_0)
          in
          (s_0))
      (s_0)
  in
  s_0

let rho (s_7: state_t) : state_t =
  let s_7 =
    foldi (usize 0)
      (usize 25)
      (fun i_8 s_7 ->
          let u_9:uint64 = array_index (s_7) (i_8) in
          let s_7 = array_upd s_7 (i_8) (uint64_rotate_left (u_9) (array_index (rotc_v) (i_8))) in
          (s_7))
      (s_7)
  in
  s_7

let pi (s_10: state_t) : state_t =
  let v_11 = array_new_ (secret (pub_u64 0x0)) (25) in
  let v_11 =
    foldi (usize 0)
      (usize 25)
      (fun i_12 v_11 ->
          let v_11 = array_upd v_11 (i_12) (array_index (s_10) (array_index (pi_v) (i_12))) in
          (v_11))
      (v_11)
  in
  v_11

let chi (s_13: state_t) : state_t =
  let b_14 = array_new_ (secret (pub_u64 0x0)) (5) in
  let s_13, b_14 =
    foldi (usize 0)
      (usize 5)
      (fun i_15 (s_13, b_14) ->
          let b_14 =
            foldi (usize 0)
              (usize 5)
              (fun j_16 b_14 ->
                  let b_14 =
                    array_upd b_14 (j_16) (array_index (s_13) (((usize 5) * (i_15)) + (j_16)))
                  in
                  (b_14))
              (b_14)
          in
          let s_13 =
            foldi (usize 0)
              (usize 5)
              (fun j_17 s_13 ->
                  let u_18:uint64 = array_index (b_14) (((j_17) + (usize 1)) % (usize 5)) in
                  let s_13 =
                    array_upd s_13
                      (((usize 5) * (i_15)) + (j_17))
                      ((array_index (s_13) (((usize 5) * (i_15)) + (j_17))) ^.
                        ((~.(u_18)) &. (array_index (b_14) (((j_17) + (usize 2)) % (usize 5)))))
                  in
                  (s_13))
              (s_13)
          in
          (s_13, b_14))
      (s_13, b_14)
  in
  s_13

let iota (s_19: state_t) (rndconst_20: pub_uint64) : state_t =
  let s_19 =
    array_upd s_19 (usize 0) ((array_index (s_19) (usize 0)) ^. (uint64_classify (rndconst_20)))
  in
  s_19

let keccakf1600 (s_21: state_t) : state_t =
  let s_21 =
    foldi (usize 0)
      (rounds_v)
      (fun i_22 s_21 ->
          let s_21 = theta (s_21) in
          let s_21 = rho (s_21) in
          let s_21 = pi (s_21) in
          let s_21 = chi (s_21) in
          let s_21 = iota (s_21) (array_index (roundconstants_v) (i_22)) in
          (s_21))
      (s_21)
  in
  s_21

let absorb_block (s_23: state_t) (block_24: byte_seq) : state_t =
  let s_23 =
    foldi (usize 0)
      (seq_len (block_24))
      (fun i_25 s_23 ->
          let w_26 = (i_25) `usize_shift_right` (pub_u32 0x3) in
          let o_27 = (usize 8) * ((i_25) `usize_bit_and` (usize 7)) in
          let s_23 =
            array_upd s_23
              (w_26)
              ((array_index (s_23) (w_26)) ^.
                ((uint64_from_uint8 (seq_index (block_24) (i_25))) `shift_left` (o_27)))
          in
          (s_23))
      (s_23)
  in
  keccakf1600 (s_23)

let squeeze (s_28: state_t) (nbytes_29 rate_30: uint_size) : byte_seq =
  let out_31 = seq_new_ (secret (pub_u8 0x0)) (nbytes_29) in
  let s_28, out_31 =
    foldi (usize 0)
      (nbytes_29)
      (fun i_32 (s_28, out_31) ->
          let pos_33 = (i_32) % (rate_30) in
          let w_34 = (pos_33) `usize_shift_right` (pub_u32 0x3) in
          let o_35 = (usize 8) * ((pos_33) `usize_bit_and` (usize 7)) in
          let b_36 =
            ((array_index (s_28) (w_34)) `shift_right` (o_35)) &. (uint64_classify (pub_u64 0xff))
          in
          let out_31 = seq_upd out_31 (i_32) (uint8_from_uint64 (b_36)) in
          let s_28 =
            if (((i_32) + (usize 1)) % (rate_30)) = (usize 0)
            then
              let s_28 = keccakf1600 (s_28) in
              (s_28)
            else (s_28)
          in
          (s_28, out_31))
      (s_28, out_31)
  in
  out_31

let keccak (rate_37: uint_size) (data_38: byte_seq) (p_39: pub_uint8) (outbytes_40: uint_size)
    : byte_seq =
  let buf_41 = seq_new_ (secret (pub_u8 0x0)) (rate_37) in
  let last_block_len_42 = usize 0 in
  let s_43 = array_new_ (secret (pub_u64 0x0)) (25) in
  let buf_41, last_block_len_42, s_43 =
    foldi (usize 0)
      (seq_num_chunks (data_38) (rate_37))
      (fun i_44 (buf_41, last_block_len_42, s_43) ->
          let block_len_45, block_46 = seq_get_chunk (data_38) (rate_37) (i_44) in
          let buf_41, last_block_len_42, s_43 =
            if (block_len_45) = (rate_37)
            then
              let s_43 = absorb_block (s_43) (block_46) in
              (buf_41, last_block_len_42, s_43)
            else
              let buf_41 = seq_update_start (buf_41) (block_46) in
              let last_block_len_42 = block_len_45 in
              (buf_41, last_block_len_42, s_43)
          in
          (buf_41, last_block_len_42, s_43))
      (buf_41, last_block_len_42, s_43)
  in
  let buf_41 = seq_upd buf_41 (last_block_len_42) (secret (p_39)) in
  let buf_41 =
    seq_upd buf_41
      ((rate_37) - (usize 1))
      ((seq_index (buf_41) ((rate_37) - (usize 1))) |. (secret (pub_u8 0x80)))
  in
  let s_43 = absorb_block (s_43) (buf_41) in
  squeeze (s_43) (outbytes_40) (rate_37)

let sha3224 (data_47: byte_seq) : digest224_t =
  let t_48 = keccak (sha3224_rate_v) (data_47) (pub_u8 0x6) (usize 28) in
  array_from_seq (28) (t_48)

let sha3256 (data_49: byte_seq) : digest256_t =
  let t_50 = keccak (sha3256_rate_v) (data_49) (pub_u8 0x6) (usize 32) in
  array_from_seq (32) (t_50)

let sha3384 (data_51: byte_seq) : digest384_t =
  let t_52 = keccak (sha3384_rate_v) (data_51) (pub_u8 0x6) (usize 48) in
  array_from_seq (48) (t_52)

let sha3512 (data_53: byte_seq) : digest512_t =
  let t_54 = keccak (sha3512_rate_v) (data_53) (pub_u8 0x6) (usize 64) in
  array_from_seq (64) (t_54)

let shake128 (data_55: byte_seq) (outlen_56: uint_size) : byte_seq =
  keccak (shake128_rate_v) (data_55) (pub_u8 0x1f) (outlen_56)

let shake256 (data_57: byte_seq) (outlen_58: uint_size) : byte_seq =
  keccak (shake256_rate_v) (data_57) (pub_u8 0x1f) (outlen_58)

