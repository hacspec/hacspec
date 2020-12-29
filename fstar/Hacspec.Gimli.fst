module gimli

#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"

open Hacspec.Lib
open FStar.Mul



type state = lseq (uint32) (usize 12)

let state_idx =
  nat_mod (usize 12)

let swap (s_0 : state) (i_1 : state_idx) (j_2 : state_idx) : state =
  let tmp_3 = array_index (s_0) (i_1) in
  let s_0 = array_upd s_0 (i_1) (array_index (s_0) (j_2)) in
  let s_0 = array_upd s_0 (j_2) (tmp_3) in
  s_0

let gimli_round (s_4 : state) (r_5 : pub_uint32) : state =
  let (s_4) =
    foldi (usize 0) (usize 4) (fun col_6 (s_4) ->
      let x_7 = uint32_rotate_left (array_index (s_4) (col_6)) (usize 24) in
      let y_8 =
        uint32_rotate_left (array_index (s_4) ((col_6) + (usize 4))) (usize 9)
      in
      let z_9 = array_index (s_4) ((col_6) + (usize 8)) in
      let s_4 =
        array_upd s_4 ((col_6) + (usize 8)) (
          ((x_7) ^. ((z_9) `shift_left` (usize 1))) ^. (
            ((y_8) &. (z_9)) `shift_left` (usize 2)))
      in
      let s_4 =
        array_upd s_4 ((col_6) + (usize 4)) (
          ((y_8) ^. (x_7)) ^. (((x_7) |. (z_9)) `shift_left` (usize 1)))
      in
      let s_4 =
        array_upd s_4 (col_6) (
          ((z_9) ^. (y_8)) ^. (((x_7) &. (y_8)) `shift_left` (usize 3)))
      in
      (s_4))
    (s_4)
  in
  let (s_4) =
    if ((r_5) &. (pub_u32 0x3)) = (pub_u32 0x0) then begin
      let s_4 = swap (s_4) (usize 0) (usize 1) in
      let s_4 = swap (s_4) (usize 2) (usize 3) in
      (s_4)
    end else begin (s_4)
    end
  in
  let (s_4) =
    if ((r_5) &. (pub_u32 0x3)) = (pub_u32 0x2) then begin
      let s_4 = swap (s_4) (usize 0) (usize 2) in
      let s_4 = swap (s_4) (usize 1) (usize 3) in
      (s_4)
    end else begin (s_4)
    end
  in
  let (s_4) =
    if ((r_5) &. (pub_u32 0x3)) = (pub_u32 0x0) then begin
      let s_4 =
        array_upd s_4 (usize 0) (
          (array_index (s_4) (usize 0)) ^. (
            (secret (pub_u32 0x9e377900)) |. (secret (r_5))))
      in
      (s_4)
    end else begin (s_4)
    end
  in
  s_4

let gimli (s_10 : state) : state =
  let (s_10) =
    foldi (usize 0) (usize 24) (fun rnd_11 (s_10) ->
      let s_10 = gimli_round (s_10) (pub_u32 ((usize 24) - (rnd_11))) in
      (s_10))
    (s_10)
  in
  s_10

type block = lseq (uint8) (usize 16)

type digest = lseq (uint8) (usize 32)

let absorb_block (input_block_12 : block) (s_13 : state) : state =
  let input_bytes_14 = array_to_le_uint32s (input_block_12) in
  let s_13 =
    array_upd s_13 (usize 0) (
      (array_index (s_13) (usize 0)) ^. (
        array_index (input_bytes_14) (usize 0)))
  in
  let s_13 =
    array_upd s_13 (usize 1) (
      (array_index (s_13) (usize 1)) ^. (
        array_index (input_bytes_14) (usize 1)))
  in
  let s_13 =
    array_upd s_13 (usize 2) (
      (array_index (s_13) (usize 2)) ^. (
        array_index (input_bytes_14) (usize 2)))
  in
  let s_13 =
    array_upd s_13 (usize 3) (
      (array_index (s_13) (usize 3)) ^. (
        array_index (input_bytes_14) (usize 3)))
  in
  gimli (s_13)

let squeeze_block (s_15 : state) : block =
  let block_16 = array_new_ (secret (pub_u8 0x8)) (16) in
  let (block_16) =
    foldi (usize 0) (usize 4) (fun i_17 (block_16) ->
      let s_i_18 : uint32 = array_index (s_15) (i_17) in
      let s_i_bytes_19 = uint32_to_le_bytes (s_i_18) in
      let block_16 =
        array_upd block_16 ((usize 4) * (i_17)) (
          array_index (s_i_bytes_19) (usize 0))
      in
      let block_16 =
        array_upd block_16 (((usize 4) * (i_17)) + (usize 1)) (
          array_index (s_i_bytes_19) (usize 1))
      in
      let block_16 =
        array_upd block_16 (((usize 4) * (i_17)) + (usize 2)) (
          array_index (s_i_bytes_19) (usize 2))
      in
      let block_16 =
        array_upd block_16 (((usize 4) * (i_17)) + (usize 3)) (
          array_index (s_i_bytes_19) (usize 3))
      in
      (block_16))
    (block_16)
  in
  block_16

let gimli_hash_state (input_20 : byte_seq) (s_21 : state) : state =
  let rate_22 = array_length () in
  let (s_21, input_block_padded_23) =
    foldi (usize 0) (seq_num_chunks (input_20) (rate_22)) (fun i_24 (
        s_21,
        input_block_padded_23
      ) ->
      let (block_len_25, input_block_26) =
        seq_get_chunk (input_20) (rate_22) (i_24)
      in
      let (s_21, input_block_padded_23) =
        if (block_len_25) = (rate_22) then begin
          let full_block_27 = array_from_seq (16) (input_block_26) in
          let s_21 = absorb_block (full_block_27) (s_21) in
          (s_21, input_block_padded_23)
        end else begin
          let input_block_padded_28 = array_new_ (secret (pub_u8 0x8)) (16) in
          let input_block_padded_23 =
            array_update_start (input_block_padded_28) (input_block_26)
          in
          let input_block_padded_23 =
            array_upd input_block_padded_23 (block_len_25) (secret (pub_u8 0x1))
          in
          let s_21 =
            array_upd s_21 (usize 11) (
              (array_index (s_21) (usize 11)) ^. (secret (pub_u32 0x1000000)))
          in
          let s_21 = absorb_block (input_block_padded_23) (s_21) in
          (s_21, input_block_padded_23)
        end
      in
      (s_21, input_block_padded_23))
    (s_21, input_block_padded_23)
  in
  s_21

let gimli_hash (input_bytes_29 : byte_seq) : digest =
  let s_30 = array_new_ (secret (pub_u32 0x8)) (12) in
  let s_31 = gimli_hash_state (input_bytes_29) (s_30) in
  let output_32 = array_new_ (secret (pub_u8 0x8)) (32) in
  let output_33 = array_update_start (output_32) (squeeze_block (s_31)) in
  let s_34 = gimli (s_31) in
  array_update (output_33) (array_length ()) (squeeze_block (s_34))

type nonce = lseq (uint8) (usize 16)

type key = lseq (uint8) (usize 32)

type tag = lseq (pub_uint8) (usize 16)

let process_ad (ad_35 : byte_seq) (s_36 : state) : state =
  gimli_hash_state (ad_35) (s_36)

let process_msg (message_37 : byte_seq) (s_38 : state) : (state & byte_seq) =
  let ciphertext_39 = seq_new_ (secret (pub_u8 0x8)) (seq_len (message_37)) in
  let rate_40 = array_length () in
  let num_chunks_41 = seq_num_chunks (message_37) (rate_40) in
  let (s_38, ciphertext_39, msg_block_padded_42) =
    foldi (usize 0) (num_chunks_41) (fun i_43 (
        s_38,
        ciphertext_39,
        msg_block_padded_42
      ) ->
      let key_block_44 = squeeze_block (s_38) in
      let (block_len_45, msg_block_46) =
        seq_get_chunk (message_37) (rate_40) (i_43)
      in
      let msg_block_padded_47 = array_new_ (secret (pub_u8 0x8)) (16) in
      let msg_block_padded_42 =
        array_update_start (msg_block_padded_47) (msg_block_46)
      in
      let ciphertext_39 =
        seq_set_chunk (ciphertext_39) (rate_40) (i_43) (
          array_slice_range (
            (msg_block_padded_42) `array_xor (^.)` (key_block_44)) (
            (usize 0, block_len_45)))
      in
      let (s_38, msg_block_padded_42) =
        if (i_43) = ((num_chunks_41) - (usize 1)) then begin
          let msg_block_padded_42 =
            array_upd msg_block_padded_42 (block_len_45) (
              (array_index (msg_block_padded_42) (block_len_45)) ^. (
                secret (pub_u8 0x1)))
          in
          let s_38 =
            array_upd s_38 (usize 11) (
              (array_index (s_38) (usize 11)) ^. (secret (pub_u32 0x1000000)))
          in
          (s_38, msg_block_padded_42)
        end else begin (s_38, msg_block_padded_42)
        end
      in
      let s_38 = absorb_block (msg_block_padded_42) (s_38) in
      (s_38, ciphertext_39, msg_block_padded_42))
    (s_38, ciphertext_39, msg_block_padded_42)
  in
  (s_38, ciphertext_39)

let process_ct (ciphertext_48 : byte_seq) (s_49 : state) : (state & byte_seq) =
  let message_50 = seq_new_ (secret (pub_u8 0x8)) (seq_len (ciphertext_48)) in
  let rate_51 = array_length () in
  let num_chunks_52 = seq_num_chunks (ciphertext_48) (rate_51) in
  let (s_49, message_50, msg_block_53) =
    foldi (usize 0) (num_chunks_52) (fun i_54 (s_49, message_50, msg_block_53
      ) ->
      let key_block_55 = squeeze_block (s_49) in
      let (block_len_56, ct_block_57) =
        seq_get_chunk (ciphertext_48) (rate_51) (i_54)
      in
      let ct_block_padded_58 = array_new_ (secret (pub_u8 0x8)) (16) in
      let ct_block_padded_59 =
        array_update_start (ct_block_padded_58) (ct_block_57)
      in
      let msg_block_60 = (ct_block_padded_59) `array_xor (^.)` (key_block_55) in
      let msg_block_53 =
        array_from_slice_range (secret (pub_u8 0x8)) (16) (msg_block_60) (
          (usize 0, block_len_56))
      in
      let message_50 =
        seq_set_chunk (message_50) (rate_51) (i_54) (
          array_slice_range (msg_block_53) ((usize 0, block_len_56)))
      in
      let (s_49, msg_block_53) =
        if (i_54) = ((num_chunks_52) - (usize 1)) then begin
          let msg_block_53 =
            array_upd msg_block_53 (block_len_56) (
              (array_index (msg_block_53) (block_len_56)) ^. (
                secret (pub_u8 0x1)))
          in
          let s_49 =
            array_upd s_49 (usize 11) (
              (array_index (s_49) (usize 11)) ^. (secret (pub_u32 0x1000000)))
          in
          (s_49, msg_block_53)
        end else begin (s_49, msg_block_53)
        end
      in
      let s_49 = absorb_block (msg_block_53) (s_49) in
      (s_49, message_50, msg_block_53))
    (s_49, message_50, msg_block_53)
  in
  (s_49, message_50)

let nonce_to_u32s (nonce_61 : nonce) : seq uint32 =
  let uints_62 = seq_new_ (secret (pub_u32 0x8)) (usize 4) in
  let uints_62 =
    array_upd uints_62 (usize 0) (
      uint32_from_le_bytes (
        array_from_slice_range (secret (pub_u8 0x8)) (4) (nonce_61) (
          (usize 0, usize 4))))
  in
  let uints_62 =
    array_upd uints_62 (usize 1) (
      uint32_from_le_bytes (
        array_from_slice_range (secret (pub_u8 0x8)) (4) (nonce_61) (
          (usize 4, usize 8))))
  in
  let uints_62 =
    array_upd uints_62 (usize 2) (
      uint32_from_le_bytes (
        array_from_slice_range (secret (pub_u8 0x8)) (4) (nonce_61) (
          (usize 8, usize 12))))
  in
  let uints_62 =
    array_upd uints_62 (usize 3) (
      uint32_from_le_bytes (
        array_from_slice_range (secret (pub_u8 0x8)) (4) (nonce_61) (
          (usize 12, usize 16))))
  in
  uints_62

let key_to_u32s (key_63 : key) : seq uint32 =
  let uints_64 = seq_new_ (secret (pub_u32 0x8)) (usize 8) in
  let uints_64 =
    array_upd uints_64 (usize 0) (
      uint32_from_le_bytes (
        array_from_slice_range (secret (pub_u8 0x8)) (4) (key_63) (
          (usize 0, usize 4))))
  in
  let uints_64 =
    array_upd uints_64 (usize 1) (
      uint32_from_le_bytes (
        array_from_slice_range (secret (pub_u8 0x8)) (4) (key_63) (
          (usize 4, usize 8))))
  in
  let uints_64 =
    array_upd uints_64 (usize 2) (
      uint32_from_le_bytes (
        array_from_slice_range (secret (pub_u8 0x8)) (4) (key_63) (
          (usize 8, usize 12))))
  in
  let uints_64 =
    array_upd uints_64 (usize 3) (
      uint32_from_le_bytes (
        array_from_slice_range (secret (pub_u8 0x8)) (4) (key_63) (
          (usize 12, usize 16))))
  in
  let uints_64 =
    array_upd uints_64 (usize 4) (
      uint32_from_le_bytes (
        array_from_slice_range (secret (pub_u8 0x8)) (4) (key_63) (
          (usize 16, usize 20))))
  in
  let uints_64 =
    array_upd uints_64 (usize 5) (
      uint32_from_le_bytes (
        array_from_slice_range (secret (pub_u8 0x8)) (4) (key_63) (
          (usize 20, usize 24))))
  in
  let uints_64 =
    array_upd uints_64 (usize 6) (
      uint32_from_le_bytes (
        array_from_slice_range (secret (pub_u8 0x8)) (4) (key_63) (
          (usize 24, usize 28))))
  in
  let uints_64 =
    array_upd uints_64 (usize 7) (
      uint32_from_le_bytes (
        array_from_slice_range (secret (pub_u8 0x8)) (4) (key_63) (
          (usize 28, usize 32))))
  in
  uints_64

let gimli_aead_encrypt
  (message_65 : byte_seq)
  (ad_66 : byte_seq)
  (nonce_67 : nonce)
  (key_68 : key)
  : (byte_seq & tag) =
  let s_69 =
    array_from_seq (12) (
      seq_concat (nonce_to_u32s (nonce_67)) (key_to_u32s (key_68)))
  in
  let s_70 = gimli (s_69) in
  let s_71 = process_ad (ad_66) (s_70) in
  let (s_72, ciphertext_73) = process_msg (message_65) (s_71) in
  let tag_74 = squeeze_block (s_72) in
  let public_tag_75 = array_new_ (pub_u8 0x0) (16) in
  let (public_tag_75) =
    foldi (usize 0) (array_length ()) (fun i_76 (public_tag_75) ->
      let public_tag_75 =
        array_upd public_tag_75 (i_76) (
          uint8_declassify (array_index (tag_74) (i_76)))
      in
      (public_tag_75))
    (public_tag_75)
  in
  (ciphertext_73, public_tag_75)

let gimli_aead_decrypt
  (ciphertext_77 : byte_seq)
  (ad_78 : byte_seq)
  (tag_79 : tag)
  (nonce_80 : nonce)
  (key_81 : key)
  : byte_seq =
  let s_82 =
    array_from_seq (12) (
      seq_concat (nonce_to_u32s (nonce_80)) (key_to_u32s (key_81)))
  in
  let s_83 = gimli (s_82) in
  let s_84 = process_ad (ad_78) (s_83) in
  let (s_85, message_86) = process_ct (ciphertext_77) (s_84) in
  let my_tag_87 = squeeze_block (s_85) in
  let my_public_tag_88 = array_new_ (pub_u8 0x0) (16) in
  let (my_public_tag_88) =
    foldi (usize 0) (array_length ()) (fun i_89 (my_public_tag_88) ->
      let my_public_tag_88 =
        array_upd my_public_tag_88 (i_89) (
          uint8_declassify (array_index (my_tag_87) (i_89)))
      in
      (my_public_tag_88))
    (my_public_tag_88)
  in
  let out_90 = seq_new_ (secret (pub_u8 0x8)) (usize 0) in
  let (out_90) =
    if (my_public_tag_88) `array_eq (=)` (tag_79) then begin
      let out_90 = message_86 in
      (out_90)
    end else begin (out_90)
    end
  in
  out_90

