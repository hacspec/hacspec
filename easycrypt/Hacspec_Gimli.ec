require import List Int IntDiv CoreMap AllCore.
require import Array3 Array4 Array8 Array12 Array16 Array17 Array32 Array64.
require import WArray64.

from Jasmin require import JModel JMemory JArray.
require import Hacspec.


type state = uint32 Array12.t.

type state_idx = uint_size.

op swap (s_0 : state) (i_1 : state_idx) (j_2 : state_idx) : state =
  let tmp_3 = s_0.[i_1] in
  let s_0 = s_0.[(i_1) <- (s_0.[j_2])] in
  let s_0 = s_0.[(j_2) <- (tmp_3)] in
  s_0.

op gimli_round (s_4 : state) (r_5 : pub_uint32) : state =
  let s_4 =
    foldi (0) (4) (fun col_6 s_4 =>
      let x_7 = uint32_rotate_left (s_4.[col_6]) (24) in
      let y_8 = uint32_rotate_left (s_4.[(col_6) + (4)]) (9) in
      let z_9 = s_4.[(col_6) + (8)] in
      let s_4 =
        s_4.[((col_6) + (8)) <- (
            ((x_7) +^ (shift_left (z_9) (1))) +^ (
              shift_left ((y_8) & (z_9)) (2)))]
      in
      let s_4 =
        s_4.[((col_6) + (4)) <- (
            ((y_8) +^ (x_7)) +^ (shift_left ((x_7) | (z_9)) (1)))]
      in
      let s_4 =
        s_4.[(col_6) <- (((z_9) +^ (y_8)) +^ (shift_left ((x_7) & (y_8)) (3)))]
      in
      s_4)
    s_4
  in
  let s_4 =
    if ((r_5) & (pub_u32 3)) = (pub_u32 0) then begin
      let s_4 = swap (s_4) (0) (1) in
      let s_4 = swap (s_4) (2) (3) in
      s_4
    end else begin s_4
    end
  in
  let s_4 =
    if ((r_5) & (pub_u32 3)) = (pub_u32 2) then begin
      let s_4 = swap (s_4) (0) (2) in
      let s_4 = swap (s_4) (1) (3) in
      s_4
    end else begin s_4
    end
  in
  let s_4 =
    if ((r_5) & (pub_u32 3)) = (pub_u32 0) then begin
      let s_4 =
        s_4.[(0) <- (
            (s_4.[0]) +^ ((secret (pub_u32 2654435584)) | (secret (r_5))))]
      in
      s_4
    end else begin s_4
    end
  in
  s_4.

op gimli (s_10 : state) : state =
  let s_10 =
    foldi (0) (24) (fun rnd_11 s_10 =>
      let s_10 = gimli_round (s_10) (pub_u32 ((24) - (rnd_11))) in
      s_10)
    s_10
  in
  s_10.

type block = uint8 Array16.t.

type digest = uint8 Array32.t.

op absorb_block (input_block_12 : block) (s_13 : state) : state =
  let input_bytes_14 = array_16_to_le_uint32s (input_block_12) in
  let s_13 = s_13.[(0) <- ((s_13.[0]) +^ (input_bytes_14.[0]))] in
  let s_13 = s_13.[(1) <- ((s_13.[1]) +^ (input_bytes_14.[1]))] in
  let s_13 = s_13.[(2) <- ((s_13.[2]) +^ (input_bytes_14.[2]))] in
  let s_13 = s_13.[(3) <- ((s_13.[3]) +^ (input_bytes_14.[3]))] in
  gimli (s_13).

op squeeze_block (s_15 : state) : block =
  let block_16 = array_16_new_ (secret (pub_u8 8)) in
  let block_16 =
    foldi (0) (4) (fun i_17 block_16 =>
      let s_i_18 : uint32 = s_15.[i_17] in
      let s_i_bytes_19 = uint32_to_le_bytes (s_i_18) in
      let block_16 = block_16.[((4) * (i_17)) <- (s_i_bytes_19.[0])] in
      let block_16 = block_16.[(((4) * (i_17)) + (1)) <- (s_i_bytes_19.[1])] in
      let block_16 = block_16.[(((4) * (i_17)) + (2)) <- (s_i_bytes_19.[2])] in
      let block_16 = block_16.[(((4) * (i_17)) + (3)) <- (s_i_bytes_19.[3])] in
      block_16)
    block_16
  in
  block_16.

op gimli_hash_state (input_20 : byte_seq) (s_21 : state) : state =
  let rate_22 = array_16_length () in
  let (s_21, input_block_padded_23) =
    foldi (0) (seq_num_chunks (input_20) (rate_22)) (fun i_24 acc =>
      let (s_21, input_block_padded_23) =
        acc
      in
      let (block_len_25, input_block_26) =
        seq_get_chunk (input_20) (rate_22) (i_24)
      in
      let (s_21, input_block_padded_23) =
        if (block_len_25) = (rate_22) then begin
          let full_block_27 = array_16_from_seq (input_block_26) in
          let s_21 = absorb_block (full_block_27) (s_21) in
          (s_21, input_block_padded_23)
        end else begin
          let input_block_padded_28 = array_16_new_ (secret (pub_u8 8)) in
          let input_block_padded_23 =
            array_16_update_start (input_block_padded_28) (input_block_26)
          in
          let input_block_padded_23 =
            input_block_padded_23.[(block_len_25) <- (secret (pub_u8 1))]
          in
          let s_21 =
            s_21.[(11) <- ((s_21.[11]) +^ (secret (pub_u32 16777216)))]
          in
          let s_21 = absorb_block (input_block_padded_23) (s_21) in
          (s_21, input_block_padded_23)
        end
      in
      (s_21, input_block_padded_23))
    (s_21, input_block_padded_23)
  in
  s_21.

op gimli_hash (input_bytes_29 : byte_seq) : digest =
  let s_30 = array_12_new_ (secret (pub_u32 8)) in
  let s_31 = gimli_hash_state (input_bytes_29) (s_30) in
  let output_32 = array_32_new_ (secret (pub_u8 8)) in
  let output_33 = array_32_update_start (output_32) (squeeze_block (s_31)) in
  let s_34 = gimli (s_31) in
  array_32_update (output_33) (array_16_length ()) (squeeze_block (s_34)).

type nonce = uint8 Array16.t.

type key = uint8 Array32.t.

type tag = pub_uint8 Array16.t.

op process_ad (ad_35 : byte_seq) (s_36 : state) : state =
  gimli_hash_state (ad_35) (s_36).

op process_msg (message_37 : byte_seq) (s_38 : state) : (state & byte_seq) =
  let ciphertext_39 = seq_new_ (secret (pub_u8 8)) (seq_len (message_37)) in
  let rate_40 = array_16_length () in
  let num_chunks_41 = seq_num_chunks (message_37) (rate_40) in
  let (s_38, ciphertext_39, msg_block_padded_42) =
    foldi (0) (num_chunks_41) (fun i_43 acc =>
      let (s_38, ciphertext_39, msg_block_padded_42) =
        acc
      in
      let key_block_44 = squeeze_block (s_38) in
      let (block_len_45, msg_block_46) =
        seq_get_chunk (message_37) (rate_40) (i_43)
      in
      let msg_block_padded_47 = array_16_new_ (secret (pub_u8 8)) in
      let msg_block_padded_42 =
        array_16_update_start (msg_block_padded_47) (msg_block_46)
      in
      let ciphertext_39 =
        seq_set_chunk (ciphertext_39) (rate_40) (i_43) (
          array_16_slice_range (
            array_16_xor W8.(+^) (msg_block_padded_42) (key_block_44)) (
            (0, block_len_45)))
      in
      let (s_38, msg_block_padded_42) =
        if (i_43) = ((num_chunks_41) - (1)) then begin
          let msg_block_padded_42 =
            msg_block_padded_42.[(block_len_45) <- (
                (msg_block_padded_42.[block_len_45]) +^ (secret (pub_u8 1)))]
          in
          let s_38 =
            s_38.[(11) <- ((s_38.[11]) +^ (secret (pub_u32 16777216)))]
          in
          (s_38, msg_block_padded_42)
        end else begin (s_38, msg_block_padded_42)
        end
      in
      let s_38 = absorb_block (msg_block_padded_42) (s_38) in
      (s_38, ciphertext_39, msg_block_padded_42))
    (s_38, ciphertext_39, msg_block_padded_42)
  in
  (s_38, ciphertext_39).

op process_ct (ciphertext_48 : byte_seq) (s_49 : state) : (state & byte_seq) =
  let message_50 = seq_new_ (secret (pub_u8 8)) (seq_len (ciphertext_48)) in
  let rate_51 = array_16_length () in
  let num_chunks_52 = seq_num_chunks (ciphertext_48) (rate_51) in
  let (s_49, message_50, msg_block_53) =
    foldi (0) (num_chunks_52) (fun i_54 acc =>
      let (s_49, message_50, msg_block_53) =
        acc
      in
      let key_block_55 = squeeze_block (s_49) in
      let (block_len_56, ct_block_57) =
        seq_get_chunk (ciphertext_48) (rate_51) (i_54)
      in
      let ct_block_padded_58 = array_16_new_ (secret (pub_u8 8)) in
      let ct_block_padded_59 =
        array_16_update_start (ct_block_padded_58) (ct_block_57)
      in
      let msg_block_60 =
        array_16_xor W8.(+^) (ct_block_padded_59) (key_block_55)
      in
      let msg_block_53 =
        array_16_from_slice_range (secret (pub_u8 8)) (msg_block_60) (
          (0, block_len_56))
      in
      let message_50 =
        seq_set_chunk (message_50) (rate_51) (i_54) (
          array_16_slice_range (msg_block_53) ((0, block_len_56)))
      in
      let (s_49, msg_block_53) =
        if (i_54) = ((num_chunks_52) - (1)) then begin
          let msg_block_53 =
            msg_block_53.[(block_len_56) <- (
                (msg_block_53.[block_len_56]) +^ (secret (pub_u8 1)))]
          in
          let s_49 =
            s_49.[(11) <- ((s_49.[11]) +^ (secret (pub_u32 16777216)))]
          in
          (s_49, msg_block_53)
        end else begin (s_49, msg_block_53)
        end
      in
      let s_49 = absorb_block (msg_block_53) (s_49) in
      (s_49, message_50, msg_block_53))
    (s_49, message_50, msg_block_53)
  in
  (s_49, message_50).

op nonce_to_u32s (nonce_61 : nonce) : uint32 Sequence.t =
  let uints_62 = seq_new_ (secret (pub_u32 8)) (4) in
  let uints_62 =
    uints_62.[(0) <- (
        uint32_from_le_bytes (
          array_4_from_slice_range (secret (pub_u8 8)) (nonce_61) ((0, 4))))]
  in
  let uints_62 =
    uints_62.[(1) <- (
        uint32_from_le_bytes (
          array_4_from_slice_range (secret (pub_u8 8)) (nonce_61) ((4, 8))))]
  in
  let uints_62 =
    uints_62.[(2) <- (
        uint32_from_le_bytes (
          array_4_from_slice_range (secret (pub_u8 8)) (nonce_61) ((8, 12))))]
  in
  let uints_62 =
    uints_62.[(3) <- (
        uint32_from_le_bytes (
          array_4_from_slice_range (secret (pub_u8 8)) (nonce_61) ((12, 16))))]
  in
  uints_62.

op key_to_u32s (key_63 : key) : uint32 Sequence.t =
  let uints_64 = seq_new_ (secret (pub_u32 8)) (8) in
  let uints_64 =
    uints_64.[(0) <- (
        uint32_from_le_bytes (
          array_4_from_slice_range (secret (pub_u8 8)) (key_63) ((0, 4))))]
  in
  let uints_64 =
    uints_64.[(1) <- (
        uint32_from_le_bytes (
          array_4_from_slice_range (secret (pub_u8 8)) (key_63) ((4, 8))))]
  in
  let uints_64 =
    uints_64.[(2) <- (
        uint32_from_le_bytes (
          array_4_from_slice_range (secret (pub_u8 8)) (key_63) ((8, 12))))]
  in
  let uints_64 =
    uints_64.[(3) <- (
        uint32_from_le_bytes (
          array_4_from_slice_range (secret (pub_u8 8)) (key_63) ((12, 16))))]
  in
  let uints_64 =
    uints_64.[(4) <- (
        uint32_from_le_bytes (
          array_4_from_slice_range (secret (pub_u8 8)) (key_63) ((16, 20))))]
  in
  let uints_64 =
    uints_64.[(5) <- (
        uint32_from_le_bytes (
          array_4_from_slice_range (secret (pub_u8 8)) (key_63) ((20, 24))))]
  in
  let uints_64 =
    uints_64.[(6) <- (
        uint32_from_le_bytes (
          array_4_from_slice_range (secret (pub_u8 8)) (key_63) ((24, 28))))]
  in
  let uints_64 =
    uints_64.[(7) <- (
        uint32_from_le_bytes (
          array_4_from_slice_range (secret (pub_u8 8)) (key_63) ((28, 32))))]
  in
  uints_64.

op gimli_aead_encrypt
  (message_65 : byte_seq)
  (ad_66 : byte_seq)
  (nonce_67 : nonce)
  (key_68 : key)
  : (byte_seq & tag) =
  let s_69 =
    array_12_from_seq (
      seq_concat (nonce_to_u32s (nonce_67)) (key_to_u32s (key_68)))
  in
  let s_70 = gimli (s_69) in
  let s_71 = process_ad (ad_66) (s_70) in
  let (s_72, ciphertext_73) = process_msg (message_65) (s_71) in
  let tag_74 = squeeze_block (s_72) in
  let public_tag_75 = array_16_new_ (pub_u8 0) in
  let public_tag_75 =
    foldi (0) (array_16_length ()) (fun i_76 public_tag_75 =>
      let public_tag_75 =
        public_tag_75.[(i_76) <- (uint8_declassify (tag_74.[i_76]))]
      in
      public_tag_75)
    public_tag_75
  in
  (ciphertext_73, public_tag_75).

op gimli_aead_decrypt
  (ciphertext_77 : byte_seq)
  (ad_78 : byte_seq)
  (tag_79 : tag)
  (nonce_80 : nonce)
  (key_81 : key)
  : byte_seq =
  let s_82 =
    array_12_from_seq (
      seq_concat (nonce_to_u32s (nonce_80)) (key_to_u32s (key_81)))
  in
  let s_83 = gimli (s_82) in
  let s_84 = process_ad (ad_78) (s_83) in
  let (s_85, message_86) = process_ct (ciphertext_77) (s_84) in
  let my_tag_87 = squeeze_block (s_85) in
  let my_public_tag_88 = array_16_new_ (pub_u8 0) in
  let my_public_tag_88 =
    foldi (0) (array_16_length ()) (fun i_89 my_public_tag_88 =>
      let my_public_tag_88 =
        my_public_tag_88.[(i_89) <- (uint8_declassify (my_tag_87.[i_89]))]
      in
      my_public_tag_88)
    my_public_tag_88
  in
  let out_90 = seq_new_ (secret (pub_u8 8)) (0) in
  let out_90 =
    if array_16_eq Unknown.(=) (my_public_tag_88) (tag_79) then begin
      let out_90 = message_86 in
      out_90
    end else begin out_90
    end
  in
  out_90.

