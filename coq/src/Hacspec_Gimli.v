(** This file was automatically generated using Hacspec **)
Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
Require Import Hacspec_Lib.

Definition state_t := nseq (uint32) (usize 12).

Definition state_idx_t :=
  nat_mod (usize 12).
Definition uint_size_in_state_idx_t(n : uint_size) : state_idx_t := int_in_nat_mod n.
Coercion uint_size_in_state_idx_t : uint_size >-> state_idx_t.

Definition swap
  (s_986 : state_t)
  (i_987 : state_idx_t)
  (j_988 : state_idx_t)
  : state_t :=
  let tmp_989 : uint32 :=
    array_index (s_986) (i_987) in 
  let s_986 :=
    array_upd s_986 (i_987) (array_index (s_986) (j_988)) in 
  let s_986 :=
    array_upd s_986 (j_988) (tmp_989) in 
  s_986.

Definition gimli_round (s_990 : state_t) (r_991 : int32) : state_t :=
  let s_990 :=
    foldi (usize 0) (usize 4) (fun col_992 s_990 =>
      let x_993 : uint32 :=
        uint32_rotate_left (array_index (s_990) (col_992)) (usize 24) in 
      let y_994 : uint32 :=
        uint32_rotate_left (array_index (s_990) ((col_992) + (usize 4))) (
          usize 9) in 
      let z_995 : uint32 :=
        array_index (s_990) ((col_992) + (usize 8)) in 
      let s_990 :=
        array_upd s_990 ((col_992) + (usize 8)) (((x_993) .^ ((
                z_995) shift_left (usize 1))) .^ (((y_994) .& (
                z_995)) shift_left (usize 2))) in 
      let s_990 :=
        array_upd s_990 ((col_992) + (usize 4)) (((y_994) .^ (x_993)) .^ (((
                x_993) .| (z_995)) shift_left (usize 1))) in 
      let s_990 :=
        array_upd s_990 (col_992) (((z_995) .^ (y_994)) .^ (((x_993) .& (
                y_994)) shift_left (usize 3))) in 
      (s_990))
    s_990 in 
  let '(s_990) :=
    if ((r_991) .& (@repr WORDSIZE32 3)) =.? (@repr WORDSIZE32 0):bool then (
      let s_990 :=
        swap (s_990) (usize 0) (usize 1) in 
      let s_990 :=
        swap (s_990) (usize 2) (usize 3) in 
      (s_990)) else ((s_990)) in 
  let '(s_990) :=
    if ((r_991) .& (@repr WORDSIZE32 3)) =.? (@repr WORDSIZE32 2):bool then (
      let s_990 :=
        swap (s_990) (usize 0) (usize 2) in 
      let s_990 :=
        swap (s_990) (usize 1) (usize 3) in 
      (s_990)) else ((s_990)) in 
  let '(s_990) :=
    if ((r_991) .& (@repr WORDSIZE32 3)) =.? (@repr WORDSIZE32 0):bool then (
      let s_990 :=
        array_upd s_990 (usize 0) ((array_index (s_990) (usize 0)) .^ ((secret (
                @repr WORDSIZE32 2654435584) : int32) .| (secret (
                r_991) : int32))) in 
      (s_990)) else ((s_990)) in 
  s_990.

Definition gimli (s_996 : state_t) : state_t :=
  let s_996 :=
    foldi (usize 0) (usize 24) (fun rnd_997 s_996 =>
      let rnd_998 : int32 :=
        pub_u32 ((usize 24) - (rnd_997)) in 
      let s_996 :=
        gimli_round (s_996) (rnd_998) in 
      (s_996))
    s_996 in 
  s_996.

Definition block_t := nseq (uint8) (usize 16).

Definition digest_t := nseq (uint8) (usize 32).

Definition absorb_block
  (input_block_999 : block_t)
  (s_1000 : state_t)
  : state_t :=
  let input_bytes_1001 : seq uint32 :=
    array_to_le_uint32s (input_block_999) in 
  let s_1000 :=
    array_upd s_1000 (usize 0) ((array_index (s_1000) (usize 0)) .^ (seq_index (
          input_bytes_1001) (usize 0))) in 
  let s_1000 :=
    array_upd s_1000 (usize 1) ((array_index (s_1000) (usize 1)) .^ (seq_index (
          input_bytes_1001) (usize 1))) in 
  let s_1000 :=
    array_upd s_1000 (usize 2) ((array_index (s_1000) (usize 2)) .^ (seq_index (
          input_bytes_1001) (usize 2))) in 
  let s_1000 :=
    array_upd s_1000 (usize 3) ((array_index (s_1000) (usize 3)) .^ (seq_index (
          input_bytes_1001) (usize 3))) in 
  gimli (s_1000).

Definition squeeze_block (s_1002 : state_t) : block_t :=
  let block_1003 : block_t :=
    array_new_ (default) (16) in 
  let block_1003 :=
    foldi (usize 0) (usize 4) (fun i_1004 block_1003 =>
      let s_i_1005 : uint32 :=
        array_index (s_1002) (i_1004) in 
      let s_i_bytes_1006 : seq uint8 :=
        uint32_to_le_bytes (s_i_1005) in 
      let block_1003 :=
        array_upd block_1003 ((usize 4) * (i_1004)) (seq_index (
            s_i_bytes_1006) (usize 0)) in 
      let block_1003 :=
        array_upd block_1003 (((usize 4) * (i_1004)) + (usize 1)) (seq_index (
            s_i_bytes_1006) (usize 1)) in 
      let block_1003 :=
        array_upd block_1003 (((usize 4) * (i_1004)) + (usize 2)) (seq_index (
            s_i_bytes_1006) (usize 2)) in 
      let block_1003 :=
        array_upd block_1003 (((usize 4) * (i_1004)) + (usize 3)) (seq_index (
            s_i_bytes_1006) (usize 3)) in 
      (block_1003))
    block_1003 in 
  block_1003.

Definition gimli_hash_state
  (input_1007 : byte_seq)
  (s_1008 : state_t)
  : state_t :=
  let rate_1009 : uint_size :=
    array_length  in 
  let chunks_1010 : uint_size :=
    seq_num_exact_chunks (input_1007) (rate_1009) in 
  let s_1008 :=
    foldi (usize 0) (chunks_1010) (fun i_1011 s_1008 =>
      let input_block_1012 : seq uint8 :=
        seq_get_exact_chunk (input_1007) (rate_1009) (i_1011) in 
      let full_block_1013 : block_t :=
        array_from_seq (16) (input_block_1012) in 
      let s_1008 :=
        absorb_block (full_block_1013) (s_1008) in 
      (s_1008))
    s_1008 in 
  let input_block_1014 : seq uint8 :=
    seq_get_remainder_chunk (input_1007) (rate_1009) in 
  let input_block_padded_1015 : block_t :=
    array_new_ (default) (16) in 
  let input_block_padded_1016 : block_t :=
    array_update_start (input_block_padded_1015) (input_block_1014) in 
  let input_block_padded_1016 :=
    array_upd input_block_padded_1016 (seq_len (input_block_1014)) (secret (
        @repr WORDSIZE8 1) : int8) in 
  let s_1008 :=
    array_upd s_1008 (usize 11) ((array_index (s_1008) (usize 11)) .^ (secret (
          @repr WORDSIZE32 16777216) : int32)) in 
  let s_1008 :=
    absorb_block (input_block_padded_1016) (s_1008) in 
  s_1008.

Definition gimli_hash (input_bytes_1017 : byte_seq) : digest_t :=
  let s_1018 : state_t :=
    array_new_ (default) (12) in 
  let s_1019 : state_t :=
    gimli_hash_state (input_bytes_1017) (s_1018) in 
  let output_1020 : digest_t :=
    array_new_ (default) (32) in 
  let output_1021 : digest_t :=
    array_update_start (output_1020) (array_to_seq (squeeze_block (s_1019))) in 
  let s_1022 : state_t :=
    gimli (s_1019) in 
  array_update (output_1021) (array_length ) (array_to_seq (squeeze_block (
      s_1022))).

Definition nonce_t := nseq (uint8) (usize 16).

Definition key_t := nseq (uint8) (usize 32).

Definition tag_t := nseq (uint8) (usize 16).

Definition process_ad (ad_1023 : byte_seq) (s_1024 : state_t) : state_t :=
  gimli_hash_state (ad_1023) (s_1024).

Definition process_msg
  (message_1025 : byte_seq)
  (s_1026 : state_t)
  : (state_t × byte_seq) :=
  let ciphertext_1027 : seq uint8 :=
    seq_new_ (default) (seq_len (message_1025)) in 
  let rate_1028 : uint_size :=
    array_length  in 
  let num_chunks_1029 : uint_size :=
    seq_num_exact_chunks (message_1025) (rate_1028) in 
  let '(s_1026, ciphertext_1027) :=
    foldi (usize 0) (num_chunks_1029) (fun i_1030 '(s_1026, ciphertext_1027) =>
      let key_block_1031 : block_t :=
        squeeze_block (s_1026) in 
      let msg_block_1032 : seq uint8 :=
        seq_get_exact_chunk (message_1025) (rate_1028) (i_1030) in 
      let msg_block_1033 : block_t :=
        array_from_seq (16) (msg_block_1032) in 
      let ciphertext_1027 :=
        seq_set_exact_chunk (ciphertext_1027) (rate_1028) (i_1030) (
          array_to_seq ((msg_block_1033) array_xor (key_block_1031))) in 
      let s_1026 :=
        absorb_block (msg_block_1033) (s_1026) in 
      (s_1026, ciphertext_1027))
    (s_1026, ciphertext_1027) in 
  let key_block_1034 : block_t :=
    squeeze_block (s_1026) in 
  let last_block_1035 : seq uint8 :=
    seq_get_remainder_chunk (message_1025) (rate_1028) in 
  let block_len_1036 : uint_size :=
    seq_len (last_block_1035) in 
  let msg_block_padded_1037 : block_t :=
    array_new_ (default) (16) in 
  let msg_block_padded_1038 : block_t :=
    array_update_start (msg_block_padded_1037) (last_block_1035) in 
  let ciphertext_1027 :=
    seq_set_chunk (ciphertext_1027) (rate_1028) (num_chunks_1029) (
      array_slice_range ((msg_block_padded_1038) array_xor (key_block_1034)) ((
          usize 0,
          block_len_1036
        ))) in 
  let msg_block_padded_1038 :=
    array_upd msg_block_padded_1038 (block_len_1036) ((array_index (
          msg_block_padded_1038) (block_len_1036)) .^ (secret (
          @repr WORDSIZE8 1) : int8)) in 
  let s_1026 :=
    array_upd s_1026 (usize 11) ((array_index (s_1026) (usize 11)) .^ (secret (
          @repr WORDSIZE32 16777216) : int32)) in 
  let s_1026 :=
    absorb_block (msg_block_padded_1038) (s_1026) in 
  (s_1026, ciphertext_1027).

Definition process_ct
  (ciphertext_1039 : byte_seq)
  (s_1040 : state_t)
  : (state_t × byte_seq) :=
  let message_1041 : seq uint8 :=
    seq_new_ (default) (seq_len (ciphertext_1039)) in 
  let rate_1042 : uint_size :=
    array_length  in 
  let num_chunks_1043 : uint_size :=
    seq_num_exact_chunks (ciphertext_1039) (rate_1042) in 
  let '(s_1040, message_1041) :=
    foldi (usize 0) (num_chunks_1043) (fun i_1044 '(s_1040, message_1041) =>
      let key_block_1045 : block_t :=
        squeeze_block (s_1040) in 
      let ct_block_1046 : seq uint8 :=
        seq_get_exact_chunk (ciphertext_1039) (rate_1042) (i_1044) in 
      let ct_block_1047 : block_t :=
        array_from_seq (16) (ct_block_1046) in 
      let msg_block_1048 : block_t :=
        (ct_block_1047) array_xor (key_block_1045) in 
      let message_1041 :=
        seq_set_exact_chunk (message_1041) (rate_1042) (i_1044) (array_to_seq ((
            ct_block_1047) array_xor (key_block_1045))) in 
      let s_1040 :=
        absorb_block (msg_block_1048) (s_1040) in 
      (s_1040, message_1041))
    (s_1040, message_1041) in 
  let key_block_1049 : block_t :=
    squeeze_block (s_1040) in 
  let ct_final_1050 : seq uint8 :=
    seq_get_remainder_chunk (ciphertext_1039) (rate_1042) in 
  let block_len_1051 : uint_size :=
    seq_len (ct_final_1050) in 
  let ct_block_padded_1052 : block_t :=
    array_new_ (default) (16) in 
  let ct_block_padded_1053 : block_t :=
    array_update_start (ct_block_padded_1052) (ct_final_1050) in 
  let msg_block_1054 : block_t :=
    (ct_block_padded_1053) array_xor (key_block_1049) in 
  let message_1041 :=
    seq_set_chunk (message_1041) (rate_1042) (num_chunks_1043) (
      array_slice_range (msg_block_1054) ((usize 0, block_len_1051))) in 
  let msg_block_1055 : block_t :=
    array_from_slice_range (default) (16) (array_to_seq (msg_block_1054)) ((
        usize 0,
        block_len_1051
      )) in 
  let msg_block_1055 :=
    array_upd msg_block_1055 (block_len_1051) ((array_index (msg_block_1055) (
          block_len_1051)) .^ (secret (@repr WORDSIZE8 1) : int8)) in 
  let s_1040 :=
    array_upd s_1040 (usize 11) ((array_index (s_1040) (usize 11)) .^ (secret (
          @repr WORDSIZE32 16777216) : int32)) in 
  let s_1040 :=
    absorb_block (msg_block_1055) (s_1040) in 
  (s_1040, message_1041).

Definition nonce_to_u32s (nonce_1056 : nonce_t) : seq uint32 :=
  let uints_1057 : seq uint32 :=
    seq_new_ (default) (usize 4) in 
  let uints_1057 :=
    seq_upd uints_1057 (usize 0) (uint32_from_le_bytes (array_from_slice_range (
          default) (4) (array_to_seq (nonce_1056)) ((usize 0, usize 4)))) in 
  let uints_1057 :=
    seq_upd uints_1057 (usize 1) (uint32_from_le_bytes (array_from_slice_range (
          default) (4) (array_to_seq (nonce_1056)) ((usize 4, usize 8)))) in 
  let uints_1057 :=
    seq_upd uints_1057 (usize 2) (uint32_from_le_bytes (array_from_slice_range (
          default) (4) (array_to_seq (nonce_1056)) ((usize 8, usize 12)))) in 
  let uints_1057 :=
    seq_upd uints_1057 (usize 3) (uint32_from_le_bytes (array_from_slice_range (
          default) (4) (array_to_seq (nonce_1056)) ((usize 12, usize 16)))) in 
  uints_1057.

Definition key_to_u32s (key_1058 : key_t) : seq uint32 :=
  let uints_1059 : seq uint32 :=
    seq_new_ (default) (usize 8) in 
  let uints_1059 :=
    seq_upd uints_1059 (usize 0) (uint32_from_le_bytes (array_from_slice_range (
          default) (4) (array_to_seq (key_1058)) ((usize 0, usize 4)))) in 
  let uints_1059 :=
    seq_upd uints_1059 (usize 1) (uint32_from_le_bytes (array_from_slice_range (
          default) (4) (array_to_seq (key_1058)) ((usize 4, usize 8)))) in 
  let uints_1059 :=
    seq_upd uints_1059 (usize 2) (uint32_from_le_bytes (array_from_slice_range (
          default) (4) (array_to_seq (key_1058)) ((usize 8, usize 12)))) in 
  let uints_1059 :=
    seq_upd uints_1059 (usize 3) (uint32_from_le_bytes (array_from_slice_range (
          default) (4) (array_to_seq (key_1058)) ((usize 12, usize 16)))) in 
  let uints_1059 :=
    seq_upd uints_1059 (usize 4) (uint32_from_le_bytes (array_from_slice_range (
          default) (4) (array_to_seq (key_1058)) ((usize 16, usize 20)))) in 
  let uints_1059 :=
    seq_upd uints_1059 (usize 5) (uint32_from_le_bytes (array_from_slice_range (
          default) (4) (array_to_seq (key_1058)) ((usize 20, usize 24)))) in 
  let uints_1059 :=
    seq_upd uints_1059 (usize 6) (uint32_from_le_bytes (array_from_slice_range (
          default) (4) (array_to_seq (key_1058)) ((usize 24, usize 28)))) in 
  let uints_1059 :=
    seq_upd uints_1059 (usize 7) (uint32_from_le_bytes (array_from_slice_range (
          default) (4) (array_to_seq (key_1058)) ((usize 28, usize 32)))) in 
  uints_1059.

Definition gimli_aead_encrypt
  (message_1060 : byte_seq)
  (ad_1061 : byte_seq)
  (nonce_1062 : nonce_t)
  (key_1063 : key_t)
  : (byte_seq × tag_t) :=
  let s_1064 : state_t :=
    array_from_seq (12) (seq_concat (nonce_to_u32s (nonce_1062)) (key_to_u32s (
          key_1063))) in 
  let s_1065 : state_t :=
    gimli (s_1064) in 
  let s_1066 : state_t :=
    process_ad (ad_1061) (s_1065) in 
  let '(s_1067, ciphertext_1068) :=
    process_msg (message_1060) (s_1066) in 
  let tag_1069 : block_t :=
    squeeze_block (s_1067) in 
  let tag_1070 : tag_t :=
    array_from_seq (16) (array_to_seq (tag_1069)) in 
  (ciphertext_1068, tag_1070).

Definition gimli_aead_decrypt
  (ciphertext_1071 : byte_seq)
  (ad_1072 : byte_seq)
  (tag_1073 : tag_t)
  (nonce_1074 : nonce_t)
  (key_1075 : key_t)
  : byte_seq :=
  let s_1076 : state_t :=
    array_from_seq (12) (seq_concat (nonce_to_u32s (nonce_1074)) (key_to_u32s (
          key_1075))) in 
  let s_1077 : state_t :=
    gimli (s_1076) in 
  let s_1078 : state_t :=
    process_ad (ad_1072) (s_1077) in 
  let '(s_1079, message_1080) :=
    process_ct (ciphertext_1071) (s_1078) in 
  let my_tag_1081 : block_t :=
    squeeze_block (s_1079) in 
  let my_tag_1082 : tag_t :=
    array_from_seq (16) (array_to_seq (my_tag_1081)) in 
  let out_1083 : seq uint8 :=
    seq_new_ (default) (usize 0) in 
  let '(out_1083) :=
    if array_equal (my_tag_1082) (tag_1073):bool then (let out_1083 :=
        message_1080 in 
      (out_1083)) else ((out_1083)) in 
  out_1083.

