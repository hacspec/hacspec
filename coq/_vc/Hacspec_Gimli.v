(** This file was automatically generated using Hacspec **)
Set Warnings "-notation-overridden,-ambiguous-paths".
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
  (s_1103 : state_t)
  (i_1104 : state_idx_t)
  (j_1105 : state_idx_t)
  : state_t :=
  let tmp_1106 : uint32 :=
    array_index (s_1103) (i_1104) in 
  let s_1103 :=
    array_upd s_1103 (i_1104) (array_index (s_1103) (j_1105)) in 
  let s_1103 :=
    array_upd s_1103 (j_1105) (tmp_1106) in 
  s_1103.

Definition gimli_round (s_1107 : state_t) (r_1108 : int32) : state_t :=
  let s_1107 :=
    foldi (usize 0) (usize 4) (fun col_1109 s_1107 =>
      let x_1110 : uint32 :=
        uint32_rotate_left (array_index (s_1107) (col_1109)) (usize 24) in 
      let y_1111 : uint32 :=
        uint32_rotate_left (array_index (s_1107) ((col_1109) + (usize 4))) (
          usize 9) in 
      let z_1112 : uint32 :=
        array_index (s_1107) ((col_1109) + (usize 8)) in 
      let s_1107 :=
        array_upd s_1107 ((col_1109) + (usize 8)) (((x_1110) .^ ((
                z_1112) shift_left (usize 1))) .^ (((y_1111) .& (
                z_1112)) shift_left (usize 2))) in 
      let s_1107 :=
        array_upd s_1107 ((col_1109) + (usize 4)) (((y_1111) .^ (x_1110)) .^ (((
                x_1110) .| (z_1112)) shift_left (usize 1))) in 
      let s_1107 :=
        array_upd s_1107 (col_1109) (((z_1112) .^ (y_1111)) .^ (((x_1110) .& (
                y_1111)) shift_left (usize 3))) in 
      (s_1107))
    s_1107 in 
  let '(s_1107) :=
    if ((r_1108) .& (@repr WORDSIZE32 3)) =.? (@repr WORDSIZE32 0):bool then (
      let s_1107 :=
        swap (s_1107) (usize 0) (usize 1) in 
      let s_1107 :=
        swap (s_1107) (usize 2) (usize 3) in 
      (s_1107)) else ((s_1107)) in 
  let '(s_1107) :=
    if ((r_1108) .& (@repr WORDSIZE32 3)) =.? (@repr WORDSIZE32 2):bool then (
      let s_1107 :=
        swap (s_1107) (usize 0) (usize 2) in 
      let s_1107 :=
        swap (s_1107) (usize 1) (usize 3) in 
      (s_1107)) else ((s_1107)) in 
  let '(s_1107) :=
    if ((r_1108) .& (@repr WORDSIZE32 3)) =.? (@repr WORDSIZE32 0):bool then (
      let s_1107 :=
        array_upd s_1107 (usize 0) ((array_index (s_1107) (usize 0)) .^ ((
              secret (@repr WORDSIZE32 2654435584) : int32) .| (secret (
                r_1108) : int32))) in 
      (s_1107)) else ((s_1107)) in 
  s_1107.

Definition gimli (s_1113 : state_t) : state_t :=
  let s_1113 :=
    foldi (usize 0) (usize 24) (fun rnd_1114 s_1113 =>
      let rnd_1115 : int32 :=
        pub_u32 ((usize 24) - (rnd_1114)) in 
      let s_1113 :=
        gimli_round (s_1113) (rnd_1115) in 
      (s_1113))
    s_1113 in 
  s_1113.

Definition block_t := nseq (uint8) (usize 16).

Definition digest_t := nseq (uint8) (usize 32).

Definition absorb_block
  (input_block_1116 : block_t)
  (s_1117 : state_t)
  : state_t :=
  let input_bytes_1118 : seq uint32 :=
    array_to_le_uint32s (input_block_1116) in 
  let s_1117 :=
    array_upd s_1117 (usize 0) ((array_index (s_1117) (usize 0)) .^ (seq_index (
          input_bytes_1118) (usize 0))) in 
  let s_1117 :=
    array_upd s_1117 (usize 1) ((array_index (s_1117) (usize 1)) .^ (seq_index (
          input_bytes_1118) (usize 1))) in 
  let s_1117 :=
    array_upd s_1117 (usize 2) ((array_index (s_1117) (usize 2)) .^ (seq_index (
          input_bytes_1118) (usize 2))) in 
  let s_1117 :=
    array_upd s_1117 (usize 3) ((array_index (s_1117) (usize 3)) .^ (seq_index (
          input_bytes_1118) (usize 3))) in 
  gimli (s_1117).

Definition squeeze_block (s_1119 : state_t) : block_t :=
  let block_1120 : block_t :=
    array_new_ (default : uint8) (16) in 
  let block_1120 :=
    foldi (usize 0) (usize 4) (fun i_1121 block_1120 =>
      let s_i_1122 : uint32 :=
        array_index (s_1119) (i_1121) in 
      let s_i_bytes_1123 : seq uint8 :=
        uint32_to_le_bytes (s_i_1122) in 
      let block_1120 :=
        array_upd block_1120 ((usize 4) * (i_1121)) (seq_index (
            s_i_bytes_1123) (usize 0)) in 
      let block_1120 :=
        array_upd block_1120 (((usize 4) * (i_1121)) + (usize 1)) (seq_index (
            s_i_bytes_1123) (usize 1)) in 
      let block_1120 :=
        array_upd block_1120 (((usize 4) * (i_1121)) + (usize 2)) (seq_index (
            s_i_bytes_1123) (usize 2)) in 
      let block_1120 :=
        array_upd block_1120 (((usize 4) * (i_1121)) + (usize 3)) (seq_index (
            s_i_bytes_1123) (usize 3)) in 
      (block_1120))
    block_1120 in 
  block_1120.

Definition gimli_hash_state
  (input_1124 : byte_seq)
  (s_1125 : state_t)
  : state_t :=
  let rate_1126 : uint_size :=
    array_length  in 
  let chunks_1127 : uint_size :=
    seq_num_exact_chunks (input_1124) (rate_1126) in 
  let s_1125 :=
    foldi (usize 0) (chunks_1127) (fun i_1128 s_1125 =>
      let input_block_1129 : seq uint8 :=
        seq_get_exact_chunk (input_1124) (rate_1126) (i_1128) in 
      let full_block_1130 : block_t :=
        array_from_seq (16) (input_block_1129) in 
      let s_1125 :=
        absorb_block (full_block_1130) (s_1125) in 
      (s_1125))
    s_1125 in 
  let input_block_1131 : seq uint8 :=
    seq_get_remainder_chunk (input_1124) (rate_1126) in 
  let input_block_padded_1132 : block_t :=
    array_new_ (default : uint8) (16) in 
  let input_block_padded_1133 : block_t :=
    array_update_start (input_block_padded_1132) (input_block_1131) in 
  let input_block_padded_1133 :=
    array_upd input_block_padded_1133 (seq_len (input_block_1131)) (secret (
        @repr WORDSIZE8 1) : int8) in 
  let s_1125 :=
    array_upd s_1125 (usize 11) ((array_index (s_1125) (usize 11)) .^ (secret (
          @repr WORDSIZE32 16777216) : int32)) in 
  let s_1125 :=
    absorb_block (input_block_padded_1133) (s_1125) in 
  s_1125.

Definition gimli_hash (input_bytes_1134 : byte_seq) : digest_t :=
  let s_1135 : state_t :=
    array_new_ (default : uint32) (12) in 
  let s_1136 : state_t :=
    gimli_hash_state (input_bytes_1134) (s_1135) in 
  let output_1137 : digest_t :=
    array_new_ (default : uint8) (32) in 
  let output_1138 : digest_t :=
    array_update_start (output_1137) (array_to_seq (squeeze_block (s_1136))) in 
  let s_1139 : state_t :=
    gimli (s_1136) in 
  array_update (output_1138) (array_length ) (array_to_seq (squeeze_block (
      s_1139))).

Definition nonce_t := nseq (uint8) (usize 16).

Definition key_t := nseq (uint8) (usize 32).

Definition tag_t := nseq (uint8) (usize 16).

Definition process_ad (ad_1140 : byte_seq) (s_1141 : state_t) : state_t :=
  gimli_hash_state (ad_1140) (s_1141).

Definition process_msg
  (message_1142 : byte_seq)
  (s_1143 : state_t)
  : (state_t × byte_seq) :=
  let ciphertext_1144 : seq uint8 :=
    seq_new_ (default : uint8) (seq_len (message_1142)) in 
  let rate_1145 : uint_size :=
    array_length  in 
  let num_chunks_1146 : uint_size :=
    seq_num_exact_chunks (message_1142) (rate_1145) in 
  let '(s_1143, ciphertext_1144) :=
    foldi (usize 0) (num_chunks_1146) (fun i_1147 '(s_1143, ciphertext_1144) =>
      let key_block_1148 : block_t :=
        squeeze_block (s_1143) in 
      let msg_block_1149 : seq uint8 :=
        seq_get_exact_chunk (message_1142) (rate_1145) (i_1147) in 
      let msg_block_1150 : block_t :=
        array_from_seq (16) (msg_block_1149) in 
      let ciphertext_1144 :=
        seq_set_exact_chunk (ciphertext_1144) (rate_1145) (i_1147) (
          array_to_seq ((msg_block_1150) array_xor (key_block_1148))) in 
      let s_1143 :=
        absorb_block (msg_block_1150) (s_1143) in 
      (s_1143, ciphertext_1144))
    (s_1143, ciphertext_1144) in 
  let key_block_1151 : block_t :=
    squeeze_block (s_1143) in 
  let last_block_1152 : seq uint8 :=
    seq_get_remainder_chunk (message_1142) (rate_1145) in 
  let block_len_1153 : uint_size :=
    seq_len (last_block_1152) in 
  let msg_block_padded_1154 : block_t :=
    array_new_ (default : uint8) (16) in 
  let msg_block_padded_1155 : block_t :=
    array_update_start (msg_block_padded_1154) (last_block_1152) in 
  let ciphertext_1144 :=
    seq_set_chunk (ciphertext_1144) (rate_1145) (num_chunks_1146) (
      array_slice_range ((msg_block_padded_1155) array_xor (key_block_1151)) ((
          usize 0,
          block_len_1153
        ))) in 
  let msg_block_padded_1155 :=
    array_upd msg_block_padded_1155 (block_len_1153) ((array_index (
          msg_block_padded_1155) (block_len_1153)) .^ (secret (
          @repr WORDSIZE8 1) : int8)) in 
  let s_1143 :=
    array_upd s_1143 (usize 11) ((array_index (s_1143) (usize 11)) .^ (secret (
          @repr WORDSIZE32 16777216) : int32)) in 
  let s_1143 :=
    absorb_block (msg_block_padded_1155) (s_1143) in 
  (s_1143, ciphertext_1144).

Definition process_ct
  (ciphertext_1156 : byte_seq)
  (s_1157 : state_t)
  : (state_t × byte_seq) :=
  let message_1158 : seq uint8 :=
    seq_new_ (default : uint8) (seq_len (ciphertext_1156)) in 
  let rate_1159 : uint_size :=
    array_length  in 
  let num_chunks_1160 : uint_size :=
    seq_num_exact_chunks (ciphertext_1156) (rate_1159) in 
  let '(s_1157, message_1158) :=
    foldi (usize 0) (num_chunks_1160) (fun i_1161 '(s_1157, message_1158) =>
      let key_block_1162 : block_t :=
        squeeze_block (s_1157) in 
      let ct_block_1163 : seq uint8 :=
        seq_get_exact_chunk (ciphertext_1156) (rate_1159) (i_1161) in 
      let ct_block_1164 : block_t :=
        array_from_seq (16) (ct_block_1163) in 
      let msg_block_1165 : block_t :=
        (ct_block_1164) array_xor (key_block_1162) in 
      let message_1158 :=
        seq_set_exact_chunk (message_1158) (rate_1159) (i_1161) (array_to_seq ((
            ct_block_1164) array_xor (key_block_1162))) in 
      let s_1157 :=
        absorb_block (msg_block_1165) (s_1157) in 
      (s_1157, message_1158))
    (s_1157, message_1158) in 
  let key_block_1166 : block_t :=
    squeeze_block (s_1157) in 
  let ct_final_1167 : seq uint8 :=
    seq_get_remainder_chunk (ciphertext_1156) (rate_1159) in 
  let block_len_1168 : uint_size :=
    seq_len (ct_final_1167) in 
  let ct_block_padded_1169 : block_t :=
    array_new_ (default : uint8) (16) in 
  let ct_block_padded_1170 : block_t :=
    array_update_start (ct_block_padded_1169) (ct_final_1167) in 
  let msg_block_1171 : block_t :=
    (ct_block_padded_1170) array_xor (key_block_1166) in 
  let message_1158 :=
    seq_set_chunk (message_1158) (rate_1159) (num_chunks_1160) (
      array_slice_range (msg_block_1171) ((usize 0, block_len_1168))) in 
  let msg_block_1172 : block_t :=
    array_from_slice_range (default : uint8) (16) (
      array_to_seq (msg_block_1171)) ((usize 0, block_len_1168)) in 
  let msg_block_1172 :=
    array_upd msg_block_1172 (block_len_1168) ((array_index (msg_block_1172) (
          block_len_1168)) .^ (secret (@repr WORDSIZE8 1) : int8)) in 
  let s_1157 :=
    array_upd s_1157 (usize 11) ((array_index (s_1157) (usize 11)) .^ (secret (
          @repr WORDSIZE32 16777216) : int32)) in 
  let s_1157 :=
    absorb_block (msg_block_1172) (s_1157) in 
  (s_1157, message_1158).

Definition nonce_to_u32s (nonce_1173 : nonce_t) : seq uint32 :=
  let uints_1174 : seq uint32 :=
    seq_new_ (default : uint32) (usize 4) in 
  let uints_1174 :=
    seq_upd uints_1174 (usize 0) (uint32_from_le_bytes (array_from_slice_range (
          default : uint8) (4) (array_to_seq (nonce_1173)) ((usize 0, usize 4
          )))) in 
  let uints_1174 :=
    seq_upd uints_1174 (usize 1) (uint32_from_le_bytes (array_from_slice_range (
          default : uint8) (4) (array_to_seq (nonce_1173)) ((usize 4, usize 8
          )))) in 
  let uints_1174 :=
    seq_upd uints_1174 (usize 2) (uint32_from_le_bytes (array_from_slice_range (
          default : uint8) (4) (array_to_seq (nonce_1173)) ((usize 8, usize 12
          )))) in 
  let uints_1174 :=
    seq_upd uints_1174 (usize 3) (uint32_from_le_bytes (array_from_slice_range (
          default : uint8) (4) (array_to_seq (nonce_1173)) ((usize 12, usize 16
          )))) in 
  uints_1174.

Definition key_to_u32s (key_1175 : key_t) : seq uint32 :=
  let uints_1176 : seq uint32 :=
    seq_new_ (default : uint32) (usize 8) in 
  let uints_1176 :=
    seq_upd uints_1176 (usize 0) (uint32_from_le_bytes (array_from_slice_range (
          default : uint8) (4) (array_to_seq (key_1175)) ((usize 0, usize 4
          )))) in 
  let uints_1176 :=
    seq_upd uints_1176 (usize 1) (uint32_from_le_bytes (array_from_slice_range (
          default : uint8) (4) (array_to_seq (key_1175)) ((usize 4, usize 8
          )))) in 
  let uints_1176 :=
    seq_upd uints_1176 (usize 2) (uint32_from_le_bytes (array_from_slice_range (
          default : uint8) (4) (array_to_seq (key_1175)) ((usize 8, usize 12
          )))) in 
  let uints_1176 :=
    seq_upd uints_1176 (usize 3) (uint32_from_le_bytes (array_from_slice_range (
          default : uint8) (4) (array_to_seq (key_1175)) ((usize 12, usize 16
          )))) in 
  let uints_1176 :=
    seq_upd uints_1176 (usize 4) (uint32_from_le_bytes (array_from_slice_range (
          default : uint8) (4) (array_to_seq (key_1175)) ((usize 16, usize 20
          )))) in 
  let uints_1176 :=
    seq_upd uints_1176 (usize 5) (uint32_from_le_bytes (array_from_slice_range (
          default : uint8) (4) (array_to_seq (key_1175)) ((usize 20, usize 24
          )))) in 
  let uints_1176 :=
    seq_upd uints_1176 (usize 6) (uint32_from_le_bytes (array_from_slice_range (
          default : uint8) (4) (array_to_seq (key_1175)) ((usize 24, usize 28
          )))) in 
  let uints_1176 :=
    seq_upd uints_1176 (usize 7) (uint32_from_le_bytes (array_from_slice_range (
          default : uint8) (4) (array_to_seq (key_1175)) ((usize 28, usize 32
          )))) in 
  uints_1176.

Definition gimli_aead_encrypt
  (message_1177 : byte_seq)
  (ad_1178 : byte_seq)
  (nonce_1179 : nonce_t)
  (key_1180 : key_t)
  : (byte_seq × tag_t) :=
  let s_1181 : state_t :=
    array_from_seq (12) (seq_concat (nonce_to_u32s (nonce_1179)) (key_to_u32s (
          key_1180))) in 
  let s_1182 : state_t :=
    gimli (s_1181) in 
  let s_1183 : state_t :=
    process_ad (ad_1178) (s_1182) in 
  let '(s_1184, ciphertext_1185) :=
    process_msg (message_1177) (s_1183) in 
  let tag_1186 : block_t :=
    squeeze_block (s_1184) in 
  let tag_1187 : tag_t :=
    array_from_seq (16) (array_to_seq (tag_1186)) in 
  (ciphertext_1185, tag_1187).

Definition gimli_aead_decrypt
  (ciphertext_1188 : byte_seq)
  (ad_1189 : byte_seq)
  (tag_1190 : tag_t)
  (nonce_1191 : nonce_t)
  (key_1192 : key_t)
  : byte_seq :=
  let s_1193 : state_t :=
    array_from_seq (12) (seq_concat (nonce_to_u32s (nonce_1191)) (key_to_u32s (
          key_1192))) in 
  let s_1194 : state_t :=
    gimli (s_1193) in 
  let s_1195 : state_t :=
    process_ad (ad_1189) (s_1194) in 
  let '(s_1196, message_1197) :=
    process_ct (ciphertext_1188) (s_1195) in 
  let my_tag_1198 : block_t :=
    squeeze_block (s_1196) in 
  let my_tag_1199 : tag_t :=
    array_from_seq (16) (array_to_seq (my_tag_1198)) in 
  let out_1200 : seq uint8 :=
    seq_new_ (default : uint8) (usize 0) in 
  let '(out_1200) :=
    if array_equal (my_tag_1199) (tag_1190):bool then (let out_1200 :=
        message_1197 in 
      (out_1200)) else ((out_1200)) in 
  out_1200.

