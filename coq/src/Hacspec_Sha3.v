(** This file was automatically generated using Hacspec **)
Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
Require Import Hacspec_Lib.

Definition rounds_v : uint_size :=
  usize 24.

Definition sha3224_rate_v : uint_size :=
  usize 144.

Definition sha3256_rate_v : uint_size :=
  usize 136.

Definition sha3384_rate_v : uint_size :=
  usize 104.

Definition sha3512_rate_v : uint_size :=
  usize 72.

Definition shake128_rate_v : uint_size :=
  usize 168.

Definition shake256_rate_v : uint_size :=
  usize 136.

Definition state_t := nseq (uint64) (usize 25).

Definition row_t := nseq (uint64) (usize 5).

Definition digest224_t := nseq (uint8) (usize 28).

Definition digest256_t := nseq (uint8) (usize 32).

Definition digest384_t := nseq (uint8) (usize 48).

Definition digest512_t := nseq (uint8) (usize 64).

Definition round_constants_t := nseq (int64) (rounds_v).

Definition rotation_constants_t := nseq (uint_size) (usize 25).

Definition roundconstants_v : round_constants_t :=
  array_from_list int64 (let l :=
      [
        @repr WORDSIZE64 1;
        @repr WORDSIZE64 32898;
        @repr WORDSIZE64 9223372036854808714;
        @repr WORDSIZE64 9223372039002292224;
        @repr WORDSIZE64 32907;
        @repr WORDSIZE64 2147483649;
        @repr WORDSIZE64 9223372039002292353;
        @repr WORDSIZE64 9223372036854808585;
        @repr WORDSIZE64 138;
        @repr WORDSIZE64 136;
        @repr WORDSIZE64 2147516425;
        @repr WORDSIZE64 2147483658;
        @repr WORDSIZE64 2147516555;
        @repr WORDSIZE64 9223372036854775947;
        @repr WORDSIZE64 9223372036854808713;
        @repr WORDSIZE64 9223372036854808579;
        @repr WORDSIZE64 9223372036854808578;
        @repr WORDSIZE64 9223372036854775936;
        @repr WORDSIZE64 32778;
        @repr WORDSIZE64 9223372039002259466;
        @repr WORDSIZE64 9223372039002292353;
        @repr WORDSIZE64 9223372036854808704;
        @repr WORDSIZE64 2147483649;
        @repr WORDSIZE64 9223372039002292232
      ] in  l).

Definition rotc_v : rotation_constants_t :=
  array_from_list uint_size (let l :=
      [
        usize 0;
        usize 1;
        usize 62;
        usize 28;
        usize 27;
        usize 36;
        usize 44;
        usize 6;
        usize 55;
        usize 20;
        usize 3;
        usize 10;
        usize 43;
        usize 25;
        usize 39;
        usize 41;
        usize 45;
        usize 15;
        usize 21;
        usize 8;
        usize 18;
        usize 2;
        usize 61;
        usize 56;
        usize 14
      ] in  l).

Definition pi_v : rotation_constants_t :=
  array_from_list uint_size (let l :=
      [
        usize 0;
        usize 6;
        usize 12;
        usize 18;
        usize 24;
        usize 3;
        usize 9;
        usize 10;
        usize 16;
        usize 22;
        usize 1;
        usize 7;
        usize 13;
        usize 19;
        usize 20;
        usize 4;
        usize 5;
        usize 11;
        usize 17;
        usize 23;
        usize 2;
        usize 8;
        usize 14;
        usize 15;
        usize 21
      ] in  l).

Definition theta (s_1115 : state_t) : state_t :=
  let b_1116 : row_t :=
    array_new_ (default) (5) in 
  let b_1116 :=
    foldi (usize 0) (usize 5) (fun i_1117 b_1116 =>
      let b_1116 :=
        array_upd b_1116 (i_1117) (((((array_index (s_1115) (i_1117)) .^ (
                  array_index (s_1115) ((i_1117) + (usize 5)))) .^ (
                array_index (s_1115) ((i_1117) + (usize 10)))) .^ (array_index (
                s_1115) ((i_1117) + (usize 15)))) .^ (array_index (s_1115) ((
                i_1117) + (usize 20)))) in 
      (b_1116))
    b_1116 in 
  let s_1115 :=
    foldi (usize 0) (usize 5) (fun i_1118 s_1115 =>
      let u_1119 : uint64 :=
        array_index (b_1116) (((i_1118) + (usize 1)) %% (usize 5)) in 
      let t_1120 : uint64 :=
        (array_index (b_1116) (((i_1118) + (usize 4)) %% (usize 5))) .^ (
          uint64_rotate_left (u_1119) (usize 1)) in 
      let s_1115 :=
        foldi (usize 0) (usize 5) (fun j_1121 s_1115 =>
          let s_1115 :=
            array_upd s_1115 (((usize 5) * (j_1121)) + (i_1118)) ((array_index (
                  s_1115) (((usize 5) * (j_1121)) + (i_1118))) .^ (t_1120)) in 
          (s_1115))
        s_1115 in 
      (s_1115))
    s_1115 in 
  s_1115.

Definition rho (s_1122 : state_t) : state_t :=
  let s_1122 :=
    foldi (usize 0) (usize 25) (fun i_1123 s_1122 =>
      let u_1124 : uint64 :=
        array_index (s_1122) (i_1123) in 
      let s_1122 :=
        array_upd s_1122 (i_1123) (uint64_rotate_left (u_1124) (array_index (
              rotc_v) (i_1123))) in 
      (s_1122))
    s_1122 in 
  s_1122.

Definition pi (s_1125 : state_t) : state_t :=
  let v_1126 : state_t :=
    array_new_ (default) (25) in 
  let v_1126 :=
    foldi (usize 0) (usize 25) (fun i_1127 v_1126 =>
      let v_1126 :=
        array_upd v_1126 (i_1127) (array_index (s_1125) (array_index (pi_v) (
              i_1127))) in 
      (v_1126))
    v_1126 in 
  v_1126.

Definition chi (s_1128 : state_t) : state_t :=
  let b_1129 : row_t :=
    array_new_ (default) (5) in 
  let '(s_1128, b_1129) :=
    foldi (usize 0) (usize 5) (fun i_1130 '(s_1128, b_1129) =>
      let b_1129 :=
        foldi (usize 0) (usize 5) (fun j_1131 b_1129 =>
          let b_1129 :=
            array_upd b_1129 (j_1131) (array_index (s_1128) (((usize 5) * (
                    i_1130)) + (j_1131))) in 
          (b_1129))
        b_1129 in 
      let s_1128 :=
        foldi (usize 0) (usize 5) (fun j_1132 s_1128 =>
          let u_1133 : uint64 :=
            array_index (b_1129) (((j_1132) + (usize 1)) %% (usize 5)) in 
          let s_1128 :=
            array_upd s_1128 (((usize 5) * (i_1130)) + (j_1132)) ((array_index (
                  s_1128) (((usize 5) * (i_1130)) + (j_1132))) .^ ((not (
                    u_1133)) .& (array_index (b_1129) (((j_1132) + (
                        usize 2)) %% (usize 5))))) in 
          (s_1128))
        s_1128 in 
      (s_1128, b_1129))
    (s_1128, b_1129) in 
  s_1128.

Definition iota (s_1134 : state_t) (rndconst_1135 : int64) : state_t :=
  let s_1134 :=
    array_upd s_1134 (usize 0) ((array_index (s_1134) (usize 0)) .^ (
        uint64_classify (rndconst_1135))) in 
  s_1134.

Definition keccakf1600 (s_1136 : state_t) : state_t :=
  let s_1136 :=
    foldi (usize 0) (rounds_v) (fun i_1137 s_1136 =>
      let s_1136 :=
        theta (s_1136) in 
      let s_1136 :=
        rho (s_1136) in 
      let s_1136 :=
        pi (s_1136) in 
      let s_1136 :=
        chi (s_1136) in 
      let s_1136 :=
        iota (s_1136) (array_index (roundconstants_v) (i_1137)) in 
      (s_1136))
    s_1136 in 
  s_1136.

Definition absorb_block (s_1138 : state_t) (block_1139 : byte_seq) : state_t :=
  let s_1138 :=
    foldi (usize 0) (seq_len (block_1139)) (fun i_1140 s_1138 =>
      let w_1141 : uint_size :=
        (i_1140) usize_shift_right (@repr WORDSIZE32 3) in 
      let o_1142 : uint_size :=
        (usize 8) * ((i_1140) .& (usize 7)) in 
      let s_1138 :=
        array_upd s_1138 (w_1141) ((array_index (s_1138) (w_1141)) .^ ((
              uint64_from_uint8 (seq_index (block_1139) (i_1140))) shift_left (
              o_1142))) in 
      (s_1138))
    s_1138 in 
  keccakf1600 (s_1138).

Definition squeeze
  (s_1143 : state_t)
  (nbytes_1144 : uint_size)
  (rate_1145 : uint_size)
  : byte_seq :=
  let out_1146 : seq uint8 :=
    seq_new_ (default) (nbytes_1144) in 
  let '(s_1143, out_1146) :=
    foldi (usize 0) (nbytes_1144) (fun i_1147 '(s_1143, out_1146) =>
      let pos_1148 : uint_size :=
        (i_1147) %% (rate_1145) in 
      let w_1149 : uint_size :=
        (pos_1148) usize_shift_right (@repr WORDSIZE32 3) in 
      let o_1150 : uint_size :=
        (usize 8) * ((pos_1148) .& (usize 7)) in 
      let b_1151 : uint64 :=
        ((array_index (s_1143) (w_1149)) shift_right (o_1150)) .& (
          uint64_classify (@repr WORDSIZE64 255)) in 
      let out_1146 :=
        seq_upd out_1146 (i_1147) (uint8_from_uint64 (b_1151)) in 
      let '(s_1143) :=
        if (((i_1147) + (usize 1)) %% (rate_1145)) =.? (usize 0):bool then (
          let s_1143 :=
            keccakf1600 (s_1143) in 
          (s_1143)) else ((s_1143)) in 
      (s_1143, out_1146))
    (s_1143, out_1146) in 
  out_1146.

Definition keccak
  (rate_1152 : uint_size)
  (data_1153 : byte_seq)
  (p_1154 : int8)
  (outbytes_1155 : uint_size)
  : byte_seq :=
  let buf_1156 : seq uint8 :=
    seq_new_ (default) (rate_1152) in 
  let last_block_len_1157 : uint_size :=
    usize 0 in 
  let s_1158 : state_t :=
    array_new_ (default) (25) in 
  let '(buf_1156, last_block_len_1157, s_1158) :=
    foldi (usize 0) (seq_num_chunks (data_1153) (rate_1152)) (fun i_1159 '(
        buf_1156,
        last_block_len_1157,
        s_1158
      ) =>
      let '(block_len_1160, block_1161) :=
        seq_get_chunk (data_1153) (rate_1152) (i_1159) in 
      let '(buf_1156, last_block_len_1157, s_1158) :=
        if (block_len_1160) =.? (rate_1152):bool then (let s_1158 :=
            absorb_block (s_1158) (block_1161) in 
          (buf_1156, last_block_len_1157, s_1158)) else (let buf_1156 :=
            seq_update_start (buf_1156) (block_1161) in 
          let last_block_len_1157 :=
            block_len_1160 in 
          (buf_1156, last_block_len_1157, s_1158)) in 
      (buf_1156, last_block_len_1157, s_1158))
    (buf_1156, last_block_len_1157, s_1158) in 
  let buf_1156 :=
    seq_upd buf_1156 (last_block_len_1157) (secret (p_1154) : int8) in 
  let buf_1156 :=
    seq_upd buf_1156 ((rate_1152) - (usize 1)) ((seq_index (buf_1156) ((
            rate_1152) - (usize 1))) .| (secret (
          @repr WORDSIZE8 128) : int8)) in 
  let s_1158 :=
    absorb_block (s_1158) (buf_1156) in 
  squeeze (s_1158) (outbytes_1155) (rate_1152).

Definition sha3224 (data_1162 : byte_seq) : digest224_t :=
  let t_1163 : seq uint8 :=
    keccak (sha3224_rate_v) (data_1162) (@repr WORDSIZE8 6) (usize 28) in 
  array_from_seq (28) (t_1163).

Definition sha3256 (data_1164 : byte_seq) : digest256_t :=
  let t_1165 : seq uint8 :=
    keccak (sha3256_rate_v) (data_1164) (@repr WORDSIZE8 6) (usize 32) in 
  array_from_seq (32) (t_1165).

Definition sha3384 (data_1166 : byte_seq) : digest384_t :=
  let t_1167 : seq uint8 :=
    keccak (sha3384_rate_v) (data_1166) (@repr WORDSIZE8 6) (usize 48) in 
  array_from_seq (48) (t_1167).

Definition sha3512 (data_1168 : byte_seq) : digest512_t :=
  let t_1169 : seq uint8 :=
    keccak (sha3512_rate_v) (data_1168) (@repr WORDSIZE8 6) (usize 64) in 
  array_from_seq (64) (t_1169).

Definition shake128
  (data_1170 : byte_seq)
  (outlen_1171 : uint_size)
  : byte_seq :=
  keccak (shake128_rate_v) (data_1170) (@repr WORDSIZE8 31) (outlen_1171).

Definition shake256
  (data_1172 : byte_seq)
  (outlen_1173 : uint_size)
  : byte_seq :=
  keccak (shake256_rate_v) (data_1172) (@repr WORDSIZE8 31) (outlen_1173).

