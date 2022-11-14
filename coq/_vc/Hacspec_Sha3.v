(** This file was automatically generated using Hacspec **)
Set Warnings "-notation-overridden,-ambiguous-paths".
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

Definition theta (s_1044 : state_t) : state_t :=
  let b_1045 : row_t :=
    array_new_ (default : uint64) (5) in 
  let b_1045 :=
    foldi (usize 0) (usize 5) (fun i_1046 b_1045 =>
      let b_1045 :=
        array_upd b_1045 (i_1046) (((((array_index (s_1044) (i_1046)) .^ (
                  array_index (s_1044) ((i_1046) + (usize 5)))) .^ (
                array_index (s_1044) ((i_1046) + (usize 10)))) .^ (array_index (
                s_1044) ((i_1046) + (usize 15)))) .^ (array_index (s_1044) ((
                i_1046) + (usize 20)))) in 
      (b_1045))
    b_1045 in 
  let s_1044 :=
    foldi (usize 0) (usize 5) (fun i_1047 s_1044 =>
      let u_1048 : uint64 :=
        array_index (b_1045) (((i_1047) + (usize 1)) %% (usize 5)) in 
      let t_1049 : uint64 :=
        (array_index (b_1045) (((i_1047) + (usize 4)) %% (usize 5))) .^ (
          uint64_rotate_left (u_1048) (usize 1)) in 
      let s_1044 :=
        foldi (usize 0) (usize 5) (fun j_1050 s_1044 =>
          let s_1044 :=
            array_upd s_1044 (((usize 5) * (j_1050)) + (i_1047)) ((array_index (
                  s_1044) (((usize 5) * (j_1050)) + (i_1047))) .^ (t_1049)) in 
          (s_1044))
        s_1044 in 
      (s_1044))
    s_1044 in 
  s_1044.

Definition rho (s_1051 : state_t) : state_t :=
  let s_1051 :=
    foldi (usize 0) (usize 25) (fun i_1052 s_1051 =>
      let u_1053 : uint64 :=
        array_index (s_1051) (i_1052) in 
      let s_1051 :=
        array_upd s_1051 (i_1052) (uint64_rotate_left (u_1053) (array_index (
              rotc_v) (i_1052))) in 
      (s_1051))
    s_1051 in 
  s_1051.

Definition pi (s_1054 : state_t) : state_t :=
  let v_1055 : state_t :=
    array_new_ (default : uint64) (25) in 
  let v_1055 :=
    foldi (usize 0) (usize 25) (fun i_1056 v_1055 =>
      let v_1055 :=
        array_upd v_1055 (i_1056) (array_index (s_1054) (array_index (pi_v) (
              i_1056))) in 
      (v_1055))
    v_1055 in 
  v_1055.

Definition chi (s_1057 : state_t) : state_t :=
  let b_1058 : row_t :=
    array_new_ (default : uint64) (5) in 
  let '(s_1057, b_1058) :=
    foldi (usize 0) (usize 5) (fun i_1059 '(s_1057, b_1058) =>
      let b_1058 :=
        foldi (usize 0) (usize 5) (fun j_1060 b_1058 =>
          let b_1058 :=
            array_upd b_1058 (j_1060) (array_index (s_1057) (((usize 5) * (
                    i_1059)) + (j_1060))) in 
          (b_1058))
        b_1058 in 
      let s_1057 :=
        foldi (usize 0) (usize 5) (fun j_1061 s_1057 =>
          let u_1062 : uint64 :=
            array_index (b_1058) (((j_1061) + (usize 1)) %% (usize 5)) in 
          let s_1057 :=
            array_upd s_1057 (((usize 5) * (i_1059)) + (j_1061)) ((array_index (
                  s_1057) (((usize 5) * (i_1059)) + (j_1061))) .^ ((not (
                    u_1062)) .& (array_index (b_1058) (((j_1061) + (
                        usize 2)) %% (usize 5))))) in 
          (s_1057))
        s_1057 in 
      (s_1057, b_1058))
    (s_1057, b_1058) in 
  s_1057.

Definition iota (s_1063 : state_t) (rndconst_1064 : int64) : state_t :=
  let s_1063 :=
    array_upd s_1063 (usize 0) ((array_index (s_1063) (usize 0)) .^ (
        uint64_classify (rndconst_1064))) in 
  s_1063.

Definition keccakf1600 (s_1065 : state_t) : state_t :=
  let s_1065 :=
    foldi (usize 0) (rounds_v) (fun i_1066 s_1065 =>
      let s_1065 :=
        theta (s_1065) in 
      let s_1065 :=
        rho (s_1065) in 
      let s_1065 :=
        pi (s_1065) in 
      let s_1065 :=
        chi (s_1065) in 
      let s_1065 :=
        iota (s_1065) (array_index (roundconstants_v) (i_1066)) in 
      (s_1065))
    s_1065 in 
  s_1065.

Definition absorb_block (s_1067 : state_t) (block_1068 : byte_seq) : state_t :=
  let s_1067 :=
    foldi (usize 0) (seq_len (block_1068)) (fun i_1069 s_1067 =>
      let w_1070 : uint_size :=
        (i_1069) usize_shift_right (@repr WORDSIZE32 3) in 
      let o_1071 : uint_size :=
        (usize 8) * ((i_1069) .& (usize 7)) in 
      let s_1067 :=
        array_upd s_1067 (w_1070) ((array_index (s_1067) (w_1070)) .^ ((
              uint64_from_uint8 (seq_index (block_1068) (i_1069))) shift_left (
              o_1071))) in 
      (s_1067))
    s_1067 in 
  keccakf1600 (s_1067).

Definition squeeze
  (s_1072 : state_t)
  (nbytes_1073 : uint_size)
  (rate_1074 : uint_size)
  : byte_seq :=
  let out_1075 : seq uint8 :=
    seq_new_ (default : uint8) (nbytes_1073) in 
  let '(s_1072, out_1075) :=
    foldi (usize 0) (nbytes_1073) (fun i_1076 '(s_1072, out_1075) =>
      let pos_1077 : uint_size :=
        (i_1076) %% (rate_1074) in 
      let w_1078 : uint_size :=
        (pos_1077) usize_shift_right (@repr WORDSIZE32 3) in 
      let o_1079 : uint_size :=
        (usize 8) * ((pos_1077) .& (usize 7)) in 
      let b_1080 : uint64 :=
        ((array_index (s_1072) (w_1078)) shift_right (o_1079)) .& (
          uint64_classify (@repr WORDSIZE64 255)) in 
      let out_1075 :=
        seq_upd out_1075 (i_1076) (uint8_from_uint64 (b_1080)) in 
      let '(s_1072) :=
        if (((i_1076) + (usize 1)) %% (rate_1074)) =.? (usize 0):bool then (
          let s_1072 :=
            keccakf1600 (s_1072) in 
          (s_1072)) else ((s_1072)) in 
      (s_1072, out_1075))
    (s_1072, out_1075) in 
  out_1075.

Definition keccak
  (rate_1081 : uint_size)
  (data_1082 : byte_seq)
  (p_1083 : int8)
  (outbytes_1084 : uint_size)
  : byte_seq :=
  let buf_1085 : seq uint8 :=
    seq_new_ (default : uint8) (rate_1081) in 
  let last_block_len_1086 : uint_size :=
    usize 0 in 
  let s_1087 : state_t :=
    array_new_ (default : uint64) (25) in 
  let '(buf_1085, last_block_len_1086, s_1087) :=
    foldi (usize 0) (seq_num_chunks (data_1082) (rate_1081)) (fun i_1088 '(
        buf_1085,
        last_block_len_1086,
        s_1087
      ) =>
      let '(block_len_1089, block_1090) :=
        seq_get_chunk (data_1082) (rate_1081) (i_1088) in 
      let '(buf_1085, last_block_len_1086, s_1087) :=
        if (block_len_1089) =.? (rate_1081):bool then (let s_1087 :=
            absorb_block (s_1087) (block_1090) in 
          (buf_1085, last_block_len_1086, s_1087)) else (let buf_1085 :=
            seq_update_start (buf_1085) (block_1090) in 
          let last_block_len_1086 :=
            block_len_1089 in 
          (buf_1085, last_block_len_1086, s_1087)) in 
      (buf_1085, last_block_len_1086, s_1087))
    (buf_1085, last_block_len_1086, s_1087) in 
  let buf_1085 :=
    seq_upd buf_1085 (last_block_len_1086) (secret (p_1083) : int8) in 
  let buf_1085 :=
    seq_upd buf_1085 ((rate_1081) - (usize 1)) ((seq_index (buf_1085) ((
            rate_1081) - (usize 1))) .| (secret (
          @repr WORDSIZE8 128) : int8)) in 
  let s_1087 :=
    absorb_block (s_1087) (buf_1085) in 
  squeeze (s_1087) (outbytes_1084) (rate_1081).

Definition sha3224 (data_1091 : byte_seq) : digest224_t :=
  let t_1092 : seq uint8 :=
    keccak (sha3224_rate_v) (data_1091) (@repr WORDSIZE8 6) (usize 28) in 
  array_from_seq (28) (t_1092).

Definition sha3256 (data_1093 : byte_seq) : digest256_t :=
  let t_1094 : seq uint8 :=
    keccak (sha3256_rate_v) (data_1093) (@repr WORDSIZE8 6) (usize 32) in 
  array_from_seq (32) (t_1094).

Definition sha3384 (data_1095 : byte_seq) : digest384_t :=
  let t_1096 : seq uint8 :=
    keccak (sha3384_rate_v) (data_1095) (@repr WORDSIZE8 6) (usize 48) in 
  array_from_seq (48) (t_1096).

Definition sha3512 (data_1097 : byte_seq) : digest512_t :=
  let t_1098 : seq uint8 :=
    keccak (sha3512_rate_v) (data_1097) (@repr WORDSIZE8 6) (usize 64) in 
  array_from_seq (64) (t_1098).

Definition shake128
  (data_1099 : byte_seq)
  (outlen_1100 : uint_size)
  : byte_seq :=
  keccak (shake128_rate_v) (data_1099) (@repr WORDSIZE8 31) (outlen_1100).

Definition shake256
  (data_1101 : byte_seq)
  (outlen_1102 : uint_size)
  : byte_seq :=
  keccak (shake256_rate_v) (data_1101) (@repr WORDSIZE8 31) (outlen_1102).

