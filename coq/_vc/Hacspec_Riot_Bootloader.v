(** This file was automatically generated using Hacspec **)
Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
Require Import Hacspec_Lib.

Definition riotboot_magic_v : int32 :=
  @repr WORDSIZE32 1414482258.

Notation "'fletcher_t'" := ((int32 × int32)) : hacspec_scope.

Definition new_fletcher  : fletcher_t :=
  (@repr WORDSIZE32 65535, @repr WORDSIZE32 65535).

Definition max_chunk_size  : uint_size :=
  usize 360.

Definition reduce_u32 (x_1211 : int32) : int32 :=
  ((x_1211) .& (@repr WORDSIZE32 65535)) .+ ((x_1211) shift_right (
      @repr WORDSIZE32 16)).

Definition combine (lower_1212 : int32) (upper_1213 : int32) : int32 :=
  (lower_1212) .| ((upper_1213) shift_left (@repr WORDSIZE32 16)).

Definition update_fletcher
  (f_1214 : fletcher_t)
  (data_1215 : seq int16)
  : fletcher_t :=
  let max_chunk_size_1216 : uint_size :=
    max_chunk_size  in 
  let '(a_1217, b_1218) :=
    f_1214 in 
  let '(a_1217, b_1218) :=
    foldi (usize 0) (seq_num_chunks (data_1215) (
          max_chunk_size_1216)) (fun i_1219 '(a_1217, b_1218) =>
      let '(chunk_len_1220, chunk_1221) :=
        seq_get_chunk (data_1215) (max_chunk_size_1216) (i_1219) in 
      let intermediate_a_1222 : int32 :=
        a_1217 in 
      let intermediate_b_1223 : int32 :=
        b_1218 in 
      let '(intermediate_a_1222, intermediate_b_1223) :=
        foldi (usize 0) (chunk_len_1220) (fun j_1224 '(
            intermediate_a_1222,
            intermediate_b_1223
          ) =>
          let intermediate_a_1222 :=
            (intermediate_a_1222) .+ (@cast _ uint32 _ (seq_index (chunk_1221) (
                  j_1224))) in 
          let intermediate_b_1223 :=
            (intermediate_b_1223) .+ (intermediate_a_1222) in 
          (intermediate_a_1222, intermediate_b_1223))
        (intermediate_a_1222, intermediate_b_1223) in 
      let a_1217 :=
        reduce_u32 (intermediate_a_1222) in 
      let b_1218 :=
        reduce_u32 (intermediate_b_1223) in 
      (a_1217, b_1218))
    (a_1217, b_1218) in 
  let a_1217 :=
    reduce_u32 (a_1217) in 
  let b_1218 :=
    reduce_u32 (b_1218) in 
  (a_1217, b_1218).

Definition value (x_1225 : fletcher_t) : int32 :=
  let '(a_1226, b_1227) :=
    x_1225 in 
  combine (a_1226) (b_1227).

Notation "'header_t'" := ((int32 × int32 × int32 × int32)) : hacspec_scope.

Definition header_as_u16_slice (h_1228 : header_t) : seq int16 :=
  let '(magic_1229, seq_number_1230, start_addr_1231, _) :=
    h_1228 in 
  let magic_1232 : u32_word_t :=
    u32_to_be_bytes (magic_1229) in 
  let seq_number_1233 : u32_word_t :=
    u32_to_be_bytes (seq_number_1230) in 
  let start_addr_1234 : u32_word_t :=
    u32_to_be_bytes (start_addr_1231) in 
  let u8_seq_1235 : seq int8 :=
    seq_new_ (default) (usize 12) in 
  let u8_seq_1236 : seq int8 :=
    seq_update_slice (u8_seq_1235) (usize 0) (array_to_seq (magic_1232)) (
      usize 0) (usize 4) in 
  let u8_seq_1237 : seq int8 :=
    seq_update_slice (u8_seq_1236) (usize 4) (array_to_seq (seq_number_1233)) (
      usize 0) (usize 4) in 
  let u8_seq_1238 : seq int8 :=
    seq_update_slice (u8_seq_1237) (usize 8) (array_to_seq (start_addr_1234)) (
      usize 0) (usize 4) in 
  let u16_seq_1239 : seq int16 :=
    seq_new_ (default) (usize 6) in 
  let u16_seq_1239 :=
    foldi (usize 0) (usize 3) (fun i_1240 u16_seq_1239 =>
      let u16_word_1241 : u16_word_t :=
        array_from_seq (2) (seq_slice (u8_seq_1238) ((i_1240) * (usize 4)) (
            usize 2)) in 
      let u16_value_1242 : int16 :=
        u16_from_be_bytes (u16_word_1241) in 
      let u16_seq_1239 :=
        seq_upd u16_seq_1239 (((usize 2) * (i_1240)) + (usize 1)) (
          u16_value_1242) in 
      let u16_word_1243 : u16_word_t :=
        array_from_seq (2) (seq_slice (u8_seq_1238) (((i_1240) * (usize 4)) + (
              usize 2)) (usize 2)) in 
      let u16_value_1244 : int16 :=
        u16_from_be_bytes (u16_word_1243) in 
      let u16_seq_1239 :=
        seq_upd u16_seq_1239 ((usize 2) * (i_1240)) (u16_value_1244) in 
      (u16_seq_1239))
    u16_seq_1239 in 
  u16_seq_1239.

Definition is_valid_header (h_1245 : header_t) : bool :=
  let '(magic_number_1246, seq_number_1247, start_addr_1248, checksum_1249) :=
    h_1245 in 
  let slice_1250 : seq int16 :=
    header_as_u16_slice ((
        magic_number_1246,
        seq_number_1247,
        start_addr_1248,
        checksum_1249
      )) in 
  let result_1251 : bool :=
    false in 
  let '(result_1251) :=
    if (magic_number_1246) =.? (riotboot_magic_v):bool then (
      let fletcher_1252 : (int32 × int32) :=
        new_fletcher  in 
      let fletcher_1253 : (int32 × int32) :=
        update_fletcher (fletcher_1252) (slice_1250) in 
      let sum_1254 : int32 :=
        value (fletcher_1253) in 
      let result_1251 :=
        (sum_1254) =.? (checksum_1249) in 
      (result_1251)) else ((result_1251)) in 
  result_1251.

Definition choose_image (images_1255 : seq header_t) : (bool × int32) :=
  let image_1256 : int32 :=
    @repr WORDSIZE32 0 in 
  let image_found_1257 : bool :=
    false in 
  let '(image_1256, image_found_1257) :=
    foldi (usize 0) (seq_len (images_1255)) (fun i_1258 '(
        image_1256,
        image_found_1257
      ) =>
      let header_1259 : (int32 × int32 × int32 × int32) :=
        seq_index (images_1255) (i_1258) in 
      let '(magic_number_1260, seq_number_1261, start_addr_1262, checksum_1263
        ) :=
        header_1259 in 
      let '(image_1256, image_found_1257) :=
        if is_valid_header ((
            magic_number_1260,
            seq_number_1261,
            start_addr_1262,
            checksum_1263
          )):bool then (let change_image_1264 : bool :=
            negb ((image_found_1257) && ((seq_number_1261) <=.? (
                  image_1256))) in 
          let '(image_1256, image_found_1257) :=
            if change_image_1264:bool then (let image_1256 :=
                start_addr_1262 in 
              let image_found_1257 :=
                true in 
              (image_1256, image_found_1257)) else ((
                image_1256,
                image_found_1257
              )) in 
          (image_1256, image_found_1257)) else ((image_1256, image_found_1257
          )) in 
      (image_1256, image_found_1257))
    (image_1256, image_found_1257) in 
  (image_found_1257, image_1256).

