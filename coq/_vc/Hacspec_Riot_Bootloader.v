(** This file was automatically generated using Hacspec **)
Set Warnings "-notation-overridden,-ambiguous-paths".
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

Definition reduce_u32 (x_1269 : int32) : int32 :=
  ((x_1269) .& (@repr WORDSIZE32 65535)) .+ ((x_1269) shift_right (
      @repr WORDSIZE32 16)).

Definition combine (lower_1270 : int32) (upper_1271 : int32) : int32 :=
  (lower_1270) .| ((upper_1271) shift_left (@repr WORDSIZE32 16)).

Definition update_fletcher
  (f_1272 : fletcher_t)
  (data_1273 : seq int16)
  : fletcher_t :=
  let max_chunk_size_1274 : uint_size :=
    max_chunk_size  in 
  let '(a_1275, b_1276) :=
    f_1272 in 
  let '(a_1275, b_1276) :=
    foldi (usize 0) (seq_num_chunks (data_1273) (
          max_chunk_size_1274)) (fun i_1277 '(a_1275, b_1276) =>
      let '(chunk_len_1278, chunk_1279) :=
        seq_get_chunk (data_1273) (max_chunk_size_1274) (i_1277) in 
      let intermediate_a_1280 : int32 :=
        a_1275 in 
      let intermediate_b_1281 : int32 :=
        b_1276 in 
      let '(intermediate_a_1280, intermediate_b_1281) :=
        foldi (usize 0) (chunk_len_1278) (fun j_1282 '(
            intermediate_a_1280,
            intermediate_b_1281
          ) =>
          let intermediate_a_1280 :=
            (intermediate_a_1280) .+ (@cast _ uint32 _ (seq_index (chunk_1279) (
                  j_1282))) in 
          let intermediate_b_1281 :=
            (intermediate_b_1281) .+ (intermediate_a_1280) in 
          (intermediate_a_1280, intermediate_b_1281))
        (intermediate_a_1280, intermediate_b_1281) in 
      let a_1275 :=
        reduce_u32 (intermediate_a_1280) in 
      let b_1276 :=
        reduce_u32 (intermediate_b_1281) in 
      (a_1275, b_1276))
    (a_1275, b_1276) in 
  let a_1275 :=
    reduce_u32 (a_1275) in 
  let b_1276 :=
    reduce_u32 (b_1276) in 
  (a_1275, b_1276).

Definition value (x_1283 : fletcher_t) : int32 :=
  let '(a_1284, b_1285) :=
    x_1283 in 
  combine (a_1284) (b_1285).

Notation "'header_t'" := ((int32 × int32 × int32 × int32)) : hacspec_scope.

Definition header_as_u16_slice (h_1286 : header_t) : seq int16 :=
  let '(magic_1287, seq_number_1288, start_addr_1289, _) :=
    h_1286 in 
  let magic_1290 : u32_word_t :=
    u32_to_be_bytes (magic_1287) in 
  let seq_number_1291 : u32_word_t :=
    u32_to_be_bytes (seq_number_1288) in 
  let start_addr_1292 : u32_word_t :=
    u32_to_be_bytes (start_addr_1289) in 
  let u8_seq_1293 : seq int8 :=
    seq_new_ (default : int8) (usize 12) in 
  let u8_seq_1294 : seq int8 :=
    seq_update_slice (u8_seq_1293) (usize 0) (array_to_seq (magic_1290)) (
      usize 0) (usize 4) in 
  let u8_seq_1295 : seq int8 :=
    seq_update_slice (u8_seq_1294) (usize 4) (array_to_seq (seq_number_1291)) (
      usize 0) (usize 4) in 
  let u8_seq_1296 : seq int8 :=
    seq_update_slice (u8_seq_1295) (usize 8) (array_to_seq (start_addr_1292)) (
      usize 0) (usize 4) in 
  let u16_seq_1297 : seq int16 :=
    seq_new_ (default : int16) (usize 6) in 
  let u16_seq_1297 :=
    foldi (usize 0) (usize 3) (fun i_1298 u16_seq_1297 =>
      let u16_word_1299 : u16_word_t :=
        array_from_seq (2) (seq_slice (u8_seq_1296) ((i_1298) * (usize 4)) (
            usize 2)) in 
      let u16_value_1300 : int16 :=
        u16_from_be_bytes (u16_word_1299) in 
      let u16_seq_1297 :=
        seq_upd u16_seq_1297 (((usize 2) * (i_1298)) + (usize 1)) (
          u16_value_1300) in 
      let u16_word_1301 : u16_word_t :=
        array_from_seq (2) (seq_slice (u8_seq_1296) (((i_1298) * (usize 4)) + (
              usize 2)) (usize 2)) in 
      let u16_value_1302 : int16 :=
        u16_from_be_bytes (u16_word_1301) in 
      let u16_seq_1297 :=
        seq_upd u16_seq_1297 ((usize 2) * (i_1298)) (u16_value_1302) in 
      (u16_seq_1297))
    u16_seq_1297 in 
  u16_seq_1297.

Definition is_valid_header (h_1303 : header_t) : bool :=
  let '(magic_number_1304, seq_number_1305, start_addr_1306, checksum_1307) :=
    h_1303 in 
  let slice_1308 : seq int16 :=
    header_as_u16_slice ((
        magic_number_1304,
        seq_number_1305,
        start_addr_1306,
        checksum_1307
      )) in 
  let result_1309 : bool :=
    false in 
  let '(result_1309) :=
    if (magic_number_1304) =.? (riotboot_magic_v):bool then (
      let fletcher_1310 : (int32 × int32) :=
        new_fletcher  in 
      let fletcher_1311 : (int32 × int32) :=
        update_fletcher (fletcher_1310) (slice_1308) in 
      let sum_1312 : int32 :=
        value (fletcher_1311) in 
      let result_1309 :=
        (sum_1312) =.? (checksum_1307) in 
      (result_1309)) else ((result_1309)) in 
  result_1309.

Definition choose_image (images_1313 : seq header_t) : (bool × int32) :=
  let image_1314 : int32 :=
    @repr WORDSIZE32 0 in 
  let image_found_1315 : bool :=
    false in 
  let '(image_1314, image_found_1315) :=
    foldi (usize 0) (seq_len (images_1313)) (fun i_1316 '(
        image_1314,
        image_found_1315
      ) =>
      let header_1317 : (int32 × int32 × int32 × int32) :=
        seq_index (images_1313) (i_1316) in 
      let '(magic_number_1318, seq_number_1319, start_addr_1320, checksum_1321
        ) :=
        header_1317 in 
      let '(image_1314, image_found_1315) :=
        if is_valid_header ((
            magic_number_1318,
            seq_number_1319,
            start_addr_1320,
            checksum_1321
          )):bool then (let change_image_1322 : bool :=
            negb ((image_found_1315) && ((seq_number_1319) <=.? (
                  image_1314))) in 
          let '(image_1314, image_found_1315) :=
            if change_image_1322:bool then (let image_1314 :=
                start_addr_1320 in 
              let image_found_1315 :=
                true in 
              (image_1314, image_found_1315)) else ((
                image_1314,
                image_found_1315
              )) in 
          (image_1314, image_found_1315)) else ((image_1314, image_found_1315
          )) in 
      (image_1314, image_found_1315))
    (image_1314, image_found_1315) in 
  (image_found_1315, image_1314).

