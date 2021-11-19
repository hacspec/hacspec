module Hacspec.Riot.Bootloader

#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"

open FStar.Mul

open Hacspec.Lib

let riotboot_magic_v:pub_uint32 = pub_u32 0x544f4952

type fletcher_t = (pub_uint32 & pub_uint32)

let new_fletcher () : fletcher_t = (pub_u32 0xffff, pub_u32 0xffff)

let max_chunk_size () : uint_size = usize 360

let reduce_u32 (x_0: pub_uint32) : pub_uint32 =
  ((x_0) &. (pub_u32 0xffff)) +. ((x_0) `shift_right` (pub_u32 0x10))

let combine (lower_1 upper_2: pub_uint32) : pub_uint32 =
  (lower_1) |. ((upper_2) `shift_left` (pub_u32 0x10))

let update_fletcher (f_3: fletcher_t) (data_4: seq pub_uint16) : fletcher_t =
  let max_chunk_size_5 = max_chunk_size () in
  let a_6, b_7 = f_3 in
  let a_6, b_7 =
    foldi (usize 0)
      (seq_num_chunks (data_4) (max_chunk_size_5))
      (fun i_8 (a_6, b_7) ->
          let chunk_len_9, chunk_10 = seq_get_chunk (data_4) (max_chunk_size_5) (i_8) in
          let intermediate_a_11 = a_6 in
          let intermediate_b_12 = b_7 in
          let intermediate_a_11, intermediate_b_12 =
            foldi (usize 0)
              (chunk_len_9)
              (fun j_13 (intermediate_a_11, intermediate_b_12) ->
                  let intermediate_a_11 =
                    (intermediate_a_11) +. (cast U32 PUB (seq_index (chunk_10) (j_13)))
                  in
                  let intermediate_b_12 = (intermediate_b_12) +. (intermediate_a_11) in
                  (intermediate_a_11, intermediate_b_12))
              (intermediate_a_11, intermediate_b_12)
          in
          let a_6 = reduce_u32 (intermediate_a_11) in
          let b_7 = reduce_u32 (intermediate_b_12) in
          (a_6, b_7))
      (a_6, b_7)
  in
  let a_6 = reduce_u32 (a_6) in
  let b_7 = reduce_u32 (b_7) in
  (a_6, b_7)

let value (x_14: fletcher_t) : pub_uint32 =
  let a_15, b_16 = x_14 in
  combine (a_15) (b_16)

type header_t = (pub_uint32 & pub_uint32 & pub_uint32 & pub_uint32)

let header_as_u16_slice (h_17: header_t) : seq pub_uint16 =
  let magic_18, seq_number_19, start_addr_20, _ = h_17 in
  let magic_21 = u32_to_be_bytes (magic_18) in
  let seq_number_22 = u32_to_be_bytes (seq_number_19) in
  let start_addr_23 = u32_to_be_bytes (start_addr_20) in
  let u8_seq_24 = seq_new_ (pub_u8 0x0) (usize 12) in
  let u8_seq_25 = seq_update_slice (u8_seq_24) (usize 0) (magic_21) (usize 0) (usize 4) in
  let u8_seq_26 = seq_update_slice (u8_seq_25) (usize 4) (seq_number_22) (usize 0) (usize 4) in
  let u8_seq_27 = seq_update_slice (u8_seq_26) (usize 8) (start_addr_23) (usize 0) (usize 4) in
  let u16_seq_28 = seq_new_ (pub_u16 0x0) (usize 6) in
  let u16_seq_28 =
    foldi (usize 0)
      (usize 3)
      (fun i_29 u16_seq_28 ->
          let u16_word_30 =
            array_from_seq (2) (seq_slice (u8_seq_27) ((i_29) * (usize 4)) (usize 2))
          in
          let u16_value_31 = u16_from_be_bytes (u16_word_30) in
          let u16_seq_28 = seq_upd u16_seq_28 (((usize 2) * (i_29)) + (usize 1)) (u16_value_31) in
          let u16_word_32 =
            array_from_seq (2) (seq_slice (u8_seq_27) (((i_29) * (usize 4)) + (usize 2)) (usize 2))
          in
          let u16_value_33 = u16_from_be_bytes (u16_word_32) in
          let u16_seq_28 = seq_upd u16_seq_28 ((usize 2) * (i_29)) (u16_value_33) in
          (u16_seq_28))
      (u16_seq_28)
  in
  u16_seq_28

let is_valid_header (h_34: header_t) : bool =
  let magic_number_35, seq_number_36, start_addr_37, checksum_38 = h_34 in
  let slice_39 =
    header_as_u16_slice ((magic_number_35, seq_number_36, start_addr_37, checksum_38))
  in
  let result_40 = false in
  let result_40 =
    if (magic_number_35) = (riotboot_magic_v)
    then
      let fletcher_41 = new_fletcher () in
      let fletcher_42 = update_fletcher (fletcher_41) (slice_39) in
      let sum_43 = value (fletcher_42) in
      let result_40 = (sum_43) = (checksum_38) in
      (result_40)
    else (result_40)
  in
  result_40

let choose_image (images_44: seq header_t) : (bool & pub_uint32) =
  let image_45 = pub_u32 0x0 in
  let image_found_46 = false in
  let image_45, image_found_46 =
    foldi (usize 0)
      (seq_len (images_44))
      (fun i_47 (image_45, image_found_46) ->
          let header_48 = seq_index (images_44) (i_47) in
          let magic_number_49, seq_number_50, start_addr_51, checksum_52 = header_48 in
          let image_45, image_found_46 =
            if is_valid_header ((magic_number_49, seq_number_50, start_addr_51, checksum_52))
            then
              let change_image_53 = not ((image_found_46) && ((seq_number_50) <=. (image_45))) in
              let image_45, image_found_46 =
                if change_image_53
                then
                  let image_45 = start_addr_51 in
                  let image_found_46 = true in
                  (image_45, image_found_46)
                else (image_45, image_found_46)
              in
              (image_45, image_found_46)
            else (image_45, image_found_46)
          in
          (image_45, image_found_46))
      (image_45, image_found_46)
  in
  (image_found_46, image_45)

