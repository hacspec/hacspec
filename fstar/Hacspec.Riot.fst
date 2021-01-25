module Hacspec.Riot

#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"

open Hacspec.Lib
open FStar.Mul



type fletcher = (pub_uint32 & pub_uint32)
type header = (pub_uint32 & pub_uint32 & pub_uint32 & pub_uint32)

let riotboot_magic : pub_uint32 =
  pub_u32 0x544f4952

let new_fletcher () : fletcher =
  (pub_u32 0x0, pub_u32 0x0)

let max_chunk_size () : uint_size =
  usize 360

let reduce_u32 (x_0 : pub_uint32) : pub_uint32 =
  ((x_0) &. (pub_u32 0xffff)) +. ((x_0) `shift_right` (pub_u32 0x10))

let combine (lower_1 : pub_uint32) (upper_2 : pub_uint32) : pub_uint32 =
  (lower_1) |. ((upper_2) `shift_left` (pub_u32 0x10))

let update_fletcher (f_3 : fletcher) (data_4 : seq pub_uint16) : fletcher =
  let max_chunk_size_5 = max_chunk_size () in
  let (a_6, b_7) = f_3 in
  let (a_6, b_7) =
    foldi (usize 0) (seq_num_chunks (data_4) (max_chunk_size_5)) (fun i_8 (
        a_6,
        b_7
      ) ->
      let (chunk_len_9, chunk_10) =
        seq_get_chunk (data_4) (i_8) (max_chunk_size_5)
      in
      let intermediate_a_11 = a_6 in
      let intermediate_b_12 = b_7 in
      let (intermediate_a_11, intermediate_b_12) =
        foldi (usize 0) (chunk_len_9) (fun j_13 (
            intermediate_a_11,
            intermediate_b_12
          ) ->
          let intermediate_a_11 =
            (intermediate_a_11) +. (
              cast U32 PUB (array_index
                 (**) #pub_uint16 #chunk_len_9
                 (chunk_10) (j_13)))
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

let value (x_14 : fletcher) : pub_uint32 =
  let (a_15, b_16) = x_14 in
  combine (a_15) (b_16)

let header_as_u16_slice (h_17 : header) : seq pub_uint16 =
  let (magic_18, seq_number_19, start_addr_20, _) = h_17 in
  let magic_21 = u32_to_be_bytes (magic_18) in
  let seq_number_22 = u32_to_be_bytes (seq_number_19) in
  let start_addr_23 = u32_to_be_bytes (start_addr_20) in
  let u8_seq_24 = seq_new_ (pub_u8 0x0) (usize 12) in
  let u8_seq_25 =
    seq_update_slice (u8_seq_24) (usize 0) (magic_21) (usize 0) (usize 4)
  in
  let u8_seq_26 =
    seq_update_slice (u8_seq_25) (usize 4) (seq_number_22) (usize 0) (usize 4)
  in
  let u8_seq_27 =
    seq_update_slice (u8_seq_26) (usize 8) (start_addr_23) (usize 0) (usize 4)
  in
  let u16_seq_28 = seq_new_ (pub_u16 0x0) (usize 6) in
  let (u16_seq_28) =
    foldi (usize 0) (usize 6) (fun i_29 (u16_seq_28) ->
      let u16_word_30 =
        array_from_seq (2) (
          seq_slice (u8_seq_27) ((i_29) * (usize 2)) (usize 2))
      in
      let u16_value_31 = u16_from_be_bytes (u16_word_30) in
      let u16_seq_28 = array_upd u16_seq_28 (i_29) (u16_value_31) in
      (u16_seq_28))
    (u16_seq_28)
  in
  u16_seq_28

let is_valid_header (h_32 : header) : bool =
  let (magic_number_33, seq_number_34, start_addr_35, checksum_36) = h_32 in
  let slice_37 =
    header_as_u16_slice (
      (magic_number_33, seq_number_34, start_addr_35, checksum_36))
  in
  let result_38 = false in
  let (result_38) =
    if (magic_number_33) = (riotboot_magic) then begin
      let fletcher_39 = new_fletcher () in
      let fletcher_40 = update_fletcher (fletcher_39) (slice_37) in
      let sum_41 = value (fletcher_40) in
      let result_38 = (sum_41) = (checksum_36) in
      (result_38)
    end else begin (result_38)
    end
  in
  result_38

let choose_image (images_42 : seq header) : (bool & pub_uint32) =
  let image_43 = pub_u32 0x0 in
  let image_found_44 = false in
  let (image_43, image_found_44) =
    foldi (usize 0) (seq_len (images_42)) (fun i_45 (image_43, image_found_44
      ) ->
      let header_46 = array_index
        (**) #header #(seq_len images_42)
        (images_42) (i_45)
      in
      let (magic_number_47, seq_number_48, start_addr_49, checksum_50) =
        header_46
      in
      let (image_43, image_found_44) =
        if is_valid_header (
          (magic_number_47, seq_number_48, start_addr_49, checksum_50
          )) then begin
          let change_image_51 =
            not ((image_found_44) && ((seq_number_48) <=. (image_43)))
          in
          let (image_43, image_found_44) =
            if change_image_51 then begin
              let image_43 = start_addr_49 in
              let image_found_44 = true in
              (image_43, image_found_44)
            end else begin (image_43, image_found_44)
            end
          in
          (image_43, image_found_44)
        end else begin (image_43, image_found_44)
        end
      in
      (image_43, image_found_44))
    (image_43, image_found_44)
  in
  (image_found_44, image_43)
