(** This file was automatically generated using Hacspec **)
Set Warnings "-notation-overridden,-ambiguous-paths".
From Crypt Require Import choice_type Package Prelude.
Import PackageNotation.
From extructures Require Import ord fset.
From mathcomp Require Import ssrZ word.
From Jasmin Require Import word.

From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope list_scope.
Open Scope Z_scope.
Open Scope bool_scope.

Require Import ChoiceEquality.
Require Import LocationUtility.
Require Import Hacspec_Lib_Comparable.
Require Import Hacspec_Lib_Pre.
Require Import Hacspec_Lib.

Open Scope hacspec_scope.

Obligation Tactic := try timeout 8 solve_ssprove_obligations.


Definition riotboot_magic_v : int32 :=
  @repr U32 1414482258.

Notation "'fletcher_t'" := ((int32 '× int32)) : hacspec_scope.


Notation "'new_fletcher_inp'" :=(
  unit_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'new_fletcher_inp'" :=(
  unit_ChoiceEquality : ChoiceEquality) (at level 2).
Notation "'new_fletcher_out'" :=(
  fletcher_t : choice_type) (in custom pack_type at level 2).
Notation "'new_fletcher_out'" :=(fletcher_t : ChoiceEquality) (at level 2).
Definition NEW_FLETCHER : nat :=
  1546.
Program Definition new_fletcher
  : both_package (fset.fset0) [interface] [(NEW_FLETCHER,(
      new_fletcher_inp,new_fletcher_out))] :=
  let temp_package_both := (fun temp_inp => 
    
    ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
            lift_to_both0 (@repr U32 65535),
            lift_to_both0 (@repr U32 65535)
          ))
        ) : both (fset.fset0) [interface] (fletcher_t)))in
  both_package' _ _ (NEW_FLETCHER,(
      new_fletcher_inp,new_fletcher_out)) temp_package_both.
Fail Next Obligation.


Notation "'max_chunk_size_inp'" :=(
  unit_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'max_chunk_size_inp'" :=(
  unit_ChoiceEquality : ChoiceEquality) (at level 2).
Notation "'max_chunk_size_out'" :=(
  uint_size : choice_type) (in custom pack_type at level 2).
Notation "'max_chunk_size_out'" :=(uint_size : ChoiceEquality) (at level 2).
Definition MAX_CHUNK_SIZE : nat :=
  1547.
Program Definition max_chunk_size
  : both_package (fset.fset0) [interface] [(MAX_CHUNK_SIZE,(
      max_chunk_size_inp,max_chunk_size_out))] :=
  let temp_package_both := (fun temp_inp => 
    
    ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 (
            usize 360))
        ) : both (fset.fset0) [interface] (uint_size)))in
  both_package' _ _ (MAX_CHUNK_SIZE,(
      max_chunk_size_inp,max_chunk_size_out)) temp_package_both.
Fail Next Obligation.


Notation "'reduce_u32_inp'" :=(
  int32 : choice_type) (in custom pack_type at level 2).
Notation "'reduce_u32_inp'" :=(int32 : ChoiceEquality) (at level 2).
Notation "'reduce_u32_out'" :=(
  int32 : choice_type) (in custom pack_type at level 2).
Notation "'reduce_u32_out'" :=(int32 : ChoiceEquality) (at level 2).
Definition REDUCE_U32 : nat :=
  1549.
Program Definition reduce_u32
  : both_package (fset.fset0) [interface] [(REDUCE_U32,(
      reduce_u32_inp,reduce_u32_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(x_1548) := temp_inp : int32 in
    
    ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (((
              lift_to_both0 x_1548) .& (lift_to_both0 (@repr U32 65535))) .+ ((
              lift_to_both0 x_1548) shift_right (lift_to_both0 (@repr U32 16))))
        ) : both (fset.fset0) [interface] (int32)))in
  both_package' _ _ (REDUCE_U32,(
      reduce_u32_inp,reduce_u32_out)) temp_package_both.
Fail Next Obligation.


Notation "'combine_inp'" :=(
  int32 '× int32 : choice_type) (in custom pack_type at level 2).
Notation "'combine_inp'" :=(int32 '× int32 : ChoiceEquality) (at level 2).
Notation "'combine_out'" :=(
  int32 : choice_type) (in custom pack_type at level 2).
Notation "'combine_out'" :=(int32 : ChoiceEquality) (at level 2).
Definition COMBINE : nat :=
  1552.
Program Definition combine
  : both_package (fset.fset0) [interface] [(COMBINE,(
      combine_inp,combine_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(lower_1550 , upper_1551) := temp_inp : int32 '× int32 in
    
    ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) ((
            lift_to_both0 lower_1550) .| ((
              lift_to_both0 upper_1551) shift_left (lift_to_both0 (
                @repr U32 16))))
        ) : both (fset.fset0) [interface] (int32)))in
  both_package' _ _ (COMBINE,(combine_inp,combine_out)) temp_package_both.
Fail Next Obligation.

Definition intermediate_b_1556_loc : ChoiceEqualityLocation :=
  (int32 ; 1557%nat).
Definition a_1553_loc : ChoiceEqualityLocation :=
  (int32 ; 1558%nat).
Definition b_1554_loc : ChoiceEqualityLocation :=
  (int32 ; 1559%nat).
Definition intermediate_a_1555_loc : ChoiceEqualityLocation :=
  (int32 ; 1560%nat).
Notation "'update_fletcher_inp'" :=(
  fletcher_t '× seq int16 : choice_type) (in custom pack_type at level 2).
Notation "'update_fletcher_inp'" :=(
  fletcher_t '× seq int16 : ChoiceEquality) (at level 2).
Notation "'update_fletcher_out'" :=(
  fletcher_t : choice_type) (in custom pack_type at level 2).
Notation "'update_fletcher_out'" :=(fletcher_t : ChoiceEquality) (at level 2).
Definition UPDATE_FLETCHER : nat :=
  1568.
Program Definition update_fletcher
  : both_package (CEfset (
      [a_1553_loc ; b_1554_loc ; intermediate_a_1555_loc ; intermediate_b_1556_loc])) [interface
  #val #[ MAX_CHUNK_SIZE ] : max_chunk_size_inp → max_chunk_size_out ;
  #val #[ REDUCE_U32 ] : reduce_u32_inp → reduce_u32_out ] [(UPDATE_FLETCHER,(
      update_fletcher_inp,update_fletcher_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(f_1562 , data_1563) := temp_inp : fletcher_t '× seq int16 in
    
    let max_chunk_size := package_both max_chunk_size tt in
    let reduce_u32 := fun x_0 => package_both reduce_u32 (x_0) in
    ((letb max_chunk_size_1561 : uint_size := max_chunk_size  in
        letb '(a_1553, b_1554) : (int32 '× int32) := lift_to_both0 f_1562 in
        letb '(a_1553, b_1554) :=
          foldi_both' (lift_to_both0 (usize 0)) (seq_num_chunks (
                lift_to_both0 data_1563) (
                lift_to_both0 max_chunk_size_1561)) prod_ce(a_1553, b_1554
            ) (L := (CEfset (
                [a_1553_loc ; b_1554_loc ; intermediate_a_1555_loc ; intermediate_b_1556_loc]))) (I := (
              [interface
              #val #[ MAX_CHUNK_SIZE ] : max_chunk_size_inp → max_chunk_size_out ;
              #val #[ REDUCE_U32 ] : reduce_u32_inp → reduce_u32_out
              ])) (fun i_1564 '(a_1553, b_1554) =>
            letb '(chunk_len_1565, chunk_1566) : (uint_size '× seq int16) :=
              seq_get_chunk (lift_to_both0 data_1563) (
                lift_to_both0 max_chunk_size_1561) (lift_to_both0 i_1564) in
            letbm intermediate_a_1555 : int32 loc( intermediate_a_1555_loc ) :=
              lift_to_both0 a_1553 in
            letbm intermediate_b_1556 : int32 loc( intermediate_b_1556_loc ) :=
              lift_to_both0 b_1554 in
            letb '(intermediate_a_1555, intermediate_b_1556) :=
              foldi_both' (lift_to_both0 (usize 0)) (
                  lift_to_both0 chunk_len_1565) prod_ce(
                  intermediate_a_1555,
                  intermediate_b_1556
                ) (L := (CEfset (
                    [a_1553_loc ; b_1554_loc ; intermediate_a_1555_loc ; intermediate_b_1556_loc]))) (I := (
                  [interface
                  #val #[ REDUCE_U32 ] : reduce_u32_inp → reduce_u32_out
                  ])) (fun j_1567 '(intermediate_a_1555, intermediate_b_1556) =>
                letbm intermediate_a_1555 loc( intermediate_a_1555_loc ) :=
                  (lift_to_both0 intermediate_a_1555) .+ (@cast _ uint32 _ (
                      seq_index (chunk_1566) (lift_to_both0 j_1567))) in
                letbm intermediate_b_1556 loc( intermediate_b_1556_loc ) :=
                  (lift_to_both0 intermediate_b_1556) .+ (
                    lift_to_both0 intermediate_a_1555) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                    lift_to_both0 intermediate_a_1555,
                    lift_to_both0 intermediate_b_1556
                  ))
                ) in
            letbm a_1553 loc( a_1553_loc ) :=
              reduce_u32 (lift_to_both0 intermediate_a_1555) in
            letbm b_1554 loc( b_1554_loc ) :=
              reduce_u32 (lift_to_both0 intermediate_b_1556) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                lift_to_both0 a_1553,
                lift_to_both0 b_1554
              ))
            ) in
        letbm a_1553 loc( a_1553_loc ) := reduce_u32 (lift_to_both0 a_1553) in
        letbm b_1554 loc( b_1554_loc ) := reduce_u32 (lift_to_both0 b_1554) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
            lift_to_both0 a_1553,
            lift_to_both0 b_1554
          ))
        ) : both (CEfset (
          [a_1553_loc ; b_1554_loc ; intermediate_a_1555_loc ; intermediate_b_1556_loc])) [interface
      #val #[ MAX_CHUNK_SIZE ] : max_chunk_size_inp → max_chunk_size_out ;
      #val #[ REDUCE_U32 ] : reduce_u32_inp → reduce_u32_out ] (
        fletcher_t)))in
  both_package' _ _ (UPDATE_FLETCHER,(
      update_fletcher_inp,update_fletcher_out)) temp_package_both.
Fail Next Obligation.


Notation "'value_inp'" :=(
  fletcher_t : choice_type) (in custom pack_type at level 2).
Notation "'value_inp'" :=(fletcher_t : ChoiceEquality) (at level 2).
Notation "'value_out'" :=(int32 : choice_type) (in custom pack_type at level 2).
Notation "'value_out'" :=(int32 : ChoiceEquality) (at level 2).
Definition VALUE : nat :=
  1572.
Program Definition value
  : both_package (fset.fset0) [interface
  #val #[ COMBINE ] : combine_inp → combine_out ] [(VALUE,(
      value_inp,value_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(x_1569) := temp_inp : fletcher_t in
    
    let combine := fun x_0 x_1 => package_both combine (x_0,x_1) in
    ((letb '(a_1570, b_1571) : (int32 '× int32) := lift_to_both0 x_1569 in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (combine (
            lift_to_both0 a_1570) (lift_to_both0 b_1571))
        ) : both (fset.fset0) [interface
      #val #[ COMBINE ] : combine_inp → combine_out ] (int32)))in
  both_package' _ _ (VALUE,(value_inp,value_out)) temp_package_both.
Fail Next Obligation.

Notation "'header_t'" := ((int32 '× int32 '× int32 '× int32
)) : hacspec_scope.

Definition u16_seq_1573_loc : ChoiceEqualityLocation :=
  (seq int16 ; 1574%nat).
Notation "'header_as_u16_slice_inp'" :=(
  header_t : choice_type) (in custom pack_type at level 2).
Notation "'header_as_u16_slice_inp'" :=(header_t : ChoiceEquality) (at level 2).
Notation "'header_as_u16_slice_out'" :=(
  seq int16 : choice_type) (in custom pack_type at level 2).
Notation "'header_as_u16_slice_out'" :=(
  seq int16 : ChoiceEquality) (at level 2).
Definition HEADER_AS_U16_SLICE : nat :=
  1591.
Program Definition header_as_u16_slice
  : both_package (CEfset ([u16_seq_1573_loc])) [interface] [(
    HEADER_AS_U16_SLICE,(header_as_u16_slice_inp,header_as_u16_slice_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(h_1575) := temp_inp : header_t in
    
    ((letb '(magic_1576, seq_number_1577, start_addr_1578, _) : (
            int32 '×
            int32 '×
            int32 '×
            int32
          ) :=
          lift_to_both0 h_1575 in
        letb magic_1579 : u32_word_t :=
          u32_to_be_bytes (lift_to_both0 magic_1576) in
        letb seq_number_1580 : u32_word_t :=
          u32_to_be_bytes (lift_to_both0 seq_number_1577) in
        letb start_addr_1581 : u32_word_t :=
          u32_to_be_bytes (lift_to_both0 start_addr_1578) in
        letb u8_seq_1582 : seq int8 :=
          seq_new_ (default : int8) (lift_to_both0 (usize 12)) in
        letb u8_seq_1583 : seq int8 :=
          seq_update_slice (lift_to_both0 u8_seq_1582) (lift_to_both0 (
              usize 0)) (array_to_seq (lift_to_both0 magic_1579)) (
            lift_to_both0 (usize 0)) (lift_to_both0 (usize 4)) in
        letb u8_seq_1584 : seq int8 :=
          seq_update_slice (lift_to_both0 u8_seq_1583) (lift_to_both0 (
              usize 4)) (array_to_seq (lift_to_both0 seq_number_1580)) (
            lift_to_both0 (usize 0)) (lift_to_both0 (usize 4)) in
        letb u8_seq_1585 : seq int8 :=
          seq_update_slice (lift_to_both0 u8_seq_1584) (lift_to_both0 (
              usize 8)) (array_to_seq (lift_to_both0 start_addr_1581)) (
            lift_to_both0 (usize 0)) (lift_to_both0 (usize 4)) in
        letbm u16_seq_1573 : seq int16 loc( u16_seq_1573_loc ) :=
          seq_new_ (default : int16) (lift_to_both0 (usize 6)) in
        letb u16_seq_1573 :=
          foldi_both' (lift_to_both0 (usize 0)) (lift_to_both0 (
                usize 3)) u16_seq_1573 (L := (CEfset (
                [u16_seq_1573_loc]))) (I := (
              [interface])) (fun i_1586 u16_seq_1573 =>
            letb u16_word_1587 : u16_word_t :=
              array_from_seq (2) (seq_slice (lift_to_both0 u8_seq_1585) ((
                    lift_to_both0 i_1586) .* (lift_to_both0 (usize 4))) (
                  lift_to_both0 (usize 2))) in
            letb u16_value_1588 : int16 :=
              u16_from_be_bytes (lift_to_both0 u16_word_1587) in
            letb u16_seq_1573 : seq int16 :=
              seq_upd u16_seq_1573 (((lift_to_both0 (usize 2)) .* (
                    lift_to_both0 i_1586)) .+ (lift_to_both0 (usize 1))) (
                is_pure (lift_to_both0 u16_value_1588)) in
            letb u16_word_1589 : u16_word_t :=
              array_from_seq (2) (seq_slice (lift_to_both0 u8_seq_1585) (((
                      lift_to_both0 i_1586) .* (lift_to_both0 (usize 4))) .+ (
                    lift_to_both0 (usize 2))) (lift_to_both0 (usize 2))) in
            letb u16_value_1590 : int16 :=
              u16_from_be_bytes (lift_to_both0 u16_word_1589) in
            letb u16_seq_1573 : seq int16 :=
              seq_upd u16_seq_1573 ((lift_to_both0 (usize 2)) .* (
                  lift_to_both0 i_1586)) (is_pure (
                  lift_to_both0 u16_value_1590)) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 u16_seq_1573)
            ) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          lift_to_both0 u16_seq_1573)
        ) : both (CEfset ([u16_seq_1573_loc])) [interface] (seq int16)))in
  both_package' _ _ (HEADER_AS_U16_SLICE,(
      header_as_u16_slice_inp,header_as_u16_slice_out)) temp_package_both.
Fail Next Obligation.

Definition result_1592_loc : ChoiceEqualityLocation :=
  (bool_ChoiceEquality ; 1593%nat).
Notation "'is_valid_header_inp'" :=(
  header_t : choice_type) (in custom pack_type at level 2).
Notation "'is_valid_header_inp'" :=(header_t : ChoiceEquality) (at level 2).
Notation "'is_valid_header_out'" :=(
  bool_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'is_valid_header_out'" :=(
  bool_ChoiceEquality : ChoiceEquality) (at level 2).
Definition IS_VALID_HEADER : nat :=
  1603.
Program Definition is_valid_header
  : both_package (CEfset ([result_1592_loc])) [interface
  #val #[ HEADER_AS_U16_SLICE ] : header_as_u16_slice_inp → header_as_u16_slice_out ;
  #val #[ NEW_FLETCHER ] : new_fletcher_inp → new_fletcher_out ;
  #val #[ UPDATE_FLETCHER ] : update_fletcher_inp → update_fletcher_out ;
  #val #[ VALUE ] : value_inp → value_out ] [(IS_VALID_HEADER,(
      is_valid_header_inp,is_valid_header_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(h_1594) := temp_inp : header_t in
    
    let header_as_u16_slice := fun x_0 => package_both header_as_u16_slice (
      x_0) in
    let new_fletcher := package_both new_fletcher tt in
    let update_fletcher := fun x_0 x_1 => package_both update_fletcher (
      x_0,x_1) in
    let value := fun x_0 => package_both value (x_0) in
    ((letb '(magic_number_1595, seq_number_1596, start_addr_1597, checksum_1598
          ) : (int32 '× int32 '× int32 '× int32) :=
          lift_to_both0 h_1594 in
        letb slice_1599 : seq int16 :=
          header_as_u16_slice (prod_b(
              lift_to_both0 magic_number_1595,
              lift_to_both0 seq_number_1596,
              lift_to_both0 start_addr_1597,
              lift_to_both0 checksum_1598
            )) in
        letbm result_1592 : bool_ChoiceEquality loc( result_1592_loc ) :=
          lift_to_both0 ((false : bool_ChoiceEquality)) in
        letb 'result_1592 :=
          if (lift_to_both0 magic_number_1595) =.? (
            lift_to_both0 riotboot_magic_v) :bool_ChoiceEquality
          then lift_scope (L1 := CEfset ([result_1592_loc])) (L2 := CEfset (
            [result_1592_loc])) (I1 := [interface
          #val #[ NEW_FLETCHER ] : new_fletcher_inp → new_fletcher_out ;
          #val #[ UPDATE_FLETCHER ] : update_fletcher_inp → update_fletcher_out ;
          #val #[ VALUE ] : value_inp → value_out ]) (I2 := [interface
          #val #[ HEADER_AS_U16_SLICE ] : header_as_u16_slice_inp → header_as_u16_slice_out ;
          #val #[ NEW_FLETCHER ] : new_fletcher_inp → new_fletcher_out ;
          #val #[ UPDATE_FLETCHER ] : update_fletcher_inp → update_fletcher_out ;
          #val #[ VALUE ] : value_inp → value_out
          ]) (H_loc_incl := _) (H_opsig_incl := _) (letb fletcher_1600 : (
                int32 '×
                int32
              ) :=
              new_fletcher  in
            letb fletcher_1601 : (int32 '× int32) :=
              update_fletcher (lift_to_both0 fletcher_1600) (
                lift_to_both0 slice_1599) in
            letb sum_1602 : int32 := value (lift_to_both0 fletcher_1601) in
            letbm result_1592 loc( result_1592_loc ) :=
              (lift_to_both0 sum_1602) =.? (lift_to_both0 checksum_1598) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 result_1592)
            )
          else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 result_1592)
           in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          lift_to_both0 result_1592)
        ) : both (CEfset ([result_1592_loc])) [interface
      #val #[ HEADER_AS_U16_SLICE ] : header_as_u16_slice_inp → header_as_u16_slice_out ;
      #val #[ NEW_FLETCHER ] : new_fletcher_inp → new_fletcher_out ;
      #val #[ UPDATE_FLETCHER ] : update_fletcher_inp → update_fletcher_out ;
      #val #[ VALUE ] : value_inp → value_out ] (bool_ChoiceEquality)))in
  both_package' _ _ (IS_VALID_HEADER,(
      is_valid_header_inp,is_valid_header_out)) temp_package_both.
Fail Next Obligation.

Definition image_1604_loc : ChoiceEqualityLocation :=
  (int32 ; 1606%nat).
Definition image_found_1605_loc : ChoiceEqualityLocation :=
  (bool_ChoiceEquality ; 1607%nat).
Notation "'choose_image_inp'" :=(
  seq header_t : choice_type) (in custom pack_type at level 2).
Notation "'choose_image_inp'" :=(seq header_t : ChoiceEquality) (at level 2).
Notation "'choose_image_out'" :=((bool_ChoiceEquality '× int32
  ) : choice_type) (in custom pack_type at level 2).
Notation "'choose_image_out'" :=((bool_ChoiceEquality '× int32
  ) : ChoiceEquality) (at level 2).
Definition CHOOSE_IMAGE : nat :=
  1616.
Program Definition choose_image
  : both_package (CEfset ([image_1604_loc ; image_found_1605_loc])) [interface
  #val #[ IS_VALID_HEADER ] : is_valid_header_inp → is_valid_header_out ] [(
    CHOOSE_IMAGE,(choose_image_inp,choose_image_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(images_1608) := temp_inp : seq header_t in
    
    let is_valid_header := fun x_0 => package_both is_valid_header (x_0) in
    ((letbm image_1604 : int32 loc( image_1604_loc ) :=
          lift_to_both0 (@repr U32 0) in
        letbm image_found_1605 : bool_ChoiceEquality loc( image_found_1605_loc ) :=
          lift_to_both0 ((false : bool_ChoiceEquality)) in
        letb '(image_1604, image_found_1605) :=
          foldi_both' (lift_to_both0 (usize 0)) (seq_len (
                lift_to_both0 images_1608)) prod_ce(image_1604, image_found_1605
            ) (L := (CEfset ([image_1604_loc ; image_found_1605_loc]))) (I := (
              [interface
              #val #[ IS_VALID_HEADER ] : is_valid_header_inp → is_valid_header_out
              ])) (fun i_1609 '(image_1604, image_found_1605) =>
            letb header_1610 : (int32 '× int32 '× int32 '× int32) :=
              seq_index (images_1608) (lift_to_both0 i_1609) in
            letb '(
                magic_number_1611,
                seq_number_1612,
                start_addr_1613,
                checksum_1614
              ) : (int32 '× int32 '× int32 '× int32) :=
              lift_to_both0 header_1610 in
            letb '(image_1604, image_found_1605) :=
              if is_valid_header (prod_b(
                  lift_to_both0 magic_number_1611,
                  lift_to_both0 seq_number_1612,
                  lift_to_both0 start_addr_1613,
                  lift_to_both0 checksum_1614
                )) :bool_ChoiceEquality
              then lift_scope (L1 := CEfset (
                [image_1604_loc ; image_found_1605_loc])) (L2 := CEfset (
                [image_1604_loc ; image_found_1605_loc])) (I1 := [interface]) (I2 := [interface
              #val #[ IS_VALID_HEADER ] : is_valid_header_inp → is_valid_header_out
              ]) (H_loc_incl := _) (H_opsig_incl := _) (
                letb change_image_1615 : bool_ChoiceEquality :=
                  negb ((lift_to_both0 image_found_1605) && ((
                        lift_to_both0 seq_number_1612) <=.? (
                        lift_to_both0 image_1604))) in
                letb '(image_1604, image_found_1605) :=
                  if lift_to_both0 change_image_1615 :bool_ChoiceEquality
                  then lift_scope (L1 := CEfset (
                    [image_1604_loc ; image_found_1605_loc])) (L2 := CEfset (
                    [image_1604_loc ; image_found_1605_loc])) (I1 := [interface]) (I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
                    letbm image_1604 loc( image_1604_loc ) :=
                      lift_to_both0 start_addr_1613 in
                    letbm image_found_1605 loc( image_found_1605_loc ) :=
                      lift_to_both0 ((true : bool_ChoiceEquality)) in
                    lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                        lift_to_both0 image_1604,
                        lift_to_both0 image_found_1605
                      ))
                    )
                  else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                      lift_to_both0 image_1604,
                      lift_to_both0 image_found_1605
                    ))
                   in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                    lift_to_both0 image_1604,
                    lift_to_both0 image_found_1605
                  ))
                )
              else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                  lift_to_both0 image_1604,
                  lift_to_both0 image_found_1605
                ))
               in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                lift_to_both0 image_1604,
                lift_to_both0 image_found_1605
              ))
            ) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
            lift_to_both0 image_found_1605,
            lift_to_both0 image_1604
          ))
        ) : both (CEfset ([image_1604_loc ; image_found_1605_loc])) [interface
      #val #[ IS_VALID_HEADER ] : is_valid_header_inp → is_valid_header_out
      ] ((bool_ChoiceEquality '× int32))))in
  both_package' _ _ (CHOOSE_IMAGE,(
      choose_image_inp,choose_image_out)) temp_package_both.
Fail Next Obligation.

