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
  1666.
Program Definition new_fletcher  : both (fset.fset0) [interface] (fletcher_t) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 (@repr U32 65535),
          lift_to_both0 (@repr U32 65535)
        ))
      ) : both (fset.fset0) [interface] (fletcher_t)).
Fail Next Obligation.


Notation "'max_chunk_size_inp'" :=(
  unit_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'max_chunk_size_inp'" :=(
  unit_ChoiceEquality : ChoiceEquality) (at level 2).
Notation "'max_chunk_size_out'" :=(
  uint_size : choice_type) (in custom pack_type at level 2).
Notation "'max_chunk_size_out'" :=(uint_size : ChoiceEquality) (at level 2).
Definition MAX_CHUNK_SIZE : nat :=
  1667.
Program Definition max_chunk_size 
  : both (fset.fset0) [interface] (uint_size) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 (usize 360))
      ) : both (fset.fset0) [interface] (uint_size)).
Fail Next Obligation.


Notation "'reduce_u32_inp'" :=(
  int32 : choice_type) (in custom pack_type at level 2).
Notation "'reduce_u32_inp'" :=(int32 : ChoiceEquality) (at level 2).
Notation "'reduce_u32_out'" :=(
  int32 : choice_type) (in custom pack_type at level 2).
Notation "'reduce_u32_out'" :=(int32 : ChoiceEquality) (at level 2).
Definition REDUCE_U32 : nat :=
  1669.
Program Definition reduce_u32 (x_1668 : int32)
  : both (fset.fset0) [interface] (int32) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (((
            lift_to_both0 x_1668) .& (lift_to_both0 (@repr U32 65535))) .+ ((
            lift_to_both0 x_1668) shift_right (lift_to_both0 (@repr U32 16))))
      ) : both (fset.fset0) [interface] (int32)).
Fail Next Obligation.


Notation "'combine_inp'" :=(
  int32 '× int32 : choice_type) (in custom pack_type at level 2).
Notation "'combine_inp'" :=(int32 '× int32 : ChoiceEquality) (at level 2).
Notation "'combine_out'" :=(
  int32 : choice_type) (in custom pack_type at level 2).
Notation "'combine_out'" :=(int32 : ChoiceEquality) (at level 2).
Definition COMBINE : nat :=
  1672.
Program Definition combine (lower_1670 : int32) (upper_1671 : int32)
  : both (fset.fset0) [interface] (int32) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) ((
          lift_to_both0 lower_1670) .| ((lift_to_both0 upper_1671) shift_left (
            lift_to_both0 (@repr U32 16))))
      ) : both (fset.fset0) [interface] (int32)).
Fail Next Obligation.

Definition b_1674_loc : ChoiceEqualityLocation :=
  (int32 ; 1677%nat).
Definition intermediate_b_1676_loc : ChoiceEqualityLocation :=
  (int32 ; 1678%nat).
Definition a_1673_loc : ChoiceEqualityLocation :=
  (int32 ; 1679%nat).
Definition intermediate_a_1675_loc : ChoiceEqualityLocation :=
  (int32 ; 1680%nat).
Notation "'update_fletcher_inp'" :=(
  fletcher_t '× seq int16 : choice_type) (in custom pack_type at level 2).
Notation "'update_fletcher_inp'" :=(
  fletcher_t '× seq int16 : ChoiceEquality) (at level 2).
Notation "'update_fletcher_out'" :=(
  fletcher_t : choice_type) (in custom pack_type at level 2).
Notation "'update_fletcher_out'" :=(fletcher_t : ChoiceEquality) (at level 2).
Definition UPDATE_FLETCHER : nat :=
  1688.
Program Definition update_fletcher (f_1682 : fletcher_t) (data_1683 : seq int16)
  : both (CEfset (
      [a_1673_loc ; b_1674_loc ; intermediate_a_1675_loc ; intermediate_b_1676_loc])) [interface] (
    fletcher_t) :=
  ((letb max_chunk_size_1681 : uint_size := max_chunk_size  in
      letb '(a_1673, b_1674) : (int32 '× int32) := lift_to_both0 f_1682 in
      letb '(a_1673, b_1674) :=
        foldi_both' (lift_to_both0 (usize 0)) (seq_num_chunks (
              lift_to_both0 data_1683) (
              lift_to_both0 max_chunk_size_1681)) prod_ce(a_1673, b_1674) (
            L := (CEfset (
                [a_1673_loc ; b_1674_loc ; intermediate_a_1675_loc ; intermediate_b_1676_loc]))) (
            I := [interface]) (fun i_1684 '(a_1673, b_1674) =>
            letb '(chunk_len_1685, chunk_1686) : (uint_size '× seq int16) :=
              seq_get_chunk (lift_to_both0 data_1683) (
                lift_to_both0 max_chunk_size_1681) (lift_to_both0 i_1684) in
            letbm intermediate_a_1675 : int32 loc( intermediate_a_1675_loc ) :=
              lift_to_both0 a_1673 in
            letbm intermediate_b_1676 : int32 loc( intermediate_b_1676_loc ) :=
              lift_to_both0 b_1674 in
            letb '(intermediate_a_1675, intermediate_b_1676) :=
              foldi_both' (lift_to_both0 (usize 0)) (
                  lift_to_both0 chunk_len_1685) prod_ce(
                  intermediate_a_1675,
                  intermediate_b_1676
                ) (L := (CEfset (
                      [a_1673_loc ; b_1674_loc ; intermediate_a_1675_loc ; intermediate_b_1676_loc]))) (
                  I := [interface]) (fun j_1687 '(
                    intermediate_a_1675,
                    intermediate_b_1676
                  ) =>
                  letbm intermediate_a_1675 loc( intermediate_a_1675_loc ) :=
                    (lift_to_both0 intermediate_a_1675) .+ (@cast _ uint32 _ (
                        seq_index (chunk_1686) (lift_to_both0 j_1687))) in
                  letbm intermediate_b_1676 loc( intermediate_b_1676_loc ) :=
                    (lift_to_both0 intermediate_b_1676) .+ (
                      lift_to_both0 intermediate_a_1675) in
                  lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                      lift_to_both0 intermediate_a_1675,
                      lift_to_both0 intermediate_b_1676
                    ))
                  ) in
            letbm a_1673 loc( a_1673_loc ) :=
              reduce_u32 (lift_to_both0 intermediate_a_1675) in
            letbm b_1674 loc( b_1674_loc ) :=
              reduce_u32 (lift_to_both0 intermediate_b_1676) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                lift_to_both0 a_1673,
                lift_to_both0 b_1674
              ))
            ) in
      letbm a_1673 loc( a_1673_loc ) := reduce_u32 (lift_to_both0 a_1673) in
      letbm b_1674 loc( b_1674_loc ) := reduce_u32 (lift_to_both0 b_1674) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 a_1673,
          lift_to_both0 b_1674
        ))
      ) : both (CEfset (
        [a_1673_loc ; b_1674_loc ; intermediate_a_1675_loc ; intermediate_b_1676_loc])) [interface] (
      fletcher_t)).
Fail Next Obligation.


Notation "'value_inp'" :=(
  fletcher_t : choice_type) (in custom pack_type at level 2).
Notation "'value_inp'" :=(fletcher_t : ChoiceEquality) (at level 2).
Notation "'value_out'" :=(int32 : choice_type) (in custom pack_type at level 2).
Notation "'value_out'" :=(int32 : ChoiceEquality) (at level 2).
Definition VALUE : nat :=
  1692.
Program Definition value (x_1689 : fletcher_t)
  : both (fset.fset0) [interface] (int32) :=
  ((letb '(a_1690, b_1691) : (int32 '× int32) := lift_to_both0 x_1689 in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (combine (
          lift_to_both0 a_1690) (lift_to_both0 b_1691))
      ) : both (fset.fset0) [interface] (int32)).
Fail Next Obligation.

Notation "'header_t'" := ((int32 '× int32 '× int32 '× int32
)) : hacspec_scope.

Definition u16_seq_1693_loc : ChoiceEqualityLocation :=
  (seq int16 ; 1694%nat).
Notation "'header_as_u16_slice_inp'" :=(
  header_t : choice_type) (in custom pack_type at level 2).
Notation "'header_as_u16_slice_inp'" :=(header_t : ChoiceEquality) (at level 2).
Notation "'header_as_u16_slice_out'" :=(
  seq int16 : choice_type) (in custom pack_type at level 2).
Notation "'header_as_u16_slice_out'" :=(
  seq int16 : ChoiceEquality) (at level 2).
Definition HEADER_AS_U16_SLICE : nat :=
  1711.
Program Definition header_as_u16_slice (h_1695 : header_t)
  : both (CEfset ([u16_seq_1693_loc])) [interface] (seq int16) :=
  ((letb '(magic_1696, seq_number_1697, start_addr_1698, _) : (
          int32 '×
          int32 '×
          int32 '×
          int32
        ) :=
        lift_to_both0 h_1695 in
      letb magic_1699 : u32_word_t :=
        u32_to_be_bytes (lift_to_both0 magic_1696) in
      letb seq_number_1700 : u32_word_t :=
        u32_to_be_bytes (lift_to_both0 seq_number_1697) in
      letb start_addr_1701 : u32_word_t :=
        u32_to_be_bytes (lift_to_both0 start_addr_1698) in
      letb u8_seq_1702 : seq int8 :=
        seq_new_ (default : int8) (lift_to_both0 (usize 12)) in
      letb u8_seq_1703 : seq int8 :=
        seq_update_slice (lift_to_both0 u8_seq_1702) (lift_to_both0 (usize 0)) (
          array_to_seq (lift_to_both0 magic_1699)) (lift_to_both0 (usize 0)) (
          lift_to_both0 (usize 4)) in
      letb u8_seq_1704 : seq int8 :=
        seq_update_slice (lift_to_both0 u8_seq_1703) (lift_to_both0 (usize 4)) (
          array_to_seq (lift_to_both0 seq_number_1700)) (lift_to_both0 (
            usize 0)) (lift_to_both0 (usize 4)) in
      letb u8_seq_1705 : seq int8 :=
        seq_update_slice (lift_to_both0 u8_seq_1704) (lift_to_both0 (usize 8)) (
          array_to_seq (lift_to_both0 start_addr_1701)) (lift_to_both0 (
            usize 0)) (lift_to_both0 (usize 4)) in
      letbm u16_seq_1693 : seq int16 loc( u16_seq_1693_loc ) :=
        seq_new_ (default : int16) (lift_to_both0 (usize 6)) in
      letb u16_seq_1693 :=
        foldi_both' (lift_to_both0 (usize 0)) (lift_to_both0 (
              usize 3)) u16_seq_1693 (L := (CEfset ([u16_seq_1693_loc]))) (
            I := [interface]) (fun i_1706 u16_seq_1693 =>
            letb u16_word_1707 : u16_word_t :=
              array_from_seq (2) (seq_slice (lift_to_both0 u8_seq_1705) ((
                    lift_to_both0 i_1706) .* (lift_to_both0 (usize 4))) (
                  lift_to_both0 (usize 2))) in
            letb u16_value_1708 : int16 :=
              u16_from_be_bytes (lift_to_both0 u16_word_1707) in
            letb u16_seq_1693 : seq int16 :=
              seq_upd u16_seq_1693 (((lift_to_both0 (usize 2)) .* (
                    lift_to_both0 i_1706)) .+ (lift_to_both0 (usize 1))) (
                is_pure (lift_to_both0 u16_value_1708)) in
            letb u16_word_1709 : u16_word_t :=
              array_from_seq (2) (seq_slice (lift_to_both0 u8_seq_1705) (((
                      lift_to_both0 i_1706) .* (lift_to_both0 (usize 4))) .+ (
                    lift_to_both0 (usize 2))) (lift_to_both0 (usize 2))) in
            letb u16_value_1710 : int16 :=
              u16_from_be_bytes (lift_to_both0 u16_word_1709) in
            letb u16_seq_1693 : seq int16 :=
              seq_upd u16_seq_1693 ((lift_to_both0 (usize 2)) .* (
                  lift_to_both0 i_1706)) (is_pure (
                  lift_to_both0 u16_value_1710)) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 u16_seq_1693)
            ) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        lift_to_both0 u16_seq_1693)
      ) : both (CEfset ([u16_seq_1693_loc])) [interface] (seq int16)).
Fail Next Obligation.

Definition result_1712_loc : ChoiceEqualityLocation :=
  (bool_ChoiceEquality ; 1713%nat).
Notation "'is_valid_header_inp'" :=(
  header_t : choice_type) (in custom pack_type at level 2).
Notation "'is_valid_header_inp'" :=(header_t : ChoiceEquality) (at level 2).
Notation "'is_valid_header_out'" :=(
  bool_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'is_valid_header_out'" :=(
  bool_ChoiceEquality : ChoiceEquality) (at level 2).
Definition IS_VALID_HEADER : nat :=
  1723.
Program Definition is_valid_header (h_1714 : header_t)
  : both (CEfset (
      [a_1673_loc ; b_1674_loc ; intermediate_a_1675_loc ; intermediate_b_1676_loc ; u16_seq_1693_loc ; result_1712_loc])) [interface] (
    bool_ChoiceEquality) :=
  ((letb '(magic_number_1715, seq_number_1716, start_addr_1717, checksum_1718
        ) : (int32 '× int32 '× int32 '× int32) :=
        lift_to_both0 h_1714 in
      letb slice_1719 : seq int16 :=
        header_as_u16_slice (prod_b(
            lift_to_both0 magic_number_1715,
            lift_to_both0 seq_number_1716,
            lift_to_both0 start_addr_1717,
            lift_to_both0 checksum_1718
          )) in
      letbm result_1712 : bool_ChoiceEquality loc( result_1712_loc ) :=
        lift_to_both0 ((false : bool_ChoiceEquality)) in
      letb '(result_1712) :=
        if (lift_to_both0 magic_number_1715) =.? (
          lift_to_both0 riotboot_magic_v) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset (
            [a_1673_loc ; b_1674_loc ; intermediate_a_1675_loc ; intermediate_b_1676_loc ; u16_seq_1693_loc ; result_1712_loc])) (
          L2 := CEfset (
            [a_1673_loc ; b_1674_loc ; intermediate_a_1675_loc ; intermediate_b_1676_loc ; u16_seq_1693_loc ; result_1712_loc])) (
          I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
          letb fletcher_1720 : (int32 '× int32) := new_fletcher  in
          letb fletcher_1721 : (int32 '× int32) :=
            update_fletcher (lift_to_both0 fletcher_1720) (
              lift_to_both0 slice_1719) in
          letb sum_1722 : int32 := value (lift_to_both0 fletcher_1721) in
          letbm result_1712 loc( result_1712_loc ) :=
            (lift_to_both0 sum_1722) =.? (lift_to_both0 checksum_1718) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 result_1712)
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          lift_to_both0 result_1712)
         in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        lift_to_both0 result_1712)
      ) : both (CEfset (
        [a_1673_loc ; b_1674_loc ; intermediate_a_1675_loc ; intermediate_b_1676_loc ; u16_seq_1693_loc ; result_1712_loc])) [interface] (
      bool_ChoiceEquality)).
Fail Next Obligation.

Definition image_1724_loc : ChoiceEqualityLocation :=
  (int32 ; 1726%nat).
Definition image_found_1725_loc : ChoiceEqualityLocation :=
  (bool_ChoiceEquality ; 1727%nat).
Notation "'choose_image_inp'" :=(
  seq header_t : choice_type) (in custom pack_type at level 2).
Notation "'choose_image_inp'" :=(seq header_t : ChoiceEquality) (at level 2).
Notation "'choose_image_out'" :=((bool_ChoiceEquality '× int32
  ) : choice_type) (in custom pack_type at level 2).
Notation "'choose_image_out'" :=((bool_ChoiceEquality '× int32
  ) : ChoiceEquality) (at level 2).
Definition CHOOSE_IMAGE : nat :=
  1736.
Program Definition choose_image (images_1728 : seq header_t)
  : both (CEfset (
      [a_1673_loc ; b_1674_loc ; intermediate_a_1675_loc ; intermediate_b_1676_loc ; u16_seq_1693_loc ; result_1712_loc ; image_1724_loc ; image_found_1725_loc])) [interface] (
    (bool_ChoiceEquality '× int32)) :=
  ((letbm image_1724 : int32 loc( image_1724_loc ) :=
        lift_to_both0 (@repr U32 0) in
      letbm image_found_1725 : bool_ChoiceEquality loc( image_found_1725_loc ) :=
        lift_to_both0 ((false : bool_ChoiceEquality)) in
      letb '(image_1724, image_found_1725) :=
        foldi_both' (lift_to_both0 (usize 0)) (seq_len (
              lift_to_both0 images_1728)) prod_ce(image_1724, image_found_1725
          ) (L := (CEfset (
                [a_1673_loc ; b_1674_loc ; intermediate_a_1675_loc ; intermediate_b_1676_loc ; u16_seq_1693_loc ; result_1712_loc ; image_1724_loc ; image_found_1725_loc]))) (
            I := [interface]) (fun i_1729 '(image_1724, image_found_1725) =>
            letb header_1730 : (int32 '× int32 '× int32 '× int32) :=
              seq_index (images_1728) (lift_to_both0 i_1729) in
            letb '(
                magic_number_1731,
                seq_number_1732,
                start_addr_1733,
                checksum_1734
              ) : (int32 '× int32 '× int32 '× int32) :=
              lift_to_both0 header_1730 in
            letb '(image_1724, image_found_1725) :=
              if is_valid_header (prod_b(
                  lift_to_both0 magic_number_1731,
                  lift_to_both0 seq_number_1732,
                  lift_to_both0 start_addr_1733,
                  lift_to_both0 checksum_1734
                )) :bool_ChoiceEquality
              then lift_scope (L1 := CEfset (
                  [a_1673_loc ; b_1674_loc ; intermediate_a_1675_loc ; intermediate_b_1676_loc ; u16_seq_1693_loc ; result_1712_loc ; image_1724_loc ; image_found_1725_loc])) (
                L2 := CEfset (
                  [a_1673_loc ; b_1674_loc ; intermediate_a_1675_loc ; intermediate_b_1676_loc ; u16_seq_1693_loc ; result_1712_loc ; image_1724_loc ; image_found_1725_loc])) (
                I1 := [interface]) (
                I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
                letb change_image_1735 : bool_ChoiceEquality :=
                  negb ((lift_to_both0 image_found_1725) && ((
                        lift_to_both0 seq_number_1732) <=.? (
                        lift_to_both0 image_1724))) in
                letb '(image_1724, image_found_1725) :=
                  if lift_to_both0 change_image_1735 :bool_ChoiceEquality
                  then lift_scope (L1 := CEfset (
                      [a_1673_loc ; b_1674_loc ; intermediate_a_1675_loc ; intermediate_b_1676_loc ; u16_seq_1693_loc ; result_1712_loc ; image_1724_loc ; image_found_1725_loc])) (
                    L2 := CEfset (
                      [a_1673_loc ; b_1674_loc ; intermediate_a_1675_loc ; intermediate_b_1676_loc ; u16_seq_1693_loc ; result_1712_loc ; image_1724_loc ; image_found_1725_loc])) (
                    I1 := [interface]) (
                    I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
                    letbm image_1724 loc( image_1724_loc ) :=
                      lift_to_both0 start_addr_1733 in
                    letbm image_found_1725 loc( image_found_1725_loc ) :=
                      lift_to_both0 ((true : bool_ChoiceEquality)) in
                    lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                        lift_to_both0 image_1724,
                        lift_to_both0 image_found_1725
                      ))
                    )
                  else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                      lift_to_both0 image_1724,
                      lift_to_both0 image_found_1725
                    ))
                   in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                    lift_to_both0 image_1724,
                    lift_to_both0 image_found_1725
                  ))
                )
              else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                  lift_to_both0 image_1724,
                  lift_to_both0 image_found_1725
                ))
               in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                lift_to_both0 image_1724,
                lift_to_both0 image_found_1725
              ))
            ) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 image_found_1725,
          lift_to_both0 image_1724
        ))
      ) : both (CEfset (
        [a_1673_loc ; b_1674_loc ; intermediate_a_1675_loc ; intermediate_b_1676_loc ; u16_seq_1693_loc ; result_1712_loc ; image_1724_loc ; image_found_1725_loc])) [interface] (
      (bool_ChoiceEquality '× int32))).
Fail Next Obligation.

