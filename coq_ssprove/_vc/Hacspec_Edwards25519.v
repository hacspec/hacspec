(** This file was automatically generated using Hacspec **)
Set Warnings "-notation-overridden,-ambiguous-paths".
From Crypt Require Import choice_type Package Prelude.
Import PackageNotation.
From extructures Require Import ord fset.
From mathcomp.word Require Import ssrZ word.
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


Require Import Hacspec_Sha512.

Definition field_canvas_t := nseq (int8) (usize 32).
Definition ed25519_field_element_t :=
  nat_mod 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed.

Definition scalar_canvas_t := nseq (int8) (usize 32).
Definition scalar_t :=
  nat_mod 0x1000000000000000000000000000000014def9dea2f79cd65812631a5cf5d3ed.

Definition big_scalar_canvas_t := nseq (int8) (usize 64).
Definition big_scalar_t :=
  nat_mod 0x1000000000000000000000000000000014def9dea2f79cd65812631a5cf5d3ed.

Definition big_integer_canvas_t := nseq (int8) (usize 32).
Definition big_integer_t :=
  nat_mod 0x8000000000000000000000000000000080000000000000000000000000000000.

Notation "'ed_point_t'" := ((
  ed25519_field_element_t '×
  ed25519_field_element_t '×
  ed25519_field_element_t '×
  ed25519_field_element_t
)) : hacspec_scope.

Definition compressed_ed_point_t := nseq (uint8) (usize 32).

Definition serialized_scalar_t := nseq (uint8) (usize 32).

Definition signature_t := nseq (uint8) (usize 64).

Notation "'public_key_t'" := (compressed_ed_point_t) : hacspec_scope.

Notation "'secret_key_t'" := (serialized_scalar_t) : hacspec_scope.

Definition error_t : ChoiceEquality :=
  unit_ChoiceEquality '+ unit_ChoiceEquality '+ unit_ChoiceEquality '+ unit_ChoiceEquality '+ unit_ChoiceEquality '+ unit_ChoiceEquality.
Definition InvalidPublickey : error_t :=
  inl (inl (inl (inl (inl tt)))).
Definition InvalidSignature : error_t :=
  inl (inl (inl (inl (inr tt)))).
Definition InvalidS : error_t :=
  inl (inl (inl (inr tt))).
Definition InvalidR : error_t :=
  inl (inl (inr tt)).
Definition SmallOrderPoint : error_t :=
  inl (inr tt).
Definition NotEnoughRandomness : error_t :=
  inr tt.

Notation "'verify_result_t'" := ((result error_t unit)) : hacspec_scope.

Definition base_v : compressed_ed_point_t :=
  array_from_list uint8 [
    (secret (@repr U8 88)) : uint8;
    (secret (@repr U8 102)) : uint8;
    (secret (@repr U8 102)) : uint8;
    (secret (@repr U8 102)) : uint8;
    (secret (@repr U8 102)) : uint8;
    (secret (@repr U8 102)) : uint8;
    (secret (@repr U8 102)) : uint8;
    (secret (@repr U8 102)) : uint8;
    (secret (@repr U8 102)) : uint8;
    (secret (@repr U8 102)) : uint8;
    (secret (@repr U8 102)) : uint8;
    (secret (@repr U8 102)) : uint8;
    (secret (@repr U8 102)) : uint8;
    (secret (@repr U8 102)) : uint8;
    (secret (@repr U8 102)) : uint8;
    (secret (@repr U8 102)) : uint8;
    (secret (@repr U8 102)) : uint8;
    (secret (@repr U8 102)) : uint8;
    (secret (@repr U8 102)) : uint8;
    (secret (@repr U8 102)) : uint8;
    (secret (@repr U8 102)) : uint8;
    (secret (@repr U8 102)) : uint8;
    (secret (@repr U8 102)) : uint8;
    (secret (@repr U8 102)) : uint8;
    (secret (@repr U8 102)) : uint8;
    (secret (@repr U8 102)) : uint8;
    (secret (@repr U8 102)) : uint8;
    (secret (@repr U8 102)) : uint8;
    (secret (@repr U8 102)) : uint8;
    (secret (@repr U8 102)) : uint8;
    (secret (@repr U8 102)) : uint8;
    (secret (@repr U8 102)) : uint8
  ].

Definition constant_p_v : serialized_scalar_t :=
  array_from_list uint8 [
    (secret (@repr U8 237)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 127)) : uint8
  ].

Definition constant_l_v : serialized_scalar_t :=
  array_from_list uint8 [
    (secret (@repr U8 237)) : uint8;
    (secret (@repr U8 211)) : uint8;
    (secret (@repr U8 245)) : uint8;
    (secret (@repr U8 92)) : uint8;
    (secret (@repr U8 26)) : uint8;
    (secret (@repr U8 99)) : uint8;
    (secret (@repr U8 18)) : uint8;
    (secret (@repr U8 88)) : uint8;
    (secret (@repr U8 214)) : uint8;
    (secret (@repr U8 156)) : uint8;
    (secret (@repr U8 247)) : uint8;
    (secret (@repr U8 162)) : uint8;
    (secret (@repr U8 222)) : uint8;
    (secret (@repr U8 249)) : uint8;
    (secret (@repr U8 222)) : uint8;
    (secret (@repr U8 20)) : uint8;
    (secret (@repr U8 0)) : uint8;
    (secret (@repr U8 0)) : uint8;
    (secret (@repr U8 0)) : uint8;
    (secret (@repr U8 0)) : uint8;
    (secret (@repr U8 0)) : uint8;
    (secret (@repr U8 0)) : uint8;
    (secret (@repr U8 0)) : uint8;
    (secret (@repr U8 0)) : uint8;
    (secret (@repr U8 0)) : uint8;
    (secret (@repr U8 0)) : uint8;
    (secret (@repr U8 0)) : uint8;
    (secret (@repr U8 0)) : uint8;
    (secret (@repr U8 0)) : uint8;
    (secret (@repr U8 0)) : uint8;
    (secret (@repr U8 0)) : uint8;
    (secret (@repr U8 16)) : uint8
  ].

Definition constant_p3_8_v : serialized_scalar_t :=
  array_from_list uint8 [
    (secret (@repr U8 254)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 15)) : uint8
  ].

Definition constant_p1_4_v : serialized_scalar_t :=
  array_from_list uint8 [
    (secret (@repr U8 251)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 31)) : uint8
  ].

Definition constant_d_v : serialized_scalar_t :=
  array_from_list uint8 [
    (secret (@repr U8 163)) : uint8;
    (secret (@repr U8 120)) : uint8;
    (secret (@repr U8 89)) : uint8;
    (secret (@repr U8 19)) : uint8;
    (secret (@repr U8 202)) : uint8;
    (secret (@repr U8 77)) : uint8;
    (secret (@repr U8 235)) : uint8;
    (secret (@repr U8 117)) : uint8;
    (secret (@repr U8 171)) : uint8;
    (secret (@repr U8 216)) : uint8;
    (secret (@repr U8 65)) : uint8;
    (secret (@repr U8 65)) : uint8;
    (secret (@repr U8 77)) : uint8;
    (secret (@repr U8 10)) : uint8;
    (secret (@repr U8 112)) : uint8;
    (secret (@repr U8 0)) : uint8;
    (secret (@repr U8 152)) : uint8;
    (secret (@repr U8 232)) : uint8;
    (secret (@repr U8 121)) : uint8;
    (secret (@repr U8 119)) : uint8;
    (secret (@repr U8 121)) : uint8;
    (secret (@repr U8 64)) : uint8;
    (secret (@repr U8 199)) : uint8;
    (secret (@repr U8 140)) : uint8;
    (secret (@repr U8 115)) : uint8;
    (secret (@repr U8 254)) : uint8;
    (secret (@repr U8 111)) : uint8;
    (secret (@repr U8 43)) : uint8;
    (secret (@repr U8 238)) : uint8;
    (secret (@repr U8 108)) : uint8;
    (secret (@repr U8 3)) : uint8;
    (secret (@repr U8 82)) : uint8
  ].


Notation "'is_negative_inp'" :=(
  ed25519_field_element_t : choice_type) (in custom pack_type at level 2).
Notation "'is_negative_inp'" :=(
  ed25519_field_element_t : ChoiceEquality) (at level 2).
Notation "'is_negative_out'" :=(
  uint8 : choice_type) (in custom pack_type at level 2).
Notation "'is_negative_out'" :=(uint8 : ChoiceEquality) (at level 2).
Definition IS_NEGATIVE : nat :=
  2739.
Program Definition is_negative (x_2738 : ed25519_field_element_t)
  : both (fset.fset0) [interface] (uint8) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        if is_pure (I := [interface]) (nat_mod_bit (lift_to_both0 x_2738) (
            lift_to_both0 (usize 0)))
        then secret (lift_to_both0 (@repr U8 1))
        else secret (lift_to_both0 (@repr U8 0)))
      ) : both (fset.fset0) [interface] (uint8)).
Fail Next Obligation.

Definition s_2740_loc : ChoiceEqualityLocation :=
  (byte_seq ; 2741%nat).
Notation "'compress_inp'" :=(
  ed_point_t : choice_type) (in custom pack_type at level 2).
Notation "'compress_inp'" :=(ed_point_t : ChoiceEquality) (at level 2).
Notation "'compress_out'" :=(
  compressed_ed_point_t : choice_type) (in custom pack_type at level 2).
Notation "'compress_out'" :=(
  compressed_ed_point_t : ChoiceEquality) (at level 2).
Definition COMPRESS : nat :=
  2749.
Program Definition compress (p_2742 : ed_point_t)
  : both (CEfset ([s_2740_loc])) [interface] (compressed_ed_point_t) :=
  ((letb '(x_2743, y_2744, z_2745, _) : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        lift_to_both0 p_2742 in
      letb z_inv_2746 : ed25519_field_element_t :=
        nat_mod_inv (lift_to_both0 z_2745) in
      letb x_2747 : ed25519_field_element_t :=
        (lift_to_both0 x_2743) *% (lift_to_both0 z_inv_2746) in
      letb y_2748 : ed25519_field_element_t :=
        (lift_to_both0 y_2744) *% (lift_to_both0 z_inv_2746) in
      letbm s_2740 : byte_seq loc( s_2740_loc ) :=
        nat_mod_to_byte_seq_le (lift_to_both0 y_2748) in
      letb s_2740 : seq uint8 :=
        seq_upd s_2740 (lift_to_both0 (usize 31)) (is_pure ((seq_index (
                s_2740) (lift_to_both0 (usize 31))) .^ ((is_negative (
                  lift_to_both0 x_2747)) shift_left (lift_to_both0 (
                  usize 7))))) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (array_from_slice (
          default : uint8) (32) (lift_to_both0 s_2740) (lift_to_both0 (
            usize 0)) (lift_to_both0 (usize 32)))
      ) : both (CEfset ([s_2740_loc])) [interface] (compressed_ed_point_t)).
Fail Next Obligation.

Definition result_2750_loc : ChoiceEqualityLocation :=
  ((option (ed25519_field_element_t)) ; 2751%nat).
Notation "'sqrt_inp'" :=(
  ed25519_field_element_t : choice_type) (in custom pack_type at level 2).
Notation "'sqrt_inp'" :=(ed25519_field_element_t : ChoiceEquality) (at level 2).
Notation "'sqrt_out'" :=((option (
      ed25519_field_element_t)) : choice_type) (in custom pack_type at level 2).
Notation "'sqrt_out'" :=((option (
      ed25519_field_element_t)) : ChoiceEquality) (at level 2).
Definition SQRT : nat :=
  2757.
Program Definition sqrt (a_2754 : ed25519_field_element_t)
  : both (CEfset ([result_2750_loc])) [interface] ((option (
        ed25519_field_element_t))) :=
  ((letb p3_8_2752 : ed25519_field_element_t :=
        nat_mod_from_byte_seq_le (
          array_to_seq (lift_to_both0 constant_p3_8_v)) in
      letb p1_4_2753 : ed25519_field_element_t :=
        nat_mod_from_byte_seq_le (
          array_to_seq (lift_to_both0 constant_p1_4_v)) in
      letb x_c_2755 : ed25519_field_element_t :=
        nat_mod_pow_self (lift_to_both0 a_2754) (lift_to_both0 p3_8_2752) in
      letbm result_2750 : (option (
            ed25519_field_element_t)) loc( result_2750_loc ) :=
        @None ed25519_field_element_t in
      letb '(result_2750) :=
        if ((lift_to_both0 x_c_2755) *% (lift_to_both0 x_c_2755)) =.? (
          lift_to_both0 a_2754) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset ([result_2750_loc])) (L2 := CEfset (
            [result_2750_loc])) (I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
          letbm result_2750 loc( result_2750_loc ) :=
            some (lift_to_both0 x_c_2755) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 result_2750)
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          lift_to_both0 result_2750)
         in
      letb '(result_2750) :=
        if ((lift_to_both0 x_c_2755) *% (lift_to_both0 x_c_2755)) =.? ((
            nat_mod_zero ) -% (lift_to_both0 a_2754)) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset ([result_2750_loc])) (L2 := CEfset (
            [result_2750_loc])) (I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
          letb x_2756 : ed25519_field_element_t :=
            (nat_mod_pow_self (nat_mod_two ) (lift_to_both0 p1_4_2753)) *% (
              lift_to_both0 x_c_2755) in
          letbm result_2750 loc( result_2750_loc ) :=
            some (lift_to_both0 x_2756) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 result_2750)
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          lift_to_both0 result_2750)
         in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        lift_to_both0 result_2750)
      ) : both (CEfset ([result_2750_loc])) [interface] ((option (
          ed25519_field_element_t)))).
Fail Next Obligation.


Notation "'check_canonical_point_inp'" :=(
  compressed_ed_point_t : choice_type) (in custom pack_type at level 2).
Notation "'check_canonical_point_inp'" :=(
  compressed_ed_point_t : ChoiceEquality) (at level 2).
Notation "'check_canonical_point_out'" :=(
  bool_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'check_canonical_point_out'" :=(
  bool_ChoiceEquality : ChoiceEquality) (at level 2).
Definition CHECK_CANONICAL_POINT : nat :=
  2760.
Program Definition check_canonical_point (x_2758 : compressed_ed_point_t)
  : both (fset.fset0) [interface] (bool_ChoiceEquality) :=
  ((letb x_2758 : compressed_ed_point_t :=
        array_upd x_2758 (lift_to_both0 (usize 31)) (is_pure ((array_index (
                x_2758) (lift_to_both0 (usize 31))) .& (secret (lift_to_both0 (
                  @repr U8 127))))) in
      letb x_2759 : big_integer_t :=
        nat_mod_from_byte_seq_le (array_to_seq (lift_to_both0 x_2758)) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) ((
          lift_to_both0 x_2759) <.? (nat_mod_from_byte_seq_le (
            array_to_seq (lift_to_both0 constant_p_v))))
      ) : both (fset.fset0) [interface] (bool_ChoiceEquality)).
Fail Next Obligation.

Definition y_s_2761_loc : ChoiceEqualityLocation :=
  (compressed_ed_point_t ; 2763%nat).
Definition x_2762_loc : ChoiceEqualityLocation :=
  (ed25519_field_element_t ; 2764%nat).
Notation "'decompress_inp'" :=(
  compressed_ed_point_t : choice_type) (in custom pack_type at level 2).
Notation "'decompress_inp'" :=(
  compressed_ed_point_t : ChoiceEquality) (at level 2).
Notation "'decompress_out'" :=((option (
      ed_point_t)) : choice_type) (in custom pack_type at level 2).
Notation "'decompress_out'" :=((option (
      ed_point_t)) : ChoiceEquality) (at level 2).
Definition DECOMPRESS : nat :=
  2775.
Program Definition decompress (q_2766 : compressed_ed_point_t)
  : both (CEfset ([result_2750_loc ; y_s_2761_loc ; x_2762_loc])) [interface] ((
      option (ed_point_t))) :=
  ((letb d_2765 : ed25519_field_element_t :=
        nat_mod_from_byte_seq_le (array_to_seq (lift_to_both0 constant_d_v)) in
      letb x_s_2767 : uint8 :=
        ((array_index (q_2766) (lift_to_both0 (usize 31))) .& (secret (
              lift_to_both0 (@repr U8 128)))) shift_right (lift_to_both0 (
            usize 7)) in
      letbm y_s_2761 : compressed_ed_point_t loc( y_s_2761_loc ) :=
        lift_to_both0 q_2766 in
      letb y_s_2761 : compressed_ed_point_t :=
        array_upd y_s_2761 (lift_to_both0 (usize 31)) (is_pure ((array_index (
                y_s_2761) (lift_to_both0 (usize 31))) .& (secret (
                lift_to_both0 (@repr U8 127))))) in
      letbnd(ChoiceEqualityMonad.option_bind_both) 'tt :=
        if negb (check_canonical_point (
            lift_to_both0 y_s_2761)) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset ([y_s_2761_loc])) (L2 := CEfset (
            [result_2750_loc ; y_s_2761_loc ; x_2762_loc])) (
          I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (letbnd(
              _) _ : ed_point_t :=
            @None ed_point_t in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            @Some unit_ChoiceEquality (lift_to_both0 (
                (tt : unit_ChoiceEquality))))
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          @Some unit_ChoiceEquality (lift_to_both0 (
              (tt : unit_ChoiceEquality))))
         in
      letb y_2768 : ed25519_field_element_t :=
        nat_mod_from_byte_seq_le (array_to_seq (lift_to_both0 y_s_2761)) in
      letb z_2769 : ed25519_field_element_t := nat_mod_one  in
      letb yy_2770 : ed25519_field_element_t :=
        (lift_to_both0 y_2768) *% (lift_to_both0 y_2768) in
      letb u_2771 : ed25519_field_element_t :=
        (lift_to_both0 yy_2770) -% (lift_to_both0 z_2769) in
      letb v_2772 : ed25519_field_element_t :=
        ((lift_to_both0 d_2765) *% (lift_to_both0 yy_2770)) +% (
          lift_to_both0 z_2769) in
      letb xx_2773 : ed25519_field_element_t :=
        (lift_to_both0 u_2771) *% (nat_mod_inv (lift_to_both0 v_2772)) in
      letbndm(_) x_2762 : ed25519_field_element_t :=
        sqrt (lift_to_both0 xx_2773) in
      letb x_r_2774 : uint8 := is_negative (lift_to_both0 x_2762) in
      letbnd(ChoiceEqualityMonad.option_bind_both) 'tt :=
        if ((lift_to_both0 x_2762) =.? (nat_mod_zero )) && ((uint8_declassify (
              lift_to_both0 x_s_2767)) =.? (lift_to_both0 (
              @repr U8 1))) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset (
            [result_2750_loc ; y_s_2761_loc ; x_2762_loc])) (L2 := CEfset (
            [result_2750_loc ; y_s_2761_loc ; x_2762_loc])) (
          I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (letbnd(
              _) _ : ed_point_t :=
            @None ed_point_t in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            @Some unit_ChoiceEquality (lift_to_both0 (
                (tt : unit_ChoiceEquality))))
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          @Some unit_ChoiceEquality (lift_to_both0 (
              (tt : unit_ChoiceEquality))))
         in
      letb '(x_2762) :=
        if (uint8_declassify (lift_to_both0 x_r_2774)) !=.? (uint8_declassify (
            lift_to_both0 x_s_2767)) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset (
            [result_2750_loc ; y_s_2761_loc ; x_2762_loc])) (L2 := CEfset (
            [result_2750_loc ; y_s_2761_loc ; x_2762_loc])) (
          I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
          letbm x_2762 loc( x_2762_loc ) :=
            (nat_mod_zero ) -% (lift_to_both0 x_2762) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 x_2762)
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          lift_to_both0 x_2762)
         in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (some (prod_b(
            lift_to_both0 x_2762,
            lift_to_both0 y_2768,
            lift_to_both0 z_2769,
            (lift_to_both0 x_2762) *% (lift_to_both0 y_2768)
          )))
      ) : both (CEfset (
        [result_2750_loc ; y_s_2761_loc ; x_2762_loc])) [interface] ((option (
          ed_point_t)))).
Fail Next Obligation.

Definition x_2777_loc : ChoiceEqualityLocation :=
  (ed25519_field_element_t ; 2778%nat).
Definition y_s_2776_loc : ChoiceEqualityLocation :=
  (compressed_ed_point_t ; 2779%nat).
Notation "'decompress_non_canonical_inp'" :=(
  compressed_ed_point_t : choice_type) (in custom pack_type at level 2).
Notation "'decompress_non_canonical_inp'" :=(
  compressed_ed_point_t : ChoiceEquality) (at level 2).
Notation "'decompress_non_canonical_out'" :=((option (
      ed_point_t)) : choice_type) (in custom pack_type at level 2).
Notation "'decompress_non_canonical_out'" :=((option (
      ed_point_t)) : ChoiceEquality) (at level 2).
Definition DECOMPRESS_NON_CANONICAL : nat :=
  2790.
Program Definition decompress_non_canonical (p_2781 : compressed_ed_point_t)
  : both (CEfset ([result_2750_loc ; y_s_2776_loc ; x_2777_loc])) [interface] ((
      option (ed_point_t))) :=
  ((letb d_2780 : ed25519_field_element_t :=
        nat_mod_from_byte_seq_le (array_to_seq (lift_to_both0 constant_d_v)) in
      letb x_s_2782 : uint8 :=
        ((array_index (p_2781) (lift_to_both0 (usize 31))) .& (secret (
              lift_to_both0 (@repr U8 128)))) shift_right (lift_to_both0 (
            usize 7)) in
      letbm y_s_2776 : compressed_ed_point_t loc( y_s_2776_loc ) :=
        lift_to_both0 p_2781 in
      letb y_s_2776 : compressed_ed_point_t :=
        array_upd y_s_2776 (lift_to_both0 (usize 31)) (is_pure ((array_index (
                y_s_2776) (lift_to_both0 (usize 31))) .& (secret (
                lift_to_both0 (@repr U8 127))))) in
      letb y_2783 : ed25519_field_element_t :=
        nat_mod_from_byte_seq_le (array_to_seq (lift_to_both0 y_s_2776)) in
      letb z_2784 : ed25519_field_element_t := nat_mod_one  in
      letb yy_2785 : ed25519_field_element_t :=
        (lift_to_both0 y_2783) *% (lift_to_both0 y_2783) in
      letb u_2786 : ed25519_field_element_t :=
        (lift_to_both0 yy_2785) -% (lift_to_both0 z_2784) in
      letb v_2787 : ed25519_field_element_t :=
        ((lift_to_both0 d_2780) *% (lift_to_both0 yy_2785)) +% (
          lift_to_both0 z_2784) in
      letb xx_2788 : ed25519_field_element_t :=
        (lift_to_both0 u_2786) *% (nat_mod_inv (lift_to_both0 v_2787)) in
      letbndm(_) x_2777 : ed25519_field_element_t :=
        sqrt (lift_to_both0 xx_2788) in
      letb x_r_2789 : uint8 := is_negative (lift_to_both0 x_2777) in
      letb '(x_2777) :=
        if (uint8_declassify (lift_to_both0 x_r_2789)) !=.? (uint8_declassify (
            lift_to_both0 x_s_2782)) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset (
            [result_2750_loc ; y_s_2776_loc ; x_2777_loc])) (L2 := CEfset (
            [result_2750_loc ; y_s_2776_loc ; x_2777_loc])) (
          I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
          letbm x_2777 loc( x_2777_loc ) :=
            (nat_mod_zero ) -% (lift_to_both0 x_2777) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 x_2777)
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          lift_to_both0 x_2777)
         in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (some (prod_b(
            lift_to_both0 x_2777,
            lift_to_both0 y_2783,
            lift_to_both0 z_2784,
            (lift_to_both0 x_2777) *% (lift_to_both0 y_2783)
          )))
      ) : both (CEfset (
        [result_2750_loc ; y_s_2776_loc ; x_2777_loc])) [interface] ((option (
          ed_point_t)))).
Fail Next Obligation.

Definition s_2791_loc : ChoiceEqualityLocation :=
  (byte_seq ; 2792%nat).
Notation "'encode_inp'" :=(
  ed_point_t : choice_type) (in custom pack_type at level 2).
Notation "'encode_inp'" :=(ed_point_t : ChoiceEquality) (at level 2).
Notation "'encode_out'" :=(
  byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'encode_out'" :=(byte_seq : ChoiceEquality) (at level 2).
Definition ENCODE : nat :=
  2800.
Program Definition encode (p_2793 : ed_point_t)
  : both (CEfset ([s_2791_loc])) [interface] (byte_seq) :=
  ((letb '(x_2794, y_2795, z_2796, _) : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        lift_to_both0 p_2793 in
      letb z_inv_2797 : ed25519_field_element_t :=
        nat_mod_inv (lift_to_both0 z_2796) in
      letb x_2798 : ed25519_field_element_t :=
        (lift_to_both0 x_2794) *% (lift_to_both0 z_inv_2797) in
      letb y_2799 : ed25519_field_element_t :=
        (lift_to_both0 y_2795) *% (lift_to_both0 z_inv_2797) in
      letbm s_2791 : byte_seq loc( s_2791_loc ) :=
        nat_mod_to_byte_seq_le (lift_to_both0 y_2799) in
      letb s_2791 : seq uint8 :=
        seq_upd s_2791 (lift_to_both0 (usize 31)) (is_pure ((seq_index (
                s_2791) (lift_to_both0 (usize 31))) .^ ((is_negative (
                  lift_to_both0 x_2798)) shift_left (lift_to_both0 (
                  usize 7))))) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 s_2791)
      ) : both (CEfset ([s_2791_loc])) [interface] (byte_seq)).
Fail Next Obligation.


Notation "'decode_inp'" :=(
  byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'decode_inp'" :=(byte_seq : ChoiceEquality) (at level 2).
Notation "'decode_out'" :=((option (
      ed_point_t)) : choice_type) (in custom pack_type at level 2).
Notation "'decode_out'" :=((option (ed_point_t)) : ChoiceEquality) (at level 2).
Definition DECODE : nat :=
  2803.
Program Definition decode (q_s_2801 : byte_seq)
  : both (CEfset ([result_2750_loc ; y_s_2761_loc ; x_2762_loc])) [interface] ((
      option (ed_point_t))) :=
  ((letb q_2802 : compressed_ed_point_t :=
        array_from_slice (default : uint8) (32) (lift_to_both0 q_s_2801) (
          lift_to_both0 (usize 0)) (lift_to_both0 (usize 32)) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (decompress (
          lift_to_both0 q_2802))
      ) : both (CEfset (
        [result_2750_loc ; y_s_2761_loc ; x_2762_loc])) [interface] ((option (
          ed_point_t)))).
Fail Next Obligation.


Notation "'point_add_inp'" :=(
  ed_point_t '× ed_point_t : choice_type) (in custom pack_type at level 2).
Notation "'point_add_inp'" :=(
  ed_point_t '× ed_point_t : ChoiceEquality) (at level 2).
Notation "'point_add_out'" :=(
  ed_point_t : choice_type) (in custom pack_type at level 2).
Notation "'point_add_out'" :=(ed_point_t : ChoiceEquality) (at level 2).
Definition POINT_ADD : nat :=
  2828.
Program Definition point_add (p_2806 : ed_point_t) (q_2811 : ed_point_t)
  : both (fset.fset0) [interface] (ed_point_t) :=
  ((letb d_c_2804 : ed25519_field_element_t :=
        nat_mod_from_byte_seq_le (array_to_seq (lift_to_both0 constant_d_v)) in
      letb two_2805 : ed25519_field_element_t := nat_mod_two  in
      letb '(x1_2807, y1_2808, z1_2809, t1_2810) : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        lift_to_both0 p_2806 in
      letb '(x2_2812, y2_2813, z2_2814, t2_2815) : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        lift_to_both0 q_2811 in
      letb a_2816 : ed25519_field_element_t :=
        ((lift_to_both0 y1_2808) -% (lift_to_both0 x1_2807)) *% ((
            lift_to_both0 y2_2813) -% (lift_to_both0 x2_2812)) in
      letb b_2817 : ed25519_field_element_t :=
        ((lift_to_both0 y1_2808) +% (lift_to_both0 x1_2807)) *% ((
            lift_to_both0 y2_2813) +% (lift_to_both0 x2_2812)) in
      letb c_2818 : ed25519_field_element_t :=
        (((lift_to_both0 t1_2810) *% (lift_to_both0 two_2805)) *% (
            lift_to_both0 d_c_2804)) *% (lift_to_both0 t2_2815) in
      letb d_2819 : ed25519_field_element_t :=
        ((lift_to_both0 z1_2809) *% (lift_to_both0 two_2805)) *% (
          lift_to_both0 z2_2814) in
      letb e_2820 : ed25519_field_element_t :=
        (lift_to_both0 b_2817) -% (lift_to_both0 a_2816) in
      letb f_2821 : ed25519_field_element_t :=
        (lift_to_both0 d_2819) -% (lift_to_both0 c_2818) in
      letb g_2822 : ed25519_field_element_t :=
        (lift_to_both0 d_2819) +% (lift_to_both0 c_2818) in
      letb h_2823 : ed25519_field_element_t :=
        (lift_to_both0 b_2817) +% (lift_to_both0 a_2816) in
      letb x3_2824 : ed25519_field_element_t :=
        (lift_to_both0 e_2820) *% (lift_to_both0 f_2821) in
      letb y3_2825 : ed25519_field_element_t :=
        (lift_to_both0 g_2822) *% (lift_to_both0 h_2823) in
      letb t3_2826 : ed25519_field_element_t :=
        (lift_to_both0 e_2820) *% (lift_to_both0 h_2823) in
      letb z3_2827 : ed25519_field_element_t :=
        (lift_to_both0 f_2821) *% (lift_to_both0 g_2822) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 x3_2824,
          lift_to_both0 y3_2825,
          lift_to_both0 z3_2827,
          lift_to_both0 t3_2826
        ))
      ) : both (fset.fset0) [interface] (ed_point_t)).
Fail Next Obligation.


Notation "'point_identity_inp'" :=(
  unit_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'point_identity_inp'" :=(
  unit_ChoiceEquality : ChoiceEquality) (at level 2).
Notation "'point_identity_out'" :=(
  ed_point_t : choice_type) (in custom pack_type at level 2).
Notation "'point_identity_out'" :=(ed_point_t : ChoiceEquality) (at level 2).
Definition POINT_IDENTITY : nat :=
  2829.
Program Definition point_identity 
  : both (fset.fset0) [interface] (ed_point_t) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          nat_mod_zero ,
          nat_mod_one ,
          nat_mod_one ,
          nat_mod_zero 
        ))
      ) : both (fset.fset0) [interface] (ed_point_t)).
Fail Next Obligation.

Definition q_2831_loc : ChoiceEqualityLocation :=
  ((
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t
    ) ; 2832%nat).
Definition p_2830_loc : ChoiceEqualityLocation :=
  ((
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t
    ) ; 2833%nat).
Notation "'point_mul_inp'" :=(
  scalar_t '× ed_point_t : choice_type) (in custom pack_type at level 2).
Notation "'point_mul_inp'" :=(
  scalar_t '× ed_point_t : ChoiceEquality) (at level 2).
Notation "'point_mul_out'" :=(
  ed_point_t : choice_type) (in custom pack_type at level 2).
Notation "'point_mul_out'" :=(ed_point_t : ChoiceEquality) (at level 2).
Definition POINT_MUL : nat :=
  2837.
Program Definition point_mul (s_2836 : scalar_t) (p_2834 : ed_point_t)
  : both (CEfset ([p_2830_loc ; q_2831_loc])) [interface] (ed_point_t) :=
  ((letbm p_2830 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) loc( p_2830_loc ) :=
        lift_to_both0 p_2834 in
      letbm q_2831 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) loc( q_2831_loc ) :=
        point_identity  in
      letb '(p_2830, q_2831) :=
        foldi_both' (lift_to_both0 (usize 0)) (lift_to_both0 (
              usize 256)) prod_ce(p_2830, q_2831) (L := (CEfset (
                [p_2830_loc ; q_2831_loc]))) (I := [interface]) (fun i_2835 '(
              p_2830,
              q_2831
            ) =>
            letb '(q_2831) :=
              if nat_mod_bit (lift_to_both0 s_2836) (
                lift_to_both0 i_2835) :bool_ChoiceEquality
              then lift_scope (L1 := CEfset ([p_2830_loc ; q_2831_loc])) (
                L2 := CEfset ([p_2830_loc ; q_2831_loc])) (I1 := [interface]) (
                I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
                letbm q_2831 loc( q_2831_loc ) :=
                  point_add (lift_to_both0 q_2831) (lift_to_both0 p_2830) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                  lift_to_both0 q_2831)
                )
              else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                lift_to_both0 q_2831)
               in
            letbm p_2830 loc( p_2830_loc ) :=
              point_add (lift_to_both0 p_2830) (lift_to_both0 p_2830) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                lift_to_both0 p_2830,
                lift_to_both0 q_2831
              ))
            ) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 q_2831)
      ) : both (CEfset ([p_2830_loc ; q_2831_loc])) [interface] (ed_point_t)).
Fail Next Obligation.


Notation "'point_mul_by_cofactor_inp'" :=(
  ed_point_t : choice_type) (in custom pack_type at level 2).
Notation "'point_mul_by_cofactor_inp'" :=(
  ed_point_t : ChoiceEquality) (at level 2).
Notation "'point_mul_by_cofactor_out'" :=(
  ed_point_t : choice_type) (in custom pack_type at level 2).
Notation "'point_mul_by_cofactor_out'" :=(
  ed_point_t : ChoiceEquality) (at level 2).
Definition POINT_MUL_BY_COFACTOR : nat :=
  2842.
Program Definition point_mul_by_cofactor (p_2838 : ed_point_t)
  : both (fset.fset0) [interface] (ed_point_t) :=
  ((letb p2_2839 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_add (lift_to_both0 p_2838) (lift_to_both0 p_2838) in
      letb p4_2840 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_add (lift_to_both0 p2_2839) (lift_to_both0 p2_2839) in
      letb p8_2841 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_add (lift_to_both0 p4_2840) (lift_to_both0 p4_2840) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 p8_2841)
      ) : both (fset.fset0) [interface] (ed_point_t)).
Fail Next Obligation.


Notation "'point_neg_inp'" :=(
  ed_point_t : choice_type) (in custom pack_type at level 2).
Notation "'point_neg_inp'" :=(ed_point_t : ChoiceEquality) (at level 2).
Notation "'point_neg_out'" :=(
  ed_point_t : choice_type) (in custom pack_type at level 2).
Notation "'point_neg_out'" :=(ed_point_t : ChoiceEquality) (at level 2).
Definition POINT_NEG : nat :=
  2848.
Program Definition point_neg (p_2843 : ed_point_t)
  : both (fset.fset0) [interface] (ed_point_t) :=
  ((letb '(x_2844, y_2845, z_2846, t_2847) : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        lift_to_both0 p_2843 in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          (nat_mod_zero ) -% (lift_to_both0 x_2844),
          lift_to_both0 y_2845,
          lift_to_both0 z_2846,
          (nat_mod_zero ) -% (lift_to_both0 t_2847)
        ))
      ) : both (fset.fset0) [interface] (ed_point_t)).
Fail Next Obligation.


Notation "'point_eq_inp'" :=(
  ed_point_t '× ed_point_t : choice_type) (in custom pack_type at level 2).
Notation "'point_eq_inp'" :=(
  ed_point_t '× ed_point_t : ChoiceEquality) (at level 2).
Notation "'point_eq_out'" :=(
  bool_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'point_eq_out'" :=(bool_ChoiceEquality : ChoiceEquality) (at level 2).
Definition POINT_EQ : nat :=
  2857.
Program Definition point_eq (p_2849 : ed_point_t) (q_2853 : ed_point_t)
  : both (fset.fset0) [interface] (bool_ChoiceEquality) :=
  ((letb '(x1_2850, y1_2851, z1_2852, _) : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        lift_to_both0 p_2849 in
      letb '(x2_2854, y2_2855, z2_2856, _) : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        lift_to_both0 q_2853 in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) ((((
              lift_to_both0 x1_2850) *% (lift_to_both0 z2_2856)) =.? ((
              lift_to_both0 x2_2854) *% (lift_to_both0 z1_2852))) && (((
              lift_to_both0 y1_2851) *% (lift_to_both0 z2_2856)) =.? ((
              lift_to_both0 y2_2855) *% (lift_to_both0 z1_2852))))
      ) : both (fset.fset0) [interface] (bool_ChoiceEquality)).
Fail Next Obligation.


Notation "'point_normalize_inp'" :=(
  ed_point_t : choice_type) (in custom pack_type at level 2).
Notation "'point_normalize_inp'" :=(ed_point_t : ChoiceEquality) (at level 2).
Notation "'point_normalize_out'" :=(
  ed_point_t : choice_type) (in custom pack_type at level 2).
Notation "'point_normalize_out'" :=(ed_point_t : ChoiceEquality) (at level 2).
Definition POINT_NORMALIZE : nat :=
  2866.
Program Definition point_normalize (q_2858 : ed_point_t)
  : both (fset.fset0) [interface] (ed_point_t) :=
  ((letb '(qx_2859, qy_2860, qz_2861, _) : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        lift_to_both0 q_2858 in
      letb px_2862 : ed25519_field_element_t :=
        (lift_to_both0 qx_2859) *% (nat_mod_inv (lift_to_both0 qz_2861)) in
      letb py_2863 : ed25519_field_element_t :=
        (lift_to_both0 qy_2860) *% (nat_mod_inv (lift_to_both0 qz_2861)) in
      letb pz_2864 : ed25519_field_element_t := nat_mod_one  in
      letb pt_2865 : ed25519_field_element_t :=
        (lift_to_both0 px_2862) *% (lift_to_both0 py_2863) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 px_2862,
          lift_to_both0 py_2863,
          lift_to_both0 pz_2864,
          lift_to_both0 pt_2865
        ))
      ) : both (fset.fset0) [interface] (ed_point_t)).
Fail Next Obligation.

Definition s_2867_loc : ChoiceEqualityLocation :=
  (serialized_scalar_t ; 2868%nat).
Notation "'secret_expand_inp'" :=(
  secret_key_t : choice_type) (in custom pack_type at level 2).
Notation "'secret_expand_inp'" :=(secret_key_t : ChoiceEquality) (at level 2).
Notation "'secret_expand_out'" :=((serialized_scalar_t '× serialized_scalar_t
  ) : choice_type) (in custom pack_type at level 2).
Notation "'secret_expand_out'" :=((serialized_scalar_t '× serialized_scalar_t
  ) : ChoiceEquality) (at level 2).
Definition SECRET_EXPAND : nat :=
  2872.
Program Definition secret_expand (sk_2869 : secret_key_t)
  : both (CEfset ([s_2867_loc])) [interface] ((
      serialized_scalar_t '×
      serialized_scalar_t
    )) :=
  ((letb h_2870 : sha512_digest_t :=
        sha512 (seq_from_slice (lift_to_both0 sk_2869) (lift_to_both0 (
              usize 0)) (lift_to_both0 (usize 32))) in
      letb h_d_2871 : serialized_scalar_t :=
        array_from_slice (default : uint8) (32) (
          array_to_seq (lift_to_both0 h_2870)) (lift_to_both0 (usize 32)) (
          lift_to_both0 (usize 32)) in
      letbm s_2867 : serialized_scalar_t loc( s_2867_loc ) :=
        array_from_slice (default : uint8) (32) (
          array_to_seq (lift_to_both0 h_2870)) (lift_to_both0 (usize 0)) (
          lift_to_both0 (usize 32)) in
      letb s_2867 : serialized_scalar_t :=
        array_upd s_2867 (lift_to_both0 (usize 0)) (is_pure ((array_index (
                s_2867) (lift_to_both0 (usize 0))) .& (secret (lift_to_both0 (
                  @repr U8 248))))) in
      letb s_2867 : serialized_scalar_t :=
        array_upd s_2867 (lift_to_both0 (usize 31)) (is_pure ((array_index (
                s_2867) (lift_to_both0 (usize 31))) .& (secret (lift_to_both0 (
                  @repr U8 127))))) in
      letb s_2867 : serialized_scalar_t :=
        array_upd s_2867 (lift_to_both0 (usize 31)) (is_pure ((array_index (
                s_2867) (lift_to_both0 (usize 31))) .| (secret (lift_to_both0 (
                  @repr U8 64))))) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 s_2867,
          lift_to_both0 h_d_2871
        ))
      ) : both (CEfset ([s_2867_loc])) [interface] ((
        serialized_scalar_t '×
        serialized_scalar_t
      ))).
Fail Next Obligation.


Notation "'secret_to_public_inp'" :=(
  secret_key_t : choice_type) (in custom pack_type at level 2).
Notation "'secret_to_public_inp'" :=(
  secret_key_t : ChoiceEquality) (at level 2).
Notation "'secret_to_public_out'" :=(
  public_key_t : choice_type) (in custom pack_type at level 2).
Notation "'secret_to_public_out'" :=(
  public_key_t : ChoiceEquality) (at level 2).
Definition SECRET_TO_PUBLIC : nat :=
  2878.
Program Definition secret_to_public (sk_2873 : secret_key_t)
  : both (CEfset (
      [s_2740_loc ; result_2750_loc ; y_s_2761_loc ; x_2762_loc ; p_2830_loc ; q_2831_loc ; s_2867_loc])) [interface] (
    public_key_t) :=
  ((letb '(s_2874, _) : (serialized_scalar_t '× serialized_scalar_t) :=
        secret_expand (lift_to_both0 sk_2873) in
      letb base_2875 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        option_unwrap (decompress (lift_to_both0 base_v)) in
      letb ss_2876 : scalar_t :=
        nat_mod_from_byte_seq_le (array_to_seq (lift_to_both0 s_2874)) in
      letb a_2877 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_mul (lift_to_both0 ss_2876) (lift_to_both0 base_2875) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (compress (
          lift_to_both0 a_2877))
      ) : both (CEfset (
        [s_2740_loc ; result_2750_loc ; y_s_2761_loc ; x_2762_loc ; p_2830_loc ; q_2831_loc ; s_2867_loc])) [interface] (
      public_key_t)).
Fail Next Obligation.


Notation "'check_canonical_scalar_inp'" :=(
  serialized_scalar_t : choice_type) (in custom pack_type at level 2).
Notation "'check_canonical_scalar_inp'" :=(
  serialized_scalar_t : ChoiceEquality) (at level 2).
Notation "'check_canonical_scalar_out'" :=(
  bool_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'check_canonical_scalar_out'" :=(
  bool_ChoiceEquality : ChoiceEquality) (at level 2).
Definition CHECK_CANONICAL_SCALAR : nat :=
  2880.
Program Definition check_canonical_scalar (s_2879 : serialized_scalar_t)
  : both (fset.fset0) [interface] (bool_ChoiceEquality) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        if is_pure (I := [interface]) ((uint8_declassify ((array_index (
                  s_2879) (lift_to_both0 (usize 31))) .& (secret (
                  lift_to_both0 (@repr U8 224))))) !=.? (lift_to_both0 (
              @repr U8 0)))
        then lift_to_both0 ((false : bool_ChoiceEquality))
        else (nat_mod_from_byte_seq_le (
            array_to_seq (lift_to_both0 s_2879))) <.? (
          nat_mod_from_byte_seq_le (array_to_seq (lift_to_both0 constant_l_v))))
      ) : both (fset.fset0) [interface] (bool_ChoiceEquality)).
Fail Next Obligation.

