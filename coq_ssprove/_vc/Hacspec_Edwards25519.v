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
  @array_from_list uint8 [
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
  @array_from_list uint8 [
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
  @array_from_list uint8 [
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
  @array_from_list uint8 [
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
  @array_from_list uint8 [
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
  @array_from_list uint8 [
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
  2819.
Program Definition is_negative (x_2818 : ed25519_field_element_t)
  : both (fset.fset0) [interface] (uint8) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        if is_pure (I := [interface]) (nat_mod_bit (lift_to_both0 x_2818) (
            lift_to_both0 (usize 0)))
        then secret (lift_to_both0 (@repr U8 1))
        else secret (lift_to_both0 (@repr U8 0)))
      ) : both (fset.fset0) [interface] (uint8)).
Fail Next Obligation.

Definition s_2820_loc : ChoiceEqualityLocation :=
  (byte_seq ; 2821%nat).
Notation "'compress_inp'" :=(
  ed_point_t : choice_type) (in custom pack_type at level 2).
Notation "'compress_inp'" :=(ed_point_t : ChoiceEquality) (at level 2).
Notation "'compress_out'" :=(
  compressed_ed_point_t : choice_type) (in custom pack_type at level 2).
Notation "'compress_out'" :=(
  compressed_ed_point_t : ChoiceEquality) (at level 2).
Definition COMPRESS : nat :=
  2829.
Program Definition compress (p_2822 : ed_point_t)
  : both (CEfset ([s_2820_loc])) [interface] (compressed_ed_point_t) :=
  ((letb '(x_2823, y_2824, z_2825, _) : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        lift_to_both0 p_2822 in
      letb z_inv_2826 : ed25519_field_element_t :=
        nat_mod_inv (lift_to_both0 z_2825) in
      letb x_2827 : ed25519_field_element_t :=
        (lift_to_both0 x_2823) *% (lift_to_both0 z_inv_2826) in
      letb y_2828 : ed25519_field_element_t :=
        (lift_to_both0 y_2824) *% (lift_to_both0 z_inv_2826) in
      letbm s_2820 : byte_seq loc( s_2820_loc ) :=
        nat_mod_to_byte_seq_le (lift_to_both0 y_2828) in
      letb s_2820 : seq uint8 :=
        seq_upd s_2820 (lift_to_both0 (usize 31)) (is_pure ((seq_index (
                s_2820) (lift_to_both0 (usize 31))) .^ ((is_negative (
                  lift_to_both0 x_2827)) shift_left (lift_to_both0 (
                  usize 7))))) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (array_from_slice (
          default : uint8) (32) (lift_to_both0 s_2820) (lift_to_both0 (
            usize 0)) (lift_to_both0 (usize 32)))
      ) : both (CEfset ([s_2820_loc])) [interface] (compressed_ed_point_t)).
Fail Next Obligation.

Definition result_2830_loc : ChoiceEqualityLocation :=
  ((option (ed25519_field_element_t)) ; 2831%nat).
Notation "'sqrt_inp'" :=(
  ed25519_field_element_t : choice_type) (in custom pack_type at level 2).
Notation "'sqrt_inp'" :=(ed25519_field_element_t : ChoiceEquality) (at level 2).
Notation "'sqrt_out'" :=((option (
      ed25519_field_element_t)) : choice_type) (in custom pack_type at level 2).
Notation "'sqrt_out'" :=((option (
      ed25519_field_element_t)) : ChoiceEquality) (at level 2).
Definition SQRT : nat :=
  2837.
Program Definition sqrt (a_2834 : ed25519_field_element_t)
  : both (CEfset ([result_2830_loc])) [interface] ((option (
        ed25519_field_element_t))) :=
  ((letb p3_8_2832 : ed25519_field_element_t :=
        nat_mod_from_byte_seq_le (
          array_to_seq (lift_to_both0 constant_p3_8_v)) in
      letb p1_4_2833 : ed25519_field_element_t :=
        nat_mod_from_byte_seq_le (
          array_to_seq (lift_to_both0 constant_p1_4_v)) in
      letb x_c_2835 : ed25519_field_element_t :=
        nat_mod_pow_self (lift_to_both0 a_2834) (lift_to_both0 p3_8_2832) in
      letbm result_2830 : (option (
            ed25519_field_element_t)) loc( result_2830_loc ) :=
        @None ed25519_field_element_t in
      letb '(result_2830) :=
        if ((lift_to_both0 x_c_2835) *% (lift_to_both0 x_c_2835)) =.? (
          lift_to_both0 a_2834) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset ([result_2830_loc])) (L2 := CEfset (
            [result_2830_loc])) (I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
          letbm result_2830 loc( result_2830_loc ) :=
            some (lift_to_both0 x_c_2835) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 result_2830)
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          lift_to_both0 result_2830)
         in
      letb '(result_2830) :=
        if ((lift_to_both0 x_c_2835) *% (lift_to_both0 x_c_2835)) =.? ((
            nat_mod_zero ) -% (lift_to_both0 a_2834)) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset ([result_2830_loc])) (L2 := CEfset (
            [result_2830_loc])) (I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
          letb x_2836 : ed25519_field_element_t :=
            (nat_mod_pow_self (nat_mod_two ) (lift_to_both0 p1_4_2833)) *% (
              lift_to_both0 x_c_2835) in
          letbm result_2830 loc( result_2830_loc ) :=
            some (lift_to_both0 x_2836) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 result_2830)
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          lift_to_both0 result_2830)
         in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        lift_to_both0 result_2830)
      ) : both (CEfset ([result_2830_loc])) [interface] ((option (
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
  2840.
Program Definition check_canonical_point (x_2838 : compressed_ed_point_t)
  : both (fset.fset0) [interface] (bool_ChoiceEquality) :=
  ((letb x_2838 : compressed_ed_point_t :=
        array_upd x_2838 (lift_to_both0 (usize 31)) (is_pure ((array_index (
                x_2838) (lift_to_both0 (usize 31))) .& (secret (lift_to_both0 (
                  @repr U8 127))))) in
      letb x_2839 : big_integer_t :=
        nat_mod_from_byte_seq_le (array_to_seq (lift_to_both0 x_2838)) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) ((
          lift_to_both0 x_2839) <.? (nat_mod_from_byte_seq_le (
            array_to_seq (lift_to_both0 constant_p_v))))
      ) : both (fset.fset0) [interface] (bool_ChoiceEquality)).
Fail Next Obligation.

Definition y_s_2841_loc : ChoiceEqualityLocation :=
  (compressed_ed_point_t ; 2843%nat).
Definition x_2842_loc : ChoiceEqualityLocation :=
  (ed25519_field_element_t ; 2844%nat).
Notation "'decompress_inp'" :=(
  compressed_ed_point_t : choice_type) (in custom pack_type at level 2).
Notation "'decompress_inp'" :=(
  compressed_ed_point_t : ChoiceEquality) (at level 2).
Notation "'decompress_out'" :=((option (
      ed_point_t)) : choice_type) (in custom pack_type at level 2).
Notation "'decompress_out'" :=((option (
      ed_point_t)) : ChoiceEquality) (at level 2).
Definition DECOMPRESS : nat :=
  2855.
Program Definition decompress (q_2846 : compressed_ed_point_t)
  : both (CEfset ([result_2830_loc ; y_s_2841_loc ; x_2842_loc])) [interface] ((
      option (ed_point_t))) :=
  ((letb d_2845 : ed25519_field_element_t :=
        nat_mod_from_byte_seq_le (array_to_seq (lift_to_both0 constant_d_v)) in
      letb x_s_2847 : uint8 :=
        ((array_index (q_2846) (lift_to_both0 (usize 31))) .& (secret (
              lift_to_both0 (@repr U8 128)))) shift_right (lift_to_both0 (
            usize 7)) in
      letbm y_s_2841 : compressed_ed_point_t loc( y_s_2841_loc ) :=
        lift_to_both0 q_2846 in
      letb y_s_2841 : compressed_ed_point_t :=
        array_upd y_s_2841 (lift_to_both0 (usize 31)) (is_pure ((array_index (
                y_s_2841) (lift_to_both0 (usize 31))) .& (secret (
                lift_to_both0 (@repr U8 127))))) in
      letbnd(ChoiceEqualityMonad.option_bind_both) 'tt :=
        if negb (check_canonical_point (
            lift_to_both0 y_s_2841)) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset ([y_s_2841_loc])) (L2 := CEfset (
            [result_2830_loc ; y_s_2841_loc ; x_2842_loc])) (
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
      letb y_2848 : ed25519_field_element_t :=
        nat_mod_from_byte_seq_le (array_to_seq (lift_to_both0 y_s_2841)) in
      letb z_2849 : ed25519_field_element_t := nat_mod_one  in
      letb yy_2850 : ed25519_field_element_t :=
        (lift_to_both0 y_2848) *% (lift_to_both0 y_2848) in
      letb u_2851 : ed25519_field_element_t :=
        (lift_to_both0 yy_2850) -% (lift_to_both0 z_2849) in
      letb v_2852 : ed25519_field_element_t :=
        ((lift_to_both0 d_2845) *% (lift_to_both0 yy_2850)) +% (
          lift_to_both0 z_2849) in
      letb xx_2853 : ed25519_field_element_t :=
        (lift_to_both0 u_2851) *% (nat_mod_inv (lift_to_both0 v_2852)) in
      letbndm(_) x_2842 : ed25519_field_element_t :=
        sqrt (lift_to_both0 xx_2853) in
      letb x_r_2854 : uint8 := is_negative (lift_to_both0 x_2842) in
      letbnd(ChoiceEqualityMonad.option_bind_both) 'tt :=
        if ((lift_to_both0 x_2842) =.? (nat_mod_zero )) && ((uint8_declassify (
              lift_to_both0 x_s_2847)) =.? (lift_to_both0 (
              @repr U8 1))) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset (
            [result_2830_loc ; y_s_2841_loc ; x_2842_loc])) (L2 := CEfset (
            [result_2830_loc ; y_s_2841_loc ; x_2842_loc])) (
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
      letb '(x_2842) :=
        if (uint8_declassify (lift_to_both0 x_r_2854)) !=.? (uint8_declassify (
            lift_to_both0 x_s_2847)) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset (
            [result_2830_loc ; y_s_2841_loc ; x_2842_loc])) (L2 := CEfset (
            [result_2830_loc ; y_s_2841_loc ; x_2842_loc])) (
          I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
          letbm x_2842 loc( x_2842_loc ) :=
            (nat_mod_zero ) -% (lift_to_both0 x_2842) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 x_2842)
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          lift_to_both0 x_2842)
         in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (some (prod_b(
            lift_to_both0 x_2842,
            lift_to_both0 y_2848,
            lift_to_both0 z_2849,
            (lift_to_both0 x_2842) *% (lift_to_both0 y_2848)
          )))
      ) : both (CEfset (
        [result_2830_loc ; y_s_2841_loc ; x_2842_loc])) [interface] ((option (
          ed_point_t)))).
Fail Next Obligation.

Definition y_s_2856_loc : ChoiceEqualityLocation :=
  (compressed_ed_point_t ; 2858%nat).
Definition x_2857_loc : ChoiceEqualityLocation :=
  (ed25519_field_element_t ; 2859%nat).
Notation "'decompress_non_canonical_inp'" :=(
  compressed_ed_point_t : choice_type) (in custom pack_type at level 2).
Notation "'decompress_non_canonical_inp'" :=(
  compressed_ed_point_t : ChoiceEquality) (at level 2).
Notation "'decompress_non_canonical_out'" :=((option (
      ed_point_t)) : choice_type) (in custom pack_type at level 2).
Notation "'decompress_non_canonical_out'" :=((option (
      ed_point_t)) : ChoiceEquality) (at level 2).
Definition DECOMPRESS_NON_CANONICAL : nat :=
  2870.
Program Definition decompress_non_canonical (p_2861 : compressed_ed_point_t)
  : both (CEfset ([result_2830_loc ; y_s_2856_loc ; x_2857_loc])) [interface] ((
      option (ed_point_t))) :=
  ((letb d_2860 : ed25519_field_element_t :=
        nat_mod_from_byte_seq_le (array_to_seq (lift_to_both0 constant_d_v)) in
      letb x_s_2862 : uint8 :=
        ((array_index (p_2861) (lift_to_both0 (usize 31))) .& (secret (
              lift_to_both0 (@repr U8 128)))) shift_right (lift_to_both0 (
            usize 7)) in
      letbm y_s_2856 : compressed_ed_point_t loc( y_s_2856_loc ) :=
        lift_to_both0 p_2861 in
      letb y_s_2856 : compressed_ed_point_t :=
        array_upd y_s_2856 (lift_to_both0 (usize 31)) (is_pure ((array_index (
                y_s_2856) (lift_to_both0 (usize 31))) .& (secret (
                lift_to_both0 (@repr U8 127))))) in
      letb y_2863 : ed25519_field_element_t :=
        nat_mod_from_byte_seq_le (array_to_seq (lift_to_both0 y_s_2856)) in
      letb z_2864 : ed25519_field_element_t := nat_mod_one  in
      letb yy_2865 : ed25519_field_element_t :=
        (lift_to_both0 y_2863) *% (lift_to_both0 y_2863) in
      letb u_2866 : ed25519_field_element_t :=
        (lift_to_both0 yy_2865) -% (lift_to_both0 z_2864) in
      letb v_2867 : ed25519_field_element_t :=
        ((lift_to_both0 d_2860) *% (lift_to_both0 yy_2865)) +% (
          lift_to_both0 z_2864) in
      letb xx_2868 : ed25519_field_element_t :=
        (lift_to_both0 u_2866) *% (nat_mod_inv (lift_to_both0 v_2867)) in
      letbndm(_) x_2857 : ed25519_field_element_t :=
        sqrt (lift_to_both0 xx_2868) in
      letb x_r_2869 : uint8 := is_negative (lift_to_both0 x_2857) in
      letb '(x_2857) :=
        if (uint8_declassify (lift_to_both0 x_r_2869)) !=.? (uint8_declassify (
            lift_to_both0 x_s_2862)) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset (
            [result_2830_loc ; y_s_2856_loc ; x_2857_loc])) (L2 := CEfset (
            [result_2830_loc ; y_s_2856_loc ; x_2857_loc])) (
          I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
          letbm x_2857 loc( x_2857_loc ) :=
            (nat_mod_zero ) -% (lift_to_both0 x_2857) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 x_2857)
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          lift_to_both0 x_2857)
         in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (some (prod_b(
            lift_to_both0 x_2857,
            lift_to_both0 y_2863,
            lift_to_both0 z_2864,
            (lift_to_both0 x_2857) *% (lift_to_both0 y_2863)
          )))
      ) : both (CEfset (
        [result_2830_loc ; y_s_2856_loc ; x_2857_loc])) [interface] ((option (
          ed_point_t)))).
Fail Next Obligation.

Definition s_2871_loc : ChoiceEqualityLocation :=
  (byte_seq ; 2872%nat).
Notation "'encode_inp'" :=(
  ed_point_t : choice_type) (in custom pack_type at level 2).
Notation "'encode_inp'" :=(ed_point_t : ChoiceEquality) (at level 2).
Notation "'encode_out'" :=(
  byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'encode_out'" :=(byte_seq : ChoiceEquality) (at level 2).
Definition ENCODE : nat :=
  2880.
Program Definition encode (p_2873 : ed_point_t)
  : both (CEfset ([s_2871_loc])) [interface] (byte_seq) :=
  ((letb '(x_2874, y_2875, z_2876, _) : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        lift_to_both0 p_2873 in
      letb z_inv_2877 : ed25519_field_element_t :=
        nat_mod_inv (lift_to_both0 z_2876) in
      letb x_2878 : ed25519_field_element_t :=
        (lift_to_both0 x_2874) *% (lift_to_both0 z_inv_2877) in
      letb y_2879 : ed25519_field_element_t :=
        (lift_to_both0 y_2875) *% (lift_to_both0 z_inv_2877) in
      letbm s_2871 : byte_seq loc( s_2871_loc ) :=
        nat_mod_to_byte_seq_le (lift_to_both0 y_2879) in
      letb s_2871 : seq uint8 :=
        seq_upd s_2871 (lift_to_both0 (usize 31)) (is_pure ((seq_index (
                s_2871) (lift_to_both0 (usize 31))) .^ ((is_negative (
                  lift_to_both0 x_2878)) shift_left (lift_to_both0 (
                  usize 7))))) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 s_2871)
      ) : both (CEfset ([s_2871_loc])) [interface] (byte_seq)).
Fail Next Obligation.


Notation "'decode_inp'" :=(
  byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'decode_inp'" :=(byte_seq : ChoiceEquality) (at level 2).
Notation "'decode_out'" :=((option (
      ed_point_t)) : choice_type) (in custom pack_type at level 2).
Notation "'decode_out'" :=((option (ed_point_t)) : ChoiceEquality) (at level 2).
Definition DECODE : nat :=
  2883.
Program Definition decode (q_s_2881 : byte_seq)
  : both (CEfset ([result_2830_loc ; y_s_2841_loc ; x_2842_loc])) [interface] ((
      option (ed_point_t))) :=
  ((letb q_2882 : compressed_ed_point_t :=
        array_from_slice (default : uint8) (32) (lift_to_both0 q_s_2881) (
          lift_to_both0 (usize 0)) (lift_to_both0 (usize 32)) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (decompress (
          lift_to_both0 q_2882))
      ) : both (CEfset (
        [result_2830_loc ; y_s_2841_loc ; x_2842_loc])) [interface] ((option (
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
  2908.
Program Definition point_add (p_2886 : ed_point_t) (q_2891 : ed_point_t)
  : both (fset.fset0) [interface] (ed_point_t) :=
  ((letb d_c_2884 : ed25519_field_element_t :=
        nat_mod_from_byte_seq_le (array_to_seq (lift_to_both0 constant_d_v)) in
      letb two_2885 : ed25519_field_element_t := nat_mod_two  in
      letb '(x1_2887, y1_2888, z1_2889, t1_2890) : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        lift_to_both0 p_2886 in
      letb '(x2_2892, y2_2893, z2_2894, t2_2895) : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        lift_to_both0 q_2891 in
      letb a_2896 : ed25519_field_element_t :=
        ((lift_to_both0 y1_2888) -% (lift_to_both0 x1_2887)) *% ((
            lift_to_both0 y2_2893) -% (lift_to_both0 x2_2892)) in
      letb b_2897 : ed25519_field_element_t :=
        ((lift_to_both0 y1_2888) +% (lift_to_both0 x1_2887)) *% ((
            lift_to_both0 y2_2893) +% (lift_to_both0 x2_2892)) in
      letb c_2898 : ed25519_field_element_t :=
        (((lift_to_both0 t1_2890) *% (lift_to_both0 two_2885)) *% (
            lift_to_both0 d_c_2884)) *% (lift_to_both0 t2_2895) in
      letb d_2899 : ed25519_field_element_t :=
        ((lift_to_both0 z1_2889) *% (lift_to_both0 two_2885)) *% (
          lift_to_both0 z2_2894) in
      letb e_2900 : ed25519_field_element_t :=
        (lift_to_both0 b_2897) -% (lift_to_both0 a_2896) in
      letb f_2901 : ed25519_field_element_t :=
        (lift_to_both0 d_2899) -% (lift_to_both0 c_2898) in
      letb g_2902 : ed25519_field_element_t :=
        (lift_to_both0 d_2899) +% (lift_to_both0 c_2898) in
      letb h_2903 : ed25519_field_element_t :=
        (lift_to_both0 b_2897) +% (lift_to_both0 a_2896) in
      letb x3_2904 : ed25519_field_element_t :=
        (lift_to_both0 e_2900) *% (lift_to_both0 f_2901) in
      letb y3_2905 : ed25519_field_element_t :=
        (lift_to_both0 g_2902) *% (lift_to_both0 h_2903) in
      letb t3_2906 : ed25519_field_element_t :=
        (lift_to_both0 e_2900) *% (lift_to_both0 h_2903) in
      letb z3_2907 : ed25519_field_element_t :=
        (lift_to_both0 f_2901) *% (lift_to_both0 g_2902) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 x3_2904,
          lift_to_both0 y3_2905,
          lift_to_both0 z3_2907,
          lift_to_both0 t3_2906
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
  2909.
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

Definition p_2910_loc : ChoiceEqualityLocation :=
  ((
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t
    ) ; 2912%nat).
Definition q_2911_loc : ChoiceEqualityLocation :=
  ((
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t
    ) ; 2913%nat).
Notation "'point_mul_inp'" :=(
  scalar_t '× ed_point_t : choice_type) (in custom pack_type at level 2).
Notation "'point_mul_inp'" :=(
  scalar_t '× ed_point_t : ChoiceEquality) (at level 2).
Notation "'point_mul_out'" :=(
  ed_point_t : choice_type) (in custom pack_type at level 2).
Notation "'point_mul_out'" :=(ed_point_t : ChoiceEquality) (at level 2).
Definition POINT_MUL : nat :=
  2917.
Program Definition point_mul (s_2916 : scalar_t) (p_2914 : ed_point_t)
  : both (CEfset ([p_2910_loc ; q_2911_loc])) [interface] (ed_point_t) :=
  ((letbm p_2910 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) loc( p_2910_loc ) :=
        lift_to_both0 p_2914 in
      letbm q_2911 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) loc( q_2911_loc ) :=
        point_identity  in
      letb '(p_2910, q_2911) :=
        foldi_both' (lift_to_both0 (usize 0)) (lift_to_both0 (
              usize 256)) prod_ce(p_2910, q_2911) (L := (CEfset (
                [p_2910_loc ; q_2911_loc]))) (I := [interface]) (fun i_2915 '(
              p_2910,
              q_2911
            ) =>
            letb '(q_2911) :=
              if nat_mod_bit (lift_to_both0 s_2916) (
                lift_to_both0 i_2915) :bool_ChoiceEquality
              then lift_scope (L1 := CEfset ([p_2910_loc ; q_2911_loc])) (
                L2 := CEfset ([p_2910_loc ; q_2911_loc])) (I1 := [interface]) (
                I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
                letbm q_2911 loc( q_2911_loc ) :=
                  point_add (lift_to_both0 q_2911) (lift_to_both0 p_2910) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                  lift_to_both0 q_2911)
                )
              else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                lift_to_both0 q_2911)
               in
            letbm p_2910 loc( p_2910_loc ) :=
              point_add (lift_to_both0 p_2910) (lift_to_both0 p_2910) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                lift_to_both0 p_2910,
                lift_to_both0 q_2911
              ))
            ) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 q_2911)
      ) : both (CEfset ([p_2910_loc ; q_2911_loc])) [interface] (ed_point_t)).
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
  2922.
Program Definition point_mul_by_cofactor (p_2918 : ed_point_t)
  : both (fset.fset0) [interface] (ed_point_t) :=
  ((letb p2_2919 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_add (lift_to_both0 p_2918) (lift_to_both0 p_2918) in
      letb p4_2920 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_add (lift_to_both0 p2_2919) (lift_to_both0 p2_2919) in
      letb p8_2921 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_add (lift_to_both0 p4_2920) (lift_to_both0 p4_2920) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 p8_2921)
      ) : both (fset.fset0) [interface] (ed_point_t)).
Fail Next Obligation.


Notation "'point_neg_inp'" :=(
  ed_point_t : choice_type) (in custom pack_type at level 2).
Notation "'point_neg_inp'" :=(ed_point_t : ChoiceEquality) (at level 2).
Notation "'point_neg_out'" :=(
  ed_point_t : choice_type) (in custom pack_type at level 2).
Notation "'point_neg_out'" :=(ed_point_t : ChoiceEquality) (at level 2).
Definition POINT_NEG : nat :=
  2928.
Program Definition point_neg (p_2923 : ed_point_t)
  : both (fset.fset0) [interface] (ed_point_t) :=
  ((letb '(x_2924, y_2925, z_2926, t_2927) : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        lift_to_both0 p_2923 in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          (nat_mod_zero ) -% (lift_to_both0 x_2924),
          lift_to_both0 y_2925,
          lift_to_both0 z_2926,
          (nat_mod_zero ) -% (lift_to_both0 t_2927)
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
  2937.
Program Definition point_eq (p_2929 : ed_point_t) (q_2933 : ed_point_t)
  : both (fset.fset0) [interface] (bool_ChoiceEquality) :=
  ((letb '(x1_2930, y1_2931, z1_2932, _) : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        lift_to_both0 p_2929 in
      letb '(x2_2934, y2_2935, z2_2936, _) : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        lift_to_both0 q_2933 in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) ((((
              lift_to_both0 x1_2930) *% (lift_to_both0 z2_2936)) =.? ((
              lift_to_both0 x2_2934) *% (lift_to_both0 z1_2932))) && (((
              lift_to_both0 y1_2931) *% (lift_to_both0 z2_2936)) =.? ((
              lift_to_both0 y2_2935) *% (lift_to_both0 z1_2932))))
      ) : both (fset.fset0) [interface] (bool_ChoiceEquality)).
Fail Next Obligation.


Notation "'point_normalize_inp'" :=(
  ed_point_t : choice_type) (in custom pack_type at level 2).
Notation "'point_normalize_inp'" :=(ed_point_t : ChoiceEquality) (at level 2).
Notation "'point_normalize_out'" :=(
  ed_point_t : choice_type) (in custom pack_type at level 2).
Notation "'point_normalize_out'" :=(ed_point_t : ChoiceEquality) (at level 2).
Definition POINT_NORMALIZE : nat :=
  2946.
Program Definition point_normalize (q_2938 : ed_point_t)
  : both (fset.fset0) [interface] (ed_point_t) :=
  ((letb '(qx_2939, qy_2940, qz_2941, _) : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        lift_to_both0 q_2938 in
      letb px_2942 : ed25519_field_element_t :=
        (lift_to_both0 qx_2939) *% (nat_mod_inv (lift_to_both0 qz_2941)) in
      letb py_2943 : ed25519_field_element_t :=
        (lift_to_both0 qy_2940) *% (nat_mod_inv (lift_to_both0 qz_2941)) in
      letb pz_2944 : ed25519_field_element_t := nat_mod_one  in
      letb pt_2945 : ed25519_field_element_t :=
        (lift_to_both0 px_2942) *% (lift_to_both0 py_2943) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 px_2942,
          lift_to_both0 py_2943,
          lift_to_both0 pz_2944,
          lift_to_both0 pt_2945
        ))
      ) : both (fset.fset0) [interface] (ed_point_t)).
Fail Next Obligation.

Definition s_2947_loc : ChoiceEqualityLocation :=
  (serialized_scalar_t ; 2948%nat).
Notation "'secret_expand_inp'" :=(
  secret_key_t : choice_type) (in custom pack_type at level 2).
Notation "'secret_expand_inp'" :=(secret_key_t : ChoiceEquality) (at level 2).
Notation "'secret_expand_out'" :=((serialized_scalar_t '× serialized_scalar_t
  ) : choice_type) (in custom pack_type at level 2).
Notation "'secret_expand_out'" :=((serialized_scalar_t '× serialized_scalar_t
  ) : ChoiceEquality) (at level 2).
Definition SECRET_EXPAND : nat :=
  2952.
Program Definition secret_expand (sk_2949 : secret_key_t)
  : both (CEfset ([s_2947_loc])) [interface] ((
      serialized_scalar_t '×
      serialized_scalar_t
    )) :=
  ((letb h_2950 : sha512_digest_t :=
        sha512 (seq_from_slice (lift_to_both0 sk_2949) (lift_to_both0 (
              usize 0)) (lift_to_both0 (usize 32))) in
      letb h_d_2951 : serialized_scalar_t :=
        array_from_slice (default : uint8) (32) (
          array_to_seq (lift_to_both0 h_2950)) (lift_to_both0 (usize 32)) (
          lift_to_both0 (usize 32)) in
      letbm s_2947 : serialized_scalar_t loc( s_2947_loc ) :=
        array_from_slice (default : uint8) (32) (
          array_to_seq (lift_to_both0 h_2950)) (lift_to_both0 (usize 0)) (
          lift_to_both0 (usize 32)) in
      letb s_2947 : serialized_scalar_t :=
        array_upd s_2947 (lift_to_both0 (usize 0)) (is_pure ((array_index (
                s_2947) (lift_to_both0 (usize 0))) .& (secret (lift_to_both0 (
                  @repr U8 248))))) in
      letb s_2947 : serialized_scalar_t :=
        array_upd s_2947 (lift_to_both0 (usize 31)) (is_pure ((array_index (
                s_2947) (lift_to_both0 (usize 31))) .& (secret (lift_to_both0 (
                  @repr U8 127))))) in
      letb s_2947 : serialized_scalar_t :=
        array_upd s_2947 (lift_to_both0 (usize 31)) (is_pure ((array_index (
                s_2947) (lift_to_both0 (usize 31))) .| (secret (lift_to_both0 (
                  @repr U8 64))))) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 s_2947,
          lift_to_both0 h_d_2951
        ))
      ) : both (CEfset ([s_2947_loc])) [interface] ((
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
  2958.
Program Definition secret_to_public (sk_2953 : secret_key_t)
  : both (CEfset (
      [s_2820_loc ; result_2830_loc ; y_s_2841_loc ; x_2842_loc ; p_2910_loc ; q_2911_loc ; s_2947_loc])) [interface] (
    public_key_t) :=
  ((letb '(s_2954, _) : (serialized_scalar_t '× serialized_scalar_t) :=
        secret_expand (lift_to_both0 sk_2953) in
      letb base_2955 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        option_unwrap (decompress (lift_to_both0 base_v)) in
      letb ss_2956 : scalar_t :=
        nat_mod_from_byte_seq_le (array_to_seq (lift_to_both0 s_2954)) in
      letb a_2957 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_mul (lift_to_both0 ss_2956) (lift_to_both0 base_2955) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (compress (
          lift_to_both0 a_2957))
      ) : both (CEfset (
        [s_2820_loc ; result_2830_loc ; y_s_2841_loc ; x_2842_loc ; p_2910_loc ; q_2911_loc ; s_2947_loc])) [interface] (
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
  2960.
Program Definition check_canonical_scalar (s_2959 : serialized_scalar_t)
  : both (fset.fset0) [interface] (bool_ChoiceEquality) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        if is_pure (I := [interface]) ((uint8_declassify ((array_index (
                  s_2959) (lift_to_both0 (usize 31))) .& (secret (
                  lift_to_both0 (@repr U8 224))))) !=.? (lift_to_both0 (
              @repr U8 0)))
        then lift_to_both0 ((false : bool_ChoiceEquality))
        else (nat_mod_from_byte_seq_le (
            array_to_seq (lift_to_both0 s_2959))) <.? (
          nat_mod_from_byte_seq_le (array_to_seq (lift_to_both0 constant_l_v))))
      ) : both (fset.fset0) [interface] (bool_ChoiceEquality)).
Fail Next Obligation.

