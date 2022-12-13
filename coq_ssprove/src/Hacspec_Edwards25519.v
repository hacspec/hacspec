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
  2689.
Program Definition is_negative (x_2688 : ed25519_field_element_t)
  : both (fset.fset0) [interface] (uint8) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        if is_pure (I := [interface]) (nat_mod_bit (lift_to_both0 x_2688) (
            lift_to_both0 (usize 0)))
        then secret (lift_to_both0 (@repr U8 1))
        else secret (lift_to_both0 (@repr U8 0)))
      ) : both (fset.fset0) [interface] (uint8)).
Fail Next Obligation.

Definition s_2690_loc : ChoiceEqualityLocation :=
  (byte_seq ; 2691%nat).
Notation "'compress_inp'" :=(
  ed_point_t : choice_type) (in custom pack_type at level 2).
Notation "'compress_inp'" :=(ed_point_t : ChoiceEquality) (at level 2).
Notation "'compress_out'" :=(
  compressed_ed_point_t : choice_type) (in custom pack_type at level 2).
Notation "'compress_out'" :=(
  compressed_ed_point_t : ChoiceEquality) (at level 2).
Definition COMPRESS : nat :=
  2699.
Program Definition compress (p_2692 : ed_point_t)
  : both (CEfset ([s_2690_loc])) [interface] (compressed_ed_point_t) :=
  ((letb '(x_2693, y_2694, z_2695, _) : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        lift_to_both0 p_2692 in
      letb z_inv_2696 : ed25519_field_element_t :=
        nat_mod_inv (lift_to_both0 z_2695) in
      letb x_2697 : ed25519_field_element_t :=
        (lift_to_both0 x_2693) *% (lift_to_both0 z_inv_2696) in
      letb y_2698 : ed25519_field_element_t :=
        (lift_to_both0 y_2694) *% (lift_to_both0 z_inv_2696) in
      letbm s_2690 : byte_seq loc( s_2690_loc ) :=
        nat_mod_to_byte_seq_le (lift_to_both0 y_2698) in
      letb s_2690 : seq uint8 :=
        seq_upd s_2690 (lift_to_both0 (usize 31)) (is_pure ((seq_index (
                s_2690) (lift_to_both0 (usize 31))) .^ ((is_negative (
                  lift_to_both0 x_2697)) shift_left (lift_to_both0 (
                  usize 7))))) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (array_from_slice (
          default : uint8) (32) (lift_to_both0 s_2690) (lift_to_both0 (
            usize 0)) (lift_to_both0 (usize 32)))
      ) : both (CEfset ([s_2690_loc])) [interface] (compressed_ed_point_t)).
Fail Next Obligation.

Definition result_2700_loc : ChoiceEqualityLocation :=
  ((option (ed25519_field_element_t)) ; 2701%nat).
Notation "'sqrt_inp'" :=(
  ed25519_field_element_t : choice_type) (in custom pack_type at level 2).
Notation "'sqrt_inp'" :=(ed25519_field_element_t : ChoiceEquality) (at level 2).
Notation "'sqrt_out'" :=((option (
      ed25519_field_element_t)) : choice_type) (in custom pack_type at level 2).
Notation "'sqrt_out'" :=((option (
      ed25519_field_element_t)) : ChoiceEquality) (at level 2).
Definition SQRT : nat :=
  2707.
Program Definition sqrt (a_2704 : ed25519_field_element_t)
  : both (CEfset ([result_2700_loc])) [interface] ((option (
        ed25519_field_element_t))) :=
  ((letb p3_8_2702 : ed25519_field_element_t :=
        nat_mod_from_byte_seq_le (
          array_to_seq (lift_to_both0 constant_p3_8_v)) in
      letb p1_4_2703 : ed25519_field_element_t :=
        nat_mod_from_byte_seq_le (
          array_to_seq (lift_to_both0 constant_p1_4_v)) in
      letb x_c_2705 : ed25519_field_element_t :=
        nat_mod_pow_self (lift_to_both0 a_2704) (lift_to_both0 p3_8_2702) in
      letbm result_2700 : (option (
            ed25519_field_element_t)) loc( result_2700_loc ) :=
        @None ed25519_field_element_t in
      letb '(result_2700) :=
        if ((lift_to_both0 x_c_2705) *% (lift_to_both0 x_c_2705)) =.? (
          lift_to_both0 a_2704) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset ([result_2700_loc])) (L2 := CEfset (
            [result_2700_loc])) (I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
          letbm result_2700 loc( result_2700_loc ) :=
            some (lift_to_both0 x_c_2705) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 result_2700)
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          lift_to_both0 result_2700)
         in
      letb '(result_2700) :=
        if ((lift_to_both0 x_c_2705) *% (lift_to_both0 x_c_2705)) =.? ((
            nat_mod_zero ) -% (lift_to_both0 a_2704)) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset ([result_2700_loc])) (L2 := CEfset (
            [result_2700_loc])) (I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
          letb x_2706 : ed25519_field_element_t :=
            (nat_mod_pow_self (nat_mod_two ) (lift_to_both0 p1_4_2703)) *% (
              lift_to_both0 x_c_2705) in
          letbm result_2700 loc( result_2700_loc ) :=
            some (lift_to_both0 x_2706) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 result_2700)
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          lift_to_both0 result_2700)
         in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        lift_to_both0 result_2700)
      ) : both (CEfset ([result_2700_loc])) [interface] ((option (
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
  2710.
Program Definition check_canonical_point (x_2708 : compressed_ed_point_t)
  : both (fset.fset0) [interface] (bool_ChoiceEquality) :=
  ((letb x_2708 : compressed_ed_point_t :=
        array_upd x_2708 (lift_to_both0 (usize 31)) (is_pure ((array_index (
                x_2708) (lift_to_both0 (usize 31))) .& (secret (lift_to_both0 (
                  @repr U8 127))))) in
      letb x_2709 : big_integer_t :=
        nat_mod_from_byte_seq_le (array_to_seq (lift_to_both0 x_2708)) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) ((
          lift_to_both0 x_2709) <.? (nat_mod_from_byte_seq_le (
            array_to_seq (lift_to_both0 constant_p_v))))
      ) : both (fset.fset0) [interface] (bool_ChoiceEquality)).
Fail Next Obligation.

Definition x_2712_loc : ChoiceEqualityLocation :=
  (ed25519_field_element_t ; 2713%nat).
Definition y_s_2711_loc : ChoiceEqualityLocation :=
  (compressed_ed_point_t ; 2714%nat).
Notation "'decompress_inp'" :=(
  compressed_ed_point_t : choice_type) (in custom pack_type at level 2).
Notation "'decompress_inp'" :=(
  compressed_ed_point_t : ChoiceEquality) (at level 2).
Notation "'decompress_out'" :=((option (
      ed_point_t)) : choice_type) (in custom pack_type at level 2).
Notation "'decompress_out'" :=((option (
      ed_point_t)) : ChoiceEquality) (at level 2).
Definition DECOMPRESS : nat :=
  2725.
Program Definition decompress (q_2716 : compressed_ed_point_t)
  : both (CEfset ([result_2700_loc ; y_s_2711_loc ; x_2712_loc])) [interface] ((
      option (ed_point_t))) :=
  ((letb d_2715 : ed25519_field_element_t :=
        nat_mod_from_byte_seq_le (array_to_seq (lift_to_both0 constant_d_v)) in
      letb x_s_2717 : uint8 :=
        ((array_index (q_2716) (lift_to_both0 (usize 31))) .& (secret (
              lift_to_both0 (@repr U8 128)))) shift_right (lift_to_both0 (
            usize 7)) in
      letbm y_s_2711 : compressed_ed_point_t loc( y_s_2711_loc ) :=
        lift_to_both0 q_2716 in
      letb y_s_2711 : compressed_ed_point_t :=
        array_upd y_s_2711 (lift_to_both0 (usize 31)) (is_pure ((array_index (
                y_s_2711) (lift_to_both0 (usize 31))) .& (secret (
                lift_to_both0 (@repr U8 127))))) in
      letbnd(ChoiceEqualityMonad.option_bind_both) 'tt :=
        if negb (check_canonical_point (
            lift_to_both0 y_s_2711)) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset ([y_s_2711_loc])) (L2 := CEfset (
            [result_2700_loc ; y_s_2711_loc ; x_2712_loc])) (
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
      letb y_2718 : ed25519_field_element_t :=
        nat_mod_from_byte_seq_le (array_to_seq (lift_to_both0 y_s_2711)) in
      letb z_2719 : ed25519_field_element_t := nat_mod_one  in
      letb yy_2720 : ed25519_field_element_t :=
        (lift_to_both0 y_2718) *% (lift_to_both0 y_2718) in
      letb u_2721 : ed25519_field_element_t :=
        (lift_to_both0 yy_2720) -% (lift_to_both0 z_2719) in
      letb v_2722 : ed25519_field_element_t :=
        ((lift_to_both0 d_2715) *% (lift_to_both0 yy_2720)) +% (
          lift_to_both0 z_2719) in
      letb xx_2723 : ed25519_field_element_t :=
        (lift_to_both0 u_2721) *% (nat_mod_inv (lift_to_both0 v_2722)) in
      letbndm(_) x_2712 : ed25519_field_element_t :=
        sqrt (lift_to_both0 xx_2723) in
      letb x_r_2724 : uint8 := is_negative (lift_to_both0 x_2712) in
      letbnd(ChoiceEqualityMonad.option_bind_both) 'tt :=
        if ((lift_to_both0 x_2712) =.? (nat_mod_zero )) && ((uint8_declassify (
              lift_to_both0 x_s_2717)) =.? (lift_to_both0 (
              @repr U8 1))) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset (
            [result_2700_loc ; y_s_2711_loc ; x_2712_loc])) (L2 := CEfset (
            [result_2700_loc ; y_s_2711_loc ; x_2712_loc])) (
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
      letb '(x_2712) :=
        if (uint8_declassify (lift_to_both0 x_r_2724)) !=.? (uint8_declassify (
            lift_to_both0 x_s_2717)) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset (
            [result_2700_loc ; y_s_2711_loc ; x_2712_loc])) (L2 := CEfset (
            [result_2700_loc ; y_s_2711_loc ; x_2712_loc])) (
          I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
          letbm x_2712 loc( x_2712_loc ) :=
            (nat_mod_zero ) -% (lift_to_both0 x_2712) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 x_2712)
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          lift_to_both0 x_2712)
         in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (some (prod_b(
            lift_to_both0 x_2712,
            lift_to_both0 y_2718,
            lift_to_both0 z_2719,
            (lift_to_both0 x_2712) *% (lift_to_both0 y_2718)
          )))
      ) : both (CEfset (
        [result_2700_loc ; y_s_2711_loc ; x_2712_loc])) [interface] ((option (
          ed_point_t)))).
Fail Next Obligation.

Definition y_s_2726_loc : ChoiceEqualityLocation :=
  (compressed_ed_point_t ; 2728%nat).
Definition x_2727_loc : ChoiceEqualityLocation :=
  (ed25519_field_element_t ; 2729%nat).
Notation "'decompress_non_canonical_inp'" :=(
  compressed_ed_point_t : choice_type) (in custom pack_type at level 2).
Notation "'decompress_non_canonical_inp'" :=(
  compressed_ed_point_t : ChoiceEquality) (at level 2).
Notation "'decompress_non_canonical_out'" :=((option (
      ed_point_t)) : choice_type) (in custom pack_type at level 2).
Notation "'decompress_non_canonical_out'" :=((option (
      ed_point_t)) : ChoiceEquality) (at level 2).
Definition DECOMPRESS_NON_CANONICAL : nat :=
  2740.
Program Definition decompress_non_canonical (p_2731 : compressed_ed_point_t)
  : both (CEfset ([result_2700_loc ; y_s_2726_loc ; x_2727_loc])) [interface] ((
      option (ed_point_t))) :=
  ((letb d_2730 : ed25519_field_element_t :=
        nat_mod_from_byte_seq_le (array_to_seq (lift_to_both0 constant_d_v)) in
      letb x_s_2732 : uint8 :=
        ((array_index (p_2731) (lift_to_both0 (usize 31))) .& (secret (
              lift_to_both0 (@repr U8 128)))) shift_right (lift_to_both0 (
            usize 7)) in
      letbm y_s_2726 : compressed_ed_point_t loc( y_s_2726_loc ) :=
        lift_to_both0 p_2731 in
      letb y_s_2726 : compressed_ed_point_t :=
        array_upd y_s_2726 (lift_to_both0 (usize 31)) (is_pure ((array_index (
                y_s_2726) (lift_to_both0 (usize 31))) .& (secret (
                lift_to_both0 (@repr U8 127))))) in
      letb y_2733 : ed25519_field_element_t :=
        nat_mod_from_byte_seq_le (array_to_seq (lift_to_both0 y_s_2726)) in
      letb z_2734 : ed25519_field_element_t := nat_mod_one  in
      letb yy_2735 : ed25519_field_element_t :=
        (lift_to_both0 y_2733) *% (lift_to_both0 y_2733) in
      letb u_2736 : ed25519_field_element_t :=
        (lift_to_both0 yy_2735) -% (lift_to_both0 z_2734) in
      letb v_2737 : ed25519_field_element_t :=
        ((lift_to_both0 d_2730) *% (lift_to_both0 yy_2735)) +% (
          lift_to_both0 z_2734) in
      letb xx_2738 : ed25519_field_element_t :=
        (lift_to_both0 u_2736) *% (nat_mod_inv (lift_to_both0 v_2737)) in
      letbndm(_) x_2727 : ed25519_field_element_t :=
        sqrt (lift_to_both0 xx_2738) in
      letb x_r_2739 : uint8 := is_negative (lift_to_both0 x_2727) in
      letb '(x_2727) :=
        if (uint8_declassify (lift_to_both0 x_r_2739)) !=.? (uint8_declassify (
            lift_to_both0 x_s_2732)) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset (
            [result_2700_loc ; y_s_2726_loc ; x_2727_loc])) (L2 := CEfset (
            [result_2700_loc ; y_s_2726_loc ; x_2727_loc])) (
          I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
          letbm x_2727 loc( x_2727_loc ) :=
            (nat_mod_zero ) -% (lift_to_both0 x_2727) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 x_2727)
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          lift_to_both0 x_2727)
         in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (some (prod_b(
            lift_to_both0 x_2727,
            lift_to_both0 y_2733,
            lift_to_both0 z_2734,
            (lift_to_both0 x_2727) *% (lift_to_both0 y_2733)
          )))
      ) : both (CEfset (
        [result_2700_loc ; y_s_2726_loc ; x_2727_loc])) [interface] ((option (
          ed_point_t)))).
Fail Next Obligation.

Definition s_2741_loc : ChoiceEqualityLocation :=
  (byte_seq ; 2742%nat).
Notation "'encode_inp'" :=(
  ed_point_t : choice_type) (in custom pack_type at level 2).
Notation "'encode_inp'" :=(ed_point_t : ChoiceEquality) (at level 2).
Notation "'encode_out'" :=(
  byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'encode_out'" :=(byte_seq : ChoiceEquality) (at level 2).
Definition ENCODE : nat :=
  2750.
Program Definition encode (p_2743 : ed_point_t)
  : both (CEfset ([s_2741_loc])) [interface] (byte_seq) :=
  ((letb '(x_2744, y_2745, z_2746, _) : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        lift_to_both0 p_2743 in
      letb z_inv_2747 : ed25519_field_element_t :=
        nat_mod_inv (lift_to_both0 z_2746) in
      letb x_2748 : ed25519_field_element_t :=
        (lift_to_both0 x_2744) *% (lift_to_both0 z_inv_2747) in
      letb y_2749 : ed25519_field_element_t :=
        (lift_to_both0 y_2745) *% (lift_to_both0 z_inv_2747) in
      letbm s_2741 : byte_seq loc( s_2741_loc ) :=
        nat_mod_to_byte_seq_le (lift_to_both0 y_2749) in
      letb s_2741 : seq uint8 :=
        seq_upd s_2741 (lift_to_both0 (usize 31)) (is_pure ((seq_index (
                s_2741) (lift_to_both0 (usize 31))) .^ ((is_negative (
                  lift_to_both0 x_2748)) shift_left (lift_to_both0 (
                  usize 7))))) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 s_2741)
      ) : both (CEfset ([s_2741_loc])) [interface] (byte_seq)).
Fail Next Obligation.


Notation "'decode_inp'" :=(
  byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'decode_inp'" :=(byte_seq : ChoiceEquality) (at level 2).
Notation "'decode_out'" :=((option (
      ed_point_t)) : choice_type) (in custom pack_type at level 2).
Notation "'decode_out'" :=((option (ed_point_t)) : ChoiceEquality) (at level 2).
Definition DECODE : nat :=
  2753.
Program Definition decode (q_s_2751 : byte_seq)
  : both (CEfset ([result_2700_loc ; y_s_2711_loc ; x_2712_loc])) [interface] ((
      option (ed_point_t))) :=
  ((letb q_2752 : compressed_ed_point_t :=
        array_from_slice (default : uint8) (32) (lift_to_both0 q_s_2751) (
          lift_to_both0 (usize 0)) (lift_to_both0 (usize 32)) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (decompress (
          lift_to_both0 q_2752))
      ) : both (CEfset (
        [result_2700_loc ; y_s_2711_loc ; x_2712_loc])) [interface] ((option (
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
  2778.
Program Definition point_add (p_2756 : ed_point_t) (q_2761 : ed_point_t)
  : both (fset.fset0) [interface] (ed_point_t) :=
  ((letb d_c_2754 : ed25519_field_element_t :=
        nat_mod_from_byte_seq_le (array_to_seq (lift_to_both0 constant_d_v)) in
      letb two_2755 : ed25519_field_element_t := nat_mod_two  in
      letb '(x1_2757, y1_2758, z1_2759, t1_2760) : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        lift_to_both0 p_2756 in
      letb '(x2_2762, y2_2763, z2_2764, t2_2765) : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        lift_to_both0 q_2761 in
      letb a_2766 : ed25519_field_element_t :=
        ((lift_to_both0 y1_2758) -% (lift_to_both0 x1_2757)) *% ((
            lift_to_both0 y2_2763) -% (lift_to_both0 x2_2762)) in
      letb b_2767 : ed25519_field_element_t :=
        ((lift_to_both0 y1_2758) +% (lift_to_both0 x1_2757)) *% ((
            lift_to_both0 y2_2763) +% (lift_to_both0 x2_2762)) in
      letb c_2768 : ed25519_field_element_t :=
        (((lift_to_both0 t1_2760) *% (lift_to_both0 two_2755)) *% (
            lift_to_both0 d_c_2754)) *% (lift_to_both0 t2_2765) in
      letb d_2769 : ed25519_field_element_t :=
        ((lift_to_both0 z1_2759) *% (lift_to_both0 two_2755)) *% (
          lift_to_both0 z2_2764) in
      letb e_2770 : ed25519_field_element_t :=
        (lift_to_both0 b_2767) -% (lift_to_both0 a_2766) in
      letb f_2771 : ed25519_field_element_t :=
        (lift_to_both0 d_2769) -% (lift_to_both0 c_2768) in
      letb g_2772 : ed25519_field_element_t :=
        (lift_to_both0 d_2769) +% (lift_to_both0 c_2768) in
      letb h_2773 : ed25519_field_element_t :=
        (lift_to_both0 b_2767) +% (lift_to_both0 a_2766) in
      letb x3_2774 : ed25519_field_element_t :=
        (lift_to_both0 e_2770) *% (lift_to_both0 f_2771) in
      letb y3_2775 : ed25519_field_element_t :=
        (lift_to_both0 g_2772) *% (lift_to_both0 h_2773) in
      letb t3_2776 : ed25519_field_element_t :=
        (lift_to_both0 e_2770) *% (lift_to_both0 h_2773) in
      letb z3_2777 : ed25519_field_element_t :=
        (lift_to_both0 f_2771) *% (lift_to_both0 g_2772) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 x3_2774,
          lift_to_both0 y3_2775,
          lift_to_both0 z3_2777,
          lift_to_both0 t3_2776
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
  2779.
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

Definition q_2781_loc : ChoiceEqualityLocation :=
  ((
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t
    ) ; 2782%nat).
Definition p_2780_loc : ChoiceEqualityLocation :=
  ((
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t
    ) ; 2783%nat).
Notation "'point_mul_inp'" :=(
  scalar_t '× ed_point_t : choice_type) (in custom pack_type at level 2).
Notation "'point_mul_inp'" :=(
  scalar_t '× ed_point_t : ChoiceEquality) (at level 2).
Notation "'point_mul_out'" :=(
  ed_point_t : choice_type) (in custom pack_type at level 2).
Notation "'point_mul_out'" :=(ed_point_t : ChoiceEquality) (at level 2).
Definition POINT_MUL : nat :=
  2787.
Program Definition point_mul (s_2786 : scalar_t) (p_2784 : ed_point_t)
  : both (CEfset ([p_2780_loc ; q_2781_loc])) [interface] (ed_point_t) :=
  ((letbm p_2780 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) loc( p_2780_loc ) :=
        lift_to_both0 p_2784 in
      letbm q_2781 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) loc( q_2781_loc ) :=
        point_identity  in
      letb '(p_2780, q_2781) :=
        foldi_both' (lift_to_both0 (usize 0)) (lift_to_both0 (
              usize 256)) prod_ce(p_2780, q_2781) (L := (CEfset (
                [p_2780_loc ; q_2781_loc]))) (I := [interface]) (fun i_2785 '(
              p_2780,
              q_2781
            ) =>
            letb '(q_2781) :=
              if nat_mod_bit (lift_to_both0 s_2786) (
                lift_to_both0 i_2785) :bool_ChoiceEquality
              then lift_scope (L1 := CEfset ([p_2780_loc ; q_2781_loc])) (
                L2 := CEfset ([p_2780_loc ; q_2781_loc])) (I1 := [interface]) (
                I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
                letbm q_2781 loc( q_2781_loc ) :=
                  point_add (lift_to_both0 q_2781) (lift_to_both0 p_2780) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                  lift_to_both0 q_2781)
                )
              else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                lift_to_both0 q_2781)
               in
            letbm p_2780 loc( p_2780_loc ) :=
              point_add (lift_to_both0 p_2780) (lift_to_both0 p_2780) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                lift_to_both0 p_2780,
                lift_to_both0 q_2781
              ))
            ) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 q_2781)
      ) : both (CEfset ([p_2780_loc ; q_2781_loc])) [interface] (ed_point_t)).
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
  2792.
Program Definition point_mul_by_cofactor (p_2788 : ed_point_t)
  : both (fset.fset0) [interface] (ed_point_t) :=
  ((letb p2_2789 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_add (lift_to_both0 p_2788) (lift_to_both0 p_2788) in
      letb p4_2790 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_add (lift_to_both0 p2_2789) (lift_to_both0 p2_2789) in
      letb p8_2791 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_add (lift_to_both0 p4_2790) (lift_to_both0 p4_2790) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 p8_2791)
      ) : both (fset.fset0) [interface] (ed_point_t)).
Fail Next Obligation.


Notation "'point_neg_inp'" :=(
  ed_point_t : choice_type) (in custom pack_type at level 2).
Notation "'point_neg_inp'" :=(ed_point_t : ChoiceEquality) (at level 2).
Notation "'point_neg_out'" :=(
  ed_point_t : choice_type) (in custom pack_type at level 2).
Notation "'point_neg_out'" :=(ed_point_t : ChoiceEquality) (at level 2).
Definition POINT_NEG : nat :=
  2798.
Program Definition point_neg (p_2793 : ed_point_t)
  : both (fset.fset0) [interface] (ed_point_t) :=
  ((letb '(x_2794, y_2795, z_2796, t_2797) : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        lift_to_both0 p_2793 in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          (nat_mod_zero ) -% (lift_to_both0 x_2794),
          lift_to_both0 y_2795,
          lift_to_both0 z_2796,
          (nat_mod_zero ) -% (lift_to_both0 t_2797)
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
  2807.
Program Definition point_eq (p_2799 : ed_point_t) (q_2803 : ed_point_t)
  : both (fset.fset0) [interface] (bool_ChoiceEquality) :=
  ((letb '(x1_2800, y1_2801, z1_2802, _) : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        lift_to_both0 p_2799 in
      letb '(x2_2804, y2_2805, z2_2806, _) : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        lift_to_both0 q_2803 in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) ((((
              lift_to_both0 x1_2800) *% (lift_to_both0 z2_2806)) =.? ((
              lift_to_both0 x2_2804) *% (lift_to_both0 z1_2802))) && (((
              lift_to_both0 y1_2801) *% (lift_to_both0 z2_2806)) =.? ((
              lift_to_both0 y2_2805) *% (lift_to_both0 z1_2802))))
      ) : both (fset.fset0) [interface] (bool_ChoiceEquality)).
Fail Next Obligation.


Notation "'point_normalize_inp'" :=(
  ed_point_t : choice_type) (in custom pack_type at level 2).
Notation "'point_normalize_inp'" :=(ed_point_t : ChoiceEquality) (at level 2).
Notation "'point_normalize_out'" :=(
  ed_point_t : choice_type) (in custom pack_type at level 2).
Notation "'point_normalize_out'" :=(ed_point_t : ChoiceEquality) (at level 2).
Definition POINT_NORMALIZE : nat :=
  2816.
Program Definition point_normalize (q_2808 : ed_point_t)
  : both (fset.fset0) [interface] (ed_point_t) :=
  ((letb '(qx_2809, qy_2810, qz_2811, _) : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        lift_to_both0 q_2808 in
      letb px_2812 : ed25519_field_element_t :=
        (lift_to_both0 qx_2809) *% (nat_mod_inv (lift_to_both0 qz_2811)) in
      letb py_2813 : ed25519_field_element_t :=
        (lift_to_both0 qy_2810) *% (nat_mod_inv (lift_to_both0 qz_2811)) in
      letb pz_2814 : ed25519_field_element_t := nat_mod_one  in
      letb pt_2815 : ed25519_field_element_t :=
        (lift_to_both0 px_2812) *% (lift_to_both0 py_2813) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 px_2812,
          lift_to_both0 py_2813,
          lift_to_both0 pz_2814,
          lift_to_both0 pt_2815
        ))
      ) : both (fset.fset0) [interface] (ed_point_t)).
Fail Next Obligation.

Definition s_2817_loc : ChoiceEqualityLocation :=
  (serialized_scalar_t ; 2818%nat).
Notation "'secret_expand_inp'" :=(
  secret_key_t : choice_type) (in custom pack_type at level 2).
Notation "'secret_expand_inp'" :=(secret_key_t : ChoiceEquality) (at level 2).
Notation "'secret_expand_out'" :=((serialized_scalar_t '× serialized_scalar_t
  ) : choice_type) (in custom pack_type at level 2).
Notation "'secret_expand_out'" :=((serialized_scalar_t '× serialized_scalar_t
  ) : ChoiceEquality) (at level 2).
Definition SECRET_EXPAND : nat :=
  2822.
Program Definition secret_expand (sk_2819 : secret_key_t)
  : both (CEfset ([s_2817_loc])) [interface] ((
      serialized_scalar_t '×
      serialized_scalar_t
    )) :=
  ((letb h_2820 : sha512_digest_t :=
        sha512 (seq_from_slice (lift_to_both0 sk_2819) (lift_to_both0 (
              usize 0)) (lift_to_both0 (usize 32))) in
      letb h_d_2821 : serialized_scalar_t :=
        array_from_slice (default : uint8) (32) (
          array_to_seq (lift_to_both0 h_2820)) (lift_to_both0 (usize 32)) (
          lift_to_both0 (usize 32)) in
      letbm s_2817 : serialized_scalar_t loc( s_2817_loc ) :=
        array_from_slice (default : uint8) (32) (
          array_to_seq (lift_to_both0 h_2820)) (lift_to_both0 (usize 0)) (
          lift_to_both0 (usize 32)) in
      letb s_2817 : serialized_scalar_t :=
        array_upd s_2817 (lift_to_both0 (usize 0)) (is_pure ((array_index (
                s_2817) (lift_to_both0 (usize 0))) .& (secret (lift_to_both0 (
                  @repr U8 248))))) in
      letb s_2817 : serialized_scalar_t :=
        array_upd s_2817 (lift_to_both0 (usize 31)) (is_pure ((array_index (
                s_2817) (lift_to_both0 (usize 31))) .& (secret (lift_to_both0 (
                  @repr U8 127))))) in
      letb s_2817 : serialized_scalar_t :=
        array_upd s_2817 (lift_to_both0 (usize 31)) (is_pure ((array_index (
                s_2817) (lift_to_both0 (usize 31))) .| (secret (lift_to_both0 (
                  @repr U8 64))))) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 s_2817,
          lift_to_both0 h_d_2821
        ))
      ) : both (CEfset ([s_2817_loc])) [interface] ((
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
  2828.
Program Definition secret_to_public (sk_2823 : secret_key_t)
  : both (CEfset (
      [s_2690_loc ; result_2700_loc ; y_s_2711_loc ; x_2712_loc ; p_2780_loc ; q_2781_loc ; s_2817_loc])) [interface] (
    public_key_t) :=
  ((letb '(s_2824, _) : (serialized_scalar_t '× serialized_scalar_t) :=
        secret_expand (lift_to_both0 sk_2823) in
      letb base_2825 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        option_unwrap (decompress (lift_to_both0 base_v)) in
      letb ss_2826 : scalar_t :=
        nat_mod_from_byte_seq_le (array_to_seq (lift_to_both0 s_2824)) in
      letb a_2827 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_mul (lift_to_both0 ss_2826) (lift_to_both0 base_2825) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (compress (
          lift_to_both0 a_2827))
      ) : both (CEfset (
        [s_2690_loc ; result_2700_loc ; y_s_2711_loc ; x_2712_loc ; p_2780_loc ; q_2781_loc ; s_2817_loc])) [interface] (
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
  2830.
Program Definition check_canonical_scalar (s_2829 : serialized_scalar_t)
  : both (fset.fset0) [interface] (bool_ChoiceEquality) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        if is_pure (I := [interface]) ((uint8_declassify ((array_index (
                  s_2829) (lift_to_both0 (usize 31))) .& (secret (
                  lift_to_both0 (@repr U8 224))))) !=.? (lift_to_both0 (
              @repr U8 0)))
        then lift_to_both0 ((false : bool_ChoiceEquality))
        else (nat_mod_from_byte_seq_le (
            array_to_seq (lift_to_both0 s_2829))) <.? (
          nat_mod_from_byte_seq_le (array_to_seq (lift_to_both0 constant_l_v))))
      ) : both (fset.fset0) [interface] (bool_ChoiceEquality)).
Fail Next Obligation.

