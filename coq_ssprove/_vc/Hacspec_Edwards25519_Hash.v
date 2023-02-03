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


Require Import Hacspec_Edwards25519.

Require Import Hacspec_Sha512.

Definition b_in_bytes_v : uint_size :=
  usize 64.

Definition s_in_bytes_v : uint_size :=
  usize 128.

Definition l_v : uint_size :=
  usize 48.

Definition j_v : int128 :=
  @repr U128 486662.

Definition z_v : int128 :=
  @repr U128 2.

Definition arr_ed25519_field_element_t := nseq (uint64) (usize 4).

Definition ed_field_hash_canvas_t := nseq (int8) (usize 64).
Definition ed_field_hash_t :=
  nat_mod 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed.

Definition error_t : ChoiceEquality :=
  unit_ChoiceEquality.
Definition ExpandMessageAbort : error_t :=
   tt.

Notation "'byte_seq_result_t'" := ((result error_t byte_seq)) : hacspec_scope.

Notation "'seq_ed_result_t'" := ((
  result error_t seq ed25519_field_element_t)) : hacspec_scope.

Notation "'ed_point_result_t'" := ((result error_t ed_point_t)) : hacspec_scope.

Definition p_1_2_v : arr_ed25519_field_element_t :=
  @array_from_list uint64 [
    (secret (@repr U64 4611686018427387903)) : uint64;
    (secret (@repr U64 18446744073709551615)) : uint64;
    (secret (@repr U64 18446744073709551615)) : uint64;
    (secret (@repr U64 18446744073709551606)) : uint64
  ].

Definition p_3_8_v : arr_ed25519_field_element_t :=
  @array_from_list uint64 [
    (secret (@repr U64 1152921504606846975)) : uint64;
    (secret (@repr U64 18446744073709551615)) : uint64;
    (secret (@repr U64 18446744073709551615)) : uint64;
    (secret (@repr U64 18446744073709551614)) : uint64
  ].

Definition p_5_8_v : arr_ed25519_field_element_t :=
  @array_from_list uint64 [
    (secret (@repr U64 1152921504606846975)) : uint64;
    (secret (@repr U64 18446744073709551615)) : uint64;
    (secret (@repr U64 18446744073709551615)) : uint64;
    (secret (@repr U64 18446744073709551613)) : uint64
  ].

Definition l_i_b_str_3028_loc : ChoiceEqualityLocation :=
  (seq uint8 ; 3031%nat).
Definition uniform_bytes_3030_loc : ChoiceEqualityLocation :=
  (seq uint8 ; 3032%nat).
Definition b_i_3029_loc : ChoiceEqualityLocation :=
  (seq uint8 ; 3033%nat).
Definition result_3027_loc : ChoiceEqualityLocation :=
  ((result (error_t) (byte_seq)) ; 3034%nat).
Notation "'expand_message_xmd_inp'" :=(
  byte_seq '× byte_seq '× uint_size : choice_type) (in custom pack_type at level 2).
Notation "'expand_message_xmd_inp'" :=(
  byte_seq '× byte_seq '× uint_size : ChoiceEquality) (at level 2).
Notation "'expand_message_xmd_out'" :=(
  byte_seq_result_t : choice_type) (in custom pack_type at level 2).
Notation "'expand_message_xmd_out'" :=(
  byte_seq_result_t : ChoiceEquality) (at level 2).
Definition EXPAND_MESSAGE_XMD : nat :=
  3045.
Program Definition expand_message_xmd (msg_3040 : byte_seq) (
    dst_3037 : byte_seq) (len_in_bytes_3035 : uint_size)
  : both (CEfset (
      [result_3027_loc ; l_i_b_str_3028_loc ; b_i_3029_loc ; uniform_bytes_3030_loc])) [interface] (
    byte_seq_result_t) :=
  ((letb ell_3036 : uint_size :=
        (((lift_to_both0 len_in_bytes_3035) .+ (
              lift_to_both0 b_in_bytes_v)) .- (lift_to_both0 (usize 1))) ./ (
          lift_to_both0 b_in_bytes_v) in
      letbm result_3027 : (result (error_t) (
            byte_seq)) loc( result_3027_loc ) :=
        @Err byte_seq error_t (ExpandMessageAbort) in
      letb '(result_3027) :=
        if negb ((((lift_to_both0 ell_3036) >.? (lift_to_both0 (
                  usize 255))) || ((lift_to_both0 len_in_bytes_3035) >.? (
                lift_to_both0 (usize 65535)))) || ((seq_len (
                lift_to_both0 dst_3037)) >.? (lift_to_both0 (
                usize 255)))) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset (
            [result_3027_loc ; l_i_b_str_3028_loc ; b_i_3029_loc ; uniform_bytes_3030_loc])) (
          L2 := CEfset (
            [result_3027_loc ; l_i_b_str_3028_loc ; b_i_3029_loc ; uniform_bytes_3030_loc])) (
          I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
          letb dst_prime_3038 : seq uint8 :=
            seq_push (lift_to_both0 dst_3037) (uint8_from_usize (seq_len (
                  lift_to_both0 dst_3037))) in
          letb z_pad_3039 : seq uint8 :=
            seq_new_ (default : uint8) (lift_to_both0 s_in_bytes_v) in
          letbm l_i_b_str_3028 : seq uint8 loc( l_i_b_str_3028_loc ) :=
            seq_new_ (default : uint8) (lift_to_both0 (usize 2)) in
          letb l_i_b_str_3028 : seq uint8 :=
            seq_upd l_i_b_str_3028 (lift_to_both0 (usize 0)) (is_pure (
                uint8_from_usize ((lift_to_both0 len_in_bytes_3035) ./ (
                    lift_to_both0 (usize 256))))) in
          letb l_i_b_str_3028 : seq uint8 :=
            seq_upd l_i_b_str_3028 (lift_to_both0 (usize 1)) (is_pure (
                uint8_from_usize (lift_to_both0 len_in_bytes_3035))) in
          letb msg_prime_3041 : seq uint8 :=
            seq_concat (seq_concat (seq_concat (seq_concat (
                    lift_to_both0 z_pad_3039) (lift_to_both0 msg_3040)) (
                  lift_to_both0 l_i_b_str_3028)) (seq_new_ (default : uint8) (
                  lift_to_both0 (usize 1)))) (lift_to_both0 dst_prime_3038) in
          letb b_0_3042 : seq uint8 :=
            seq_from_seq (array_to_seq (hash (lift_to_both0 msg_prime_3041))) in
          letbm b_i_3029 : seq uint8 loc( b_i_3029_loc ) :=
            seq_from_seq (array_to_seq (hash (seq_concat (seq_push (
                    lift_to_both0 b_0_3042) (secret (lift_to_both0 (
                        @repr U8 1)))) (lift_to_both0 dst_prime_3038)))) in
          letbm uniform_bytes_3030 : seq uint8 loc( uniform_bytes_3030_loc ) :=
            seq_from_seq (lift_to_both0 b_i_3029) in
          letb '(b_i_3029, uniform_bytes_3030) :=
            foldi_both' (lift_to_both0 (usize 2)) ((lift_to_both0 ell_3036) .+ (
                  lift_to_both0 (usize 1))) prod_ce(b_i_3029, uniform_bytes_3030
              ) (L := (CEfset (
                    [result_3027_loc ; l_i_b_str_3028_loc ; b_i_3029_loc ; uniform_bytes_3030_loc]))) (
                I := [interface]) (fun i_3043 '(b_i_3029, uniform_bytes_3030) =>
                letb t_3044 : seq uint8 :=
                  seq_from_seq (lift_to_both0 b_0_3042) in
                letbm b_i_3029 loc( b_i_3029_loc ) :=
                  seq_from_seq (array_to_seq (hash (seq_concat (seq_push ((
                            lift_to_both0 t_3044) seq_xor (
                            lift_to_both0 b_i_3029)) (uint8_from_usize (
                            lift_to_both0 i_3043))) (
                        lift_to_both0 dst_prime_3038)))) in
                letbm uniform_bytes_3030 loc( uniform_bytes_3030_loc ) :=
                  seq_concat (lift_to_both0 uniform_bytes_3030) (
                    lift_to_both0 b_i_3029) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                    lift_to_both0 b_i_3029,
                    lift_to_both0 uniform_bytes_3030
                  ))
                ) in
          letbm result_3027 loc( result_3027_loc ) :=
            @Ok byte_seq error_t (seq_truncate (
                lift_to_both0 uniform_bytes_3030) (
                lift_to_both0 len_in_bytes_3035)) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 result_3027)
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          lift_to_both0 result_3027)
         in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        lift_to_both0 result_3027)
      ) : both (CEfset (
        [result_3027_loc ; l_i_b_str_3028_loc ; b_i_3029_loc ; uniform_bytes_3030_loc])) [interface] (
      byte_seq_result_t)).
Fail Next Obligation.

Definition output_3046_loc : ChoiceEqualityLocation :=
  (seq ed25519_field_element_t ; 3047%nat).
Notation "'ed_hash_to_field_inp'" :=(
  byte_seq '× byte_seq '× uint_size : choice_type) (in custom pack_type at level 2).
Notation "'ed_hash_to_field_inp'" :=(
  byte_seq '× byte_seq '× uint_size : ChoiceEquality) (at level 2).
Notation "'ed_hash_to_field_out'" :=(
  seq_ed_result_t : choice_type) (in custom pack_type at level 2).
Notation "'ed_hash_to_field_out'" :=(
  seq_ed_result_t : ChoiceEquality) (at level 2).
Definition ED_HASH_TO_FIELD : nat :=
  3057.
Program Definition ed_hash_to_field (msg_3050 : byte_seq) (
    dst_3051 : byte_seq) (count_3048 : uint_size)
  : both (CEfset (
      [result_3027_loc ; l_i_b_str_3028_loc ; b_i_3029_loc ; uniform_bytes_3030_loc ; output_3046_loc])) [interface] (
    seq_ed_result_t) :=
  ((letb len_in_bytes_3049 : uint_size :=
        (lift_to_both0 count_3048) .* (lift_to_both0 l_v) in
      letbnd(_) uniform_bytes_3052 : byte_seq :=
        expand_message_xmd (lift_to_both0 msg_3050) (lift_to_both0 dst_3051) (
          lift_to_both0 len_in_bytes_3049) in
      letbm output_3046 : seq ed25519_field_element_t loc( output_3046_loc ) :=
        seq_new_ (default : ed25519_field_element_t) (
          lift_to_both0 count_3048) in
      letb output_3046 :=
        foldi_both' (lift_to_both0 (usize 0)) (
            lift_to_both0 count_3048) output_3046 (L := (CEfset (
                [result_3027_loc ; l_i_b_str_3028_loc ; b_i_3029_loc ; uniform_bytes_3030_loc ; output_3046_loc]))) (
            I := [interface]) (fun i_3053 output_3046 =>
            letb elm_offset_3054 : uint_size :=
              (lift_to_both0 l_v) .* (lift_to_both0 i_3053) in
            letb tv_3055 : seq uint8 :=
              seq_slice (lift_to_both0 uniform_bytes_3052) (
                lift_to_both0 elm_offset_3054) (lift_to_both0 l_v) in
            letb u_i_3056 : ed25519_field_element_t :=
              nat_mod_from_byte_seq_be (seq_slice (nat_mod_to_byte_seq_be (
                    nat_mod_from_byte_seq_be (lift_to_both0 tv_3055))) (
                  lift_to_both0 (usize 32)) (lift_to_both0 (usize 32))) in
            letb output_3046 : seq ed25519_field_element_t :=
              seq_upd output_3046 (lift_to_both0 i_3053) (is_pure (
                  lift_to_both0 u_i_3056)) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 output_3046)
            ) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        @Ok seq ed25519_field_element_t error_t (lift_to_both0 output_3046))
      ) : both (CEfset (
        [result_3027_loc ; l_i_b_str_3028_loc ; b_i_3029_loc ; uniform_bytes_3030_loc ; output_3046_loc])) [interface] (
      seq_ed_result_t)).
Fail Next Obligation.


Notation "'ed_is_square_inp'" :=(
  ed25519_field_element_t : choice_type) (in custom pack_type at level 2).
Notation "'ed_is_square_inp'" :=(
  ed25519_field_element_t : ChoiceEquality) (at level 2).
Notation "'ed_is_square_out'" :=(
  bool_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'ed_is_square_out'" :=(
  bool_ChoiceEquality : ChoiceEquality) (at level 2).
Definition ED_IS_SQUARE : nat :=
  3061.
Program Definition ed_is_square (x_3059 : ed25519_field_element_t)
  : both (fset.fset0) [interface] (bool_ChoiceEquality) :=
  ((letb c1_3058 : ed25519_field_element_t :=
        nat_mod_from_byte_seq_be (array_to_be_bytes (lift_to_both0 p_1_2_v)) in
      letb tv_3060 : ed25519_field_element_t :=
        nat_mod_pow_self (lift_to_both0 x_3059) (lift_to_both0 c1_3058) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (((
            lift_to_both0 tv_3060) =.? (nat_mod_zero )) || ((
            lift_to_both0 tv_3060) =.? (nat_mod_one )))
      ) : both (fset.fset0) [interface] (bool_ChoiceEquality)).
Fail Next Obligation.


Notation "'sgn0_m_eq_1_inp'" :=(
  ed25519_field_element_t : choice_type) (in custom pack_type at level 2).
Notation "'sgn0_m_eq_1_inp'" :=(
  ed25519_field_element_t : ChoiceEquality) (at level 2).
Notation "'sgn0_m_eq_1_out'" :=(
  bool_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'sgn0_m_eq_1_out'" :=(
  bool_ChoiceEquality : ChoiceEquality) (at level 2).
Definition SGN0_M_EQ_1 : nat :=
  3063.
Program Definition sgn0_m_eq_1 (x_3062 : ed25519_field_element_t)
  : both (fset.fset0) [interface] (bool_ChoiceEquality) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (((
            lift_to_both0 x_3062) rem (nat_mod_two )) =.? (nat_mod_one ))
      ) : both (fset.fset0) [interface] (bool_ChoiceEquality)).
Fail Next Obligation.


Notation "'ed_clear_cofactor_inp'" :=(
  ed_point_t : choice_type) (in custom pack_type at level 2).
Notation "'ed_clear_cofactor_inp'" :=(ed_point_t : ChoiceEquality) (at level 2).
Notation "'ed_clear_cofactor_out'" :=(
  ed_point_t : choice_type) (in custom pack_type at level 2).
Notation "'ed_clear_cofactor_out'" :=(ed_point_t : ChoiceEquality) (at level 2).
Definition ED_CLEAR_COFACTOR : nat :=
  3065.
Program Definition ed_clear_cofactor (x_3064 : ed_point_t)
  : both (fset.fset0) [interface] (ed_point_t) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (point_mul_by_cofactor (
          lift_to_both0 x_3064))
      ) : both (fset.fset0) [interface] (ed_point_t)).
Fail Next Obligation.


Notation "'cmov_inp'" :=(
  ed25519_field_element_t '× ed25519_field_element_t '× bool_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'cmov_inp'" :=(
  ed25519_field_element_t '× ed25519_field_element_t '× bool_ChoiceEquality : ChoiceEquality) (at level 2).
Notation "'cmov_out'" :=(
  ed25519_field_element_t : choice_type) (in custom pack_type at level 2).
Notation "'cmov_out'" :=(ed25519_field_element_t : ChoiceEquality) (at level 2).
Definition CMOV : nat :=
  3069.
Program Definition cmov (a_3068 : ed25519_field_element_t) (
    b_3067 : ed25519_field_element_t) (c_3066 : bool_ChoiceEquality)
  : both (fset.fset0) [interface] (ed25519_field_element_t) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        if is_pure (I := [interface]) (lift_to_both0 c_3066)
        then lift_to_both0 b_3067
        else lift_to_both0 a_3068)
      ) : both (fset.fset0) [interface] (ed25519_field_element_t)).
Fail Next Obligation.


Notation "'xor_inp'" :=(
  bool_ChoiceEquality '× bool_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'xor_inp'" :=(
  bool_ChoiceEquality '× bool_ChoiceEquality : ChoiceEquality) (at level 2).
Notation "'xor_out'" :=(
  bool_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'xor_out'" :=(bool_ChoiceEquality : ChoiceEquality) (at level 2).
Definition XOR : nat :=
  3072.
Program Definition xor (a_3070 : bool_ChoiceEquality) (
    b_3071 : bool_ChoiceEquality)
  : both (fset.fset0) [interface] (bool_ChoiceEquality) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        if is_pure (I := [interface]) (lift_to_both0 a_3070)
        then if is_pure (I := [interface]) (lift_to_both0 b_3071)
        then lift_to_both0 ((false : bool_ChoiceEquality))
        else lift_to_both0 ((true : bool_ChoiceEquality))
        else if is_pure (I := [interface]) (lift_to_both0 b_3071)
        then lift_to_both0 ((true : bool_ChoiceEquality))
        else lift_to_both0 ((false : bool_ChoiceEquality)))
      ) : both (fset.fset0) [interface] (bool_ChoiceEquality)).
Fail Next Obligation.


Notation "'curve25519_to_edwards25519_inp'" :=(
  ed_point_t : choice_type) (in custom pack_type at level 2).
Notation "'curve25519_to_edwards25519_inp'" :=(
  ed_point_t : ChoiceEquality) (at level 2).
Notation "'curve25519_to_edwards25519_out'" :=(
  ed_point_t : choice_type) (in custom pack_type at level 2).
Notation "'curve25519_to_edwards25519_out'" :=(
  ed_point_t : ChoiceEquality) (at level 2).
Definition CURVE25519_TO_EDWARDS25519 : nat :=
  3091.
Program Definition curve25519_to_edwards25519 (p_3073 : ed_point_t)
  : both (fset.fset0) [interface] (ed_point_t) :=
  ((letb '(s_3074, t_3075, _, _) : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_normalize (lift_to_both0 p_3073) in
      letb one_3076 : ed25519_field_element_t := nat_mod_one  in
      letb zero_3077 : ed25519_field_element_t := nat_mod_zero  in
      letb tv1_3078 : ed25519_field_element_t :=
        (lift_to_both0 s_3074) +% (lift_to_both0 one_3076) in
      letb tv2_3079 : ed25519_field_element_t :=
        (lift_to_both0 tv1_3078) *% (lift_to_both0 t_3075) in
      letb tv2_3080 : ed25519_field_element_t :=
        nat_mod_inv (lift_to_both0 tv2_3079) in
      letb v_3081 : ed25519_field_element_t :=
        (lift_to_both0 tv2_3080) *% (lift_to_both0 tv1_3078) in
      letb v_3082 : ed25519_field_element_t :=
        (lift_to_both0 v_3081) *% (lift_to_both0 s_3074) in
      letb w_3083 : ed25519_field_element_t :=
        (lift_to_both0 tv2_3080) *% (lift_to_both0 t_3075) in
      letb tv1_3084 : ed25519_field_element_t :=
        (lift_to_both0 s_3074) -% (lift_to_both0 one_3076) in
      letb w_3085 : ed25519_field_element_t :=
        (lift_to_both0 w_3083) *% (lift_to_both0 tv1_3084) in
      letb e_3086 : bool_ChoiceEquality :=
        (lift_to_both0 tv2_3080) =.? (lift_to_both0 zero_3077) in
      letb w_3087 : ed25519_field_element_t :=
        cmov (lift_to_both0 w_3085) (lift_to_both0 one_3076) (
          lift_to_both0 e_3086) in
      letb c_3088 : ed25519_field_element_t :=
        (nat_mod_zero ) -% (nat_mod_from_literal (_) (lift_to_both0 (
              @repr U128 486664))) in
      letb sq_3089 : (option (ed25519_field_element_t)) :=
        sqrt (lift_to_both0 c_3088) in
      letb v_3090 : ed25519_field_element_t :=
        (lift_to_both0 v_3082) *% (option_unwrap (lift_to_both0 sq_3089)) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 v_3090,
          lift_to_both0 w_3087,
          lift_to_both0 one_3076,
          (lift_to_both0 v_3090) *% (lift_to_both0 w_3087)
        ))
      ) : both (fset.fset0) [interface] (ed_point_t)).
Fail Next Obligation.

Definition y_3094_loc : ChoiceEqualityLocation :=
  (ed25519_field_element_t ; 3095%nat).
Definition x_3093_loc : ChoiceEqualityLocation :=
  (ed25519_field_element_t ; 3096%nat).
Definition x1_3092_loc : ChoiceEqualityLocation :=
  (ed25519_field_element_t ; 3097%nat).
Notation "'map_to_curve_elligator2_inp'" :=(
  ed25519_field_element_t : choice_type) (in custom pack_type at level 2).
Notation "'map_to_curve_elligator2_inp'" :=(
  ed25519_field_element_t : ChoiceEquality) (at level 2).
Notation "'map_to_curve_elligator2_out'" :=(
  ed_point_t : choice_type) (in custom pack_type at level 2).
Notation "'map_to_curve_elligator2_out'" :=(
  ed_point_t : ChoiceEquality) (at level 2).
Definition MAP_TO_CURVE_ELLIGATOR2 : nat :=
  3108.
Program Definition map_to_curve_elligator2 (u_3102 : ed25519_field_element_t)
  : both (CEfset ([x1_3092_loc ; x_3093_loc ; y_3094_loc])) [interface] (
    ed_point_t) :=
  ((letb j_3098 : ed25519_field_element_t :=
        nat_mod_from_literal (_) (lift_to_both0 j_v) in
      letb z_3099 : ed25519_field_element_t :=
        nat_mod_from_literal (_) (lift_to_both0 z_v) in
      letb one_3100 : ed25519_field_element_t := nat_mod_one  in
      letb zero_3101 : ed25519_field_element_t := nat_mod_zero  in
      letbm x1_3092 : ed25519_field_element_t loc( x1_3092_loc ) :=
        ((lift_to_both0 zero_3101) -% (lift_to_both0 j_3098)) *% (nat_mod_inv ((
              lift_to_both0 one_3100) +% (((lift_to_both0 z_3099) *% (
                  lift_to_both0 u_3102)) *% (lift_to_both0 u_3102)))) in
      letb '(x1_3092) :=
        if (lift_to_both0 x1_3092) =.? (
          lift_to_both0 zero_3101) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset ([x1_3092_loc])) (L2 := CEfset (
            [x1_3092_loc ; x_3093_loc ; y_3094_loc])) (I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
          letbm x1_3092 loc( x1_3092_loc ) :=
            (lift_to_both0 zero_3101) -% (lift_to_both0 j_3098) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 x1_3092)
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          lift_to_both0 x1_3092)
         in
      letb gx1_3103 : ed25519_field_element_t :=
        ((((lift_to_both0 x1_3092) *% (lift_to_both0 x1_3092)) *% (
              lift_to_both0 x1_3092)) +% (((lift_to_both0 j_3098) *% (
                lift_to_both0 x1_3092)) *% (lift_to_both0 x1_3092))) +% (
          lift_to_both0 x1_3092) in
      letb x2_3104 : ed25519_field_element_t :=
        ((lift_to_both0 zero_3101) -% (lift_to_both0 x1_3092)) -% (
          lift_to_both0 j_3098) in
      letb gx2_3105 : ed25519_field_element_t :=
        ((((lift_to_both0 x2_3104) *% (lift_to_both0 x2_3104)) *% (
              lift_to_both0 x2_3104)) +% ((lift_to_both0 j_3098) *% ((
                lift_to_both0 x2_3104) *% (lift_to_both0 x2_3104)))) +% (
          lift_to_both0 x2_3104) in
      letbm x_3093 : ed25519_field_element_t loc( x_3093_loc ) :=
        lift_to_both0 zero_3101 in
      letbm y_3094 : ed25519_field_element_t loc( y_3094_loc ) :=
        lift_to_both0 zero_3101 in
      letb '(x_3093, y_3094) :=
        if ed_is_square (lift_to_both0 gx1_3103) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset (
            [x1_3092_loc ; x_3093_loc ; y_3094_loc])) (L2 := CEfset (
            [x1_3092_loc ; x_3093_loc ; y_3094_loc])) (I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
          letbm x_3093 loc( x_3093_loc ) := lift_to_both0 x1_3092 in
          letbm y_3094 loc( y_3094_loc ) :=
            option_unwrap (sqrt (lift_to_both0 gx1_3103)) in
          letb '(y_3094) :=
            if negb (sgn0_m_eq_1 (lift_to_both0 y_3094)) :bool_ChoiceEquality
            then lift_scope (L1 := CEfset (
                [x1_3092_loc ; x_3093_loc ; y_3094_loc])) (L2 := CEfset (
                [x1_3092_loc ; x_3093_loc ; y_3094_loc])) (I1 := [interface]) (
              I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
              letbm y_3094 loc( y_3094_loc ) :=
                (lift_to_both0 zero_3101) -% (lift_to_both0 y_3094) in
              lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                lift_to_both0 y_3094)
              )
            else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 y_3094)
             in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
              lift_to_both0 x_3093,
              lift_to_both0 y_3094
            ))
          )
        else  lift_scope (L1 := CEfset (
            [x1_3092_loc ; x_3093_loc ; y_3094_loc])) (L2 := CEfset (
            [x1_3092_loc ; x_3093_loc ; y_3094_loc])) (I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
          letbm x_3093 loc( x_3093_loc ) := lift_to_both0 x2_3104 in
          letbm y_3094 loc( y_3094_loc ) :=
            option_unwrap (sqrt (lift_to_both0 gx2_3105)) in
          letb '(y_3094) :=
            if sgn0_m_eq_1 (lift_to_both0 y_3094) :bool_ChoiceEquality
            then lift_scope (L1 := CEfset (
                [x1_3092_loc ; x_3093_loc ; y_3094_loc])) (L2 := CEfset (
                [x1_3092_loc ; x_3093_loc ; y_3094_loc])) (I1 := [interface]) (
              I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
              letbm y_3094 loc( y_3094_loc ) :=
                (lift_to_both0 zero_3101) -% (lift_to_both0 y_3094) in
              lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                lift_to_both0 y_3094)
              )
            else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 y_3094)
             in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
              lift_to_both0 x_3093,
              lift_to_both0 y_3094
            ))
          ) in
      letb s_3106 : ed25519_field_element_t := lift_to_both0 x_3093 in
      letb t_3107 : ed25519_field_element_t := lift_to_both0 y_3094 in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 s_3106,
          lift_to_both0 t_3107,
          lift_to_both0 one_3100,
          (lift_to_both0 s_3106) *% (lift_to_both0 t_3107)
        ))
      ) : both (CEfset ([x1_3092_loc ; x_3093_loc ; y_3094_loc])) [interface] (
      ed_point_t)).
Fail Next Obligation.


Notation "'map_to_curve_elligator2_straight_inp'" :=(
  ed25519_field_element_t : choice_type) (in custom pack_type at level 2).
Notation "'map_to_curve_elligator2_straight_inp'" :=(
  ed25519_field_element_t : ChoiceEquality) (at level 2).
Notation "'map_to_curve_elligator2_straight_out'" :=(
  ed_point_t : choice_type) (in custom pack_type at level 2).
Notation "'map_to_curve_elligator2_straight_out'" :=(
  ed_point_t : ChoiceEquality) (at level 2).
Definition MAP_TO_CURVE_ELLIGATOR2_STRAIGHT : nat :=
  3135.
Program Definition map_to_curve_elligator2_straight (
    u_3113 : ed25519_field_element_t)
  : both (fset.fset0) [interface] (ed_point_t) :=
  ((letb j_3109 : ed25519_field_element_t :=
        nat_mod_from_literal (_) (lift_to_both0 j_v) in
      letb z_3110 : ed25519_field_element_t :=
        nat_mod_from_literal (_) (lift_to_both0 z_v) in
      letb one_3111 : ed25519_field_element_t := nat_mod_one  in
      letb zero_3112 : ed25519_field_element_t := nat_mod_zero  in
      letb tv1_3114 : ed25519_field_element_t :=
        (lift_to_both0 u_3113) *% (lift_to_both0 u_3113) in
      letb tv1_3115 : ed25519_field_element_t :=
        (lift_to_both0 z_3110) *% (lift_to_both0 tv1_3114) in
      letb e1_3116 : bool_ChoiceEquality :=
        (lift_to_both0 tv1_3115) =.? ((lift_to_both0 zero_3112) -% (
            lift_to_both0 one_3111)) in
      letb tv1_3117 : ed25519_field_element_t :=
        cmov (lift_to_both0 tv1_3115) (lift_to_both0 zero_3112) (
          lift_to_both0 e1_3116) in
      letb x1_3118 : ed25519_field_element_t :=
        (lift_to_both0 tv1_3117) +% (lift_to_both0 one_3111) in
      letb x1_3119 : ed25519_field_element_t :=
        nat_mod_inv (lift_to_both0 x1_3118) in
      letb x1_3120 : ed25519_field_element_t :=
        ((lift_to_both0 zero_3112) -% (lift_to_both0 j_3109)) *% (
          lift_to_both0 x1_3119) in
      letb gx1_3121 : ed25519_field_element_t :=
        (lift_to_both0 x1_3120) +% (lift_to_both0 j_3109) in
      letb gx1_3122 : ed25519_field_element_t :=
        (lift_to_both0 gx1_3121) *% (lift_to_both0 x1_3120) in
      letb gx1_3123 : ed25519_field_element_t :=
        (lift_to_both0 gx1_3122) +% (lift_to_both0 one_3111) in
      letb gx1_3124 : ed25519_field_element_t :=
        (lift_to_both0 gx1_3123) *% (lift_to_both0 x1_3120) in
      letb x2_3125 : ed25519_field_element_t :=
        ((lift_to_both0 zero_3112) -% (lift_to_both0 x1_3120)) -% (
          lift_to_both0 j_3109) in
      letb gx2_3126 : ed25519_field_element_t :=
        (lift_to_both0 tv1_3117) *% (lift_to_both0 gx1_3124) in
      letb e2_3127 : bool_ChoiceEquality :=
        ed_is_square (lift_to_both0 gx1_3124) in
      letb x_3128 : ed25519_field_element_t :=
        cmov (lift_to_both0 x2_3125) (lift_to_both0 x1_3120) (
          lift_to_both0 e2_3127) in
      letb y2_3129 : ed25519_field_element_t :=
        cmov (lift_to_both0 gx2_3126) (lift_to_both0 gx1_3124) (
          lift_to_both0 e2_3127) in
      letb y_3130 : ed25519_field_element_t :=
        option_unwrap (sqrt (lift_to_both0 y2_3129)) in
      letb e3_3131 : bool_ChoiceEquality :=
        sgn0_m_eq_1 (lift_to_both0 y_3130) in
      letb y_3132 : ed25519_field_element_t :=
        cmov (lift_to_both0 y_3130) ((lift_to_both0 zero_3112) -% (
            lift_to_both0 y_3130)) (xor (lift_to_both0 e2_3127) (
            lift_to_both0 e3_3131)) in
      letb s_3133 : ed25519_field_element_t := lift_to_both0 x_3128 in
      letb t_3134 : ed25519_field_element_t := lift_to_both0 y_3132 in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 s_3133,
          lift_to_both0 t_3134,
          lift_to_both0 one_3111,
          (lift_to_both0 s_3133) *% (lift_to_both0 t_3134)
        ))
      ) : both (fset.fset0) [interface] (ed_point_t)).
Fail Next Obligation.


Notation "'map_to_curve_elligator2_curve25519_inp'" :=(
  ed25519_field_element_t : choice_type) (in custom pack_type at level 2).
Notation "'map_to_curve_elligator2_curve25519_inp'" :=(
  ed25519_field_element_t : ChoiceEquality) (at level 2).
Notation "'map_to_curve_elligator2_curve25519_out'" :=(
  ed_point_t : choice_type) (in custom pack_type at level 2).
Notation "'map_to_curve_elligator2_curve25519_out'" :=(
  ed_point_t : ChoiceEquality) (at level 2).
Definition MAP_TO_CURVE_ELLIGATOR2_CURVE25519 : nat :=
  3183.
Program Definition map_to_curve_elligator2_curve25519 (
    u_3144 : ed25519_field_element_t)
  : both (fset.fset0) [interface] (ed_point_t) :=
  ((letb j_3136 : ed25519_field_element_t :=
        nat_mod_from_literal (_) (lift_to_both0 j_v) in
      letb zero_3137 : ed25519_field_element_t := nat_mod_zero  in
      letb one_3138 : ed25519_field_element_t := nat_mod_one  in
      letb two_3139 : ed25519_field_element_t := nat_mod_two  in
      letb c1_3140 : ed25519_field_element_t :=
        nat_mod_from_byte_seq_be (array_to_be_bytes (lift_to_both0 p_3_8_v)) in
      letb c2_3141 : ed25519_field_element_t :=
        nat_mod_pow_self (lift_to_both0 two_3139) (lift_to_both0 c1_3140) in
      letb c3_3142 : ed25519_field_element_t :=
        option_unwrap (sqrt ((lift_to_both0 zero_3137) -% (
              lift_to_both0 one_3138))) in
      letb c4_3143 : ed25519_field_element_t :=
        nat_mod_from_byte_seq_be (array_to_be_bytes (lift_to_both0 p_5_8_v)) in
      letb tv1_3145 : ed25519_field_element_t :=
        (lift_to_both0 u_3144) *% (lift_to_both0 u_3144) in
      letb tv1_3146 : ed25519_field_element_t :=
        (lift_to_both0 two_3139) *% (lift_to_both0 tv1_3145) in
      letb xd_3147 : ed25519_field_element_t :=
        (lift_to_both0 tv1_3146) +% (lift_to_both0 one_3138) in
      letb x1n_3148 : ed25519_field_element_t :=
        (lift_to_both0 zero_3137) -% (lift_to_both0 j_3136) in
      letb tv2_3149 : ed25519_field_element_t :=
        (lift_to_both0 xd_3147) *% (lift_to_both0 xd_3147) in
      letb gxd_3150 : ed25519_field_element_t :=
        (lift_to_both0 tv2_3149) *% (lift_to_both0 xd_3147) in
      letb gx1_3151 : ed25519_field_element_t :=
        (lift_to_both0 j_3136) *% (lift_to_both0 tv1_3146) in
      letb gx1_3152 : ed25519_field_element_t :=
        (lift_to_both0 gx1_3151) *% (lift_to_both0 x1n_3148) in
      letb gx1_3153 : ed25519_field_element_t :=
        (lift_to_both0 gx1_3152) +% (lift_to_both0 tv2_3149) in
      letb gx1_3154 : ed25519_field_element_t :=
        (lift_to_both0 gx1_3153) *% (lift_to_both0 x1n_3148) in
      letb tv3_3155 : ed25519_field_element_t :=
        (lift_to_both0 gxd_3150) *% (lift_to_both0 gxd_3150) in
      letb tv2_3156 : ed25519_field_element_t :=
        (lift_to_both0 tv3_3155) *% (lift_to_both0 tv3_3155) in
      letb tv3_3157 : ed25519_field_element_t :=
        (lift_to_both0 tv3_3155) *% (lift_to_both0 gxd_3150) in
      letb tv3_3158 : ed25519_field_element_t :=
        (lift_to_both0 tv3_3157) *% (lift_to_both0 gx1_3154) in
      letb tv2_3159 : ed25519_field_element_t :=
        (lift_to_both0 tv2_3156) *% (lift_to_both0 tv3_3158) in
      letb y11_3160 : ed25519_field_element_t :=
        nat_mod_pow_self (lift_to_both0 tv2_3159) (lift_to_both0 c4_3143) in
      letb y11_3161 : ed25519_field_element_t :=
        (lift_to_both0 y11_3160) *% (lift_to_both0 tv3_3158) in
      letb y12_3162 : ed25519_field_element_t :=
        (lift_to_both0 y11_3161) *% (lift_to_both0 c3_3142) in
      letb tv2_3163 : ed25519_field_element_t :=
        (lift_to_both0 y11_3161) *% (lift_to_both0 y11_3161) in
      letb tv2_3164 : ed25519_field_element_t :=
        (lift_to_both0 tv2_3163) *% (lift_to_both0 gxd_3150) in
      letb e1_3165 : bool_ChoiceEquality :=
        (lift_to_both0 tv2_3164) =.? (lift_to_both0 gx1_3154) in
      letb y1_3166 : ed25519_field_element_t :=
        cmov (lift_to_both0 y12_3162) (lift_to_both0 y11_3161) (
          lift_to_both0 e1_3165) in
      letb x2n_3167 : ed25519_field_element_t :=
        (lift_to_both0 x1n_3148) *% (lift_to_both0 tv1_3146) in
      letb y21_3168 : ed25519_field_element_t :=
        (lift_to_both0 y11_3161) *% (lift_to_both0 u_3144) in
      letb y21_3169 : ed25519_field_element_t :=
        (lift_to_both0 y21_3168) *% (lift_to_both0 c2_3141) in
      letb y22_3170 : ed25519_field_element_t :=
        (lift_to_both0 y21_3169) *% (lift_to_both0 c3_3142) in
      letb gx2_3171 : ed25519_field_element_t :=
        (lift_to_both0 gx1_3154) *% (lift_to_both0 tv1_3146) in
      letb tv2_3172 : ed25519_field_element_t :=
        (lift_to_both0 y21_3169) *% (lift_to_both0 y21_3169) in
      letb tv2_3173 : ed25519_field_element_t :=
        (lift_to_both0 tv2_3172) *% (lift_to_both0 gxd_3150) in
      letb e2_3174 : bool_ChoiceEquality :=
        (lift_to_both0 tv2_3173) =.? (lift_to_both0 gx2_3171) in
      letb y2_3175 : ed25519_field_element_t :=
        cmov (lift_to_both0 y22_3170) (lift_to_both0 y21_3169) (
          lift_to_both0 e2_3174) in
      letb tv2_3176 : ed25519_field_element_t :=
        (lift_to_both0 y1_3166) *% (lift_to_both0 y1_3166) in
      letb tv2_3177 : ed25519_field_element_t :=
        (lift_to_both0 tv2_3176) *% (lift_to_both0 gxd_3150) in
      letb e3_3178 : bool_ChoiceEquality :=
        (lift_to_both0 tv2_3177) =.? (lift_to_both0 gx1_3154) in
      letb xn_3179 : ed25519_field_element_t :=
        cmov (lift_to_both0 x2n_3167) (lift_to_both0 x1n_3148) (
          lift_to_both0 e3_3178) in
      letb y_3180 : ed25519_field_element_t :=
        cmov (lift_to_both0 y2_3175) (lift_to_both0 y1_3166) (
          lift_to_both0 e3_3178) in
      letb e4_3181 : bool_ChoiceEquality :=
        sgn0_m_eq_1 (lift_to_both0 y_3180) in
      letb y_3182 : ed25519_field_element_t :=
        cmov (lift_to_both0 y_3180) ((lift_to_both0 zero_3137) -% (
            lift_to_both0 y_3180)) (xor (lift_to_both0 e3_3178) (
            lift_to_both0 e4_3181)) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 xn_3179,
          lift_to_both0 xd_3147,
          lift_to_both0 y_3182,
          lift_to_both0 one_3138
        ))
      ) : both (fset.fset0) [interface] (ed_point_t)).
Fail Next Obligation.


Notation "'map_to_curve_elligator2_edwards25519_inp'" :=(
  ed25519_field_element_t : choice_type) (in custom pack_type at level 2).
Notation "'map_to_curve_elligator2_edwards25519_inp'" :=(
  ed25519_field_element_t : ChoiceEquality) (at level 2).
Notation "'map_to_curve_elligator2_edwards25519_out'" :=(
  ed_point_t : choice_type) (in custom pack_type at level 2).
Notation "'map_to_curve_elligator2_edwards25519_out'" :=(
  ed_point_t : ChoiceEquality) (at level 2).
Definition MAP_TO_CURVE_ELLIGATOR2_EDWARDS25519 : nat :=
  3207.
Program Definition map_to_curve_elligator2_edwards25519 (
    u_3189 : ed25519_field_element_t)
  : both (fset.fset0) [interface] (ed_point_t) :=
  ((letb j_3184 : ed25519_field_element_t :=
        nat_mod_from_literal (_) (lift_to_both0 j_v) in
      letb zero_3185 : ed25519_field_element_t := nat_mod_zero  in
      letb one_3186 : ed25519_field_element_t := nat_mod_one  in
      letb two_3187 : ed25519_field_element_t := nat_mod_two  in
      letb c1_3188 : ed25519_field_element_t :=
        option_unwrap (sqrt ((lift_to_both0 zero_3185) -% ((
                lift_to_both0 j_3184) +% (lift_to_both0 two_3187)))) in
      letb '(xmn_3190, xmd_3191, ymn_3192, ymd_3193) : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        map_to_curve_elligator2_curve25519 (lift_to_both0 u_3189) in
      letb xn_3194 : ed25519_field_element_t :=
        (lift_to_both0 xmn_3190) *% (lift_to_both0 ymd_3193) in
      letb xn_3195 : ed25519_field_element_t :=
        (lift_to_both0 xn_3194) *% (lift_to_both0 c1_3188) in
      letb xd_3196 : ed25519_field_element_t :=
        (lift_to_both0 xmd_3191) *% (lift_to_both0 ymn_3192) in
      letb yn_3197 : ed25519_field_element_t :=
        (lift_to_both0 xmn_3190) -% (lift_to_both0 xmd_3191) in
      letb yd_3198 : ed25519_field_element_t :=
        (lift_to_both0 xmn_3190) +% (lift_to_both0 xmd_3191) in
      letb tv1_3199 : ed25519_field_element_t :=
        (lift_to_both0 xd_3196) *% (lift_to_both0 yd_3198) in
      letb e_3200 : bool_ChoiceEquality :=
        (lift_to_both0 tv1_3199) =.? (lift_to_both0 zero_3185) in
      letb xn_3201 : ed25519_field_element_t :=
        cmov (lift_to_both0 xn_3195) (lift_to_both0 zero_3185) (
          lift_to_both0 e_3200) in
      letb xd_3202 : ed25519_field_element_t :=
        cmov (lift_to_both0 xd_3196) (lift_to_both0 one_3186) (
          lift_to_both0 e_3200) in
      letb yn_3203 : ed25519_field_element_t :=
        cmov (lift_to_both0 yn_3197) (lift_to_both0 one_3186) (
          lift_to_both0 e_3200) in
      letb yd_3204 : ed25519_field_element_t :=
        cmov (lift_to_both0 yd_3198) (lift_to_both0 one_3186) (
          lift_to_both0 e_3200) in
      letb x_3205 : ed25519_field_element_t :=
        (lift_to_both0 xn_3201) *% (nat_mod_inv (lift_to_both0 xd_3202)) in
      letb y_3206 : ed25519_field_element_t :=
        (lift_to_both0 yn_3203) *% (nat_mod_inv (lift_to_both0 yd_3204)) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 x_3205,
          lift_to_both0 y_3206,
          lift_to_both0 one_3186,
          (lift_to_both0 x_3205) *% (lift_to_both0 y_3206)
        ))
      ) : both (fset.fset0) [interface] (ed_point_t)).
Fail Next Obligation.


Notation "'map_to_curve_elligator2_edwards_inp'" :=(
  ed25519_field_element_t : choice_type) (in custom pack_type at level 2).
Notation "'map_to_curve_elligator2_edwards_inp'" :=(
  ed25519_field_element_t : ChoiceEquality) (at level 2).
Notation "'map_to_curve_elligator2_edwards_out'" :=(
  ed_point_t : choice_type) (in custom pack_type at level 2).
Notation "'map_to_curve_elligator2_edwards_out'" :=(
  ed_point_t : ChoiceEquality) (at level 2).
Definition MAP_TO_CURVE_ELLIGATOR2_EDWARDS : nat :=
  3210.
Program Definition map_to_curve_elligator2_edwards (
    u_3208 : ed25519_field_element_t)
  : both (CEfset ([x1_3092_loc ; x_3093_loc ; y_3094_loc])) [interface] (
    ed_point_t) :=
  ((letb st_3209 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        map_to_curve_elligator2 (lift_to_both0 u_3208) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        curve25519_to_edwards25519 (lift_to_both0 st_3209))
      ) : both (CEfset ([x1_3092_loc ; x_3093_loc ; y_3094_loc])) [interface] (
      ed_point_t)).
Fail Next Obligation.


Notation "'ed_encode_to_curve_inp'" :=(
  byte_seq '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'ed_encode_to_curve_inp'" :=(
  byte_seq '× byte_seq : ChoiceEquality) (at level 2).
Notation "'ed_encode_to_curve_out'" :=(
  ed_point_result_t : choice_type) (in custom pack_type at level 2).
Notation "'ed_encode_to_curve_out'" :=(
  ed_point_result_t : ChoiceEquality) (at level 2).
Definition ED_ENCODE_TO_CURVE : nat :=
  3215.
Program Definition ed_encode_to_curve (msg_3211 : byte_seq) (
    dst_3212 : byte_seq)
  : both (CEfset (
      [result_3027_loc ; l_i_b_str_3028_loc ; b_i_3029_loc ; uniform_bytes_3030_loc ; output_3046_loc ; x1_3092_loc ; x_3093_loc ; y_3094_loc])) [interface] (
    ed_point_result_t) :=
  ((letbnd(_) u_3213 : seq ed25519_field_element_t :=
        ed_hash_to_field (lift_to_both0 msg_3211) (lift_to_both0 dst_3212) (
          lift_to_both0 (usize 1)) in
      letb q_3214 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        map_to_curve_elligator2_edwards (seq_index (u_3213) (lift_to_both0 (
              usize 0))) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (@Ok ed_point_t error_t (
          ed_clear_cofactor (lift_to_both0 q_3214)))
      ) : both (CEfset (
        [result_3027_loc ; l_i_b_str_3028_loc ; b_i_3029_loc ; uniform_bytes_3030_loc ; output_3046_loc ; x1_3092_loc ; x_3093_loc ; y_3094_loc])) [interface] (
      ed_point_result_t)).
Fail Next Obligation.

