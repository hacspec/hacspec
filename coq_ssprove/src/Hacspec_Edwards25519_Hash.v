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
  array_from_list uint64 [
    (secret (@repr U64 4611686018427387903)) : uint64;
    (secret (@repr U64 18446744073709551615)) : uint64;
    (secret (@repr U64 18446744073709551615)) : uint64;
    (secret (@repr U64 18446744073709551606)) : uint64
  ].

Definition p_3_8_v : arr_ed25519_field_element_t :=
  array_from_list uint64 [
    (secret (@repr U64 1152921504606846975)) : uint64;
    (secret (@repr U64 18446744073709551615)) : uint64;
    (secret (@repr U64 18446744073709551615)) : uint64;
    (secret (@repr U64 18446744073709551614)) : uint64
  ].

Definition p_5_8_v : arr_ed25519_field_element_t :=
  array_from_list uint64 [
    (secret (@repr U64 1152921504606846975)) : uint64;
    (secret (@repr U64 18446744073709551615)) : uint64;
    (secret (@repr U64 18446744073709551615)) : uint64;
    (secret (@repr U64 18446744073709551613)) : uint64
  ].

Definition result_2897_loc : ChoiceEqualityLocation :=
  ((result (error_t) (byte_seq)) ; 2901%nat).
Definition b_i_2899_loc : ChoiceEqualityLocation :=
  (seq uint8 ; 2902%nat).
Definition l_i_b_str_2898_loc : ChoiceEqualityLocation :=
  (seq uint8 ; 2903%nat).
Definition uniform_bytes_2900_loc : ChoiceEqualityLocation :=
  (seq uint8 ; 2904%nat).
Notation "'expand_message_xmd_inp'" :=(
  byte_seq '× byte_seq '× uint_size : choice_type) (in custom pack_type at level 2).
Notation "'expand_message_xmd_inp'" :=(
  byte_seq '× byte_seq '× uint_size : ChoiceEquality) (at level 2).
Notation "'expand_message_xmd_out'" :=(
  byte_seq_result_t : choice_type) (in custom pack_type at level 2).
Notation "'expand_message_xmd_out'" :=(
  byte_seq_result_t : ChoiceEquality) (at level 2).
Definition EXPAND_MESSAGE_XMD : nat :=
  2915.
Program Definition expand_message_xmd (msg_2910 : byte_seq) (
    dst_2907 : byte_seq) (len_in_bytes_2905 : uint_size)
  : both (CEfset (
      [result_2897_loc ; l_i_b_str_2898_loc ; b_i_2899_loc ; uniform_bytes_2900_loc])) [interface] (
    byte_seq_result_t) :=
  ((letb ell_2906 : uint_size :=
        (((lift_to_both0 len_in_bytes_2905) .+ (
              lift_to_both0 b_in_bytes_v)) .- (lift_to_both0 (usize 1))) ./ (
          lift_to_both0 b_in_bytes_v) in
      letbm result_2897 : (result (error_t) (
            byte_seq)) loc( result_2897_loc ) :=
        @Err byte_seq error_t (ExpandMessageAbort) in
      letb '(result_2897) :=
        if negb ((((lift_to_both0 ell_2906) >.? (lift_to_both0 (
                  usize 255))) || ((lift_to_both0 len_in_bytes_2905) >.? (
                lift_to_both0 (usize 65535)))) || ((seq_len (
                lift_to_both0 dst_2907)) >.? (lift_to_both0 (
                usize 255)))) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset (
            [result_2897_loc ; l_i_b_str_2898_loc ; b_i_2899_loc ; uniform_bytes_2900_loc])) (
          L2 := CEfset (
            [result_2897_loc ; l_i_b_str_2898_loc ; b_i_2899_loc ; uniform_bytes_2900_loc])) (
          I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
          letb dst_prime_2908 : seq uint8 :=
            seq_push (lift_to_both0 dst_2907) (uint8_from_usize (seq_len (
                  lift_to_both0 dst_2907))) in
          letb z_pad_2909 : seq uint8 :=
            seq_new_ (default : uint8) (lift_to_both0 s_in_bytes_v) in
          letbm l_i_b_str_2898 : seq uint8 loc( l_i_b_str_2898_loc ) :=
            seq_new_ (default : uint8) (lift_to_both0 (usize 2)) in
          letb l_i_b_str_2898 : seq uint8 :=
            seq_upd l_i_b_str_2898 (lift_to_both0 (usize 0)) (is_pure (
                uint8_from_usize ((lift_to_both0 len_in_bytes_2905) ./ (
                    lift_to_both0 (usize 256))))) in
          letb l_i_b_str_2898 : seq uint8 :=
            seq_upd l_i_b_str_2898 (lift_to_both0 (usize 1)) (is_pure (
                uint8_from_usize (lift_to_both0 len_in_bytes_2905))) in
          letb msg_prime_2911 : seq uint8 :=
            seq_concat (seq_concat (seq_concat (seq_concat (
                    lift_to_both0 z_pad_2909) (lift_to_both0 msg_2910)) (
                  lift_to_both0 l_i_b_str_2898)) (seq_new_ (default : uint8) (
                  lift_to_both0 (usize 1)))) (lift_to_both0 dst_prime_2908) in
          letb b_0_2912 : seq uint8 :=
            seq_from_seq (array_to_seq (hash (lift_to_both0 msg_prime_2911))) in
          letbm b_i_2899 : seq uint8 loc( b_i_2899_loc ) :=
            seq_from_seq (array_to_seq (hash (seq_concat (seq_push (
                    lift_to_both0 b_0_2912) (secret (lift_to_both0 (
                        @repr U8 1)))) (lift_to_both0 dst_prime_2908)))) in
          letbm uniform_bytes_2900 : seq uint8 loc( uniform_bytes_2900_loc ) :=
            seq_from_seq (lift_to_both0 b_i_2899) in
          letb '(b_i_2899, uniform_bytes_2900) :=
            foldi_both' (lift_to_both0 (usize 2)) ((lift_to_both0 ell_2906) .+ (
                  lift_to_both0 (usize 1))) prod_ce(b_i_2899, uniform_bytes_2900
              ) (L := (CEfset (
                    [result_2897_loc ; l_i_b_str_2898_loc ; b_i_2899_loc ; uniform_bytes_2900_loc]))) (
                I := [interface]) (fun i_2913 '(b_i_2899, uniform_bytes_2900) =>
                letb t_2914 : seq uint8 :=
                  seq_from_seq (lift_to_both0 b_0_2912) in
                letbm b_i_2899 loc( b_i_2899_loc ) :=
                  seq_from_seq (array_to_seq (hash (seq_concat (seq_push ((
                            lift_to_both0 t_2914) seq_xor (
                            lift_to_both0 b_i_2899)) (uint8_from_usize (
                            lift_to_both0 i_2913))) (
                        lift_to_both0 dst_prime_2908)))) in
                letbm uniform_bytes_2900 loc( uniform_bytes_2900_loc ) :=
                  seq_concat (lift_to_both0 uniform_bytes_2900) (
                    lift_to_both0 b_i_2899) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                    lift_to_both0 b_i_2899,
                    lift_to_both0 uniform_bytes_2900
                  ))
                ) in
          letbm result_2897 loc( result_2897_loc ) :=
            @Ok byte_seq error_t (seq_truncate (
                lift_to_both0 uniform_bytes_2900) (
                lift_to_both0 len_in_bytes_2905)) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 result_2897)
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          lift_to_both0 result_2897)
         in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        lift_to_both0 result_2897)
      ) : both (CEfset (
        [result_2897_loc ; l_i_b_str_2898_loc ; b_i_2899_loc ; uniform_bytes_2900_loc])) [interface] (
      byte_seq_result_t)).
Fail Next Obligation.

Definition output_2916_loc : ChoiceEqualityLocation :=
  (seq ed25519_field_element_t ; 2917%nat).
Notation "'ed_hash_to_field_inp'" :=(
  byte_seq '× byte_seq '× uint_size : choice_type) (in custom pack_type at level 2).
Notation "'ed_hash_to_field_inp'" :=(
  byte_seq '× byte_seq '× uint_size : ChoiceEquality) (at level 2).
Notation "'ed_hash_to_field_out'" :=(
  seq_ed_result_t : choice_type) (in custom pack_type at level 2).
Notation "'ed_hash_to_field_out'" :=(
  seq_ed_result_t : ChoiceEquality) (at level 2).
Definition ED_HASH_TO_FIELD : nat :=
  2927.
Program Definition ed_hash_to_field (msg_2920 : byte_seq) (
    dst_2921 : byte_seq) (count_2918 : uint_size)
  : both (CEfset (
      [result_2897_loc ; l_i_b_str_2898_loc ; b_i_2899_loc ; uniform_bytes_2900_loc ; output_2916_loc])) [interface] (
    seq_ed_result_t) :=
  ((letb len_in_bytes_2919 : uint_size :=
        (lift_to_both0 count_2918) .* (lift_to_both0 l_v) in
      letbnd(_) uniform_bytes_2922 : byte_seq :=
        expand_message_xmd (lift_to_both0 msg_2920) (lift_to_both0 dst_2921) (
          lift_to_both0 len_in_bytes_2919) in
      letbm output_2916 : seq ed25519_field_element_t loc( output_2916_loc ) :=
        seq_new_ (default : ed25519_field_element_t) (
          lift_to_both0 count_2918) in
      letb output_2916 :=
        foldi_both' (lift_to_both0 (usize 0)) (
            lift_to_both0 count_2918) output_2916 (L := (CEfset (
                [result_2897_loc ; l_i_b_str_2898_loc ; b_i_2899_loc ; uniform_bytes_2900_loc ; output_2916_loc]))) (
            I := [interface]) (fun i_2923 output_2916 =>
            letb elm_offset_2924 : uint_size :=
              (lift_to_both0 l_v) .* (lift_to_both0 i_2923) in
            letb tv_2925 : seq uint8 :=
              seq_slice (lift_to_both0 uniform_bytes_2922) (
                lift_to_both0 elm_offset_2924) (lift_to_both0 l_v) in
            letb u_i_2926 : ed25519_field_element_t :=
              nat_mod_from_byte_seq_be (seq_slice (nat_mod_to_byte_seq_be (
                    nat_mod_from_byte_seq_be (lift_to_both0 tv_2925))) (
                  lift_to_both0 (usize 32)) (lift_to_both0 (usize 32))) in
            letb output_2916 : seq ed25519_field_element_t :=
              seq_upd output_2916 (lift_to_both0 i_2923) (is_pure (
                  lift_to_both0 u_i_2926)) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 output_2916)
            ) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        @Ok seq ed25519_field_element_t error_t (lift_to_both0 output_2916))
      ) : both (CEfset (
        [result_2897_loc ; l_i_b_str_2898_loc ; b_i_2899_loc ; uniform_bytes_2900_loc ; output_2916_loc])) [interface] (
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
  2931.
Program Definition ed_is_square (x_2929 : ed25519_field_element_t)
  : both (fset.fset0) [interface] (bool_ChoiceEquality) :=
  ((letb c1_2928 : ed25519_field_element_t :=
        nat_mod_from_byte_seq_be (array_to_be_bytes (lift_to_both0 p_1_2_v)) in
      letb tv_2930 : ed25519_field_element_t :=
        nat_mod_pow_self (lift_to_both0 x_2929) (lift_to_both0 c1_2928) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (((
            lift_to_both0 tv_2930) =.? (nat_mod_zero )) || ((
            lift_to_both0 tv_2930) =.? (nat_mod_one )))
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
  2933.
Program Definition sgn0_m_eq_1 (x_2932 : ed25519_field_element_t)
  : both (fset.fset0) [interface] (bool_ChoiceEquality) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (((
            lift_to_both0 x_2932) rem (nat_mod_two )) =.? (nat_mod_one ))
      ) : both (fset.fset0) [interface] (bool_ChoiceEquality)).
Fail Next Obligation.


Notation "'ed_clear_cofactor_inp'" :=(
  ed_point_t : choice_type) (in custom pack_type at level 2).
Notation "'ed_clear_cofactor_inp'" :=(ed_point_t : ChoiceEquality) (at level 2).
Notation "'ed_clear_cofactor_out'" :=(
  ed_point_t : choice_type) (in custom pack_type at level 2).
Notation "'ed_clear_cofactor_out'" :=(ed_point_t : ChoiceEquality) (at level 2).
Definition ED_CLEAR_COFACTOR : nat :=
  2935.
Program Definition ed_clear_cofactor (x_2934 : ed_point_t)
  : both (fset.fset0) [interface] (ed_point_t) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (point_mul_by_cofactor (
          lift_to_both0 x_2934))
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
  2939.
Program Definition cmov (a_2938 : ed25519_field_element_t) (
    b_2937 : ed25519_field_element_t) (c_2936 : bool_ChoiceEquality)
  : both (fset.fset0) [interface] (ed25519_field_element_t) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        if is_pure (I := [interface]) (lift_to_both0 c_2936)
        then lift_to_both0 b_2937
        else lift_to_both0 a_2938)
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
  2942.
Program Definition xor (a_2940 : bool_ChoiceEquality) (
    b_2941 : bool_ChoiceEquality)
  : both (fset.fset0) [interface] (bool_ChoiceEquality) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        if is_pure (I := [interface]) (lift_to_both0 a_2940)
        then if is_pure (I := [interface]) (lift_to_both0 b_2941)
        then lift_to_both0 ((false : bool_ChoiceEquality))
        else lift_to_both0 ((true : bool_ChoiceEquality))
        else if is_pure (I := [interface]) (lift_to_both0 b_2941)
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
  2961.
Program Definition curve25519_to_edwards25519 (p_2943 : ed_point_t)
  : both (fset.fset0) [interface] (ed_point_t) :=
  ((letb '(s_2944, t_2945, _, _) : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_normalize (lift_to_both0 p_2943) in
      letb one_2946 : ed25519_field_element_t := nat_mod_one  in
      letb zero_2947 : ed25519_field_element_t := nat_mod_zero  in
      letb tv1_2948 : ed25519_field_element_t :=
        (lift_to_both0 s_2944) +% (lift_to_both0 one_2946) in
      letb tv2_2949 : ed25519_field_element_t :=
        (lift_to_both0 tv1_2948) *% (lift_to_both0 t_2945) in
      letb tv2_2950 : ed25519_field_element_t :=
        nat_mod_inv (lift_to_both0 tv2_2949) in
      letb v_2951 : ed25519_field_element_t :=
        (lift_to_both0 tv2_2950) *% (lift_to_both0 tv1_2948) in
      letb v_2952 : ed25519_field_element_t :=
        (lift_to_both0 v_2951) *% (lift_to_both0 s_2944) in
      letb w_2953 : ed25519_field_element_t :=
        (lift_to_both0 tv2_2950) *% (lift_to_both0 t_2945) in
      letb tv1_2954 : ed25519_field_element_t :=
        (lift_to_both0 s_2944) -% (lift_to_both0 one_2946) in
      letb w_2955 : ed25519_field_element_t :=
        (lift_to_both0 w_2953) *% (lift_to_both0 tv1_2954) in
      letb e_2956 : bool_ChoiceEquality :=
        (lift_to_both0 tv2_2950) =.? (lift_to_both0 zero_2947) in
      letb w_2957 : ed25519_field_element_t :=
        cmov (lift_to_both0 w_2955) (lift_to_both0 one_2946) (
          lift_to_both0 e_2956) in
      letb c_2958 : ed25519_field_element_t :=
        (nat_mod_zero ) -% (nat_mod_from_literal (_) (lift_to_both0 (
              @repr U128 486664))) in
      letb sq_2959 : (option (ed25519_field_element_t)) :=
        sqrt (lift_to_both0 c_2958) in
      letb v_2960 : ed25519_field_element_t :=
        (lift_to_both0 v_2952) *% (option_unwrap (lift_to_both0 sq_2959)) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 v_2960,
          lift_to_both0 w_2957,
          lift_to_both0 one_2946,
          (lift_to_both0 v_2960) *% (lift_to_both0 w_2957)
        ))
      ) : both (fset.fset0) [interface] (ed_point_t)).
Fail Next Obligation.

Definition y_2964_loc : ChoiceEqualityLocation :=
  (ed25519_field_element_t ; 2965%nat).
Definition x1_2962_loc : ChoiceEqualityLocation :=
  (ed25519_field_element_t ; 2966%nat).
Definition x_2963_loc : ChoiceEqualityLocation :=
  (ed25519_field_element_t ; 2967%nat).
Notation "'map_to_curve_elligator2_inp'" :=(
  ed25519_field_element_t : choice_type) (in custom pack_type at level 2).
Notation "'map_to_curve_elligator2_inp'" :=(
  ed25519_field_element_t : ChoiceEquality) (at level 2).
Notation "'map_to_curve_elligator2_out'" :=(
  ed_point_t : choice_type) (in custom pack_type at level 2).
Notation "'map_to_curve_elligator2_out'" :=(
  ed_point_t : ChoiceEquality) (at level 2).
Definition MAP_TO_CURVE_ELLIGATOR2 : nat :=
  2978.
Program Definition map_to_curve_elligator2 (u_2972 : ed25519_field_element_t)
  : both (CEfset ([x1_2962_loc ; x_2963_loc ; y_2964_loc])) [interface] (
    ed_point_t) :=
  ((letb j_2968 : ed25519_field_element_t :=
        nat_mod_from_literal (_) (lift_to_both0 j_v) in
      letb z_2969 : ed25519_field_element_t :=
        nat_mod_from_literal (_) (lift_to_both0 z_v) in
      letb one_2970 : ed25519_field_element_t := nat_mod_one  in
      letb zero_2971 : ed25519_field_element_t := nat_mod_zero  in
      letbm x1_2962 : ed25519_field_element_t loc( x1_2962_loc ) :=
        ((lift_to_both0 zero_2971) -% (lift_to_both0 j_2968)) *% (nat_mod_inv ((
              lift_to_both0 one_2970) +% (((lift_to_both0 z_2969) *% (
                  lift_to_both0 u_2972)) *% (lift_to_both0 u_2972)))) in
      letb '(x1_2962) :=
        if (lift_to_both0 x1_2962) =.? (
          lift_to_both0 zero_2971) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset ([x1_2962_loc])) (L2 := CEfset (
            [x1_2962_loc ; x_2963_loc ; y_2964_loc])) (I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
          letbm x1_2962 loc( x1_2962_loc ) :=
            (lift_to_both0 zero_2971) -% (lift_to_both0 j_2968) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 x1_2962)
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          lift_to_both0 x1_2962)
         in
      letb gx1_2973 : ed25519_field_element_t :=
        ((((lift_to_both0 x1_2962) *% (lift_to_both0 x1_2962)) *% (
              lift_to_both0 x1_2962)) +% (((lift_to_both0 j_2968) *% (
                lift_to_both0 x1_2962)) *% (lift_to_both0 x1_2962))) +% (
          lift_to_both0 x1_2962) in
      letb x2_2974 : ed25519_field_element_t :=
        ((lift_to_both0 zero_2971) -% (lift_to_both0 x1_2962)) -% (
          lift_to_both0 j_2968) in
      letb gx2_2975 : ed25519_field_element_t :=
        ((((lift_to_both0 x2_2974) *% (lift_to_both0 x2_2974)) *% (
              lift_to_both0 x2_2974)) +% ((lift_to_both0 j_2968) *% ((
                lift_to_both0 x2_2974) *% (lift_to_both0 x2_2974)))) +% (
          lift_to_both0 x2_2974) in
      letbm x_2963 : ed25519_field_element_t loc( x_2963_loc ) :=
        lift_to_both0 zero_2971 in
      letbm y_2964 : ed25519_field_element_t loc( y_2964_loc ) :=
        lift_to_both0 zero_2971 in
      letb '(x_2963, y_2964) :=
        if ed_is_square (lift_to_both0 gx1_2973) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset (
            [x1_2962_loc ; x_2963_loc ; y_2964_loc])) (L2 := CEfset (
            [x1_2962_loc ; x_2963_loc ; y_2964_loc])) (I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
          letbm x_2963 loc( x_2963_loc ) := lift_to_both0 x1_2962 in
          letbm y_2964 loc( y_2964_loc ) :=
            option_unwrap (sqrt (lift_to_both0 gx1_2973)) in
          letb '(y_2964) :=
            if negb (sgn0_m_eq_1 (lift_to_both0 y_2964)) :bool_ChoiceEquality
            then lift_scope (L1 := CEfset (
                [x1_2962_loc ; x_2963_loc ; y_2964_loc])) (L2 := CEfset (
                [x1_2962_loc ; x_2963_loc ; y_2964_loc])) (I1 := [interface]) (
              I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
              letbm y_2964 loc( y_2964_loc ) :=
                (lift_to_both0 zero_2971) -% (lift_to_both0 y_2964) in
              lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                lift_to_both0 y_2964)
              )
            else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 y_2964)
             in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
              lift_to_both0 x_2963,
              lift_to_both0 y_2964
            ))
          )
        else  lift_scope (L1 := CEfset (
            [x1_2962_loc ; x_2963_loc ; y_2964_loc])) (L2 := CEfset (
            [x1_2962_loc ; x_2963_loc ; y_2964_loc])) (I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
          letbm x_2963 loc( x_2963_loc ) := lift_to_both0 x2_2974 in
          letbm y_2964 loc( y_2964_loc ) :=
            option_unwrap (sqrt (lift_to_both0 gx2_2975)) in
          letb '(y_2964) :=
            if sgn0_m_eq_1 (lift_to_both0 y_2964) :bool_ChoiceEquality
            then lift_scope (L1 := CEfset (
                [x1_2962_loc ; x_2963_loc ; y_2964_loc])) (L2 := CEfset (
                [x1_2962_loc ; x_2963_loc ; y_2964_loc])) (I1 := [interface]) (
              I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
              letbm y_2964 loc( y_2964_loc ) :=
                (lift_to_both0 zero_2971) -% (lift_to_both0 y_2964) in
              lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                lift_to_both0 y_2964)
              )
            else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 y_2964)
             in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
              lift_to_both0 x_2963,
              lift_to_both0 y_2964
            ))
          ) in
      letb s_2976 : ed25519_field_element_t := lift_to_both0 x_2963 in
      letb t_2977 : ed25519_field_element_t := lift_to_both0 y_2964 in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 s_2976,
          lift_to_both0 t_2977,
          lift_to_both0 one_2970,
          (lift_to_both0 s_2976) *% (lift_to_both0 t_2977)
        ))
      ) : both (CEfset ([x1_2962_loc ; x_2963_loc ; y_2964_loc])) [interface] (
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
  3005.
Program Definition map_to_curve_elligator2_straight (
    u_2983 : ed25519_field_element_t)
  : both (fset.fset0) [interface] (ed_point_t) :=
  ((letb j_2979 : ed25519_field_element_t :=
        nat_mod_from_literal (_) (lift_to_both0 j_v) in
      letb z_2980 : ed25519_field_element_t :=
        nat_mod_from_literal (_) (lift_to_both0 z_v) in
      letb one_2981 : ed25519_field_element_t := nat_mod_one  in
      letb zero_2982 : ed25519_field_element_t := nat_mod_zero  in
      letb tv1_2984 : ed25519_field_element_t :=
        (lift_to_both0 u_2983) *% (lift_to_both0 u_2983) in
      letb tv1_2985 : ed25519_field_element_t :=
        (lift_to_both0 z_2980) *% (lift_to_both0 tv1_2984) in
      letb e1_2986 : bool_ChoiceEquality :=
        (lift_to_both0 tv1_2985) =.? ((lift_to_both0 zero_2982) -% (
            lift_to_both0 one_2981)) in
      letb tv1_2987 : ed25519_field_element_t :=
        cmov (lift_to_both0 tv1_2985) (lift_to_both0 zero_2982) (
          lift_to_both0 e1_2986) in
      letb x1_2988 : ed25519_field_element_t :=
        (lift_to_both0 tv1_2987) +% (lift_to_both0 one_2981) in
      letb x1_2989 : ed25519_field_element_t :=
        nat_mod_inv (lift_to_both0 x1_2988) in
      letb x1_2990 : ed25519_field_element_t :=
        ((lift_to_both0 zero_2982) -% (lift_to_both0 j_2979)) *% (
          lift_to_both0 x1_2989) in
      letb gx1_2991 : ed25519_field_element_t :=
        (lift_to_both0 x1_2990) +% (lift_to_both0 j_2979) in
      letb gx1_2992 : ed25519_field_element_t :=
        (lift_to_both0 gx1_2991) *% (lift_to_both0 x1_2990) in
      letb gx1_2993 : ed25519_field_element_t :=
        (lift_to_both0 gx1_2992) +% (lift_to_both0 one_2981) in
      letb gx1_2994 : ed25519_field_element_t :=
        (lift_to_both0 gx1_2993) *% (lift_to_both0 x1_2990) in
      letb x2_2995 : ed25519_field_element_t :=
        ((lift_to_both0 zero_2982) -% (lift_to_both0 x1_2990)) -% (
          lift_to_both0 j_2979) in
      letb gx2_2996 : ed25519_field_element_t :=
        (lift_to_both0 tv1_2987) *% (lift_to_both0 gx1_2994) in
      letb e2_2997 : bool_ChoiceEquality :=
        ed_is_square (lift_to_both0 gx1_2994) in
      letb x_2998 : ed25519_field_element_t :=
        cmov (lift_to_both0 x2_2995) (lift_to_both0 x1_2990) (
          lift_to_both0 e2_2997) in
      letb y2_2999 : ed25519_field_element_t :=
        cmov (lift_to_both0 gx2_2996) (lift_to_both0 gx1_2994) (
          lift_to_both0 e2_2997) in
      letb y_3000 : ed25519_field_element_t :=
        option_unwrap (sqrt (lift_to_both0 y2_2999)) in
      letb e3_3001 : bool_ChoiceEquality :=
        sgn0_m_eq_1 (lift_to_both0 y_3000) in
      letb y_3002 : ed25519_field_element_t :=
        cmov (lift_to_both0 y_3000) ((lift_to_both0 zero_2982) -% (
            lift_to_both0 y_3000)) (xor (lift_to_both0 e2_2997) (
            lift_to_both0 e3_3001)) in
      letb s_3003 : ed25519_field_element_t := lift_to_both0 x_2998 in
      letb t_3004 : ed25519_field_element_t := lift_to_both0 y_3002 in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 s_3003,
          lift_to_both0 t_3004,
          lift_to_both0 one_2981,
          (lift_to_both0 s_3003) *% (lift_to_both0 t_3004)
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
  3053.
Program Definition map_to_curve_elligator2_curve25519 (
    u_3014 : ed25519_field_element_t)
  : both (fset.fset0) [interface] (ed_point_t) :=
  ((letb j_3006 : ed25519_field_element_t :=
        nat_mod_from_literal (_) (lift_to_both0 j_v) in
      letb zero_3007 : ed25519_field_element_t := nat_mod_zero  in
      letb one_3008 : ed25519_field_element_t := nat_mod_one  in
      letb two_3009 : ed25519_field_element_t := nat_mod_two  in
      letb c1_3010 : ed25519_field_element_t :=
        nat_mod_from_byte_seq_be (array_to_be_bytes (lift_to_both0 p_3_8_v)) in
      letb c2_3011 : ed25519_field_element_t :=
        nat_mod_pow_self (lift_to_both0 two_3009) (lift_to_both0 c1_3010) in
      letb c3_3012 : ed25519_field_element_t :=
        option_unwrap (sqrt ((lift_to_both0 zero_3007) -% (
              lift_to_both0 one_3008))) in
      letb c4_3013 : ed25519_field_element_t :=
        nat_mod_from_byte_seq_be (array_to_be_bytes (lift_to_both0 p_5_8_v)) in
      letb tv1_3015 : ed25519_field_element_t :=
        (lift_to_both0 u_3014) *% (lift_to_both0 u_3014) in
      letb tv1_3016 : ed25519_field_element_t :=
        (lift_to_both0 two_3009) *% (lift_to_both0 tv1_3015) in
      letb xd_3017 : ed25519_field_element_t :=
        (lift_to_both0 tv1_3016) +% (lift_to_both0 one_3008) in
      letb x1n_3018 : ed25519_field_element_t :=
        (lift_to_both0 zero_3007) -% (lift_to_both0 j_3006) in
      letb tv2_3019 : ed25519_field_element_t :=
        (lift_to_both0 xd_3017) *% (lift_to_both0 xd_3017) in
      letb gxd_3020 : ed25519_field_element_t :=
        (lift_to_both0 tv2_3019) *% (lift_to_both0 xd_3017) in
      letb gx1_3021 : ed25519_field_element_t :=
        (lift_to_both0 j_3006) *% (lift_to_both0 tv1_3016) in
      letb gx1_3022 : ed25519_field_element_t :=
        (lift_to_both0 gx1_3021) *% (lift_to_both0 x1n_3018) in
      letb gx1_3023 : ed25519_field_element_t :=
        (lift_to_both0 gx1_3022) +% (lift_to_both0 tv2_3019) in
      letb gx1_3024 : ed25519_field_element_t :=
        (lift_to_both0 gx1_3023) *% (lift_to_both0 x1n_3018) in
      letb tv3_3025 : ed25519_field_element_t :=
        (lift_to_both0 gxd_3020) *% (lift_to_both0 gxd_3020) in
      letb tv2_3026 : ed25519_field_element_t :=
        (lift_to_both0 tv3_3025) *% (lift_to_both0 tv3_3025) in
      letb tv3_3027 : ed25519_field_element_t :=
        (lift_to_both0 tv3_3025) *% (lift_to_both0 gxd_3020) in
      letb tv3_3028 : ed25519_field_element_t :=
        (lift_to_both0 tv3_3027) *% (lift_to_both0 gx1_3024) in
      letb tv2_3029 : ed25519_field_element_t :=
        (lift_to_both0 tv2_3026) *% (lift_to_both0 tv3_3028) in
      letb y11_3030 : ed25519_field_element_t :=
        nat_mod_pow_self (lift_to_both0 tv2_3029) (lift_to_both0 c4_3013) in
      letb y11_3031 : ed25519_field_element_t :=
        (lift_to_both0 y11_3030) *% (lift_to_both0 tv3_3028) in
      letb y12_3032 : ed25519_field_element_t :=
        (lift_to_both0 y11_3031) *% (lift_to_both0 c3_3012) in
      letb tv2_3033 : ed25519_field_element_t :=
        (lift_to_both0 y11_3031) *% (lift_to_both0 y11_3031) in
      letb tv2_3034 : ed25519_field_element_t :=
        (lift_to_both0 tv2_3033) *% (lift_to_both0 gxd_3020) in
      letb e1_3035 : bool_ChoiceEquality :=
        (lift_to_both0 tv2_3034) =.? (lift_to_both0 gx1_3024) in
      letb y1_3036 : ed25519_field_element_t :=
        cmov (lift_to_both0 y12_3032) (lift_to_both0 y11_3031) (
          lift_to_both0 e1_3035) in
      letb x2n_3037 : ed25519_field_element_t :=
        (lift_to_both0 x1n_3018) *% (lift_to_both0 tv1_3016) in
      letb y21_3038 : ed25519_field_element_t :=
        (lift_to_both0 y11_3031) *% (lift_to_both0 u_3014) in
      letb y21_3039 : ed25519_field_element_t :=
        (lift_to_both0 y21_3038) *% (lift_to_both0 c2_3011) in
      letb y22_3040 : ed25519_field_element_t :=
        (lift_to_both0 y21_3039) *% (lift_to_both0 c3_3012) in
      letb gx2_3041 : ed25519_field_element_t :=
        (lift_to_both0 gx1_3024) *% (lift_to_both0 tv1_3016) in
      letb tv2_3042 : ed25519_field_element_t :=
        (lift_to_both0 y21_3039) *% (lift_to_both0 y21_3039) in
      letb tv2_3043 : ed25519_field_element_t :=
        (lift_to_both0 tv2_3042) *% (lift_to_both0 gxd_3020) in
      letb e2_3044 : bool_ChoiceEquality :=
        (lift_to_both0 tv2_3043) =.? (lift_to_both0 gx2_3041) in
      letb y2_3045 : ed25519_field_element_t :=
        cmov (lift_to_both0 y22_3040) (lift_to_both0 y21_3039) (
          lift_to_both0 e2_3044) in
      letb tv2_3046 : ed25519_field_element_t :=
        (lift_to_both0 y1_3036) *% (lift_to_both0 y1_3036) in
      letb tv2_3047 : ed25519_field_element_t :=
        (lift_to_both0 tv2_3046) *% (lift_to_both0 gxd_3020) in
      letb e3_3048 : bool_ChoiceEquality :=
        (lift_to_both0 tv2_3047) =.? (lift_to_both0 gx1_3024) in
      letb xn_3049 : ed25519_field_element_t :=
        cmov (lift_to_both0 x2n_3037) (lift_to_both0 x1n_3018) (
          lift_to_both0 e3_3048) in
      letb y_3050 : ed25519_field_element_t :=
        cmov (lift_to_both0 y2_3045) (lift_to_both0 y1_3036) (
          lift_to_both0 e3_3048) in
      letb e4_3051 : bool_ChoiceEquality :=
        sgn0_m_eq_1 (lift_to_both0 y_3050) in
      letb y_3052 : ed25519_field_element_t :=
        cmov (lift_to_both0 y_3050) ((lift_to_both0 zero_3007) -% (
            lift_to_both0 y_3050)) (xor (lift_to_both0 e3_3048) (
            lift_to_both0 e4_3051)) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 xn_3049,
          lift_to_both0 xd_3017,
          lift_to_both0 y_3052,
          lift_to_both0 one_3008
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
  3077.
Program Definition map_to_curve_elligator2_edwards25519 (
    u_3059 : ed25519_field_element_t)
  : both (fset.fset0) [interface] (ed_point_t) :=
  ((letb j_3054 : ed25519_field_element_t :=
        nat_mod_from_literal (_) (lift_to_both0 j_v) in
      letb zero_3055 : ed25519_field_element_t := nat_mod_zero  in
      letb one_3056 : ed25519_field_element_t := nat_mod_one  in
      letb two_3057 : ed25519_field_element_t := nat_mod_two  in
      letb c1_3058 : ed25519_field_element_t :=
        option_unwrap (sqrt ((lift_to_both0 zero_3055) -% ((
                lift_to_both0 j_3054) +% (lift_to_both0 two_3057)))) in
      letb '(xmn_3060, xmd_3061, ymn_3062, ymd_3063) : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        map_to_curve_elligator2_curve25519 (lift_to_both0 u_3059) in
      letb xn_3064 : ed25519_field_element_t :=
        (lift_to_both0 xmn_3060) *% (lift_to_both0 ymd_3063) in
      letb xn_3065 : ed25519_field_element_t :=
        (lift_to_both0 xn_3064) *% (lift_to_both0 c1_3058) in
      letb xd_3066 : ed25519_field_element_t :=
        (lift_to_both0 xmd_3061) *% (lift_to_both0 ymn_3062) in
      letb yn_3067 : ed25519_field_element_t :=
        (lift_to_both0 xmn_3060) -% (lift_to_both0 xmd_3061) in
      letb yd_3068 : ed25519_field_element_t :=
        (lift_to_both0 xmn_3060) +% (lift_to_both0 xmd_3061) in
      letb tv1_3069 : ed25519_field_element_t :=
        (lift_to_both0 xd_3066) *% (lift_to_both0 yd_3068) in
      letb e_3070 : bool_ChoiceEquality :=
        (lift_to_both0 tv1_3069) =.? (lift_to_both0 zero_3055) in
      letb xn_3071 : ed25519_field_element_t :=
        cmov (lift_to_both0 xn_3065) (lift_to_both0 zero_3055) (
          lift_to_both0 e_3070) in
      letb xd_3072 : ed25519_field_element_t :=
        cmov (lift_to_both0 xd_3066) (lift_to_both0 one_3056) (
          lift_to_both0 e_3070) in
      letb yn_3073 : ed25519_field_element_t :=
        cmov (lift_to_both0 yn_3067) (lift_to_both0 one_3056) (
          lift_to_both0 e_3070) in
      letb yd_3074 : ed25519_field_element_t :=
        cmov (lift_to_both0 yd_3068) (lift_to_both0 one_3056) (
          lift_to_both0 e_3070) in
      letb x_3075 : ed25519_field_element_t :=
        (lift_to_both0 xn_3071) *% (nat_mod_inv (lift_to_both0 xd_3072)) in
      letb y_3076 : ed25519_field_element_t :=
        (lift_to_both0 yn_3073) *% (nat_mod_inv (lift_to_both0 yd_3074)) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 x_3075,
          lift_to_both0 y_3076,
          lift_to_both0 one_3056,
          (lift_to_both0 x_3075) *% (lift_to_both0 y_3076)
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
  3080.
Program Definition map_to_curve_elligator2_edwards (
    u_3078 : ed25519_field_element_t)
  : both (CEfset ([x1_2962_loc ; x_2963_loc ; y_2964_loc])) [interface] (
    ed_point_t) :=
  ((letb st_3079 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        map_to_curve_elligator2 (lift_to_both0 u_3078) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        curve25519_to_edwards25519 (lift_to_both0 st_3079))
      ) : both (CEfset ([x1_2962_loc ; x_2963_loc ; y_2964_loc])) [interface] (
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
  3085.
Program Definition ed_encode_to_curve (msg_3081 : byte_seq) (
    dst_3082 : byte_seq)
  : both (CEfset (
      [result_2897_loc ; l_i_b_str_2898_loc ; b_i_2899_loc ; uniform_bytes_2900_loc ; output_2916_loc ; x1_2962_loc ; x_2963_loc ; y_2964_loc])) [interface] (
    ed_point_result_t) :=
  ((letbnd(_) u_3083 : seq ed25519_field_element_t :=
        ed_hash_to_field (lift_to_both0 msg_3081) (lift_to_both0 dst_3082) (
          lift_to_both0 (usize 1)) in
      letb q_3084 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        map_to_curve_elligator2_edwards (seq_index (u_3083) (lift_to_both0 (
              usize 0))) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (@Ok ed_point_t error_t (
          ed_clear_cofactor (lift_to_both0 q_3084)))
      ) : both (CEfset (
        [result_2897_loc ; l_i_b_str_2898_loc ; b_i_2899_loc ; uniform_bytes_2900_loc ; output_2916_loc ; x1_2962_loc ; x_2963_loc ; y_2964_loc])) [interface] (
      ed_point_result_t)).
Fail Next Obligation.

