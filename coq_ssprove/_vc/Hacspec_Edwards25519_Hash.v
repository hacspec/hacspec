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

Definition uniform_bytes_2950_loc : ChoiceEqualityLocation :=
  (seq uint8 ; 2951%nat).
Definition l_i_b_str_2948_loc : ChoiceEqualityLocation :=
  (seq uint8 ; 2952%nat).
Definition b_i_2949_loc : ChoiceEqualityLocation :=
  (seq uint8 ; 2953%nat).
Definition result_2947_loc : ChoiceEqualityLocation :=
  ((result (error_t) (byte_seq)) ; 2954%nat).
Notation "'expand_message_xmd_inp'" :=(
  byte_seq '× byte_seq '× uint_size : choice_type) (in custom pack_type at level 2).
Notation "'expand_message_xmd_inp'" :=(
  byte_seq '× byte_seq '× uint_size : ChoiceEquality) (at level 2).
Notation "'expand_message_xmd_out'" :=(
  byte_seq_result_t : choice_type) (in custom pack_type at level 2).
Notation "'expand_message_xmd_out'" :=(
  byte_seq_result_t : ChoiceEquality) (at level 2).
Definition EXPAND_MESSAGE_XMD : nat :=
  2965.
Program Definition expand_message_xmd (msg_2960 : byte_seq) (
    dst_2957 : byte_seq) (len_in_bytes_2955 : uint_size)
  : both (CEfset (
      [result_2947_loc ; l_i_b_str_2948_loc ; b_i_2949_loc ; uniform_bytes_2950_loc])) [interface] (
    byte_seq_result_t) :=
  ((letb ell_2956 : uint_size :=
        (((lift_to_both0 len_in_bytes_2955) .+ (
              lift_to_both0 b_in_bytes_v)) .- (lift_to_both0 (usize 1))) ./ (
          lift_to_both0 b_in_bytes_v) in
      letbm result_2947 : (result (error_t) (
            byte_seq)) loc( result_2947_loc ) :=
        @Err byte_seq error_t (ExpandMessageAbort) in
      letb '(result_2947) :=
        if negb ((((lift_to_both0 ell_2956) >.? (lift_to_both0 (
                  usize 255))) || ((lift_to_both0 len_in_bytes_2955) >.? (
                lift_to_both0 (usize 65535)))) || ((seq_len (
                lift_to_both0 dst_2957)) >.? (lift_to_both0 (
                usize 255)))) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset (
            [result_2947_loc ; l_i_b_str_2948_loc ; b_i_2949_loc ; uniform_bytes_2950_loc])) (
          L2 := CEfset (
            [result_2947_loc ; l_i_b_str_2948_loc ; b_i_2949_loc ; uniform_bytes_2950_loc])) (
          I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
          letb dst_prime_2958 : seq uint8 :=
            seq_push (lift_to_both0 dst_2957) (uint8_from_usize (seq_len (
                  lift_to_both0 dst_2957))) in
          letb z_pad_2959 : seq uint8 :=
            seq_new_ (default : uint8) (lift_to_both0 s_in_bytes_v) in
          letbm l_i_b_str_2948 : seq uint8 loc( l_i_b_str_2948_loc ) :=
            seq_new_ (default : uint8) (lift_to_both0 (usize 2)) in
          letb l_i_b_str_2948 : seq uint8 :=
            seq_upd l_i_b_str_2948 (lift_to_both0 (usize 0)) (is_pure (
                uint8_from_usize ((lift_to_both0 len_in_bytes_2955) ./ (
                    lift_to_both0 (usize 256))))) in
          letb l_i_b_str_2948 : seq uint8 :=
            seq_upd l_i_b_str_2948 (lift_to_both0 (usize 1)) (is_pure (
                uint8_from_usize (lift_to_both0 len_in_bytes_2955))) in
          letb msg_prime_2961 : seq uint8 :=
            seq_concat (seq_concat (seq_concat (seq_concat (
                    lift_to_both0 z_pad_2959) (lift_to_both0 msg_2960)) (
                  lift_to_both0 l_i_b_str_2948)) (seq_new_ (default : uint8) (
                  lift_to_both0 (usize 1)))) (lift_to_both0 dst_prime_2958) in
          letb b_0_2962 : seq uint8 :=
            seq_from_seq (array_to_seq (hash (lift_to_both0 msg_prime_2961))) in
          letbm b_i_2949 : seq uint8 loc( b_i_2949_loc ) :=
            seq_from_seq (array_to_seq (hash (seq_concat (seq_push (
                    lift_to_both0 b_0_2962) (secret (lift_to_both0 (
                        @repr U8 1)))) (lift_to_both0 dst_prime_2958)))) in
          letbm uniform_bytes_2950 : seq uint8 loc( uniform_bytes_2950_loc ) :=
            seq_from_seq (lift_to_both0 b_i_2949) in
          letb '(b_i_2949, uniform_bytes_2950) :=
            foldi_both' (lift_to_both0 (usize 2)) ((lift_to_both0 ell_2956) .+ (
                  lift_to_both0 (usize 1))) prod_ce(b_i_2949, uniform_bytes_2950
              ) (L := (CEfset (
                    [result_2947_loc ; l_i_b_str_2948_loc ; b_i_2949_loc ; uniform_bytes_2950_loc]))) (
                I := [interface]) (fun i_2963 '(b_i_2949, uniform_bytes_2950) =>
                letb t_2964 : seq uint8 :=
                  seq_from_seq (lift_to_both0 b_0_2962) in
                letbm b_i_2949 loc( b_i_2949_loc ) :=
                  seq_from_seq (array_to_seq (hash (seq_concat (seq_push ((
                            lift_to_both0 t_2964) seq_xor (
                            lift_to_both0 b_i_2949)) (uint8_from_usize (
                            lift_to_both0 i_2963))) (
                        lift_to_both0 dst_prime_2958)))) in
                letbm uniform_bytes_2950 loc( uniform_bytes_2950_loc ) :=
                  seq_concat (lift_to_both0 uniform_bytes_2950) (
                    lift_to_both0 b_i_2949) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                    lift_to_both0 b_i_2949,
                    lift_to_both0 uniform_bytes_2950
                  ))
                ) in
          letbm result_2947 loc( result_2947_loc ) :=
            @Ok byte_seq error_t (seq_truncate (
                lift_to_both0 uniform_bytes_2950) (
                lift_to_both0 len_in_bytes_2955)) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 result_2947)
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          lift_to_both0 result_2947)
         in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        lift_to_both0 result_2947)
      ) : both (CEfset (
        [result_2947_loc ; l_i_b_str_2948_loc ; b_i_2949_loc ; uniform_bytes_2950_loc])) [interface] (
      byte_seq_result_t)).
Fail Next Obligation.

Definition output_2966_loc : ChoiceEqualityLocation :=
  (seq ed25519_field_element_t ; 2967%nat).
Notation "'ed_hash_to_field_inp'" :=(
  byte_seq '× byte_seq '× uint_size : choice_type) (in custom pack_type at level 2).
Notation "'ed_hash_to_field_inp'" :=(
  byte_seq '× byte_seq '× uint_size : ChoiceEquality) (at level 2).
Notation "'ed_hash_to_field_out'" :=(
  seq_ed_result_t : choice_type) (in custom pack_type at level 2).
Notation "'ed_hash_to_field_out'" :=(
  seq_ed_result_t : ChoiceEquality) (at level 2).
Definition ED_HASH_TO_FIELD : nat :=
  2977.
Program Definition ed_hash_to_field (msg_2970 : byte_seq) (
    dst_2971 : byte_seq) (count_2968 : uint_size)
  : both (CEfset (
      [result_2947_loc ; l_i_b_str_2948_loc ; b_i_2949_loc ; uniform_bytes_2950_loc ; output_2966_loc])) [interface] (
    seq_ed_result_t) :=
  ((letb len_in_bytes_2969 : uint_size :=
        (lift_to_both0 count_2968) .* (lift_to_both0 l_v) in
      letbnd(_) uniform_bytes_2972 : byte_seq :=
        expand_message_xmd (lift_to_both0 msg_2970) (lift_to_both0 dst_2971) (
          lift_to_both0 len_in_bytes_2969) in
      letbm output_2966 : seq ed25519_field_element_t loc( output_2966_loc ) :=
        seq_new_ (default : ed25519_field_element_t) (
          lift_to_both0 count_2968) in
      letb output_2966 :=
        foldi_both' (lift_to_both0 (usize 0)) (
            lift_to_both0 count_2968) output_2966 (L := (CEfset (
                [result_2947_loc ; l_i_b_str_2948_loc ; b_i_2949_loc ; uniform_bytes_2950_loc ; output_2966_loc]))) (
            I := [interface]) (fun i_2973 output_2966 =>
            letb elm_offset_2974 : uint_size :=
              (lift_to_both0 l_v) .* (lift_to_both0 i_2973) in
            letb tv_2975 : seq uint8 :=
              seq_slice (lift_to_both0 uniform_bytes_2972) (
                lift_to_both0 elm_offset_2974) (lift_to_both0 l_v) in
            letb u_i_2976 : ed25519_field_element_t :=
              nat_mod_from_byte_seq_be (seq_slice (nat_mod_to_byte_seq_be (
                    nat_mod_from_byte_seq_be (lift_to_both0 tv_2975))) (
                  lift_to_both0 (usize 32)) (lift_to_both0 (usize 32))) in
            letb output_2966 : seq ed25519_field_element_t :=
              seq_upd output_2966 (lift_to_both0 i_2973) (is_pure (
                  lift_to_both0 u_i_2976)) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 output_2966)
            ) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        @Ok seq ed25519_field_element_t error_t (lift_to_both0 output_2966))
      ) : both (CEfset (
        [result_2947_loc ; l_i_b_str_2948_loc ; b_i_2949_loc ; uniform_bytes_2950_loc ; output_2966_loc])) [interface] (
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
  2981.
Program Definition ed_is_square (x_2979 : ed25519_field_element_t)
  : both (fset.fset0) [interface] (bool_ChoiceEquality) :=
  ((letb c1_2978 : ed25519_field_element_t :=
        nat_mod_from_byte_seq_be (array_to_be_bytes (lift_to_both0 p_1_2_v)) in
      letb tv_2980 : ed25519_field_element_t :=
        nat_mod_pow_self (lift_to_both0 x_2979) (lift_to_both0 c1_2978) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (((
            lift_to_both0 tv_2980) =.? (nat_mod_zero )) || ((
            lift_to_both0 tv_2980) =.? (nat_mod_one )))
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
  2983.
Program Definition sgn0_m_eq_1 (x_2982 : ed25519_field_element_t)
  : both (fset.fset0) [interface] (bool_ChoiceEquality) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (((
            lift_to_both0 x_2982) rem (nat_mod_two )) =.? (nat_mod_one ))
      ) : both (fset.fset0) [interface] (bool_ChoiceEquality)).
Fail Next Obligation.


Notation "'ed_clear_cofactor_inp'" :=(
  ed_point_t : choice_type) (in custom pack_type at level 2).
Notation "'ed_clear_cofactor_inp'" :=(ed_point_t : ChoiceEquality) (at level 2).
Notation "'ed_clear_cofactor_out'" :=(
  ed_point_t : choice_type) (in custom pack_type at level 2).
Notation "'ed_clear_cofactor_out'" :=(ed_point_t : ChoiceEquality) (at level 2).
Definition ED_CLEAR_COFACTOR : nat :=
  2985.
Program Definition ed_clear_cofactor (x_2984 : ed_point_t)
  : both (fset.fset0) [interface] (ed_point_t) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (point_mul_by_cofactor (
          lift_to_both0 x_2984))
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
  2989.
Program Definition cmov (a_2988 : ed25519_field_element_t) (
    b_2987 : ed25519_field_element_t) (c_2986 : bool_ChoiceEquality)
  : both (fset.fset0) [interface] (ed25519_field_element_t) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        if is_pure (I := [interface]) (lift_to_both0 c_2986)
        then lift_to_both0 b_2987
        else lift_to_both0 a_2988)
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
  2992.
Program Definition xor (a_2990 : bool_ChoiceEquality) (
    b_2991 : bool_ChoiceEquality)
  : both (fset.fset0) [interface] (bool_ChoiceEquality) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        if is_pure (I := [interface]) (lift_to_both0 a_2990)
        then if is_pure (I := [interface]) (lift_to_both0 b_2991)
        then lift_to_both0 ((false : bool_ChoiceEquality))
        else lift_to_both0 ((true : bool_ChoiceEquality))
        else if is_pure (I := [interface]) (lift_to_both0 b_2991)
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
  3011.
Program Definition curve25519_to_edwards25519 (p_2993 : ed_point_t)
  : both (fset.fset0) [interface] (ed_point_t) :=
  ((letb '(s_2994, t_2995, _, _) : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_normalize (lift_to_both0 p_2993) in
      letb one_2996 : ed25519_field_element_t := nat_mod_one  in
      letb zero_2997 : ed25519_field_element_t := nat_mod_zero  in
      letb tv1_2998 : ed25519_field_element_t :=
        (lift_to_both0 s_2994) +% (lift_to_both0 one_2996) in
      letb tv2_2999 : ed25519_field_element_t :=
        (lift_to_both0 tv1_2998) *% (lift_to_both0 t_2995) in
      letb tv2_3000 : ed25519_field_element_t :=
        nat_mod_inv (lift_to_both0 tv2_2999) in
      letb v_3001 : ed25519_field_element_t :=
        (lift_to_both0 tv2_3000) *% (lift_to_both0 tv1_2998) in
      letb v_3002 : ed25519_field_element_t :=
        (lift_to_both0 v_3001) *% (lift_to_both0 s_2994) in
      letb w_3003 : ed25519_field_element_t :=
        (lift_to_both0 tv2_3000) *% (lift_to_both0 t_2995) in
      letb tv1_3004 : ed25519_field_element_t :=
        (lift_to_both0 s_2994) -% (lift_to_both0 one_2996) in
      letb w_3005 : ed25519_field_element_t :=
        (lift_to_both0 w_3003) *% (lift_to_both0 tv1_3004) in
      letb e_3006 : bool_ChoiceEquality :=
        (lift_to_both0 tv2_3000) =.? (lift_to_both0 zero_2997) in
      letb w_3007 : ed25519_field_element_t :=
        cmov (lift_to_both0 w_3005) (lift_to_both0 one_2996) (
          lift_to_both0 e_3006) in
      letb c_3008 : ed25519_field_element_t :=
        (nat_mod_zero ) -% (nat_mod_from_literal (_) (lift_to_both0 (
              @repr U128 486664))) in
      letb sq_3009 : (option (ed25519_field_element_t)) :=
        sqrt (lift_to_both0 c_3008) in
      letb v_3010 : ed25519_field_element_t :=
        (lift_to_both0 v_3002) *% (option_unwrap (lift_to_both0 sq_3009)) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 v_3010,
          lift_to_both0 w_3007,
          lift_to_both0 one_2996,
          (lift_to_both0 v_3010) *% (lift_to_both0 w_3007)
        ))
      ) : both (fset.fset0) [interface] (ed_point_t)).
Fail Next Obligation.

Definition x1_3012_loc : ChoiceEqualityLocation :=
  (ed25519_field_element_t ; 3015%nat).
Definition y_3014_loc : ChoiceEqualityLocation :=
  (ed25519_field_element_t ; 3016%nat).
Definition x_3013_loc : ChoiceEqualityLocation :=
  (ed25519_field_element_t ; 3017%nat).
Notation "'map_to_curve_elligator2_inp'" :=(
  ed25519_field_element_t : choice_type) (in custom pack_type at level 2).
Notation "'map_to_curve_elligator2_inp'" :=(
  ed25519_field_element_t : ChoiceEquality) (at level 2).
Notation "'map_to_curve_elligator2_out'" :=(
  ed_point_t : choice_type) (in custom pack_type at level 2).
Notation "'map_to_curve_elligator2_out'" :=(
  ed_point_t : ChoiceEquality) (at level 2).
Definition MAP_TO_CURVE_ELLIGATOR2 : nat :=
  3028.
Program Definition map_to_curve_elligator2 (u_3022 : ed25519_field_element_t)
  : both (CEfset ([x1_3012_loc ; x_3013_loc ; y_3014_loc])) [interface] (
    ed_point_t) :=
  ((letb j_3018 : ed25519_field_element_t :=
        nat_mod_from_literal (_) (lift_to_both0 j_v) in
      letb z_3019 : ed25519_field_element_t :=
        nat_mod_from_literal (_) (lift_to_both0 z_v) in
      letb one_3020 : ed25519_field_element_t := nat_mod_one  in
      letb zero_3021 : ed25519_field_element_t := nat_mod_zero  in
      letbm x1_3012 : ed25519_field_element_t loc( x1_3012_loc ) :=
        ((lift_to_both0 zero_3021) -% (lift_to_both0 j_3018)) *% (nat_mod_inv ((
              lift_to_both0 one_3020) +% (((lift_to_both0 z_3019) *% (
                  lift_to_both0 u_3022)) *% (lift_to_both0 u_3022)))) in
      letb '(x1_3012) :=
        if (lift_to_both0 x1_3012) =.? (
          lift_to_both0 zero_3021) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset ([x1_3012_loc])) (L2 := CEfset (
            [x1_3012_loc ; x_3013_loc ; y_3014_loc])) (I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
          letbm x1_3012 loc( x1_3012_loc ) :=
            (lift_to_both0 zero_3021) -% (lift_to_both0 j_3018) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 x1_3012)
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          lift_to_both0 x1_3012)
         in
      letb gx1_3023 : ed25519_field_element_t :=
        ((((lift_to_both0 x1_3012) *% (lift_to_both0 x1_3012)) *% (
              lift_to_both0 x1_3012)) +% (((lift_to_both0 j_3018) *% (
                lift_to_both0 x1_3012)) *% (lift_to_both0 x1_3012))) +% (
          lift_to_both0 x1_3012) in
      letb x2_3024 : ed25519_field_element_t :=
        ((lift_to_both0 zero_3021) -% (lift_to_both0 x1_3012)) -% (
          lift_to_both0 j_3018) in
      letb gx2_3025 : ed25519_field_element_t :=
        ((((lift_to_both0 x2_3024) *% (lift_to_both0 x2_3024)) *% (
              lift_to_both0 x2_3024)) +% ((lift_to_both0 j_3018) *% ((
                lift_to_both0 x2_3024) *% (lift_to_both0 x2_3024)))) +% (
          lift_to_both0 x2_3024) in
      letbm x_3013 : ed25519_field_element_t loc( x_3013_loc ) :=
        lift_to_both0 zero_3021 in
      letbm y_3014 : ed25519_field_element_t loc( y_3014_loc ) :=
        lift_to_both0 zero_3021 in
      letb '(x_3013, y_3014) :=
        if ed_is_square (lift_to_both0 gx1_3023) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset (
            [x1_3012_loc ; x_3013_loc ; y_3014_loc])) (L2 := CEfset (
            [x1_3012_loc ; x_3013_loc ; y_3014_loc])) (I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
          letbm x_3013 loc( x_3013_loc ) := lift_to_both0 x1_3012 in
          letbm y_3014 loc( y_3014_loc ) :=
            option_unwrap (sqrt (lift_to_both0 gx1_3023)) in
          letb '(y_3014) :=
            if negb (sgn0_m_eq_1 (lift_to_both0 y_3014)) :bool_ChoiceEquality
            then lift_scope (L1 := CEfset (
                [x1_3012_loc ; x_3013_loc ; y_3014_loc])) (L2 := CEfset (
                [x1_3012_loc ; x_3013_loc ; y_3014_loc])) (I1 := [interface]) (
              I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
              letbm y_3014 loc( y_3014_loc ) :=
                (lift_to_both0 zero_3021) -% (lift_to_both0 y_3014) in
              lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                lift_to_both0 y_3014)
              )
            else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 y_3014)
             in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
              lift_to_both0 x_3013,
              lift_to_both0 y_3014
            ))
          )
        else  lift_scope (L1 := CEfset (
            [x1_3012_loc ; x_3013_loc ; y_3014_loc])) (L2 := CEfset (
            [x1_3012_loc ; x_3013_loc ; y_3014_loc])) (I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
          letbm x_3013 loc( x_3013_loc ) := lift_to_both0 x2_3024 in
          letbm y_3014 loc( y_3014_loc ) :=
            option_unwrap (sqrt (lift_to_both0 gx2_3025)) in
          letb '(y_3014) :=
            if sgn0_m_eq_1 (lift_to_both0 y_3014) :bool_ChoiceEquality
            then lift_scope (L1 := CEfset (
                [x1_3012_loc ; x_3013_loc ; y_3014_loc])) (L2 := CEfset (
                [x1_3012_loc ; x_3013_loc ; y_3014_loc])) (I1 := [interface]) (
              I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
              letbm y_3014 loc( y_3014_loc ) :=
                (lift_to_both0 zero_3021) -% (lift_to_both0 y_3014) in
              lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                lift_to_both0 y_3014)
              )
            else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 y_3014)
             in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
              lift_to_both0 x_3013,
              lift_to_both0 y_3014
            ))
          ) in
      letb s_3026 : ed25519_field_element_t := lift_to_both0 x_3013 in
      letb t_3027 : ed25519_field_element_t := lift_to_both0 y_3014 in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 s_3026,
          lift_to_both0 t_3027,
          lift_to_both0 one_3020,
          (lift_to_both0 s_3026) *% (lift_to_both0 t_3027)
        ))
      ) : both (CEfset ([x1_3012_loc ; x_3013_loc ; y_3014_loc])) [interface] (
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
  3055.
Program Definition map_to_curve_elligator2_straight (
    u_3033 : ed25519_field_element_t)
  : both (fset.fset0) [interface] (ed_point_t) :=
  ((letb j_3029 : ed25519_field_element_t :=
        nat_mod_from_literal (_) (lift_to_both0 j_v) in
      letb z_3030 : ed25519_field_element_t :=
        nat_mod_from_literal (_) (lift_to_both0 z_v) in
      letb one_3031 : ed25519_field_element_t := nat_mod_one  in
      letb zero_3032 : ed25519_field_element_t := nat_mod_zero  in
      letb tv1_3034 : ed25519_field_element_t :=
        (lift_to_both0 u_3033) *% (lift_to_both0 u_3033) in
      letb tv1_3035 : ed25519_field_element_t :=
        (lift_to_both0 z_3030) *% (lift_to_both0 tv1_3034) in
      letb e1_3036 : bool_ChoiceEquality :=
        (lift_to_both0 tv1_3035) =.? ((lift_to_both0 zero_3032) -% (
            lift_to_both0 one_3031)) in
      letb tv1_3037 : ed25519_field_element_t :=
        cmov (lift_to_both0 tv1_3035) (lift_to_both0 zero_3032) (
          lift_to_both0 e1_3036) in
      letb x1_3038 : ed25519_field_element_t :=
        (lift_to_both0 tv1_3037) +% (lift_to_both0 one_3031) in
      letb x1_3039 : ed25519_field_element_t :=
        nat_mod_inv (lift_to_both0 x1_3038) in
      letb x1_3040 : ed25519_field_element_t :=
        ((lift_to_both0 zero_3032) -% (lift_to_both0 j_3029)) *% (
          lift_to_both0 x1_3039) in
      letb gx1_3041 : ed25519_field_element_t :=
        (lift_to_both0 x1_3040) +% (lift_to_both0 j_3029) in
      letb gx1_3042 : ed25519_field_element_t :=
        (lift_to_both0 gx1_3041) *% (lift_to_both0 x1_3040) in
      letb gx1_3043 : ed25519_field_element_t :=
        (lift_to_both0 gx1_3042) +% (lift_to_both0 one_3031) in
      letb gx1_3044 : ed25519_field_element_t :=
        (lift_to_both0 gx1_3043) *% (lift_to_both0 x1_3040) in
      letb x2_3045 : ed25519_field_element_t :=
        ((lift_to_both0 zero_3032) -% (lift_to_both0 x1_3040)) -% (
          lift_to_both0 j_3029) in
      letb gx2_3046 : ed25519_field_element_t :=
        (lift_to_both0 tv1_3037) *% (lift_to_both0 gx1_3044) in
      letb e2_3047 : bool_ChoiceEquality :=
        ed_is_square (lift_to_both0 gx1_3044) in
      letb x_3048 : ed25519_field_element_t :=
        cmov (lift_to_both0 x2_3045) (lift_to_both0 x1_3040) (
          lift_to_both0 e2_3047) in
      letb y2_3049 : ed25519_field_element_t :=
        cmov (lift_to_both0 gx2_3046) (lift_to_both0 gx1_3044) (
          lift_to_both0 e2_3047) in
      letb y_3050 : ed25519_field_element_t :=
        option_unwrap (sqrt (lift_to_both0 y2_3049)) in
      letb e3_3051 : bool_ChoiceEquality :=
        sgn0_m_eq_1 (lift_to_both0 y_3050) in
      letb y_3052 : ed25519_field_element_t :=
        cmov (lift_to_both0 y_3050) ((lift_to_both0 zero_3032) -% (
            lift_to_both0 y_3050)) (xor (lift_to_both0 e2_3047) (
            lift_to_both0 e3_3051)) in
      letb s_3053 : ed25519_field_element_t := lift_to_both0 x_3048 in
      letb t_3054 : ed25519_field_element_t := lift_to_both0 y_3052 in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 s_3053,
          lift_to_both0 t_3054,
          lift_to_both0 one_3031,
          (lift_to_both0 s_3053) *% (lift_to_both0 t_3054)
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
  3103.
Program Definition map_to_curve_elligator2_curve25519 (
    u_3064 : ed25519_field_element_t)
  : both (fset.fset0) [interface] (ed_point_t) :=
  ((letb j_3056 : ed25519_field_element_t :=
        nat_mod_from_literal (_) (lift_to_both0 j_v) in
      letb zero_3057 : ed25519_field_element_t := nat_mod_zero  in
      letb one_3058 : ed25519_field_element_t := nat_mod_one  in
      letb two_3059 : ed25519_field_element_t := nat_mod_two  in
      letb c1_3060 : ed25519_field_element_t :=
        nat_mod_from_byte_seq_be (array_to_be_bytes (lift_to_both0 p_3_8_v)) in
      letb c2_3061 : ed25519_field_element_t :=
        nat_mod_pow_self (lift_to_both0 two_3059) (lift_to_both0 c1_3060) in
      letb c3_3062 : ed25519_field_element_t :=
        option_unwrap (sqrt ((lift_to_both0 zero_3057) -% (
              lift_to_both0 one_3058))) in
      letb c4_3063 : ed25519_field_element_t :=
        nat_mod_from_byte_seq_be (array_to_be_bytes (lift_to_both0 p_5_8_v)) in
      letb tv1_3065 : ed25519_field_element_t :=
        (lift_to_both0 u_3064) *% (lift_to_both0 u_3064) in
      letb tv1_3066 : ed25519_field_element_t :=
        (lift_to_both0 two_3059) *% (lift_to_both0 tv1_3065) in
      letb xd_3067 : ed25519_field_element_t :=
        (lift_to_both0 tv1_3066) +% (lift_to_both0 one_3058) in
      letb x1n_3068 : ed25519_field_element_t :=
        (lift_to_both0 zero_3057) -% (lift_to_both0 j_3056) in
      letb tv2_3069 : ed25519_field_element_t :=
        (lift_to_both0 xd_3067) *% (lift_to_both0 xd_3067) in
      letb gxd_3070 : ed25519_field_element_t :=
        (lift_to_both0 tv2_3069) *% (lift_to_both0 xd_3067) in
      letb gx1_3071 : ed25519_field_element_t :=
        (lift_to_both0 j_3056) *% (lift_to_both0 tv1_3066) in
      letb gx1_3072 : ed25519_field_element_t :=
        (lift_to_both0 gx1_3071) *% (lift_to_both0 x1n_3068) in
      letb gx1_3073 : ed25519_field_element_t :=
        (lift_to_both0 gx1_3072) +% (lift_to_both0 tv2_3069) in
      letb gx1_3074 : ed25519_field_element_t :=
        (lift_to_both0 gx1_3073) *% (lift_to_both0 x1n_3068) in
      letb tv3_3075 : ed25519_field_element_t :=
        (lift_to_both0 gxd_3070) *% (lift_to_both0 gxd_3070) in
      letb tv2_3076 : ed25519_field_element_t :=
        (lift_to_both0 tv3_3075) *% (lift_to_both0 tv3_3075) in
      letb tv3_3077 : ed25519_field_element_t :=
        (lift_to_both0 tv3_3075) *% (lift_to_both0 gxd_3070) in
      letb tv3_3078 : ed25519_field_element_t :=
        (lift_to_both0 tv3_3077) *% (lift_to_both0 gx1_3074) in
      letb tv2_3079 : ed25519_field_element_t :=
        (lift_to_both0 tv2_3076) *% (lift_to_both0 tv3_3078) in
      letb y11_3080 : ed25519_field_element_t :=
        nat_mod_pow_self (lift_to_both0 tv2_3079) (lift_to_both0 c4_3063) in
      letb y11_3081 : ed25519_field_element_t :=
        (lift_to_both0 y11_3080) *% (lift_to_both0 tv3_3078) in
      letb y12_3082 : ed25519_field_element_t :=
        (lift_to_both0 y11_3081) *% (lift_to_both0 c3_3062) in
      letb tv2_3083 : ed25519_field_element_t :=
        (lift_to_both0 y11_3081) *% (lift_to_both0 y11_3081) in
      letb tv2_3084 : ed25519_field_element_t :=
        (lift_to_both0 tv2_3083) *% (lift_to_both0 gxd_3070) in
      letb e1_3085 : bool_ChoiceEquality :=
        (lift_to_both0 tv2_3084) =.? (lift_to_both0 gx1_3074) in
      letb y1_3086 : ed25519_field_element_t :=
        cmov (lift_to_both0 y12_3082) (lift_to_both0 y11_3081) (
          lift_to_both0 e1_3085) in
      letb x2n_3087 : ed25519_field_element_t :=
        (lift_to_both0 x1n_3068) *% (lift_to_both0 tv1_3066) in
      letb y21_3088 : ed25519_field_element_t :=
        (lift_to_both0 y11_3081) *% (lift_to_both0 u_3064) in
      letb y21_3089 : ed25519_field_element_t :=
        (lift_to_both0 y21_3088) *% (lift_to_both0 c2_3061) in
      letb y22_3090 : ed25519_field_element_t :=
        (lift_to_both0 y21_3089) *% (lift_to_both0 c3_3062) in
      letb gx2_3091 : ed25519_field_element_t :=
        (lift_to_both0 gx1_3074) *% (lift_to_both0 tv1_3066) in
      letb tv2_3092 : ed25519_field_element_t :=
        (lift_to_both0 y21_3089) *% (lift_to_both0 y21_3089) in
      letb tv2_3093 : ed25519_field_element_t :=
        (lift_to_both0 tv2_3092) *% (lift_to_both0 gxd_3070) in
      letb e2_3094 : bool_ChoiceEquality :=
        (lift_to_both0 tv2_3093) =.? (lift_to_both0 gx2_3091) in
      letb y2_3095 : ed25519_field_element_t :=
        cmov (lift_to_both0 y22_3090) (lift_to_both0 y21_3089) (
          lift_to_both0 e2_3094) in
      letb tv2_3096 : ed25519_field_element_t :=
        (lift_to_both0 y1_3086) *% (lift_to_both0 y1_3086) in
      letb tv2_3097 : ed25519_field_element_t :=
        (lift_to_both0 tv2_3096) *% (lift_to_both0 gxd_3070) in
      letb e3_3098 : bool_ChoiceEquality :=
        (lift_to_both0 tv2_3097) =.? (lift_to_both0 gx1_3074) in
      letb xn_3099 : ed25519_field_element_t :=
        cmov (lift_to_both0 x2n_3087) (lift_to_both0 x1n_3068) (
          lift_to_both0 e3_3098) in
      letb y_3100 : ed25519_field_element_t :=
        cmov (lift_to_both0 y2_3095) (lift_to_both0 y1_3086) (
          lift_to_both0 e3_3098) in
      letb e4_3101 : bool_ChoiceEquality :=
        sgn0_m_eq_1 (lift_to_both0 y_3100) in
      letb y_3102 : ed25519_field_element_t :=
        cmov (lift_to_both0 y_3100) ((lift_to_both0 zero_3057) -% (
            lift_to_both0 y_3100)) (xor (lift_to_both0 e3_3098) (
            lift_to_both0 e4_3101)) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 xn_3099,
          lift_to_both0 xd_3067,
          lift_to_both0 y_3102,
          lift_to_both0 one_3058
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
  3127.
Program Definition map_to_curve_elligator2_edwards25519 (
    u_3109 : ed25519_field_element_t)
  : both (fset.fset0) [interface] (ed_point_t) :=
  ((letb j_3104 : ed25519_field_element_t :=
        nat_mod_from_literal (_) (lift_to_both0 j_v) in
      letb zero_3105 : ed25519_field_element_t := nat_mod_zero  in
      letb one_3106 : ed25519_field_element_t := nat_mod_one  in
      letb two_3107 : ed25519_field_element_t := nat_mod_two  in
      letb c1_3108 : ed25519_field_element_t :=
        option_unwrap (sqrt ((lift_to_both0 zero_3105) -% ((
                lift_to_both0 j_3104) +% (lift_to_both0 two_3107)))) in
      letb '(xmn_3110, xmd_3111, ymn_3112, ymd_3113) : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        map_to_curve_elligator2_curve25519 (lift_to_both0 u_3109) in
      letb xn_3114 : ed25519_field_element_t :=
        (lift_to_both0 xmn_3110) *% (lift_to_both0 ymd_3113) in
      letb xn_3115 : ed25519_field_element_t :=
        (lift_to_both0 xn_3114) *% (lift_to_both0 c1_3108) in
      letb xd_3116 : ed25519_field_element_t :=
        (lift_to_both0 xmd_3111) *% (lift_to_both0 ymn_3112) in
      letb yn_3117 : ed25519_field_element_t :=
        (lift_to_both0 xmn_3110) -% (lift_to_both0 xmd_3111) in
      letb yd_3118 : ed25519_field_element_t :=
        (lift_to_both0 xmn_3110) +% (lift_to_both0 xmd_3111) in
      letb tv1_3119 : ed25519_field_element_t :=
        (lift_to_both0 xd_3116) *% (lift_to_both0 yd_3118) in
      letb e_3120 : bool_ChoiceEquality :=
        (lift_to_both0 tv1_3119) =.? (lift_to_both0 zero_3105) in
      letb xn_3121 : ed25519_field_element_t :=
        cmov (lift_to_both0 xn_3115) (lift_to_both0 zero_3105) (
          lift_to_both0 e_3120) in
      letb xd_3122 : ed25519_field_element_t :=
        cmov (lift_to_both0 xd_3116) (lift_to_both0 one_3106) (
          lift_to_both0 e_3120) in
      letb yn_3123 : ed25519_field_element_t :=
        cmov (lift_to_both0 yn_3117) (lift_to_both0 one_3106) (
          lift_to_both0 e_3120) in
      letb yd_3124 : ed25519_field_element_t :=
        cmov (lift_to_both0 yd_3118) (lift_to_both0 one_3106) (
          lift_to_both0 e_3120) in
      letb x_3125 : ed25519_field_element_t :=
        (lift_to_both0 xn_3121) *% (nat_mod_inv (lift_to_both0 xd_3122)) in
      letb y_3126 : ed25519_field_element_t :=
        (lift_to_both0 yn_3123) *% (nat_mod_inv (lift_to_both0 yd_3124)) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 x_3125,
          lift_to_both0 y_3126,
          lift_to_both0 one_3106,
          (lift_to_both0 x_3125) *% (lift_to_both0 y_3126)
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
  3130.
Program Definition map_to_curve_elligator2_edwards (
    u_3128 : ed25519_field_element_t)
  : both (CEfset ([x1_3012_loc ; x_3013_loc ; y_3014_loc])) [interface] (
    ed_point_t) :=
  ((letb st_3129 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        map_to_curve_elligator2 (lift_to_both0 u_3128) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        curve25519_to_edwards25519 (lift_to_both0 st_3129))
      ) : both (CEfset ([x1_3012_loc ; x_3013_loc ; y_3014_loc])) [interface] (
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
  3135.
Program Definition ed_encode_to_curve (msg_3131 : byte_seq) (
    dst_3132 : byte_seq)
  : both (CEfset (
      [result_2947_loc ; l_i_b_str_2948_loc ; b_i_2949_loc ; uniform_bytes_2950_loc ; output_2966_loc ; x1_3012_loc ; x_3013_loc ; y_3014_loc])) [interface] (
    ed_point_result_t) :=
  ((letbnd(_) u_3133 : seq ed25519_field_element_t :=
        ed_hash_to_field (lift_to_both0 msg_3131) (lift_to_both0 dst_3132) (
          lift_to_both0 (usize 1)) in
      letb q_3134 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        map_to_curve_elligator2_edwards (seq_index (u_3133) (lift_to_both0 (
              usize 0))) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (@Ok ed_point_t error_t (
          ed_clear_cofactor (lift_to_both0 q_3134)))
      ) : both (CEfset (
        [result_2947_loc ; l_i_b_str_2948_loc ; b_i_2949_loc ; uniform_bytes_2950_loc ; output_2966_loc ; x1_3012_loc ; x_3013_loc ; y_3014_loc])) [interface] (
      ed_point_result_t)).
Fail Next Obligation.

