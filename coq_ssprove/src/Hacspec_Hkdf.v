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
Require Import Hacspec_Hmac.



Require Import Hacspec_Sha256.

Definition hash_len_v : uint_size :=
  ((usize 256) ./ (usize 8)).

Definition hkdf_error_t : ChoiceEquality :=
  unit_ChoiceEquality.
Definition InvalidOutputLength : hkdf_error_t :=
   tt.

Notation "'hkdf_byte_seq_result_t'" := ((
  result hkdf_error_t byte_seq)) : hacspec_scope.

Definition salt_or_zero_898_loc : ChoiceEqualityLocation :=
  (seq uint8 ; 899%nat).
Notation "'extract_inp'" :=(
  byte_seq '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'extract_inp'" :=(
  byte_seq '× byte_seq : ChoiceEquality) (at level 2).
Notation "'extract_out'" :=(
  prk_t : choice_type) (in custom pack_type at level 2).
Notation "'extract_out'" :=(prk_t : ChoiceEquality) (at level 2).
Definition EXTRACT : nat :=
  902.
Program Definition extract (salt_900 : byte_seq) (ikm_901 : byte_seq)
  : both (CEfset ([salt_or_zero_898_loc])) [interface] (prk_t) :=
  ((letbm salt_or_zero_898 : seq uint8 loc( salt_or_zero_898_loc ) :=
        seq_new_ (default : uint8) (lift_to_both0 hash_len_v) in
      letb '(salt_or_zero_898) :=
        if (seq_len (lift_to_both0 salt_900)) >.? (lift_to_both0 (
            usize 0)) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset ([salt_or_zero_898_loc])) (L2 := CEfset (
            [salt_or_zero_898_loc])) (I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
          letbm salt_or_zero_898 loc( salt_or_zero_898_loc ) :=
            seq_from_seq (lift_to_both0 salt_900) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 salt_or_zero_898)
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          lift_to_both0 salt_or_zero_898)
         in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (array_from_seq (_) (
          array_to_seq (hmac (lift_to_both0 salt_or_zero_898) (
            lift_to_both0 ikm_901))))
      ) : both (CEfset ([salt_or_zero_898_loc])) [interface] (prk_t)).
Fail Next Obligation.

Definition out_903_loc : ChoiceEqualityLocation :=
  (seq uint8 ; 904%nat).
Notation "'build_hmac_txt_inp'" :=(
  byte_seq '× byte_seq '× uint8 : choice_type) (in custom pack_type at level 2).
Notation "'build_hmac_txt_inp'" :=(
  byte_seq '× byte_seq '× uint8 : ChoiceEquality) (at level 2).
Notation "'build_hmac_txt_out'" :=(
  byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'build_hmac_txt_out'" :=(byte_seq : ChoiceEquality) (at level 2).
Definition BUILD_HMAC_TXT : nat :=
  908.
Program Definition build_hmac_txt (t_905 : byte_seq) (info_906 : byte_seq) (
    iteration_907 : uint8)
  : both (CEfset ([out_903_loc])) [interface] (byte_seq) :=
  ((letbm out_903 : seq uint8 loc( out_903_loc ) :=
        seq_new_ (default : uint8) (((seq_len (lift_to_both0 t_905)) .+ (
              seq_len (lift_to_both0 info_906))) .+ (lift_to_both0 (
              usize 1))) in
      letbm out_903 loc( out_903_loc ) :=
        seq_update (lift_to_both0 out_903) (lift_to_both0 (usize 0)) (
          lift_to_both0 t_905) in
      letbm out_903 loc( out_903_loc ) :=
        seq_update (lift_to_both0 out_903) (seq_len (lift_to_both0 t_905)) (
          lift_to_both0 info_906) in
      letb out_903 : seq uint8 :=
        seq_upd out_903 ((seq_len (lift_to_both0 t_905)) .+ (seq_len (
              lift_to_both0 info_906))) (is_pure (
            lift_to_both0 iteration_907)) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 out_903)
      ) : both (CEfset ([out_903_loc])) [interface] (byte_seq)).
Fail Next Obligation.

Definition q_909_loc : ChoiceEqualityLocation :=
  (uint_size ; 910%nat).
Notation "'div_ceil_inp'" :=(
  uint_size '× uint_size : choice_type) (in custom pack_type at level 2).
Notation "'div_ceil_inp'" :=(
  uint_size '× uint_size : ChoiceEquality) (at level 2).
Notation "'div_ceil_out'" :=(
  uint_size : choice_type) (in custom pack_type at level 2).
Notation "'div_ceil_out'" :=(uint_size : ChoiceEquality) (at level 2).
Definition DIV_CEIL : nat :=
  913.
Program Definition div_ceil (a_911 : uint_size) (b_912 : uint_size)
  : both (CEfset ([q_909_loc])) [interface] (uint_size) :=
  ((letbm q_909 : uint_size loc( q_909_loc ) :=
        (lift_to_both0 a_911) ./ (lift_to_both0 b_912) in
      letb '(q_909) :=
        if ((lift_to_both0 a_911) %% (lift_to_both0 b_912)) !=.? (
          lift_to_both0 (usize 0)) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset ([q_909_loc])) (L2 := CEfset (
            [q_909_loc])) (I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
          letbm q_909 loc( q_909_loc ) :=
            (lift_to_both0 q_909) .+ (lift_to_both0 (usize 1)) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 q_909)
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          lift_to_both0 q_909)
         in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 q_909)
      ) : both (CEfset ([q_909_loc])) [interface] (uint_size)).
Fail Next Obligation.


Notation "'check_output_limit_inp'" :=(
  uint_size : choice_type) (in custom pack_type at level 2).
Notation "'check_output_limit_inp'" :=(uint_size : ChoiceEquality) (at level 2).
Notation "'check_output_limit_out'" :=((result (hkdf_error_t) (
      uint_size)) : choice_type) (in custom pack_type at level 2).
Notation "'check_output_limit_out'" :=((result (hkdf_error_t) (
      uint_size)) : ChoiceEquality) (at level 2).
Definition CHECK_OUTPUT_LIMIT : nat :=
  916.
Program Definition check_output_limit (l_914 : uint_size)
  : both (CEfset ([q_909_loc])) [interface] ((result (hkdf_error_t) (
        uint_size))) :=
  ((letb n_915 : uint_size :=
        div_ceil (lift_to_both0 l_914) (lift_to_both0 hash_len_v) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        if is_pure (I := [interface]) ((lift_to_both0 n_915) <=.? (
            lift_to_both0 (usize 255)))
        then @Ok uint_size hkdf_error_t (lift_to_both0 n_915)
        else @Err uint_size hkdf_error_t (InvalidOutputLength))
      ) : both (CEfset ([q_909_loc])) [interface] ((result (hkdf_error_t) (
          uint_size)))).
Fail Next Obligation.

Definition t_i_917_loc : ChoiceEqualityLocation :=
  (prk_t ; 919%nat).
Definition t_918_loc : ChoiceEqualityLocation :=
  (seq uint8 ; 920%nat).
Notation "'expand_inp'" :=(
  byte_seq '× byte_seq '× uint_size : choice_type) (in custom pack_type at level 2).
Notation "'expand_inp'" :=(
  byte_seq '× byte_seq '× uint_size : ChoiceEquality) (at level 2).
Notation "'expand_out'" :=(
  hkdf_byte_seq_result_t : choice_type) (in custom pack_type at level 2).
Notation "'expand_out'" :=(
  hkdf_byte_seq_result_t : ChoiceEquality) (at level 2).
Definition EXPAND : nat :=
  927.
Program Definition expand (prk_926 : byte_seq) (info_924 : byte_seq) (
    l_921 : uint_size)
  : both (CEfset (
      [out_903_loc ; q_909_loc ; t_i_917_loc ; t_918_loc])) [interface] (
    hkdf_byte_seq_result_t) :=
  ((letbnd(_) n_922 : uint_size := check_output_limit (lift_to_both0 l_921) in
      letbm t_i_917 : prk_t loc( t_i_917_loc ) :=
        array_new_ (default : uint8) (_) in
      letbm t_918 : seq uint8 loc( t_918_loc ) :=
        seq_new_ (default : uint8) ((lift_to_both0 n_922) .* (
            lift_to_both0 hash_size_v)) in
      letb '(t_i_917, t_918) :=
        foldi_both' (lift_to_both0 (usize 0)) (lift_to_both0 n_922) prod_ce(
            t_i_917,
            t_918
          ) (L := (CEfset (
                [out_903_loc ; q_909_loc ; t_i_917_loc ; t_918_loc]))) (
            I := [interface]) (fun i_923 '(t_i_917, t_918) =>
            letb hmac_txt_in_925 : seq uint8 :=
              if is_pure (I := [interface]) ((lift_to_both0 i_923) =.? (
                  lift_to_both0 (usize 0)))
              then build_hmac_txt (seq_new_ (default : uint8) (lift_to_both0 (
                    usize 0))) (lift_to_both0 info_924) (secret ((pub_u8 (
                      is_pure (lift_to_both0 i_923))) .+ (lift_to_both0 (
                      @repr U8 1))))
              else build_hmac_txt (seq_from_seq (
                  array_to_seq (lift_to_both0 t_i_917))) (
                lift_to_both0 info_924) (secret ((pub_u8 (is_pure (
                        lift_to_both0 i_923))) .+ (lift_to_both0 (
                      @repr U8 1)))) in
            letbm t_i_917 loc( t_i_917_loc ) :=
              hmac (lift_to_both0 prk_926) (lift_to_both0 hmac_txt_in_925) in
            letbm t_918 loc( t_918_loc ) :=
              seq_update (lift_to_both0 t_918) ((lift_to_both0 i_923) .* (
                  array_len (lift_to_both0 t_i_917))) (
                array_to_seq (lift_to_both0 t_i_917)) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                lift_to_both0 t_i_917,
                lift_to_both0 t_918
              ))
            ) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        @Ok byte_seq hkdf_error_t (seq_slice (lift_to_both0 t_918) (
            lift_to_both0 (usize 0)) (lift_to_both0 l_921)))
      ) : both (CEfset (
        [out_903_loc ; q_909_loc ; t_i_917_loc ; t_918_loc])) [interface] (
      hkdf_byte_seq_result_t)).
Fail Next Obligation.

