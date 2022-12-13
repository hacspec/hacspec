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


Require Import Hacspec_Sha256.

Definition bit_size_v : int32 :=
  @repr U32 2048.

Definition byte_size_v : int32 :=
  ((@repr U32 2048) ./ (@repr U32 8)).

Definition hlen_v : uint_size :=
  usize 32.

Definition rsa_int_t := nat_mod pow2 2048.

Definition error_t : ChoiceEquality :=
  unit_ChoiceEquality '+ unit_ChoiceEquality '+ unit_ChoiceEquality '+ unit_ChoiceEquality.
Definition InvalidLength : error_t :=
  inl (inl (inl tt)).
Definition MessageTooLarge : error_t :=
  inl (inl (inr tt)).
Definition DecryptionFailed : error_t :=
  inl (inr tt).
Definition VerificationFailed : error_t :=
  inr tt.

Notation "'pk_t'" := ((rsa_int_t '× rsa_int_t)) : hacspec_scope.

Notation "'sk_t'" := ((rsa_int_t '× rsa_int_t)) : hacspec_scope.

Notation "'key_pair_t'" := ((pk_t '× sk_t)) : hacspec_scope.

Notation "'byte_seq_result_t'" := ((result error_t byte_seq)) : hacspec_scope.

Notation "'rsa_int_result_t'" := ((result error_t rsa_int_t)) : hacspec_scope.


Notation "'rsaep_inp'" :=(
  pk_t '× rsa_int_t : choice_type) (in custom pack_type at level 2).
Notation "'rsaep_inp'" :=(pk_t '× rsa_int_t : ChoiceEquality) (at level 2).
Notation "'rsaep_out'" :=(
  rsa_int_result_t : choice_type) (in custom pack_type at level 2).
Notation "'rsaep_out'" :=(rsa_int_result_t : ChoiceEquality) (at level 2).
Definition RSAEP : nat :=
  3090.
Program Definition rsaep (pk_3086 : pk_t) (m_3089 : rsa_int_t)
  : both (fset.fset0) [interface] (rsa_int_result_t) :=
  ((letb '(n_3087, e_3088) : (rsa_int_t '× rsa_int_t) :=
        lift_to_both0 pk_3086 in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        if is_pure (I := [interface]) ((lift_to_both0 m_3089) >.? ((
              lift_to_both0 n_3087) -% (nat_mod_one )))
        then @Err rsa_int_t error_t (MessageTooLarge)
        else @Ok rsa_int_t error_t (nat_mod_pow_mod (lift_to_both0 m_3089) (
            lift_to_both0 e_3088) (lift_to_both0 n_3087)))
      ) : both (fset.fset0) [interface] (rsa_int_result_t)).
Fail Next Obligation.


Notation "'rsadp_inp'" :=(
  sk_t '× rsa_int_t : choice_type) (in custom pack_type at level 2).
Notation "'rsadp_inp'" :=(sk_t '× rsa_int_t : ChoiceEquality) (at level 2).
Notation "'rsadp_out'" :=(
  rsa_int_result_t : choice_type) (in custom pack_type at level 2).
Notation "'rsadp_out'" :=(rsa_int_result_t : ChoiceEquality) (at level 2).
Definition RSADP : nat :=
  3095.
Program Definition rsadp (sk_3091 : sk_t) (c_3094 : rsa_int_t)
  : both (fset.fset0) [interface] (rsa_int_result_t) :=
  ((letb '(n_3092, d_3093) : (rsa_int_t '× rsa_int_t) :=
        lift_to_both0 sk_3091 in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        if is_pure (I := [interface]) ((lift_to_both0 c_3094) >.? ((
              lift_to_both0 n_3092) -% (nat_mod_one )))
        then @Err rsa_int_t error_t (MessageTooLarge)
        else @Ok rsa_int_t error_t (nat_mod_pow_mod (lift_to_both0 c_3094) (
            lift_to_both0 d_3093) (lift_to_both0 n_3092)))
      ) : both (fset.fset0) [interface] (rsa_int_result_t)).
Fail Next Obligation.


Notation "'rsasp1_inp'" :=(
  sk_t '× rsa_int_t : choice_type) (in custom pack_type at level 2).
Notation "'rsasp1_inp'" :=(sk_t '× rsa_int_t : ChoiceEquality) (at level 2).
Notation "'rsasp1_out'" :=(
  rsa_int_result_t : choice_type) (in custom pack_type at level 2).
Notation "'rsasp1_out'" :=(rsa_int_result_t : ChoiceEquality) (at level 2).
Definition RSASP1 : nat :=
  3100.
Program Definition rsasp1 (sk_3096 : sk_t) (m_3099 : rsa_int_t)
  : both (fset.fset0) [interface] (rsa_int_result_t) :=
  ((letb '(n_3097, d_3098) : (rsa_int_t '× rsa_int_t) :=
        lift_to_both0 sk_3096 in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        if is_pure (I := [interface]) ((lift_to_both0 m_3099) >.? ((
              lift_to_both0 n_3097) -% (nat_mod_one )))
        then @Err rsa_int_t error_t (MessageTooLarge)
        else @Ok rsa_int_t error_t (nat_mod_pow_mod (lift_to_both0 m_3099) (
            lift_to_both0 d_3098) (lift_to_both0 n_3097)))
      ) : both (fset.fset0) [interface] (rsa_int_result_t)).
Fail Next Obligation.


Notation "'rsavp1_inp'" :=(
  pk_t '× rsa_int_t : choice_type) (in custom pack_type at level 2).
Notation "'rsavp1_inp'" :=(pk_t '× rsa_int_t : ChoiceEquality) (at level 2).
Notation "'rsavp1_out'" :=(
  rsa_int_result_t : choice_type) (in custom pack_type at level 2).
Notation "'rsavp1_out'" :=(rsa_int_result_t : ChoiceEquality) (at level 2).
Definition RSAVP1 : nat :=
  3105.
Program Definition rsavp1 (pk_3101 : pk_t) (s_3104 : rsa_int_t)
  : both (fset.fset0) [interface] (rsa_int_result_t) :=
  ((letb '(n_3102, e_3103) : (rsa_int_t '× rsa_int_t) :=
        lift_to_both0 pk_3101 in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        if is_pure (I := [interface]) ((lift_to_both0 s_3104) >.? ((
              lift_to_both0 n_3102) -% (nat_mod_one )))
        then @Err rsa_int_t error_t (MessageTooLarge)
        else @Ok rsa_int_t error_t (nat_mod_pow_mod (lift_to_both0 s_3104) (
            lift_to_both0 e_3103) (lift_to_both0 n_3102)))
      ) : both (fset.fset0) [interface] (rsa_int_result_t)).
Fail Next Obligation.


Notation "'i2osp_inp'" :=(
  rsa_int_t '× int32 : choice_type) (in custom pack_type at level 2).
Notation "'i2osp_inp'" :=(rsa_int_t '× int32 : ChoiceEquality) (at level 2).
Notation "'i2osp_out'" :=(
  byte_seq_result_t : choice_type) (in custom pack_type at level 2).
Notation "'i2osp_out'" :=(byte_seq_result_t : ChoiceEquality) (at level 2).
Definition I2OSP : nat :=
  3108.
Program Definition i2osp (x_3106 : rsa_int_t) (x_len_3107 : int32)
  : both (fset.fset0) [interface] (byte_seq_result_t) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        if is_pure (I := [interface]) (((lift_to_both0 x_3106) >=.? (
              nat_mod_exp (nat_mod_from_literal (0x) (lift_to_both0 (
                    @repr U128 256))) (lift_to_both0 x_len_3107))) && ((
              lift_to_both0 x_len_3107) !=.? (lift_to_both0 byte_size_v)))
        then @Err byte_seq error_t (InvalidLength)
        else @Ok byte_seq error_t (seq_slice (nat_mod_to_byte_seq_be (
              lift_to_both0 x_3106)) (@cast _ uint32 _ ((
                lift_to_both0 byte_size_v) .- (lift_to_both0 x_len_3107))) (
            @cast _ uint32 _ (lift_to_both0 x_len_3107))))
      ) : both (fset.fset0) [interface] (byte_seq_result_t)).
Fail Next Obligation.


Notation "'os2ip_inp'" :=(
  byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'os2ip_inp'" :=(byte_seq : ChoiceEquality) (at level 2).
Notation "'os2ip_out'" :=(
  rsa_int_t : choice_type) (in custom pack_type at level 2).
Notation "'os2ip_out'" :=(rsa_int_t : ChoiceEquality) (at level 2).
Definition OS2IP : nat :=
  3110.
Program Definition os2ip (x_3109 : byte_seq)
  : both (fset.fset0) [interface] (rsa_int_t) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (nat_mod_from_byte_seq_be (
          lift_to_both0 x_3109))
      ) : both (fset.fset0) [interface] (rsa_int_t)).
Fail Next Obligation.

Definition result_3111_loc : ChoiceEqualityLocation :=
  ((result (error_t) (byte_seq)) ; 3113%nat).
Definition t_3112_loc : ChoiceEqualityLocation :=
  (seq uint8 ; 3114%nat).
Notation "'mgf1_inp'" :=(
  byte_seq '× uint_size : choice_type) (in custom pack_type at level 2).
Notation "'mgf1_inp'" :=(byte_seq '× uint_size : ChoiceEquality) (at level 2).
Notation "'mgf1_out'" :=(
  byte_seq_result_t : choice_type) (in custom pack_type at level 2).
Notation "'mgf1_out'" :=(byte_seq_result_t : ChoiceEquality) (at level 2).
Definition MGF1 : nat :=
  3119.
Program Definition mgf1 (mgf_seed_3118 : byte_seq) (mask_len_3115 : uint_size)
  : both (CEfset ([result_3111_loc ; t_3112_loc])) [interface] (
    byte_seq_result_t) :=
  ((letbm result_3111 : (result (error_t) (byte_seq)) loc( result_3111_loc ) :=
        @Err byte_seq error_t (InvalidLength) in
      letbnd(ChoiceEqualityMonad.result_bind_both error_t) '(result_3111) :=
        if (lift_to_both0 mask_len_3115) <.? ((lift_to_both0 (usize 2)) .^ ((
              lift_to_both0 (usize 32)) .* (
              lift_to_both0 hlen_v))) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset ([result_3111_loc ; t_3112_loc])) (
          L2 := CEfset ([result_3111_loc ; t_3112_loc])) (I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
          letbm t_3112 : seq uint8 loc( t_3112_loc ) :=
            seq_new_ (default : uint8) (lift_to_both0 (usize 0)) in
          letbnd(ChoiceEqualityMonad.result_bind_both error_t) t_3112 :=
            foldi_bind_both' (lift_to_both0 (usize 0)) (((
                    lift_to_both0 mask_len_3115) .+ (lift_to_both0 (
                      usize 32))) ./ (lift_to_both0 (usize 32))) t_3112 (L := (
                  CEfset ([result_3111_loc ; t_3112_loc]))) (I := [interface]) (
                fun i_3116 t_3112 =>
                letbnd(_) x_3117 : byte_seq :=
                  i2osp (nat_mod_from_literal (0x) (pub_u128 (is_pure (
                          lift_to_both0 i_3116)))) (lift_to_both0 (
                      @repr U32 4)) in
                letbm t_3112 loc( t_3112_loc ) :=
                  seq_concat (lift_to_both0 t_3112) (array_to_seq (sha256 (
                      seq_concat (lift_to_both0 mgf_seed_3118) (
                        lift_to_both0 x_3117)))) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (@Ok (seq uint8
                  ) error_t (lift_to_both0 t_3112))
                ) in
          letbm result_3111 loc( result_3111_loc ) :=
            @Ok byte_seq error_t (seq_slice (lift_to_both0 t_3112) (
                lift_to_both0 (usize 0)) (lift_to_both0 mask_len_3115)) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (@Ok (
              (result (error_t) (byte_seq))
            ) error_t (lift_to_both0 result_3111))
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (@Ok (
            (result (error_t) (byte_seq))
          ) error_t (lift_to_both0 result_3111))
         in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        lift_to_both0 result_3111)
      ) : both (CEfset ([result_3111_loc ; t_3112_loc])) [interface] (
      byte_seq_result_t)).
Fail Next Obligation.

