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
  3140.
Program Definition rsaep (pk_3136 : pk_t) (m_3139 : rsa_int_t)
  : both (fset.fset0) [interface] (rsa_int_result_t) :=
  ((letb '(n_3137, e_3138) : (rsa_int_t '× rsa_int_t) :=
        lift_to_both0 pk_3136 in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        if is_pure (I := [interface]) ((lift_to_both0 m_3139) >.? ((
              lift_to_both0 n_3137) -% (nat_mod_one )))
        then @Err rsa_int_t error_t (MessageTooLarge)
        else @Ok rsa_int_t error_t (nat_mod_pow_mod (lift_to_both0 m_3139) (
            lift_to_both0 e_3138) (lift_to_both0 n_3137)))
      ) : both (fset.fset0) [interface] (rsa_int_result_t)).
Fail Next Obligation.


Notation "'rsadp_inp'" :=(
  sk_t '× rsa_int_t : choice_type) (in custom pack_type at level 2).
Notation "'rsadp_inp'" :=(sk_t '× rsa_int_t : ChoiceEquality) (at level 2).
Notation "'rsadp_out'" :=(
  rsa_int_result_t : choice_type) (in custom pack_type at level 2).
Notation "'rsadp_out'" :=(rsa_int_result_t : ChoiceEquality) (at level 2).
Definition RSADP : nat :=
  3145.
Program Definition rsadp (sk_3141 : sk_t) (c_3144 : rsa_int_t)
  : both (fset.fset0) [interface] (rsa_int_result_t) :=
  ((letb '(n_3142, d_3143) : (rsa_int_t '× rsa_int_t) :=
        lift_to_both0 sk_3141 in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        if is_pure (I := [interface]) ((lift_to_both0 c_3144) >.? ((
              lift_to_both0 n_3142) -% (nat_mod_one )))
        then @Err rsa_int_t error_t (MessageTooLarge)
        else @Ok rsa_int_t error_t (nat_mod_pow_mod (lift_to_both0 c_3144) (
            lift_to_both0 d_3143) (lift_to_both0 n_3142)))
      ) : both (fset.fset0) [interface] (rsa_int_result_t)).
Fail Next Obligation.


Notation "'rsasp1_inp'" :=(
  sk_t '× rsa_int_t : choice_type) (in custom pack_type at level 2).
Notation "'rsasp1_inp'" :=(sk_t '× rsa_int_t : ChoiceEquality) (at level 2).
Notation "'rsasp1_out'" :=(
  rsa_int_result_t : choice_type) (in custom pack_type at level 2).
Notation "'rsasp1_out'" :=(rsa_int_result_t : ChoiceEquality) (at level 2).
Definition RSASP1 : nat :=
  3150.
Program Definition rsasp1 (sk_3146 : sk_t) (m_3149 : rsa_int_t)
  : both (fset.fset0) [interface] (rsa_int_result_t) :=
  ((letb '(n_3147, d_3148) : (rsa_int_t '× rsa_int_t) :=
        lift_to_both0 sk_3146 in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        if is_pure (I := [interface]) ((lift_to_both0 m_3149) >.? ((
              lift_to_both0 n_3147) -% (nat_mod_one )))
        then @Err rsa_int_t error_t (MessageTooLarge)
        else @Ok rsa_int_t error_t (nat_mod_pow_mod (lift_to_both0 m_3149) (
            lift_to_both0 d_3148) (lift_to_both0 n_3147)))
      ) : both (fset.fset0) [interface] (rsa_int_result_t)).
Fail Next Obligation.


Notation "'rsavp1_inp'" :=(
  pk_t '× rsa_int_t : choice_type) (in custom pack_type at level 2).
Notation "'rsavp1_inp'" :=(pk_t '× rsa_int_t : ChoiceEquality) (at level 2).
Notation "'rsavp1_out'" :=(
  rsa_int_result_t : choice_type) (in custom pack_type at level 2).
Notation "'rsavp1_out'" :=(rsa_int_result_t : ChoiceEquality) (at level 2).
Definition RSAVP1 : nat :=
  3155.
Program Definition rsavp1 (pk_3151 : pk_t) (s_3154 : rsa_int_t)
  : both (fset.fset0) [interface] (rsa_int_result_t) :=
  ((letb '(n_3152, e_3153) : (rsa_int_t '× rsa_int_t) :=
        lift_to_both0 pk_3151 in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        if is_pure (I := [interface]) ((lift_to_both0 s_3154) >.? ((
              lift_to_both0 n_3152) -% (nat_mod_one )))
        then @Err rsa_int_t error_t (MessageTooLarge)
        else @Ok rsa_int_t error_t (nat_mod_pow_mod (lift_to_both0 s_3154) (
            lift_to_both0 e_3153) (lift_to_both0 n_3152)))
      ) : both (fset.fset0) [interface] (rsa_int_result_t)).
Fail Next Obligation.


Notation "'i2osp_inp'" :=(
  rsa_int_t '× int32 : choice_type) (in custom pack_type at level 2).
Notation "'i2osp_inp'" :=(rsa_int_t '× int32 : ChoiceEquality) (at level 2).
Notation "'i2osp_out'" :=(
  byte_seq_result_t : choice_type) (in custom pack_type at level 2).
Notation "'i2osp_out'" :=(byte_seq_result_t : ChoiceEquality) (at level 2).
Definition I2OSP : nat :=
  3158.
Program Definition i2osp (x_3156 : rsa_int_t) (x_len_3157 : int32)
  : both (fset.fset0) [interface] (byte_seq_result_t) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        if is_pure (I := [interface]) (((lift_to_both0 x_3156) >=.? (
              nat_mod_exp (nat_mod_from_literal (0x) (lift_to_both0 (
                    @repr U128 256))) (lift_to_both0 x_len_3157))) && ((
              lift_to_both0 x_len_3157) !=.? (lift_to_both0 byte_size_v)))
        then @Err byte_seq error_t (InvalidLength)
        else @Ok byte_seq error_t (seq_slice (nat_mod_to_byte_seq_be (
              lift_to_both0 x_3156)) (
            (fun x => lift_to_both0 (repr (unsigned x)))((
                lift_to_both0 byte_size_v) .- (lift_to_both0 x_len_3157))) (
            (fun x => lift_to_both0 (repr (unsigned x)))(
              lift_to_both0 x_len_3157))))
      ) : both (fset.fset0) [interface] (byte_seq_result_t)).
Fail Next Obligation.


Notation "'os2ip_inp'" :=(
  byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'os2ip_inp'" :=(byte_seq : ChoiceEquality) (at level 2).
Notation "'os2ip_out'" :=(
  rsa_int_t : choice_type) (in custom pack_type at level 2).
Notation "'os2ip_out'" :=(rsa_int_t : ChoiceEquality) (at level 2).
Definition OS2IP : nat :=
  3160.
Program Definition os2ip (x_3159 : byte_seq)
  : both (fset.fset0) [interface] (rsa_int_t) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (nat_mod_from_byte_seq_be (
          lift_to_both0 x_3159))
      ) : both (fset.fset0) [interface] (rsa_int_t)).
Fail Next Obligation.

Definition result_3161_loc : ChoiceEqualityLocation :=
  ((result (error_t) (byte_seq)) ; 3163%nat).
Definition t_3162_loc : ChoiceEqualityLocation :=
  (seq uint8 ; 3164%nat).
Notation "'mgf1_inp'" :=(
  byte_seq '× uint_size : choice_type) (in custom pack_type at level 2).
Notation "'mgf1_inp'" :=(byte_seq '× uint_size : ChoiceEquality) (at level 2).
Notation "'mgf1_out'" :=(
  byte_seq_result_t : choice_type) (in custom pack_type at level 2).
Notation "'mgf1_out'" :=(byte_seq_result_t : ChoiceEquality) (at level 2).
Definition MGF1 : nat :=
  3169.
Program Definition mgf1 (mgf_seed_3168 : byte_seq) (mask_len_3165 : uint_size)
  : both (CEfset ([result_3161_loc ; t_3162_loc])) [interface] (
    byte_seq_result_t) :=
  ((letbm result_3161 : (result (error_t) (byte_seq)) loc( result_3161_loc ) :=
        @Err byte_seq error_t (InvalidLength) in
      letbnd(ChoiceEqualityMonad.result_bind_both error_t) '(result_3161) :=
        if (lift_to_both0 mask_len_3165) <.? ((lift_to_both0 (usize 2)) .^ ((
              lift_to_both0 (usize 32)) .* (
              lift_to_both0 hlen_v))) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset ([result_3161_loc ; t_3162_loc])) (
          L2 := CEfset ([result_3161_loc ; t_3162_loc])) (I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
          letbm t_3162 : seq uint8 loc( t_3162_loc ) :=
            seq_new_ (default : uint8) (lift_to_both0 (usize 0)) in
          letbnd(ChoiceEqualityMonad.result_bind_both error_t) t_3162 :=
            foldi_bind_both' (lift_to_both0 (usize 0)) (((
                    lift_to_both0 mask_len_3165) .+ (lift_to_both0 (
                      usize 32))) ./ (lift_to_both0 (usize 32))) t_3162 (L := (
                  CEfset ([result_3161_loc ; t_3162_loc]))) (I := [interface]) (
                fun i_3166 t_3162 =>
                letbnd(_) x_3167 : byte_seq :=
                  i2osp (nat_mod_from_literal (0x) (pub_u128 (is_pure (
                          lift_to_both0 i_3166)))) (lift_to_both0 (
                      @repr U32 4)) in
                letbm t_3162 loc( t_3162_loc ) :=
                  seq_concat (lift_to_both0 t_3162) (array_to_seq (sha256 (
                      seq_concat (lift_to_both0 mgf_seed_3168) (
                        lift_to_both0 x_3167)))) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (@Ok (seq uint8
                  ) error_t (lift_to_both0 t_3162))
                ) in
          letbm result_3161 loc( result_3161_loc ) :=
            @Ok byte_seq error_t (seq_slice (lift_to_both0 t_3162) (
                lift_to_both0 (usize 0)) (lift_to_both0 mask_len_3165)) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (@Ok (
              (result (error_t) (byte_seq))
            ) error_t (lift_to_both0 result_3161))
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (@Ok (
            (result (error_t) (byte_seq))
          ) error_t (lift_to_both0 result_3161))
         in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        lift_to_both0 result_3161)
      ) : both (CEfset ([result_3161_loc ; t_3162_loc])) [interface] (
      byte_seq_result_t)).
Fail Next Obligation.

