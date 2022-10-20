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

Require Import Hacspec_Rsa_Pkcs1.

Definition int_byte_t := nseq (uint8) (usize 1).

Definition one_v : int_byte_t :=
  array_from_list uint8 [(secret (@repr U8 1)) : uint8].

Definition two_v : int_byte_t :=
  array_from_list uint8 [(secret (@repr U8 2)) : uint8].

Definition suite_string_v : int_byte_t :=
  one_v.


Notation "'vrf_mgf1_inp'" :=(
  rsa_int_t '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'vrf_mgf1_inp'" :=(
  rsa_int_t '× byte_seq : ChoiceEquality) (at level 2).
Notation "'vrf_mgf1_out'" :=(
  byte_seq_result_t : choice_type) (in custom pack_type at level 2).
Notation "'vrf_mgf1_out'" :=(byte_seq_result_t : ChoiceEquality) (at level 2).
Definition VRF_MGF1 : nat :=
  3124.
Program Definition vrf_mgf1
  : both_package (fset.fset0) [interface
  #val #[ I2OSP ] : i2osp_inp → i2osp_out ;
  #val #[ MGF1 ] : mgf1_inp → mgf1_out ] [(VRF_MGF1,(
      vrf_mgf1_inp,vrf_mgf1_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(n_3118 , alpha_3121) := temp_inp : rsa_int_t '× byte_seq in
    
    let i2osp := fun x_0 x_1 => package_both i2osp (x_0,x_1) in
    let mgf1 := fun x_0 x_1 => package_both mgf1 (x_0,x_1) in
    ((letbnd(_) mgf_salt1_3117 : seq uint8 :=
          i2osp (rsa_int_from_literal (@cast _ uint128 _ (
                lift_to_both0 byte_size_v))) (lift_to_both0 (@repr U32 4)) in
        letbnd(_) mgf_salt2_3119 : seq uint8 :=
          i2osp (lift_to_both0 n_3118) (lift_to_both0 byte_size_v) in
        letb mgf_salt_3120 : seq uint8 :=
          seq_concat (lift_to_both0 mgf_salt1_3117) (
            lift_to_both0 mgf_salt2_3119) in
        letb mgf_string_3122 : seq uint8 :=
          seq_concat (seq_concat (array_concat (lift_to_both0 suite_string_v) (
                array_to_seq (lift_to_both0 one_v))) (
              lift_to_both0 mgf_salt_3120)) (lift_to_both0 alpha_3121) in
        letbnd(_) mgf_3123 : seq uint8 :=
          mgf1 (lift_to_both0 mgf_string_3122) ((@cast _ uint32 _ (
                lift_to_both0 byte_size_v)) .- (lift_to_both0 (usize 1))) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          @Ok seq uint8 error_t (lift_to_both0 mgf_3123))
        ) : both (fset.fset0) [interface
      #val #[ I2OSP ] : i2osp_inp → i2osp_out ;
      #val #[ MGF1 ] : mgf1_inp → mgf1_out ] (byte_seq_result_t)))in
  both_package' _ _ (VRF_MGF1,(vrf_mgf1_inp,vrf_mgf1_out)) temp_package_both.
Fail Next Obligation.


Notation "'prove_inp'" :=(
  sk_t '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'prove_inp'" :=(sk_t '× byte_seq : ChoiceEquality) (at level 2).
Notation "'prove_out'" :=(
  byte_seq_result_t : choice_type) (in custom pack_type at level 2).
Notation "'prove_out'" :=(byte_seq_result_t : ChoiceEquality) (at level 2).
Definition PROVE : nat :=
  3132.
Program Definition prove
  : both_package (fset.fset0) [interface
  #val #[ I2OSP ] : i2osp_inp → i2osp_out ;
  #val #[ OS2IP ] : os2ip_inp → os2ip_out ;
  #val #[ RSASP1 ] : rsasp1_inp → rsasp1_out ;
  #val #[ VRF_MGF1 ] : vrf_mgf1_inp → vrf_mgf1_out ] [(PROVE,(
      prove_inp,prove_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(sk_3125 , alpha_3128) := temp_inp : sk_t '× byte_seq in
    
    let i2osp := fun x_0 x_1 => package_both i2osp (x_0,x_1) in
    let os2ip := fun x_0 => package_both os2ip (x_0) in
    let rsasp1 := fun x_0 x_1 => package_both rsasp1 (x_0,x_1) in
    let vrf_mgf1 := fun x_0 x_1 => package_both vrf_mgf1 (x_0,x_1) in
    ((letb '(n_3126, d_3127) : (rsa_int_t '× rsa_int_t) :=
          (lift_to_both0 sk_3125) in
        letbnd(_) em_3129 : seq uint8 :=
          vrf_mgf1 (lift_to_both0 n_3126) (lift_to_both0 alpha_3128) in
        letb m_3130 : rsa_int_t := os2ip (lift_to_both0 em_3129) in
        letbnd(_) s_3131 : rsa_int_t :=
          rsasp1 (lift_to_both0 sk_3125) (lift_to_both0 m_3130) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (i2osp (
            lift_to_both0 s_3131) (lift_to_both0 byte_size_v))
        ) : both (fset.fset0) [interface
      #val #[ I2OSP ] : i2osp_inp → i2osp_out ;
      #val #[ OS2IP ] : os2ip_inp → os2ip_out ;
      #val #[ RSASP1 ] : rsasp1_inp → rsasp1_out ;
      #val #[ VRF_MGF1 ] : vrf_mgf1_inp → vrf_mgf1_out ] (
        byte_seq_result_t)))in
  both_package' _ _ (PROVE,(prove_inp,prove_out)) temp_package_both.
Fail Next Obligation.


Notation "'proof_to_hash_inp'" :=(
  byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'proof_to_hash_inp'" :=(byte_seq : ChoiceEquality) (at level 2).
Notation "'proof_to_hash_out'" :=(
  byte_seq_result_t : choice_type) (in custom pack_type at level 2).
Notation "'proof_to_hash_out'" :=(
  byte_seq_result_t : ChoiceEquality) (at level 2).
Definition PROOF_TO_HASH : nat :=
  3135.
Program Definition proof_to_hash
  : both_package (fset.fset0) [interface
  #val #[ SHA256 ] : sha256_inp → sha256_out ] [(PROOF_TO_HASH,(
      proof_to_hash_inp,proof_to_hash_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(pi_string_3133) := temp_inp : byte_seq in
    
    let sha256 := fun x_0 => package_both sha256 (x_0) in
    ((letb hash_string_3134 : seq uint8 :=
          array_concat (lift_to_both0 suite_string_v) (array_concat (
              lift_to_both0 two_v) (lift_to_both0 pi_string_3133)) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          @Ok seq uint8 error_t (array_slice (sha256 (
                lift_to_both0 hash_string_3134)) (lift_to_both0 (usize 0)) (
              lift_to_both0 (usize 32))))
        ) : both (fset.fset0) [interface
      #val #[ SHA256 ] : sha256_inp → sha256_out ] (byte_seq_result_t)))in
  both_package' _ _ (PROOF_TO_HASH,(
      proof_to_hash_inp,proof_to_hash_out)) temp_package_both.
Fail Next Obligation.


Notation "'verify_inp'" :=(
  pk_t '× byte_seq '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'verify_inp'" :=(
  pk_t '× byte_seq '× byte_seq : ChoiceEquality) (at level 2).
Notation "'verify_out'" :=(
  byte_seq_result_t : choice_type) (in custom pack_type at level 2).
Notation "'verify_out'" :=(byte_seq_result_t : ChoiceEquality) (at level 2).
Definition VERIFY : nat :=
  3145.
Program Definition verify
  : both_package (fset.fset0) [interface
  #val #[ OS2IP ] : os2ip_inp → os2ip_out ;
  #val #[ PROOF_TO_HASH ] : proof_to_hash_inp → proof_to_hash_out ;
  #val #[ RSAVP1 ] : rsavp1_inp → rsavp1_out ;
  #val #[ VRF_MGF1 ] : vrf_mgf1_inp → vrf_mgf1_out ] [(VERIFY,(
      verify_inp,verify_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(
      pk_3136 , alpha_3142 , pi_string_3139) := temp_inp : pk_t '× byte_seq '× byte_seq in
    
    let os2ip := fun x_0 => package_both os2ip (x_0) in
    let proof_to_hash := fun x_0 => package_both proof_to_hash (x_0) in
    let rsavp1 := fun x_0 x_1 => package_both rsavp1 (x_0,x_1) in
    let vrf_mgf1 := fun x_0 x_1 => package_both vrf_mgf1 (x_0,x_1) in
    ((letb '(n_3137, e_3138) : (rsa_int_t '× rsa_int_t) :=
          (lift_to_both0 pk_3136) in
        letb s_3140 : rsa_int_t := os2ip (lift_to_both0 pi_string_3139) in
        letbnd(_) m_3141 : rsa_int_t :=
          rsavp1 (lift_to_both0 pk_3136) (lift_to_both0 s_3140) in
        letbnd(_) em_prime_3143 : seq uint8 :=
          vrf_mgf1 (lift_to_both0 n_3137) (lift_to_both0 alpha_3142) in
        letb m_prime_3144 : rsa_int_t := os2ip (lift_to_both0 em_prime_3143) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          if is_pure (I := [interface]) ((lift_to_both0 m_3141) =.? (
              lift_to_both0 m_prime_3144))
          then proof_to_hash (lift_to_both0 pi_string_3139)
          else @Err seq uint8 error_t (VerificationFailed))
        ) : both (fset.fset0) [interface
      #val #[ OS2IP ] : os2ip_inp → os2ip_out ;
      #val #[ PROOF_TO_HASH ] : proof_to_hash_inp → proof_to_hash_out ;
      #val #[ RSAVP1 ] : rsavp1_inp → rsavp1_out ;
      #val #[ VRF_MGF1 ] : vrf_mgf1_inp → vrf_mgf1_out ] (
        byte_seq_result_t)))in
  both_package' _ _ (VERIFY,(verify_inp,verify_out)) temp_package_both.
Fail Next Obligation.

