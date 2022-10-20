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
  2970.
Program Definition rsaep
  : both_package (fset.fset0) [interface] [(RSAEP,(rsaep_inp,rsaep_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(pk_2966 , m_2969) := temp_inp : pk_t '× rsa_int_t in
    
    ((letb '(n_2967, e_2968) : (rsa_int_t '× rsa_int_t) :=
          lift_to_both0 pk_2966 in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          if is_pure (I := [interface]) ((lift_to_both0 m_2969) >.? ((
                lift_to_both0 n_2967) -% (nat_mod_one )))
          then @Err rsa_int_t error_t (MessageTooLarge)
          else @Ok rsa_int_t error_t (nat_mod_pow_mod (lift_to_both0 m_2969) (
              lift_to_both0 e_2968) (lift_to_both0 n_2967)))
        ) : both (fset.fset0) [interface] (rsa_int_result_t)))in
  both_package' _ _ (RSAEP,(rsaep_inp,rsaep_out)) temp_package_both.
Fail Next Obligation.


Notation "'rsadp_inp'" :=(
  sk_t '× rsa_int_t : choice_type) (in custom pack_type at level 2).
Notation "'rsadp_inp'" :=(sk_t '× rsa_int_t : ChoiceEquality) (at level 2).
Notation "'rsadp_out'" :=(
  rsa_int_result_t : choice_type) (in custom pack_type at level 2).
Notation "'rsadp_out'" :=(rsa_int_result_t : ChoiceEquality) (at level 2).
Definition RSADP : nat :=
  2975.
Program Definition rsadp
  : both_package (fset.fset0) [interface] [(RSADP,(rsadp_inp,rsadp_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(sk_2971 , c_2974) := temp_inp : sk_t '× rsa_int_t in
    
    ((letb '(n_2972, d_2973) : (rsa_int_t '× rsa_int_t) :=
          lift_to_both0 sk_2971 in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          if is_pure (I := [interface]) ((lift_to_both0 c_2974) >.? ((
                lift_to_both0 n_2972) -% (nat_mod_one )))
          then @Err rsa_int_t error_t (MessageTooLarge)
          else @Ok rsa_int_t error_t (nat_mod_pow_mod (lift_to_both0 c_2974) (
              lift_to_both0 d_2973) (lift_to_both0 n_2972)))
        ) : both (fset.fset0) [interface] (rsa_int_result_t)))in
  both_package' _ _ (RSADP,(rsadp_inp,rsadp_out)) temp_package_both.
Fail Next Obligation.


Notation "'rsasp1_inp'" :=(
  sk_t '× rsa_int_t : choice_type) (in custom pack_type at level 2).
Notation "'rsasp1_inp'" :=(sk_t '× rsa_int_t : ChoiceEquality) (at level 2).
Notation "'rsasp1_out'" :=(
  rsa_int_result_t : choice_type) (in custom pack_type at level 2).
Notation "'rsasp1_out'" :=(rsa_int_result_t : ChoiceEquality) (at level 2).
Definition RSASP1 : nat :=
  2980.
Program Definition rsasp1
  : both_package (fset.fset0) [interface] [(RSASP1,(rsasp1_inp,rsasp1_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(sk_2976 , m_2979) := temp_inp : sk_t '× rsa_int_t in
    
    ((letb '(n_2977, d_2978) : (rsa_int_t '× rsa_int_t) :=
          lift_to_both0 sk_2976 in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          if is_pure (I := [interface]) ((lift_to_both0 m_2979) >.? ((
                lift_to_both0 n_2977) -% (nat_mod_one )))
          then @Err rsa_int_t error_t (MessageTooLarge)
          else @Ok rsa_int_t error_t (nat_mod_pow_mod (lift_to_both0 m_2979) (
              lift_to_both0 d_2978) (lift_to_both0 n_2977)))
        ) : both (fset.fset0) [interface] (rsa_int_result_t)))in
  both_package' _ _ (RSASP1,(rsasp1_inp,rsasp1_out)) temp_package_both.
Fail Next Obligation.


Notation "'rsavp1_inp'" :=(
  pk_t '× rsa_int_t : choice_type) (in custom pack_type at level 2).
Notation "'rsavp1_inp'" :=(pk_t '× rsa_int_t : ChoiceEquality) (at level 2).
Notation "'rsavp1_out'" :=(
  rsa_int_result_t : choice_type) (in custom pack_type at level 2).
Notation "'rsavp1_out'" :=(rsa_int_result_t : ChoiceEquality) (at level 2).
Definition RSAVP1 : nat :=
  2985.
Program Definition rsavp1
  : both_package (fset.fset0) [interface] [(RSAVP1,(rsavp1_inp,rsavp1_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(pk_2981 , s_2984) := temp_inp : pk_t '× rsa_int_t in
    
    ((letb '(n_2982, e_2983) : (rsa_int_t '× rsa_int_t) :=
          lift_to_both0 pk_2981 in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          if is_pure (I := [interface]) ((lift_to_both0 s_2984) >.? ((
                lift_to_both0 n_2982) -% (nat_mod_one )))
          then @Err rsa_int_t error_t (MessageTooLarge)
          else @Ok rsa_int_t error_t (nat_mod_pow_mod (lift_to_both0 s_2984) (
              lift_to_both0 e_2983) (lift_to_both0 n_2982)))
        ) : both (fset.fset0) [interface] (rsa_int_result_t)))in
  both_package' _ _ (RSAVP1,(rsavp1_inp,rsavp1_out)) temp_package_both.
Fail Next Obligation.


Notation "'i2osp_inp'" :=(
  rsa_int_t '× int32 : choice_type) (in custom pack_type at level 2).
Notation "'i2osp_inp'" :=(rsa_int_t '× int32 : ChoiceEquality) (at level 2).
Notation "'i2osp_out'" :=(
  byte_seq_result_t : choice_type) (in custom pack_type at level 2).
Notation "'i2osp_out'" :=(byte_seq_result_t : ChoiceEquality) (at level 2).
Definition I2OSP : nat :=
  2988.
Program Definition i2osp
  : both_package (fset.fset0) [interface] [(I2OSP,(i2osp_inp,i2osp_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(x_2986 , x_len_2987) := temp_inp : rsa_int_t '× int32 in
    
    ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          if is_pure (I := [interface]) (((lift_to_both0 x_2986) >=.? (
                nat_mod_exp (nat_mod_from_literal (0x) (lift_to_both0 (
                      @repr U128 256))) (lift_to_both0 x_len_2987))) && ((
                lift_to_both0 x_len_2987) !=.? (lift_to_both0 byte_size_v)))
          then @Err byte_seq error_t (InvalidLength)
          else @Ok byte_seq error_t (seq_slice (nat_mod_to_byte_seq_be (
                lift_to_both0 x_2986)) (@cast _ uint32 _ ((
                  lift_to_both0 byte_size_v) .- (lift_to_both0 x_len_2987))) (
              @cast _ uint32 _ (lift_to_both0 x_len_2987))))
        ) : both (fset.fset0) [interface] (byte_seq_result_t)))in
  both_package' _ _ (I2OSP,(i2osp_inp,i2osp_out)) temp_package_both.
Fail Next Obligation.


Notation "'os2ip_inp'" :=(
  byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'os2ip_inp'" :=(byte_seq : ChoiceEquality) (at level 2).
Notation "'os2ip_out'" :=(
  rsa_int_t : choice_type) (in custom pack_type at level 2).
Notation "'os2ip_out'" :=(rsa_int_t : ChoiceEquality) (at level 2).
Definition OS2IP : nat :=
  2990.
Program Definition os2ip
  : both_package (fset.fset0) [interface] [(OS2IP,(os2ip_inp,os2ip_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(x_2989) := temp_inp : byte_seq in
    
    ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          nat_mod_from_byte_seq_be (lift_to_both0 x_2989))
        ) : both (fset.fset0) [interface] (rsa_int_t)))in
  both_package' _ _ (OS2IP,(os2ip_inp,os2ip_out)) temp_package_both.
Fail Next Obligation.

Definition result_2991_loc : ChoiceEqualityLocation :=
  ((result (error_t) (byte_seq)) ; 2993%nat).
Definition t_2992_loc : ChoiceEqualityLocation :=
  (seq uint8 ; 2994%nat).
Notation "'mgf1_inp'" :=(
  byte_seq '× uint_size : choice_type) (in custom pack_type at level 2).
Notation "'mgf1_inp'" :=(byte_seq '× uint_size : ChoiceEquality) (at level 2).
Notation "'mgf1_out'" :=(
  byte_seq_result_t : choice_type) (in custom pack_type at level 2).
Notation "'mgf1_out'" :=(byte_seq_result_t : ChoiceEquality) (at level 2).
Definition MGF1 : nat :=
  2999.
Program Definition mgf1
  : both_package (CEfset ([result_2991_loc ; t_2992_loc])) [interface
  #val #[ I2OSP ] : i2osp_inp → i2osp_out ;
  #val #[ SHA256 ] : sha256_inp → sha256_out ] [(MGF1,(mgf1_inp,mgf1_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(mgf_seed_2998 , mask_len_2995) := temp_inp : byte_seq '× uint_size in
    
    let i2osp := fun x_0 x_1 => package_both i2osp (x_0,x_1) in
    let sha256 := fun x_0 => package_both sha256 (x_0) in
    ((letbm result_2991 : (result (error_t) (
              byte_seq)) loc( result_2991_loc ) :=
          @Err byte_seq error_t (InvalidLength) in
        letbnd(_) 'result_2991 :=
          if (lift_to_both0 mask_len_2995) <.? ((lift_to_both0 (usize 2)) .^ ((
                lift_to_both0 (usize 32)) .* (
                lift_to_both0 hlen_v))) :bool_ChoiceEquality
          then lift_scope (L1 := CEfset (
            [result_2991_loc ; t_2992_loc])) (L2 := CEfset (
            [result_2991_loc ; t_2992_loc])) (I1 := [interface
          #val #[ I2OSP ] : i2osp_inp → i2osp_out ;
          #val #[ SHA256 ] : sha256_inp → sha256_out ]) (I2 := [interface
          #val #[ I2OSP ] : i2osp_inp → i2osp_out ;
          #val #[ SHA256 ] : sha256_inp → sha256_out
          ]) (H_loc_incl := _) (H_opsig_incl := _) (
            letbm t_2992 : seq uint8 loc( t_2992_loc ) :=
              seq_new_ (default : uint8) (lift_to_both0 (usize 0)) in
            letbnd(_) t_2992 :=
              foldi_bind_both' (lift_to_both0 (usize 0)) (((
                      lift_to_both0 mask_len_2995) .+ (lift_to_both0 (
                        usize 32))) ./ (lift_to_both0 (
                      usize 32))) t_2992 (L := (CEfset (
                    [result_2991_loc ; t_2992_loc]))) (I := ([interface
                  #val #[ I2OSP ] : i2osp_inp → i2osp_out ;
                  #val #[ SHA256 ] : sha256_inp → sha256_out
                  ])) (fun i_2996 t_2992 =>
                letbnd(_) x_2997 : byte_seq :=
                  i2osp (nat_mod_from_literal (0x) (pub_u128 (is_pure (
                          lift_to_both0 i_2996)))) (lift_to_both0 (
                      @repr U32 4)) in
                letbm t_2992 loc( t_2992_loc ) :=
                  seq_concat (lift_to_both0 t_2992) (array_to_seq (sha256 (
                      seq_concat (lift_to_both0 mgf_seed_2998) (
                        lift_to_both0 x_2997)))) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (@Ok (seq uint8
                  ) error_t (lift_to_both0 t_2992))
                ) in
            letbm result_2991 loc( result_2991_loc ) :=
              @Ok byte_seq error_t (seq_slice (lift_to_both0 t_2992) (
                  lift_to_both0 (usize 0)) (lift_to_both0 mask_len_2995)) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (@Ok (
                (result (error_t) (byte_seq))
              ) error_t (lift_to_both0 result_2991))
            )
          else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (@Ok (
              (result (error_t) (byte_seq))
            ) error_t (lift_to_both0 result_2991))
           in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          lift_to_both0 result_2991)
        ) : both (CEfset ([result_2991_loc ; t_2992_loc])) [interface
      #val #[ I2OSP ] : i2osp_inp → i2osp_out ;
      #val #[ SHA256 ] : sha256_inp → sha256_out ] (byte_seq_result_t)))in
  both_package' _ _ (MGF1,(mgf1_inp,mgf1_out)) temp_package_both.
Fail Next Obligation.

