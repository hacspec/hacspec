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
Require Import Hacspec_Lib.

Require Import Hacspec_Sha256.

Definition bit_size_v : (int32) :=
  ((@repr U32 2048)).

Definition byte_size_v : (int32) :=
  (let temp_14353 : int32 :=
      ((@repr U32 2048) ./ (@repr U32 8)) in
    (temp_14353)).

Definition hlen_v : (uint_size) :=
  ((usize 32)).

Definition rsa_int_t  :=
  (nat_mod pow2 2048).

Definition error_t : ChoiceEquality :=
  (
    unit_ChoiceEquality '+ unit_ChoiceEquality '+ unit_ChoiceEquality '+ unit_ChoiceEquality).
Definition InvalidLength : error_t :=
  (inl (inl (inl tt))).
Definition MessageTooLarge : error_t :=
  (inl (inl (inr tt))).
Definition DecryptionFailed : error_t :=
  (inl (inr tt)).
Definition VerificationFailed : error_t :=
  (inr tt).

Definition eqb_error_t (x y : error_t) : bool_ChoiceEquality :=
  (match x with
       | InvalidLength => match y with | InvalidLength=> true | _ => false end
       | MessageTooLarge =>
           match y with
           | MessageTooLarge=> true
           | _ => false
           end
       | DecryptionFailed =>
           match y with
           | DecryptionFailed=> true
           | _ => false
           end
       | VerificationFailed =>
           match y with
           | VerificationFailed=> true
           | _ => false
           end
       end.).

Definition eqb_leibniz_error_t (x y : error_t) : eqb_error_t x y = true <-> x = y.
Proof. split. intros; destruct x ; destruct y ; try (f_equal ; apply eqb_leibniz) ; easy. intros ; subst ; destruct y ; try reflexivity ; try (apply eqb_refl). Qed.

Instance eq_dec_error_t : EqDec (error_t) :=
Build_EqDec (error_t) (eqb_error_t) (eqb_leibniz_error_t).


Notation "'pk_t'" := ((rsa_int_t '× rsa_int_t)) : hacspec_scope.

Notation "'sk_t'" := ((rsa_int_t '× rsa_int_t)) : hacspec_scope.

Notation "'key_pair_t'" := ((pk_t '× sk_t)) : hacspec_scope.

Notation "'byte_seq_result_t'" := ((result error_t byte_seq)) : hacspec_scope.

Notation "'rsa_int_result_t'" := ((result error_t rsa_int_t)) : hacspec_scope.


Notation "'rsaep_inp'" := (
  pk_t '× rsa_int_t : choice_type) (in custom pack_type at level 2).
Notation "'rsaep_out'" := (
  rsa_int_result_t : choice_type) (in custom pack_type at level 2).
Definition RSAEP : nat :=
  (14368).
Program Definition rsaep
   : package (fset.fset0) [interface] [interface
  #val #[ RSAEP ] : rsaep_inp → rsaep_out ] :=
  ([package #def #[ RSAEP ] (temp_inp : rsaep_inp) : rsaep_out { 
    let '(pk_14354 , m_14355) := temp_inp : pk_t '× rsa_int_t in
    ({ code  temp_14367 ←
        (ret (pk_14354)) ;;
      let '(n_14356, e_14363) :=
        (temp_14367) : (rsa_int_t '× rsa_int_t) in
       '(temp_14358 : rsa_int_t) ←
        (nat_mod_one ) ;;
       '(temp_14360 : rsa_int_t) ←
        ((n_14356) -% (temp_14358)) ;;
       '(temp_14362 : bool_ChoiceEquality) ←
        ((m_14355) >.? (temp_14360)) ;;
       temp_14365 ←
        (nat_mod_pow_mod (m_14355) (e_14363) (n_14356)) ;;
      @ret ((result error_t rsa_int_t)) ((if (
            temp_14362):bool_ChoiceEquality then (*inline*) (
            @inr rsa_int_t error_t (MessageTooLarge)) else (
            @inl rsa_int_t error_t (temp_14365)))) } : code (
        fset.fset0) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_rsaep : package _ _ _ :=
  (rsaep).
Fail Next Obligation.


Notation "'rsadp_inp'" := (
  sk_t '× rsa_int_t : choice_type) (in custom pack_type at level 2).
Notation "'rsadp_out'" := (
  rsa_int_result_t : choice_type) (in custom pack_type at level 2).
Definition RSADP : nat :=
  (14383).
Program Definition rsadp
   : package (fset.fset0) [interface] [interface
  #val #[ RSADP ] : rsadp_inp → rsadp_out ] :=
  ([package #def #[ RSADP ] (temp_inp : rsadp_inp) : rsadp_out { 
    let '(sk_14369 , c_14370) := temp_inp : sk_t '× rsa_int_t in
    ({ code  temp_14382 ←
        (ret (sk_14369)) ;;
      let '(n_14371, d_14378) :=
        (temp_14382) : (rsa_int_t '× rsa_int_t) in
       '(temp_14373 : rsa_int_t) ←
        (nat_mod_one ) ;;
       '(temp_14375 : rsa_int_t) ←
        ((n_14371) -% (temp_14373)) ;;
       '(temp_14377 : bool_ChoiceEquality) ←
        ((c_14370) >.? (temp_14375)) ;;
       temp_14380 ←
        (nat_mod_pow_mod (c_14370) (d_14378) (n_14371)) ;;
      @ret ((result error_t rsa_int_t)) ((if (
            temp_14377):bool_ChoiceEquality then (*inline*) (
            @inr rsa_int_t error_t (MessageTooLarge)) else (
            @inl rsa_int_t error_t (temp_14380)))) } : code (
        fset.fset0) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_rsadp : package _ _ _ :=
  (rsadp).
Fail Next Obligation.


Notation "'rsasp1_inp'" := (
  sk_t '× rsa_int_t : choice_type) (in custom pack_type at level 2).
Notation "'rsasp1_out'" := (
  rsa_int_result_t : choice_type) (in custom pack_type at level 2).
Definition RSASP1 : nat :=
  (14398).
Program Definition rsasp1
   : package (fset.fset0) [interface] [interface
  #val #[ RSASP1 ] : rsasp1_inp → rsasp1_out ] :=
  ([package #def #[ RSASP1 ] (temp_inp : rsasp1_inp) : rsasp1_out { 
    let '(sk_14384 , m_14385) := temp_inp : sk_t '× rsa_int_t in
    ({ code  temp_14397 ←
        (ret (sk_14384)) ;;
      let '(n_14386, d_14393) :=
        (temp_14397) : (rsa_int_t '× rsa_int_t) in
       '(temp_14388 : rsa_int_t) ←
        (nat_mod_one ) ;;
       '(temp_14390 : rsa_int_t) ←
        ((n_14386) -% (temp_14388)) ;;
       '(temp_14392 : bool_ChoiceEquality) ←
        ((m_14385) >.? (temp_14390)) ;;
       temp_14395 ←
        (nat_mod_pow_mod (m_14385) (d_14393) (n_14386)) ;;
      @ret ((result error_t rsa_int_t)) ((if (
            temp_14392):bool_ChoiceEquality then (*inline*) (
            @inr rsa_int_t error_t (MessageTooLarge)) else (
            @inl rsa_int_t error_t (temp_14395)))) } : code (
        fset.fset0) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_rsasp1 : package _ _ _ :=
  (rsasp1).
Fail Next Obligation.


Notation "'rsavp1_inp'" := (
  pk_t '× rsa_int_t : choice_type) (in custom pack_type at level 2).
Notation "'rsavp1_out'" := (
  rsa_int_result_t : choice_type) (in custom pack_type at level 2).
Definition RSAVP1 : nat :=
  (14413).
Program Definition rsavp1
   : package (fset.fset0) [interface] [interface
  #val #[ RSAVP1 ] : rsavp1_inp → rsavp1_out ] :=
  ([package #def #[ RSAVP1 ] (temp_inp : rsavp1_inp) : rsavp1_out { 
    let '(pk_14399 , s_14400) := temp_inp : pk_t '× rsa_int_t in
    ({ code  temp_14412 ←
        (ret (pk_14399)) ;;
      let '(n_14401, e_14408) :=
        (temp_14412) : (rsa_int_t '× rsa_int_t) in
       '(temp_14403 : rsa_int_t) ←
        (nat_mod_one ) ;;
       '(temp_14405 : rsa_int_t) ←
        ((n_14401) -% (temp_14403)) ;;
       '(temp_14407 : bool_ChoiceEquality) ←
        ((s_14400) >.? (temp_14405)) ;;
       temp_14410 ←
        (nat_mod_pow_mod (s_14400) (e_14408) (n_14401)) ;;
      @ret ((result error_t rsa_int_t)) ((if (
            temp_14407):bool_ChoiceEquality then (*inline*) (
            @inr rsa_int_t error_t (MessageTooLarge)) else (
            @inl rsa_int_t error_t (temp_14410)))) } : code (
        fset.fset0) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_rsavp1 : package _ _ _ :=
  (rsavp1).
Fail Next Obligation.


Notation "'i2osp_inp'" := (
  rsa_int_t '× int32 : choice_type) (in custom pack_type at level 2).
Notation "'i2osp_out'" := (
  byte_seq_result_t : choice_type) (in custom pack_type at level 2).
Definition I2OSP : nat :=
  (14432).
Program Definition i2osp
   : package (fset.fset0) [interface] [interface
  #val #[ I2OSP ] : i2osp_inp → i2osp_out ] :=
  ([package #def #[ I2OSP ] (temp_inp : i2osp_inp) : i2osp_out { 
    let '(x_14414 , x_len_14417) := temp_inp : rsa_int_t '× int32 in
    ({ code  '(temp_14416 : rsa_int_t) ←
        (nat_mod_from_literal (0x) (@repr U128 256)) ;;
       temp_14419 ←
        (nat_mod_exp (temp_14416) (x_len_14417)) ;;
       '(temp_14421 : bool_ChoiceEquality) ←
        ((x_14414) >=.? (temp_14419)) ;;
       '(temp_14423 : bool_ChoiceEquality) ←
        ((x_len_14417) !=.? (byte_size_v)) ;;
       '(temp_14425 : bool_ChoiceEquality) ←
        ((temp_14421) && (temp_14423)) ;;
       temp_14427 ←
        (nat_mod_to_byte_seq_be (x_14414)) ;;
       '(temp_14429 : int32) ←
        ((byte_size_v) .- (x_len_14417)) ;;
       '(temp_14431 : seq uint8) ←
        (seq_slice (temp_14427) (@cast _ uint32 _ (temp_14429)) (
            @cast _ uint32 _ (x_len_14417))) ;;
      @ret ((result error_t byte_seq)) ((if (
            temp_14425):bool_ChoiceEquality then (*inline*) (
            @inr byte_seq error_t (InvalidLength)) else (@inl byte_seq error_t (
              temp_14431)))) } : code (fset.fset0) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_i2osp : package _ _ _ :=
  (i2osp).
Fail Next Obligation.


Notation "'os2ip_inp'" := (
  byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'os2ip_out'" := (
  rsa_int_t : choice_type) (in custom pack_type at level 2).
Definition OS2IP : nat :=
  (14436).
Program Definition os2ip
   : package (fset.fset0) [interface] [interface
  #val #[ OS2IP ] : os2ip_inp → os2ip_out ] :=
  ([package #def #[ OS2IP ] (temp_inp : os2ip_inp) : os2ip_out { 
    let '(x_14433) := temp_inp : byte_seq in
    ({ code  '(temp_14435 : rsa_int_t) ←
        (nat_mod_from_byte_seq_be (x_14433)) ;;
      @ret (rsa_int_t) (temp_14435) } : code (fset.fset0) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_os2ip : package _ _ _ :=
  (os2ip).
Fail Next Obligation.

Definition t_14455_loc : ChoiceEqualityLocation :=
  ((seq uint8 ; 14469%nat)).
Definition result_14466_loc : ChoiceEqualityLocation :=
  (((result error_t byte_seq) ; 14470%nat)).
Notation "'mgf1_inp'" := (
  byte_seq '× uint_size : choice_type) (in custom pack_type at level 2).
Notation "'mgf1_out'" := (
  byte_seq_result_t : choice_type) (in custom pack_type at level 2).
Definition MGF1 : nat :=
  (14471).
Program Definition mgf1
   : package (CEfset ([result_14466_loc ; t_14455_loc])) [interface
  #val #[ I2OSP ] : i2osp_inp → i2osp_out ;
  #val #[ SHA256 ] : sha256_inp → sha256_out ] [interface
  #val #[ MGF1 ] : mgf1_inp → mgf1_out ] :=
  ([package #def #[ MGF1 ] (temp_inp : mgf1_inp) : mgf1_out { 
    let '(
      mgf_seed_14456 , mask_len_14437) := temp_inp : byte_seq '× uint_size in
    #import {sig #[ I2OSP ] : i2osp_inp → i2osp_out } as i2osp ;;
    let i2osp := fun x_0 x_1 => i2osp (x_0,x_1) in
    #import {sig #[ SHA256 ] : sha256_inp → sha256_out } as sha256 ;;
    let sha256 := fun x_0 => sha256 (x_0) in
    ({ code  '(result_14466 : (result error_t byte_seq)) ←
          (ret (@inr byte_seq error_t (InvalidLength))) ;;
        #put result_14466_loc := result_14466 ;;
       '(temp_14439 : uint_size) ←
        ((usize 32) .* (hlen_v)) ;;
       temp_14441 ←
        ((usize 2) .^ (temp_14439)) ;;
       '(temp_14443 : bool_ChoiceEquality) ←
        ((mask_len_14437) <.? (temp_14441)) ;;
      bnd(ChoiceEqualityMonad.result_bind_code error_t , (
          (result error_t byte_seq)
        ) , _ , CEfset ([result_14466_loc ; t_14455_loc])) 'result_14466 ⇠
      (if temp_14443 : bool_ChoiceEquality
        then (*state*) (({ code  '(t_14455 : seq uint8) ←
                ( temp_14445 ←
                    (seq_new_ (default : uint8) (usize 0)) ;;
                  ret (temp_14445)) ;;
              #put t_14455_loc := t_14455 ;;
             '(temp_14447 : uint_size) ←
              ((mask_len_14437) .+ (usize 32)) ;;
             '(temp_14449 : uint_size) ←
              ((temp_14447) ./ (usize 32)) ;;
            bnd(ChoiceEqualityMonad.result_bind_code error_t , (seq uint8
              ) , _ , CEfset ([result_14466_loc ; t_14455_loc])) t_14455 ⇠
            (foldi_bind_code' (usize 0) (temp_14449) (
                t_14455) (fun i_14450 t_14455 =>
              ({ code bnd(
                  ChoiceEqualityMonad.result_bind_code error_t , byte_seq , _ , CEfset (
                    [result_14466_loc ; t_14455_loc])) x_14457 ⇠
                (({ code  '(temp_14452 : rsa_int_t) ←
                      (nat_mod_from_literal (0x) (pub_u128 (i_14450))) ;;
                     '(temp_14454 : byte_seq_result_t) ←
                      (i2osp (temp_14452) (@repr U32 4)) ;;
                    @ret _ (temp_14454) } : code (CEfset (
                        [result_14466_loc ; t_14455_loc])) [interface
                    #val #[ I2OSP ] : i2osp_inp → i2osp_out ] _)) in
                ({ code  '(t_14455 : seq uint8) ←
                      (( '(temp_14459 : byte_seq) ←
                            (seq_concat (mgf_seed_14456) (x_14457)) ;;
                           temp_14461 ←
                            (sha256 (temp_14459)) ;;
                           '(temp_14463 : seq uint8) ←
                            (array_to_seq (temp_14461)) ;;
                           '(temp_14465 : seq uint8) ←
                            (seq_concat (t_14455) (temp_14463)) ;;
                          ret (temp_14465))) ;;
                    #put t_14455_loc := t_14455 ;;
                  
                  @ret ((result error_t (seq uint8))) (@inl (seq uint8
                    ) error_t (t_14455)) } : code (CEfset (
                      [result_14466_loc ; t_14455_loc])) [interface
                  #val #[ I2OSP ] : i2osp_inp → i2osp_out ;
                  #val #[ SHA256 ] : sha256_inp → sha256_out ] _) } : code (
                  CEfset ([result_14466_loc ; t_14455_loc])) [interface
                #val #[ I2OSP ] : i2osp_inp → i2osp_out ;
                #val #[ SHA256 ] : sha256_inp → sha256_out ] _))) in
            ({ code  '(result_14466 : (result error_t byte_seq)) ←
                  (( '(temp_14468 : seq uint8) ←
                        (seq_slice (t_14455) (usize 0) (mask_len_14437)) ;;
                      ret (@inl byte_seq error_t (temp_14468)))) ;;
                #put result_14466_loc := result_14466 ;;
              
              @ret ((result error_t ((result error_t byte_seq)))) (@inl (
                  (result error_t byte_seq)
                ) error_t (result_14466)) } : code (CEfset (
                  [result_14466_loc ; t_14455_loc])) [interface
              #val #[ I2OSP ] : i2osp_inp → i2osp_out ;
              #val #[ SHA256 ] : sha256_inp → sha256_out ] _) } : code (
              CEfset ([result_14466_loc ; t_14455_loc])) [interface
            #val #[ I2OSP ] : i2osp_inp → i2osp_out ;
            #val #[ SHA256 ] : sha256_inp → sha256_out ] _))
        else ({ code @ret ((result error_t ((result error_t byte_seq)))) (@inl (
              (result error_t byte_seq)
            ) error_t (result_14466)) } : code _ _ _) ) in
      ({ code @ret ((result error_t byte_seq)) (result_14466) } : code (CEfset (
            [result_14466_loc ; t_14455_loc])) [interface
        #val #[ I2OSP ] : i2osp_inp → i2osp_out ;
        #val #[ SHA256 ] : sha256_inp → sha256_out ] _) } : code (CEfset (
          [result_14466_loc ; t_14455_loc])) [interface
      #val #[ I2OSP ] : i2osp_inp → i2osp_out ;
      #val #[ SHA256 ] : sha256_inp → sha256_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_mgf1 : package _ _ _ :=
  (seq_link mgf1 link_rest(package_i2osp,package_sha256)).
Fail Next Obligation.

