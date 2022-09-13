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

Definition irr_6947_loc : ChoiceEqualityLocation :=
  ((seq int128 ; 6948%nat)).
Notation "'build_irreducible_inp'" := (
  uint_size : choice_type) (in custom pack_type at level 2).
Notation "'build_irreducible_out'" := (
  seq int128 : choice_type) (in custom pack_type at level 2).
Definition BUILD_IRREDUCIBLE : nat :=
  (6949).
Program Definition build_irreducible
   : package (CEfset ([irr_6947_loc])) [interface] [interface
  #val #[ BUILD_IRREDUCIBLE ] : build_irreducible_inp → build_irreducible_out
  ] :=
  (
    [package #def #[ BUILD_IRREDUCIBLE ] (temp_inp : build_irreducible_inp) : build_irreducible_out { 
    let '(p_6942) := temp_inp : uint_size in
    ({ code  '(irr_6947 : seq int128) ←
          ( '(temp_6944 : uint_size) ←
              ((p_6942) .+ (usize 1)) ;;
             temp_6946 ←
              (seq_new_ (default : int128) (temp_6944)) ;;
            ret (temp_6946)) ;;
        #put irr_6947_loc := irr_6947 ;;
       '(irr_6947 : seq int128) ←
        (ret (seq_upd irr_6947 (usize 0) (- (@repr U128 1)))) ;;
      
       '(irr_6947 : seq int128) ←
        (ret (seq_upd irr_6947 (usize 1) (- (@repr U128 1)))) ;;
      
       '(irr_6947 : seq int128) ←
        (ret (seq_upd irr_6947 (p_6942) (@repr U128 1))) ;;
      
      @ret (seq int128) (irr_6947) } : code (CEfset (
          [irr_6947_loc])) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_build_irreducible : package _ _ _ :=
  (build_irreducible).
Fail Next Obligation.

Definition result_6968_loc : ChoiceEqualityLocation :=
  ((seq int128 ; 6992%nat)).
Notation "'round_to_3_inp'" := (
  seq int128 '× int128 : choice_type) (in custom pack_type at level 2).
Notation "'round_to_3_out'" := (
  seq int128 : choice_type) (in custom pack_type at level 2).
Definition ROUND_TO_3 : nat :=
  (6993).
Program Definition round_to_3
   : package (CEfset ([result_6968_loc])) [interface] [interface
  #val #[ ROUND_TO_3 ] : round_to_3_inp → round_to_3_out ] :=
  ([package #def #[ ROUND_TO_3 ] (temp_inp : round_to_3_inp) : round_to_3_out { 
    let '(poly_6950 , q_6951) := temp_inp : seq int128 '× int128 in
    ({ code  '(result_6968 : seq int128) ←
          (ret ((poly_6950))) ;;
        #put result_6968_loc := result_6968 ;;
       '(q_12_6961 : int128) ←
        ( '(temp_6953 : int128) ←
            ((q_6951) .- (@repr U128 1)) ;;
           '(temp_6955 : int128) ←
            ((temp_6953) ./ (@repr U128 2)) ;;
          ret (temp_6955)) ;;
       '(temp_6957 : uint_size) ←
        (seq_len (poly_6950)) ;;
       '(result_6968 : (seq int128)) ←
        (foldi' (usize 0) (temp_6957) result_6968 (L2 := CEfset (
                [result_6968_loc])) (
              I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (fun i_6958 result_6968 =>
            ({ code  '(temp_6960 : int128) ←
                (seq_index (poly_6950) (i_6958)) ;;
               '(temp_6963 : bool_ChoiceEquality) ←
                ((temp_6960) >.? (q_12_6961)) ;;
               '(result_6968 : (seq int128)) ←
                (if temp_6963:bool_ChoiceEquality
                  then (*not state*) (let temp_then :=  '(
                        result_6968 : seq int128) ←
                      ( '(temp_6965 : int128) ←
                          (seq_index (poly_6950) (i_6958)) ;;
                         '(temp_6967 : int128) ←
                          ((temp_6965) .- (q_6951)) ;;
                        ret (seq_upd result_6968 (i_6958) (temp_6967))) ;;
                    
                    @ret ((seq int128)) (result_6968) in
                    ({ code temp_then } : code (CEfset (
                          [result_6968_loc])) [interface] _))
                  else @ret ((seq int128)) (result_6968)) ;;
              
              @ret ((seq int128)) (result_6968) } : code (CEfset (
                  [result_6968_loc])) [interface] _))) ;;
      
       '(temp_6970 : uint_size) ←
        (seq_len (result_6968)) ;;
       '(result_6968 : (seq int128)) ←
        (foldi' (usize 0) (temp_6970) result_6968 (L2 := CEfset (
                [result_6968_loc])) (
              I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (fun i_6971 result_6968 =>
            ({ code  '(temp_6973 : int128) ←
                (seq_index (result_6968) (i_6971)) ;;
               '(temp_6975 : int128) ←
                ((temp_6973) .% (@repr U128 3)) ;;
               '(temp_6977 : bool_ChoiceEquality) ←
                ((temp_6975) !=.? (@repr U128 0)) ;;
               '(result_6968 : (seq int128)) ←
                (if temp_6977:bool_ChoiceEquality
                  then (*not state*) (let temp_then :=  '(
                        result_6968 : seq int128) ←
                      ( '(temp_6979 : int128) ←
                          (seq_index (result_6968) (i_6971)) ;;
                         '(temp_6981 : int128) ←
                          ((temp_6979) .- (@repr U128 1)) ;;
                        ret (seq_upd result_6968 (i_6971) (temp_6981))) ;;
                    
                     '(temp_6983 : int128) ←
                      (seq_index (result_6968) (i_6971)) ;;
                     '(temp_6985 : int128) ←
                      ((temp_6983) .% (@repr U128 3)) ;;
                     '(temp_6987 : bool_ChoiceEquality) ←
                      ((temp_6985) !=.? (@repr U128 0)) ;;
                     '(result_6968 : (seq int128)) ←
                      (if temp_6987:bool_ChoiceEquality
                        then (*not state*) (let temp_then :=  '(
                              result_6968 : seq int128) ←
                            ( '(temp_6989 : int128) ←
                                (seq_index (result_6968) (i_6971)) ;;
                               '(temp_6991 : int128) ←
                                ((temp_6989) .+ (@repr U128 2)) ;;
                              ret (seq_upd result_6968 (i_6971) (temp_6991))) ;;
                          
                          @ret ((seq int128)) (result_6968) in
                          ({ code temp_then } : code (CEfset (
                                [result_6968_loc])) [interface] _))
                        else @ret ((seq int128)) (result_6968)) ;;
                    
                    @ret ((seq int128)) (result_6968) in
                    ({ code temp_then } : code (CEfset (
                          [result_6968_loc])) [interface] _))
                  else @ret ((seq int128)) (result_6968)) ;;
              
              @ret ((seq int128)) (result_6968) } : code (CEfset (
                  [result_6968_loc])) [interface] _))) ;;
      
      @ret (seq int128) (result_6968) } : code (CEfset (
          [result_6968_loc])) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_round_to_3 : package _ _ _ :=
  (round_to_3).
Fail Next Obligation.


Notation "'encrypt_inp'" := (
  seq int128 '× seq int128 '× int128 '× seq int128 : choice_type) (in custom pack_type at level 2).
Notation "'encrypt_out'" := (
  seq int128 : choice_type) (in custom pack_type at level 2).
Definition ENCRYPT : nat :=
  (7003).
Program Definition encrypt
   : package (CEfset ([])) [interface
  #val #[ ROUND_TO_3 ] : round_to_3_inp → round_to_3_out ] [interface
  #val #[ ENCRYPT ] : encrypt_inp → encrypt_out ] :=
  ([package #def #[ ENCRYPT ] (temp_inp : encrypt_inp) : encrypt_out { 
    let '(
      r_6994 , h_6995 , q_6997 , irreducible_6996) := temp_inp : seq int128 '× seq int128 '× int128 '× seq int128 in
    #import {sig #[ ROUND_TO_3 ] : round_to_3_inp → round_to_3_out } as round_to_3 ;;
    let round_to_3 := fun x_0 x_1 => round_to_3 (x_0,x_1) in
    ({ code  '(pre_7000 : seq int128) ←
        ( temp_6999 ←
            (mul_poly_irr (r_6994) (h_6995) (irreducible_6996) (q_6997)) ;;
          ret (temp_6999)) ;;
       '(temp_7002 : seq int128) ←
        (round_to_3 (pre_7000) (q_6997)) ;;
      @ret (seq int128) (temp_7002) } : code (CEfset ([])) [interface
      #val #[ ROUND_TO_3 ] : round_to_3_inp → round_to_3_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_encrypt : package _ _ _ :=
  (seq_link encrypt link_rest(package_round_to_3)).
Fail Next Obligation.


Notation "'ntru_prime_653_encrypt_inp'" := (
  seq int128 '× seq int128 : choice_type) (in custom pack_type at level 2).
Notation "'ntru_prime_653_encrypt_out'" := (
  seq int128 : choice_type) (in custom pack_type at level 2).
Definition NTRU_PRIME_653_ENCRYPT : nat :=
  (7014).
Program Definition ntru_prime_653_encrypt
   : package (CEfset ([])) [interface
  #val #[ BUILD_IRREDUCIBLE ] : build_irreducible_inp → build_irreducible_out ;
  #val #[ ENCRYPT ] : encrypt_inp → encrypt_out ] [interface
  #val #[ NTRU_PRIME_653_ENCRYPT ] : ntru_prime_653_encrypt_inp → ntru_prime_653_encrypt_out
  ] :=
  (
    [package #def #[ NTRU_PRIME_653_ENCRYPT ] (temp_inp : ntru_prime_653_encrypt_inp) : ntru_prime_653_encrypt_out { 
    let '(r_7007 , h_7008) := temp_inp : seq int128 '× seq int128 in
    #import {sig #[ BUILD_IRREDUCIBLE ] : build_irreducible_inp → build_irreducible_out } as build_irreducible ;;
    let build_irreducible := fun x_0 => build_irreducible (x_0) in
    #import {sig #[ ENCRYPT ] : encrypt_inp → encrypt_out } as encrypt ;;
    let encrypt := fun x_0 x_1 x_2 x_3 => encrypt (x_0,x_1,x_2,x_3) in
    ({ code  '(p_7004 : uint_size) ←
        (ret (usize 653)) ;;
       '(q_7009 : int128) ←
        (ret (@repr U128 4621)) ;;
       '(w_7013 : uint_size) ←
        (ret (usize 288)) ;;
       '(irreducible_7010 : seq int128) ←
        ( '(temp_7006 : seq int128) ←
            (build_irreducible (p_7004)) ;;
          ret (temp_7006)) ;;
       '(temp_7012 : seq int128) ←
        (encrypt (r_7007) (h_7008) (q_7009) (irreducible_7010)) ;;
      @ret (seq int128) (temp_7012) } : code (CEfset ([])) [interface
      #val #[ BUILD_IRREDUCIBLE ] : build_irreducible_inp → build_irreducible_out ;
      #val #[ ENCRYPT ] : encrypt_inp → encrypt_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_ntru_prime_653_encrypt : package _ _ _ :=
  (seq_link ntru_prime_653_encrypt link_rest(
      package_build_irreducible,package_encrypt)).
Fail Next Obligation.

Definition e_7054_loc : ChoiceEqualityLocation :=
  ((seq int128 ; 7079%nat)).
Definition f_3_c_7037_loc : ChoiceEqualityLocation :=
  ((seq int128 ; 7080%nat)).
Definition r_7067_loc : ChoiceEqualityLocation :=
  ((seq int128 ; 7081%nat)).
Notation "'ntru_prime_653_decrypt_inp'" := (
  seq int128 '× seq int128 '× seq int128 : choice_type) (in custom pack_type at level 2).
Notation "'ntru_prime_653_decrypt_out'" := ((seq int128 '× bool_ChoiceEquality
  ) : choice_type) (in custom pack_type at level 2).
Definition NTRU_PRIME_653_DECRYPT : nat :=
  (7082).
Program Definition ntru_prime_653_decrypt
   : package (CEfset ([f_3_c_7037_loc ; e_7054_loc ; r_7067_loc])) [interface
  #val #[ BUILD_IRREDUCIBLE ] : build_irreducible_inp → build_irreducible_out ;
  #val #[ MAKE_POSITIVE ] : make_positive_inp → make_positive_out ] [interface
  #val #[ NTRU_PRIME_653_DECRYPT ] : ntru_prime_653_decrypt_inp → ntru_prime_653_decrypt_out
  ] :=
  (
    [package #def #[ NTRU_PRIME_653_DECRYPT ] (temp_inp : ntru_prime_653_decrypt_inp) : ntru_prime_653_decrypt_out { 
    let '(
      c_7019 , key_f_7018 , key_v_7064) := temp_inp : seq int128 '× seq int128 '× seq int128 in
    #import {sig #[ BUILD_IRREDUCIBLE ] : build_irreducible_inp → build_irreducible_out } as build_irreducible ;;
    let build_irreducible := fun x_0 => build_irreducible (x_0) in
    #import {sig #[ MAKE_POSITIVE ] : make_positive_inp → make_positive_out } as make_positive ;;
    let make_positive := fun x_0 x_1 => make_positive (x_0,x_1) in
    ({ code  '(p_7015 : uint_size) ←
        (ret (usize 653)) ;;
       '(q_7021 : int128) ←
        (ret (@repr U128 4621)) ;;
       '(w_7078 : uint_size) ←
        (ret (usize 288)) ;;
       '(irreducible_7020 : seq int128) ←
        ( '(temp_7017 : seq int128) ←
            (build_irreducible (p_7015)) ;;
          ret (temp_7017)) ;;
       '(f_c_7024 : seq int128) ←
        ( temp_7023 ←
            (mul_poly_irr (key_f_7018) (c_7019) (irreducible_7020) (q_7021)) ;;
          ret (temp_7023)) ;;
       '(f_3_c_and_decryption_ok_7031 : (seq int128 '× bool_ChoiceEquality
          )) ←
        ( temp_7026 ←
            (add_poly (f_c_7024) (f_c_7024) (q_7021)) ;;
           temp_7028 ←
            (add_poly (f_c_7024) (temp_7026) (q_7021)) ;;
           temp_7030 ←
            (poly_to_ring (irreducible_7020) (temp_7028) (q_7021)) ;;
          ret (temp_7030)) ;;
       temp_7077 ←
        (ret (f_3_c_and_decryption_ok_7031)) ;;
      let '(f_3_c_7032, ok_decrypt_7075) :=
        (temp_7077) : (seq int128 '× bool_ChoiceEquality) in
       '(f_3_c_7037 : seq int128) ←
          (ret (f_3_c_7032)) ;;
        #put f_3_c_7037_loc := f_3_c_7037 ;;
       '(q_12_7043 : int128) ←
        ( '(temp_7034 : int128) ←
            ((q_7021) .- (@repr U128 1)) ;;
           '(temp_7036 : int128) ←
            ((temp_7034) ./ (@repr U128 2)) ;;
          ret (temp_7036)) ;;
       '(temp_7039 : uint_size) ←
        (seq_len (f_3_c_7037)) ;;
       '(f_3_c_7037 : (seq int128)) ←
        (foldi' (usize 0) (temp_7039) f_3_c_7037 (L2 := CEfset (
                [f_3_c_7037_loc ; e_7054_loc ; r_7067_loc])) (I2 := [interface
              #val #[ BUILD_IRREDUCIBLE ] : build_irreducible_inp → build_irreducible_out ;
              #val #[ MAKE_POSITIVE ] : make_positive_inp → make_positive_out
              ]) (H_loc_incl := _) (H_opsig_incl := _) (fun i_7040 f_3_c_7037 =>
            ({ code  '(temp_7042 : int128) ←
                (seq_index (f_3_c_7037) (i_7040)) ;;
               '(temp_7045 : bool_ChoiceEquality) ←
                ((temp_7042) >.? (q_12_7043)) ;;
               '(f_3_c_7037 : (seq int128)) ←
                (if temp_7045:bool_ChoiceEquality
                  then (*not state*) (let temp_then :=  '(
                        f_3_c_7037 : seq int128) ←
                      ( '(temp_7047 : int128) ←
                          (seq_index (f_3_c_7037) (i_7040)) ;;
                         '(temp_7049 : int128) ←
                          ((temp_7047) .- (q_7021)) ;;
                        ret (seq_upd f_3_c_7037 (i_7040) (temp_7049))) ;;
                    
                    @ret ((seq int128)) (f_3_c_7037) in
                    ({ code temp_then } : code (CEfset (
                          [f_3_c_7037_loc])) [interface] _))
                  else @ret ((seq int128)) (f_3_c_7037)) ;;
              
              @ret ((seq int128)) (f_3_c_7037) } : code (CEfset (
                  [f_3_c_7037_loc])) [interface] _))) ;;
      
       '(e_7054 : seq int128) ←
          ( '(temp_7051 : uint_size) ←
              (seq_len (f_3_c_7037)) ;;
             temp_7053 ←
              (seq_new_ (default : int128) (temp_7051)) ;;
            ret (temp_7053)) ;;
        #put e_7054_loc := e_7054 ;;
       '(temp_7056 : uint_size) ←
        (seq_len (e_7054)) ;;
       '(e_7054 : (seq int128)) ←
        (foldi' (usize 0) (temp_7056) e_7054 (L2 := CEfset (
                [f_3_c_7037_loc ; e_7054_loc ; r_7067_loc])) (I2 := [interface
              #val #[ BUILD_IRREDUCIBLE ] : build_irreducible_inp → build_irreducible_out ;
              #val #[ MAKE_POSITIVE ] : make_positive_inp → make_positive_out
              ]) (H_loc_incl := _) (H_opsig_incl := _) (fun i_7057 e_7054 =>
            ({ code  '(e_7054 : seq int128) ←
                ( '(temp_7059 : int128) ←
                    (seq_index (f_3_c_7037) (i_7057)) ;;
                   '(temp_7061 : int128) ←
                    ((temp_7059) .% (@repr U128 3)) ;;
                  ret (seq_upd e_7054 (i_7057) (temp_7061))) ;;
              
              @ret ((seq int128)) (e_7054) } : code (CEfset (
                  [f_3_c_7037_loc ; e_7054_loc])) [interface] _))) ;;
      
       '(e_7054 : seq int128) ←
          (( temp_7063 ←
                (make_positive (e_7054) (@repr U128 3)) ;;
              ret (temp_7063))) ;;
        #put e_7054_loc := e_7054 ;;
      
       '(r_7067 : seq int128) ←
          ( temp_7066 ←
              (mul_poly_irr (e_7054) (key_v_7064) (irreducible_7020) (
                  @repr U128 3)) ;;
            ret (temp_7066)) ;;
        #put r_7067_loc := r_7067 ;;
       '(temp_7069 : uint_size) ←
        (seq_len (r_7067)) ;;
       '(r_7067 : (seq int128)) ←
        (foldi' (usize 0) (temp_7069) r_7067 (L2 := CEfset (
                [f_3_c_7037_loc ; e_7054_loc ; r_7067_loc])) (I2 := [interface
              #val #[ BUILD_IRREDUCIBLE ] : build_irreducible_inp → build_irreducible_out ;
              #val #[ MAKE_POSITIVE ] : make_positive_inp → make_positive_out
              ]) (H_loc_incl := _) (H_opsig_incl := _) (fun i_7070 r_7067 =>
            ({ code  '(temp_7072 : int128) ←
                (seq_index (r_7067) (i_7070)) ;;
               '(temp_7074 : bool_ChoiceEquality) ←
                ((temp_7072) =.? (@repr U128 2)) ;;
               '(r_7067 : (seq int128)) ←
                (if temp_7074:bool_ChoiceEquality
                  then (*not state*) (let temp_then :=  '(
                        r_7067 : seq int128) ←
                      (ret (seq_upd r_7067 (i_7070) (- (@repr U128 1)))) ;;
                    
                    @ret ((seq int128)) (r_7067) in
                    ({ code temp_then } : code (CEfset (
                          [f_3_c_7037_loc ; e_7054_loc ; r_7067_loc])) [interface] _))
                  else @ret ((seq int128)) (r_7067)) ;;
              
              @ret ((seq int128)) (r_7067) } : code (CEfset (
                  [f_3_c_7037_loc ; e_7054_loc ; r_7067_loc])) [interface] _))) ;;
      
      @ret ((seq int128 '× bool_ChoiceEquality)) (prod_ce(
          r_7067,
          ok_decrypt_7075
        )) } : code (CEfset (
          [f_3_c_7037_loc ; e_7054_loc ; r_7067_loc])) [interface
      #val #[ BUILD_IRREDUCIBLE ] : build_irreducible_inp → build_irreducible_out ;
      #val #[ MAKE_POSITIVE ] : make_positive_inp → make_positive_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_ntru_prime_653_decrypt : package _ _ _ :=
  (seq_link ntru_prime_653_decrypt link_rest(
      package_build_irreducible,package_make_positive)).
Fail Next Obligation.

