(** This file was automatically generated using Hacspec **)
Set Warnings "-notation-overridden,-ambiguous-paths".
From Crypt Require Import choice_type Package Prelude.
Import PackageNotation.
From extructures Require Import ord fset.
From CoqWord Require Import ssrZ word.
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


Definition build_irreducible_pure (p_2 : uint_size) : seq int128 :=
  let irr_0 : seq int128 :=
    seq_new_ (default : int128) (((p_2) .+ (usize 1))) in 
  let irr_0 :=
    seq_upd irr_0 (usize 0) (- (@repr U128 1)) in 
  let irr_0 :=
    seq_upd irr_0 (usize 1) (- (@repr U128 1)) in 
  let irr_0 :=
    seq_upd irr_0 (p_2) (@repr U128 1) in 
  irr_0.
Definition build_irreducible_pure_code
  (p_2 : uint_size)
  : code fset.fset0 [interface] (@ct (seq int128)) :=
  lift_to_code (build_irreducible_pure p_2).

Definition irr_0_loc : ChoiceEqualityLocation :=
  ((seq int128 ; 7%nat)).
Program Definition build_irreducible_state
  (p_2 : uint_size) : code (CEfset ([irr_0_loc])) [interface] (@ct (
      seq int128)) :=
  (({ code  '(irr_0 : seq int128) ←
          ( '(temp_4 : uint_size) ←
              ((p_2) .+ (usize 1)) ;;
             temp_6 ←
              (seq_new_ (default : int128) (temp_4)) ;;
            ret (temp_6)) ;;
        #put irr_0_loc := irr_0 ;;
       '(irr_0 : seq int128) ←
        (ret (seq_upd irr_0 (usize 0) (- (@repr U128 1)))) ;;
      
       '(irr_0 : seq int128) ←
        (ret (seq_upd irr_0 (usize 1) (- (@repr U128 1)))) ;;
      
       '(irr_0 : seq int128) ←
        (ret (seq_upd irr_0 (p_2) (@repr U128 1))) ;;
      
      @ret (seq int128) (irr_0) } : code (CEfset ([irr_0_loc])) [interface] _)).
Fail Next Obligation.

Program Definition build_irreducible
  (p_2 : uint_size)
  : both (CEfset ([irr_0_loc])) [interface] (seq int128) :=
  letbm irr_0 : seq int128 loc( irr_0_loc ) :=
    seq_new_ (default : int128) ((lift_to_both0 p_2) .+ (lift_to_both0 (
          usize 1))) in
  letb irr_0 : seq int128 :=
    seq_upd irr_0 (lift_to_both0 (usize 0)) (is_pure (- (lift_to_both0 (
            @repr U128 1)))) in
  letb irr_0 : seq int128 :=
    seq_upd irr_0 (lift_to_both0 (usize 1)) (is_pure (- (lift_to_both0 (
            @repr U128 1)))) in
  letb irr_0 : seq int128 :=
    seq_upd irr_0 (lift_to_both0 p_2) (is_pure (lift_to_both0 (
          @repr U128 1))) in
  lift_scope (H_incl := _) (lift_to_both0 irr_0)
  .
Fail Next Obligation.

Definition round_to_3_pure
  (poly_10 : seq int128)
  (q_11 : int128)
  : seq int128 :=
  let result_8 : seq int128 :=
    (poly_10) in 
  let q_12_12 : int128 :=
    ((((q_11) .- (@repr U128 1))) ./ (@repr U128 2)) in 
  let result_8 :=
    Hacspec_Lib_Pre.foldi (usize 0) (seq_len (poly_10)) result_8
      (fun i_13 result_8 =>
      let '(result_8) :=
        ((if (((seq_index (poly_10) (i_13)) >.? (q_12_12))):bool_ChoiceEquality
            then (let result_8 :=
                seq_upd result_8 (i_13) (((seq_index (poly_10) (i_13)) .- (
                      q_11))) in 
              (result_8))
            else ((result_8))) : T _) in 
      (result_8)) in 
  let result_8 :=
    Hacspec_Lib_Pre.foldi (usize 0) (seq_len (result_8)) result_8
      (fun i_14 result_8 =>
      let '(result_8) :=
        ((if (((((seq_index (result_8) (i_14)) .% (@repr U128 3))) !=.? (
                  @repr U128 0))):bool_ChoiceEquality
            then (let result_8 :=
                seq_upd result_8 (i_14) (((seq_index (result_8) (i_14)) .- (
                      @repr U128 1))) in 
              let '(result_8) :=
                ((if (((((seq_index (result_8) (i_14)) .% (
                              @repr U128 3))) !=.? (
                          @repr U128 0))):bool_ChoiceEquality
                    then (let result_8 :=
                        seq_upd result_8 (i_14) (((seq_index (result_8) (
                                i_14)) .+ (@repr U128 2))) in 
                      (result_8))
                    else ((result_8))) : T _) in 
              (result_8))
            else ((result_8))) : T _) in 
      (result_8)) in 
  result_8.
Definition round_to_3_pure_code
  (poly_10 : seq int128)
  (q_11 : int128)
  : code fset.fset0 [interface] (@ct (seq int128)) :=
  lift_to_code (round_to_3_pure poly_10 q_11).

Definition result_8_loc : ChoiceEqualityLocation :=
  ((seq int128 ; 51%nat)).
Program Definition round_to_3_state
  (poly_10 : seq int128)
  (q_11 : int128) : code (CEfset ([result_8_loc])) [interface] (@ct (
      seq int128)) :=
  (({ code  '(result_8 : seq int128) ←
          (ret ((poly_10))) ;;
        #put result_8_loc := result_8 ;;
       '(q_12_12 : int128) ←
        ( '(temp_16 : int128) ←
            ((q_11) .- (@repr U128 1)) ;;
           '(temp_18 : int128) ←
            ((temp_16) ./ (@repr U128 2)) ;;
          ret (temp_18)) ;;
       '(temp_20 : uint_size) ←
        (seq_len (poly_10)) ;;
       '(result_8 : (seq int128)) ←
        (foldi (usize 0) (temp_20) result_8 (fun i_13 result_8 =>
            ({ code  '(temp_22 : int128) ←
                (seq_index (poly_10) (i_13)) ;;
               '(temp_24 : bool_ChoiceEquality) ←
                ((temp_22) >.? (q_12_12)) ;;
               '(result_8 : (seq int128)) ←
                (if temp_24:bool_ChoiceEquality
                  then (({ code  '(result_8 : seq int128) ←
                        ( '(temp_26 : int128) ←
                            (seq_index (poly_10) (i_13)) ;;
                           '(temp_28 : int128) ←
                            ((temp_26) .- (q_11)) ;;
                          ret (seq_upd result_8 (i_13) (temp_28))) ;;
                      
                      @ret ((seq int128)) (result_8) } : code (CEfset (
                          [result_8_loc])) [interface] _))
                  else @ret ((seq int128)) (result_8)) ;;
              
              @ret ((seq int128)) (result_8) } : code (CEfset (
                  [result_8_loc])) [interface] _))) ;;
      
       '(temp_30 : uint_size) ←
        (seq_len (result_8)) ;;
       '(result_8 : (seq int128)) ←
        (foldi (usize 0) (temp_30) result_8 (fun i_14 result_8 =>
            ({ code  '(temp_32 : int128) ←
                (seq_index (result_8) (i_14)) ;;
               '(temp_34 : int128) ←
                ((temp_32) .% (@repr U128 3)) ;;
               '(temp_36 : bool_ChoiceEquality) ←
                ((temp_34) !=.? (@repr U128 0)) ;;
               '(result_8 : (seq int128)) ←
                (if temp_36:bool_ChoiceEquality
                  then (({ code  '(result_8 : seq int128) ←
                        ( '(temp_38 : int128) ←
                            (seq_index (result_8) (i_14)) ;;
                           '(temp_40 : int128) ←
                            ((temp_38) .- (@repr U128 1)) ;;
                          ret (seq_upd result_8 (i_14) (temp_40))) ;;
                      
                       '(temp_42 : int128) ←
                        (seq_index (result_8) (i_14)) ;;
                       '(temp_44 : int128) ←
                        ((temp_42) .% (@repr U128 3)) ;;
                       '(temp_46 : bool_ChoiceEquality) ←
                        ((temp_44) !=.? (@repr U128 0)) ;;
                       '(result_8 : (seq int128)) ←
                        (if temp_46:bool_ChoiceEquality
                          then (({ code  '(result_8 : seq int128) ←
                                ( '(temp_48 : int128) ←
                                    (seq_index (result_8) (i_14)) ;;
                                   '(temp_50 : int128) ←
                                    ((temp_48) .+ (@repr U128 2)) ;;
                                  ret (seq_upd result_8 (i_14) (temp_50))) ;;
                              
                              @ret ((seq int128)) (result_8) } : code (CEfset (
                                  [result_8_loc])) [interface] _))
                          else @ret ((seq int128)) (result_8)) ;;
                      
                      @ret ((seq int128)) (result_8) } : code (CEfset (
                          [result_8_loc])) [interface] _))
                  else @ret ((seq int128)) (result_8)) ;;
              
              @ret ((seq int128)) (result_8) } : code (CEfset (
                  [result_8_loc])) [interface] _))) ;;
      
      @ret (seq int128) (result_8) } : code (CEfset (
          [result_8_loc])) [interface] _)).
Fail Next Obligation.

Program Definition round_to_3
  (poly_10 : seq int128)
  (q_11 : int128)
  : both (CEfset ([result_8_loc])) [interface] (seq int128) :=
  letbm result_8 : seq int128 loc( result_8_loc ) := (lift_to_both0 poly_10) in
  letb q_12_12 : int128 :=
    ((lift_to_both0 q_11) .- (lift_to_both0 (@repr U128 1))) ./ (lift_to_both0 (
        @repr U128 2)) in
  letb result_8 :=
    foldi_both' (lift_to_both0 (usize 0)) (seq_len (
          lift_to_both0 poly_10)) result_8 (L := (CEfset (
          [result_8_loc]))) (fun i_13 result_8 =>
      letb 'result_8 :=
        if (seq_index (poly_10) (lift_to_both0 i_13)) >.? (
          lift_to_both0 q_12_12) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset ([result_8_loc])) (L2 := CEfset (
          [result_8_loc])) (H_incl := _) (letb result_8 : seq int128 :=
            seq_upd result_8 (lift_to_both0 i_13) (is_pure ((seq_index (
                    poly_10) (lift_to_both0 i_13)) .- (lift_to_both0 q_11))) in
          lift_scope (H_incl := _) (lift_to_both0 result_8)
          )
        else lift_scope (H_incl := _) (lift_to_both0 result_8)
         in
      lift_scope (H_incl := _) (lift_to_both0 result_8)
      ) in
  letb result_8 :=
    foldi_both' (lift_to_both0 (usize 0)) (seq_len (
          lift_to_both0 result_8)) result_8 (L := (CEfset (
          [result_8_loc]))) (fun i_14 result_8 =>
      letb 'result_8 :=
        if ((seq_index (result_8) (lift_to_both0 i_14)) .% (lift_to_both0 (
              @repr U128 3))) !=.? (lift_to_both0 (
            @repr U128 0)) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset ([result_8_loc])) (L2 := CEfset (
          [result_8_loc])) (H_incl := _) (letb result_8 : seq int128 :=
            seq_upd result_8 (lift_to_both0 i_14) (is_pure ((seq_index (
                    result_8) (lift_to_both0 i_14)) .- (lift_to_both0 (
                    @repr U128 1)))) in
          letb 'result_8 :=
            if ((seq_index (result_8) (lift_to_both0 i_14)) .% (lift_to_both0 (
                  @repr U128 3))) !=.? (lift_to_both0 (
                @repr U128 0)) :bool_ChoiceEquality
            then lift_scope (L1 := CEfset ([result_8_loc])) (L2 := CEfset (
              [result_8_loc])) (H_incl := _) (letb result_8 : seq int128 :=
                seq_upd result_8 (lift_to_both0 i_14) (is_pure ((seq_index (
                        result_8) (lift_to_both0 i_14)) .+ (lift_to_both0 (
                        @repr U128 2)))) in
              lift_scope (H_incl := _) (lift_to_both0 result_8)
              )
            else lift_scope (H_incl := _) (lift_to_both0 result_8)
             in
          lift_scope (H_incl := _) (lift_to_both0 result_8)
          )
        else lift_scope (H_incl := _) (lift_to_both0 result_8)
         in
      lift_scope (H_incl := _) (lift_to_both0 result_8)
      ) in
  lift_scope (H_incl := _) (lift_to_both0 result_8)
  .
Fail Next Obligation.

Definition encrypt_pure
  (r_52 : seq int128)
  (h_53 : seq int128)
  (q_54 : int128)
  (irreducible_55 : seq int128)
  : seq int128 :=
  let pre_56 : seq int128 :=
    mul_poly_irr (r_52) (h_53) (irreducible_55) (q_54) in 
  round_to_3 (pre_56) (q_54).
Definition encrypt_pure_code
  (r_52 : seq int128)
  (h_53 : seq int128)
  (q_54 : int128)
  (irreducible_55 : seq int128)
  : code fset.fset0 [interface] (@ct (seq int128)) :=
  lift_to_code (encrypt_pure r_52 h_53 q_54 irreducible_55).


Program Definition encrypt_state
  (r_52 : seq int128)
  (h_53 : seq int128)
  (q_54 : int128)
  (irreducible_55 : seq int128) : code (CEfset ([result_8_loc])) [interface] (
    @ct (seq int128)) :=
  (({ code  '(pre_56 : seq int128) ←
        ( temp_58 ←
            (mul_poly_irr (r_52) (h_53) (irreducible_55) (q_54)) ;;
          ret (temp_58)) ;;
       '(temp_60 : seq int128) ←
        (round_to_3 (pre_56) (q_54)) ;;
      @ret (seq int128) (temp_60) } : code (CEfset (
          [result_8_loc])) [interface] _)).
Fail Next Obligation.

Program Definition encrypt
  (r_52 : seq int128)
  (h_53 : seq int128)
  (q_54 : int128)
  (irreducible_55 : seq int128)
  : both (CEfset ([result_8_loc])) [interface] (seq int128) :=
  letb pre_56 : seq int128 :=
    mul_poly_irr (lift_to_both0 r_52) (lift_to_both0 h_53) (
      lift_to_both0 irreducible_55) (lift_to_both0 q_54) in
  lift_scope (H_incl := _) (round_to_3 (lift_to_both0 pre_56) (
      lift_to_both0 q_54))
  .
Fail Next Obligation.

Definition ntru_prime_653_encrypt_pure
  (r_61 : seq int128)
  (h_62 : seq int128)
  : seq int128 :=
  let p_63 : uint_size :=
    usize 653 in 
  let q_64 : int128 :=
    @repr U128 4621 in 
  let w_65 : uint_size :=
    usize 288 in 
  let irreducible_66 : seq int128 :=
    build_irreducible (p_63) in 
  encrypt (r_61) (h_62) (q_64) (irreducible_66).
Definition ntru_prime_653_encrypt_pure_code
  (r_61 : seq int128)
  (h_62 : seq int128)
  : code fset.fset0 [interface] (@ct (seq int128)) :=
  lift_to_code (ntru_prime_653_encrypt_pure r_61 h_62).


Program Definition ntru_prime_653_encrypt_state
  (r_61 : seq int128)
  (h_62 : seq int128) : code (CEfset ([irr_0_loc ; result_8_loc])) [interface] (
    @ct (seq int128)) :=
  (({ code  '(p_63 : uint_size) ←
        (ret (usize 653)) ;;
       '(q_64 : int128) ←
        (ret (@repr U128 4621)) ;;
       '(w_65 : uint_size) ←
        (ret (usize 288)) ;;
       '(irreducible_66 : seq int128) ←
        ( '(temp_68 : seq int128) ←
            (build_irreducible (p_63)) ;;
          ret (temp_68)) ;;
       '(temp_70 : seq int128) ←
        (encrypt (r_61) (h_62) (q_64) (irreducible_66)) ;;
      @ret (seq int128) (temp_70) } : code (CEfset (
          [irr_0_loc ; result_8_loc])) [interface] _)).
Fail Next Obligation.

Program Definition ntru_prime_653_encrypt
  (r_61 : seq int128)
  (h_62 : seq int128)
  : both (CEfset ([irr_0_loc ; result_8_loc])) [interface] (seq int128) :=
  letb p_63 : uint_size := lift_to_both0 (usize 653) in
  letb q_64 : int128 := lift_to_both0 (@repr U128 4621) in
  letb w_65 : uint_size := lift_to_both0 (usize 288) in
  letb irreducible_66 : seq int128 := build_irreducible (lift_to_both0 p_63) in
  lift_scope (H_incl := _) (encrypt (lift_to_both0 r_61) (lift_to_both0 h_62) (
      lift_to_both0 q_64) (lift_to_both0 irreducible_66))
  .
Fail Next Obligation.

Definition ntru_prime_653_decrypt_pure
  (c_77 : seq int128)
  (key_f_78 : seq int128)
  (key_v_79 : seq int128)
  : (seq int128 '× bool_ChoiceEquality) :=
  let p_80 : uint_size :=
    usize 653 in 
  let q_81 : int128 :=
    @repr U128 4621 in 
  let w_82 : uint_size :=
    usize 288 in 
  let irreducible_83 : seq int128 :=
    build_irreducible (p_80) in 
  let f_c_84 : seq int128 :=
    mul_poly_irr (key_f_78) (c_77) (irreducible_83) (q_81) in 
  let f_3_c_and_decryption_ok_85 : (seq int128 '× bool_ChoiceEquality) :=
    poly_to_ring (irreducible_83) (add_poly (f_c_84) (add_poly (f_c_84) (
          f_c_84) (q_81)) (q_81)) (q_81) in 
  let '(f_3_c_86, ok_decrypt_87) :=
    f_3_c_and_decryption_ok_85 : (seq int128 '× bool_ChoiceEquality) in 
  let f_3_c_71 : seq int128 :=
    f_3_c_86 in 
  let q_12_88 : int128 :=
    ((((q_81) .- (@repr U128 1))) ./ (@repr U128 2)) in 
  let f_3_c_71 :=
    Hacspec_Lib_Pre.foldi (usize 0) (seq_len (f_3_c_71)) f_3_c_71
      (fun i_89 f_3_c_71 =>
      let '(f_3_c_71) :=
        ((if (((seq_index (f_3_c_71) (i_89)) >.? (q_12_88))):bool_ChoiceEquality
            then (let f_3_c_71 :=
                seq_upd f_3_c_71 (i_89) (((seq_index (f_3_c_71) (i_89)) .- (
                      q_81))) in 
              (f_3_c_71))
            else ((f_3_c_71))) : T _) in 
      (f_3_c_71)) in 
  let e_72 : seq int128 :=
    seq_new_ (default : int128) (seq_len (f_3_c_71)) in 
  let e_72 :=
    Hacspec_Lib_Pre.foldi (usize 0) (seq_len (e_72)) e_72
      (fun i_90 e_72 =>
      let e_72 :=
        seq_upd e_72 (i_90) (((seq_index (f_3_c_71) (i_90)) .% (
              @repr U128 3))) in 
      (e_72)) in 
  let e_72 :=
    make_positive (e_72) (@repr U128 3) in 
  let r_73 : seq int128 :=
    mul_poly_irr (e_72) (key_v_79) (irreducible_83) (@repr U128 3) in 
  let r_73 :=
    Hacspec_Lib_Pre.foldi (usize 0) (seq_len (r_73)) r_73
      (fun i_91 r_73 =>
      let '(r_73) :=
        ((if (((seq_index (r_73) (i_91)) =.? (
                  @repr U128 2))):bool_ChoiceEquality
            then (let r_73 :=
                seq_upd r_73 (i_91) (- (@repr U128 1)) in 
              (r_73))
            else ((r_73))) : T _) in 
      (r_73)) in 
  prod_ce(r_73, ok_decrypt_87).
Definition ntru_prime_653_decrypt_pure_code
  (c_77 : seq int128)
  (key_f_78 : seq int128)
  (key_v_79 : seq int128)
  : code fset.fset0 [interface] (@ct ((seq int128 '× bool_ChoiceEquality))) :=
  lift_to_code (ntru_prime_653_decrypt_pure c_77 key_f_78 key_v_79).

Definition r_73_loc : ChoiceEqualityLocation :=
  ((seq int128 ; 138%nat)).
Definition e_72_loc : ChoiceEqualityLocation :=
  ((seq int128 ; 139%nat)).
Definition f_3_c_71_loc : ChoiceEqualityLocation :=
  ((seq int128 ; 140%nat)).
Program Definition ntru_prime_653_decrypt_state
  (c_77 : seq int128)
  (key_f_78 : seq int128)
  (key_v_79 : seq int128) : code (CEfset (
      [irr_0_loc ; f_3_c_71_loc ; e_72_loc ; r_73_loc])) [interface] (@ct ((
        seq int128 '×
        bool_ChoiceEquality
      ))) :=
  (({ code  '(p_80 : uint_size) ←
        (ret (usize 653)) ;;
       '(q_81 : int128) ←
        (ret (@repr U128 4621)) ;;
       '(w_82 : uint_size) ←
        (ret (usize 288)) ;;
       '(irreducible_83 : seq int128) ←
        ( '(temp_93 : seq int128) ←
            (build_irreducible (p_80)) ;;
          ret (temp_93)) ;;
       '(f_c_84 : seq int128) ←
        ( temp_95 ←
            (mul_poly_irr (key_f_78) (c_77) (irreducible_83) (q_81)) ;;
          ret (temp_95)) ;;
       '(f_3_c_and_decryption_ok_85 : (seq int128 '× bool_ChoiceEquality)) ←
        ( temp_97 ←
            (add_poly (f_c_84) (f_c_84) (q_81)) ;;
           temp_99 ←
            (add_poly (f_c_84) (temp_97) (q_81)) ;;
           temp_101 ←
            (poly_to_ring (irreducible_83) (temp_99) (q_81)) ;;
          ret (temp_101)) ;;
       temp_137 ←
        (ret (f_3_c_and_decryption_ok_85)) ;;
      let '(f_3_c_86, ok_decrypt_87) :=
        (temp_137) : (seq int128 '× bool_ChoiceEquality) in
       '(f_3_c_71 : seq int128) ←
          (ret (f_3_c_86)) ;;
        #put f_3_c_71_loc := f_3_c_71 ;;
       '(q_12_88 : int128) ←
        ( '(temp_103 : int128) ←
            ((q_81) .- (@repr U128 1)) ;;
           '(temp_105 : int128) ←
            ((temp_103) ./ (@repr U128 2)) ;;
          ret (temp_105)) ;;
       '(temp_107 : uint_size) ←
        (seq_len (f_3_c_71)) ;;
       '(f_3_c_71 : (seq int128)) ←
        (foldi (usize 0) (temp_107) f_3_c_71 (fun i_89 f_3_c_71 =>
            ({ code  '(temp_109 : int128) ←
                (seq_index (f_3_c_71) (i_89)) ;;
               '(temp_111 : bool_ChoiceEquality) ←
                ((temp_109) >.? (q_12_88)) ;;
               '(f_3_c_71 : (seq int128)) ←
                (if temp_111:bool_ChoiceEquality
                  then (({ code  '(f_3_c_71 : seq int128) ←
                        ( '(temp_113 : int128) ←
                            (seq_index (f_3_c_71) (i_89)) ;;
                           '(temp_115 : int128) ←
                            ((temp_113) .- (q_81)) ;;
                          ret (seq_upd f_3_c_71 (i_89) (temp_115))) ;;
                      
                      @ret ((seq int128)) (f_3_c_71) } : code (CEfset (
                          [irr_0_loc ; f_3_c_71_loc])) [interface] _))
                  else @ret ((seq int128)) (f_3_c_71)) ;;
              
              @ret ((seq int128)) (f_3_c_71) } : code (CEfset (
                  [irr_0_loc ; f_3_c_71_loc])) [interface] _))) ;;
      
       '(e_72 : seq int128) ←
          ( '(temp_117 : uint_size) ←
              (seq_len (f_3_c_71)) ;;
             temp_119 ←
              (seq_new_ (default : int128) (temp_117)) ;;
            ret (temp_119)) ;;
        #put e_72_loc := e_72 ;;
       '(temp_121 : uint_size) ←
        (seq_len (e_72)) ;;
       '(e_72 : (seq int128)) ←
        (foldi (usize 0) (temp_121) e_72 (fun i_90 e_72 =>
            ({ code  '(e_72 : seq int128) ←
                ( '(temp_123 : int128) ←
                    (seq_index (f_3_c_71) (i_90)) ;;
                   '(temp_125 : int128) ←
                    ((temp_123) .% (@repr U128 3)) ;;
                  ret (seq_upd e_72 (i_90) (temp_125))) ;;
              
              @ret ((seq int128)) (e_72) } : code (CEfset (
                  [irr_0_loc ; f_3_c_71_loc ; e_72_loc])) [interface] _))) ;;
      
       '(e_72 : seq int128) ←
          (( temp_127 ←
                (make_positive (e_72) (@repr U128 3)) ;;
              ret (temp_127))) ;;
        #put e_72_loc := e_72 ;;
      
       '(r_73 : seq int128) ←
          ( temp_129 ←
              (mul_poly_irr (e_72) (key_v_79) (irreducible_83) (
                  @repr U128 3)) ;;
            ret (temp_129)) ;;
        #put r_73_loc := r_73 ;;
       '(temp_131 : uint_size) ←
        (seq_len (r_73)) ;;
       '(r_73 : (seq int128)) ←
        (foldi (usize 0) (temp_131) r_73 (fun i_91 r_73 =>
            ({ code  '(temp_133 : int128) ←
                (seq_index (r_73) (i_91)) ;;
               '(temp_135 : bool_ChoiceEquality) ←
                ((temp_133) =.? (@repr U128 2)) ;;
               '(r_73 : (seq int128)) ←
                (if temp_135:bool_ChoiceEquality
                  then (({ code  '(r_73 : seq int128) ←
                        (ret (seq_upd r_73 (i_91) (- (@repr U128 1)))) ;;
                      
                      @ret ((seq int128)) (r_73) } : code (CEfset (
                          [irr_0_loc ; f_3_c_71_loc ; e_72_loc ; r_73_loc])) [interface] _))
                  else @ret ((seq int128)) (r_73)) ;;
              
              @ret ((seq int128)) (r_73) } : code (CEfset (
                  [irr_0_loc ; f_3_c_71_loc ; e_72_loc ; r_73_loc])) [interface] _))) ;;
      
      @ret ((seq int128 '× bool_ChoiceEquality)) (prod_ce(r_73, ok_decrypt_87
        )) } : code (CEfset (
          [irr_0_loc ; f_3_c_71_loc ; e_72_loc ; r_73_loc])) [interface] _)).
Fail Next Obligation.

Program Definition ntru_prime_653_decrypt
  (c_77 : seq int128)
  (key_f_78 : seq int128)
  (key_v_79 : seq int128)
  : both (CEfset (
      [irr_0_loc ; f_3_c_71_loc ; e_72_loc ; r_73_loc])) [interface] ((
      seq int128 '×
      bool_ChoiceEquality
    )) :=
  letb p_80 : uint_size := lift_to_both0 (usize 653) in
  letb q_81 : int128 := lift_to_both0 (@repr U128 4621) in
  letb w_82 : uint_size := lift_to_both0 (usize 288) in
  letb irreducible_83 : seq int128 := build_irreducible (lift_to_both0 p_80) in
  letb f_c_84 : seq int128 :=
    mul_poly_irr (lift_to_both0 key_f_78) (lift_to_both0 c_77) (
      lift_to_both0 irreducible_83) (lift_to_both0 q_81) in
  letb f_3_c_and_decryption_ok_85 : (seq int128 '× bool_ChoiceEquality) :=
    poly_to_ring (lift_to_both0 irreducible_83) (add_poly (
        lift_to_both0 f_c_84) (add_poly (lift_to_both0 f_c_84) (
          lift_to_both0 f_c_84) (lift_to_both0 q_81)) (lift_to_both0 q_81)) (
      lift_to_both0 q_81) in
  letb '(f_3_c_86, ok_decrypt_87) : (seq int128 '× bool_ChoiceEquality) :=
    lift_to_both0 f_3_c_and_decryption_ok_85 in
  letbm f_3_c_71 : seq int128 loc( f_3_c_71_loc ) := lift_to_both0 f_3_c_86 in
  letb q_12_88 : int128 :=
    ((lift_to_both0 q_81) .- (lift_to_both0 (@repr U128 1))) ./ (lift_to_both0 (
        @repr U128 2)) in
  letb f_3_c_71 :=
    foldi_both' (lift_to_both0 (usize 0)) (seq_len (
          lift_to_both0 f_3_c_71)) f_3_c_71 (L := (CEfset (
          [irr_0_loc ; f_3_c_71_loc ; e_72_loc ; r_73_loc]))) (fun i_89 f_3_c_71 =>
      letb 'f_3_c_71 :=
        if (seq_index (f_3_c_71) (lift_to_both0 i_89)) >.? (
          lift_to_both0 q_12_88) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset (
          [irr_0_loc ; f_3_c_71_loc])) (L2 := CEfset (
          [irr_0_loc ; f_3_c_71_loc])) (H_incl := _) (
          letb f_3_c_71 : seq int128 :=
            seq_upd f_3_c_71 (lift_to_both0 i_89) (is_pure ((seq_index (
                    f_3_c_71) (lift_to_both0 i_89)) .- (lift_to_both0 q_81))) in
          lift_scope (H_incl := _) (lift_to_both0 f_3_c_71)
          )
        else lift_scope (H_incl := _) (lift_to_both0 f_3_c_71)
         in
      lift_scope (H_incl := _) (lift_to_both0 f_3_c_71)
      ) in
  letbm e_72 : seq int128 loc( e_72_loc ) :=
    seq_new_ (default : int128) (seq_len (lift_to_both0 f_3_c_71)) in
  letb e_72 :=
    foldi_both' (lift_to_both0 (usize 0)) (seq_len (
          lift_to_both0 e_72)) e_72 (L := (CEfset (
          [irr_0_loc ; f_3_c_71_loc ; e_72_loc ; r_73_loc]))) (fun i_90 e_72 =>
      letb e_72 : seq int128 :=
        seq_upd e_72 (lift_to_both0 i_90) (is_pure ((seq_index (f_3_c_71) (
                lift_to_both0 i_90)) .% (lift_to_both0 (@repr U128 3)))) in
      lift_scope (H_incl := _) (lift_to_both0 e_72)
      ) in
  letbm e_72 loc( e_72_loc ) :=
    make_positive (lift_to_both0 e_72) (lift_to_both0 (@repr U128 3)) in
  letbm r_73 : seq int128 loc( r_73_loc ) :=
    mul_poly_irr (lift_to_both0 e_72) (lift_to_both0 key_v_79) (
      lift_to_both0 irreducible_83) (lift_to_both0 (@repr U128 3)) in
  letb r_73 :=
    foldi_both' (lift_to_both0 (usize 0)) (seq_len (
          lift_to_both0 r_73)) r_73 (L := (CEfset (
          [irr_0_loc ; f_3_c_71_loc ; e_72_loc ; r_73_loc]))) (fun i_91 r_73 =>
      letb 'r_73 :=
        if (seq_index (r_73) (lift_to_both0 i_91)) =.? (lift_to_both0 (
            @repr U128 2)) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset (
          [irr_0_loc ; f_3_c_71_loc ; e_72_loc ; r_73_loc])) (L2 := CEfset (
          [irr_0_loc ; f_3_c_71_loc ; e_72_loc ; r_73_loc])) (H_incl := _) (
          letb r_73 : seq int128 :=
            seq_upd r_73 (lift_to_both0 i_91) (is_pure (- (lift_to_both0 (
                    @repr U128 1)))) in
          lift_scope (H_incl := _) (lift_to_both0 r_73)
          )
        else lift_scope (H_incl := _) (lift_to_both0 r_73)
         in
      lift_scope (H_incl := _) (lift_to_both0 r_73)
      ) in
  lift_scope (H_incl := _) (prod_b(
      lift_to_both0 r_73,
      lift_to_both0 ok_decrypt_87
    ))
  .
Fail Next Obligation.

