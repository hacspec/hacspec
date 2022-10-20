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


Definition rounds_v : uint_size :=
  usize 24.

Definition sha3224_rate_v : uint_size :=
  usize 144.

Definition sha3256_rate_v : uint_size :=
  usize 136.

Definition sha3384_rate_v : uint_size :=
  usize 104.

Definition sha3512_rate_v : uint_size :=
  usize 72.

Definition shake128_rate_v : uint_size :=
  usize 168.

Definition shake256_rate_v : uint_size :=
  usize 136.

Definition state_t := nseq (uint64) (usize 25).

Definition row_t := nseq (uint64) (usize 5).

Definition digest224_t := nseq (uint8) (usize 28).

Definition digest256_t := nseq (uint8) (usize 32).

Definition digest384_t := nseq (uint8) (usize 48).

Definition digest512_t := nseq (uint8) (usize 64).

Definition round_constants_t := nseq (int64) (rounds_v).

Definition rotation_constants_t := nseq (uint_size) (usize 25).

Definition roundconstants_v : round_constants_t :=
  array_from_list int64 [
    (@repr U64 1) : int64;
    (@repr U64 32898) : int64;
    (@repr U64 9223372036854808714) : int64;
    (@repr U64 9223372039002292224) : int64;
    (@repr U64 32907) : int64;
    (@repr U64 2147483649) : int64;
    (@repr U64 9223372039002292353) : int64;
    (@repr U64 9223372036854808585) : int64;
    (@repr U64 138) : int64;
    (@repr U64 136) : int64;
    (@repr U64 2147516425) : int64;
    (@repr U64 2147483658) : int64;
    (@repr U64 2147516555) : int64;
    (@repr U64 9223372036854775947) : int64;
    (@repr U64 9223372036854808713) : int64;
    (@repr U64 9223372036854808579) : int64;
    (@repr U64 9223372036854808578) : int64;
    (@repr U64 9223372036854775936) : int64;
    (@repr U64 32778) : int64;
    (@repr U64 9223372039002259466) : int64;
    (@repr U64 9223372039002292353) : int64;
    (@repr U64 9223372036854808704) : int64;
    (@repr U64 2147483649) : int64;
    (@repr U64 9223372039002292232) : int64
  ].

Definition rotc_v : rotation_constants_t :=
  array_from_list uint_size [
    (usize 0) : uint_size;
    (usize 1) : uint_size;
    (usize 62) : uint_size;
    (usize 28) : uint_size;
    (usize 27) : uint_size;
    (usize 36) : uint_size;
    (usize 44) : uint_size;
    (usize 6) : uint_size;
    (usize 55) : uint_size;
    (usize 20) : uint_size;
    (usize 3) : uint_size;
    (usize 10) : uint_size;
    (usize 43) : uint_size;
    (usize 25) : uint_size;
    (usize 39) : uint_size;
    (usize 41) : uint_size;
    (usize 45) : uint_size;
    (usize 15) : uint_size;
    (usize 21) : uint_size;
    (usize 8) : uint_size;
    (usize 18) : uint_size;
    (usize 2) : uint_size;
    (usize 61) : uint_size;
    (usize 56) : uint_size;
    (usize 14) : uint_size
  ].

Definition pi_v : rotation_constants_t :=
  array_from_list uint_size [
    (usize 0) : uint_size;
    (usize 6) : uint_size;
    (usize 12) : uint_size;
    (usize 18) : uint_size;
    (usize 24) : uint_size;
    (usize 3) : uint_size;
    (usize 9) : uint_size;
    (usize 10) : uint_size;
    (usize 16) : uint_size;
    (usize 22) : uint_size;
    (usize 1) : uint_size;
    (usize 7) : uint_size;
    (usize 13) : uint_size;
    (usize 19) : uint_size;
    (usize 20) : uint_size;
    (usize 4) : uint_size;
    (usize 5) : uint_size;
    (usize 11) : uint_size;
    (usize 17) : uint_size;
    (usize 23) : uint_size;
    (usize 2) : uint_size;
    (usize 8) : uint_size;
    (usize 14) : uint_size;
    (usize 15) : uint_size;
    (usize 21) : uint_size
  ].

Definition b_1418_loc : ChoiceEqualityLocation :=
  (row_t ; 1419%nat).
Notation "'theta_inp'" :=(
  state_t : choice_type) (in custom pack_type at level 2).
Notation "'theta_inp'" :=(state_t : ChoiceEquality) (at level 2).
Notation "'theta_out'" :=(
  state_t : choice_type) (in custom pack_type at level 2).
Notation "'theta_out'" :=(state_t : ChoiceEquality) (at level 2).
Definition THETA : nat :=
  1426.
Program Definition theta
  : both_package (CEfset ([b_1418_loc])) [interface] [(THETA,(
      theta_inp,theta_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(s_1421) := temp_inp : state_t in
    
    ((letbm b_1418 : row_t loc( b_1418_loc ) :=
          array_new_ (default : uint64) (5) in
        letb b_1418 :=
          foldi_both' (lift_to_both0 (usize 0)) (lift_to_both0 (
                usize 5)) b_1418 (L := (CEfset ([b_1418_loc]))) (I := (
              [interface])) (fun i_1420 b_1418 =>
            letb b_1418 : row_t :=
              array_upd b_1418 (lift_to_both0 i_1420) (is_pure (((((
                          array_index (s_1421) (lift_to_both0 i_1420)) .^ (
                          array_index (s_1421) ((lift_to_both0 i_1420) .+ (
                              lift_to_both0 (usize 5))))) .^ (array_index (
                          s_1421) ((lift_to_both0 i_1420) .+ (lift_to_both0 (
                              usize 10))))) .^ (array_index (s_1421) ((
                          lift_to_both0 i_1420) .+ (lift_to_both0 (
                            usize 15))))) .^ (array_index (s_1421) ((
                        lift_to_both0 i_1420) .+ (lift_to_both0 (
                          usize 20)))))) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 b_1418)
            ) in
        letb s_1421 :=
          foldi_both' (lift_to_both0 (usize 0)) (lift_to_both0 (
                usize 5)) s_1421 (L := (CEfset ([b_1418_loc]))) (I := (
              [interface])) (fun i_1422 s_1421 =>
            letb u_1423 : uint64 :=
              array_index (b_1418) (((lift_to_both0 i_1422) .+ (lift_to_both0 (
                      usize 1))) %% (lift_to_both0 (usize 5))) in
            letb t_1424 : uint64 :=
              (array_index (b_1418) (((lift_to_both0 i_1422) .+ (lift_to_both0 (
                        usize 4))) %% (lift_to_both0 (usize 5)))) .^ (
                uint64_rotate_left (lift_to_both0 u_1423) (lift_to_both0 (
                    usize 1))) in
            letb s_1421 :=
              foldi_both' (lift_to_both0 (usize 0)) (lift_to_both0 (
                    usize 5)) s_1421 (L := (CEfset ([b_1418_loc]))) (I := (
                  [interface])) (fun j_1425 s_1421 =>
                letb s_1421 : state_t :=
                  array_upd s_1421 (((lift_to_both0 (usize 5)) .* (
                        lift_to_both0 j_1425)) .+ (lift_to_both0 i_1422)) (
                    is_pure ((array_index (s_1421) (((lift_to_both0 (
                                usize 5)) .* (lift_to_both0 j_1425)) .+ (
                            lift_to_both0 i_1422))) .^ (
                        lift_to_both0 t_1424))) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                  lift_to_both0 s_1421)
                ) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 s_1421)
            ) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 s_1421)
        ) : both (CEfset ([b_1418_loc])) [interface] (state_t)))in
  both_package' _ _ (THETA,(theta_inp,theta_out)) temp_package_both.
Fail Next Obligation.


Notation "'rho_inp'" :=(state_t : choice_type) (in custom pack_type at level 2).
Notation "'rho_inp'" :=(state_t : ChoiceEquality) (at level 2).
Notation "'rho_out'" :=(state_t : choice_type) (in custom pack_type at level 2).
Notation "'rho_out'" :=(state_t : ChoiceEquality) (at level 2).
Definition RHO : nat :=
  1430.
Program Definition rho
  : both_package (fset.fset0) [interface] [(RHO,(rho_inp,rho_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(s_1427) := temp_inp : state_t in
    
    ((letb s_1427 :=
          foldi_both' (lift_to_both0 (usize 0)) (lift_to_both0 (
                usize 25)) s_1427 (L := (fset.fset0)) (I := (
              [interface])) (fun i_1428 s_1427 =>
            letb u_1429 : uint64 :=
              array_index (s_1427) (lift_to_both0 i_1428) in
            letb s_1427 : state_t :=
              array_upd s_1427 (lift_to_both0 i_1428) (is_pure (
                  uint64_rotate_left (lift_to_both0 u_1429) (array_index (
                      rotc_v) (lift_to_both0 i_1428)))) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 s_1427)
            ) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 s_1427)
        ) : both (fset.fset0) [interface] (state_t)))in
  both_package' _ _ (RHO,(rho_inp,rho_out)) temp_package_both.
Fail Next Obligation.

Definition v_1431_loc : ChoiceEqualityLocation :=
  (state_t ; 1432%nat).
Notation "'pi_inp'" :=(state_t : choice_type) (in custom pack_type at level 2).
Notation "'pi_inp'" :=(state_t : ChoiceEquality) (at level 2).
Notation "'pi_out'" :=(state_t : choice_type) (in custom pack_type at level 2).
Notation "'pi_out'" :=(state_t : ChoiceEquality) (at level 2).
Definition PI : nat :=
  1435.
Program Definition pi
  : both_package (CEfset ([v_1431_loc])) [interface] [(PI,(pi_inp,pi_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(s_1434) := temp_inp : state_t in
    
    ((letbm v_1431 : state_t loc( v_1431_loc ) :=
          array_new_ (default : uint64) (25) in
        letb v_1431 :=
          foldi_both' (lift_to_both0 (usize 0)) (lift_to_both0 (
                usize 25)) v_1431 (L := (CEfset ([v_1431_loc]))) (I := (
              [interface])) (fun i_1433 v_1431 =>
            letb v_1431 : state_t :=
              array_upd v_1431 (lift_to_both0 i_1433) (is_pure (array_index (
                    s_1434) (array_index (pi_v) (lift_to_both0 i_1433)))) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 v_1431)
            ) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 v_1431)
        ) : both (CEfset ([v_1431_loc])) [interface] (state_t)))in
  both_package' _ _ (PI,(pi_inp,pi_out)) temp_package_both.
Fail Next Obligation.

Definition b_1436_loc : ChoiceEqualityLocation :=
  (row_t ; 1437%nat).
Notation "'chi_inp'" :=(state_t : choice_type) (in custom pack_type at level 2).
Notation "'chi_inp'" :=(state_t : ChoiceEquality) (at level 2).
Notation "'chi_out'" :=(state_t : choice_type) (in custom pack_type at level 2).
Notation "'chi_out'" :=(state_t : ChoiceEquality) (at level 2).
Definition CHI : nat :=
  1443.
Program Definition chi
  : both_package (CEfset ([b_1436_loc])) [interface] [(CHI,(
      chi_inp,chi_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(s_1438) := temp_inp : state_t in
    
    ((letbm b_1436 : row_t loc( b_1436_loc ) :=
          array_new_ (default : uint64) (5) in
        letb '(s_1438, b_1436) :=
          foldi_both' (lift_to_both0 (usize 0)) (lift_to_both0 (
                usize 5)) prod_ce(s_1438, b_1436) (L := (CEfset (
                [b_1436_loc]))) (I := ([interface])) (fun i_1439 '(
              s_1438,
              b_1436
            ) =>
            letb b_1436 :=
              foldi_both' (lift_to_both0 (usize 0)) (lift_to_both0 (
                    usize 5)) b_1436 (L := (CEfset ([b_1436_loc]))) (I := (
                  [interface])) (fun j_1440 b_1436 =>
                letb b_1436 : row_t :=
                  array_upd b_1436 (lift_to_both0 j_1440) (is_pure (
                      array_index (s_1438) (((lift_to_both0 (usize 5)) .* (
                            lift_to_both0 i_1439)) .+ (
                          lift_to_both0 j_1440)))) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                  lift_to_both0 b_1436)
                ) in
            letb s_1438 :=
              foldi_both' (lift_to_both0 (usize 0)) (lift_to_both0 (
                    usize 5)) s_1438 (L := (CEfset ([b_1436_loc]))) (I := (
                  [interface])) (fun j_1441 s_1438 =>
                letb u_1442 : uint64 :=
                  array_index (b_1436) (((lift_to_both0 j_1441) .+ (
                        lift_to_both0 (usize 1))) %% (lift_to_both0 (
                        usize 5))) in
                letb s_1438 : state_t :=
                  array_upd s_1438 (((lift_to_both0 (usize 5)) .* (
                        lift_to_both0 i_1439)) .+ (lift_to_both0 j_1441)) (
                    is_pure ((array_index (s_1438) (((lift_to_both0 (
                                usize 5)) .* (lift_to_both0 i_1439)) .+ (
                            lift_to_both0 j_1441))) .^ ((not (
                            lift_to_both0 u_1442)) .& (array_index (b_1436) (((
                                lift_to_both0 j_1441) .+ (lift_to_both0 (
                                  usize 2))) %% (lift_to_both0 (
                                usize 5))))))) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                  lift_to_both0 s_1438)
                ) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                lift_to_both0 s_1438,
                lift_to_both0 b_1436
              ))
            ) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 s_1438)
        ) : both (CEfset ([b_1436_loc])) [interface] (state_t)))in
  both_package' _ _ (CHI,(chi_inp,chi_out)) temp_package_both.
Fail Next Obligation.


Notation "'iota_inp'" :=(
  state_t '× int64 : choice_type) (in custom pack_type at level 2).
Notation "'iota_inp'" :=(state_t '× int64 : ChoiceEquality) (at level 2).
Notation "'iota_out'" :=(
  state_t : choice_type) (in custom pack_type at level 2).
Notation "'iota_out'" :=(state_t : ChoiceEquality) (at level 2).
Definition IOTA : nat :=
  1446.
Program Definition iota
  : both_package (fset.fset0) [interface] [(IOTA,(iota_inp,iota_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(s_1444 , rndconst_1445) := temp_inp : state_t '× int64 in
    
    ((letb s_1444 : state_t :=
          array_upd s_1444 (lift_to_both0 (usize 0)) (is_pure ((array_index (
                  s_1444) (lift_to_both0 (usize 0))) .^ (uint64_classify (
                  lift_to_both0 rndconst_1445)))) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 s_1444)
        ) : both (fset.fset0) [interface] (state_t)))in
  both_package' _ _ (IOTA,(iota_inp,iota_out)) temp_package_both.
Fail Next Obligation.


Notation "'keccakf1600_inp'" :=(
  state_t : choice_type) (in custom pack_type at level 2).
Notation "'keccakf1600_inp'" :=(state_t : ChoiceEquality) (at level 2).
Notation "'keccakf1600_out'" :=(
  state_t : choice_type) (in custom pack_type at level 2).
Notation "'keccakf1600_out'" :=(state_t : ChoiceEquality) (at level 2).
Definition KECCAKF1600 : nat :=
  1449.
Program Definition keccakf1600
  : both_package (CEfset ([])) [interface #val #[ CHI ] : chi_inp → chi_out ;
  #val #[ IOTA ] : iota_inp → iota_out ; #val #[ PI ] : pi_inp → pi_out ;
  #val #[ RHO ] : rho_inp → rho_out ;
  #val #[ THETA ] : theta_inp → theta_out ] [(KECCAKF1600,(
      keccakf1600_inp,keccakf1600_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(s_1447) := temp_inp : state_t in
    
    let chi := fun x_0 => package_both chi (x_0) in
    let iota := fun x_0 x_1 => package_both iota (x_0,x_1) in
    let pi := fun x_0 => package_both pi (x_0) in
    let rho := fun x_0 => package_both rho (x_0) in
    let theta := fun x_0 => package_both theta (x_0) in
    ((letb s_1447 :=
          foldi_both' (lift_to_both0 (usize 0)) (
              lift_to_both0 rounds_v) s_1447 (L := (CEfset ([]))) (I := (
              [interface #val #[ CHI ] : chi_inp → chi_out ;
              #val #[ IOTA ] : iota_inp → iota_out ;
              #val #[ PI ] : pi_inp → pi_out ;
              #val #[ RHO ] : rho_inp → rho_out ;
              #val #[ THETA ] : theta_inp → theta_out
              ])) (fun i_1448 s_1447 =>
            letbm s_1447 loc( s_1447_loc ) := theta (lift_to_both0 s_1447) in
            letbm s_1447 loc( s_1447_loc ) := rho (lift_to_both0 s_1447) in
            letbm s_1447 loc( s_1447_loc ) := pi (lift_to_both0 s_1447) in
            letbm s_1447 loc( s_1447_loc ) := chi (lift_to_both0 s_1447) in
            letbm s_1447 loc( s_1447_loc ) :=
              iota (lift_to_both0 s_1447) (array_index (roundconstants_v) (
                  lift_to_both0 i_1448)) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 s_1447)
            ) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 s_1447)
        ) : both (CEfset ([])) [interface #val #[ CHI ] : chi_inp → chi_out ;
      #val #[ IOTA ] : iota_inp → iota_out ;
      #val #[ PI ] : pi_inp → pi_out ; #val #[ RHO ] : rho_inp → rho_out ;
      #val #[ THETA ] : theta_inp → theta_out ] (state_t)))in
  both_package' _ _ (KECCAKF1600,(
      keccakf1600_inp,keccakf1600_out)) temp_package_both.
Fail Next Obligation.


Notation "'absorb_block_inp'" :=(
  state_t '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'absorb_block_inp'" :=(
  state_t '× byte_seq : ChoiceEquality) (at level 2).
Notation "'absorb_block_out'" :=(
  state_t : choice_type) (in custom pack_type at level 2).
Notation "'absorb_block_out'" :=(state_t : ChoiceEquality) (at level 2).
Definition ABSORB_BLOCK : nat :=
  1455.
Program Definition absorb_block
  : both_package (CEfset ([])) [interface
  #val #[ U64_FROM_U8 ] : uint64_from_uint8_inp → uint64_from_uint8_out ;
  #val #[ KECCAKF1600 ] : keccakf1600_inp → keccakf1600_out ] [(ABSORB_BLOCK,(
      absorb_block_inp,absorb_block_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(s_1451 , block_1450) := temp_inp : state_t '× byte_seq in
    
    let uint64_from_uint8 := fun x_0 => package_both uint64_from_uint8 (x_0) in
    let keccakf1600 := fun x_0 => package_both keccakf1600 (x_0) in
    ((letb s_1451 :=
          foldi_both' (lift_to_both0 (usize 0)) (seq_len (
                lift_to_both0 block_1450)) s_1451 (L := (CEfset ([]))) (I := (
              [interface
              #val #[ U64_FROM_U8 ] : uint64_from_uint8_inp → uint64_from_uint8_out ;
              #val #[ KECCAKF1600 ] : keccakf1600_inp → keccakf1600_out
              ])) (fun i_1452 s_1451 =>
            letb w_1453 : uint_size :=
              (lift_to_both0 i_1452) usize_shift_right (lift_to_both0 (
                  @repr U32 3)) in
            letb o_1454 : uint_size :=
              (lift_to_both0 (usize 8)) .* ((lift_to_both0 i_1452) .& (
                  lift_to_both0 (usize 7))) in
            letb s_1451 : state_t :=
              array_upd s_1451 (lift_to_both0 w_1453) (is_pure ((array_index (
                      s_1451) (lift_to_both0 w_1453)) .^ ((uint64_from_uint8 (
                        seq_index (block_1450) (
                          lift_to_both0 i_1452))) shift_left (
                      lift_to_both0 o_1454)))) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 s_1451)
            ) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (keccakf1600 (
            lift_to_both0 s_1451))
        ) : both (CEfset ([])) [interface
      #val #[ U64_FROM_U8 ] : uint64_from_uint8_inp → uint64_from_uint8_out ;
      #val #[ KECCAKF1600 ] : keccakf1600_inp → keccakf1600_out ] (
        state_t)))in
  both_package' _ _ (ABSORB_BLOCK,(
      absorb_block_inp,absorb_block_out)) temp_package_both.
Fail Next Obligation.

Definition out_1456_loc : ChoiceEqualityLocation :=
  (seq uint8 ; 1457%nat).
Notation "'squeeze_inp'" :=(
  state_t '× uint_size '× uint_size : choice_type) (in custom pack_type at level 2).
Notation "'squeeze_inp'" :=(
  state_t '× uint_size '× uint_size : ChoiceEquality) (at level 2).
Notation "'squeeze_out'" :=(
  byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'squeeze_out'" :=(byte_seq : ChoiceEquality) (at level 2).
Definition SQUEEZE : nat :=
  1466.
Program Definition squeeze
  : both_package (CEfset ([out_1456_loc])) [interface
  #val #[ U8_FROM_U64 ] : uint8_from_uint64_inp → uint8_from_uint64_out ;
  #val #[ KECCAKF1600 ] : keccakf1600_inp → keccakf1600_out ] [(SQUEEZE,(
      squeeze_inp,squeeze_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(
      s_1459 , nbytes_1458 , rate_1461) := temp_inp : state_t '× uint_size '× uint_size in
    
    let uint8_from_uint64 := fun x_0 => package_both uint8_from_uint64 (x_0) in
    let keccakf1600 := fun x_0 => package_both keccakf1600 (x_0) in
    ((letbm out_1456 : seq uint8 loc( out_1456_loc ) :=
          seq_new_ (default : uint8) (lift_to_both0 nbytes_1458) in
        letb '(s_1459, out_1456) :=
          foldi_both' (lift_to_both0 (usize 0)) (
              lift_to_both0 nbytes_1458) prod_ce(s_1459, out_1456) (L := (
              CEfset ([out_1456_loc]))) (I := ([interface
              #val #[ U8_FROM_U64 ] : uint8_from_uint64_inp → uint8_from_uint64_out ;
              #val #[ KECCAKF1600 ] : keccakf1600_inp → keccakf1600_out
              ])) (fun i_1460 '(s_1459, out_1456) =>
            letb pos_1462 : uint_size :=
              (lift_to_both0 i_1460) %% (lift_to_both0 rate_1461) in
            letb w_1463 : uint_size :=
              (lift_to_both0 pos_1462) usize_shift_right (lift_to_both0 (
                  @repr U32 3)) in
            letb o_1464 : uint_size :=
              (lift_to_both0 (usize 8)) .* ((lift_to_both0 pos_1462) .& (
                  lift_to_both0 (usize 7))) in
            letb b_1465 : uint64 :=
              ((array_index (s_1459) (lift_to_both0 w_1463)) shift_right (
                  lift_to_both0 o_1464)) .& (uint64_classify (lift_to_both0 (
                    @repr U64 255))) in
            letb out_1456 : seq uint8 :=
              seq_upd out_1456 (lift_to_both0 i_1460) (is_pure (
                  uint8_from_uint64 (lift_to_both0 b_1465))) in
            letb 's_1459 :=
              if (((lift_to_both0 i_1460) .+ (lift_to_both0 (usize 1))) %% (
                  lift_to_both0 rate_1461)) =.? (lift_to_both0 (
                  usize 0)) :bool_ChoiceEquality
              then lift_scope (L1 := CEfset ([out_1456_loc])) (L2 := CEfset (
                [out_1456_loc])) (I1 := [interface
              #val #[ KECCAKF1600 ] : keccakf1600_inp → keccakf1600_out
              ]) (I2 := [interface
              #val #[ U8_FROM_U64 ] : uint8_from_uint64_inp → uint8_from_uint64_out ;
              #val #[ KECCAKF1600 ] : keccakf1600_inp → keccakf1600_out
              ]) (H_loc_incl := _) (H_opsig_incl := _) (
                letbm s_1459 loc( s_1459_loc ) :=
                  keccakf1600 (lift_to_both0 s_1459) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                  lift_to_both0 s_1459)
                )
              else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                lift_to_both0 s_1459)
               in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                lift_to_both0 s_1459,
                lift_to_both0 out_1456
              ))
            ) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          lift_to_both0 out_1456)
        ) : both (CEfset ([out_1456_loc])) [interface
      #val #[ U8_FROM_U64 ] : uint8_from_uint64_inp → uint8_from_uint64_out ;
      #val #[ KECCAKF1600 ] : keccakf1600_inp → keccakf1600_out ] (
        byte_seq)))in
  both_package' _ _ (SQUEEZE,(squeeze_inp,squeeze_out)) temp_package_both.
Fail Next Obligation.

Definition last_block_len_1468_loc : ChoiceEqualityLocation :=
  (uint_size ; 1470%nat).
Definition s_1469_loc : ChoiceEqualityLocation :=
  (state_t ; 1471%nat).
Definition buf_1467_loc : ChoiceEqualityLocation :=
  (seq uint8 ; 1472%nat).
Notation "'keccak_inp'" :=(
  uint_size '× byte_seq '× int8 '× uint_size : choice_type) (in custom pack_type at level 2).
Notation "'keccak_inp'" :=(
  uint_size '× byte_seq '× int8 '× uint_size : ChoiceEquality) (at level 2).
Notation "'keccak_out'" :=(
  byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'keccak_out'" :=(byte_seq : ChoiceEquality) (at level 2).
Definition KECCAK : nat :=
  1480.
Program Definition keccak
  : both_package (CEfset (
      [buf_1467_loc ; last_block_len_1468_loc ; s_1469_loc])) [interface
  #val #[ ABSORB_BLOCK ] : absorb_block_inp → absorb_block_out ;
  #val #[ SQUEEZE ] : squeeze_inp → squeeze_out ] [(KECCAK,(
      keccak_inp,keccak_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(
      rate_1473 , data_1474 , p_1478 , outbytes_1479) := temp_inp : uint_size '× byte_seq '× int8 '× uint_size in
    
    let absorb_block := fun x_0 x_1 => package_both absorb_block (x_0,x_1) in
    let squeeze := fun x_0 x_1 x_2 => package_both squeeze (x_0,x_1,x_2) in
    ((letbm buf_1467 : seq uint8 loc( buf_1467_loc ) :=
          seq_new_ (default : uint8) (lift_to_both0 rate_1473) in
        letbm last_block_len_1468 : uint_size loc( last_block_len_1468_loc ) :=
          lift_to_both0 (usize 0) in
        letbm s_1469 : state_t loc( s_1469_loc ) :=
          array_new_ (default : uint64) (25) in
        letb '(buf_1467, last_block_len_1468, s_1469) :=
          foldi_both' (lift_to_both0 (usize 0)) (seq_num_chunks (
                lift_to_both0 data_1474) (lift_to_both0 rate_1473)) prod_ce(
              buf_1467,
              last_block_len_1468,
              s_1469
            ) (L := (CEfset (
                [buf_1467_loc ; last_block_len_1468_loc ; s_1469_loc]))) (I := (
              [interface
              #val #[ ABSORB_BLOCK ] : absorb_block_inp → absorb_block_out ;
              #val #[ SQUEEZE ] : squeeze_inp → squeeze_out ])) (fun i_1475 '(
              buf_1467,
              last_block_len_1468,
              s_1469
            ) =>
            letb '(block_len_1476, block_1477) : (uint_size '× seq uint8) :=
              seq_get_chunk (lift_to_both0 data_1474) (
                lift_to_both0 rate_1473) (lift_to_both0 i_1475) in
            letb '(buf_1467, last_block_len_1468, s_1469) :=
              if (lift_to_both0 block_len_1476) =.? (
                lift_to_both0 rate_1473) :bool_ChoiceEquality
              then lift_scope (L1 := CEfset (
                [buf_1467_loc ; last_block_len_1468_loc ; s_1469_loc])) (L2 := CEfset (
                [buf_1467_loc ; last_block_len_1468_loc ; s_1469_loc])) (I1 := [interface
              #val #[ ABSORB_BLOCK ] : absorb_block_inp → absorb_block_out
              ]) (I2 := [interface
              #val #[ ABSORB_BLOCK ] : absorb_block_inp → absorb_block_out
              ]) (H_loc_incl := _) (H_opsig_incl := _) (
                letbm s_1469 loc( s_1469_loc ) :=
                  absorb_block (lift_to_both0 s_1469) (
                    lift_to_both0 block_1477) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                    lift_to_both0 buf_1467,
                    lift_to_both0 last_block_len_1468,
                    lift_to_both0 s_1469
                  ))
                )
              else  lift_scope (L1 := CEfset (
                [buf_1467_loc ; last_block_len_1468_loc ; s_1469_loc])) (L2 := CEfset (
                [buf_1467_loc ; last_block_len_1468_loc ; s_1469_loc])) (I1 := [interface]) (I2 := [interface
              #val #[ ABSORB_BLOCK ] : absorb_block_inp → absorb_block_out
              ]) (H_loc_incl := _) (H_opsig_incl := _) (
                letbm buf_1467 loc( buf_1467_loc ) :=
                  seq_update_start (lift_to_both0 buf_1467) (
                    lift_to_both0 block_1477) in
                letbm last_block_len_1468 loc( last_block_len_1468_loc ) :=
                  lift_to_both0 block_len_1476 in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                    lift_to_both0 buf_1467,
                    lift_to_both0 last_block_len_1468,
                    lift_to_both0 s_1469
                  ))
                ) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                lift_to_both0 buf_1467,
                lift_to_both0 last_block_len_1468,
                lift_to_both0 s_1469
              ))
            ) in
        letb buf_1467 : seq uint8 :=
          seq_upd buf_1467 (lift_to_both0 last_block_len_1468) (is_pure (
              secret (lift_to_both0 p_1478))) in
        letb buf_1467 : seq uint8 :=
          seq_upd buf_1467 ((lift_to_both0 rate_1473) .- (lift_to_both0 (
                usize 1))) (is_pure ((seq_index (buf_1467) ((
                    lift_to_both0 rate_1473) .- (lift_to_both0 (usize 1)))) .| (
                secret (lift_to_both0 (@repr U8 128))))) in
        letbm s_1469 loc( s_1469_loc ) :=
          absorb_block (lift_to_both0 s_1469) (lift_to_both0 buf_1467) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (squeeze (
            lift_to_both0 s_1469) (lift_to_both0 outbytes_1479) (
            lift_to_both0 rate_1473))
        ) : both (CEfset (
          [buf_1467_loc ; last_block_len_1468_loc ; s_1469_loc])) [interface
      #val #[ ABSORB_BLOCK ] : absorb_block_inp → absorb_block_out ;
      #val #[ SQUEEZE ] : squeeze_inp → squeeze_out ] (byte_seq)))in
  both_package' _ _ (KECCAK,(keccak_inp,keccak_out)) temp_package_both.
Fail Next Obligation.


Notation "'sha3224_inp'" :=(
  byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'sha3224_inp'" :=(byte_seq : ChoiceEquality) (at level 2).
Notation "'sha3224_out'" :=(
  digest224_t : choice_type) (in custom pack_type at level 2).
Notation "'sha3224_out'" :=(digest224_t : ChoiceEquality) (at level 2).
Definition SHA3224 : nat :=
  1483.
Program Definition sha3224
  : both_package (CEfset ([])) [interface
  #val #[ KECCAK ] : keccak_inp → keccak_out ] [(SHA3224,(
      sha3224_inp,sha3224_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(data_1481) := temp_inp : byte_seq in
    
    let keccak := fun x_0 x_1 x_2 x_3 => package_both keccak (
      x_0,x_1,x_2,x_3) in
    ((letb t_1482 : seq uint8 :=
          keccak (lift_to_both0 sha3224_rate_v) (lift_to_both0 data_1481) (
            lift_to_both0 (@repr U8 6)) (lift_to_both0 (usize 28)) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (array_from_seq (28) (
            lift_to_both0 t_1482))
        ) : both (CEfset ([])) [interface
      #val #[ KECCAK ] : keccak_inp → keccak_out ] (digest224_t)))in
  both_package' _ _ (SHA3224,(sha3224_inp,sha3224_out)) temp_package_both.
Fail Next Obligation.


Notation "'sha3256_inp'" :=(
  byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'sha3256_inp'" :=(byte_seq : ChoiceEquality) (at level 2).
Notation "'sha3256_out'" :=(
  digest256_t : choice_type) (in custom pack_type at level 2).
Notation "'sha3256_out'" :=(digest256_t : ChoiceEquality) (at level 2).
Definition SHA3256 : nat :=
  1486.
Program Definition sha3256
  : both_package (CEfset ([])) [interface
  #val #[ KECCAK ] : keccak_inp → keccak_out ] [(SHA3256,(
      sha3256_inp,sha3256_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(data_1484) := temp_inp : byte_seq in
    
    let keccak := fun x_0 x_1 x_2 x_3 => package_both keccak (
      x_0,x_1,x_2,x_3) in
    ((letb t_1485 : seq uint8 :=
          keccak (lift_to_both0 sha3256_rate_v) (lift_to_both0 data_1484) (
            lift_to_both0 (@repr U8 6)) (lift_to_both0 (usize 32)) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (array_from_seq (32) (
            lift_to_both0 t_1485))
        ) : both (CEfset ([])) [interface
      #val #[ KECCAK ] : keccak_inp → keccak_out ] (digest256_t)))in
  both_package' _ _ (SHA3256,(sha3256_inp,sha3256_out)) temp_package_both.
Fail Next Obligation.


Notation "'sha3384_inp'" :=(
  byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'sha3384_inp'" :=(byte_seq : ChoiceEquality) (at level 2).
Notation "'sha3384_out'" :=(
  digest384_t : choice_type) (in custom pack_type at level 2).
Notation "'sha3384_out'" :=(digest384_t : ChoiceEquality) (at level 2).
Definition SHA3384 : nat :=
  1489.
Program Definition sha3384
  : both_package (CEfset ([])) [interface
  #val #[ KECCAK ] : keccak_inp → keccak_out ] [(SHA3384,(
      sha3384_inp,sha3384_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(data_1487) := temp_inp : byte_seq in
    
    let keccak := fun x_0 x_1 x_2 x_3 => package_both keccak (
      x_0,x_1,x_2,x_3) in
    ((letb t_1488 : seq uint8 :=
          keccak (lift_to_both0 sha3384_rate_v) (lift_to_both0 data_1487) (
            lift_to_both0 (@repr U8 6)) (lift_to_both0 (usize 48)) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (array_from_seq (48) (
            lift_to_both0 t_1488))
        ) : both (CEfset ([])) [interface
      #val #[ KECCAK ] : keccak_inp → keccak_out ] (digest384_t)))in
  both_package' _ _ (SHA3384,(sha3384_inp,sha3384_out)) temp_package_both.
Fail Next Obligation.


Notation "'sha3512_inp'" :=(
  byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'sha3512_inp'" :=(byte_seq : ChoiceEquality) (at level 2).
Notation "'sha3512_out'" :=(
  digest512_t : choice_type) (in custom pack_type at level 2).
Notation "'sha3512_out'" :=(digest512_t : ChoiceEquality) (at level 2).
Definition SHA3512 : nat :=
  1492.
Program Definition sha3512
  : both_package (CEfset ([])) [interface
  #val #[ KECCAK ] : keccak_inp → keccak_out ] [(SHA3512,(
      sha3512_inp,sha3512_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(data_1490) := temp_inp : byte_seq in
    
    let keccak := fun x_0 x_1 x_2 x_3 => package_both keccak (
      x_0,x_1,x_2,x_3) in
    ((letb t_1491 : seq uint8 :=
          keccak (lift_to_both0 sha3512_rate_v) (lift_to_both0 data_1490) (
            lift_to_both0 (@repr U8 6)) (lift_to_both0 (usize 64)) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (array_from_seq (64) (
            lift_to_both0 t_1491))
        ) : both (CEfset ([])) [interface
      #val #[ KECCAK ] : keccak_inp → keccak_out ] (digest512_t)))in
  both_package' _ _ (SHA3512,(sha3512_inp,sha3512_out)) temp_package_both.
Fail Next Obligation.


Notation "'shake128_inp'" :=(
  byte_seq '× uint_size : choice_type) (in custom pack_type at level 2).
Notation "'shake128_inp'" :=(
  byte_seq '× uint_size : ChoiceEquality) (at level 2).
Notation "'shake128_out'" :=(
  byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'shake128_out'" :=(byte_seq : ChoiceEquality) (at level 2).
Definition SHAKE128 : nat :=
  1495.
Program Definition shake128
  : both_package (CEfset ([])) [interface
  #val #[ KECCAK ] : keccak_inp → keccak_out ] [(SHAKE128,(
      shake128_inp,shake128_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(data_1493 , outlen_1494) := temp_inp : byte_seq '× uint_size in
    
    let keccak := fun x_0 x_1 x_2 x_3 => package_both keccak (
      x_0,x_1,x_2,x_3) in
    ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (keccak (
            lift_to_both0 shake128_rate_v) (lift_to_both0 data_1493) (
            lift_to_both0 (@repr U8 31)) (lift_to_both0 outlen_1494))
        ) : both (CEfset ([])) [interface
      #val #[ KECCAK ] : keccak_inp → keccak_out ] (byte_seq)))in
  both_package' _ _ (SHAKE128,(shake128_inp,shake128_out)) temp_package_both.
Fail Next Obligation.


Notation "'shake256_inp'" :=(
  byte_seq '× uint_size : choice_type) (in custom pack_type at level 2).
Notation "'shake256_inp'" :=(
  byte_seq '× uint_size : ChoiceEquality) (at level 2).
Notation "'shake256_out'" :=(
  byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'shake256_out'" :=(byte_seq : ChoiceEquality) (at level 2).
Definition SHAKE256 : nat :=
  1498.
Program Definition shake256
  : both_package (CEfset ([])) [interface
  #val #[ KECCAK ] : keccak_inp → keccak_out ] [(SHAKE256,(
      shake256_inp,shake256_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(data_1496 , outlen_1497) := temp_inp : byte_seq '× uint_size in
    
    let keccak := fun x_0 x_1 x_2 x_3 => package_both keccak (
      x_0,x_1,x_2,x_3) in
    ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (keccak (
            lift_to_both0 shake256_rate_v) (lift_to_both0 data_1496) (
            lift_to_both0 (@repr U8 31)) (lift_to_both0 outlen_1497))
        ) : both (CEfset ([])) [interface
      #val #[ KECCAK ] : keccak_inp → keccak_out ] (byte_seq)))in
  both_package' _ _ (SHAKE256,(shake256_inp,shake256_out)) temp_package_both.
Fail Next Obligation.

