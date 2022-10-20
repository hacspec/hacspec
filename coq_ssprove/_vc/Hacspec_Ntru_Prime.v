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


Definition irr_1499_loc : ChoiceEqualityLocation :=
  (seq int128 ; 1500%nat).
Notation "'build_irreducible_inp'" :=(
  uint_size : choice_type) (in custom pack_type at level 2).
Notation "'build_irreducible_inp'" :=(uint_size : ChoiceEquality) (at level 2).
Notation "'build_irreducible_out'" :=(
  seq int128 : choice_type) (in custom pack_type at level 2).
Notation "'build_irreducible_out'" :=(seq int128 : ChoiceEquality) (at level 2).
Definition BUILD_IRREDUCIBLE : nat :=
  1502.
Program Definition build_irreducible
  : both_package (CEfset ([irr_1499_loc])) [interface] [(BUILD_IRREDUCIBLE,(
      build_irreducible_inp,build_irreducible_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(p_1501) := temp_inp : uint_size in
    
    ((letbm irr_1499 : seq int128 loc( irr_1499_loc ) :=
          seq_new_ (default : int128) ((lift_to_both0 p_1501) .+ (
              lift_to_both0 (usize 1))) in
        letb irr_1499 : seq int128 :=
          seq_upd irr_1499 (lift_to_both0 (usize 0)) (is_pure (- (
                lift_to_both0 (@repr U128 1)))) in
        letb irr_1499 : seq int128 :=
          seq_upd irr_1499 (lift_to_both0 (usize 1)) (is_pure (- (
                lift_to_both0 (@repr U128 1)))) in
        letb irr_1499 : seq int128 :=
          seq_upd irr_1499 (lift_to_both0 p_1501) (is_pure (lift_to_both0 (
                @repr U128 1))) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          lift_to_both0 irr_1499)
        ) : both (CEfset ([irr_1499_loc])) [interface] (seq int128)))in
  both_package' _ _ (BUILD_IRREDUCIBLE,(
      build_irreducible_inp,build_irreducible_out)) temp_package_both.
Fail Next Obligation.

Definition result_1503_loc : ChoiceEqualityLocation :=
  (seq int128 ; 1504%nat).
Notation "'round_to_3_inp'" :=(
  seq int128 '× int128 : choice_type) (in custom pack_type at level 2).
Notation "'round_to_3_inp'" :=(
  seq int128 '× int128 : ChoiceEquality) (at level 2).
Notation "'round_to_3_out'" :=(
  seq int128 : choice_type) (in custom pack_type at level 2).
Notation "'round_to_3_out'" :=(seq int128 : ChoiceEquality) (at level 2).
Definition ROUND_TO_3 : nat :=
  1510.
Program Definition round_to_3
  : both_package (CEfset ([result_1503_loc])) [interface] [(ROUND_TO_3,(
      round_to_3_inp,round_to_3_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(poly_1505 , q_1506) := temp_inp : seq int128 '× int128 in
    
    ((letbm result_1503 : seq int128 loc( result_1503_loc ) :=
          (lift_to_both0 poly_1505) in
        letb q_12_1507 : int128 :=
          ((lift_to_both0 q_1506) .- (lift_to_both0 (@repr U128 1))) ./ (
            lift_to_both0 (@repr U128 2)) in
        letb result_1503 :=
          foldi_both' (lift_to_both0 (usize 0)) (seq_len (
                lift_to_both0 poly_1505)) result_1503 (L := (CEfset (
                [result_1503_loc]))) (I := (
              [interface])) (fun i_1508 result_1503 =>
            letb 'result_1503 :=
              if (seq_index (poly_1505) (lift_to_both0 i_1508)) >.? (
                lift_to_both0 q_12_1507) :bool_ChoiceEquality
              then lift_scope (L1 := CEfset ([result_1503_loc])) (L2 := CEfset (
                [result_1503_loc])) (I1 := [interface]) (I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
                letb result_1503 : seq int128 :=
                  seq_upd result_1503 (lift_to_both0 i_1508) (is_pure ((
                        seq_index (poly_1505) (lift_to_both0 i_1508)) .- (
                        lift_to_both0 q_1506))) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                  lift_to_both0 result_1503)
                )
              else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                lift_to_both0 result_1503)
               in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 result_1503)
            ) in
        letb result_1503 :=
          foldi_both' (lift_to_both0 (usize 0)) (seq_len (
                lift_to_both0 result_1503)) result_1503 (L := (CEfset (
                [result_1503_loc]))) (I := (
              [interface])) (fun i_1509 result_1503 =>
            letb 'result_1503 :=
              if ((seq_index (result_1503) (lift_to_both0 i_1509)) .% (
                  lift_to_both0 (@repr U128 3))) !=.? (lift_to_both0 (
                  @repr U128 0)) :bool_ChoiceEquality
              then lift_scope (L1 := CEfset ([result_1503_loc])) (L2 := CEfset (
                [result_1503_loc])) (I1 := [interface]) (I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
                letb result_1503 : seq int128 :=
                  seq_upd result_1503 (lift_to_both0 i_1509) (is_pure ((
                        seq_index (result_1503) (lift_to_both0 i_1509)) .- (
                        lift_to_both0 (@repr U128 1)))) in
                letb 'result_1503 :=
                  if ((seq_index (result_1503) (lift_to_both0 i_1509)) .% (
                      lift_to_both0 (@repr U128 3))) !=.? (lift_to_both0 (
                      @repr U128 0)) :bool_ChoiceEquality
                  then lift_scope (L1 := CEfset (
                    [result_1503_loc])) (L2 := CEfset (
                    [result_1503_loc])) (I1 := [interface]) (I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
                    letb result_1503 : seq int128 :=
                      seq_upd result_1503 (lift_to_both0 i_1509) (is_pure ((
                            seq_index (result_1503) (lift_to_both0 i_1509)) .+ (
                            lift_to_both0 (@repr U128 2)))) in
                    lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                      lift_to_both0 result_1503)
                    )
                  else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                    lift_to_both0 result_1503)
                   in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                  lift_to_both0 result_1503)
                )
              else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                lift_to_both0 result_1503)
               in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 result_1503)
            ) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          lift_to_both0 result_1503)
        ) : both (CEfset ([result_1503_loc])) [interface] (seq int128)))in
  both_package' _ _ (ROUND_TO_3,(
      round_to_3_inp,round_to_3_out)) temp_package_both.
Fail Next Obligation.


Notation "'encrypt_inp'" :=(
  seq int128 '× seq int128 '× int128 '× seq int128 : choice_type) (in custom pack_type at level 2).
Notation "'encrypt_inp'" :=(
  seq int128 '× seq int128 '× int128 '× seq int128 : ChoiceEquality) (at level 2).
Notation "'encrypt_out'" :=(
  seq int128 : choice_type) (in custom pack_type at level 2).
Notation "'encrypt_out'" :=(seq int128 : ChoiceEquality) (at level 2).
Definition ENCRYPT : nat :=
  1516.
Program Definition encrypt
  : both_package (CEfset ([])) [interface
  #val #[ ROUND_TO_3 ] : round_to_3_inp → round_to_3_out ] [(ENCRYPT,(
      encrypt_inp,encrypt_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(
      r_1511 , h_1512 , q_1514 , irreducible_1513) := temp_inp : seq int128 '× seq int128 '× int128 '× seq int128 in
    
    let round_to_3 := fun x_0 x_1 => package_both round_to_3 (x_0,x_1) in
    ((letb pre_1515 : seq int128 :=
          mul_poly_irr (lift_to_both0 r_1511) (lift_to_both0 h_1512) (
            lift_to_both0 irreducible_1513) (lift_to_both0 q_1514) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (round_to_3 (
            lift_to_both0 pre_1515) (lift_to_both0 q_1514))
        ) : both (CEfset ([])) [interface
      #val #[ ROUND_TO_3 ] : round_to_3_inp → round_to_3_out ] (
        seq int128)))in
  both_package' _ _ (ENCRYPT,(encrypt_inp,encrypt_out)) temp_package_both.
Fail Next Obligation.


Notation "'ntru_prime_653_encrypt_inp'" :=(
  seq int128 '× seq int128 : choice_type) (in custom pack_type at level 2).
Notation "'ntru_prime_653_encrypt_inp'" :=(
  seq int128 '× seq int128 : ChoiceEquality) (at level 2).
Notation "'ntru_prime_653_encrypt_out'" :=(
  seq int128 : choice_type) (in custom pack_type at level 2).
Notation "'ntru_prime_653_encrypt_out'" :=(
  seq int128 : ChoiceEquality) (at level 2).
Definition NTRU_PRIME_653_ENCRYPT : nat :=
  1523.
Program Definition ntru_prime_653_encrypt
  : both_package (CEfset ([])) [interface
  #val #[ BUILD_IRREDUCIBLE ] : build_irreducible_inp → build_irreducible_out ;
  #val #[ ENCRYPT ] : encrypt_inp → encrypt_out ] [(NTRU_PRIME_653_ENCRYPT,(
      ntru_prime_653_encrypt_inp,ntru_prime_653_encrypt_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(r_1521 , h_1522) := temp_inp : seq int128 '× seq int128 in
    
    let build_irreducible := fun x_0 => package_both build_irreducible (x_0) in
    let encrypt := fun x_0 x_1 x_2 x_3 => package_both encrypt (
      x_0,x_1,x_2,x_3) in
    ((letb p_1517 : uint_size := lift_to_both0 (usize 653) in
        letb q_1518 : int128 := lift_to_both0 (@repr U128 4621) in
        letb w_1519 : uint_size := lift_to_both0 (usize 288) in
        letb irreducible_1520 : seq int128 :=
          build_irreducible (lift_to_both0 p_1517) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (encrypt (
            lift_to_both0 r_1521) (lift_to_both0 h_1522) (
            lift_to_both0 q_1518) (lift_to_both0 irreducible_1520))
        ) : both (CEfset ([])) [interface
      #val #[ BUILD_IRREDUCIBLE ] : build_irreducible_inp → build_irreducible_out ;
      #val #[ ENCRYPT ] : encrypt_inp → encrypt_out ] (seq int128)))in
  both_package' _ _ (NTRU_PRIME_653_ENCRYPT,(
      ntru_prime_653_encrypt_inp,ntru_prime_653_encrypt_out)) temp_package_both.
Fail Next Obligation.

Definition r_1526_loc : ChoiceEqualityLocation :=
  (seq int128 ; 1527%nat).
Definition f_3_c_1524_loc : ChoiceEqualityLocation :=
  (seq int128 ; 1528%nat).
Definition e_1525_loc : ChoiceEqualityLocation :=
  (seq int128 ; 1529%nat).
Notation "'ntru_prime_653_decrypt_inp'" :=(
  seq int128 '× seq int128 '× seq int128 : choice_type) (in custom pack_type at level 2).
Notation "'ntru_prime_653_decrypt_inp'" :=(
  seq int128 '× seq int128 '× seq int128 : ChoiceEquality) (at level 2).
Notation "'ntru_prime_653_decrypt_out'" :=((seq int128 '× bool_ChoiceEquality
  ) : choice_type) (in custom pack_type at level 2).
Notation "'ntru_prime_653_decrypt_out'" :=((seq int128 '× bool_ChoiceEquality
  ) : ChoiceEquality) (at level 2).
Definition NTRU_PRIME_653_DECRYPT : nat :=
  1545.
Program Definition ntru_prime_653_decrypt
  : both_package (CEfset (
      [f_3_c_1524_loc ; e_1525_loc ; r_1526_loc])) [interface
  #val #[ BUILD_IRREDUCIBLE ] : build_irreducible_inp → build_irreducible_out ;
  #val #[ MAKE_POSITIVE ] : make_positive_inp → make_positive_out ] [(
    NTRU_PRIME_653_DECRYPT,(
      ntru_prime_653_decrypt_inp,ntru_prime_653_decrypt_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(
      c_1535 , key_f_1534 , key_v_1543) := temp_inp : seq int128 '× seq int128 '× seq int128 in
    
    let build_irreducible := fun x_0 => package_both build_irreducible (x_0) in
    let make_positive := fun x_0 x_1 => package_both make_positive (x_0,x_1) in
    ((letb p_1530 : uint_size := lift_to_both0 (usize 653) in
        letb q_1531 : int128 := lift_to_both0 (@repr U128 4621) in
        letb w_1532 : uint_size := lift_to_both0 (usize 288) in
        letb irreducible_1533 : seq int128 :=
          build_irreducible (lift_to_both0 p_1530) in
        letb f_c_1536 : seq int128 :=
          mul_poly_irr (lift_to_both0 key_f_1534) (lift_to_both0 c_1535) (
            lift_to_both0 irreducible_1533) (lift_to_both0 q_1531) in
        letb f_3_c_and_decryption_ok_1537 : (seq int128 '× bool_ChoiceEquality
          ) :=
          poly_to_ring (lift_to_both0 irreducible_1533) (add_poly (
              lift_to_both0 f_c_1536) (add_poly (lift_to_both0 f_c_1536) (
                lift_to_both0 f_c_1536) (lift_to_both0 q_1531)) (
              lift_to_both0 q_1531)) (lift_to_both0 q_1531) in
        letb '(f_3_c_1538, ok_decrypt_1539) : (
            seq int128 '×
            bool_ChoiceEquality
          ) :=
          lift_to_both0 f_3_c_and_decryption_ok_1537 in
        letbm f_3_c_1524 : seq int128 loc( f_3_c_1524_loc ) :=
          lift_to_both0 f_3_c_1538 in
        letb q_12_1540 : int128 :=
          ((lift_to_both0 q_1531) .- (lift_to_both0 (@repr U128 1))) ./ (
            lift_to_both0 (@repr U128 2)) in
        letb f_3_c_1524 :=
          foldi_both' (lift_to_both0 (usize 0)) (seq_len (
                lift_to_both0 f_3_c_1524)) f_3_c_1524 (L := (CEfset (
                [f_3_c_1524_loc ; e_1525_loc ; r_1526_loc]))) (I := ([interface
              #val #[ BUILD_IRREDUCIBLE ] : build_irreducible_inp → build_irreducible_out ;
              #val #[ MAKE_POSITIVE ] : make_positive_inp → make_positive_out
              ])) (fun i_1541 f_3_c_1524 =>
            letb 'f_3_c_1524 :=
              if (seq_index (f_3_c_1524) (lift_to_both0 i_1541)) >.? (
                lift_to_both0 q_12_1540) :bool_ChoiceEquality
              then lift_scope (L1 := CEfset ([f_3_c_1524_loc])) (L2 := CEfset (
                [f_3_c_1524_loc])) (I1 := [interface]) (I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
                letb f_3_c_1524 : seq int128 :=
                  seq_upd f_3_c_1524 (lift_to_both0 i_1541) (is_pure ((
                        seq_index (f_3_c_1524) (lift_to_both0 i_1541)) .- (
                        lift_to_both0 q_1531))) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                  lift_to_both0 f_3_c_1524)
                )
              else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                lift_to_both0 f_3_c_1524)
               in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 f_3_c_1524)
            ) in
        letbm e_1525 : seq int128 loc( e_1525_loc ) :=
          seq_new_ (default : int128) (seq_len (lift_to_both0 f_3_c_1524)) in
        letb e_1525 :=
          foldi_both' (lift_to_both0 (usize 0)) (seq_len (
                lift_to_both0 e_1525)) e_1525 (L := (CEfset (
                [f_3_c_1524_loc ; e_1525_loc ; r_1526_loc]))) (I := ([interface
              #val #[ BUILD_IRREDUCIBLE ] : build_irreducible_inp → build_irreducible_out ;
              #val #[ MAKE_POSITIVE ] : make_positive_inp → make_positive_out
              ])) (fun i_1542 e_1525 =>
            letb e_1525 : seq int128 :=
              seq_upd e_1525 (lift_to_both0 i_1542) (is_pure ((seq_index (
                      f_3_c_1524) (lift_to_both0 i_1542)) .% (lift_to_both0 (
                      @repr U128 3)))) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 e_1525)
            ) in
        letbm e_1525 loc( e_1525_loc ) :=
          make_positive (lift_to_both0 e_1525) (lift_to_both0 (@repr U128 3)) in
        letbm r_1526 : seq int128 loc( r_1526_loc ) :=
          mul_poly_irr (lift_to_both0 e_1525) (lift_to_both0 key_v_1543) (
            lift_to_both0 irreducible_1533) (lift_to_both0 (@repr U128 3)) in
        letb r_1526 :=
          foldi_both' (lift_to_both0 (usize 0)) (seq_len (
                lift_to_both0 r_1526)) r_1526 (L := (CEfset (
                [f_3_c_1524_loc ; e_1525_loc ; r_1526_loc]))) (I := ([interface
              #val #[ BUILD_IRREDUCIBLE ] : build_irreducible_inp → build_irreducible_out ;
              #val #[ MAKE_POSITIVE ] : make_positive_inp → make_positive_out
              ])) (fun i_1544 r_1526 =>
            letb 'r_1526 :=
              if (seq_index (r_1526) (lift_to_both0 i_1544)) =.? (
                lift_to_both0 (@repr U128 2)) :bool_ChoiceEquality
              then lift_scope (L1 := CEfset (
                [f_3_c_1524_loc ; e_1525_loc ; r_1526_loc])) (L2 := CEfset (
                [f_3_c_1524_loc ; e_1525_loc ; r_1526_loc])) (I1 := [interface]) (I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
                letb r_1526 : seq int128 :=
                  seq_upd r_1526 (lift_to_both0 i_1544) (is_pure (- (
                        lift_to_both0 (@repr U128 1)))) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                  lift_to_both0 r_1526)
                )
              else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                lift_to_both0 r_1526)
               in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 r_1526)
            ) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
            lift_to_both0 r_1526,
            lift_to_both0 ok_decrypt_1539
          ))
        ) : both (CEfset (
          [f_3_c_1524_loc ; e_1525_loc ; r_1526_loc])) [interface
      #val #[ BUILD_IRREDUCIBLE ] : build_irreducible_inp → build_irreducible_out ;
      #val #[ MAKE_POSITIVE ] : make_positive_inp → make_positive_out ] ((
          seq int128 '×
          bool_ChoiceEquality
        ))))in
  both_package' _ _ (NTRU_PRIME_653_DECRYPT,(
      ntru_prime_653_decrypt_inp,ntru_prime_653_decrypt_out)) temp_package_both.
Fail Next Obligation.

