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


Definition irr_1619_loc : ChoiceEqualityLocation :=
  (seq int128 ; 1620%nat).
Notation "'build_irreducible_inp'" :=(
  uint_size : choice_type) (in custom pack_type at level 2).
Notation "'build_irreducible_inp'" :=(uint_size : ChoiceEquality) (at level 2).
Notation "'build_irreducible_out'" :=(
  seq int128 : choice_type) (in custom pack_type at level 2).
Notation "'build_irreducible_out'" :=(seq int128 : ChoiceEquality) (at level 2).
Definition BUILD_IRREDUCIBLE : nat :=
  1622.
Program Definition build_irreducible (p_1621 : uint_size)
  : both (CEfset ([irr_1619_loc])) [interface] (seq int128) :=
  ((letbm irr_1619 : seq int128 loc( irr_1619_loc ) :=
        seq_new_ (default : int128) ((lift_to_both0 p_1621) .+ (lift_to_both0 (
              usize 1))) in
      letb irr_1619 : seq int128 :=
        seq_upd irr_1619 (lift_to_both0 (usize 0)) (is_pure (- (lift_to_both0 (
                @repr U128 1)))) in
      letb irr_1619 : seq int128 :=
        seq_upd irr_1619 (lift_to_both0 (usize 1)) (is_pure (- (lift_to_both0 (
                @repr U128 1)))) in
      letb irr_1619 : seq int128 :=
        seq_upd irr_1619 (lift_to_both0 p_1621) (is_pure (lift_to_both0 (
              @repr U128 1))) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 irr_1619)
      ) : both (CEfset ([irr_1619_loc])) [interface] (seq int128)).
Fail Next Obligation.

Definition result_1623_loc : ChoiceEqualityLocation :=
  (seq int128 ; 1624%nat).
Notation "'round_to_3_inp'" :=(
  seq int128 '× int128 : choice_type) (in custom pack_type at level 2).
Notation "'round_to_3_inp'" :=(
  seq int128 '× int128 : ChoiceEquality) (at level 2).
Notation "'round_to_3_out'" :=(
  seq int128 : choice_type) (in custom pack_type at level 2).
Notation "'round_to_3_out'" :=(seq int128 : ChoiceEquality) (at level 2).
Definition ROUND_TO_3 : nat :=
  1630.
Program Definition round_to_3 (poly_1625 : seq int128) (q_1626 : int128)
  : both (CEfset ([result_1623_loc])) [interface] (seq int128) :=
  ((letbm result_1623 : seq int128 loc( result_1623_loc ) :=
        (lift_to_both0 poly_1625) in
      letb q_12_1627 : int128 :=
        ((lift_to_both0 q_1626) .- (lift_to_both0 (@repr U128 1))) ./ (
          lift_to_both0 (@repr U128 2)) in
      letb result_1623 :=
        foldi_both' (lift_to_both0 (usize 0)) (seq_len (
              lift_to_both0 poly_1625)) result_1623 (L := (CEfset (
                [result_1623_loc]))) (I := [interface]) (
            fun i_1628 result_1623 =>
            letb '(result_1623) :=
              if (seq_index (poly_1625) (lift_to_both0 i_1628)) >.? (
                lift_to_both0 q_12_1627) :bool_ChoiceEquality
              then lift_scope (L1 := CEfset ([result_1623_loc])) (L2 := CEfset (
                  [result_1623_loc])) (I1 := [interface]) (
                I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
                letb result_1623 : seq int128 :=
                  seq_upd result_1623 (lift_to_both0 i_1628) (is_pure ((
                        seq_index (poly_1625) (lift_to_both0 i_1628)) .- (
                        lift_to_both0 q_1626))) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                  lift_to_both0 result_1623)
                )
              else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                lift_to_both0 result_1623)
               in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 result_1623)
            ) in
      letb result_1623 :=
        foldi_both' (lift_to_both0 (usize 0)) (seq_len (
              lift_to_both0 result_1623)) result_1623 (L := (CEfset (
                [result_1623_loc]))) (I := [interface]) (
            fun i_1629 result_1623 =>
            letb '(result_1623) :=
              if ((seq_index (result_1623) (lift_to_both0 i_1629)) .% (
                  lift_to_both0 (@repr U128 3))) !=.? (lift_to_both0 (
                  @repr U128 0)) :bool_ChoiceEquality
              then lift_scope (L1 := CEfset ([result_1623_loc])) (L2 := CEfset (
                  [result_1623_loc])) (I1 := [interface]) (
                I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
                letb result_1623 : seq int128 :=
                  seq_upd result_1623 (lift_to_both0 i_1629) (is_pure ((
                        seq_index (result_1623) (lift_to_both0 i_1629)) .- (
                        lift_to_both0 (@repr U128 1)))) in
                letb '(result_1623) :=
                  if ((seq_index (result_1623) (lift_to_both0 i_1629)) .% (
                      lift_to_both0 (@repr U128 3))) !=.? (lift_to_both0 (
                      @repr U128 0)) :bool_ChoiceEquality
                  then lift_scope (L1 := CEfset ([result_1623_loc])) (
                    L2 := CEfset ([result_1623_loc])) (I1 := [interface]) (
                    I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
                    letb result_1623 : seq int128 :=
                      seq_upd result_1623 (lift_to_both0 i_1629) (is_pure ((
                            seq_index (result_1623) (lift_to_both0 i_1629)) .+ (
                            lift_to_both0 (@repr U128 2)))) in
                    lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                      lift_to_both0 result_1623)
                    )
                  else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                    lift_to_both0 result_1623)
                   in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                  lift_to_both0 result_1623)
                )
              else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                lift_to_both0 result_1623)
               in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 result_1623)
            ) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        lift_to_both0 result_1623)
      ) : both (CEfset ([result_1623_loc])) [interface] (seq int128)).
Fail Next Obligation.


Notation "'encrypt_inp'" :=(
  seq int128 '× seq int128 '× int128 '× seq int128 : choice_type) (in custom pack_type at level 2).
Notation "'encrypt_inp'" :=(
  seq int128 '× seq int128 '× int128 '× seq int128 : ChoiceEquality) (at level 2).
Notation "'encrypt_out'" :=(
  seq int128 : choice_type) (in custom pack_type at level 2).
Notation "'encrypt_out'" :=(seq int128 : ChoiceEquality) (at level 2).
Definition ENCRYPT : nat :=
  1636.
Program Definition encrypt (r_1631 : seq int128) (h_1632 : seq int128) (
    q_1634 : int128) (irreducible_1633 : seq int128)
  : both (CEfset ([result_1623_loc])) [interface] (seq int128) :=
  ((letb pre_1635 : seq int128 :=
        mul_poly_irr (lift_to_both0 r_1631) (lift_to_both0 h_1632) (
          lift_to_both0 irreducible_1633) (lift_to_both0 q_1634) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (round_to_3 (
          lift_to_both0 pre_1635) (lift_to_both0 q_1634))
      ) : both (CEfset ([result_1623_loc])) [interface] (seq int128)).
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
  1643.
Program Definition ntru_prime_653_encrypt (r_1641 : seq int128) (
    h_1642 : seq int128)
  : both (CEfset ([irr_1619_loc ; result_1623_loc])) [interface] (seq int128) :=
  ((letb p_1637 : uint_size := lift_to_both0 (usize 653) in
      letb q_1638 : int128 := lift_to_both0 (@repr U128 4621) in
      letb w_1639 : uint_size := lift_to_both0 (usize 288) in
      letb irreducible_1640 : seq int128 :=
        build_irreducible (lift_to_both0 p_1637) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (encrypt (
          lift_to_both0 r_1641) (lift_to_both0 h_1642) (lift_to_both0 q_1638) (
          lift_to_both0 irreducible_1640))
      ) : both (CEfset ([irr_1619_loc ; result_1623_loc])) [interface] (
      seq int128)).
Fail Next Obligation.

Definition f_3_c_1644_loc : ChoiceEqualityLocation :=
  (seq int128 ; 1647%nat).
Definition r_1646_loc : ChoiceEqualityLocation :=
  (seq int128 ; 1648%nat).
Definition e_1645_loc : ChoiceEqualityLocation :=
  (seq int128 ; 1649%nat).
Notation "'ntru_prime_653_decrypt_inp'" :=(
  seq int128 '× seq int128 '× seq int128 : choice_type) (in custom pack_type at level 2).
Notation "'ntru_prime_653_decrypt_inp'" :=(
  seq int128 '× seq int128 '× seq int128 : ChoiceEquality) (at level 2).
Notation "'ntru_prime_653_decrypt_out'" :=((seq int128 '× bool_ChoiceEquality
  ) : choice_type) (in custom pack_type at level 2).
Notation "'ntru_prime_653_decrypt_out'" :=((seq int128 '× bool_ChoiceEquality
  ) : ChoiceEquality) (at level 2).
Definition NTRU_PRIME_653_DECRYPT : nat :=
  1665.
Program Definition ntru_prime_653_decrypt (c_1655 : seq int128) (
    key_f_1654 : seq int128) (key_v_1663 : seq int128)
  : both (CEfset (
      [irr_1619_loc ; f_3_c_1644_loc ; e_1645_loc ; r_1646_loc])) [interface] ((
      seq int128 '×
      bool_ChoiceEquality
    )) :=
  ((letb p_1650 : uint_size := lift_to_both0 (usize 653) in
      letb q_1651 : int128 := lift_to_both0 (@repr U128 4621) in
      letb w_1652 : uint_size := lift_to_both0 (usize 288) in
      letb irreducible_1653 : seq int128 :=
        build_irreducible (lift_to_both0 p_1650) in
      letb f_c_1656 : seq int128 :=
        mul_poly_irr (lift_to_both0 key_f_1654) (lift_to_both0 c_1655) (
          lift_to_both0 irreducible_1653) (lift_to_both0 q_1651) in
      letb f_3_c_and_decryption_ok_1657 : (seq int128 '× bool_ChoiceEquality
        ) :=
        poly_to_ring (lift_to_both0 irreducible_1653) (add_poly (
            lift_to_both0 f_c_1656) (add_poly (lift_to_both0 f_c_1656) (
              lift_to_both0 f_c_1656) (lift_to_both0 q_1651)) (
            lift_to_both0 q_1651)) (lift_to_both0 q_1651) in
      letb '(f_3_c_1658, ok_decrypt_1659) : (seq int128 '× bool_ChoiceEquality
        ) :=
        lift_to_both0 f_3_c_and_decryption_ok_1657 in
      letbm f_3_c_1644 : seq int128 loc( f_3_c_1644_loc ) :=
        lift_to_both0 f_3_c_1658 in
      letb q_12_1660 : int128 :=
        ((lift_to_both0 q_1651) .- (lift_to_both0 (@repr U128 1))) ./ (
          lift_to_both0 (@repr U128 2)) in
      letb f_3_c_1644 :=
        foldi_both' (lift_to_both0 (usize 0)) (seq_len (
              lift_to_both0 f_3_c_1644)) f_3_c_1644 (L := (CEfset (
                [irr_1619_loc ; f_3_c_1644_loc ; e_1645_loc ; r_1646_loc]))) (
            I := [interface]) (fun i_1661 f_3_c_1644 =>
            letb '(f_3_c_1644) :=
              if (seq_index (f_3_c_1644) (lift_to_both0 i_1661)) >.? (
                lift_to_both0 q_12_1660) :bool_ChoiceEquality
              then lift_scope (L1 := CEfset ([irr_1619_loc ; f_3_c_1644_loc])) (
                L2 := CEfset ([irr_1619_loc ; f_3_c_1644_loc])) (
                I1 := [interface]) (
                I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
                letb f_3_c_1644 : seq int128 :=
                  seq_upd f_3_c_1644 (lift_to_both0 i_1661) (is_pure ((
                        seq_index (f_3_c_1644) (lift_to_both0 i_1661)) .- (
                        lift_to_both0 q_1651))) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                  lift_to_both0 f_3_c_1644)
                )
              else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                lift_to_both0 f_3_c_1644)
               in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 f_3_c_1644)
            ) in
      letbm e_1645 : seq int128 loc( e_1645_loc ) :=
        seq_new_ (default : int128) (seq_len (lift_to_both0 f_3_c_1644)) in
      letb e_1645 :=
        foldi_both' (lift_to_both0 (usize 0)) (seq_len (
              lift_to_both0 e_1645)) e_1645 (L := (CEfset (
                [irr_1619_loc ; f_3_c_1644_loc ; e_1645_loc ; r_1646_loc]))) (
            I := [interface]) (fun i_1662 e_1645 =>
            letb e_1645 : seq int128 :=
              seq_upd e_1645 (lift_to_both0 i_1662) (is_pure ((seq_index (
                      f_3_c_1644) (lift_to_both0 i_1662)) .% (lift_to_both0 (
                      @repr U128 3)))) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 e_1645)
            ) in
      letbm e_1645 loc( e_1645_loc ) :=
        make_positive (lift_to_both0 e_1645) (lift_to_both0 (@repr U128 3)) in
      letbm r_1646 : seq int128 loc( r_1646_loc ) :=
        mul_poly_irr (lift_to_both0 e_1645) (lift_to_both0 key_v_1663) (
          lift_to_both0 irreducible_1653) (lift_to_both0 (@repr U128 3)) in
      letb r_1646 :=
        foldi_both' (lift_to_both0 (usize 0)) (seq_len (
              lift_to_both0 r_1646)) r_1646 (L := (CEfset (
                [irr_1619_loc ; f_3_c_1644_loc ; e_1645_loc ; r_1646_loc]))) (
            I := [interface]) (fun i_1664 r_1646 =>
            letb '(r_1646) :=
              if (seq_index (r_1646) (lift_to_both0 i_1664)) =.? (
                lift_to_both0 (@repr U128 2)) :bool_ChoiceEquality
              then lift_scope (L1 := CEfset (
                  [irr_1619_loc ; f_3_c_1644_loc ; e_1645_loc ; r_1646_loc])) (
                L2 := CEfset (
                  [irr_1619_loc ; f_3_c_1644_loc ; e_1645_loc ; r_1646_loc])) (
                I1 := [interface]) (
                I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
                letb r_1646 : seq int128 :=
                  seq_upd r_1646 (lift_to_both0 i_1664) (is_pure (- (
                        lift_to_both0 (@repr U128 1)))) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                  lift_to_both0 r_1646)
                )
              else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                lift_to_both0 r_1646)
               in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 r_1646)
            ) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 r_1646,
          lift_to_both0 ok_decrypt_1659
        ))
      ) : both (CEfset (
        [irr_1619_loc ; f_3_c_1644_loc ; e_1645_loc ; r_1646_loc])) [interface] (
      (seq int128 '× bool_ChoiceEquality))).
Fail Next Obligation.

