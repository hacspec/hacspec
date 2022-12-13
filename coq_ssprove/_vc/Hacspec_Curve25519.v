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


Definition field_canvas_t := nseq (int8) (usize 32).
Definition x25519_field_element_t :=
  nat_mod 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed.

Definition scalar_canvas_t := nseq (int8) (usize 32).
Definition scalar_t :=
  nat_mod 0x8000000000000000000000000000000000000000000000000000000000000000.

Notation "'point_t'" := ((x25519_field_element_t '× x25519_field_element_t
)) : hacspec_scope.

Definition x25519_serialized_point_t := nseq (uint8) (usize 32).

Definition x25519_serialized_scalar_t := nseq (uint8) (usize 32).

Definition k_610_loc : ChoiceEqualityLocation :=
  (x25519_serialized_scalar_t ; 611%nat).
Notation "'mask_scalar_inp'" :=(
  x25519_serialized_scalar_t : choice_type) (in custom pack_type at level 2).
Notation "'mask_scalar_inp'" :=(
  x25519_serialized_scalar_t : ChoiceEquality) (at level 2).
Notation "'mask_scalar_out'" :=(
  x25519_serialized_scalar_t : choice_type) (in custom pack_type at level 2).
Notation "'mask_scalar_out'" :=(
  x25519_serialized_scalar_t : ChoiceEquality) (at level 2).
Definition MASK_SCALAR : nat :=
  613.
Program Definition mask_scalar (s_612 : x25519_serialized_scalar_t)
  : both (CEfset ([k_610_loc])) [interface] (x25519_serialized_scalar_t) :=
  ((letbm k_610 : x25519_serialized_scalar_t loc( k_610_loc ) :=
        lift_to_both0 s_612 in
      letb k_610 : x25519_serialized_scalar_t :=
        array_upd k_610 (lift_to_both0 (usize 0)) (is_pure ((array_index (
                k_610) (lift_to_both0 (usize 0))) .& (secret (lift_to_both0 (
                  @repr U8 248))))) in
      letb k_610 : x25519_serialized_scalar_t :=
        array_upd k_610 (lift_to_both0 (usize 31)) (is_pure ((array_index (
                k_610) (lift_to_both0 (usize 31))) .& (secret (lift_to_both0 (
                  @repr U8 127))))) in
      letb k_610 : x25519_serialized_scalar_t :=
        array_upd k_610 (lift_to_both0 (usize 31)) (is_pure ((array_index (
                k_610) (lift_to_both0 (usize 31))) .| (secret (lift_to_both0 (
                  @repr U8 64))))) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 k_610)
      ) : both (CEfset ([k_610_loc])) [interface] (x25519_serialized_scalar_t)).
Fail Next Obligation.


Notation "'decode_scalar_inp'" :=(
  x25519_serialized_scalar_t : choice_type) (in custom pack_type at level 2).
Notation "'decode_scalar_inp'" :=(
  x25519_serialized_scalar_t : ChoiceEquality) (at level 2).
Notation "'decode_scalar_out'" :=(
  scalar_t : choice_type) (in custom pack_type at level 2).
Notation "'decode_scalar_out'" :=(scalar_t : ChoiceEquality) (at level 2).
Definition DECODE_SCALAR : nat :=
  616.
Program Definition decode_scalar (s_614 : x25519_serialized_scalar_t)
  : both (CEfset ([k_610_loc])) [interface] (scalar_t) :=
  ((letb k_615 : x25519_serialized_scalar_t :=
        mask_scalar (lift_to_both0 s_614) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        nat_mod_from_byte_seq_le (array_to_seq (lift_to_both0 k_615)))
      ) : both (CEfset ([k_610_loc])) [interface] (scalar_t)).
Fail Next Obligation.

Definition u_617_loc : ChoiceEqualityLocation :=
  (x25519_serialized_point_t ; 618%nat).
Notation "'decode_point_inp'" :=(
  x25519_serialized_point_t : choice_type) (in custom pack_type at level 2).
Notation "'decode_point_inp'" :=(
  x25519_serialized_point_t : ChoiceEquality) (at level 2).
Notation "'decode_point_out'" :=(
  point_t : choice_type) (in custom pack_type at level 2).
Notation "'decode_point_out'" :=(point_t : ChoiceEquality) (at level 2).
Definition DECODE_POINT : nat :=
  620.
Program Definition decode_point (u_619 : x25519_serialized_point_t)
  : both (CEfset ([u_617_loc])) [interface] (point_t) :=
  ((letbm u_617 : x25519_serialized_point_t loc( u_617_loc ) :=
        lift_to_both0 u_619 in
      letb u_617 : x25519_serialized_point_t :=
        array_upd u_617 (lift_to_both0 (usize 31)) (is_pure ((array_index (
                u_617) (lift_to_both0 (usize 31))) .& (secret (lift_to_both0 (
                  @repr U8 127))))) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          nat_mod_from_byte_seq_le (array_to_seq (lift_to_both0 u_617)),
          nat_mod_from_literal (
            0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed) (
            lift_to_both0 (@repr U128 1))
        ))
      ) : both (CEfset ([u_617_loc])) [interface] (point_t)).
Fail Next Obligation.


Notation "'encode_point_inp'" :=(
  point_t : choice_type) (in custom pack_type at level 2).
Notation "'encode_point_inp'" :=(point_t : ChoiceEquality) (at level 2).
Notation "'encode_point_out'" :=(
  x25519_serialized_point_t : choice_type) (in custom pack_type at level 2).
Notation "'encode_point_out'" :=(
  x25519_serialized_point_t : ChoiceEquality) (at level 2).
Definition ENCODE_POINT : nat :=
  625.
Program Definition encode_point (p_621 : point_t)
  : both (fset.fset0) [interface] (x25519_serialized_point_t) :=
  ((letb '(x_622, y_623) : (x25519_field_element_t '× x25519_field_element_t
        ) :=
        lift_to_both0 p_621 in
      letb b_624 : x25519_field_element_t :=
        (lift_to_both0 x_622) *% (nat_mod_inv (lift_to_both0 y_623)) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (array_update_start (
          array_new_ (default : uint8) (32)) (nat_mod_to_byte_seq_le (
            lift_to_both0 b_624)))
      ) : both (fset.fset0) [interface] (x25519_serialized_point_t)).
Fail Next Obligation.


Notation "'point_add_and_double_inp'" :=(point_t '× (point_t '× point_t
  ) : choice_type) (in custom pack_type at level 2).
Notation "'point_add_and_double_inp'" :=(point_t '× (point_t '× point_t
  ) : ChoiceEquality) (at level 2).
Notation "'point_add_and_double_out'" :=((point_t '× point_t
  ) : choice_type) (in custom pack_type at level 2).
Notation "'point_add_and_double_out'" :=((point_t '× point_t
  ) : ChoiceEquality) (at level 2).
Definition POINT_ADD_AND_DOUBLE : nat :=
  650.
Program Definition point_add_and_double (q_629 : point_t) (np_626 : (
      point_t '×
      point_t
    ))
  : both (fset.fset0) [interface] ((point_t '× point_t)) :=
  ((letb '(nq_627, nqp1_628) : (point_t '× point_t) := lift_to_both0 np_626 in
      letb '(x_1_630, z_1_631) : (
          x25519_field_element_t '×
          x25519_field_element_t
        ) :=
        lift_to_both0 q_629 in
      letb '(x_2_632, z_2_633) : (
          x25519_field_element_t '×
          x25519_field_element_t
        ) :=
        lift_to_both0 nq_627 in
      letb '(x_3_634, z_3_635) : (
          x25519_field_element_t '×
          x25519_field_element_t
        ) :=
        lift_to_both0 nqp1_628 in
      letb a_636 : x25519_field_element_t :=
        (lift_to_both0 x_2_632) +% (lift_to_both0 z_2_633) in
      letb aa_637 : x25519_field_element_t :=
        nat_mod_pow (lift_to_both0 a_636) (lift_to_both0 (@repr U128 2)) in
      letb b_638 : x25519_field_element_t :=
        (lift_to_both0 x_2_632) -% (lift_to_both0 z_2_633) in
      letb bb_639 : x25519_field_element_t :=
        (lift_to_both0 b_638) *% (lift_to_both0 b_638) in
      letb e_640 : x25519_field_element_t :=
        (lift_to_both0 aa_637) -% (lift_to_both0 bb_639) in
      letb c_641 : x25519_field_element_t :=
        (lift_to_both0 x_3_634) +% (lift_to_both0 z_3_635) in
      letb d_642 : x25519_field_element_t :=
        (lift_to_both0 x_3_634) -% (lift_to_both0 z_3_635) in
      letb da_643 : x25519_field_element_t :=
        (lift_to_both0 d_642) *% (lift_to_both0 a_636) in
      letb cb_644 : x25519_field_element_t :=
        (lift_to_both0 c_641) *% (lift_to_both0 b_638) in
      letb x_3_645 : x25519_field_element_t :=
        nat_mod_pow ((lift_to_both0 da_643) +% (lift_to_both0 cb_644)) (
          lift_to_both0 (@repr U128 2)) in
      letb z_3_646 : x25519_field_element_t :=
        (lift_to_both0 x_1_630) *% (nat_mod_pow ((lift_to_both0 da_643) -% (
              lift_to_both0 cb_644)) (lift_to_both0 (@repr U128 2))) in
      letb x_2_647 : x25519_field_element_t :=
        (lift_to_both0 aa_637) *% (lift_to_both0 bb_639) in
      letb e121665_648 : x25519_field_element_t :=
        nat_mod_from_literal (
          0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed) (
          lift_to_both0 (@repr U128 121665)) in
      letb z_2_649 : x25519_field_element_t :=
        (lift_to_both0 e_640) *% ((lift_to_both0 aa_637) +% ((
              lift_to_both0 e121665_648) *% (lift_to_both0 e_640))) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          prod_b(lift_to_both0 x_2_647, lift_to_both0 z_2_649),
          prod_b(lift_to_both0 x_3_645, lift_to_both0 z_3_646)
        ))
      ) : both (fset.fset0) [interface] ((point_t '× point_t))).
Fail Next Obligation.


Notation "'swap_inp'" :=((point_t '× point_t
  ) : choice_type) (in custom pack_type at level 2).
Notation "'swap_inp'" :=((point_t '× point_t) : ChoiceEquality) (at level 2).
Notation "'swap_out'" :=((point_t '× point_t
  ) : choice_type) (in custom pack_type at level 2).
Notation "'swap_out'" :=((point_t '× point_t) : ChoiceEquality) (at level 2).
Definition SWAP : nat :=
  654.
Program Definition swap (x_651 : (point_t '× point_t))
  : both (fset.fset0) [interface] ((point_t '× point_t)) :=
  ((letb '(x0_652, x1_653) : (point_t '× point_t) := lift_to_both0 x_651 in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 x1_653,
          lift_to_both0 x0_652
        ))
      ) : both (fset.fset0) [interface] ((point_t '× point_t))).
Fail Next Obligation.

Definition acc_655_loc : ChoiceEqualityLocation :=
  ((point_t '× point_t) ; 656%nat).
Notation "'montgomery_ladder_inp'" :=(
  scalar_t '× point_t : choice_type) (in custom pack_type at level 2).
Notation "'montgomery_ladder_inp'" :=(
  scalar_t '× point_t : ChoiceEquality) (at level 2).
Notation "'montgomery_ladder_out'" :=(
  point_t : choice_type) (in custom pack_type at level 2).
Notation "'montgomery_ladder_out'" :=(point_t : ChoiceEquality) (at level 2).
Definition MONTGOMERY_LADDER : nat :=
  662.
Program Definition montgomery_ladder (k_660 : scalar_t) (init_658 : point_t)
  : both (CEfset ([acc_655_loc])) [interface] (point_t) :=
  ((letb inf_657 : (x25519_field_element_t '× x25519_field_element_t) :=
        prod_b(
          nat_mod_from_literal (
            0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed) (
            lift_to_both0 (@repr U128 1)),
          nat_mod_from_literal (
            0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed) (
            lift_to_both0 (@repr U128 0))
        ) in
      letbm acc_655 : (point_t '× point_t) loc( acc_655_loc ) :=
        prod_b(lift_to_both0 inf_657, lift_to_both0 init_658) in
      letb acc_655 :=
        foldi_both' (lift_to_both0 (usize 0)) (lift_to_both0 (
              usize 256)) acc_655 (L := (CEfset ([acc_655_loc]))) (
            I := [interface]) (fun i_659 acc_655 =>
            letb '(acc_655) :=
              if nat_mod_bit (lift_to_both0 k_660) ((lift_to_both0 (
                    usize 255)) .- (lift_to_both0 i_659)) :bool_ChoiceEquality
              then lift_scope (L1 := CEfset ([acc_655_loc])) (L2 := CEfset (
                  [acc_655_loc])) (I1 := [interface]) (
                I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
                letbm acc_655 loc( acc_655_loc ) :=
                  swap (lift_to_both0 acc_655) in
                letbm acc_655 loc( acc_655_loc ) :=
                  point_add_and_double (lift_to_both0 init_658) (
                    lift_to_both0 acc_655) in
                letbm acc_655 loc( acc_655_loc ) :=
                  swap (lift_to_both0 acc_655) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                  lift_to_both0 acc_655)
                )
              else  lift_scope (L1 := CEfset ([acc_655_loc])) (L2 := CEfset (
                  [acc_655_loc])) (I1 := [interface]) (
                I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
                letbm acc_655 loc( acc_655_loc ) :=
                  point_add_and_double (lift_to_both0 init_658) (
                    lift_to_both0 acc_655) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                  lift_to_both0 acc_655)
                ) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 acc_655)
            ) in
      letb '(out_661, _) : (
          (x25519_field_element_t '× x25519_field_element_t) '×
          point_t
        ) :=
        lift_to_both0 acc_655 in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 out_661)
      ) : both (CEfset ([acc_655_loc])) [interface] (point_t)).
Fail Next Obligation.


Notation "'x25519_scalarmult_inp'" :=(
  x25519_serialized_scalar_t '× x25519_serialized_point_t : choice_type) (in custom pack_type at level 2).
Notation "'x25519_scalarmult_inp'" :=(
  x25519_serialized_scalar_t '× x25519_serialized_point_t : ChoiceEquality) (at level 2).
Notation "'x25519_scalarmult_out'" :=(
  x25519_serialized_point_t : choice_type) (in custom pack_type at level 2).
Notation "'x25519_scalarmult_out'" :=(
  x25519_serialized_point_t : ChoiceEquality) (at level 2).
Definition X25519_SCALARMULT : nat :=
  668.
Program Definition x25519_scalarmult (s_663 : x25519_serialized_scalar_t) (
    p_665 : x25519_serialized_point_t)
  : both (CEfset ([k_610_loc ; u_617_loc ; acc_655_loc])) [interface] (
    x25519_serialized_point_t) :=
  ((letb s_664 : scalar_t := decode_scalar (lift_to_both0 s_663) in
      letb p_666 : (x25519_field_element_t '× x25519_field_element_t) :=
        decode_point (lift_to_both0 p_665) in
      letb r_667 : (x25519_field_element_t '× x25519_field_element_t) :=
        montgomery_ladder (lift_to_both0 s_664) (lift_to_both0 p_666) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (encode_point (
          lift_to_both0 r_667))
      ) : both (CEfset ([k_610_loc ; u_617_loc ; acc_655_loc])) [interface] (
      x25519_serialized_point_t)).
Fail Next Obligation.

Definition base_669_loc : ChoiceEqualityLocation :=
  (x25519_serialized_point_t ; 670%nat).
Notation "'x25519_secret_to_public_inp'" :=(
  x25519_serialized_scalar_t : choice_type) (in custom pack_type at level 2).
Notation "'x25519_secret_to_public_inp'" :=(
  x25519_serialized_scalar_t : ChoiceEquality) (at level 2).
Notation "'x25519_secret_to_public_out'" :=(
  x25519_serialized_point_t : choice_type) (in custom pack_type at level 2).
Notation "'x25519_secret_to_public_out'" :=(
  x25519_serialized_point_t : ChoiceEquality) (at level 2).
Definition X25519_SECRET_TO_PUBLIC : nat :=
  672.
Program Definition x25519_secret_to_public (s_671 : x25519_serialized_scalar_t)
  : both (CEfset (
      [k_610_loc ; u_617_loc ; acc_655_loc ; base_669_loc])) [interface] (
    x25519_serialized_point_t) :=
  ((letbm base_669 : x25519_serialized_point_t loc( base_669_loc ) :=
        array_new_ (default : uint8) (32) in
      letb base_669 : x25519_serialized_point_t :=
        array_upd base_669 (lift_to_both0 (usize 0)) (is_pure (secret (
              lift_to_both0 (@repr U8 9)))) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (x25519_scalarmult (
          lift_to_both0 s_671) (lift_to_both0 base_669))
      ) : both (CEfset (
        [k_610_loc ; u_617_loc ; acc_655_loc ; base_669_loc])) [interface] (
      x25519_serialized_point_t)).
Fail Next Obligation.

