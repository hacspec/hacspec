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


Definition error_t : ChoiceEquality :=
  unit_ChoiceEquality.
Definition InvalidAddition : error_t :=
   tt.

Definition bits_v : uint_size :=
  usize 256.

Definition field_canvas_t := nseq (int8) (usize 32).
Definition p256_field_element_t :=
  nat_mod 0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff.

Definition scalar_canvas_t := nseq (int8) (usize 32).
Definition p256_scalar_t :=
  nat_mod 0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551.

Notation "'affine_t'" := ((p256_field_element_t '× p256_field_element_t
)) : hacspec_scope.

Notation "'affine_result_t'" := ((result error_t affine_t)) : hacspec_scope.

Notation "'p256_jacobian_t'" := ((
  p256_field_element_t '×
  p256_field_element_t '×
  p256_field_element_t
)) : hacspec_scope.

Notation "'jacobian_result_t'" := ((
  result error_t p256_jacobian_t)) : hacspec_scope.

Definition element_t := nseq (uint8) (usize 32).


Notation "'jacobian_to_affine_inp'" :=(
  p256_jacobian_t : choice_type) (in custom pack_type at level 2).
Notation "'jacobian_to_affine_inp'" :=(
  p256_jacobian_t : ChoiceEquality) (at level 2).
Notation "'jacobian_to_affine_out'" :=(
  affine_t : choice_type) (in custom pack_type at level 2).
Notation "'jacobian_to_affine_out'" :=(affine_t : ChoiceEquality) (at level 2).
Definition JACOBIAN_TO_AFFINE : nat :=
  730.
Program Definition jacobian_to_affine (p_720 : p256_jacobian_t)
  : both (fset.fset0) [interface] (affine_t) :=
  ((letb '(x_721, y_722, z_723) : (
          p256_field_element_t '×
          p256_field_element_t '×
          p256_field_element_t
        ) :=
        lift_to_both0 p_720 in
      letb z2_724 : p256_field_element_t :=
        nat_mod_exp (lift_to_both0 z_723) (lift_to_both0 (@repr U32 2)) in
      letb z2i_725 : p256_field_element_t :=
        nat_mod_inv (lift_to_both0 z2_724) in
      letb z3_726 : p256_field_element_t :=
        (lift_to_both0 z_723) *% (lift_to_both0 z2_724) in
      letb z3i_727 : p256_field_element_t :=
        nat_mod_inv (lift_to_both0 z3_726) in
      letb x_728 : p256_field_element_t :=
        (lift_to_both0 x_721) *% (lift_to_both0 z2i_725) in
      letb y_729 : p256_field_element_t :=
        (lift_to_both0 y_722) *% (lift_to_both0 z3i_727) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 x_728,
          lift_to_both0 y_729
        ))
      ) : both (fset.fset0) [interface] (affine_t)).
Fail Next Obligation.


Notation "'affine_to_jacobian_inp'" :=(
  affine_t : choice_type) (in custom pack_type at level 2).
Notation "'affine_to_jacobian_inp'" :=(affine_t : ChoiceEquality) (at level 2).
Notation "'affine_to_jacobian_out'" :=(
  p256_jacobian_t : choice_type) (in custom pack_type at level 2).
Notation "'affine_to_jacobian_out'" :=(
  p256_jacobian_t : ChoiceEquality) (at level 2).
Definition AFFINE_TO_JACOBIAN : nat :=
  734.
Program Definition affine_to_jacobian (p_731 : affine_t)
  : both (fset.fset0) [interface] (p256_jacobian_t) :=
  ((letb '(x_732, y_733) : (p256_field_element_t '× p256_field_element_t) :=
        lift_to_both0 p_731 in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 x_732,
          lift_to_both0 y_733,
          nat_mod_from_literal (
            0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
            lift_to_both0 (@repr U128 1))
        ))
      ) : both (fset.fset0) [interface] (p256_jacobian_t)).
Fail Next Obligation.


Notation "'point_double_inp'" :=(
  p256_jacobian_t : choice_type) (in custom pack_type at level 2).
Notation "'point_double_inp'" :=(p256_jacobian_t : ChoiceEquality) (at level 2).
Notation "'point_double_out'" :=(
  p256_jacobian_t : choice_type) (in custom pack_type at level 2).
Notation "'point_double_out'" :=(p256_jacobian_t : ChoiceEquality) (at level 2).
Definition POINT_DOUBLE : nat :=
  751.
Program Definition point_double (p_735 : p256_jacobian_t)
  : both (fset.fset0) [interface] (p256_jacobian_t) :=
  ((letb '(x1_736, y1_737, z1_738) : (
          p256_field_element_t '×
          p256_field_element_t '×
          p256_field_element_t
        ) :=
        lift_to_both0 p_735 in
      letb delta_739 : p256_field_element_t :=
        nat_mod_exp (lift_to_both0 z1_738) (lift_to_both0 (@repr U32 2)) in
      letb gamma_740 : p256_field_element_t :=
        nat_mod_exp (lift_to_both0 y1_737) (lift_to_both0 (@repr U32 2)) in
      letb beta_741 : p256_field_element_t :=
        (lift_to_both0 x1_736) *% (lift_to_both0 gamma_740) in
      letb alpha_1_742 : p256_field_element_t :=
        (lift_to_both0 x1_736) -% (lift_to_both0 delta_739) in
      letb alpha_2_743 : p256_field_element_t :=
        (lift_to_both0 x1_736) +% (lift_to_both0 delta_739) in
      letb alpha_744 : p256_field_element_t :=
        (nat_mod_from_literal (
            0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
            lift_to_both0 (@repr U128 3))) *% ((lift_to_both0 alpha_1_742) *% (
            lift_to_both0 alpha_2_743)) in
      letb x3_745 : p256_field_element_t :=
        (nat_mod_exp (lift_to_both0 alpha_744) (lift_to_both0 (
              @repr U32 2))) -% ((nat_mod_from_literal (
              0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
              lift_to_both0 (@repr U128 8))) *% (lift_to_both0 beta_741)) in
      letb z3_746 : p256_field_element_t :=
        nat_mod_exp ((lift_to_both0 y1_737) +% (lift_to_both0 z1_738)) (
          lift_to_both0 (@repr U32 2)) in
      letb z3_747 : p256_field_element_t :=
        (lift_to_both0 z3_746) -% ((lift_to_both0 gamma_740) +% (
            lift_to_both0 delta_739)) in
      letb y3_1_748 : p256_field_element_t :=
        ((nat_mod_from_literal (
              0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
              lift_to_both0 (@repr U128 4))) *% (lift_to_both0 beta_741)) -% (
          lift_to_both0 x3_745) in
      letb y3_2_749 : p256_field_element_t :=
        (nat_mod_from_literal (
            0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
            lift_to_both0 (@repr U128 8))) *% ((lift_to_both0 gamma_740) *% (
            lift_to_both0 gamma_740)) in
      letb y3_750 : p256_field_element_t :=
        ((lift_to_both0 alpha_744) *% (lift_to_both0 y3_1_748)) -% (
          lift_to_both0 y3_2_749) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 x3_745,
          lift_to_both0 y3_750,
          lift_to_both0 z3_747
        ))
      ) : both (fset.fset0) [interface] (p256_jacobian_t)).
Fail Next Obligation.


Notation "'is_point_at_infinity_inp'" :=(
  p256_jacobian_t : choice_type) (in custom pack_type at level 2).
Notation "'is_point_at_infinity_inp'" :=(
  p256_jacobian_t : ChoiceEquality) (at level 2).
Notation "'is_point_at_infinity_out'" :=(
  bool_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'is_point_at_infinity_out'" :=(
  bool_ChoiceEquality : ChoiceEquality) (at level 2).
Definition IS_POINT_AT_INFINITY : nat :=
  756.
Program Definition is_point_at_infinity (p_752 : p256_jacobian_t)
  : both (fset.fset0) [interface] (bool_ChoiceEquality) :=
  ((letb '(x_753, y_754, z_755) : (
          p256_field_element_t '×
          p256_field_element_t '×
          p256_field_element_t
        ) :=
        lift_to_both0 p_752 in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (nat_mod_equal (
          lift_to_both0 z_755) (nat_mod_from_literal (
            0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
            lift_to_both0 (@repr U128 0))))
      ) : both (fset.fset0) [interface] (bool_ChoiceEquality)).
Fail Next Obligation.


Notation "'s1_equal_s2_inp'" :=(
  p256_field_element_t '× p256_field_element_t : choice_type) (in custom pack_type at level 2).
Notation "'s1_equal_s2_inp'" :=(
  p256_field_element_t '× p256_field_element_t : ChoiceEquality) (at level 2).
Notation "'s1_equal_s2_out'" :=(
  jacobian_result_t : choice_type) (in custom pack_type at level 2).
Notation "'s1_equal_s2_out'" :=(
  jacobian_result_t : ChoiceEquality) (at level 2).
Definition S1_EQUAL_S2 : nat :=
  759.
Program Definition s1_equal_s2 (s1_757 : p256_field_element_t) (
    s2_758 : p256_field_element_t)
  : both (fset.fset0) [interface] (jacobian_result_t) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        if is_pure (I := [interface]) (nat_mod_equal (lift_to_both0 s1_757) (
            lift_to_both0 s2_758))
        then @Err p256_jacobian_t error_t (InvalidAddition)
        else @Ok p256_jacobian_t error_t (prod_b(
            nat_mod_from_literal (
              0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
              lift_to_both0 (@repr U128 0)),
            nat_mod_from_literal (
              0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
              lift_to_both0 (@repr U128 1)),
            nat_mod_from_literal (
              0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
              lift_to_both0 (@repr U128 0))
          )))
      ) : both (fset.fset0) [interface] (jacobian_result_t)).
Fail Next Obligation.

Definition result_760_loc : ChoiceEqualityLocation :=
  ((result (error_t) (p256_jacobian_t)) ; 761%nat).
Notation "'point_add_jacob_inp'" :=(
  p256_jacobian_t '× p256_jacobian_t : choice_type) (in custom pack_type at level 2).
Notation "'point_add_jacob_inp'" :=(
  p256_jacobian_t '× p256_jacobian_t : ChoiceEquality) (at level 2).
Notation "'point_add_jacob_out'" :=(
  jacobian_result_t : choice_type) (in custom pack_type at level 2).
Notation "'point_add_jacob_out'" :=(
  jacobian_result_t : ChoiceEquality) (at level 2).
Definition POINT_ADD_JACOB : nat :=
  789.
Program Definition point_add_jacob (p_763 : p256_jacobian_t) (
    q_762 : p256_jacobian_t)
  : both (CEfset ([result_760_loc])) [interface] (jacobian_result_t) :=
  ((letbm result_760 : (result (error_t) (
            p256_jacobian_t)) loc( result_760_loc ) :=
        @Ok p256_jacobian_t error_t (lift_to_both0 q_762) in
      letb '(result_760) :=
        if negb (is_point_at_infinity (
            lift_to_both0 p_763)) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset ([result_760_loc])) (L2 := CEfset (
            [result_760_loc])) (I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (letb '(
              result_760
            ) :=
            if is_point_at_infinity (lift_to_both0 q_762) :bool_ChoiceEquality
            then lift_scope (L1 := CEfset ([result_760_loc])) (L2 := CEfset (
                [result_760_loc])) (I1 := [interface]) (
              I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
              letbm result_760 loc( result_760_loc ) :=
                @Ok p256_jacobian_t error_t (lift_to_both0 p_763) in
              lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                lift_to_both0 result_760)
              )
            else  lift_scope (L1 := CEfset ([result_760_loc])) (L2 := CEfset (
                [result_760_loc])) (I1 := [interface]) (
              I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (letb '(
                  x1_764,
                  y1_765,
                  z1_766
                ) : (
                  p256_field_element_t '×
                  p256_field_element_t '×
                  p256_field_element_t
                ) :=
                lift_to_both0 p_763 in
              letb '(x2_767, y2_768, z2_769) : (
                  p256_field_element_t '×
                  p256_field_element_t '×
                  p256_field_element_t
                ) :=
                lift_to_both0 q_762 in
              letb z1z1_770 : p256_field_element_t :=
                nat_mod_exp (lift_to_both0 z1_766) (lift_to_both0 (
                    @repr U32 2)) in
              letb z2z2_771 : p256_field_element_t :=
                nat_mod_exp (lift_to_both0 z2_769) (lift_to_both0 (
                    @repr U32 2)) in
              letb u1_772 : p256_field_element_t :=
                (lift_to_both0 x1_764) *% (lift_to_both0 z2z2_771) in
              letb u2_773 : p256_field_element_t :=
                (lift_to_both0 x2_767) *% (lift_to_both0 z1z1_770) in
              letb s1_774 : p256_field_element_t :=
                ((lift_to_both0 y1_765) *% (lift_to_both0 z2_769)) *% (
                  lift_to_both0 z2z2_771) in
              letb s2_775 : p256_field_element_t :=
                ((lift_to_both0 y2_768) *% (lift_to_both0 z1_766)) *% (
                  lift_to_both0 z1z1_770) in
              letb '(result_760) :=
                if nat_mod_equal (lift_to_both0 u1_772) (
                  lift_to_both0 u2_773) :bool_ChoiceEquality
                then lift_scope (L1 := CEfset ([result_760_loc])) (
                  L2 := CEfset ([result_760_loc])) (I1 := [interface]) (
                  I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
                  letbm result_760 loc( result_760_loc ) :=
                    s1_equal_s2 (lift_to_both0 s1_774) (lift_to_both0 s2_775) in
                  lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                    lift_to_both0 result_760)
                  )
                else  lift_scope (L1 := CEfset ([result_760_loc])) (
                  L2 := CEfset ([result_760_loc])) (I1 := [interface]) (
                  I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
                  letb h_776 : p256_field_element_t :=
                    (lift_to_both0 u2_773) -% (lift_to_both0 u1_772) in
                  letb i_777 : p256_field_element_t :=
                    nat_mod_exp ((nat_mod_from_literal (
                          0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
                          lift_to_both0 (@repr U128 2))) *% (
                        lift_to_both0 h_776)) (lift_to_both0 (@repr U32 2)) in
                  letb j_778 : p256_field_element_t :=
                    (lift_to_both0 h_776) *% (lift_to_both0 i_777) in
                  letb r_779 : p256_field_element_t :=
                    (nat_mod_from_literal (
                        0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
                        lift_to_both0 (@repr U128 2))) *% ((
                        lift_to_both0 s2_775) -% (lift_to_both0 s1_774)) in
                  letb v_780 : p256_field_element_t :=
                    (lift_to_both0 u1_772) *% (lift_to_both0 i_777) in
                  letb x3_1_781 : p256_field_element_t :=
                    (nat_mod_from_literal (
                        0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
                        lift_to_both0 (@repr U128 2))) *% (
                      lift_to_both0 v_780) in
                  letb x3_2_782 : p256_field_element_t :=
                    (nat_mod_exp (lift_to_both0 r_779) (lift_to_both0 (
                          @repr U32 2))) -% (lift_to_both0 j_778) in
                  letb x3_783 : p256_field_element_t :=
                    (lift_to_both0 x3_2_782) -% (lift_to_both0 x3_1_781) in
                  letb y3_1_784 : p256_field_element_t :=
                    ((nat_mod_from_literal (
                          0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
                          lift_to_both0 (@repr U128 2))) *% (
                        lift_to_both0 s1_774)) *% (lift_to_both0 j_778) in
                  letb y3_2_785 : p256_field_element_t :=
                    (lift_to_both0 r_779) *% ((lift_to_both0 v_780) -% (
                        lift_to_both0 x3_783)) in
                  letb y3_786 : p256_field_element_t :=
                    (lift_to_both0 y3_2_785) -% (lift_to_both0 y3_1_784) in
                  letb z3_787 : p256_field_element_t :=
                    nat_mod_exp ((lift_to_both0 z1_766) +% (
                        lift_to_both0 z2_769)) (lift_to_both0 (@repr U32 2)) in
                  letb z3_788 : p256_field_element_t :=
                    ((lift_to_both0 z3_787) -% ((lift_to_both0 z1z1_770) +% (
                          lift_to_both0 z2z2_771))) *% (lift_to_both0 h_776) in
                  letbm result_760 loc( result_760_loc ) :=
                    @Ok p256_jacobian_t error_t (prod_b(
                        lift_to_both0 x3_783,
                        lift_to_both0 y3_786,
                        lift_to_both0 z3_788
                      )) in
                  lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                    lift_to_both0 result_760)
                  ) in
              lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                lift_to_both0 result_760)
              ) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 result_760)
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          lift_to_both0 result_760)
         in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        lift_to_both0 result_760)
      ) : both (CEfset ([result_760_loc])) [interface] (jacobian_result_t)).
Fail Next Obligation.

Definition q_790_loc : ChoiceEqualityLocation :=
  ((p256_field_element_t '× p256_field_element_t '× p256_field_element_t
    ) ; 791%nat).
Notation "'ltr_mul_inp'" :=(
  p256_scalar_t '× p256_jacobian_t : choice_type) (in custom pack_type at level 2).
Notation "'ltr_mul_inp'" :=(
  p256_scalar_t '× p256_jacobian_t : ChoiceEquality) (at level 2).
Notation "'ltr_mul_out'" :=(
  jacobian_result_t : choice_type) (in custom pack_type at level 2).
Notation "'ltr_mul_out'" :=(jacobian_result_t : ChoiceEquality) (at level 2).
Definition LTR_MUL : nat :=
  795.
Program Definition ltr_mul (k_793 : p256_scalar_t) (p_794 : p256_jacobian_t)
  : both (CEfset ([result_760_loc ; q_790_loc])) [interface] (
    jacobian_result_t) :=
  ((letbm q_790 : (
          p256_field_element_t '×
          p256_field_element_t '×
          p256_field_element_t
        ) loc( q_790_loc ) :=
        prod_b(
          nat_mod_from_literal (
            0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
            lift_to_both0 (@repr U128 0)),
          nat_mod_from_literal (
            0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
            lift_to_both0 (@repr U128 1)),
          nat_mod_from_literal (
            0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
            lift_to_both0 (@repr U128 0))
        ) in
      letbnd(ChoiceEqualityMonad.result_bind_both error_t) q_790 :=
        foldi_bind_both' (lift_to_both0 (usize 0)) (
            lift_to_both0 bits_v) q_790 (L := (CEfset (
                [result_760_loc ; q_790_loc]))) (I := [interface]) (
            fun i_792 q_790 =>
            letbm q_790 loc( q_790_loc ) :=
              point_double (lift_to_both0 q_790) in
            letbnd(ChoiceEqualityMonad.result_bind_both error_t) '(q_790) :=
              if nat_mod_equal (nat_mod_get_bit (lift_to_both0 k_793) (((
                      lift_to_both0 bits_v) .- (lift_to_both0 (usize 1))) .- (
                    lift_to_both0 i_792))) (nat_mod_one ) :bool_ChoiceEquality
              then lift_scope (L1 := CEfset ([result_760_loc ; q_790_loc])) (
                L2 := CEfset ([result_760_loc ; q_790_loc])) (
                I1 := [interface]) (
                I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
                letbndm(_) q_790 :=
                  point_add_jacob (lift_to_both0 q_790) (lift_to_both0 p_794) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (@Ok (
                    (
                      p256_field_element_t '×
                      p256_field_element_t '×
                      p256_field_element_t
                    )
                  ) error_t (lift_to_both0 q_790))
                )
              else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (@Ok (
                  (
                    p256_field_element_t '×
                    p256_field_element_t '×
                    p256_field_element_t
                  )
                ) error_t (lift_to_both0 q_790))
               in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (@Ok (
                (
                  p256_field_element_t '×
                  p256_field_element_t '×
                  p256_field_element_t
                )
              ) error_t (lift_to_both0 q_790))
            ) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        @Ok p256_jacobian_t error_t (lift_to_both0 q_790))
      ) : both (CEfset ([result_760_loc ; q_790_loc])) [interface] (
      jacobian_result_t)).
Fail Next Obligation.


Notation "'p256_point_mul_inp'" :=(
  p256_scalar_t '× affine_t : choice_type) (in custom pack_type at level 2).
Notation "'p256_point_mul_inp'" :=(
  p256_scalar_t '× affine_t : ChoiceEquality) (at level 2).
Notation "'p256_point_mul_out'" :=(
  affine_result_t : choice_type) (in custom pack_type at level 2).
Notation "'p256_point_mul_out'" :=(
  affine_result_t : ChoiceEquality) (at level 2).
Definition P256_POINT_MUL : nat :=
  799.
Program Definition p256_point_mul (k_796 : p256_scalar_t) (p_797 : affine_t)
  : both (CEfset ([result_760_loc ; q_790_loc])) [interface] (
    affine_result_t) :=
  ((letbnd(_) jac_798 : p256_jacobian_t :=
        ltr_mul (lift_to_both0 k_796) (affine_to_jacobian (
            lift_to_both0 p_797)) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (@Ok affine_t error_t (
          jacobian_to_affine (lift_to_both0 jac_798)))
      ) : both (CEfset ([result_760_loc ; q_790_loc])) [interface] (
      affine_result_t)).
Fail Next Obligation.


Notation "'p256_point_mul_base_inp'" :=(
  p256_scalar_t : choice_type) (in custom pack_type at level 2).
Notation "'p256_point_mul_base_inp'" :=(
  p256_scalar_t : ChoiceEquality) (at level 2).
Notation "'p256_point_mul_base_out'" :=(
  affine_result_t : choice_type) (in custom pack_type at level 2).
Notation "'p256_point_mul_base_out'" :=(
  affine_result_t : ChoiceEquality) (at level 2).
Definition P256_POINT_MUL_BASE : nat :=
  802.
Program Definition p256_point_mul_base (k_801 : p256_scalar_t)
  : both (CEfset ([result_760_loc ; q_790_loc])) [interface] (
    affine_result_t) :=
  ((letb base_point_800 : (p256_field_element_t '× p256_field_element_t) :=
        prod_b(
          nat_mod_from_byte_seq_be (array_to_seq (@array_from_list uint8 ([
                (secret (lift_to_both0 (@repr U8 107))) : uint8;
                (secret (lift_to_both0 (@repr U8 23))) : uint8;
                (secret (lift_to_both0 (@repr U8 209))) : uint8;
                (secret (lift_to_both0 (@repr U8 242))) : uint8;
                (secret (lift_to_both0 (@repr U8 225))) : uint8;
                (secret (lift_to_both0 (@repr U8 44))) : uint8;
                (secret (lift_to_both0 (@repr U8 66))) : uint8;
                (secret (lift_to_both0 (@repr U8 71))) : uint8;
                (secret (lift_to_both0 (@repr U8 248))) : uint8;
                (secret (lift_to_both0 (@repr U8 188))) : uint8;
                (secret (lift_to_both0 (@repr U8 230))) : uint8;
                (secret (lift_to_both0 (@repr U8 229))) : uint8;
                (secret (lift_to_both0 (@repr U8 99))) : uint8;
                (secret (lift_to_both0 (@repr U8 164))) : uint8;
                (secret (lift_to_both0 (@repr U8 64))) : uint8;
                (secret (lift_to_both0 (@repr U8 242))) : uint8;
                (secret (lift_to_both0 (@repr U8 119))) : uint8;
                (secret (lift_to_both0 (@repr U8 3))) : uint8;
                (secret (lift_to_both0 (@repr U8 125))) : uint8;
                (secret (lift_to_both0 (@repr U8 129))) : uint8;
                (secret (lift_to_both0 (@repr U8 45))) : uint8;
                (secret (lift_to_both0 (@repr U8 235))) : uint8;
                (secret (lift_to_both0 (@repr U8 51))) : uint8;
                (secret (lift_to_both0 (@repr U8 160))) : uint8;
                (secret (lift_to_both0 (@repr U8 244))) : uint8;
                (secret (lift_to_both0 (@repr U8 161))) : uint8;
                (secret (lift_to_both0 (@repr U8 57))) : uint8;
                (secret (lift_to_both0 (@repr U8 69))) : uint8;
                (secret (lift_to_both0 (@repr U8 216))) : uint8;
                (secret (lift_to_both0 (@repr U8 152))) : uint8;
                (secret (lift_to_both0 (@repr U8 194))) : uint8;
                (secret (lift_to_both0 (@repr U8 150))) : uint8
              ]))),
          nat_mod_from_byte_seq_be (array_to_seq (@array_from_list uint8 ([
                (secret (lift_to_both0 (@repr U8 79))) : uint8;
                (secret (lift_to_both0 (@repr U8 227))) : uint8;
                (secret (lift_to_both0 (@repr U8 66))) : uint8;
                (secret (lift_to_both0 (@repr U8 226))) : uint8;
                (secret (lift_to_both0 (@repr U8 254))) : uint8;
                (secret (lift_to_both0 (@repr U8 26))) : uint8;
                (secret (lift_to_both0 (@repr U8 127))) : uint8;
                (secret (lift_to_both0 (@repr U8 155))) : uint8;
                (secret (lift_to_both0 (@repr U8 142))) : uint8;
                (secret (lift_to_both0 (@repr U8 231))) : uint8;
                (secret (lift_to_both0 (@repr U8 235))) : uint8;
                (secret (lift_to_both0 (@repr U8 74))) : uint8;
                (secret (lift_to_both0 (@repr U8 124))) : uint8;
                (secret (lift_to_both0 (@repr U8 15))) : uint8;
                (secret (lift_to_both0 (@repr U8 158))) : uint8;
                (secret (lift_to_both0 (@repr U8 22))) : uint8;
                (secret (lift_to_both0 (@repr U8 43))) : uint8;
                (secret (lift_to_both0 (@repr U8 206))) : uint8;
                (secret (lift_to_both0 (@repr U8 51))) : uint8;
                (secret (lift_to_both0 (@repr U8 87))) : uint8;
                (secret (lift_to_both0 (@repr U8 107))) : uint8;
                (secret (lift_to_both0 (@repr U8 49))) : uint8;
                (secret (lift_to_both0 (@repr U8 94))) : uint8;
                (secret (lift_to_both0 (@repr U8 206))) : uint8;
                (secret (lift_to_both0 (@repr U8 203))) : uint8;
                (secret (lift_to_both0 (@repr U8 182))) : uint8;
                (secret (lift_to_both0 (@repr U8 64))) : uint8;
                (secret (lift_to_both0 (@repr U8 104))) : uint8;
                (secret (lift_to_both0 (@repr U8 55))) : uint8;
                (secret (lift_to_both0 (@repr U8 191))) : uint8;
                (secret (lift_to_both0 (@repr U8 81))) : uint8;
                (secret (lift_to_both0 (@repr U8 245))) : uint8
              ])))
        ) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (p256_point_mul (
          lift_to_both0 k_801) (lift_to_both0 base_point_800))
      ) : both (CEfset ([result_760_loc ; q_790_loc])) [interface] (
      affine_result_t)).
Fail Next Obligation.


Notation "'point_add_distinct_inp'" :=(
  affine_t '× affine_t : choice_type) (in custom pack_type at level 2).
Notation "'point_add_distinct_inp'" :=(
  affine_t '× affine_t : ChoiceEquality) (at level 2).
Notation "'point_add_distinct_out'" :=(
  affine_result_t : choice_type) (in custom pack_type at level 2).
Notation "'point_add_distinct_out'" :=(
  affine_result_t : ChoiceEquality) (at level 2).
Definition POINT_ADD_DISTINCT : nat :=
  806.
Program Definition point_add_distinct (p_803 : affine_t) (q_804 : affine_t)
  : both (CEfset ([result_760_loc])) [interface] (affine_result_t) :=
  ((letbnd(_) r_805 : p256_jacobian_t :=
        point_add_jacob (affine_to_jacobian (lift_to_both0 p_803)) (
          affine_to_jacobian (lift_to_both0 q_804)) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (@Ok affine_t error_t (
          jacobian_to_affine (lift_to_both0 r_805)))
      ) : both (CEfset ([result_760_loc])) [interface] (affine_result_t)).
Fail Next Obligation.


Notation "'point_add_inp'" :=(
  affine_t '× affine_t : choice_type) (in custom pack_type at level 2).
Notation "'point_add_inp'" :=(
  affine_t '× affine_t : ChoiceEquality) (at level 2).
Notation "'point_add_out'" :=(
  affine_result_t : choice_type) (in custom pack_type at level 2).
Notation "'point_add_out'" :=(affine_result_t : ChoiceEquality) (at level 2).
Definition POINT_ADD : nat :=
  809.
Program Definition point_add (p_807 : affine_t) (q_808 : affine_t)
  : both (CEfset ([result_760_loc])) [interface] (affine_result_t) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        if is_pure (I := [interface]) ((lift_to_both0 p_807) !=.? (
            lift_to_both0 q_808))
        then point_add_distinct (lift_to_both0 p_807) (lift_to_both0 q_808)
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (@Ok affine_t error_t (jacobian_to_affine (point_double (
              affine_to_jacobian (lift_to_both0 p_807))))))
   ) : both (CEfset ([result_760_loc])) [interface] (affine_result_t)).
Fail Next Obligation.

Definition all_zero_811_loc : ChoiceEqualityLocation :=
  (bool_ChoiceEquality ; 812%nat).
Definition valid_810_loc : ChoiceEqualityLocation :=
  (bool_ChoiceEquality ; 813%nat).
Notation "'p256_validate_private_key_inp'" :=(
  byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'p256_validate_private_key_inp'" :=(
  byte_seq : ChoiceEquality) (at level 2).
Notation "'p256_validate_private_key_out'" :=(
  bool_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'p256_validate_private_key_out'" :=(
  bool_ChoiceEquality : ChoiceEquality) (at level 2).
Definition P256_VALIDATE_PRIVATE_KEY : nat :=
  818.
Program Definition p256_validate_private_key (k_814 : byte_seq)
  : both (CEfset ([valid_810_loc ; all_zero_811_loc])) [interface] (
    bool_ChoiceEquality) :=
  ((letbm valid_810 : bool_ChoiceEquality loc( valid_810_loc ) :=
        lift_to_both0 ((true : bool_ChoiceEquality)) in
      letb k_element_815 : p256_scalar_t :=
        nat_mod_from_byte_seq_be (lift_to_both0 k_814) in
      letb k_element_bytes_816 : seq uint8 :=
        nat_mod_to_byte_seq_be (lift_to_both0 k_element_815) in
      letbm all_zero_811 : bool_ChoiceEquality loc( all_zero_811_loc ) :=
        lift_to_both0 ((true : bool_ChoiceEquality)) in
      letb '(valid_810, all_zero_811) :=
        foldi_both' (lift_to_both0 (usize 0)) (seq_len (
              lift_to_both0 k_814)) prod_ce(valid_810, all_zero_811) (L := (
              CEfset ([valid_810_loc ; all_zero_811_loc]))) (I := [interface]) (
            fun i_817 '(valid_810, all_zero_811) =>
            letb '(all_zero_811) :=
              if negb (uint8_equal (seq_index (k_814) (lift_to_both0 i_817)) (
                  secret (lift_to_both0 (@repr U8 0)))) :bool_ChoiceEquality
              then lift_scope (L1 := CEfset (
                  [valid_810_loc ; all_zero_811_loc])) (L2 := CEfset (
                  [valid_810_loc ; all_zero_811_loc])) (I1 := [interface]) (
                I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
                letbm all_zero_811 loc( all_zero_811_loc ) :=
                  lift_to_both0 ((false : bool_ChoiceEquality)) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                  lift_to_both0 all_zero_811)
                )
              else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                lift_to_both0 all_zero_811)
               in
            letb '(valid_810) :=
              if negb (uint8_equal (seq_index (k_element_bytes_816) (
                    lift_to_both0 i_817)) (seq_index (k_814) (
                    lift_to_both0 i_817))) :bool_ChoiceEquality
              then lift_scope (L1 := CEfset (
                  [valid_810_loc ; all_zero_811_loc])) (L2 := CEfset (
                  [valid_810_loc ; all_zero_811_loc])) (I1 := [interface]) (
                I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
                letbm valid_810 loc( valid_810_loc ) :=
                  lift_to_both0 ((false : bool_ChoiceEquality)) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                  lift_to_both0 valid_810)
                )
              else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                lift_to_both0 valid_810)
               in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                lift_to_both0 valid_810,
                lift_to_both0 all_zero_811
              ))
            ) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) ((
          lift_to_both0 valid_810) && (negb (lift_to_both0 all_zero_811)))
      ) : both (CEfset ([valid_810_loc ; all_zero_811_loc])) [interface] (
      bool_ChoiceEquality)).
Fail Next Obligation.


Notation "'p256_validate_public_key_inp'" :=(
  affine_t : choice_type) (in custom pack_type at level 2).
Notation "'p256_validate_public_key_inp'" :=(
  affine_t : ChoiceEquality) (at level 2).
Notation "'p256_validate_public_key_out'" :=(
  bool_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'p256_validate_public_key_out'" :=(
  bool_ChoiceEquality : ChoiceEquality) (at level 2).
Definition P256_VALIDATE_PUBLIC_KEY : nat :=
  825.
Program Definition p256_validate_public_key (p_820 : affine_t)
  : both (fset.fset0) [interface] (bool_ChoiceEquality) :=
  ((letb b_819 : p256_field_element_t :=
        nat_mod_from_byte_seq_be (seq_from_list _ [
            secret (lift_to_both0 (@repr U8 90));
            secret (lift_to_both0 (@repr U8 198));
            secret (lift_to_both0 (@repr U8 53));
            secret (lift_to_both0 (@repr U8 216));
            secret (lift_to_both0 (@repr U8 170));
            secret (lift_to_both0 (@repr U8 58));
            secret (lift_to_both0 (@repr U8 147));
            secret (lift_to_both0 (@repr U8 231));
            secret (lift_to_both0 (@repr U8 179));
            secret (lift_to_both0 (@repr U8 235));
            secret (lift_to_both0 (@repr U8 189));
            secret (lift_to_both0 (@repr U8 85));
            secret (lift_to_both0 (@repr U8 118));
            secret (lift_to_both0 (@repr U8 152));
            secret (lift_to_both0 (@repr U8 134));
            secret (lift_to_both0 (@repr U8 188));
            secret (lift_to_both0 (@repr U8 101));
            secret (lift_to_both0 (@repr U8 29));
            secret (lift_to_both0 (@repr U8 6));
            secret (lift_to_both0 (@repr U8 176));
            secret (lift_to_both0 (@repr U8 204));
            secret (lift_to_both0 (@repr U8 83));
            secret (lift_to_both0 (@repr U8 176));
            secret (lift_to_both0 (@repr U8 246));
            secret (lift_to_both0 (@repr U8 59));
            secret (lift_to_both0 (@repr U8 206));
            secret (lift_to_both0 (@repr U8 60));
            secret (lift_to_both0 (@repr U8 62));
            secret (lift_to_both0 (@repr U8 39));
            secret (lift_to_both0 (@repr U8 210));
            secret (lift_to_both0 (@repr U8 96));
            secret (lift_to_both0 (@repr U8 75))
          ]) in
      letb point_at_infinity_821 : bool_ChoiceEquality :=
        is_point_at_infinity (affine_to_jacobian (lift_to_both0 p_820)) in
      letb '(x_822, y_823) : (p256_field_element_t '× p256_field_element_t) :=
        lift_to_both0 p_820 in
      letb on_curve_824 : bool_ChoiceEquality :=
        ((lift_to_both0 y_823) *% (lift_to_both0 y_823)) =.? (((((
                  lift_to_both0 x_822) *% (lift_to_both0 x_822)) *% (
                lift_to_both0 x_822)) -% ((nat_mod_from_literal (
                  0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
                  lift_to_both0 (@repr U128 3))) *% (lift_to_both0 x_822))) +% (
            lift_to_both0 b_819)) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) ((negb (
            lift_to_both0 point_at_infinity_821)) && (
          lift_to_both0 on_curve_824))
      ) : both (fset.fset0) [interface] (bool_ChoiceEquality)).
Fail Next Obligation.


Notation "'p256_calculate_w_inp'" :=(
  p256_field_element_t : choice_type) (in custom pack_type at level 2).
Notation "'p256_calculate_w_inp'" :=(
  p256_field_element_t : ChoiceEquality) (at level 2).
Notation "'p256_calculate_w_out'" :=(
  p256_field_element_t : choice_type) (in custom pack_type at level 2).
Notation "'p256_calculate_w_out'" :=(
  p256_field_element_t : ChoiceEquality) (at level 2).
Definition P256_CALCULATE_W : nat :=
  831.
Program Definition p256_calculate_w (x_828 : p256_field_element_t)
  : both (fset.fset0) [interface] (p256_field_element_t) :=
  ((letb b_826 : p256_field_element_t :=
        nat_mod_from_byte_seq_be (seq_from_list _ [
            secret (lift_to_both0 (@repr U8 90));
            secret (lift_to_both0 (@repr U8 198));
            secret (lift_to_both0 (@repr U8 53));
            secret (lift_to_both0 (@repr U8 216));
            secret (lift_to_both0 (@repr U8 170));
            secret (lift_to_both0 (@repr U8 58));
            secret (lift_to_both0 (@repr U8 147));
            secret (lift_to_both0 (@repr U8 231));
            secret (lift_to_both0 (@repr U8 179));
            secret (lift_to_both0 (@repr U8 235));
            secret (lift_to_both0 (@repr U8 189));
            secret (lift_to_both0 (@repr U8 85));
            secret (lift_to_both0 (@repr U8 118));
            secret (lift_to_both0 (@repr U8 152));
            secret (lift_to_both0 (@repr U8 134));
            secret (lift_to_both0 (@repr U8 188));
            secret (lift_to_both0 (@repr U8 101));
            secret (lift_to_both0 (@repr U8 29));
            secret (lift_to_both0 (@repr U8 6));
            secret (lift_to_both0 (@repr U8 176));
            secret (lift_to_both0 (@repr U8 204));
            secret (lift_to_both0 (@repr U8 83));
            secret (lift_to_both0 (@repr U8 176));
            secret (lift_to_both0 (@repr U8 246));
            secret (lift_to_both0 (@repr U8 59));
            secret (lift_to_both0 (@repr U8 206));
            secret (lift_to_both0 (@repr U8 60));
            secret (lift_to_both0 (@repr U8 62));
            secret (lift_to_both0 (@repr U8 39));
            secret (lift_to_both0 (@repr U8 210));
            secret (lift_to_both0 (@repr U8 96));
            secret (lift_to_both0 (@repr U8 75))
          ]) in
      letb exp_827 : p256_field_element_t :=
        nat_mod_from_byte_seq_be (seq_from_list _ [
            secret (lift_to_both0 (@repr U8 63));
            secret (lift_to_both0 (@repr U8 255));
            secret (lift_to_both0 (@repr U8 255));
            secret (lift_to_both0 (@repr U8 255));
            secret (lift_to_both0 (@repr U8 192));
            secret (lift_to_both0 (@repr U8 0));
            secret (lift_to_both0 (@repr U8 0));
            secret (lift_to_both0 (@repr U8 0));
            secret (lift_to_both0 (@repr U8 64));
            secret (lift_to_both0 (@repr U8 0));
            secret (lift_to_both0 (@repr U8 0));
            secret (lift_to_both0 (@repr U8 0));
            secret (lift_to_both0 (@repr U8 0));
            secret (lift_to_both0 (@repr U8 0));
            secret (lift_to_both0 (@repr U8 0));
            secret (lift_to_both0 (@repr U8 0));
            secret (lift_to_both0 (@repr U8 0));
            secret (lift_to_both0 (@repr U8 0));
            secret (lift_to_both0 (@repr U8 0));
            secret (lift_to_both0 (@repr U8 0));
            secret (lift_to_both0 (@repr U8 64));
            secret (lift_to_both0 (@repr U8 0));
            secret (lift_to_both0 (@repr U8 0));
            secret (lift_to_both0 (@repr U8 0));
            secret (lift_to_both0 (@repr U8 0));
            secret (lift_to_both0 (@repr U8 0));
            secret (lift_to_both0 (@repr U8 0));
            secret (lift_to_both0 (@repr U8 0));
            secret (lift_to_both0 (@repr U8 0));
            secret (lift_to_both0 (@repr U8 0));
            secret (lift_to_both0 (@repr U8 0));
            secret (lift_to_both0 (@repr U8 0))
          ]) in
      letb z_829 : p256_field_element_t :=
        ((((lift_to_both0 x_828) *% (lift_to_both0 x_828)) *% (
              lift_to_both0 x_828)) -% ((nat_mod_from_literal (
                0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
                lift_to_both0 (@repr U128 3))) *% (lift_to_both0 x_828))) +% (
          lift_to_both0 b_826) in
      letb w_830 : p256_field_element_t :=
        nat_mod_pow_felem (lift_to_both0 z_829) (lift_to_both0 exp_827) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 w_830)
      ) : both (fset.fset0) [interface] (p256_field_element_t)).
Fail Next Obligation.

