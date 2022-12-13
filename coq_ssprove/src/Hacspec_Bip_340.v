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

Definition error_t : ChoiceEquality :=
  unit_ChoiceEquality '+ unit_ChoiceEquality '+ unit_ChoiceEquality '+ unit_ChoiceEquality '+ unit_ChoiceEquality.
Definition InvalidSecretKey : error_t :=
  inl (inl (inl (inl tt))).
Definition InvalidNonceGenerated : error_t :=
  inl (inl (inl (inr tt))).
Definition InvalidPublicKey : error_t :=
  inl (inl (inr tt)).
Definition InvalidXCoordinate : error_t :=
  inl (inr tt).
Definition InvalidSignature : error_t :=
  inr tt.

Definition field_canvas_t := nseq (int8) (usize 32).
Definition field_element_t :=
  nat_mod 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F.

Definition scalar_canvas_t := nseq (int8) (usize 32).
Definition scalar_t :=
  nat_mod 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141.

Definition big_integer_t := nat_mod pow2 256.

Notation "'affine_point_t'" := ((field_element_t '× field_element_t
)) : hacspec_scope.

Definition p_bytes32_t := nseq (int8) (usize 32).

Definition point_t : ChoiceEquality :=
  affine_point_t '+ unit_ChoiceEquality.
Definition Affine (x : affine_point_t) : point_t :=
  inl x.
Definition AtInfinity : point_t :=
  inr tt.


Notation "'finite_inp'" :=(
  point_t : choice_type) (in custom pack_type at level 2).
Notation "'finite_inp'" :=(point_t : ChoiceEquality) (at level 2).
Notation "'finite_out'" :=((option (
      affine_point_t)) : choice_type) (in custom pack_type at level 2).
Notation "'finite_out'" :=((option (
      affine_point_t)) : ChoiceEquality) (at level 2).
Definition FINITE : nat :=
  3120.
Program Definition finite (p_3121 : point_t)
  : both (fset.fset0) [interface] ((option (affine_point_t))) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (TODO match) ) : both (
      fset.fset0) [interface] ((option (affine_point_t)))).
Fail Next Obligation.


Notation "'x_inp'" :=(
  affine_point_t : choice_type) (in custom pack_type at level 2).
Notation "'x_inp'" :=(affine_point_t : ChoiceEquality) (at level 2).
Notation "'x_out'" :=(
  field_element_t : choice_type) (in custom pack_type at level 2).
Notation "'x_out'" :=(field_element_t : ChoiceEquality) (at level 2).
Definition X : nat :=
  3124.
Program Definition x (p_3122 : affine_point_t)
  : both (fset.fset0) [interface] (field_element_t) :=
  ((letb '(x_3123, _) : (field_element_t '× field_element_t) :=
        lift_to_both0 p_3122 in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 x_3123)
      ) : both (fset.fset0) [interface] (field_element_t)).
Fail Next Obligation.


Notation "'y_inp'" :=(
  affine_point_t : choice_type) (in custom pack_type at level 2).
Notation "'y_inp'" :=(affine_point_t : ChoiceEquality) (at level 2).
Notation "'y_out'" :=(
  field_element_t : choice_type) (in custom pack_type at level 2).
Notation "'y_out'" :=(field_element_t : ChoiceEquality) (at level 2).
Definition Y : nat :=
  3127.
Program Definition y (p_3125 : affine_point_t)
  : both (fset.fset0) [interface] (field_element_t) :=
  ((letb '(_, y_3126) : (field_element_t '× field_element_t) :=
        lift_to_both0 p_3125 in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 y_3126)
      ) : both (fset.fset0) [interface] (field_element_t)).
Fail Next Obligation.


Notation "'has_even_y_inp'" :=(
  affine_point_t : choice_type) (in custom pack_type at level 2).
Notation "'has_even_y_inp'" :=(affine_point_t : ChoiceEquality) (at level 2).
Notation "'has_even_y_out'" :=(
  bool_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'has_even_y_out'" :=(
  bool_ChoiceEquality : ChoiceEquality) (at level 2).
Definition HAS_EVEN_Y : nat :=
  3129.
Program Definition has_even_y (p_3128 : affine_point_t)
  : both (fset.fset0) [interface] (bool_ChoiceEquality) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (((y (
              lift_to_both0 p_3128)) rem (nat_mod_two )) =.? (nat_mod_zero ))
      ) : both (fset.fset0) [interface] (bool_ChoiceEquality)).
Fail Next Obligation.


Notation "'sqrt_inp'" :=(
  field_element_t : choice_type) (in custom pack_type at level 2).
Notation "'sqrt_inp'" :=(field_element_t : ChoiceEquality) (at level 2).
Notation "'sqrt_out'" :=((option (
      field_element_t)) : choice_type) (in custom pack_type at level 2).
Notation "'sqrt_out'" :=((option (
      field_element_t)) : ChoiceEquality) (at level 2).
Definition SQRT : nat :=
  3133.
Program Definition sqrt (y_3131 : field_element_t)
  : both (fset.fset0) [interface] ((option (field_element_t))) :=
  ((letb p1_4_3130 : field_element_t :=
        nat_mod_from_public_byte_seq_be (array_from_list int8 ([
              (lift_to_both0 (@repr U8 63)) : int8;
              (lift_to_both0 (@repr U8 255)) : int8;
              (lift_to_both0 (@repr U8 255)) : int8;
              (lift_to_both0 (@repr U8 255)) : int8;
              (lift_to_both0 (@repr U8 255)) : int8;
              (lift_to_both0 (@repr U8 255)) : int8;
              (lift_to_both0 (@repr U8 255)) : int8;
              (lift_to_both0 (@repr U8 255)) : int8;
              (lift_to_both0 (@repr U8 255)) : int8;
              (lift_to_both0 (@repr U8 255)) : int8;
              (lift_to_both0 (@repr U8 255)) : int8;
              (lift_to_both0 (@repr U8 255)) : int8;
              (lift_to_both0 (@repr U8 255)) : int8;
              (lift_to_both0 (@repr U8 255)) : int8;
              (lift_to_both0 (@repr U8 255)) : int8;
              (lift_to_both0 (@repr U8 255)) : int8;
              (lift_to_both0 (@repr U8 255)) : int8;
              (lift_to_both0 (@repr U8 255)) : int8;
              (lift_to_both0 (@repr U8 255)) : int8;
              (lift_to_both0 (@repr U8 255)) : int8;
              (lift_to_both0 (@repr U8 255)) : int8;
              (lift_to_both0 (@repr U8 255)) : int8;
              (lift_to_both0 (@repr U8 255)) : int8;
              (lift_to_both0 (@repr U8 255)) : int8;
              (lift_to_both0 (@repr U8 255)) : int8;
              (lift_to_both0 (@repr U8 255)) : int8;
              (lift_to_both0 (@repr U8 255)) : int8;
              (lift_to_both0 (@repr U8 255)) : int8;
              (lift_to_both0 (@repr U8 191)) : int8;
              (lift_to_both0 (@repr U8 255)) : int8;
              (lift_to_both0 (@repr U8 255)) : int8;
              (lift_to_both0 (@repr U8 12)) : int8
            ])) in
      letb x_3132 : field_element_t :=
        nat_mod_pow_self (lift_to_both0 y_3131) (lift_to_both0 p1_4_3130) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        if is_pure (I := [interface]) ((nat_mod_pow_self (
              lift_to_both0 x_3132) (nat_mod_two )) =.? (lift_to_both0 y_3131))
        then some (lift_to_both0 x_3132)
        else @None field_element_t)
      ) : both (fset.fset0) [interface] ((option (field_element_t)))).
Fail Next Obligation.

Definition y_3134_loc : ChoiceEqualityLocation :=
  (field_element_t ; 3135%nat).
Notation "'lift_x_inp'" :=(
  field_element_t : choice_type) (in custom pack_type at level 2).
Notation "'lift_x_inp'" :=(field_element_t : ChoiceEquality) (at level 2).
Notation "'lift_x_out'" :=((result (error_t) (
      affine_point_t)) : choice_type) (in custom pack_type at level 2).
Notation "'lift_x_out'" :=((result (error_t) (
      affine_point_t)) : ChoiceEquality) (at level 2).
Definition LIFT_X : nat :=
  3142.
Program Definition lift_x (x_3140 : field_element_t)
  : both (CEfset ([y_3134_loc])) [interface] ((result (error_t) (
        affine_point_t))) :=
  ((letb one_3136 : field_element_t := nat_mod_one  in
      letb two_3137 : field_element_t := nat_mod_two  in
      letb three_3138 : field_element_t :=
        nat_mod_from_literal (
          0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F) (
          lift_to_both0 (@repr U128 3)) in
      letb seven_3139 : field_element_t :=
        nat_mod_from_literal (
          0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F) (
          lift_to_both0 (@repr U128 7)) in
      letb y_sq_3141 : field_element_t :=
        (nat_mod_pow_self (lift_to_both0 x_3140) (
            lift_to_both0 three_3138)) +% (lift_to_both0 seven_3139) in
      letbndm(_) y_3134 : field_element_t :=
        option_ok_or (sqrt (lift_to_both0 y_sq_3141)) (InvalidXCoordinate) in
      letb '(y_3134) :=
        if ((lift_to_both0 y_3134) rem (lift_to_both0 two_3137)) =.? (
          lift_to_both0 one_3136) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset ([y_3134_loc])) (L2 := CEfset (
            [y_3134_loc])) (I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
          letbm y_3134 loc( y_3134_loc ) :=
            (nat_mod_zero ) -% (lift_to_both0 y_3134) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 y_3134)
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          lift_to_both0 y_3134)
         in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        @Ok affine_point_t error_t (prod_b(
            lift_to_both0 x_3140,
            lift_to_both0 y_3134
          )))
      ) : both (CEfset ([y_3134_loc])) [interface] ((result (error_t) (
          affine_point_t)))).
Fail Next Obligation.


Notation "'compute_lam_inp'" :=(
  affine_point_t '× affine_point_t : choice_type) (in custom pack_type at level 2).
Notation "'compute_lam_inp'" :=(
  affine_point_t '× affine_point_t : ChoiceEquality) (at level 2).
Notation "'compute_lam_out'" :=(
  field_element_t : choice_type) (in custom pack_type at level 2).
Notation "'compute_lam_out'" :=(field_element_t : ChoiceEquality) (at level 2).
Definition COMPUTE_LAM : nat :=
  3146.
Program Definition compute_lam (p1_3144 : affine_point_t) (
    p2_3145 : affine_point_t)
  : both (fset.fset0) [interface] (field_element_t) :=
  ((letb three_3143 : field_element_t :=
        nat_mod_from_literal (
          0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F) (
          lift_to_both0 (@repr U128 3)) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        if is_pure (I := [interface]) ((lift_to_both0 p1_3144) !=.? (
            lift_to_both0 p2_3145))
        then ((y (lift_to_both0 p2_3145)) -% (y (lift_to_both0 p1_3144))) *% (
          nat_mod_pow_self ((x (lift_to_both0 p2_3145)) -% (x (
                lift_to_both0 p1_3144))) ((nat_mod_zero ) -% (nat_mod_two )))
        else (((lift_to_both0 three_3143) *% (x (lift_to_both0 p1_3144))) *% (
            x (lift_to_both0 p1_3144))) *% (nat_mod_pow_self ((
              nat_mod_two ) *% (y (lift_to_both0 p1_3144))) ((
              nat_mod_zero ) -% (nat_mod_two ))))
      ) : both (fset.fset0) [interface] (field_element_t)).
Fail Next Obligation.

Definition result_3147_loc : ChoiceEqualityLocation :=
  (point_t ; 3148%nat).
Notation "'point_add_inp'" :=(
  point_t '× point_t : choice_type) (in custom pack_type at level 2).
Notation "'point_add_inp'" :=(
  point_t '× point_t : ChoiceEquality) (at level 2).
Notation "'point_add_out'" :=(
  point_t : choice_type) (in custom pack_type at level 2).
Notation "'point_add_out'" :=(point_t : ChoiceEquality) (at level 2).
Definition POINT_ADD : nat :=
  3155.
Program Definition point_add (p1_3149 : point_t) (p2_3150 : point_t)
  : both (CEfset ([result_3147_loc])) [interface] (point_t) :=
  ((letbm result_3147 : point_t loc( result_3147_loc ) := AtInfinity in
      letb '(result_3147) :=
        if option_is_none (finite (lift_to_both0 p1_3149)) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset ([result_3147_loc])) (L2 := CEfset (
            [result_3147_loc])) (I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
          letbm result_3147 loc( result_3147_loc ) := lift_to_both0 p2_3150 in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 result_3147)
          )
        else  lift_scope (L1 := CEfset ([result_3147_loc])) (L2 := CEfset (
            [result_3147_loc])) (I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (letb '(
              result_3147
            ) :=
            if option_is_none (finite (
                lift_to_both0 p2_3150)) :bool_ChoiceEquality
            then lift_scope (L1 := CEfset ([result_3147_loc])) (L2 := CEfset (
                [result_3147_loc])) (I1 := [interface]) (
              I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
              letbm result_3147 loc( result_3147_loc ) :=
                lift_to_both0 p1_3149 in
              lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                lift_to_both0 result_3147)
              )
            else  lift_scope (L1 := CEfset ([result_3147_loc])) (L2 := CEfset (
                [result_3147_loc])) (I1 := [interface]) (
              I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
              letb p1_3151 : (field_element_t '× field_element_t) :=
                option_unwrap (finite (lift_to_both0 p1_3149)) in
              letb p2_3152 : (field_element_t '× field_element_t) :=
                option_unwrap (finite (lift_to_both0 p2_3150)) in
              letb '(result_3147) :=
                if negb (((x (lift_to_both0 p1_3151)) =.? (x (
                        lift_to_both0 p2_3152))) && ((y (
                        lift_to_both0 p1_3151)) !=.? (y (
                        lift_to_both0 p2_3152)))) :bool_ChoiceEquality
                then lift_scope (L1 := CEfset ([result_3147_loc])) (
                  L2 := CEfset ([result_3147_loc])) (I1 := [interface]) (
                  I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
                  letb lam_3153 : field_element_t :=
                    compute_lam (lift_to_both0 p1_3151) (
                      lift_to_both0 p2_3152) in
                  letb x3_3154 : field_element_t :=
                    (((lift_to_both0 lam_3153) *% (lift_to_both0 lam_3153)) -% (
                        x (lift_to_both0 p1_3151))) -% (x (
                        lift_to_both0 p2_3152)) in
                  letbm result_3147 loc( result_3147_loc ) :=
                    Affine (prod_b(
                        lift_to_both0 x3_3154,
                        ((lift_to_both0 lam_3153) *% ((x (
                                lift_to_both0 p1_3151)) -% (
                              lift_to_both0 x3_3154))) -% (y (
                            lift_to_both0 p1_3151))
                      )) in
                  lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                    lift_to_both0 result_3147)
                  )
                else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                  lift_to_both0 result_3147)
                 in
              lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                lift_to_both0 result_3147)
              ) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 result_3147)
          ) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        lift_to_both0 result_3147)
      ) : both (CEfset ([result_3147_loc])) [interface] (point_t)).
Fail Next Obligation.

Definition p_3156_loc : ChoiceEqualityLocation :=
  (point_t ; 3158%nat).
Definition q_3157_loc : ChoiceEqualityLocation :=
  (point_t ; 3159%nat).
Notation "'point_mul_inp'" :=(
  scalar_t '× point_t : choice_type) (in custom pack_type at level 2).
Notation "'point_mul_inp'" :=(
  scalar_t '× point_t : ChoiceEquality) (at level 2).
Notation "'point_mul_out'" :=(
  point_t : choice_type) (in custom pack_type at level 2).
Notation "'point_mul_out'" :=(point_t : ChoiceEquality) (at level 2).
Definition POINT_MUL : nat :=
  3163.
Program Definition point_mul (s_3162 : scalar_t) (p_3160 : point_t)
  : both (CEfset ([result_3147_loc ; p_3156_loc ; q_3157_loc])) [interface] (
    point_t) :=
  ((letbm p_3156 : point_t loc( p_3156_loc ) := lift_to_both0 p_3160 in
      letbm q_3157 : point_t loc( q_3157_loc ) := AtInfinity in
      letb '(p_3156, q_3157) :=
        foldi_both' (lift_to_both0 (usize 0)) (lift_to_both0 (
              usize 256)) prod_ce(p_3156, q_3157) (L := (CEfset (
                [result_3147_loc ; p_3156_loc ; q_3157_loc]))) (
            I := [interface]) (fun i_3161 '(p_3156, q_3157) =>
            letb '(q_3157) :=
              if nat_mod_bit (lift_to_both0 s_3162) (
                lift_to_both0 i_3161) :bool_ChoiceEquality
              then lift_scope (L1 := CEfset (
                  [result_3147_loc ; p_3156_loc ; q_3157_loc])) (L2 := CEfset (
                  [result_3147_loc ; p_3156_loc ; q_3157_loc])) (
                I1 := [interface]) (
                I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
                letbm q_3157 loc( q_3157_loc ) :=
                  point_add (lift_to_both0 q_3157) (lift_to_both0 p_3156) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                  lift_to_both0 q_3157)
                )
              else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                lift_to_both0 q_3157)
               in
            letbm p_3156 loc( p_3156_loc ) :=
              point_add (lift_to_both0 p_3156) (lift_to_both0 p_3156) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                lift_to_both0 p_3156,
                lift_to_both0 q_3157
              ))
            ) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 q_3157)
      ) : both (CEfset (
        [result_3147_loc ; p_3156_loc ; q_3157_loc])) [interface] (point_t)).
Fail Next Obligation.


Notation "'point_mul_base_inp'" :=(
  scalar_t : choice_type) (in custom pack_type at level 2).
Notation "'point_mul_base_inp'" :=(scalar_t : ChoiceEquality) (at level 2).
Notation "'point_mul_base_out'" :=(
  point_t : choice_type) (in custom pack_type at level 2).
Notation "'point_mul_base_out'" :=(point_t : ChoiceEquality) (at level 2).
Definition POINT_MUL_BASE : nat :=
  3168.
Program Definition point_mul_base (s_3167 : scalar_t)
  : both (CEfset ([result_3147_loc ; p_3156_loc ; q_3157_loc])) [interface] (
    point_t) :=
  ((letb gx_3164 : p_bytes32_t :=
        array_from_list int8 ([
            (lift_to_both0 (@repr U8 121)) : int8;
            (lift_to_both0 (@repr U8 190)) : int8;
            (lift_to_both0 (@repr U8 102)) : int8;
            (lift_to_both0 (@repr U8 126)) : int8;
            (lift_to_both0 (@repr U8 249)) : int8;
            (lift_to_both0 (@repr U8 220)) : int8;
            (lift_to_both0 (@repr U8 187)) : int8;
            (lift_to_both0 (@repr U8 172)) : int8;
            (lift_to_both0 (@repr U8 85)) : int8;
            (lift_to_both0 (@repr U8 160)) : int8;
            (lift_to_both0 (@repr U8 98)) : int8;
            (lift_to_both0 (@repr U8 149)) : int8;
            (lift_to_both0 (@repr U8 206)) : int8;
            (lift_to_both0 (@repr U8 135)) : int8;
            (lift_to_both0 (@repr U8 11)) : int8;
            (lift_to_both0 (@repr U8 7)) : int8;
            (lift_to_both0 (@repr U8 2)) : int8;
            (lift_to_both0 (@repr U8 155)) : int8;
            (lift_to_both0 (@repr U8 252)) : int8;
            (lift_to_both0 (@repr U8 219)) : int8;
            (lift_to_both0 (@repr U8 45)) : int8;
            (lift_to_both0 (@repr U8 206)) : int8;
            (lift_to_both0 (@repr U8 40)) : int8;
            (lift_to_both0 (@repr U8 217)) : int8;
            (lift_to_both0 (@repr U8 89)) : int8;
            (lift_to_both0 (@repr U8 242)) : int8;
            (lift_to_both0 (@repr U8 129)) : int8;
            (lift_to_both0 (@repr U8 91)) : int8;
            (lift_to_both0 (@repr U8 22)) : int8;
            (lift_to_both0 (@repr U8 248)) : int8;
            (lift_to_both0 (@repr U8 23)) : int8;
            (lift_to_both0 (@repr U8 152)) : int8
          ]) in
      letb gy_3165 : p_bytes32_t :=
        array_from_list int8 ([
            (lift_to_both0 (@repr U8 72)) : int8;
            (lift_to_both0 (@repr U8 58)) : int8;
            (lift_to_both0 (@repr U8 218)) : int8;
            (lift_to_both0 (@repr U8 119)) : int8;
            (lift_to_both0 (@repr U8 38)) : int8;
            (lift_to_both0 (@repr U8 163)) : int8;
            (lift_to_both0 (@repr U8 196)) : int8;
            (lift_to_both0 (@repr U8 101)) : int8;
            (lift_to_both0 (@repr U8 93)) : int8;
            (lift_to_both0 (@repr U8 164)) : int8;
            (lift_to_both0 (@repr U8 251)) : int8;
            (lift_to_both0 (@repr U8 252)) : int8;
            (lift_to_both0 (@repr U8 14)) : int8;
            (lift_to_both0 (@repr U8 17)) : int8;
            (lift_to_both0 (@repr U8 8)) : int8;
            (lift_to_both0 (@repr U8 168)) : int8;
            (lift_to_both0 (@repr U8 253)) : int8;
            (lift_to_both0 (@repr U8 23)) : int8;
            (lift_to_both0 (@repr U8 180)) : int8;
            (lift_to_both0 (@repr U8 72)) : int8;
            (lift_to_both0 (@repr U8 166)) : int8;
            (lift_to_both0 (@repr U8 133)) : int8;
            (lift_to_both0 (@repr U8 84)) : int8;
            (lift_to_both0 (@repr U8 25)) : int8;
            (lift_to_both0 (@repr U8 156)) : int8;
            (lift_to_both0 (@repr U8 71)) : int8;
            (lift_to_both0 (@repr U8 208)) : int8;
            (lift_to_both0 (@repr U8 143)) : int8;
            (lift_to_both0 (@repr U8 251)) : int8;
            (lift_to_both0 (@repr U8 16)) : int8;
            (lift_to_both0 (@repr U8 212)) : int8;
            (lift_to_both0 (@repr U8 184)) : int8
          ]) in
      letb g_3166 : point_t :=
        Affine (prod_b(
            nat_mod_from_public_byte_seq_be (lift_to_both0 gx_3164),
            nat_mod_from_public_byte_seq_be (lift_to_both0 gy_3165)
          )) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (point_mul (
          lift_to_both0 s_3167) (lift_to_both0 g_3166))
      ) : both (CEfset (
        [result_3147_loc ; p_3156_loc ; q_3157_loc])) [interface] (point_t)).
Fail Next Obligation.

Definition bytes32_t := nseq (uint8) (usize 32).

Notation "'secret_key_t'" := (bytes32_t) : hacspec_scope.

Notation "'public_key_t'" := (bytes32_t) : hacspec_scope.

Notation "'message_t'" := (bytes32_t) : hacspec_scope.

Notation "'aux_rand_t'" := (bytes32_t) : hacspec_scope.

Definition signature_t := nseq (uint8) (usize 64).


Notation "'tagged_hash_inp'" :=(
  public_byte_seq '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'tagged_hash_inp'" :=(
  public_byte_seq '× byte_seq : ChoiceEquality) (at level 2).
Notation "'tagged_hash_out'" :=(
  bytes32_t : choice_type) (in custom pack_type at level 2).
Notation "'tagged_hash_out'" :=(bytes32_t : ChoiceEquality) (at level 2).
Definition TAGGED_HASH : nat :=
  3173.
Program Definition tagged_hash (tag_3169 : public_byte_seq) (
    msg_3171 : byte_seq)
  : both (fset.fset0) [interface] (bytes32_t) :=
  ((letb tag_hash_3170 : seq uint8 :=
        array_to_be_bytes (sha256 (seq_from_public_seq (
              lift_to_both0 tag_3169))) in
      letb hash_3172 : sha256_digest_t :=
        sha256 (seq_concat (seq_concat (lift_to_both0 tag_hash_3170) (
              lift_to_both0 tag_hash_3170)) (lift_to_both0 msg_3171)) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (array_from_seq (32) (
          array_to_seq (lift_to_both0 hash_3172)))
      ) : both (fset.fset0) [interface] (bytes32_t)).
Fail Next Obligation.

Definition tagged_hash_aux_prefix_t := nseq (int8) (usize 11).

Definition bip0340_aux_v : tagged_hash_aux_prefix_t :=
  array_from_list int8 [
    (@repr U8 66) : int8;
    (@repr U8 73) : int8;
    (@repr U8 80) : int8;
    (@repr U8 48) : int8;
    (@repr U8 51) : int8;
    (@repr U8 52) : int8;
    (@repr U8 48) : int8;
    (@repr U8 47) : int8;
    (@repr U8 97) : int8;
    (@repr U8 117) : int8;
    (@repr U8 120) : int8
  ].


Notation "'hash_aux_inp'" :=(
  aux_rand_t : choice_type) (in custom pack_type at level 2).
Notation "'hash_aux_inp'" :=(aux_rand_t : ChoiceEquality) (at level 2).
Notation "'hash_aux_out'" :=(
  bytes32_t : choice_type) (in custom pack_type at level 2).
Notation "'hash_aux_out'" :=(bytes32_t : ChoiceEquality) (at level 2).
Definition HASH_AUX : nat :=
  3175.
Program Definition hash_aux (aux_rand_3174 : aux_rand_t)
  : both (fset.fset0) [interface] (bytes32_t) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (tagged_hash (
          seq_from_seq (array_to_seq (lift_to_both0 bip0340_aux_v))) (
          seq_from_seq (lift_to_both0 aux_rand_3174)))
      ) : both (fset.fset0) [interface] (bytes32_t)).
Fail Next Obligation.

Definition tagged_hash_nonce_prefix_t := nseq (int8) (usize 13).

Definition bip0340_nonce_v : tagged_hash_nonce_prefix_t :=
  array_from_list int8 [
    (@repr U8 66) : int8;
    (@repr U8 73) : int8;
    (@repr U8 80) : int8;
    (@repr U8 48) : int8;
    (@repr U8 51) : int8;
    (@repr U8 52) : int8;
    (@repr U8 48) : int8;
    (@repr U8 47) : int8;
    (@repr U8 110) : int8;
    (@repr U8 111) : int8;
    (@repr U8 110) : int8;
    (@repr U8 99) : int8;
    (@repr U8 101) : int8
  ].


Notation "'hash_nonce_inp'" :=(
  bytes32_t '× bytes32_t '× message_t : choice_type) (in custom pack_type at level 2).
Notation "'hash_nonce_inp'" :=(
  bytes32_t '× bytes32_t '× message_t : ChoiceEquality) (at level 2).
Notation "'hash_nonce_out'" :=(
  bytes32_t : choice_type) (in custom pack_type at level 2).
Notation "'hash_nonce_out'" :=(bytes32_t : ChoiceEquality) (at level 2).
Definition HASH_NONCE : nat :=
  3180.
Program Definition hash_nonce (rand_3176 : bytes32_t) (
    pubkey_3177 : bytes32_t) (msg_3178 : message_t)
  : both (fset.fset0) [interface] (bytes32_t) :=
  ((letb c_3179 : byte_seq :=
        seq_concat (seq_concat (seq_from_seq (
              array_to_seq (lift_to_both0 rand_3176))) (
            array_to_seq (lift_to_both0 pubkey_3177))) (
          lift_to_both0 msg_3178) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (tagged_hash (
          seq_from_seq (array_to_seq (lift_to_both0 bip0340_nonce_v))) (
          lift_to_both0 c_3179))
      ) : both (fset.fset0) [interface] (bytes32_t)).
Fail Next Obligation.

Definition tagged_hash_challenge_prefix_t := nseq (int8) (usize 17).

Definition bip0340_challenge_v : tagged_hash_challenge_prefix_t :=
  array_from_list int8 [
    (@repr U8 66) : int8;
    (@repr U8 73) : int8;
    (@repr U8 80) : int8;
    (@repr U8 48) : int8;
    (@repr U8 51) : int8;
    (@repr U8 52) : int8;
    (@repr U8 48) : int8;
    (@repr U8 47) : int8;
    (@repr U8 99) : int8;
    (@repr U8 104) : int8;
    (@repr U8 97) : int8;
    (@repr U8 108) : int8;
    (@repr U8 108) : int8;
    (@repr U8 101) : int8;
    (@repr U8 110) : int8;
    (@repr U8 103) : int8;
    (@repr U8 101) : int8
  ].


Notation "'hash_challenge_inp'" :=(
  bytes32_t '× bytes32_t '× bytes32_t : choice_type) (in custom pack_type at level 2).
Notation "'hash_challenge_inp'" :=(
  bytes32_t '× bytes32_t '× bytes32_t : ChoiceEquality) (at level 2).
Notation "'hash_challenge_out'" :=(
  bytes32_t : choice_type) (in custom pack_type at level 2).
Notation "'hash_challenge_out'" :=(bytes32_t : ChoiceEquality) (at level 2).
Definition HASH_CHALLENGE : nat :=
  3185.
Program Definition hash_challenge (rx_3181 : bytes32_t) (
    pubkey_3182 : bytes32_t) (msg_3183 : bytes32_t)
  : both (fset.fset0) [interface] (bytes32_t) :=
  ((letb c_3184 : byte_seq :=
        seq_concat (seq_concat (seq_from_seq (
              array_to_seq (lift_to_both0 rx_3181))) (
            array_to_seq (lift_to_both0 pubkey_3182))) (
          array_to_seq (lift_to_both0 msg_3183)) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (tagged_hash (
          seq_from_seq (array_to_seq (lift_to_both0 bip0340_challenge_v))) (
          lift_to_both0 c_3184))
      ) : both (fset.fset0) [interface] (bytes32_t)).
Fail Next Obligation.


Notation "'bytes_from_point_inp'" :=(
  affine_point_t : choice_type) (in custom pack_type at level 2).
Notation "'bytes_from_point_inp'" :=(
  affine_point_t : ChoiceEquality) (at level 2).
Notation "'bytes_from_point_out'" :=(
  bytes32_t : choice_type) (in custom pack_type at level 2).
Notation "'bytes_from_point_out'" :=(bytes32_t : ChoiceEquality) (at level 2).
Definition BYTES_FROM_POINT : nat :=
  3188.
Program Definition bytes_from_point (p_3186 : affine_point_t)
  : both (fset.fset0) [interface] (bytes32_t) :=
  ((letb '(x_3187, _) : (field_element_t '× field_element_t) :=
        lift_to_both0 p_3186 in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (array_from_seq (32) (
          nat_mod_to_byte_seq_be (lift_to_both0 x_3187)))
      ) : both (fset.fset0) [interface] (bytes32_t)).
Fail Next Obligation.


Notation "'bytes_from_scalar_inp'" :=(
  scalar_t : choice_type) (in custom pack_type at level 2).
Notation "'bytes_from_scalar_inp'" :=(scalar_t : ChoiceEquality) (at level 2).
Notation "'bytes_from_scalar_out'" :=(
  bytes32_t : choice_type) (in custom pack_type at level 2).
Notation "'bytes_from_scalar_out'" :=(bytes32_t : ChoiceEquality) (at level 2).
Definition BYTES_FROM_SCALAR : nat :=
  3190.
Program Definition bytes_from_scalar (x_3189 : scalar_t)
  : both (fset.fset0) [interface] (bytes32_t) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (array_from_seq (32) (
          nat_mod_to_byte_seq_be (lift_to_both0 x_3189)))
      ) : both (fset.fset0) [interface] (bytes32_t)).
Fail Next Obligation.


Notation "'scalar_from_bytes_inp'" :=(
  bytes32_t : choice_type) (in custom pack_type at level 2).
Notation "'scalar_from_bytes_inp'" :=(bytes32_t : ChoiceEquality) (at level 2).
Notation "'scalar_from_bytes_out'" :=(
  scalar_t : choice_type) (in custom pack_type at level 2).
Notation "'scalar_from_bytes_out'" :=(scalar_t : ChoiceEquality) (at level 2).
Definition SCALAR_FROM_BYTES : nat :=
  3192.
Program Definition scalar_from_bytes (b_3191 : bytes32_t)
  : both (fset.fset0) [interface] (scalar_t) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (nat_mod_from_byte_seq_be (
          array_to_seq (lift_to_both0 b_3191)))
      ) : both (fset.fset0) [interface] (scalar_t)).
Fail Next Obligation.


Notation "'scalar_from_bytes_strict_inp'" :=(
  bytes32_t : choice_type) (in custom pack_type at level 2).
Notation "'scalar_from_bytes_strict_inp'" :=(
  bytes32_t : ChoiceEquality) (at level 2).
Notation "'scalar_from_bytes_strict_out'" :=((option (
      scalar_t)) : choice_type) (in custom pack_type at level 2).
Notation "'scalar_from_bytes_strict_out'" :=((option (
      scalar_t)) : ChoiceEquality) (at level 2).
Definition SCALAR_FROM_BYTES_STRICT : nat :=
  3196.
Program Definition scalar_from_bytes_strict (b_3193 : bytes32_t)
  : both (fset.fset0) [interface] ((option (scalar_t))) :=
  ((letb s_3194 : big_integer_t :=
        nat_mod_from_byte_seq_be (array_to_seq (lift_to_both0 b_3193)) in
      letb max_scalar_3195 : big_integer_t :=
        nat_mod_from_byte_seq_be (nat_mod_to_byte_seq_be (nat_mod_max_val )) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        if is_pure (I := [interface]) ((lift_to_both0 s_3194) >.? (
            lift_to_both0 max_scalar_3195))
        then @None scalar_t
        else @Some scalar_t (nat_mod_from_byte_seq_be (
            array_to_seq (lift_to_both0 b_3193))))
      ) : both (fset.fset0) [interface] ((option (scalar_t)))).
Fail Next Obligation.


Notation "'seckey_scalar_from_bytes_inp'" :=(
  bytes32_t : choice_type) (in custom pack_type at level 2).
Notation "'seckey_scalar_from_bytes_inp'" :=(
  bytes32_t : ChoiceEquality) (at level 2).
Notation "'seckey_scalar_from_bytes_out'" :=((option (
      scalar_t)) : choice_type) (in custom pack_type at level 2).
Notation "'seckey_scalar_from_bytes_out'" :=((option (
      scalar_t)) : ChoiceEquality) (at level 2).
Definition SECKEY_SCALAR_FROM_BYTES : nat :=
  3199.
Program Definition seckey_scalar_from_bytes (b_3197 : bytes32_t)
  : both (fset.fset0) [interface] ((option (scalar_t))) :=
  ((letbnd(_) s_3198 : scalar_t :=
        scalar_from_bytes_strict (lift_to_both0 b_3197) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        if is_pure (I := [interface]) ((lift_to_both0 s_3198) =.? (
            nat_mod_zero ))
        then @None scalar_t
        else @Some scalar_t (lift_to_both0 s_3198))
      ) : both (fset.fset0) [interface] ((option (scalar_t)))).
Fail Next Obligation.


Notation "'fieldelem_from_bytes_inp'" :=(
  public_key_t : choice_type) (in custom pack_type at level 2).
Notation "'fieldelem_from_bytes_inp'" :=(
  public_key_t : ChoiceEquality) (at level 2).
Notation "'fieldelem_from_bytes_out'" :=((option (
      field_element_t)) : choice_type) (in custom pack_type at level 2).
Notation "'fieldelem_from_bytes_out'" :=((option (
      field_element_t)) : ChoiceEquality) (at level 2).
Definition FIELDELEM_FROM_BYTES : nat :=
  3203.
Program Definition fieldelem_from_bytes (b_3200 : public_key_t)
  : both (fset.fset0) [interface] ((option (field_element_t))) :=
  ((letb s_3201 : big_integer_t :=
        nat_mod_from_byte_seq_be (lift_to_both0 b_3200) in
      letb max_fe_3202 : big_integer_t :=
        nat_mod_from_byte_seq_be (nat_mod_to_byte_seq_be (nat_mod_max_val )) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        if is_pure (I := [interface]) ((lift_to_both0 s_3201) >.? (
            lift_to_both0 max_fe_3202))
        then @None field_element_t
        else @Some field_element_t (nat_mod_from_byte_seq_be (
            lift_to_both0 b_3200)))
      ) : both (fset.fset0) [interface] ((option (field_element_t)))).
Fail Next Obligation.

Definition b_3204_loc : ChoiceEqualityLocation :=
  (seq uint8 ; 3205%nat).
Notation "'xor_bytes_inp'" :=(
  bytes32_t '× bytes32_t : choice_type) (in custom pack_type at level 2).
Notation "'xor_bytes_inp'" :=(
  bytes32_t '× bytes32_t : ChoiceEquality) (at level 2).
Notation "'xor_bytes_out'" :=(
  bytes32_t : choice_type) (in custom pack_type at level 2).
Notation "'xor_bytes_out'" :=(bytes32_t : ChoiceEquality) (at level 2).
Definition XOR_BYTES : nat :=
  3209.
Program Definition xor_bytes (b0_3206 : bytes32_t) (b1_3208 : bytes32_t)
  : both (CEfset ([b_3204_loc])) [interface] (bytes32_t) :=
  ((letbm b_3204 : seq uint8 loc( b_3204_loc ) :=
        seq_new_ (default : uint8) (array_len (lift_to_both0 b0_3206)) in
      letb b_3204 :=
        foldi_both' (lift_to_both0 (usize 0)) (array_len (
              lift_to_both0 b0_3206)) b_3204 (L := (CEfset ([b_3204_loc]))) (
            I := [interface]) (fun i_3207 b_3204 =>
            letb b_3204 : seq uint8 :=
              seq_upd b_3204 (lift_to_both0 i_3207) (is_pure ((array_index (
                      b0_3206) (lift_to_both0 i_3207)) .^ (array_index (
                      b1_3208) (lift_to_both0 i_3207)))) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 b_3204)
            ) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (array_from_seq (32) (
          lift_to_both0 b_3204))
      ) : both (CEfset ([b_3204_loc])) [interface] (bytes32_t)).
Fail Next Obligation.

Notation "'pubkey_gen_result_t'" := ((
  result error_t public_key_t)) : hacspec_scope.


Notation "'pubkey_gen_inp'" :=(
  secret_key_t : choice_type) (in custom pack_type at level 2).
Notation "'pubkey_gen_inp'" :=(secret_key_t : ChoiceEquality) (at level 2).
Notation "'pubkey_gen_out'" :=(
  pubkey_gen_result_t : choice_type) (in custom pack_type at level 2).
Notation "'pubkey_gen_out'" :=(
  pubkey_gen_result_t : ChoiceEquality) (at level 2).
Definition PUBKEY_GEN : nat :=
  3213.
Program Definition pubkey_gen (seckey_3210 : secret_key_t)
  : both (CEfset ([result_3147_loc ; p_3156_loc ; q_3157_loc])) [interface] (
    pubkey_gen_result_t) :=
  ((letbnd(_) d0_3211 : scalar_t :=
        option_ok_or (seckey_scalar_from_bytes (lift_to_both0 seckey_3210)) (
          InvalidSecretKey) in
      letb p_3212 : (field_element_t '× field_element_t) :=
        option_unwrap (finite (point_mul_base (lift_to_both0 d0_3211))) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        @Ok public_key_t error_t (bytes_from_point (lift_to_both0 p_3212)))
      ) : both (CEfset (
        [result_3147_loc ; p_3156_loc ; q_3157_loc])) [interface] (
      pubkey_gen_result_t)).
Fail Next Obligation.

Notation "'sign_result_t'" := ((result error_t signature_t)) : hacspec_scope.


Notation "'sign_inp'" :=(
  message_t '× secret_key_t '× aux_rand_t : choice_type) (in custom pack_type at level 2).
Notation "'sign_inp'" :=(
  message_t '× secret_key_t '× aux_rand_t : ChoiceEquality) (at level 2).
Notation "'sign_out'" :=(
  sign_result_t : choice_type) (in custom pack_type at level 2).
Notation "'sign_out'" :=(sign_result_t : ChoiceEquality) (at level 2).
Definition SIGN : nat :=
  3226.
Program Definition sign (msg_3220 : message_t) (seckey_3214 : secret_key_t) (
    aux_rand_3218 : aux_rand_t)
  : both (CEfset (
      [result_3147_loc ; p_3156_loc ; q_3157_loc ; b_3204_loc])) [interface] (
    sign_result_t) :=
  ((letbnd(_) d0_3215 : scalar_t :=
        option_ok_or (seckey_scalar_from_bytes (lift_to_both0 seckey_3214)) (
          InvalidSecretKey) in
      letb p_3216 : (field_element_t '× field_element_t) :=
        option_unwrap (finite (point_mul_base (lift_to_both0 d0_3215))) in
      letb d_3217 : scalar_t :=
        if is_pure (I := [interface]) (has_even_y (lift_to_both0 p_3216))
        then lift_to_both0 d0_3215
        else (nat_mod_zero ) -% (lift_to_both0 d0_3215) in
      letb t_3219 : bytes32_t :=
        xor_bytes (bytes_from_scalar (lift_to_both0 d_3217)) (hash_aux (
            lift_to_both0 aux_rand_3218)) in
      letb k0_3221 : scalar_t :=
        scalar_from_bytes (hash_nonce (lift_to_both0 t_3219) (bytes_from_point (
              lift_to_both0 p_3216)) (lift_to_both0 msg_3220)) in
      letbnd(ChoiceEqualityMonad.result_bind_both error_t) 'tt :=
        if (lift_to_both0 k0_3221) =.? (nat_mod_zero ) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset (
            [result_3147_loc ; p_3156_loc ; q_3157_loc ; b_3204_loc])) (
          L2 := CEfset (
            [result_3147_loc ; p_3156_loc ; q_3157_loc ; b_3204_loc])) (
          I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (letbnd(
              _) _ : signature_t :=
            @Err signature_t error_t (InvalidNonceGenerated) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            @Ok unit_ChoiceEquality error_t (lift_to_both0 (
                (tt : unit_ChoiceEquality))))
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          @Ok unit_ChoiceEquality error_t (lift_to_both0 (
              (tt : unit_ChoiceEquality))))
         in
      letb r_3222 : (field_element_t '× field_element_t) :=
        option_unwrap (finite (point_mul_base (lift_to_both0 k0_3221))) in
      letb k_3223 : scalar_t :=
        if is_pure (I := [interface]) (has_even_y (lift_to_both0 r_3222))
        then lift_to_both0 k0_3221
        else (nat_mod_zero ) -% (lift_to_both0 k0_3221) in
      letb e_3224 : scalar_t :=
        scalar_from_bytes (hash_challenge (bytes_from_point (
              lift_to_both0 r_3222)) (bytes_from_point (lift_to_both0 p_3216)) (
            lift_to_both0 msg_3220)) in
      letb sig_3225 : signature_t :=
        array_update (array_update (array_new_ (default : uint8) (64)) (
            lift_to_both0 (usize 0)) (array_to_seq (bytes_from_point (
              lift_to_both0 r_3222)))) (lift_to_both0 (usize 32)) (
          array_to_seq (bytes_from_scalar ((lift_to_both0 k_3223) +% ((
                lift_to_both0 e_3224) *% (lift_to_both0 d_3217))))) in
      letbnd(_) _ : unit_ChoiceEquality :=
        verify (lift_to_both0 msg_3220) (bytes_from_point (
            lift_to_both0 p_3216)) (lift_to_both0 sig_3225) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        @Ok signature_t error_t (lift_to_both0 sig_3225))
      ) : both (CEfset (
        [result_3147_loc ; p_3156_loc ; q_3157_loc ; b_3204_loc])) [interface] (
      sign_result_t)).
Fail Next Obligation.

Notation "'verification_result_t'" := ((result error_t unit)) : hacspec_scope.


Notation "'verify_inp'" :=(
  message_t '× public_key_t '× signature_t : choice_type) (in custom pack_type at level 2).
Notation "'verify_inp'" :=(
  message_t '× public_key_t '× signature_t : ChoiceEquality) (at level 2).
Notation "'verify_out'" :=(
  verification_result_t : choice_type) (in custom pack_type at level 2).
Notation "'verify_out'" :=(verification_result_t : ChoiceEquality) (at level 2).
Definition VERIFY : nat :=
  3236.
Program Definition verify (msg_3233 : message_t) (pubkey_3227 : public_key_t) (
    sig_3230 : signature_t)
  : both (CEfset (
      [y_3134_loc ; result_3147_loc ; p_3156_loc ; q_3157_loc])) [interface] (
    verification_result_t) :=
  ((letbnd(_) p_x_3228 : field_element_t :=
        option_ok_or (fieldelem_from_bytes (lift_to_both0 pubkey_3227)) (
          InvalidPublicKey) in
      letbnd(_) p_3229 : affine_point_t := lift_x (lift_to_both0 p_x_3228) in
      letbnd(_) r_3231 : field_element_t :=
        option_ok_or (fieldelem_from_bytes (array_from_slice (default : uint8) (
              32) (array_to_seq (lift_to_both0 sig_3230)) (lift_to_both0 (
                usize 0)) (lift_to_both0 (usize 32)))) (InvalidSignature) in
      letbnd(_) s_3232 : scalar_t :=
        option_ok_or (scalar_from_bytes_strict (array_from_slice (
              default : uint8) (32) (array_to_seq (lift_to_both0 sig_3230)) (
              lift_to_both0 (usize 32)) (lift_to_both0 (usize 32)))) (
          InvalidSignature) in
      letb e_3234 : scalar_t :=
        scalar_from_bytes (hash_challenge (array_from_slice (default : uint8) (
              32) (array_to_seq (lift_to_both0 sig_3230)) (lift_to_both0 (
                usize 0)) (lift_to_both0 (usize 32))) (bytes_from_point (
              lift_to_both0 p_3229)) (lift_to_both0 msg_3233)) in
      letbnd(_) r_p_3235 : (field_element_t '× field_element_t) :=
        option_ok_or (finite (point_add (point_mul_base (
                lift_to_both0 s_3232)) (point_mul ((nat_mod_zero ) -% (
                  lift_to_both0 e_3234)) (Affine (lift_to_both0 p_3229))))) (
          InvalidSignature) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        if is_pure (I := [interface]) ((negb (has_even_y (
                lift_to_both0 r_p_3235))) || ((x (
                lift_to_both0 r_p_3235)) !=.? (lift_to_both0 r_3231)))
        then @Err unit_ChoiceEquality error_t (InvalidSignature)
        else @Ok unit_ChoiceEquality error_t (tt))
      ) : both (CEfset (
        [y_3134_loc ; result_3147_loc ; p_3156_loc ; q_3157_loc])) [interface] (
      verification_result_t)).
Fail Next Obligation.

