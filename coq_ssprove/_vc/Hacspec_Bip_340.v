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
  3250.
Program Definition finite (p_3251 : point_t)
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
  3254.
Program Definition x (p_3252 : affine_point_t)
  : both (fset.fset0) [interface] (field_element_t) :=
  ((letb '(x_3253, _) : (field_element_t '× field_element_t) :=
        lift_to_both0 p_3252 in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 x_3253)
      ) : both (fset.fset0) [interface] (field_element_t)).
Fail Next Obligation.


Notation "'y_inp'" :=(
  affine_point_t : choice_type) (in custom pack_type at level 2).
Notation "'y_inp'" :=(affine_point_t : ChoiceEquality) (at level 2).
Notation "'y_out'" :=(
  field_element_t : choice_type) (in custom pack_type at level 2).
Notation "'y_out'" :=(field_element_t : ChoiceEquality) (at level 2).
Definition Y : nat :=
  3257.
Program Definition y (p_3255 : affine_point_t)
  : both (fset.fset0) [interface] (field_element_t) :=
  ((letb '(_, y_3256) : (field_element_t '× field_element_t) :=
        lift_to_both0 p_3255 in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 y_3256)
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
  3259.
Program Definition has_even_y (p_3258 : affine_point_t)
  : both (fset.fset0) [interface] (bool_ChoiceEquality) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (((y (
              lift_to_both0 p_3258)) rem (nat_mod_two )) =.? (nat_mod_zero ))
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
  3263.
Program Definition sqrt (y_3261 : field_element_t)
  : both (fset.fset0) [interface] ((option (field_element_t))) :=
  ((letb p1_4_3260 : field_element_t :=
        nat_mod_from_public_byte_seq_be (@array_from_list int8 ([
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
      letb x_3262 : field_element_t :=
        nat_mod_pow_self (lift_to_both0 y_3261) (lift_to_both0 p1_4_3260) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        if is_pure (I := [interface]) ((nat_mod_pow_self (
              lift_to_both0 x_3262) (nat_mod_two )) =.? (lift_to_both0 y_3261))
        then some (lift_to_both0 x_3262)
        else @None field_element_t)
      ) : both (fset.fset0) [interface] ((option (field_element_t)))).
Fail Next Obligation.

Definition y_3264_loc : ChoiceEqualityLocation :=
  (field_element_t ; 3265%nat).
Notation "'lift_x_inp'" :=(
  field_element_t : choice_type) (in custom pack_type at level 2).
Notation "'lift_x_inp'" :=(field_element_t : ChoiceEquality) (at level 2).
Notation "'lift_x_out'" :=((result (error_t) (
      affine_point_t)) : choice_type) (in custom pack_type at level 2).
Notation "'lift_x_out'" :=((result (error_t) (
      affine_point_t)) : ChoiceEquality) (at level 2).
Definition LIFT_X : nat :=
  3272.
Program Definition lift_x (x_3270 : field_element_t)
  : both (CEfset ([y_3264_loc])) [interface] ((result (error_t) (
        affine_point_t))) :=
  ((letb one_3266 : field_element_t := nat_mod_one  in
      letb two_3267 : field_element_t := nat_mod_two  in
      letb three_3268 : field_element_t :=
        nat_mod_from_literal (
          0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F) (
          lift_to_both0 (@repr U128 3)) in
      letb seven_3269 : field_element_t :=
        nat_mod_from_literal (
          0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F) (
          lift_to_both0 (@repr U128 7)) in
      letb y_sq_3271 : field_element_t :=
        (nat_mod_pow_self (lift_to_both0 x_3270) (
            lift_to_both0 three_3268)) +% (lift_to_both0 seven_3269) in
      letbndm(_) y_3264 : field_element_t :=
        option_ok_or (sqrt (lift_to_both0 y_sq_3271)) (InvalidXCoordinate) in
      letb '(y_3264) :=
        if ((lift_to_both0 y_3264) rem (lift_to_both0 two_3267)) =.? (
          lift_to_both0 one_3266) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset ([y_3264_loc])) (L2 := CEfset (
            [y_3264_loc])) (I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
          letbm y_3264 loc( y_3264_loc ) :=
            (nat_mod_zero ) -% (lift_to_both0 y_3264) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 y_3264)
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          lift_to_both0 y_3264)
         in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        @Ok affine_point_t error_t (prod_b(
            lift_to_both0 x_3270,
            lift_to_both0 y_3264
          )))
      ) : both (CEfset ([y_3264_loc])) [interface] ((result (error_t) (
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
  3276.
Program Definition compute_lam (p1_3274 : affine_point_t) (
    p2_3275 : affine_point_t)
  : both (fset.fset0) [interface] (field_element_t) :=
  ((letb three_3273 : field_element_t :=
        nat_mod_from_literal (
          0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F) (
          lift_to_both0 (@repr U128 3)) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        if is_pure (I := [interface]) ((lift_to_both0 p1_3274) !=.? (
            lift_to_both0 p2_3275))
        then ((y (lift_to_both0 p2_3275)) -% (y (lift_to_both0 p1_3274))) *% (
          nat_mod_pow_self ((x (lift_to_both0 p2_3275)) -% (x (
                lift_to_both0 p1_3274))) ((nat_mod_zero ) -% (nat_mod_two )))
        else (((lift_to_both0 three_3273) *% (x (lift_to_both0 p1_3274))) *% (
            x (lift_to_both0 p1_3274))) *% (nat_mod_pow_self ((
              nat_mod_two ) *% (y (lift_to_both0 p1_3274))) ((
              nat_mod_zero ) -% (nat_mod_two ))))
      ) : both (fset.fset0) [interface] (field_element_t)).
Fail Next Obligation.

Definition result_3277_loc : ChoiceEqualityLocation :=
  (point_t ; 3278%nat).
Notation "'point_add_inp'" :=(
  point_t '× point_t : choice_type) (in custom pack_type at level 2).
Notation "'point_add_inp'" :=(
  point_t '× point_t : ChoiceEquality) (at level 2).
Notation "'point_add_out'" :=(
  point_t : choice_type) (in custom pack_type at level 2).
Notation "'point_add_out'" :=(point_t : ChoiceEquality) (at level 2).
Definition POINT_ADD : nat :=
  3285.
Program Definition point_add (p1_3279 : point_t) (p2_3280 : point_t)
  : both (CEfset ([result_3277_loc])) [interface] (point_t) :=
  ((letbm result_3277 : point_t loc( result_3277_loc ) := AtInfinity in
      letb '(result_3277) :=
        if option_is_none (finite (lift_to_both0 p1_3279)) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset ([result_3277_loc])) (L2 := CEfset (
            [result_3277_loc])) (I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
          letbm result_3277 loc( result_3277_loc ) := lift_to_both0 p2_3280 in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 result_3277)
          )
        else  lift_scope (L1 := CEfset ([result_3277_loc])) (L2 := CEfset (
            [result_3277_loc])) (I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (letb '(
              result_3277
            ) :=
            if option_is_none (finite (
                lift_to_both0 p2_3280)) :bool_ChoiceEquality
            then lift_scope (L1 := CEfset ([result_3277_loc])) (L2 := CEfset (
                [result_3277_loc])) (I1 := [interface]) (
              I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
              letbm result_3277 loc( result_3277_loc ) :=
                lift_to_both0 p1_3279 in
              lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                lift_to_both0 result_3277)
              )
            else  lift_scope (L1 := CEfset ([result_3277_loc])) (L2 := CEfset (
                [result_3277_loc])) (I1 := [interface]) (
              I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
              letb p1_3281 : (field_element_t '× field_element_t) :=
                option_unwrap (finite (lift_to_both0 p1_3279)) in
              letb p2_3282 : (field_element_t '× field_element_t) :=
                option_unwrap (finite (lift_to_both0 p2_3280)) in
              letb '(result_3277) :=
                if negb (((x (lift_to_both0 p1_3281)) =.? (x (
                        lift_to_both0 p2_3282))) && ((y (
                        lift_to_both0 p1_3281)) !=.? (y (
                        lift_to_both0 p2_3282)))) :bool_ChoiceEquality
                then lift_scope (L1 := CEfset ([result_3277_loc])) (
                  L2 := CEfset ([result_3277_loc])) (I1 := [interface]) (
                  I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
                  letb lam_3283 : field_element_t :=
                    compute_lam (lift_to_both0 p1_3281) (
                      lift_to_both0 p2_3282) in
                  letb x3_3284 : field_element_t :=
                    (((lift_to_both0 lam_3283) *% (lift_to_both0 lam_3283)) -% (
                        x (lift_to_both0 p1_3281))) -% (x (
                        lift_to_both0 p2_3282)) in
                  letbm result_3277 loc( result_3277_loc ) :=
                    Affine (prod_b(
                        lift_to_both0 x3_3284,
                        ((lift_to_both0 lam_3283) *% ((x (
                                lift_to_both0 p1_3281)) -% (
                              lift_to_both0 x3_3284))) -% (y (
                            lift_to_both0 p1_3281))
                      )) in
                  lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                    lift_to_both0 result_3277)
                  )
                else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                  lift_to_both0 result_3277)
                 in
              lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                lift_to_both0 result_3277)
              ) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 result_3277)
          ) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        lift_to_both0 result_3277)
      ) : both (CEfset ([result_3277_loc])) [interface] (point_t)).
Fail Next Obligation.

Definition q_3287_loc : ChoiceEqualityLocation :=
  (point_t ; 3288%nat).
Definition p_3286_loc : ChoiceEqualityLocation :=
  (point_t ; 3289%nat).
Notation "'point_mul_inp'" :=(
  scalar_t '× point_t : choice_type) (in custom pack_type at level 2).
Notation "'point_mul_inp'" :=(
  scalar_t '× point_t : ChoiceEquality) (at level 2).
Notation "'point_mul_out'" :=(
  point_t : choice_type) (in custom pack_type at level 2).
Notation "'point_mul_out'" :=(point_t : ChoiceEquality) (at level 2).
Definition POINT_MUL : nat :=
  3293.
Program Definition point_mul (s_3292 : scalar_t) (p_3290 : point_t)
  : both (CEfset ([result_3277_loc ; p_3286_loc ; q_3287_loc])) [interface] (
    point_t) :=
  ((letbm p_3286 : point_t loc( p_3286_loc ) := lift_to_both0 p_3290 in
      letbm q_3287 : point_t loc( q_3287_loc ) := AtInfinity in
      letb '(p_3286, q_3287) :=
        foldi_both' (lift_to_both0 (usize 0)) (lift_to_both0 (
              usize 256)) prod_ce(p_3286, q_3287) (L := (CEfset (
                [result_3277_loc ; p_3286_loc ; q_3287_loc]))) (
            I := [interface]) (fun i_3291 '(p_3286, q_3287) =>
            letb '(q_3287) :=
              if nat_mod_bit (lift_to_both0 s_3292) (
                lift_to_both0 i_3291) :bool_ChoiceEquality
              then lift_scope (L1 := CEfset (
                  [result_3277_loc ; p_3286_loc ; q_3287_loc])) (L2 := CEfset (
                  [result_3277_loc ; p_3286_loc ; q_3287_loc])) (
                I1 := [interface]) (
                I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
                letbm q_3287 loc( q_3287_loc ) :=
                  point_add (lift_to_both0 q_3287) (lift_to_both0 p_3286) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                  lift_to_both0 q_3287)
                )
              else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                lift_to_both0 q_3287)
               in
            letbm p_3286 loc( p_3286_loc ) :=
              point_add (lift_to_both0 p_3286) (lift_to_both0 p_3286) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                lift_to_both0 p_3286,
                lift_to_both0 q_3287
              ))
            ) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 q_3287)
      ) : both (CEfset (
        [result_3277_loc ; p_3286_loc ; q_3287_loc])) [interface] (point_t)).
Fail Next Obligation.


Notation "'point_mul_base_inp'" :=(
  scalar_t : choice_type) (in custom pack_type at level 2).
Notation "'point_mul_base_inp'" :=(scalar_t : ChoiceEquality) (at level 2).
Notation "'point_mul_base_out'" :=(
  point_t : choice_type) (in custom pack_type at level 2).
Notation "'point_mul_base_out'" :=(point_t : ChoiceEquality) (at level 2).
Definition POINT_MUL_BASE : nat :=
  3298.
Program Definition point_mul_base (s_3297 : scalar_t)
  : both (CEfset ([result_3277_loc ; p_3286_loc ; q_3287_loc])) [interface] (
    point_t) :=
  ((letb gx_3294 : p_bytes32_t :=
        @array_from_list int8 ([
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
      letb gy_3295 : p_bytes32_t :=
        @array_from_list int8 ([
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
      letb g_3296 : point_t :=
        Affine (prod_b(
            nat_mod_from_public_byte_seq_be (lift_to_both0 gx_3294),
            nat_mod_from_public_byte_seq_be (lift_to_both0 gy_3295)
          )) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (point_mul (
          lift_to_both0 s_3297) (lift_to_both0 g_3296))
      ) : both (CEfset (
        [result_3277_loc ; p_3286_loc ; q_3287_loc])) [interface] (point_t)).
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
  3303.
Program Definition tagged_hash (tag_3299 : public_byte_seq) (
    msg_3301 : byte_seq)
  : both (fset.fset0) [interface] (bytes32_t) :=
  ((letb tag_hash_3300 : seq uint8 :=
        array_to_be_bytes (sha256 (seq_from_public_seq (
              lift_to_both0 tag_3299))) in
      letb hash_3302 : sha256_digest_t :=
        sha256 (seq_concat (seq_concat (lift_to_both0 tag_hash_3300) (
              lift_to_both0 tag_hash_3300)) (lift_to_both0 msg_3301)) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (array_from_seq (32) (
          array_to_seq (lift_to_both0 hash_3302)))
      ) : both (fset.fset0) [interface] (bytes32_t)).
Fail Next Obligation.

Definition tagged_hash_aux_prefix_t := nseq (int8) (usize 11).

Definition bip0340_aux_v : tagged_hash_aux_prefix_t :=
  @array_from_list int8 [
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
  3305.
Program Definition hash_aux (aux_rand_3304 : aux_rand_t)
  : both (fset.fset0) [interface] (bytes32_t) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (tagged_hash (
          seq_from_seq (array_to_seq (lift_to_both0 bip0340_aux_v))) (
          seq_from_seq (lift_to_both0 aux_rand_3304)))
      ) : both (fset.fset0) [interface] (bytes32_t)).
Fail Next Obligation.

Definition tagged_hash_nonce_prefix_t := nseq (int8) (usize 13).

Definition bip0340_nonce_v : tagged_hash_nonce_prefix_t :=
  @array_from_list int8 [
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
  3310.
Program Definition hash_nonce (rand_3306 : bytes32_t) (
    pubkey_3307 : bytes32_t) (msg_3308 : message_t)
  : both (fset.fset0) [interface] (bytes32_t) :=
  ((letb c_3309 : byte_seq :=
        seq_concat (seq_concat (seq_from_seq (
              array_to_seq (lift_to_both0 rand_3306))) (
            array_to_seq (lift_to_both0 pubkey_3307))) (
          lift_to_both0 msg_3308) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (tagged_hash (
          seq_from_seq (array_to_seq (lift_to_both0 bip0340_nonce_v))) (
          lift_to_both0 c_3309))
      ) : both (fset.fset0) [interface] (bytes32_t)).
Fail Next Obligation.

Definition tagged_hash_challenge_prefix_t := nseq (int8) (usize 17).

Definition bip0340_challenge_v : tagged_hash_challenge_prefix_t :=
  @array_from_list int8 [
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
  3315.
Program Definition hash_challenge (rx_3311 : bytes32_t) (
    pubkey_3312 : bytes32_t) (msg_3313 : bytes32_t)
  : both (fset.fset0) [interface] (bytes32_t) :=
  ((letb c_3314 : byte_seq :=
        seq_concat (seq_concat (seq_from_seq (
              array_to_seq (lift_to_both0 rx_3311))) (
            array_to_seq (lift_to_both0 pubkey_3312))) (
          array_to_seq (lift_to_both0 msg_3313)) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (tagged_hash (
          seq_from_seq (array_to_seq (lift_to_both0 bip0340_challenge_v))) (
          lift_to_both0 c_3314))
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
  3318.
Program Definition bytes_from_point (p_3316 : affine_point_t)
  : both (fset.fset0) [interface] (bytes32_t) :=
  ((letb '(x_3317, _) : (field_element_t '× field_element_t) :=
        lift_to_both0 p_3316 in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (array_from_seq (32) (
          nat_mod_to_byte_seq_be (lift_to_both0 x_3317)))
      ) : both (fset.fset0) [interface] (bytes32_t)).
Fail Next Obligation.


Notation "'bytes_from_scalar_inp'" :=(
  scalar_t : choice_type) (in custom pack_type at level 2).
Notation "'bytes_from_scalar_inp'" :=(scalar_t : ChoiceEquality) (at level 2).
Notation "'bytes_from_scalar_out'" :=(
  bytes32_t : choice_type) (in custom pack_type at level 2).
Notation "'bytes_from_scalar_out'" :=(bytes32_t : ChoiceEquality) (at level 2).
Definition BYTES_FROM_SCALAR : nat :=
  3320.
Program Definition bytes_from_scalar (x_3319 : scalar_t)
  : both (fset.fset0) [interface] (bytes32_t) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (array_from_seq (32) (
          nat_mod_to_byte_seq_be (lift_to_both0 x_3319)))
      ) : both (fset.fset0) [interface] (bytes32_t)).
Fail Next Obligation.


Notation "'scalar_from_bytes_inp'" :=(
  bytes32_t : choice_type) (in custom pack_type at level 2).
Notation "'scalar_from_bytes_inp'" :=(bytes32_t : ChoiceEquality) (at level 2).
Notation "'scalar_from_bytes_out'" :=(
  scalar_t : choice_type) (in custom pack_type at level 2).
Notation "'scalar_from_bytes_out'" :=(scalar_t : ChoiceEquality) (at level 2).
Definition SCALAR_FROM_BYTES : nat :=
  3322.
Program Definition scalar_from_bytes (b_3321 : bytes32_t)
  : both (fset.fset0) [interface] (scalar_t) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (nat_mod_from_byte_seq_be (
          array_to_seq (lift_to_both0 b_3321)))
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
  3326.
Program Definition scalar_from_bytes_strict (b_3323 : bytes32_t)
  : both (fset.fset0) [interface] ((option (scalar_t))) :=
  ((letb s_3324 : big_integer_t :=
        nat_mod_from_byte_seq_be (array_to_seq (lift_to_both0 b_3323)) in
      letb max_scalar_3325 : big_integer_t :=
        nat_mod_from_byte_seq_be (nat_mod_to_byte_seq_be (nat_mod_max_val )) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        if is_pure (I := [interface]) ((lift_to_both0 s_3324) >.? (
            lift_to_both0 max_scalar_3325))
        then @None scalar_t
        else @Some scalar_t (nat_mod_from_byte_seq_be (
            array_to_seq (lift_to_both0 b_3323))))
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
  3329.
Program Definition seckey_scalar_from_bytes (b_3327 : bytes32_t)
  : both (fset.fset0) [interface] ((option (scalar_t))) :=
  ((letbnd(_) s_3328 : scalar_t :=
        scalar_from_bytes_strict (lift_to_both0 b_3327) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        if is_pure (I := [interface]) ((lift_to_both0 s_3328) =.? (
            nat_mod_zero ))
        then @None scalar_t
        else @Some scalar_t (lift_to_both0 s_3328))
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
  3333.
Program Definition fieldelem_from_bytes (b_3330 : public_key_t)
  : both (fset.fset0) [interface] ((option (field_element_t))) :=
  ((letb s_3331 : big_integer_t :=
        nat_mod_from_byte_seq_be (lift_to_both0 b_3330) in
      letb max_fe_3332 : big_integer_t :=
        nat_mod_from_byte_seq_be (nat_mod_to_byte_seq_be (nat_mod_max_val )) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        if is_pure (I := [interface]) ((lift_to_both0 s_3331) >.? (
            lift_to_both0 max_fe_3332))
        then @None field_element_t
        else @Some field_element_t (nat_mod_from_byte_seq_be (
            lift_to_both0 b_3330)))
      ) : both (fset.fset0) [interface] ((option (field_element_t)))).
Fail Next Obligation.

Definition b_3334_loc : ChoiceEqualityLocation :=
  (seq uint8 ; 3335%nat).
Notation "'xor_bytes_inp'" :=(
  bytes32_t '× bytes32_t : choice_type) (in custom pack_type at level 2).
Notation "'xor_bytes_inp'" :=(
  bytes32_t '× bytes32_t : ChoiceEquality) (at level 2).
Notation "'xor_bytes_out'" :=(
  bytes32_t : choice_type) (in custom pack_type at level 2).
Notation "'xor_bytes_out'" :=(bytes32_t : ChoiceEquality) (at level 2).
Definition XOR_BYTES : nat :=
  3339.
Program Definition xor_bytes (b0_3336 : bytes32_t) (b1_3338 : bytes32_t)
  : both (CEfset ([b_3334_loc])) [interface] (bytes32_t) :=
  ((letbm b_3334 : seq uint8 loc( b_3334_loc ) :=
        seq_new_ (default : uint8) (array_len (lift_to_both0 b0_3336)) in
      letb b_3334 :=
        foldi_both' (lift_to_both0 (usize 0)) (array_len (
              lift_to_both0 b0_3336)) b_3334 (L := (CEfset ([b_3334_loc]))) (
            I := [interface]) (fun i_3337 b_3334 =>
            letb b_3334 : seq uint8 :=
              seq_upd b_3334 (lift_to_both0 i_3337) (is_pure ((array_index (
                      b0_3336) (lift_to_both0 i_3337)) .^ (array_index (
                      b1_3338) (lift_to_both0 i_3337)))) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 b_3334)
            ) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (array_from_seq (32) (
          lift_to_both0 b_3334))
      ) : both (CEfset ([b_3334_loc])) [interface] (bytes32_t)).
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
  3343.
Program Definition pubkey_gen (seckey_3340 : secret_key_t)
  : both (CEfset ([result_3277_loc ; p_3286_loc ; q_3287_loc])) [interface] (
    pubkey_gen_result_t) :=
  ((letbnd(_) d0_3341 : scalar_t :=
        option_ok_or (seckey_scalar_from_bytes (lift_to_both0 seckey_3340)) (
          InvalidSecretKey) in
      letb p_3342 : (field_element_t '× field_element_t) :=
        option_unwrap (finite (point_mul_base (lift_to_both0 d0_3341))) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        @Ok public_key_t error_t (bytes_from_point (lift_to_both0 p_3342)))
      ) : both (CEfset (
        [result_3277_loc ; p_3286_loc ; q_3287_loc])) [interface] (
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
  3356.
Program Definition sign (msg_3350 : message_t) (seckey_3344 : secret_key_t) (
    aux_rand_3348 : aux_rand_t)
  : both (CEfset (
      [result_3277_loc ; p_3286_loc ; q_3287_loc ; b_3334_loc])) [interface] (
    sign_result_t) :=
  ((letbnd(_) d0_3345 : scalar_t :=
        option_ok_or (seckey_scalar_from_bytes (lift_to_both0 seckey_3344)) (
          InvalidSecretKey) in
      letb p_3346 : (field_element_t '× field_element_t) :=
        option_unwrap (finite (point_mul_base (lift_to_both0 d0_3345))) in
      letb d_3347 : scalar_t :=
        if is_pure (I := [interface]) (has_even_y (lift_to_both0 p_3346))
        then lift_to_both0 d0_3345
        else (nat_mod_zero ) -% (lift_to_both0 d0_3345) in
      letb t_3349 : bytes32_t :=
        xor_bytes (bytes_from_scalar (lift_to_both0 d_3347)) (hash_aux (
            lift_to_both0 aux_rand_3348)) in
      letb k0_3351 : scalar_t :=
        scalar_from_bytes (hash_nonce (lift_to_both0 t_3349) (bytes_from_point (
              lift_to_both0 p_3346)) (lift_to_both0 msg_3350)) in
      letbnd(ChoiceEqualityMonad.result_bind_both error_t) 'tt :=
        if (lift_to_both0 k0_3351) =.? (nat_mod_zero ) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset (
            [result_3277_loc ; p_3286_loc ; q_3287_loc ; b_3334_loc])) (
          L2 := CEfset (
            [result_3277_loc ; p_3286_loc ; q_3287_loc ; b_3334_loc])) (
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
      letb r_3352 : (field_element_t '× field_element_t) :=
        option_unwrap (finite (point_mul_base (lift_to_both0 k0_3351))) in
      letb k_3353 : scalar_t :=
        if is_pure (I := [interface]) (has_even_y (lift_to_both0 r_3352))
        then lift_to_both0 k0_3351
        else (nat_mod_zero ) -% (lift_to_both0 k0_3351) in
      letb e_3354 : scalar_t :=
        scalar_from_bytes (hash_challenge (bytes_from_point (
              lift_to_both0 r_3352)) (bytes_from_point (lift_to_both0 p_3346)) (
            lift_to_both0 msg_3350)) in
      letb sig_3355 : signature_t :=
        array_update (array_update (array_new_ (default : uint8) (64)) (
            lift_to_both0 (usize 0)) (array_to_seq (bytes_from_point (
              lift_to_both0 r_3352)))) (lift_to_both0 (usize 32)) (
          array_to_seq (bytes_from_scalar ((lift_to_both0 k_3353) +% ((
                lift_to_both0 e_3354) *% (lift_to_both0 d_3347))))) in
      letbnd(_) _ : unit_ChoiceEquality :=
        verify (lift_to_both0 msg_3350) (bytes_from_point (
            lift_to_both0 p_3346)) (lift_to_both0 sig_3355) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        @Ok signature_t error_t (lift_to_both0 sig_3355))
      ) : both (CEfset (
        [result_3277_loc ; p_3286_loc ; q_3287_loc ; b_3334_loc])) [interface] (
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
  3366.
Program Definition verify (msg_3363 : message_t) (pubkey_3357 : public_key_t) (
    sig_3360 : signature_t)
  : both (CEfset (
      [y_3264_loc ; result_3277_loc ; p_3286_loc ; q_3287_loc])) [interface] (
    verification_result_t) :=
  ((letbnd(_) p_x_3358 : field_element_t :=
        option_ok_or (fieldelem_from_bytes (lift_to_both0 pubkey_3357)) (
          InvalidPublicKey) in
      letbnd(_) p_3359 : affine_point_t := lift_x (lift_to_both0 p_x_3358) in
      letbnd(_) r_3361 : field_element_t :=
        option_ok_or (fieldelem_from_bytes (array_from_slice (default : uint8) (
              32) (array_to_seq (lift_to_both0 sig_3360)) (lift_to_both0 (
                usize 0)) (lift_to_both0 (usize 32)))) (InvalidSignature) in
      letbnd(_) s_3362 : scalar_t :=
        option_ok_or (scalar_from_bytes_strict (array_from_slice (
              default : uint8) (32) (array_to_seq (lift_to_both0 sig_3360)) (
              lift_to_both0 (usize 32)) (lift_to_both0 (usize 32)))) (
          InvalidSignature) in
      letb e_3364 : scalar_t :=
        scalar_from_bytes (hash_challenge (array_from_slice (default : uint8) (
              32) (array_to_seq (lift_to_both0 sig_3360)) (lift_to_both0 (
                usize 0)) (lift_to_both0 (usize 32))) (bytes_from_point (
              lift_to_both0 p_3359)) (lift_to_both0 msg_3363)) in
      letbnd(_) r_p_3365 : (field_element_t '× field_element_t) :=
        option_ok_or (finite (point_add (point_mul_base (
                lift_to_both0 s_3362)) (point_mul ((nat_mod_zero ) -% (
                  lift_to_both0 e_3364)) (Affine (lift_to_both0 p_3359))))) (
          InvalidSignature) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        if is_pure (I := [interface]) ((negb (has_even_y (
                lift_to_both0 r_p_3365))) || ((x (
                lift_to_both0 r_p_3365)) !=.? (lift_to_both0 r_3361)))
        then @Err unit_ChoiceEquality error_t (InvalidSignature)
        else @Ok unit_ChoiceEquality error_t (tt))
      ) : both (CEfset (
        [y_3264_loc ; result_3277_loc ; p_3286_loc ; q_3287_loc])) [interface] (
      verification_result_t)).
Fail Next Obligation.

