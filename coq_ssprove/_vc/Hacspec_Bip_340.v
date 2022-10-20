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
  3000.
Program Definition finite
  : both_package (fset.fset0) [interface #val #[ SOME ] : some_inp → some_out
  ] [(FINITE,(finite_inp,finite_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(p_3001) := temp_inp : point_t in
    
    let some := fun x_0 => package_both some (x_0) in
    ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (TODO match) ) : both (
        fset.fset0) [interface #val #[ SOME ] : some_inp → some_out ] ((
          option (affine_point_t)))))in
  both_package' _ _ (FINITE,(finite_inp,finite_out)) temp_package_both.
Fail Next Obligation.


Notation "'x_inp'" :=(
  affine_point_t : choice_type) (in custom pack_type at level 2).
Notation "'x_inp'" :=(affine_point_t : ChoiceEquality) (at level 2).
Notation "'x_out'" :=(
  field_element_t : choice_type) (in custom pack_type at level 2).
Notation "'x_out'" :=(field_element_t : ChoiceEquality) (at level 2).
Definition X : nat :=
  3004.
Program Definition x
  : both_package (fset.fset0) [interface] [(X,(x_inp,x_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(p_3002) := temp_inp : affine_point_t in
    
    ((letb '(x_3003, _) : (field_element_t '× field_element_t) :=
          lift_to_both0 p_3002 in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 x_3003)
        ) : both (fset.fset0) [interface] (field_element_t)))in
  both_package' _ _ (X,(x_inp,x_out)) temp_package_both.
Fail Next Obligation.


Notation "'y_inp'" :=(
  affine_point_t : choice_type) (in custom pack_type at level 2).
Notation "'y_inp'" :=(affine_point_t : ChoiceEquality) (at level 2).
Notation "'y_out'" :=(
  field_element_t : choice_type) (in custom pack_type at level 2).
Notation "'y_out'" :=(field_element_t : ChoiceEquality) (at level 2).
Definition Y : nat :=
  3007.
Program Definition y
  : both_package (fset.fset0) [interface] [(Y,(y_inp,y_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(p_3005) := temp_inp : affine_point_t in
    
    ((letb '(_, y_3006) : (field_element_t '× field_element_t) :=
          lift_to_both0 p_3005 in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 y_3006)
        ) : both (fset.fset0) [interface] (field_element_t)))in
  both_package' _ _ (Y,(y_inp,y_out)) temp_package_both.
Fail Next Obligation.


Notation "'has_even_y_inp'" :=(
  affine_point_t : choice_type) (in custom pack_type at level 2).
Notation "'has_even_y_inp'" :=(affine_point_t : ChoiceEquality) (at level 2).
Notation "'has_even_y_out'" :=(
  bool_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'has_even_y_out'" :=(
  bool_ChoiceEquality : ChoiceEquality) (at level 2).
Definition HAS_EVEN_Y : nat :=
  3009.
Program Definition has_even_y
  : both_package (fset.fset0) [interface #val #[ Y ] : y_inp → y_out ] [(
    HAS_EVEN_Y,(has_even_y_inp,has_even_y_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(p_3008) := temp_inp : affine_point_t in
    
    let y := fun x_0 => package_both y (x_0) in
    ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (((y (
                lift_to_both0 p_3008)) rem (nat_mod_two )) =.? (nat_mod_zero ))
        ) : both (fset.fset0) [interface #val #[ Y ] : y_inp → y_out ] (
        bool_ChoiceEquality)))in
  both_package' _ _ (HAS_EVEN_Y,(
      has_even_y_inp,has_even_y_out)) temp_package_both.
Fail Next Obligation.


Notation "'sqrt_inp'" :=(
  field_element_t : choice_type) (in custom pack_type at level 2).
Notation "'sqrt_inp'" :=(field_element_t : ChoiceEquality) (at level 2).
Notation "'sqrt_out'" :=((option (
      field_element_t)) : choice_type) (in custom pack_type at level 2).
Notation "'sqrt_out'" :=((option (
      field_element_t)) : ChoiceEquality) (at level 2).
Definition SQRT : nat :=
  3013.
Program Definition sqrt
  : both_package (fset.fset0) [interface #val #[ SOME ] : some_inp → some_out
  ] [(SQRT,(sqrt_inp,sqrt_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(y_3011) := temp_inp : field_element_t in
    
    let some := fun x_0 => package_both some (x_0) in
    ((letb p1_4_3010 : field_element_t :=
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
        letb x_3012 : field_element_t :=
          nat_mod_pow_self (lift_to_both0 y_3011) (lift_to_both0 p1_4_3010) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          if is_pure (I := [interface]) ((nat_mod_pow_self (
                lift_to_both0 x_3012) (nat_mod_two )) =.? (
              lift_to_both0 y_3011))
          then some (lift_to_both0 x_3012)
          else @None field_element_t)
        ) : both (fset.fset0) [interface #val #[ SOME ] : some_inp → some_out
      ] ((option (field_element_t)))))in
  both_package' _ _ (SQRT,(sqrt_inp,sqrt_out)) temp_package_both.
Fail Next Obligation.

Definition y_3014_loc : ChoiceEqualityLocation :=
  (field_element_t ; 3015%nat).
Notation "'lift_x_inp'" :=(
  field_element_t : choice_type) (in custom pack_type at level 2).
Notation "'lift_x_inp'" :=(field_element_t : ChoiceEquality) (at level 2).
Notation "'lift_x_out'" :=((result (error_t) (
      affine_point_t)) : choice_type) (in custom pack_type at level 2).
Notation "'lift_x_out'" :=((result (error_t) (
      affine_point_t)) : ChoiceEquality) (at level 2).
Definition LIFT_X : nat :=
  3022.
Program Definition lift_x
  : both_package (CEfset ([y_3014_loc])) [interface
  #val #[ SQRT ] : sqrt_inp → sqrt_out ] [(LIFT_X,(lift_x_inp,lift_x_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(x_3020) := temp_inp : field_element_t in
    
    let sqrt := fun x_0 => package_both sqrt (x_0) in
    ((letb one_3016 : field_element_t := nat_mod_one  in
        letb two_3017 : field_element_t := nat_mod_two  in
        letb three_3018 : field_element_t :=
          nat_mod_from_literal (
            0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F) (
            lift_to_both0 (@repr U128 3)) in
        letb seven_3019 : field_element_t :=
          nat_mod_from_literal (
            0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F) (
            lift_to_both0 (@repr U128 7)) in
        letb y_sq_3021 : field_element_t :=
          (nat_mod_pow_self (lift_to_both0 x_3020) (
              lift_to_both0 three_3018)) +% (lift_to_both0 seven_3019) in
        letbndm(_) y_3014 : field_element_t :=
          option_ok_or (sqrt (lift_to_both0 y_sq_3021)) (InvalidXCoordinate) in
        letb 'y_3014 :=
          if ((lift_to_both0 y_3014) rem (lift_to_both0 two_3017)) =.? (
            lift_to_both0 one_3016) :bool_ChoiceEquality
          then lift_scope (L1 := CEfset ([y_3014_loc])) (L2 := CEfset (
            [y_3014_loc])) (I1 := [interface]) (I2 := [interface
          #val #[ SQRT ] : sqrt_inp → sqrt_out
          ]) (H_loc_incl := _) (H_opsig_incl := _) (
            letbm y_3014 loc( y_3014_loc ) :=
              (nat_mod_zero ) -% (lift_to_both0 y_3014) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 y_3014)
            )
          else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 y_3014)
           in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          @Ok affine_point_t error_t (prod_b(
              lift_to_both0 x_3020,
              lift_to_both0 y_3014
            )))
        ) : both (CEfset ([y_3014_loc])) [interface
      #val #[ SQRT ] : sqrt_inp → sqrt_out ] ((result (error_t) (
            affine_point_t)))))in
  both_package' _ _ (LIFT_X,(lift_x_inp,lift_x_out)) temp_package_both.
Fail Next Obligation.


Notation "'compute_lam_inp'" :=(
  affine_point_t '× affine_point_t : choice_type) (in custom pack_type at level 2).
Notation "'compute_lam_inp'" :=(
  affine_point_t '× affine_point_t : ChoiceEquality) (at level 2).
Notation "'compute_lam_out'" :=(
  field_element_t : choice_type) (in custom pack_type at level 2).
Notation "'compute_lam_out'" :=(field_element_t : ChoiceEquality) (at level 2).
Definition COMPUTE_LAM : nat :=
  3026.
Program Definition compute_lam
  : both_package (fset.fset0) [interface #val #[ X ] : x_inp → x_out ;
  #val #[ Y ] : y_inp → y_out ] [(COMPUTE_LAM,(
      compute_lam_inp,compute_lam_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(p1_3024 , p2_3025) := temp_inp : affine_point_t '× affine_point_t in
    
    let x := fun x_0 => package_both x (x_0) in
    let y := fun x_0 => package_both y (x_0) in
    ((letb three_3023 : field_element_t :=
          nat_mod_from_literal (
            0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F) (
            lift_to_both0 (@repr U128 3)) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          if is_pure (I := [interface]) ((lift_to_both0 p1_3024) !=.? (
              lift_to_both0 p2_3025))
          then ((y (lift_to_both0 p2_3025)) -% (y (lift_to_both0 p1_3024))) *% (
            nat_mod_pow_self ((x (lift_to_both0 p2_3025)) -% (x (
                  lift_to_both0 p1_3024))) ((nat_mod_zero ) -% (nat_mod_two )))
          else (((lift_to_both0 three_3023) *% (x (lift_to_both0 p1_3024))) *% (
              x (lift_to_both0 p1_3024))) *% (nat_mod_pow_self ((
                nat_mod_two ) *% (y (lift_to_both0 p1_3024))) ((
                nat_mod_zero ) -% (nat_mod_two ))))
        ) : both (fset.fset0) [interface #val #[ X ] : x_inp → x_out ;
      #val #[ Y ] : y_inp → y_out ] (field_element_t)))in
  both_package' _ _ (COMPUTE_LAM,(
      compute_lam_inp,compute_lam_out)) temp_package_both.
Fail Next Obligation.

Definition result_3027_loc : ChoiceEqualityLocation :=
  (point_t ; 3028%nat).
Notation "'point_add_inp'" :=(
  point_t '× point_t : choice_type) (in custom pack_type at level 2).
Notation "'point_add_inp'" :=(
  point_t '× point_t : ChoiceEquality) (at level 2).
Notation "'point_add_out'" :=(
  point_t : choice_type) (in custom pack_type at level 2).
Notation "'point_add_out'" :=(point_t : ChoiceEquality) (at level 2).
Definition POINT_ADD : nat :=
  3035.
Program Definition point_add
  : both_package (CEfset ([result_3027_loc])) [interface
  #val #[ COMPUTE_LAM ] : compute_lam_inp → compute_lam_out ;
  #val #[ FINITE ] : finite_inp → finite_out ; #val #[ X ] : x_inp → x_out ;
  #val #[ Y ] : y_inp → y_out ] [(POINT_ADD,(point_add_inp,point_add_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(p1_3029 , p2_3030) := temp_inp : point_t '× point_t in
    
    let compute_lam := fun x_0 x_1 => package_both compute_lam (x_0,x_1) in
    let finite := fun x_0 => package_both finite (x_0) in
    let x := fun x_0 => package_both x (x_0) in
    let y := fun x_0 => package_both y (x_0) in
    ((letbm result_3027 : point_t loc( result_3027_loc ) := AtInfinity in
        letb 'result_3027 :=
          if option_is_none (finite (
              lift_to_both0 p1_3029)) :bool_ChoiceEquality
          then lift_scope (L1 := CEfset ([result_3027_loc])) (L2 := CEfset (
            [result_3027_loc])) (I1 := [interface]) (I2 := [interface
          #val #[ COMPUTE_LAM ] : compute_lam_inp → compute_lam_out ;
          #val #[ FINITE ] : finite_inp → finite_out ;
          #val #[ X ] : x_inp → x_out ; #val #[ Y ] : y_inp → y_out
          ]) (H_loc_incl := _) (H_opsig_incl := _) (
            letbm result_3027 loc( result_3027_loc ) := lift_to_both0 p2_3030 in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 result_3027)
            )
          else  lift_scope (L1 := CEfset ([result_3027_loc])) (L2 := CEfset (
            [result_3027_loc])) (I1 := [interface
          #val #[ COMPUTE_LAM ] : compute_lam_inp → compute_lam_out ;
          #val #[ FINITE ] : finite_inp → finite_out ;
          #val #[ X ] : x_inp → x_out ; #val #[ Y ] : y_inp → y_out
          ]) (I2 := [interface
          #val #[ COMPUTE_LAM ] : compute_lam_inp → compute_lam_out ;
          #val #[ FINITE ] : finite_inp → finite_out ;
          #val #[ X ] : x_inp → x_out ; #val #[ Y ] : y_inp → y_out
          ]) (H_loc_incl := _) (H_opsig_incl := _) (letb 'result_3027 :=
              if option_is_none (finite (
                  lift_to_both0 p2_3030)) :bool_ChoiceEquality
              then lift_scope (L1 := CEfset ([result_3027_loc])) (L2 := CEfset (
                [result_3027_loc])) (I1 := [interface]) (I2 := [interface
              #val #[ COMPUTE_LAM ] : compute_lam_inp → compute_lam_out ;
              #val #[ FINITE ] : finite_inp → finite_out ;
              #val #[ X ] : x_inp → x_out ; #val #[ Y ] : y_inp → y_out
              ]) (H_loc_incl := _) (H_opsig_incl := _) (
                letbm result_3027 loc( result_3027_loc ) :=
                  lift_to_both0 p1_3029 in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                  lift_to_both0 result_3027)
                )
              else  lift_scope (L1 := CEfset (
                [result_3027_loc])) (L2 := CEfset (
                [result_3027_loc])) (I1 := [interface
              #val #[ COMPUTE_LAM ] : compute_lam_inp → compute_lam_out ;
              #val #[ FINITE ] : finite_inp → finite_out ;
              #val #[ X ] : x_inp → x_out ; #val #[ Y ] : y_inp → y_out
              ]) (I2 := [interface
              #val #[ COMPUTE_LAM ] : compute_lam_inp → compute_lam_out ;
              #val #[ FINITE ] : finite_inp → finite_out ;
              #val #[ X ] : x_inp → x_out ; #val #[ Y ] : y_inp → y_out
              ]) (H_loc_incl := _) (H_opsig_incl := _) (letb p1_3031 : (
                    field_element_t '×
                    field_element_t
                  ) :=
                  option_unwrap (finite (lift_to_both0 p1_3029)) in
                letb p2_3032 : (field_element_t '× field_element_t) :=
                  option_unwrap (finite (lift_to_both0 p2_3030)) in
                letb 'result_3027 :=
                  if negb (((x (lift_to_both0 p1_3031)) =.? (x (
                          lift_to_both0 p2_3032))) && ((y (
                          lift_to_both0 p1_3031)) !=.? (y (
                          lift_to_both0 p2_3032)))) :bool_ChoiceEquality
                  then lift_scope (L1 := CEfset (
                    [result_3027_loc])) (L2 := CEfset (
                    [result_3027_loc])) (I1 := [interface
                  #val #[ COMPUTE_LAM ] : compute_lam_inp → compute_lam_out ;
                  #val #[ X ] : x_inp → x_out ; #val #[ Y ] : y_inp → y_out
                  ]) (I2 := [interface
                  #val #[ COMPUTE_LAM ] : compute_lam_inp → compute_lam_out ;
                  #val #[ FINITE ] : finite_inp → finite_out ;
                  #val #[ X ] : x_inp → x_out ; #val #[ Y ] : y_inp → y_out
                  ]) (H_loc_incl := _) (H_opsig_incl := _) (
                    letb lam_3033 : field_element_t :=
                      compute_lam (lift_to_both0 p1_3031) (
                        lift_to_both0 p2_3032) in
                    letb x3_3034 : field_element_t :=
                      (((lift_to_both0 lam_3033) *% (
                            lift_to_both0 lam_3033)) -% (x (
                            lift_to_both0 p1_3031))) -% (x (
                          lift_to_both0 p2_3032)) in
                    letbm result_3027 loc( result_3027_loc ) :=
                      Affine (prod_b(
                          lift_to_both0 x3_3034,
                          ((lift_to_both0 lam_3033) *% ((x (
                                  lift_to_both0 p1_3031)) -% (
                                lift_to_both0 x3_3034))) -% (y (
                              lift_to_both0 p1_3031))
                        )) in
                    lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                      lift_to_both0 result_3027)
                    )
                  else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                    lift_to_both0 result_3027)
                   in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                  lift_to_both0 result_3027)
                ) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 result_3027)
            ) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          lift_to_both0 result_3027)
        ) : both (CEfset ([result_3027_loc])) [interface
      #val #[ COMPUTE_LAM ] : compute_lam_inp → compute_lam_out ;
      #val #[ FINITE ] : finite_inp → finite_out ;
      #val #[ X ] : x_inp → x_out ; #val #[ Y ] : y_inp → y_out ] (
        point_t)))in
  both_package' _ _ (POINT_ADD,(point_add_inp,point_add_out)) temp_package_both.
Fail Next Obligation.

Definition q_3037_loc : ChoiceEqualityLocation :=
  (point_t ; 3038%nat).
Definition p_3036_loc : ChoiceEqualityLocation :=
  (point_t ; 3039%nat).
Notation "'point_mul_inp'" :=(
  scalar_t '× point_t : choice_type) (in custom pack_type at level 2).
Notation "'point_mul_inp'" :=(
  scalar_t '× point_t : ChoiceEquality) (at level 2).
Notation "'point_mul_out'" :=(
  point_t : choice_type) (in custom pack_type at level 2).
Notation "'point_mul_out'" :=(point_t : ChoiceEquality) (at level 2).
Definition POINT_MUL : nat :=
  3043.
Program Definition point_mul
  : both_package (CEfset ([p_3036_loc ; q_3037_loc])) [interface
  #val #[ POINT_ADD ] : point_add_inp → point_add_out ] [(POINT_MUL,(
      point_mul_inp,point_mul_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(s_3042 , p_3040) := temp_inp : scalar_t '× point_t in
    
    let point_add := fun x_0 x_1 => package_both point_add (x_0,x_1) in
    ((letbm p_3036 : point_t loc( p_3036_loc ) := lift_to_both0 p_3040 in
        letbm q_3037 : point_t loc( q_3037_loc ) := AtInfinity in
        letb '(p_3036, q_3037) :=
          foldi_both' (lift_to_both0 (usize 0)) (lift_to_both0 (
                usize 256)) prod_ce(p_3036, q_3037) (L := (CEfset (
                [p_3036_loc ; q_3037_loc]))) (I := ([interface
              #val #[ POINT_ADD ] : point_add_inp → point_add_out
              ])) (fun i_3041 '(p_3036, q_3037) =>
            letb 'q_3037 :=
              if nat_mod_bit (lift_to_both0 s_3042) (
                lift_to_both0 i_3041) :bool_ChoiceEquality
              then lift_scope (L1 := CEfset (
                [p_3036_loc ; q_3037_loc])) (L2 := CEfset (
                [p_3036_loc ; q_3037_loc])) (I1 := [interface
              #val #[ POINT_ADD ] : point_add_inp → point_add_out
              ]) (I2 := [interface
              #val #[ POINT_ADD ] : point_add_inp → point_add_out
              ]) (H_loc_incl := _) (H_opsig_incl := _) (
                letbm q_3037 loc( q_3037_loc ) :=
                  point_add (lift_to_both0 q_3037) (lift_to_both0 p_3036) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                  lift_to_both0 q_3037)
                )
              else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                lift_to_both0 q_3037)
               in
            letbm p_3036 loc( p_3036_loc ) :=
              point_add (lift_to_both0 p_3036) (lift_to_both0 p_3036) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                lift_to_both0 p_3036,
                lift_to_both0 q_3037
              ))
            ) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 q_3037)
        ) : both (CEfset ([p_3036_loc ; q_3037_loc])) [interface
      #val #[ POINT_ADD ] : point_add_inp → point_add_out ] (point_t)))in
  both_package' _ _ (POINT_MUL,(point_mul_inp,point_mul_out)) temp_package_both.
Fail Next Obligation.


Notation "'point_mul_base_inp'" :=(
  scalar_t : choice_type) (in custom pack_type at level 2).
Notation "'point_mul_base_inp'" :=(scalar_t : ChoiceEquality) (at level 2).
Notation "'point_mul_base_out'" :=(
  point_t : choice_type) (in custom pack_type at level 2).
Notation "'point_mul_base_out'" :=(point_t : ChoiceEquality) (at level 2).
Definition POINT_MUL_BASE : nat :=
  3048.
Program Definition point_mul_base
  : both_package (CEfset ([])) [interface
  #val #[ POINT_MUL ] : point_mul_inp → point_mul_out ] [(POINT_MUL_BASE,(
      point_mul_base_inp,point_mul_base_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(s_3047) := temp_inp : scalar_t in
    
    let point_mul := fun x_0 x_1 => package_both point_mul (x_0,x_1) in
    ((letb gx_3044 : p_bytes32_t :=
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
        letb gy_3045 : p_bytes32_t :=
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
        letb g_3046 : point_t :=
          Affine (prod_b(
              nat_mod_from_public_byte_seq_be (lift_to_both0 gx_3044),
              nat_mod_from_public_byte_seq_be (lift_to_both0 gy_3045)
            )) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (point_mul (
            lift_to_both0 s_3047) (lift_to_both0 g_3046))
        ) : both (CEfset ([])) [interface
      #val #[ POINT_MUL ] : point_mul_inp → point_mul_out ] (point_t)))in
  both_package' _ _ (POINT_MUL_BASE,(
      point_mul_base_inp,point_mul_base_out)) temp_package_both.
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
  3053.
Program Definition tagged_hash
  : both_package (fset.fset0) [interface
  #val #[ SHA256 ] : sha256_inp → sha256_out ] [(TAGGED_HASH,(
      tagged_hash_inp,tagged_hash_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(tag_3049 , msg_3051) := temp_inp : public_byte_seq '× byte_seq in
    
    let sha256 := fun x_0 => package_both sha256 (x_0) in
    ((letb tag_hash_3050 : seq uint8 :=
          array_to_be_bytes (sha256 (seq_from_public_seq (
                lift_to_both0 tag_3049))) in
        letb hash_3052 : sha256_digest_t :=
          sha256 (seq_concat (seq_concat (lift_to_both0 tag_hash_3050) (
                lift_to_both0 tag_hash_3050)) (lift_to_both0 msg_3051)) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (array_from_seq (32) (
            array_to_seq (lift_to_both0 hash_3052)))
        ) : both (fset.fset0) [interface
      #val #[ SHA256 ] : sha256_inp → sha256_out ] (bytes32_t)))in
  both_package' _ _ (TAGGED_HASH,(
      tagged_hash_inp,tagged_hash_out)) temp_package_both.
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
  3055.
Program Definition hash_aux
  : both_package (fset.fset0) [interface
  #val #[ TAGGED_HASH ] : tagged_hash_inp → tagged_hash_out ] [(HASH_AUX,(
      hash_aux_inp,hash_aux_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(aux_rand_3054) := temp_inp : aux_rand_t in
    
    let tagged_hash := fun x_0 x_1 => package_both tagged_hash (x_0,x_1) in
    ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (tagged_hash (
            seq_from_seq (array_to_seq (lift_to_both0 bip0340_aux_v))) (
            seq_from_seq (lift_to_both0 aux_rand_3054)))
        ) : both (fset.fset0) [interface
      #val #[ TAGGED_HASH ] : tagged_hash_inp → tagged_hash_out ] (
        bytes32_t)))in
  both_package' _ _ (HASH_AUX,(hash_aux_inp,hash_aux_out)) temp_package_both.
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
  3060.
Program Definition hash_nonce
  : both_package (fset.fset0) [interface
  #val #[ TAGGED_HASH ] : tagged_hash_inp → tagged_hash_out ] [(HASH_NONCE,(
      hash_nonce_inp,hash_nonce_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(
      rand_3056 , pubkey_3057 , msg_3058) := temp_inp : bytes32_t '× bytes32_t '× message_t in
    
    let tagged_hash := fun x_0 x_1 => package_both tagged_hash (x_0,x_1) in
    ((letb c_3059 : byte_seq :=
          seq_concat (seq_concat (seq_from_seq (
                array_to_seq (lift_to_both0 rand_3056))) (
              array_to_seq (lift_to_both0 pubkey_3057))) (
            lift_to_both0 msg_3058) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (tagged_hash (
            seq_from_seq (array_to_seq (lift_to_both0 bip0340_nonce_v))) (
            lift_to_both0 c_3059))
        ) : both (fset.fset0) [interface
      #val #[ TAGGED_HASH ] : tagged_hash_inp → tagged_hash_out ] (
        bytes32_t)))in
  both_package' _ _ (HASH_NONCE,(
      hash_nonce_inp,hash_nonce_out)) temp_package_both.
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
  3065.
Program Definition hash_challenge
  : both_package (fset.fset0) [interface
  #val #[ TAGGED_HASH ] : tagged_hash_inp → tagged_hash_out ] [(
    HASH_CHALLENGE,(hash_challenge_inp,hash_challenge_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(
      rx_3061 , pubkey_3062 , msg_3063) := temp_inp : bytes32_t '× bytes32_t '× bytes32_t in
    
    let tagged_hash := fun x_0 x_1 => package_both tagged_hash (x_0,x_1) in
    ((letb c_3064 : byte_seq :=
          seq_concat (seq_concat (seq_from_seq (
                array_to_seq (lift_to_both0 rx_3061))) (
              array_to_seq (lift_to_both0 pubkey_3062))) (
            array_to_seq (lift_to_both0 msg_3063)) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (tagged_hash (
            seq_from_seq (array_to_seq (lift_to_both0 bip0340_challenge_v))) (
            lift_to_both0 c_3064))
        ) : both (fset.fset0) [interface
      #val #[ TAGGED_HASH ] : tagged_hash_inp → tagged_hash_out ] (
        bytes32_t)))in
  both_package' _ _ (HASH_CHALLENGE,(
      hash_challenge_inp,hash_challenge_out)) temp_package_both.
Fail Next Obligation.


Notation "'bytes_from_point_inp'" :=(
  affine_point_t : choice_type) (in custom pack_type at level 2).
Notation "'bytes_from_point_inp'" :=(
  affine_point_t : ChoiceEquality) (at level 2).
Notation "'bytes_from_point_out'" :=(
  bytes32_t : choice_type) (in custom pack_type at level 2).
Notation "'bytes_from_point_out'" :=(bytes32_t : ChoiceEquality) (at level 2).
Definition BYTES_FROM_POINT : nat :=
  3068.
Program Definition bytes_from_point
  : both_package (fset.fset0) [interface] [(BYTES_FROM_POINT,(
      bytes_from_point_inp,bytes_from_point_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(p_3066) := temp_inp : affine_point_t in
    
    ((letb '(x_3067, _) : (field_element_t '× field_element_t) :=
          lift_to_both0 p_3066 in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (array_from_seq (32) (
            nat_mod_to_byte_seq_be (lift_to_both0 x_3067)))
        ) : both (fset.fset0) [interface] (bytes32_t)))in
  both_package' _ _ (BYTES_FROM_POINT,(
      bytes_from_point_inp,bytes_from_point_out)) temp_package_both.
Fail Next Obligation.


Notation "'bytes_from_scalar_inp'" :=(
  scalar_t : choice_type) (in custom pack_type at level 2).
Notation "'bytes_from_scalar_inp'" :=(scalar_t : ChoiceEquality) (at level 2).
Notation "'bytes_from_scalar_out'" :=(
  bytes32_t : choice_type) (in custom pack_type at level 2).
Notation "'bytes_from_scalar_out'" :=(bytes32_t : ChoiceEquality) (at level 2).
Definition BYTES_FROM_SCALAR : nat :=
  3070.
Program Definition bytes_from_scalar
  : both_package (fset.fset0) [interface] [(BYTES_FROM_SCALAR,(
      bytes_from_scalar_inp,bytes_from_scalar_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(x_3069) := temp_inp : scalar_t in
    
    ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (array_from_seq (32) (
            nat_mod_to_byte_seq_be (lift_to_both0 x_3069)))
        ) : both (fset.fset0) [interface] (bytes32_t)))in
  both_package' _ _ (BYTES_FROM_SCALAR,(
      bytes_from_scalar_inp,bytes_from_scalar_out)) temp_package_both.
Fail Next Obligation.


Notation "'scalar_from_bytes_inp'" :=(
  bytes32_t : choice_type) (in custom pack_type at level 2).
Notation "'scalar_from_bytes_inp'" :=(bytes32_t : ChoiceEquality) (at level 2).
Notation "'scalar_from_bytes_out'" :=(
  scalar_t : choice_type) (in custom pack_type at level 2).
Notation "'scalar_from_bytes_out'" :=(scalar_t : ChoiceEquality) (at level 2).
Definition SCALAR_FROM_BYTES : nat :=
  3072.
Program Definition scalar_from_bytes
  : both_package (fset.fset0) [interface] [(SCALAR_FROM_BYTES,(
      scalar_from_bytes_inp,scalar_from_bytes_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(b_3071) := temp_inp : bytes32_t in
    
    ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          nat_mod_from_byte_seq_be (array_to_seq (lift_to_both0 b_3071)))
        ) : both (fset.fset0) [interface] (scalar_t)))in
  both_package' _ _ (SCALAR_FROM_BYTES,(
      scalar_from_bytes_inp,scalar_from_bytes_out)) temp_package_both.
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
  3076.
Program Definition scalar_from_bytes_strict
  : both_package (fset.fset0) [interface] [(SCALAR_FROM_BYTES_STRICT,(
      scalar_from_bytes_strict_inp,scalar_from_bytes_strict_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(b_3073) := temp_inp : bytes32_t in
    
    ((letb s_3074 : big_integer_t :=
          nat_mod_from_byte_seq_be (array_to_seq (lift_to_both0 b_3073)) in
        letb max_scalar_3075 : big_integer_t :=
          nat_mod_from_byte_seq_be (nat_mod_to_byte_seq_be (
              nat_mod_max_val )) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          if is_pure (I := [interface]) ((lift_to_both0 s_3074) >.? (
              lift_to_both0 max_scalar_3075))
          then @None scalar_t
          else @Some scalar_t (nat_mod_from_byte_seq_be (
              array_to_seq (lift_to_both0 b_3073))))
        ) : both (fset.fset0) [interface] ((option (scalar_t)))))in
  both_package' _ _ (SCALAR_FROM_BYTES_STRICT,(
      scalar_from_bytes_strict_inp,scalar_from_bytes_strict_out)) temp_package_both.
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
  3079.
Program Definition seckey_scalar_from_bytes
  : both_package (fset.fset0) [interface
  #val #[ SCALAR_FROM_BYTES_STRICT ] : scalar_from_bytes_strict_inp → scalar_from_bytes_strict_out
  ] [(SECKEY_SCALAR_FROM_BYTES,(
      seckey_scalar_from_bytes_inp,seckey_scalar_from_bytes_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(b_3077) := temp_inp : bytes32_t in
    
    let scalar_from_bytes_strict := fun x_0 => package_both scalar_from_bytes_strict (
      x_0) in
    ((letbnd(_) s_3078 : scalar_t :=
          scalar_from_bytes_strict (lift_to_both0 b_3077) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          if is_pure (I := [interface]) ((lift_to_both0 s_3078) =.? (
              nat_mod_zero ))
          then @None scalar_t
          else @Some scalar_t (lift_to_both0 s_3078))
        ) : both (fset.fset0) [interface
      #val #[ SCALAR_FROM_BYTES_STRICT ] : scalar_from_bytes_strict_inp → scalar_from_bytes_strict_out
      ] ((option (scalar_t)))))in
  both_package' _ _ (SECKEY_SCALAR_FROM_BYTES,(
      seckey_scalar_from_bytes_inp,seckey_scalar_from_bytes_out)) temp_package_both.
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
  3083.
Program Definition fieldelem_from_bytes
  : both_package (fset.fset0) [interface] [(FIELDELEM_FROM_BYTES,(
      fieldelem_from_bytes_inp,fieldelem_from_bytes_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(b_3080) := temp_inp : public_key_t in
    
    ((letb s_3081 : big_integer_t :=
          nat_mod_from_byte_seq_be (lift_to_both0 b_3080) in
        letb max_fe_3082 : big_integer_t :=
          nat_mod_from_byte_seq_be (nat_mod_to_byte_seq_be (
              nat_mod_max_val )) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          if is_pure (I := [interface]) ((lift_to_both0 s_3081) >.? (
              lift_to_both0 max_fe_3082))
          then @None field_element_t
          else @Some field_element_t (nat_mod_from_byte_seq_be (
              lift_to_both0 b_3080)))
        ) : both (fset.fset0) [interface] ((option (field_element_t)))))in
  both_package' _ _ (FIELDELEM_FROM_BYTES,(
      fieldelem_from_bytes_inp,fieldelem_from_bytes_out)) temp_package_both.
Fail Next Obligation.

Definition b_3084_loc : ChoiceEqualityLocation :=
  (seq uint8 ; 3085%nat).
Notation "'xor_bytes_inp'" :=(
  bytes32_t '× bytes32_t : choice_type) (in custom pack_type at level 2).
Notation "'xor_bytes_inp'" :=(
  bytes32_t '× bytes32_t : ChoiceEquality) (at level 2).
Notation "'xor_bytes_out'" :=(
  bytes32_t : choice_type) (in custom pack_type at level 2).
Notation "'xor_bytes_out'" :=(bytes32_t : ChoiceEquality) (at level 2).
Definition XOR_BYTES : nat :=
  3089.
Program Definition xor_bytes
  : both_package (CEfset ([b_3084_loc])) [interface] [(XOR_BYTES,(
      xor_bytes_inp,xor_bytes_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(b0_3086 , b1_3088) := temp_inp : bytes32_t '× bytes32_t in
    
    ((letbm b_3084 : seq uint8 loc( b_3084_loc ) :=
          seq_new_ (default : uint8) (array_len (lift_to_both0 b0_3086)) in
        letb b_3084 :=
          foldi_both' (lift_to_both0 (usize 0)) (array_len (
                lift_to_both0 b0_3086)) b_3084 (L := (CEfset (
                [b_3084_loc]))) (I := ([interface])) (fun i_3087 b_3084 =>
            letb b_3084 : seq uint8 :=
              seq_upd b_3084 (lift_to_both0 i_3087) (is_pure ((array_index (
                      b0_3086) (lift_to_both0 i_3087)) .^ (array_index (
                      b1_3088) (lift_to_both0 i_3087)))) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 b_3084)
            ) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (array_from_seq (32) (
            lift_to_both0 b_3084))
        ) : both (CEfset ([b_3084_loc])) [interface] (bytes32_t)))in
  both_package' _ _ (XOR_BYTES,(xor_bytes_inp,xor_bytes_out)) temp_package_both.
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
  3093.
Program Definition pubkey_gen
  : both_package (CEfset ([])) [interface
  #val #[ BYTES_FROM_POINT ] : bytes_from_point_inp → bytes_from_point_out ;
  #val #[ FINITE ] : finite_inp → finite_out ;
  #val #[ POINT_MUL_BASE ] : point_mul_base_inp → point_mul_base_out ;
  #val #[ SECKEY_SCALAR_FROM_BYTES ] : seckey_scalar_from_bytes_inp → seckey_scalar_from_bytes_out
  ] [(PUBKEY_GEN,(pubkey_gen_inp,pubkey_gen_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(seckey_3090) := temp_inp : secret_key_t in
    
    let bytes_from_point := fun x_0 => package_both bytes_from_point (x_0) in
    let finite := fun x_0 => package_both finite (x_0) in
    let point_mul_base := fun x_0 => package_both point_mul_base (x_0) in
    let seckey_scalar_from_bytes := fun x_0 => package_both seckey_scalar_from_bytes (
      x_0) in
    ((letbnd(_) d0_3091 : scalar_t :=
          option_ok_or (seckey_scalar_from_bytes (lift_to_both0 seckey_3090)) (
            InvalidSecretKey) in
        letb p_3092 : (field_element_t '× field_element_t) :=
          option_unwrap (finite (point_mul_base (lift_to_both0 d0_3091))) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          @Ok public_key_t error_t (bytes_from_point (lift_to_both0 p_3092)))
        ) : both (CEfset ([])) [interface
      #val #[ BYTES_FROM_POINT ] : bytes_from_point_inp → bytes_from_point_out ;
      #val #[ FINITE ] : finite_inp → finite_out ;
      #val #[ POINT_MUL_BASE ] : point_mul_base_inp → point_mul_base_out ;
      #val #[ SECKEY_SCALAR_FROM_BYTES ] : seckey_scalar_from_bytes_inp → seckey_scalar_from_bytes_out
      ] (pubkey_gen_result_t)))in
  both_package' _ _ (PUBKEY_GEN,(
      pubkey_gen_inp,pubkey_gen_out)) temp_package_both.
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
  3106.
Program Definition sign
  : both_package (CEfset ([])) [interface
  #val #[ BYTES_FROM_POINT ] : bytes_from_point_inp → bytes_from_point_out ;
  #val #[ BYTES_FROM_SCALAR ] : bytes_from_scalar_inp → bytes_from_scalar_out ;
  #val #[ FINITE ] : finite_inp → finite_out ;
  #val #[ HAS_EVEN_Y ] : has_even_y_inp → has_even_y_out ;
  #val #[ HASH_AUX ] : hash_aux_inp → hash_aux_out ;
  #val #[ HASH_CHALLENGE ] : hash_challenge_inp → hash_challenge_out ;
  #val #[ HASH_NONCE ] : hash_nonce_inp → hash_nonce_out ;
  #val #[ POINT_MUL_BASE ] : point_mul_base_inp → point_mul_base_out ;
  #val #[ SCALAR_FROM_BYTES ] : scalar_from_bytes_inp → scalar_from_bytes_out ;
  #val #[ SECKEY_SCALAR_FROM_BYTES ] : seckey_scalar_from_bytes_inp → seckey_scalar_from_bytes_out ;
  #val #[ VERIFY ] : verify_inp → verify_out ;
  #val #[ XOR_BYTES ] : xor_bytes_inp → xor_bytes_out ] [(SIGN,(
      sign_inp,sign_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(
      msg_3100 , seckey_3094 , aux_rand_3098) := temp_inp : message_t '× secret_key_t '× aux_rand_t in
    
    let bytes_from_point := fun x_0 => package_both bytes_from_point (x_0) in
    let bytes_from_scalar := fun x_0 => package_both bytes_from_scalar (x_0) in
    let finite := fun x_0 => package_both finite (x_0) in
    let has_even_y := fun x_0 => package_both has_even_y (x_0) in
    let hash_aux := fun x_0 => package_both hash_aux (x_0) in
    let hash_challenge := fun x_0 x_1 x_2 => package_both hash_challenge (
      x_0,x_1,x_2) in
    let hash_nonce := fun x_0 x_1 x_2 => package_both hash_nonce (
      x_0,x_1,x_2) in
    let point_mul_base := fun x_0 => package_both point_mul_base (x_0) in
    let scalar_from_bytes := fun x_0 => package_both scalar_from_bytes (x_0) in
    let seckey_scalar_from_bytes := fun x_0 => package_both seckey_scalar_from_bytes (
      x_0) in
    let verify := fun x_0 x_1 x_2 => package_both verify (x_0,x_1,x_2) in
    let xor_bytes := fun x_0 x_1 => package_both xor_bytes (x_0,x_1) in
    ((letbnd(_) d0_3095 : scalar_t :=
          option_ok_or (seckey_scalar_from_bytes (lift_to_both0 seckey_3094)) (
            InvalidSecretKey) in
        letb p_3096 : (field_element_t '× field_element_t) :=
          option_unwrap (finite (point_mul_base (lift_to_both0 d0_3095))) in
        letb d_3097 : scalar_t :=
          if is_pure (I := [interface]) (has_even_y (lift_to_both0 p_3096))
          then lift_to_both0 d0_3095
          else (nat_mod_zero ) -% (lift_to_both0 d0_3095) in
        letb t_3099 : bytes32_t :=
          xor_bytes (bytes_from_scalar (lift_to_both0 d_3097)) (hash_aux (
              lift_to_both0 aux_rand_3098)) in
        letb k0_3101 : scalar_t :=
          scalar_from_bytes (hash_nonce (lift_to_both0 t_3099) (
              bytes_from_point (lift_to_both0 p_3096)) (
              lift_to_both0 msg_3100)) in
        letbnd(_) 'tt :=
          if (lift_to_both0 k0_3101) =.? (nat_mod_zero ) :bool_ChoiceEquality
          then lift_scope (L1 := CEfset ([])) (L2 := CEfset (
            [])) (I1 := [interface]) (I2 := [interface
          #val #[ BYTES_FROM_POINT ] : bytes_from_point_inp → bytes_from_point_out ;
          #val #[ BYTES_FROM_SCALAR ] : bytes_from_scalar_inp → bytes_from_scalar_out ;
          #val #[ FINITE ] : finite_inp → finite_out ;
          #val #[ HAS_EVEN_Y ] : has_even_y_inp → has_even_y_out ;
          #val #[ HASH_AUX ] : hash_aux_inp → hash_aux_out ;
          #val #[ HASH_CHALLENGE ] : hash_challenge_inp → hash_challenge_out ;
          #val #[ HASH_NONCE ] : hash_nonce_inp → hash_nonce_out ;
          #val #[ POINT_MUL_BASE ] : point_mul_base_inp → point_mul_base_out ;
          #val #[ SCALAR_FROM_BYTES ] : scalar_from_bytes_inp → scalar_from_bytes_out ;
          #val #[ SECKEY_SCALAR_FROM_BYTES ] : seckey_scalar_from_bytes_inp → seckey_scalar_from_bytes_out ;
          #val #[ VERIFY ] : verify_inp → verify_out ;
          #val #[ XOR_BYTES ] : xor_bytes_inp → xor_bytes_out
          ]) (H_loc_incl := _) (H_opsig_incl := _) (letbnd(_) _ : signature_t :=
              @Err signature_t error_t (InvalidNonceGenerated) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              @Ok unit_ChoiceEquality error_t (lift_to_both0 (
                  (tt : unit_ChoiceEquality))))
            )
          else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            @Ok unit_ChoiceEquality error_t (lift_to_both0 (
                (tt : unit_ChoiceEquality))))
           in
        letb r_3102 : (field_element_t '× field_element_t) :=
          option_unwrap (finite (point_mul_base (lift_to_both0 k0_3101))) in
        letb k_3103 : scalar_t :=
          if is_pure (I := [interface]) (has_even_y (lift_to_both0 r_3102))
          then lift_to_both0 k0_3101
          else (nat_mod_zero ) -% (lift_to_both0 k0_3101) in
        letb e_3104 : scalar_t :=
          scalar_from_bytes (hash_challenge (bytes_from_point (
                lift_to_both0 r_3102)) (bytes_from_point (
                lift_to_both0 p_3096)) (lift_to_both0 msg_3100)) in
        letb sig_3105 : signature_t :=
          array_update (array_update (array_new_ (default : uint8) (64)) (
              lift_to_both0 (usize 0)) (array_to_seq (bytes_from_point (
                lift_to_both0 r_3102)))) (lift_to_both0 (usize 32)) (
            array_to_seq (bytes_from_scalar ((lift_to_both0 k_3103) +% ((
                  lift_to_both0 e_3104) *% (lift_to_both0 d_3097))))) in
        letbnd(_) _ : unit_ChoiceEquality :=
          verify (lift_to_both0 msg_3100) (bytes_from_point (
              lift_to_both0 p_3096)) (lift_to_both0 sig_3105) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          @Ok signature_t error_t (lift_to_both0 sig_3105))
        ) : both (CEfset ([])) [interface
      #val #[ BYTES_FROM_POINT ] : bytes_from_point_inp → bytes_from_point_out ;
      #val #[ BYTES_FROM_SCALAR ] : bytes_from_scalar_inp → bytes_from_scalar_out ;
      #val #[ FINITE ] : finite_inp → finite_out ;
      #val #[ HAS_EVEN_Y ] : has_even_y_inp → has_even_y_out ;
      #val #[ HASH_AUX ] : hash_aux_inp → hash_aux_out ;
      #val #[ HASH_CHALLENGE ] : hash_challenge_inp → hash_challenge_out ;
      #val #[ HASH_NONCE ] : hash_nonce_inp → hash_nonce_out ;
      #val #[ POINT_MUL_BASE ] : point_mul_base_inp → point_mul_base_out ;
      #val #[ SCALAR_FROM_BYTES ] : scalar_from_bytes_inp → scalar_from_bytes_out ;
      #val #[ SECKEY_SCALAR_FROM_BYTES ] : seckey_scalar_from_bytes_inp → seckey_scalar_from_bytes_out ;
      #val #[ VERIFY ] : verify_inp → verify_out ;
      #val #[ XOR_BYTES ] : xor_bytes_inp → xor_bytes_out ] (
        sign_result_t)))in
  both_package' _ _ (SIGN,(sign_inp,sign_out)) temp_package_both.
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
  3116.
Program Definition verify
  : both_package (CEfset ([])) [interface
  #val #[ BYTES_FROM_POINT ] : bytes_from_point_inp → bytes_from_point_out ;
  #val #[ FIELDELEM_FROM_BYTES ] : fieldelem_from_bytes_inp → fieldelem_from_bytes_out ;
  #val #[ FINITE ] : finite_inp → finite_out ;
  #val #[ HAS_EVEN_Y ] : has_even_y_inp → has_even_y_out ;
  #val #[ HASH_CHALLENGE ] : hash_challenge_inp → hash_challenge_out ;
  #val #[ LIFT_X ] : lift_x_inp → lift_x_out ;
  #val #[ POINT_ADD ] : point_add_inp → point_add_out ;
  #val #[ POINT_MUL ] : point_mul_inp → point_mul_out ;
  #val #[ POINT_MUL_BASE ] : point_mul_base_inp → point_mul_base_out ;
  #val #[ SCALAR_FROM_BYTES ] : scalar_from_bytes_inp → scalar_from_bytes_out ;
  #val #[ SCALAR_FROM_BYTES_STRICT ] : scalar_from_bytes_strict_inp → scalar_from_bytes_strict_out ;
  #val #[ X ] : x_inp → x_out ] [(VERIFY,(verify_inp,verify_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(
      msg_3113 , pubkey_3107 , sig_3110) := temp_inp : message_t '× public_key_t '× signature_t in
    
    let bytes_from_point := fun x_0 => package_both bytes_from_point (x_0) in
    let fieldelem_from_bytes := fun x_0 => package_both fieldelem_from_bytes (
      x_0) in
    let finite := fun x_0 => package_both finite (x_0) in
    let has_even_y := fun x_0 => package_both has_even_y (x_0) in
    let hash_challenge := fun x_0 x_1 x_2 => package_both hash_challenge (
      x_0,x_1,x_2) in
    let lift_x := fun x_0 => package_both lift_x (x_0) in
    let point_add := fun x_0 x_1 => package_both point_add (x_0,x_1) in
    let point_mul := fun x_0 x_1 => package_both point_mul (x_0,x_1) in
    let point_mul_base := fun x_0 => package_both point_mul_base (x_0) in
    let scalar_from_bytes := fun x_0 => package_both scalar_from_bytes (x_0) in
    let scalar_from_bytes_strict := fun x_0 => package_both scalar_from_bytes_strict (
      x_0) in
    let x := fun x_0 => package_both x (x_0) in
    ((letbnd(_) p_x_3108 : field_element_t :=
          option_ok_or (fieldelem_from_bytes (lift_to_both0 pubkey_3107)) (
            InvalidPublicKey) in
        letbnd(_) p_3109 : affine_point_t := lift_x (lift_to_both0 p_x_3108) in
        letbnd(_) r_3111 : field_element_t :=
          option_ok_or (fieldelem_from_bytes (array_from_slice (
                default : uint8) (32) (array_to_seq (lift_to_both0 sig_3110)) (
                lift_to_both0 (usize 0)) (lift_to_both0 (usize 32)))) (
            InvalidSignature) in
        letbnd(_) s_3112 : scalar_t :=
          option_ok_or (scalar_from_bytes_strict (array_from_slice (
                default : uint8) (32) (array_to_seq (lift_to_both0 sig_3110)) (
                lift_to_both0 (usize 32)) (lift_to_both0 (usize 32)))) (
            InvalidSignature) in
        letb e_3114 : scalar_t :=
          scalar_from_bytes (hash_challenge (array_from_slice (
                default : uint8) (32) (array_to_seq (lift_to_both0 sig_3110)) (
                lift_to_both0 (usize 0)) (lift_to_both0 (usize 32))) (
              bytes_from_point (lift_to_both0 p_3109)) (
              lift_to_both0 msg_3113)) in
        letbnd(_) r_p_3115 : (field_element_t '× field_element_t) :=
          option_ok_or (finite (point_add (point_mul_base (
                  lift_to_both0 s_3112)) (point_mul ((nat_mod_zero ) -% (
                    lift_to_both0 e_3114)) (Affine (lift_to_both0 p_3109))))) (
            InvalidSignature) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          if is_pure (I := [interface]) ((negb (has_even_y (
                  lift_to_both0 r_p_3115))) || ((x (
                  lift_to_both0 r_p_3115)) !=.? (lift_to_both0 r_3111)))
          then @Err unit_ChoiceEquality error_t (InvalidSignature)
          else @Ok unit_ChoiceEquality error_t (tt))
        ) : both (CEfset ([])) [interface
      #val #[ BYTES_FROM_POINT ] : bytes_from_point_inp → bytes_from_point_out ;
      #val #[ FIELDELEM_FROM_BYTES ] : fieldelem_from_bytes_inp → fieldelem_from_bytes_out ;
      #val #[ FINITE ] : finite_inp → finite_out ;
      #val #[ HAS_EVEN_Y ] : has_even_y_inp → has_even_y_out ;
      #val #[ HASH_CHALLENGE ] : hash_challenge_inp → hash_challenge_out ;
      #val #[ LIFT_X ] : lift_x_inp → lift_x_out ;
      #val #[ POINT_ADD ] : point_add_inp → point_add_out ;
      #val #[ POINT_MUL ] : point_mul_inp → point_mul_out ;
      #val #[ POINT_MUL_BASE ] : point_mul_base_inp → point_mul_base_out ;
      #val #[ SCALAR_FROM_BYTES ] : scalar_from_bytes_inp → scalar_from_bytes_out ;
      #val #[ SCALAR_FROM_BYTES_STRICT ] : scalar_from_bytes_strict_inp → scalar_from_bytes_strict_out ;
      #val #[ X ] : x_inp → x_out ] (verification_result_t)))in
  both_package' _ _ (VERIFY,(verify_inp,verify_out)) temp_package_both.
Fail Next Obligation.

