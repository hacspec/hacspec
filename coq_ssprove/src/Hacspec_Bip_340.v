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

Require Import Hacspec_Sha256.

Definition error_t : ChoiceEquality :=
  (
    unit_ChoiceEquality '+ unit_ChoiceEquality '+ unit_ChoiceEquality '+ unit_ChoiceEquality '+ unit_ChoiceEquality).
Definition InvalidSecretKey : error_t :=
  (inl (inl (inl (inl tt)))).
Definition InvalidNonceGenerated : error_t :=
  (inl (inl (inl (inr tt)))).
Definition InvalidPublicKey : error_t :=
  (inl (inl (inr tt))).
Definition InvalidXCoordinate : error_t :=
  (inl (inr tt)).
Definition InvalidSignature : error_t :=
  (inr tt).

(* Definition eqb_error_t (x y : error_t) : bool_ChoiceEquality := *)
(*   (match x with *)
(*        | InvalidSecretKey => *)
(*            match y with *)
(*            | InvalidSecretKey=> true *)
(*            (* | _ => false *) *)
(*            end *)
(*        (* | InvalidNonceGenerated => *) *)
(*        (*     match y with *) *)
(*        (*     | InvalidNonceGenerated=> true *) *)
(*        (*     | _ => false *) *)
(*        (*     end *) *)
(*        | InvalidPublicKey => *)
(*            match y with *)
(*            | InvalidPublicKey=> true *)
(*            | _ => false *)
(*            end *)
(*        | InvalidXCoordinate => *)
(*            match y with *)
(*            | InvalidXCoordinate=> true *)
(*            | _ => false *)
(*            end *)
(*        | InvalidSignature => *)
(*            match y with *)
(*            | InvalidSignature=> true *)
(*            | _ => false *)
(*            end *)
(*        end). *)

(* Definition eqb_leibniz_error_t (x y : error_t) : eqb_error_t x y = true <-> x = y. *)
(* Proof. split. intros; destruct x ; destruct y ; try (f_equal ; apply eqb_leibniz) ; easy. intros ; subst ; destruct y ; try reflexivity ; try (apply eqb_refl). Qed. *)

(* Instance eq_dec_error_t : EqDec (error_t) := *)
(* Build_EqDec (error_t) (eqb_error_t) (eqb_leibniz_error_t). *)


Definition field_canvas_t  :=
  (nseq (int8) (32)).
Definition field_element_t  :=
  (nat_mod 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F).

Definition scalar_canvas_t  :=
  (nseq (int8) (32)).
Definition scalar_t  :=
  (nat_mod 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141).

Definition big_integer_t  :=
  (nat_mod_pow2 (WS := U16) 256).

Notation "'affine_point_t'" := ((field_element_t '× field_element_t
)) : hacspec_scope.

Definition p_bytes32_t  :=
  ( nseq (int8) (usize 32)).

Definition point_t : ChoiceEquality :=
  (affine_point_t '+ unit_ChoiceEquality).
Definition Affine (x : affine_point_t) : point_t :=
  (inl x).
Definition AtInfinity : point_t :=
  (inr tt).


Notation "'finite_inp'" := (
  point_t : choice_type) (in custom pack_type at level 2).
Notation "'finite_out'" := ((
    option affine_point_t) : choice_type) (in custom pack_type at level 2).
Definition FINITE : nat :=
  (14476).
Program Definition finite
   : package (fset.fset0) [interface #val #[ SOME ] : some_inp → some_out
  ] [interface #val #[ FINITE ] : finite_inp → finite_out ] :=
  ([package #def #[ FINITE ] (temp_inp : finite_inp) : finite_out { 
    let '(p_14472) := temp_inp : point_t in
    #import {sig #[ SOME ] : some_inp → some_out } as some ;;
    let some := fun x_0 => some (x_0) in
    ({ code  temp_14475 ←
        (some (p_14473)) ;;
      @ret ((option (field_element_t '× field_element_t))) (match p_14472 with
        | Affine p_14473 => temp_14475
        | AtInfinity => @None affine_point_t
        end) } : code (fset.fset0) [interface
      #val #[ SOME ] : some_inp → some_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_finite : package _ _ _ :=
  (seq_link finite link_rest(package_some)).
Fail Next Obligation.


Notation "'x_inp'" := (
  affine_point_t : choice_type) (in custom pack_type at level 2).
Notation "'x_out'" := (
  field_element_t : choice_type) (in custom pack_type at level 2).
Definition X : nat :=
  (14481).
Program Definition x
   : package (fset.fset0) [interface] [interface #val #[ X ] : x_inp → x_out
  ] :=
  ([package #def #[ X ] (temp_inp : x_inp) : x_out { 
    let '(p_14477) := temp_inp : affine_point_t in
    ({ code  temp_14480 ←
        (ret (p_14477)) ;;
      let '(x_14478, _) :=
        (temp_14480) : (field_element_t '× field_element_t) in
      @ret (field_element_t) (x_14478) } : code (fset.fset0) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_x : package _ _ _ :=
  (x).
Fail Next Obligation.


Notation "'y_inp'" := (
  affine_point_t : choice_type) (in custom pack_type at level 2).
Notation "'y_out'" := (
  field_element_t : choice_type) (in custom pack_type at level 2).
Definition Y : nat :=
  (14486).
Program Definition y
   : package (fset.fset0) [interface] [interface #val #[ Y ] : y_inp → y_out
  ] :=
  ([package #def #[ Y ] (temp_inp : y_inp) : y_out { 
    let '(p_14482) := temp_inp : affine_point_t in
    ({ code  temp_14485 ←
        (ret (p_14482)) ;;
      let '(_, y_14483) :=
        (temp_14485) : (field_element_t '× field_element_t) in
      @ret (field_element_t) (y_14483) } : code (fset.fset0) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_y : package _ _ _ :=
  (y).
Fail Next Obligation.


Notation "'has_even_y_inp'" := (
  affine_point_t : choice_type) (in custom pack_type at level 2).
Notation "'has_even_y_out'" := (
  bool_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Definition HAS_EVEN_Y : nat :=
  (14498).
Program Definition has_even_y
   : package (fset.fset0) [interface #val #[ Y ] : y_inp → y_out ] [interface
  #val #[ HAS_EVEN_Y ] : has_even_y_inp → has_even_y_out ] :=
  ([package #def #[ HAS_EVEN_Y ] (temp_inp : has_even_y_inp) : has_even_y_out { 
    let '(p_14487) := temp_inp : affine_point_t in
    #import {sig #[ Y ] : y_inp → y_out } as y ;;
    let y := fun x_0 => y (x_0) in
    ({ code  '(temp_14489 : field_element_t) ←
        (y (p_14487)) ;;
       '(temp_14491 : field_element_t) ←
        (nat_mod_two ) ;;
       '(temp_14493 : field_element_t) ←
        ((temp_14489) rem (temp_14491)) ;;
       '(temp_14495 : field_element_t) ←
        (nat_mod_zero ) ;;
       '(temp_14497 : bool_ChoiceEquality) ←
        ((temp_14493) =.? (temp_14495)) ;;
      @ret (bool_ChoiceEquality) (temp_14497) } : code (fset.fset0) [interface
      #val #[ Y ] : y_inp → y_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_has_even_y : package _ _ _ :=
  (seq_link has_even_y link_rest(package_y)).
Fail Next Obligation.


Notation "'sqrt_inp'" := (
  field_element_t : choice_type) (in custom pack_type at level 2).
Notation "'sqrt_out'" := ((
    option field_element_t) : choice_type) (in custom pack_type at level 2).
Definition SQRT : nat :=
  (14516).
Program Definition sqrt
   : package (fset.fset0) [interface #val #[ SOME ] : some_inp → some_out
  ] [interface #val #[ SQRT ] : sqrt_inp → sqrt_out ] :=
  ([package #def #[ SQRT ] (temp_inp : sqrt_inp) : sqrt_out { 
    let '(y_14503) := temp_inp : field_element_t in
    #import {sig #[ SOME ] : some_inp → some_out } as some ;;
    let some := fun x_0 => some (x_0) in
    ({ code  '(p1_4_14504 : field_element_t) ←
        ( '(temp_14500 : nseq int8 32) ←
            (array_from_list int8 [
                @repr U8 63;
                @repr U8 255;
                @repr U8 255;
                @repr U8 255;
                @repr U8 255;
                @repr U8 255;
                @repr U8 255;
                @repr U8 255;
                @repr U8 255;
                @repr U8 255;
                @repr U8 255;
                @repr U8 255;
                @repr U8 255;
                @repr U8 255;
                @repr U8 255;
                @repr U8 255;
                @repr U8 255;
                @repr U8 255;
                @repr U8 255;
                @repr U8 255;
                @repr U8 255;
                @repr U8 255;
                @repr U8 255;
                @repr U8 255;
                @repr U8 255;
                @repr U8 255;
                @repr U8 255;
                @repr U8 255;
                @repr U8 191;
                @repr U8 255;
                @repr U8 255;
                @repr U8 12
              ]) ;;
           temp_14502 ←
            (nat_mod_from_public_byte_seq_be (temp_14500)) ;;
          ret (temp_14502)) ;;
       '(x_14507 : field_element_t) ←
        ( temp_14506 ←
            (nat_mod_pow_self (y_14503) (p1_4_14504)) ;;
          ret (temp_14506)) ;;
       '(temp_14509 : field_element_t) ←
        (nat_mod_two ) ;;
       temp_14511 ←
        (nat_mod_pow_self (x_14507) (temp_14509)) ;;
       '(temp_14513 : bool_ChoiceEquality) ←
        ((temp_14511) =.? (y_14503)) ;;
       temp_14515 ←
        (some (x_14507)) ;;
      @ret ((option field_element_t)) ((if (
            temp_14513):bool_ChoiceEquality then (*inline*) (temp_14515) else (
            @None field_element_t))) } : code (fset.fset0) [interface
      #val #[ SOME ] : some_inp → some_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_sqrt : package _ _ _ :=
  (seq_link sqrt link_rest(package_some)).
Fail Next Obligation.

Definition y_14537_loc : ChoiceEqualityLocation :=
  ((field_element_t ; 14548%nat)).
Notation "'lift_x_inp'" := (
  field_element_t : choice_type) (in custom pack_type at level 2).
Notation "'lift_x_out'" := ((
    result error_t affine_point_t) : choice_type) (in custom pack_type at level 2).
Definition LIFT_X : nat :=
  (14549).
Program Definition lift_x
   : package (CEfset ([y_14537_loc])) [interface
  #val #[ SQRT ] : sqrt_inp → sqrt_out ] [interface
  #val #[ LIFT_X ] : lift_x_inp → lift_x_out ] :=
  ([package #def #[ LIFT_X ] (temp_inp : lift_x_inp) : lift_x_out { 
    let '(x_14525) := temp_inp : field_element_t in
    #import {sig #[ SQRT ] : sqrt_inp → sqrt_out } as sqrt ;;
    let sqrt := fun x_0 => sqrt (x_0) in
    ({ code  '(one_14541 : field_element_t) ←
        ( '(temp_14518 : field_element_t) ←
            (nat_mod_one ) ;;
          ret (temp_14518)) ;;
       '(two_14538 : field_element_t) ←
        ( '(temp_14520 : field_element_t) ←
            (nat_mod_two ) ;;
          ret (temp_14520)) ;;
       '(three_14526 : field_element_t) ←
        ( '(temp_14522 : field_element_t) ←
            (nat_mod_from_literal (
                0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F) (
                @repr U128 3)) ;;
          ret (temp_14522)) ;;
       '(seven_14529 : field_element_t) ←
        ( '(temp_14524 : field_element_t) ←
            (nat_mod_from_literal (
                0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F) (
                @repr U128 7)) ;;
          ret (temp_14524)) ;;
       '(y_sq_14532 : field_element_t) ←
        ( temp_14528 ←
            (nat_mod_pow_self (x_14525) (three_14526)) ;;
           '(temp_14531 : field_element_t) ←
            ((temp_14528) +% (seven_14529)) ;;
          ret (temp_14531)) ;;
      bndm(
        ChoiceEqualityMonad.result_bind_code error_t , field_element_t , _ , CEfset (
          [y_14537_loc])) y_14537 ⇠
      (({ code  '(temp_14534 : (option field_element_t)) ←
            (sqrt (y_sq_14532)) ;;
           temp_14536 ←
            (option_ok_or (temp_14534) (InvalidXCoordinate)) ;;
          @ret _ (temp_14536) } : code (CEfset ([y_14537_loc])) [interface
          #val #[ SQRT ] : sqrt_inp → sqrt_out ] _)) in
      ({ code  '(temp_14540 : field_element_t) ←
          ((y_14537) rem (two_14538)) ;;
         '(temp_14543 : bool_ChoiceEquality) ←
          ((temp_14540) =.? (one_14541)) ;;
         '(y_14537 : (field_element_t)) ←
          (if temp_14543:bool_ChoiceEquality
            then (*not state*) (let temp_then :=  '(
                    y_14537 : field_element_t) ←
                  (( '(temp_14545 : field_element_t) ←
                        (nat_mod_zero ) ;;
                       '(temp_14547 : field_element_t) ←
                        ((temp_14545) -% (y_14537)) ;;
                      ret (temp_14547))) ;;
                #put y_14537_loc := y_14537 ;;
              
              @ret ((field_element_t)) (y_14537) in
              ({ code temp_then } : code (CEfset (
                    [y_14537_loc])) [interface] _))
            else @ret ((field_element_t)) (y_14537)) ;;
        
        @ret ((result error_t affine_point_t)) (@inl affine_point_t error_t (
            prod_ce(x_14525, y_14537))) } : code (CEfset (
            [y_14537_loc])) [interface #val #[ SQRT ] : sqrt_inp → sqrt_out
        ] _) } : code (CEfset ([y_14537_loc])) [interface
      #val #[ SQRT ] : sqrt_inp → sqrt_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_lift_x : package _ _ _ :=
  (seq_link lift_x link_rest(package_sqrt)).
Fail Next Obligation.


Notation "'compute_lam_inp'" := (
  affine_point_t '× affine_point_t : choice_type) (in custom pack_type at level 2).
Notation "'compute_lam_out'" := (
  field_element_t : choice_type) (in custom pack_type at level 2).
Definition COMPUTE_LAM : nat :=
  (14603).
Program Definition compute_lam
   : package (fset.fset0) [interface #val #[ X ] : x_inp → x_out ;
  #val #[ Y ] : y_inp → y_out ] [interface
  #val #[ COMPUTE_LAM ] : compute_lam_inp → compute_lam_out ] :=
  (
    [package #def #[ COMPUTE_LAM ] (temp_inp : compute_lam_inp) : compute_lam_out { 
    let '(
      p1_14552 , p2_14553) := temp_inp : affine_point_t '× affine_point_t in
    #import {sig #[ X ] : x_inp → x_out } as x ;;
    let x := fun x_0 => x (x_0) in
    #import {sig #[ Y ] : y_inp → y_out } as y ;;
    let y := fun x_0 => y (x_0) in
    ({ code  '(three_14578 : field_element_t) ←
        ( '(temp_14551 : field_element_t) ←
            (nat_mod_from_literal (
                0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F) (
                @repr U128 3)) ;;
          ret (temp_14551)) ;;
       '(temp_14555 : bool_ChoiceEquality) ←
        ((p1_14552) !=.? (p2_14553)) ;;
       '(temp_14557 : field_element_t) ←
        (y (p2_14553)) ;;
       '(temp_14559 : field_element_t) ←
        (y (p1_14552)) ;;
       '(temp_14561 : field_element_t) ←
        ((temp_14557) -% (temp_14559)) ;;
       '(temp_14563 : field_element_t) ←
        (x (p2_14553)) ;;
       '(temp_14565 : field_element_t) ←
        (x (p1_14552)) ;;
       '(temp_14567 : field_element_t) ←
        ((temp_14563) -% (temp_14565)) ;;
       '(temp_14569 : field_element_t) ←
        (nat_mod_zero ) ;;
       '(temp_14571 : field_element_t) ←
        (nat_mod_two ) ;;
       '(temp_14573 : field_element_t) ←
        ((temp_14569) -% (temp_14571)) ;;
       temp_14575 ←
        (nat_mod_pow_self (temp_14567) (temp_14573)) ;;
       '(temp_14577 : field_element_t) ←
        ((temp_14561) *% (temp_14575)) ;;
       '(temp_14580 : field_element_t) ←
        (x (p1_14552)) ;;
       '(temp_14582 : field_element_t) ←
        ((three_14578) *% (temp_14580)) ;;
       '(temp_14584 : field_element_t) ←
        (x (p1_14552)) ;;
       '(temp_14586 : field_element_t) ←
        ((temp_14582) *% (temp_14584)) ;;
       '(temp_14588 : field_element_t) ←
        (nat_mod_two ) ;;
       '(temp_14590 : field_element_t) ←
        (y (p1_14552)) ;;
       '(temp_14592 : field_element_t) ←
        ((temp_14588) *% (temp_14590)) ;;
       '(temp_14594 : field_element_t) ←
        (nat_mod_zero ) ;;
       '(temp_14596 : field_element_t) ←
        (nat_mod_two ) ;;
       '(temp_14598 : field_element_t) ←
        ((temp_14594) -% (temp_14596)) ;;
       temp_14600 ←
        (nat_mod_pow_self (temp_14592) (temp_14598)) ;;
       '(temp_14602 : field_element_t) ←
        ((temp_14586) *% (temp_14600)) ;;
      @ret (field_element_t) ((if (
            temp_14555):bool_ChoiceEquality then (*inline*) (temp_14577) else (
            temp_14602))) } : code (fset.fset0) [interface
      #val #[ X ] : x_inp → x_out ; #val #[ Y ] : y_inp → y_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_compute_lam : package _ _ _ :=
  (seq_link compute_lam link_rest(package_x,package_y)).
Fail Next Obligation.

Definition result_14610_loc : ChoiceEqualityLocation :=
  ((point_t ; 14663%nat)).
Notation "'point_add_inp'" := (
  point_t '× point_t : choice_type) (in custom pack_type at level 2).
Notation "'point_add_out'" := (
  point_t : choice_type) (in custom pack_type at level 2).
Definition POINT_ADD : nat :=
  (14664).
Program Definition point_add
   : package (CEfset ([result_14610_loc])) [interface
  #val #[ COMPUTE_LAM ] : compute_lam_inp → compute_lam_out ;
  #val #[ FINITE ] : finite_inp → finite_out ; #val #[ X ] : x_inp → x_out ;
  #val #[ Y ] : y_inp → y_out ] [interface
  #val #[ POINT_ADD ] : point_add_inp → point_add_out ] :=
  ([package #def #[ POINT_ADD ] (temp_inp : point_add_inp) : point_add_out { 
    let '(p1_14604 , p2_14609) := temp_inp : point_t '× point_t in
    #import {sig #[ COMPUTE_LAM ] : compute_lam_inp → compute_lam_out } as compute_lam ;;
    let compute_lam := fun x_0 x_1 => compute_lam (x_0,x_1) in
    #import {sig #[ FINITE ] : finite_inp → finite_out } as finite ;;
    let finite := fun x_0 => finite (x_0) in
    #import {sig #[ X ] : x_inp → x_out } as x ;;
    let x := fun x_0 => x (x_0) in
    #import {sig #[ Y ] : y_inp → y_out } as y ;;
    let y := fun x_0 => y (x_0) in
    ({ code  '(result_14610 : point_t) ←
          (ret (AtInfinity)) ;;
        #put result_14610_loc := result_14610 ;;
       '(temp_14606 : (option affine_point_t)) ←
        (finite (p1_14604)) ;;
       temp_14608 ←
        (option_is_none (temp_14606)) ;;
       '(result_14610 : (point_t)) ←
        (if temp_14608:bool_ChoiceEquality
          then (*not state*) (let temp_then :=  '(result_14610 : point_t) ←
                ((ret (p2_14609))) ;;
              #put result_14610_loc := result_14610 ;;
            
            @ret ((point_t)) (result_14610) in
            ({ code temp_then } : code (CEfset (
                  [result_14610_loc])) [interface] _))
          else  (({ code  '(temp_14612 : (option affine_point_t)) ←
                (finite (p2_14609)) ;;
               temp_14614 ←
                (option_is_none (temp_14612)) ;;
               '(result_14610 : (point_t)) ←
                (if temp_14614:bool_ChoiceEquality
                  then (*not state*) (let temp_then :=  '(
                          result_14610 : point_t) ←
                        ((ret (p1_14604))) ;;
                      #put result_14610_loc := result_14610 ;;
                    
                    @ret ((point_t)) (result_14610) in
                    ({ code temp_then } : code (CEfset (
                          [result_14610_loc])) [interface] _))
                  else  (({ code  '(p1_14623 : (
                            field_element_t '×
                            field_element_t
                          )) ←
                        ( '(temp_14616 : (option affine_point_t)) ←
                            (finite (p1_14604)) ;;
                           temp_14618 ←
                            (option_unwrap (temp_14616)) ;;
                          ret (temp_14618)) ;;
                       '(p2_14626 : (field_element_t '× field_element_t)) ←
                        ( '(temp_14620 : (option affine_point_t)) ←
                            (finite (p2_14609)) ;;
                           temp_14622 ←
                            (option_unwrap (temp_14620)) ;;
                          ret (temp_14622)) ;;
                       '(temp_14625 : field_element_t) ←
                        (x (p1_14623)) ;;
                       '(temp_14628 : field_element_t) ←
                        (x (p2_14626)) ;;
                       '(temp_14630 : bool_ChoiceEquality) ←
                        ((temp_14625) =.? (temp_14628)) ;;
                       '(temp_14632 : field_element_t) ←
                        (y (p1_14623)) ;;
                       '(temp_14634 : field_element_t) ←
                        (y (p2_14626)) ;;
                       '(temp_14636 : bool_ChoiceEquality) ←
                        ((temp_14632) !=.? (temp_14634)) ;;
                       '(temp_14638 : bool_ChoiceEquality) ←
                        ((temp_14630) && (temp_14636)) ;;
                       '(result_14610 : (point_t)) ←
                        (if negb (temp_14638):bool_ChoiceEquality
                          then (*not state*) (let temp_then :=  '(
                                lam_14641 : field_element_t) ←
                              ( '(temp_14640 : field_element_t) ←
                                  (compute_lam (p1_14623) (p2_14626)) ;;
                                ret (temp_14640)) ;;
                             '(x3_14652 : field_element_t) ←
                              ( '(temp_14643 : field_element_t) ←
                                  ((lam_14641) *% (lam_14641)) ;;
                                 '(temp_14645 : field_element_t) ←
                                  (x (p1_14623)) ;;
                                 '(temp_14647 : field_element_t) ←
                                  ((temp_14643) -% (temp_14645)) ;;
                                 '(temp_14649 : field_element_t) ←
                                  (x (p2_14626)) ;;
                                 '(temp_14651 : field_element_t) ←
                                  ((temp_14647) -% (temp_14649)) ;;
                                ret (temp_14651)) ;;
                             '(result_14610 : point_t) ←
                                (( '(temp_14654 : field_element_t) ←
                                      (x (p1_14623)) ;;
                                     '(temp_14656 : field_element_t) ←
                                      ((temp_14654) -% (x3_14652)) ;;
                                     '(temp_14658 : field_element_t) ←
                                      ((lam_14641) *% (temp_14656)) ;;
                                     '(temp_14660 : field_element_t) ←
                                      (y (p1_14623)) ;;
                                     '(temp_14662 : field_element_t) ←
                                      ((temp_14658) -% (temp_14660)) ;;
                                    ret (Affine (prod_ce(x3_14652, temp_14662
                                        ))))) ;;
                              #put result_14610_loc := result_14610 ;;
                            
                            @ret ((point_t)) (result_14610) in
                            ({ code temp_then } : code (CEfset (
                                  [result_14610_loc])) [interface
                              #val #[ COMPUTE_LAM ] : compute_lam_inp → compute_lam_out ;
                              #val #[ X ] : x_inp → x_out ;
                              #val #[ Y ] : y_inp → y_out ] _))
                          else @ret ((point_t)) (result_14610)) ;;
                      
                      @ret ((point_t)) (result_14610) } : code (CEfset (
                          [result_14610_loc])) [interface
                      #val #[ COMPUTE_LAM ] : compute_lam_inp → compute_lam_out ;
                      #val #[ FINITE ] : finite_inp → finite_out ;
                      #val #[ X ] : x_inp → x_out ;
                      #val #[ Y ] : y_inp → y_out ] _))) ;;
              
              @ret ((point_t)) (result_14610) } : code (CEfset (
                  [result_14610_loc])) [interface
              #val #[ COMPUTE_LAM ] : compute_lam_inp → compute_lam_out ;
              #val #[ FINITE ] : finite_inp → finite_out ;
              #val #[ X ] : x_inp → x_out ; #val #[ Y ] : y_inp → y_out
              ] _))) ;;
      
      @ret (point_t) (result_14610) } : code (CEfset (
          [result_14610_loc])) [interface
      #val #[ COMPUTE_LAM ] : compute_lam_inp → compute_lam_out ;
      #val #[ FINITE ] : finite_inp → finite_out ;
      #val #[ X ] : x_inp → x_out ; #val #[ Y ] : y_inp → y_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_point_add : package _ _ _ :=
  (seq_link point_add link_rest(
      package_compute_lam,package_finite,package_x,package_y)).
Fail Next Obligation.

Definition q_14670_loc : ChoiceEqualityLocation :=
  ((point_t ; 14678%nat)).
Definition p_14671_loc : ChoiceEqualityLocation :=
  ((point_t ; 14679%nat)).
Notation "'point_mul_inp'" := (
  scalar_t '× point_t : choice_type) (in custom pack_type at level 2).
Notation "'point_mul_out'" := (
  point_t : choice_type) (in custom pack_type at level 2).
Definition POINT_MUL : nat :=
  (14680).
Program Definition point_mul
   : package (CEfset ([p_14671_loc ; q_14670_loc])) [interface
  #val #[ POINT_ADD ] : point_add_inp → point_add_out ] [interface
  #val #[ POINT_MUL ] : point_mul_inp → point_mul_out ] :=
  ([package #def #[ POINT_MUL ] (temp_inp : point_mul_inp) : point_mul_out { 
    let '(s_14666 , p_14665) := temp_inp : scalar_t '× point_t in
    #import {sig #[ POINT_ADD ] : point_add_inp → point_add_out } as point_add ;;
    let point_add := fun x_0 x_1 => point_add (x_0,x_1) in
    ({ code  '(p_14671 : point_t) ←
          (ret (p_14665)) ;;
        #put p_14671_loc := p_14671 ;;
       '(q_14670 : point_t) ←
          (ret (AtInfinity)) ;;
        #put q_14670_loc := q_14670 ;;
       temp_14677 ←
        (foldi' (usize 0) (usize 256) prod_ce(p_14671, q_14670) (L2 := CEfset (
                [p_14671_loc ; q_14670_loc])) (I2 := [interface
              #val #[ POINT_ADD ] : point_add_inp → point_add_out
              ]) (H_loc_incl := _) (H_opsig_incl := _) (fun i_14667 '(
              p_14671,
              q_14670
            ) =>
            ({ code  temp_14669 ←
                (nat_mod_bit (s_14666) (i_14667)) ;;
               '(q_14670 : (point_t)) ←
                (if temp_14669:bool_ChoiceEquality
                  then (*not state*) (let temp_then :=  '(q_14670 : point_t) ←
                        (( '(temp_14673 : point_t) ←
                              (point_add (q_14670) (p_14671)) ;;
                            ret (temp_14673))) ;;
                      #put q_14670_loc := q_14670 ;;
                    
                    @ret ((point_t)) (q_14670) in
                    ({ code temp_then } : code (CEfset (
                          [p_14671_loc ; q_14670_loc])) [interface
                      #val #[ POINT_ADD ] : point_add_inp → point_add_out
                      ] _))
                  else @ret ((point_t)) (q_14670)) ;;
              
               '(p_14671 : point_t) ←
                  (( '(temp_14675 : point_t) ←
                        (point_add (p_14671) (p_14671)) ;;
                      ret (temp_14675))) ;;
                #put p_14671_loc := p_14671 ;;
              
              @ret ((point_t '× point_t)) (prod_ce(p_14671, q_14670
                )) } : code (CEfset ([p_14671_loc ; q_14670_loc])) [interface
              #val #[ POINT_ADD ] : point_add_inp → point_add_out ] _))) ;;
      let '(p_14671, q_14670) :=
        (temp_14677) : (point_t '× point_t) in
      
      @ret (point_t) (q_14670) } : code (CEfset (
          [p_14671_loc ; q_14670_loc])) [interface
      #val #[ POINT_ADD ] : point_add_inp → point_add_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_point_mul : package _ _ _ :=
  (seq_link point_mul link_rest(package_point_add)).
Fail Next Obligation.


Notation "'point_mul_base_inp'" := (
  scalar_t : choice_type) (in custom pack_type at level 2).
Notation "'point_mul_base_out'" := (
  point_t : choice_type) (in custom pack_type at level 2).
Definition POINT_MUL_BASE : nat :=
  (14695).
Program Definition point_mul_base
   : package (CEfset ([])) [interface
  #val #[ POINT_MUL ] : point_mul_inp → point_mul_out ] [interface
  #val #[ POINT_MUL_BASE ] : point_mul_base_inp → point_mul_base_out ] :=
  (
    [package #def #[ POINT_MUL_BASE ] (temp_inp : point_mul_base_inp) : point_mul_base_out { 
    let '(s_14691) := temp_inp : scalar_t in
    #import {sig #[ POINT_MUL ] : point_mul_inp → point_mul_out } as point_mul ;;
    let point_mul := fun x_0 x_1 => point_mul (x_0,x_1) in
    ({ code  '(gx_14685 : p_bytes32_t) ←
        ( '(temp_14682 : nseq int8 32) ←
            (array_from_list int8 [
                @repr U8 121;
                @repr U8 190;
                @repr U8 102;
                @repr U8 126;
                @repr U8 249;
                @repr U8 220;
                @repr U8 187;
                @repr U8 172;
                @repr U8 85;
                @repr U8 160;
                @repr U8 98;
                @repr U8 149;
                @repr U8 206;
                @repr U8 135;
                @repr U8 11;
                @repr U8 7;
                @repr U8 2;
                @repr U8 155;
                @repr U8 252;
                @repr U8 219;
                @repr U8 45;
                @repr U8 206;
                @repr U8 40;
                @repr U8 217;
                @repr U8 89;
                @repr U8 242;
                @repr U8 129;
                @repr U8 91;
                @repr U8 22;
                @repr U8 248;
                @repr U8 23;
                @repr U8 152
              ]) ;;
          ret (temp_14682)) ;;
       '(gy_14688 : p_bytes32_t) ←
        ( '(temp_14684 : nseq int8 32) ←
            (array_from_list int8 [
                @repr U8 72;
                @repr U8 58;
                @repr U8 218;
                @repr U8 119;
                @repr U8 38;
                @repr U8 163;
                @repr U8 196;
                @repr U8 101;
                @repr U8 93;
                @repr U8 164;
                @repr U8 251;
                @repr U8 252;
                @repr U8 14;
                @repr U8 17;
                @repr U8 8;
                @repr U8 168;
                @repr U8 253;
                @repr U8 23;
                @repr U8 180;
                @repr U8 72;
                @repr U8 166;
                @repr U8 133;
                @repr U8 84;
                @repr U8 25;
                @repr U8 156;
                @repr U8 71;
                @repr U8 208;
                @repr U8 143;
                @repr U8 251;
                @repr U8 16;
                @repr U8 212;
                @repr U8 184
              ]) ;;
          ret (temp_14684)) ;;
       '(g_14692 : point_t) ←
        ( temp_14687 ←
            (nat_mod_from_public_byte_seq_be (gx_14685)) ;;
           temp_14690 ←
            (nat_mod_from_public_byte_seq_be (gy_14688)) ;;
          ret (Affine (prod_ce(temp_14687, temp_14690)))) ;;
       '(temp_14694 : point_t) ←
        (point_mul (s_14691) (g_14692)) ;;
      @ret (point_t) (temp_14694) } : code (CEfset ([])) [interface
      #val #[ POINT_MUL ] : point_mul_inp → point_mul_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_point_mul_base : package _ _ _ :=
  (seq_link point_mul_base link_rest(package_point_mul)).
Fail Next Obligation.

Definition bytes32_t  :=
  ( nseq (uint8) (usize 32)).

Notation "'secret_key_t'" := (bytes32_t) : hacspec_scope.

Notation "'public_key_t'" := (bytes32_t) : hacspec_scope.

Notation "'message_t'" := (bytes32_t) : hacspec_scope.

Notation "'aux_rand_t'" := (bytes32_t) : hacspec_scope.

Definition signature_t  :=
  ( nseq (uint8) (usize 64)).


Notation "'tagged_hash_inp'" := (
  public_byte_seq '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'tagged_hash_out'" := (
  bytes32_t : choice_type) (in custom pack_type at level 2).
Definition TAGGED_HASH : nat :=
  (14716).
Program Definition tagged_hash
   : package (fset.fset0) [interface
  #val #[ SHA256 ] : sha256_inp → sha256_out ] [interface
  #val #[ TAGGED_HASH ] : tagged_hash_inp → tagged_hash_out ] :=
  (
    [package #def #[ TAGGED_HASH ] (temp_inp : tagged_hash_inp) : tagged_hash_out { 
    let '(tag_14696 , msg_14706) := temp_inp : public_byte_seq '× byte_seq in
    #import {sig #[ SHA256 ] : sha256_inp → sha256_out } as sha256 ;;
    let sha256 := fun x_0 => sha256 (x_0) in
    ({ code  '(tag_hash_14703 : seq uint8) ←
        ( '(temp_14698 : byte_seq) ←
            (seq_from_public_seq (tag_14696)) ;;
           temp_14700 ←
            (sha256 (temp_14698)) ;;
           '(temp_14702 : seq int8) ←
            (array_to_be_bytes (temp_14700)) ;;
          ret (temp_14702)) ;;
       '(hash_14711 : sha256_digest_t) ←
        ( '(temp_14705 : seq uint8) ←
            (seq_concat (tag_hash_14703) (tag_hash_14703)) ;;
           '(temp_14708 : seq uint8) ←
            (seq_concat (temp_14705) (msg_14706)) ;;
           temp_14710 ←
            (sha256 (temp_14708)) ;;
          ret (temp_14710)) ;;
       '(temp_14713 : seq uint8) ←
        (array_to_seq (hash_14711)) ;;
       '(temp_14715 : bytes32_t) ←
        (array_from_seq (32) (temp_14713)) ;;
      @ret (bytes32_t) (temp_14715) } : code (fset.fset0) [interface
      #val #[ SHA256 ] : sha256_inp → sha256_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_tagged_hash : package _ _ _ :=
  (seq_link tagged_hash link_rest(package_sha256)).
Fail Next Obligation.

Definition tagged_hash_aux_prefix_t  :=
  ( nseq (int8) (usize 11)).

Definition bip0340_aux_v : (tagged_hash_aux_prefix_t) :=
  (let temp_14718 : nseq int8 11 :=
      (array_from_list int8 [
          @repr U8 66;
          @repr U8 73;
          @repr U8 80;
          @repr U8 48;
          @repr U8 51;
          @repr U8 52;
          @repr U8 48;
          @repr U8 47;
          @repr U8 97;
          @repr U8 117;
          @repr U8 120
        ]) in
    (temp_14718)).


Notation "'hash_aux_inp'" := (
  aux_rand_t : choice_type) (in custom pack_type at level 2).
Notation "'hash_aux_out'" := (
  bytes32_t : choice_type) (in custom pack_type at level 2).
Definition HASH_AUX : nat :=
  (14728).
Program Definition hash_aux
   : package (fset.fset0) [interface
  #val #[ TAGGED_HASH ] : tagged_hash_inp → tagged_hash_out ] [interface
  #val #[ HASH_AUX ] : hash_aux_inp → hash_aux_out ] :=
  ([package #def #[ HASH_AUX ] (temp_inp : hash_aux_inp) : hash_aux_out { 
    let '(aux_rand_14723) := temp_inp : aux_rand_t in
    #import {sig #[ TAGGED_HASH ] : tagged_hash_inp → tagged_hash_out } as tagged_hash ;;
    let tagged_hash := fun x_0 x_1 => tagged_hash (x_0,x_1) in
    ({ code  '(temp_14720 : seq int8) ←
        (array_to_seq (bip0340_aux_v)) ;;
       '(temp_14722 : public_byte_seq) ←
        (seq_from_seq (temp_14720)) ;;
       '(temp_14725 : byte_seq) ←
        (seq_from_seq (aux_rand_14723)) ;;
       '(temp_14727 : bytes32_t) ←
        (tagged_hash (temp_14722) (temp_14725)) ;;
      @ret (bytes32_t) (temp_14727) } : code (fset.fset0) [interface
      #val #[ TAGGED_HASH ] : tagged_hash_inp → tagged_hash_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_hash_aux : package _ _ _ :=
  (seq_link hash_aux link_rest(package_tagged_hash)).
Fail Next Obligation.

Definition tagged_hash_nonce_prefix_t  :=
  ( nseq (int8) (usize 13)).

Definition bip0340_nonce_v : (tagged_hash_nonce_prefix_t) :=
  (let temp_14730 : nseq int8 13 :=
      (array_from_list int8 [
          @repr U8 66;
          @repr U8 73;
          @repr U8 80;
          @repr U8 48;
          @repr U8 51;
          @repr U8 52;
          @repr U8 48;
          @repr U8 47;
          @repr U8 110;
          @repr U8 111;
          @repr U8 110;
          @repr U8 99;
          @repr U8 101
        ]) in
    (temp_14730)).


Notation "'hash_nonce_inp'" := (
  bytes32_t '× bytes32_t '× message_t : choice_type) (in custom pack_type at level 2).
Notation "'hash_nonce_out'" := (
  bytes32_t : choice_type) (in custom pack_type at level 2).
Definition HASH_NONCE : nat :=
  (14751).
Program Definition hash_nonce
   : package (fset.fset0) [interface
  #val #[ TAGGED_HASH ] : tagged_hash_inp → tagged_hash_out ] [interface
  #val #[ HASH_NONCE ] : hash_nonce_inp → hash_nonce_out ] :=
  ([package #def #[ HASH_NONCE ] (temp_inp : hash_nonce_inp) : hash_nonce_out { 
    let '(
      rand_14731 , pubkey_14736 , msg_14741) := temp_inp : bytes32_t '× bytes32_t '× message_t in
    #import {sig #[ TAGGED_HASH ] : tagged_hash_inp → tagged_hash_out } as tagged_hash ;;
    let tagged_hash := fun x_0 x_1 => tagged_hash (x_0,x_1) in
    ({ code  '(c_14748 : byte_seq) ←
        ( '(temp_14733 : seq uint8) ←
            (array_to_seq (rand_14731)) ;;
           '(temp_14735 : byte_seq) ←
            (seq_from_seq (temp_14733)) ;;
           '(temp_14738 : seq uint8) ←
            (array_to_seq (pubkey_14736)) ;;
           '(temp_14740 : seq uint8) ←
            (seq_concat (temp_14735) (temp_14738)) ;;
           '(temp_14743 : seq uint8) ←
            (seq_concat (temp_14740) (msg_14741)) ;;
          ret (temp_14743)) ;;
       '(temp_14745 : seq int8) ←
        (array_to_seq (bip0340_nonce_v)) ;;
       '(temp_14747 : public_byte_seq) ←
        (seq_from_seq (temp_14745)) ;;
       '(temp_14750 : bytes32_t) ←
        (tagged_hash (temp_14747) (c_14748)) ;;
      @ret (bytes32_t) (temp_14750) } : code (fset.fset0) [interface
      #val #[ TAGGED_HASH ] : tagged_hash_inp → tagged_hash_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_hash_nonce : package _ _ _ :=
  (seq_link hash_nonce link_rest(package_tagged_hash)).
Fail Next Obligation.

Definition tagged_hash_challenge_prefix_t  :=
  ( nseq (int8) (usize 17)).

Definition bip0340_challenge_v : (tagged_hash_challenge_prefix_t) :=
  (let temp_14753 : nseq int8 17 :=
      (array_from_list int8 [
          @repr U8 66;
          @repr U8 73;
          @repr U8 80;
          @repr U8 48;
          @repr U8 51;
          @repr U8 52;
          @repr U8 48;
          @repr U8 47;
          @repr U8 99;
          @repr U8 104;
          @repr U8 97;
          @repr U8 108;
          @repr U8 108;
          @repr U8 101;
          @repr U8 110;
          @repr U8 103;
          @repr U8 101
        ]) in
    (temp_14753)).


Notation "'hash_challenge_inp'" := (
  bytes32_t '× bytes32_t '× bytes32_t : choice_type) (in custom pack_type at level 2).
Notation "'hash_challenge_out'" := (
  bytes32_t : choice_type) (in custom pack_type at level 2).
Definition HASH_CHALLENGE : nat :=
  (14776).
Program Definition hash_challenge
   : package (fset.fset0) [interface
  #val #[ TAGGED_HASH ] : tagged_hash_inp → tagged_hash_out ] [interface
  #val #[ HASH_CHALLENGE ] : hash_challenge_inp → hash_challenge_out ] :=
  (
    [package #def #[ HASH_CHALLENGE ] (temp_inp : hash_challenge_inp) : hash_challenge_out { 
    let '(
      rx_14754 , pubkey_14759 , msg_14764) := temp_inp : bytes32_t '× bytes32_t '× bytes32_t in
    #import {sig #[ TAGGED_HASH ] : tagged_hash_inp → tagged_hash_out } as tagged_hash ;;
    let tagged_hash := fun x_0 x_1 => tagged_hash (x_0,x_1) in
    ({ code  '(c_14773 : byte_seq) ←
        ( '(temp_14756 : seq uint8) ←
            (array_to_seq (rx_14754)) ;;
           '(temp_14758 : byte_seq) ←
            (seq_from_seq (temp_14756)) ;;
           '(temp_14761 : seq uint8) ←
            (array_to_seq (pubkey_14759)) ;;
           '(temp_14763 : seq uint8) ←
            (seq_concat (temp_14758) (temp_14761)) ;;
           '(temp_14766 : seq uint8) ←
            (array_to_seq (msg_14764)) ;;
           '(temp_14768 : seq uint8) ←
            (seq_concat (temp_14763) (temp_14766)) ;;
          ret (temp_14768)) ;;
       '(temp_14770 : seq int8) ←
        (array_to_seq (bip0340_challenge_v)) ;;
       '(temp_14772 : public_byte_seq) ←
        (seq_from_seq (temp_14770)) ;;
       '(temp_14775 : bytes32_t) ←
        (tagged_hash (temp_14772) (c_14773)) ;;
      @ret (bytes32_t) (temp_14775) } : code (fset.fset0) [interface
      #val #[ TAGGED_HASH ] : tagged_hash_inp → tagged_hash_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_hash_challenge : package _ _ _ :=
  (seq_link hash_challenge link_rest(package_tagged_hash)).
Fail Next Obligation.


Notation "'bytes_from_point_inp'" := (
  affine_point_t : choice_type) (in custom pack_type at level 2).
Notation "'bytes_from_point_out'" := (
  bytes32_t : choice_type) (in custom pack_type at level 2).
Definition BYTES_FROM_POINT : nat :=
  (14785).
Program Definition bytes_from_point
   : package (fset.fset0) [interface] [interface
  #val #[ BYTES_FROM_POINT ] : bytes_from_point_inp → bytes_from_point_out
  ] :=
  (
    [package #def #[ BYTES_FROM_POINT ] (temp_inp : bytes_from_point_inp) : bytes_from_point_out { 
    let '(p_14777) := temp_inp : affine_point_t in
    ({ code  temp_14784 ←
        (ret (p_14777)) ;;
      let '(x_14778, _) :=
        (temp_14784) : (field_element_t '× field_element_t) in
       temp_14780 ←
        (nat_mod_to_byte_seq_be (x_14778)) ;;
       '(temp_14782 : bytes32_t) ←
        (array_from_seq (32) (temp_14780)) ;;
      @ret (bytes32_t) (temp_14782) } : code (fset.fset0) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_bytes_from_point : package _ _ _ :=
  (bytes_from_point).
Fail Next Obligation.


Notation "'bytes_from_scalar_inp'" := (
  scalar_t : choice_type) (in custom pack_type at level 2).
Notation "'bytes_from_scalar_out'" := (
  bytes32_t : choice_type) (in custom pack_type at level 2).
Definition BYTES_FROM_SCALAR : nat :=
  (14791).
Program Definition bytes_from_scalar
   : package (fset.fset0) [interface] [interface
  #val #[ BYTES_FROM_SCALAR ] : bytes_from_scalar_inp → bytes_from_scalar_out
  ] :=
  (
    [package #def #[ BYTES_FROM_SCALAR ] (temp_inp : bytes_from_scalar_inp) : bytes_from_scalar_out { 
    let '(x_14786) := temp_inp : scalar_t in
    ({ code  temp_14788 ←
        (nat_mod_to_byte_seq_be (x_14786)) ;;
       '(temp_14790 : bytes32_t) ←
        (array_from_seq (32) (temp_14788)) ;;
      @ret (bytes32_t) (temp_14790) } : code (fset.fset0) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_bytes_from_scalar : package _ _ _ :=
  (bytes_from_scalar).
Fail Next Obligation.


Notation "'scalar_from_bytes_inp'" := (
  bytes32_t : choice_type) (in custom pack_type at level 2).
Notation "'scalar_from_bytes_out'" := (
  scalar_t : choice_type) (in custom pack_type at level 2).
Definition SCALAR_FROM_BYTES : nat :=
  (14797).
Program Definition scalar_from_bytes
   : package (fset.fset0) [interface] [interface
  #val #[ SCALAR_FROM_BYTES ] : scalar_from_bytes_inp → scalar_from_bytes_out
  ] :=
  (
    [package #def #[ SCALAR_FROM_BYTES ] (temp_inp : scalar_from_bytes_inp) : scalar_from_bytes_out { 
    let '(b_14792) := temp_inp : bytes32_t in
    ({ code  '(temp_14794 : seq uint8) ←
        (array_to_seq (b_14792)) ;;
       '(temp_14796 : scalar_t) ←
        (nat_mod_from_byte_seq_be (temp_14794)) ;;
      @ret (scalar_t) (temp_14796) } : code (fset.fset0) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_scalar_from_bytes : package _ _ _ :=
  (scalar_from_bytes).
Fail Next Obligation.


Notation "'scalar_from_bytes_strict_inp'" := (
  bytes32_t : choice_type) (in custom pack_type at level 2).
Notation "'scalar_from_bytes_strict_out'" := ((
    option scalar_t) : choice_type) (in custom pack_type at level 2).
Definition SCALAR_FROM_BYTES_STRICT : nat :=
  (14817).
Program Definition scalar_from_bytes_strict
   : package (fset.fset0) [interface] [interface
  #val #[ SCALAR_FROM_BYTES_STRICT ] : scalar_from_bytes_strict_inp → scalar_from_bytes_strict_out
  ] :=
  (
    [package #def #[ SCALAR_FROM_BYTES_STRICT ] (temp_inp : scalar_from_bytes_strict_inp) : scalar_from_bytes_strict_out { 
    let '(b_14798) := temp_inp : bytes32_t in
    ({ code  '(s_14809 : big_integer_t) ←
        ( '(temp_14800 : seq uint8) ←
            (array_to_seq (b_14798)) ;;
           '(temp_14802 : big_integer_t) ←
            (nat_mod_from_byte_seq_be (temp_14800)) ;;
          ret (temp_14802)) ;;
       '(max_scalar_14810 : big_integer_t) ←
        ( temp_14804 ←
            (nat_mod_max_val ) ;;
           temp_14806 ←
            (nat_mod_to_byte_seq_be (temp_14804)) ;;
           '(temp_14808 : big_integer_t) ←
            (nat_mod_from_byte_seq_be (temp_14806)) ;;
          ret (temp_14808)) ;;
       '(temp_14812 : bool_ChoiceEquality) ←
        ((s_14809) >.? (max_scalar_14810)) ;;
       '(temp_14814 : seq uint8) ←
        (array_to_seq (b_14798)) ;;
       '(temp_14816 : scalar_t) ←
        (nat_mod_from_byte_seq_be (temp_14814)) ;;
      @ret ((option scalar_t)) ((if (
            temp_14812):bool_ChoiceEquality then (*inline*) (
            @None scalar_t) else (@Some scalar_t (temp_14816)))) } : code (
        fset.fset0) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_scalar_from_bytes_strict : package _ _ _ :=
  (scalar_from_bytes_strict).
Fail Next Obligation.


Notation "'seckey_scalar_from_bytes_inp'" := (
  bytes32_t : choice_type) (in custom pack_type at level 2).
Notation "'seckey_scalar_from_bytes_out'" := ((
    option scalar_t) : choice_type) (in custom pack_type at level 2).
Definition SECKEY_SCALAR_FROM_BYTES : nat :=
  (14826).
Program Definition seckey_scalar_from_bytes
   : package (fset.fset0) [interface
  #val #[ SCALAR_FROM_BYTES_STRICT ] : scalar_from_bytes_strict_inp → scalar_from_bytes_strict_out
  ] [interface
  #val #[ SECKEY_SCALAR_FROM_BYTES ] : seckey_scalar_from_bytes_inp → seckey_scalar_from_bytes_out
  ] :=
  (
    [package #def #[ SECKEY_SCALAR_FROM_BYTES ] (temp_inp : seckey_scalar_from_bytes_inp) : seckey_scalar_from_bytes_out { 
    let '(b_14818) := temp_inp : bytes32_t in
    #import {sig #[ SCALAR_FROM_BYTES_STRICT ] : scalar_from_bytes_strict_inp → scalar_from_bytes_strict_out } as scalar_from_bytes_strict ;;
    let scalar_from_bytes_strict := fun x_0 => scalar_from_bytes_strict (x_0) in
    ({ code bnd(
        ChoiceEqualityMonad.option_bind_code , scalar_t , _ , fset.fset0) s_14821 ⇠
      (({ code  '(temp_14820 : (option scalar_t)) ←
            (scalar_from_bytes_strict (b_14818)) ;;
          @ret _ (temp_14820) } : code (fset.fset0) [interface
          #val #[ SCALAR_FROM_BYTES_STRICT ] : scalar_from_bytes_strict_inp → scalar_from_bytes_strict_out
          ] _)) in
      ({ code  '(temp_14823 : scalar_t) ←
          (nat_mod_zero ) ;;
         '(temp_14825 : bool_ChoiceEquality) ←
          ((s_14821) =.? (temp_14823)) ;;
        @ret ((option scalar_t)) ((if (
              temp_14825):bool_ChoiceEquality then (*inline*) (
              @None scalar_t) else (@Some scalar_t (s_14821)))) } : code (
          fset.fset0) [interface
        #val #[ SCALAR_FROM_BYTES_STRICT ] : scalar_from_bytes_strict_inp → scalar_from_bytes_strict_out
        ] _) } : code (fset.fset0) [interface
      #val #[ SCALAR_FROM_BYTES_STRICT ] : scalar_from_bytes_strict_inp → scalar_from_bytes_strict_out
      ] _)
    }]).
Fail Next Obligation.
Program Definition package_seckey_scalar_from_bytes : package _ _ _ :=
  (seq_link seckey_scalar_from_bytes link_rest(
      package_scalar_from_bytes_strict)).
Fail Next Obligation.


Notation "'fieldelem_from_bytes_inp'" := (
  public_key_t : choice_type) (in custom pack_type at level 2).
Notation "'fieldelem_from_bytes_out'" := ((
    option field_element_t) : choice_type) (in custom pack_type at level 2).
Definition FIELDELEM_FROM_BYTES : nat :=
  (14842).
Program Definition fieldelem_from_bytes
   : package (fset.fset0) [interface] [interface
  #val #[ FIELDELEM_FROM_BYTES ] : fieldelem_from_bytes_inp → fieldelem_from_bytes_out
  ] :=
  (
    [package #def #[ FIELDELEM_FROM_BYTES ] (temp_inp : fieldelem_from_bytes_inp) : fieldelem_from_bytes_out { 
    let '(b_14827) := temp_inp : public_key_t in
    ({ code  '(s_14836 : big_integer_t) ←
        ( '(temp_14829 : big_integer_t) ←
            (nat_mod_from_byte_seq_be (b_14827)) ;;
          ret (temp_14829)) ;;
       '(max_fe_14837 : big_integer_t) ←
        ( temp_14831 ←
            (nat_mod_max_val ) ;;
           temp_14833 ←
            (nat_mod_to_byte_seq_be (temp_14831)) ;;
           '(temp_14835 : big_integer_t) ←
            (nat_mod_from_byte_seq_be (temp_14833)) ;;
          ret (temp_14835)) ;;
       '(temp_14839 : bool_ChoiceEquality) ←
        ((s_14836) >.? (max_fe_14837)) ;;
       '(temp_14841 : field_element_t) ←
        (nat_mod_from_byte_seq_be (b_14827)) ;;
      @ret ((option field_element_t)) ((if (
            temp_14839):bool_ChoiceEquality then (*inline*) (
            @None field_element_t) else (@Some field_element_t (
              temp_14841)))) } : code (fset.fset0) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_fieldelem_from_bytes : package _ _ _ :=
  (fieldelem_from_bytes).
Fail Next Obligation.

Definition b_14858_loc : ChoiceEqualityLocation :=
  ((seq uint8 ; 14861%nat)).
Notation "'xor_bytes_inp'" := (
  bytes32_t '× bytes32_t : choice_type) (in custom pack_type at level 2).
Notation "'xor_bytes_out'" := (
  bytes32_t : choice_type) (in custom pack_type at level 2).
Definition XOR_BYTES : nat :=
  (14862).
Program Definition xor_bytes
   : package (CEfset ([b_14858_loc])) [interface] [interface
  #val #[ XOR_BYTES ] : xor_bytes_inp → xor_bytes_out ] :=
  ([package #def #[ XOR_BYTES ] (temp_inp : xor_bytes_inp) : xor_bytes_out { 
    let '(b0_14843 , b1_14854) := temp_inp : bytes32_t '× bytes32_t in
    ({ code  '(b_14858 : seq uint8) ←
          ( temp_14845 ←
              (array_len (b0_14843)) ;;
             temp_14847 ←
              (seq_new_ (default : uint8) (temp_14845)) ;;
            ret (temp_14847)) ;;
        #put b_14858_loc := b_14858 ;;
       temp_14849 ←
        (array_len (b0_14843)) ;;
       '(b_14858 : (seq uint8)) ←
        (foldi' (usize 0) (temp_14849) b_14858 (L2 := CEfset ([b_14858_loc])) (
              I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (fun i_14850 b_14858 =>
            ({ code  '(b_14858 : seq uint8) ←
                ( temp_14852 ←
                    (array_index (b0_14843) (i_14850)) ;;
                   temp_14855 ←
                    (array_index (b1_14854) (i_14850)) ;;
                   temp_14857 ←
                    ((temp_14852) .^ (temp_14855)) ;;
                  ret (seq_upd b_14858 (i_14850) (temp_14857))) ;;
              
              @ret ((seq uint8)) (b_14858) } : code (CEfset (
                  [b_14858_loc])) [interface] _))) ;;
      
       '(temp_14860 : bytes32_t) ←
        (array_from_seq (32) (b_14858)) ;;
      @ret (bytes32_t) (temp_14860) } : code (CEfset (
          [b_14858_loc])) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_xor_bytes : package _ _ _ :=
  (xor_bytes).
Fail Next Obligation.

Notation "'pubkey_gen_result_t'" := ((
  result error_t public_key_t)) : hacspec_scope.


Notation "'pubkey_gen_inp'" := (
  secret_key_t : choice_type) (in custom pack_type at level 2).
Notation "'pubkey_gen_out'" := (
  pubkey_gen_result_t : choice_type) (in custom pack_type at level 2).
Definition PUBKEY_GEN : nat :=
  (14878).
Program Definition pubkey_gen
   : package (CEfset ([])) [interface
  #val #[ BYTES_FROM_POINT ] : bytes_from_point_inp → bytes_from_point_out ;
  #val #[ FINITE ] : finite_inp → finite_out ;
  #val #[ POINT_MUL_BASE ] : point_mul_base_inp → point_mul_base_out ;
  #val #[ SECKEY_SCALAR_FROM_BYTES ] : seckey_scalar_from_bytes_inp → seckey_scalar_from_bytes_out
  ] [interface #val #[ PUBKEY_GEN ] : pubkey_gen_inp → pubkey_gen_out ] :=
  ([package #def #[ PUBKEY_GEN ] (temp_inp : pubkey_gen_inp) : pubkey_gen_out { 
    let '(seckey_14863) := temp_inp : secret_key_t in
    #import {sig #[ BYTES_FROM_POINT ] : bytes_from_point_inp → bytes_from_point_out } as bytes_from_point ;;
    let bytes_from_point := fun x_0 => bytes_from_point (x_0) in
    #import {sig #[ FINITE ] : finite_inp → finite_out } as finite ;;
    let finite := fun x_0 => finite (x_0) in
    #import {sig #[ POINT_MUL_BASE ] : point_mul_base_inp → point_mul_base_out } as point_mul_base ;;
    let point_mul_base := fun x_0 => point_mul_base (x_0) in
    #import {sig #[ SECKEY_SCALAR_FROM_BYTES ] : seckey_scalar_from_bytes_inp → seckey_scalar_from_bytes_out } as seckey_scalar_from_bytes ;;
    let seckey_scalar_from_bytes := fun x_0 => seckey_scalar_from_bytes (x_0) in
    ({ code bnd(
        ChoiceEqualityMonad.result_bind_code error_t , scalar_t , _ , CEfset (
          [])) d0_14868 ⇠
      (({ code  '(temp_14865 : (option scalar_t)) ←
            (seckey_scalar_from_bytes (seckey_14863)) ;;
           temp_14867 ←
            (option_ok_or (temp_14865) (InvalidSecretKey)) ;;
          @ret _ (temp_14867) } : code (fset.fset0) [interface
          #val #[ SECKEY_SCALAR_FROM_BYTES ] : seckey_scalar_from_bytes_inp → seckey_scalar_from_bytes_out
          ] _)) in
      ({ code  '(p_14875 : (field_element_t '× field_element_t)) ←
          ( '(temp_14870 : point_t) ←
              (point_mul_base (d0_14868)) ;;
             '(temp_14872 : (option affine_point_t)) ←
              (finite (temp_14870)) ;;
             temp_14874 ←
              (option_unwrap (temp_14872)) ;;
            ret (temp_14874)) ;;
         '(temp_14877 : bytes32_t) ←
          (bytes_from_point (p_14875)) ;;
        @ret ((result error_t public_key_t)) (@inl public_key_t error_t (
            temp_14877)) } : code (CEfset ([])) [interface
        #val #[ BYTES_FROM_POINT ] : bytes_from_point_inp → bytes_from_point_out ;
        #val #[ FINITE ] : finite_inp → finite_out ;
        #val #[ POINT_MUL_BASE ] : point_mul_base_inp → point_mul_base_out ;
        #val #[ SECKEY_SCALAR_FROM_BYTES ] : seckey_scalar_from_bytes_inp → seckey_scalar_from_bytes_out
        ] _) } : code (CEfset ([])) [interface
      #val #[ BYTES_FROM_POINT ] : bytes_from_point_inp → bytes_from_point_out ;
      #val #[ FINITE ] : finite_inp → finite_out ;
      #val #[ POINT_MUL_BASE ] : point_mul_base_inp → point_mul_base_out ;
      #val #[ SECKEY_SCALAR_FROM_BYTES ] : seckey_scalar_from_bytes_inp → seckey_scalar_from_bytes_out
      ] _)
    }]).
Fail Next Obligation.
Program Definition package_pubkey_gen : package _ _ _ :=
  (seq_link pubkey_gen link_rest(
      package_bytes_from_point,package_finite,package_point_mul_base,package_seckey_scalar_from_bytes)).
Fail Next Obligation.

Notation "'sign_result_t'" := ((result error_t signature_t)) : hacspec_scope.


Notation "'sign_inp'" := (
  message_t '× secret_key_t '× aux_rand_t : choice_type) (in custom pack_type at level 2).
Notation "'sign_out'" := (
  sign_result_t : choice_type) (in custom pack_type at level 2).
Definition SIGN : nat :=
  (14965).
Program Definition sign
   : package (CEfset ([])) [interface
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
  #val #[ XOR_BYTES ] : xor_bytes_inp → xor_bytes_out ] [interface
  #val #[ SIGN ] : sign_inp → sign_out ] :=
  ([package #def #[ SIGN ] (temp_inp : sign_inp) : sign_out { 
    let '(
      msg_14909 , seckey_14879 , aux_rand_14901) := temp_inp : message_t '× secret_key_t '× aux_rand_t in
    #import {sig #[ BYTES_FROM_POINT ] : bytes_from_point_inp → bytes_from_point_out } as bytes_from_point ;;
    let bytes_from_point := fun x_0 => bytes_from_point (x_0) in
    #import {sig #[ BYTES_FROM_SCALAR ] : bytes_from_scalar_inp → bytes_from_scalar_out } as bytes_from_scalar ;;
    let bytes_from_scalar := fun x_0 => bytes_from_scalar (x_0) in
    #import {sig #[ FINITE ] : finite_inp → finite_out } as finite ;;
    let finite := fun x_0 => finite (x_0) in
    #import {sig #[ HAS_EVEN_Y ] : has_even_y_inp → has_even_y_out } as has_even_y ;;
    let has_even_y := fun x_0 => has_even_y (x_0) in
    #import {sig #[ HASH_AUX ] : hash_aux_inp → hash_aux_out } as hash_aux ;;
    let hash_aux := fun x_0 => hash_aux (x_0) in
    #import {sig #[ HASH_CHALLENGE ] : hash_challenge_inp → hash_challenge_out } as hash_challenge ;;
    let hash_challenge := fun x_0 x_1 x_2 => hash_challenge (x_0,x_1,x_2) in
    #import {sig #[ HASH_NONCE ] : hash_nonce_inp → hash_nonce_out } as hash_nonce ;;
    let hash_nonce := fun x_0 x_1 x_2 => hash_nonce (x_0,x_1,x_2) in
    #import {sig #[ POINT_MUL_BASE ] : point_mul_base_inp → point_mul_base_out } as point_mul_base ;;
    let point_mul_base := fun x_0 => point_mul_base (x_0) in
    #import {sig #[ SCALAR_FROM_BYTES ] : scalar_from_bytes_inp → scalar_from_bytes_out } as scalar_from_bytes ;;
    let scalar_from_bytes := fun x_0 => scalar_from_bytes (x_0) in
    #import {sig #[ SECKEY_SCALAR_FROM_BYTES ] : seckey_scalar_from_bytes_inp → seckey_scalar_from_bytes_out } as seckey_scalar_from_bytes ;;
    let seckey_scalar_from_bytes := fun x_0 => seckey_scalar_from_bytes (x_0) in
    #import {sig #[ VERIFY ] : verify_inp → verify_out } as verify ;;
    let verify := fun x_0 x_1 x_2 => verify (x_0,x_1,x_2) in
    #import {sig #[ XOR_BYTES ] : xor_bytes_inp → xor_bytes_out } as xor_bytes ;;
    let xor_bytes := fun x_0 x_1 => xor_bytes (x_0,x_1) in
    ({ code bnd(
        ChoiceEqualityMonad.result_bind_code error_t , scalar_t , _ , CEfset (
          [])) d0_14884 ⇠
      (({ code  '(temp_14881 : (option scalar_t)) ←
            (seckey_scalar_from_bytes (seckey_14879)) ;;
           temp_14883 ←
            (option_ok_or (temp_14881) (InvalidSecretKey)) ;;
          @ret _ (temp_14883) } : code (fset.fset0) [interface
          #val #[ SECKEY_SCALAR_FROM_BYTES ] : seckey_scalar_from_bytes_inp → seckey_scalar_from_bytes_out
          ] _)) in
      ({ code  '(p_14891 : (field_element_t '× field_element_t)) ←
          ( '(temp_14886 : point_t) ←
              (point_mul_base (d0_14884)) ;;
             '(temp_14888 : (option affine_point_t)) ←
              (finite (temp_14886)) ;;
             temp_14890 ←
              (option_unwrap (temp_14888)) ;;
            ret (temp_14890)) ;;
         '(d_14898 : scalar_t) ←
          ( '(temp_14893 : bool_ChoiceEquality) ←
              (has_even_y (p_14891)) ;;
             '(temp_14895 : scalar_t) ←
              (nat_mod_zero ) ;;
             '(temp_14897 : scalar_t) ←
              ((temp_14895) -% (d0_14884)) ;;
            ret ((if (temp_14893):bool_ChoiceEquality then (*inline*) (
                  d0_14884) else (temp_14897)))) ;;
         '(t_14906 : bytes32_t) ←
          ( '(temp_14900 : bytes32_t) ←
              (bytes_from_scalar (d_14898)) ;;
             '(temp_14903 : bytes32_t) ←
              (hash_aux (aux_rand_14901)) ;;
             '(temp_14905 : bytes32_t) ←
              (xor_bytes (temp_14900) (temp_14903)) ;;
            ret (temp_14905)) ;;
         '(k0_14914 : scalar_t) ←
          ( '(temp_14908 : bytes32_t) ←
              (bytes_from_point (p_14891)) ;;
             '(temp_14911 : bytes32_t) ←
              (hash_nonce (t_14906) (temp_14908) (msg_14909)) ;;
             '(temp_14913 : scalar_t) ←
              (scalar_from_bytes (temp_14911)) ;;
            ret (temp_14913)) ;;
         '(temp_14916 : scalar_t) ←
          (nat_mod_zero ) ;;
         '(temp_14918 : bool_ChoiceEquality) ←
          ((k0_14914) =.? (temp_14916)) ;;
        bnd(
          ChoiceEqualityMonad.result_bind_code error_t , unit_ChoiceEquality , _ , CEfset (
            [])) 'tt ⇠
        (if temp_14918 : bool_ChoiceEquality
          then (*state*) (({ code bnd(
                ChoiceEqualityMonad.result_bind_code error_t , signature_t , _ , CEfset (
                  [])) _ ⇠
              (({ code @ret _ (@inr signature_t error_t (
                      InvalidNonceGenerated)) } : code (CEfset (
                      [])) [interface] _)) in
              ({ code @ret ((result error_t unit_ChoiceEquality)) (
                  @inl unit_ChoiceEquality error_t (
                    (tt : unit_ChoiceEquality))) } : code (CEfset (
                    [])) [interface] _) } : code (CEfset ([])) [interface] _))
          else ({ code @ret ((result error_t unit_ChoiceEquality)) (
              @inl unit_ChoiceEquality error_t (
                (tt : unit_ChoiceEquality))) } : code _ _ _) ) in
        ({ code  '(r_14925 : (field_element_t '× field_element_t)) ←
            ( '(temp_14920 : point_t) ←
                (point_mul_base (k0_14914)) ;;
               '(temp_14922 : (option affine_point_t)) ←
                (finite (temp_14920)) ;;
               temp_14924 ←
                (option_unwrap (temp_14922)) ;;
              ret (temp_14924)) ;;
           '(k_14948 : scalar_t) ←
            ( '(temp_14927 : bool_ChoiceEquality) ←
                (has_even_y (r_14925)) ;;
               '(temp_14929 : scalar_t) ←
                (nat_mod_zero ) ;;
               '(temp_14931 : scalar_t) ←
                ((temp_14929) -% (k0_14914)) ;;
              ret ((if (temp_14927):bool_ChoiceEquality then (*inline*) (
                    k0_14914) else (temp_14931)))) ;;
           '(e_14949 : scalar_t) ←
            ( '(temp_14933 : bytes32_t) ←
                (bytes_from_point (r_14925)) ;;
               '(temp_14935 : bytes32_t) ←
                (bytes_from_point (p_14891)) ;;
               '(temp_14937 : bytes32_t) ←
                (hash_challenge (temp_14933) (temp_14935) (msg_14909)) ;;
               '(temp_14939 : scalar_t) ←
                (scalar_from_bytes (temp_14937)) ;;
              ret (temp_14939)) ;;
           '(sig_14962 : signature_t) ←
            ( '(temp_14941 : signature_t) ←
                (array_new_ (default : uint8) (64)) ;;
               '(temp_14943 : bytes32_t) ←
                (bytes_from_point (r_14925)) ;;
               '(temp_14945 : seq uint8) ←
                (array_to_seq (temp_14943)) ;;
               '(temp_14947 : signature_t) ←
                (array_update (temp_14941) (usize 0) (temp_14945)) ;;
               '(temp_14951 : scalar_t) ←
                ((e_14949) *% (d_14898)) ;;
               '(temp_14953 : scalar_t) ←
                ((k_14948) +% (temp_14951)) ;;
               '(temp_14955 : bytes32_t) ←
                (bytes_from_scalar (temp_14953)) ;;
               '(temp_14957 : seq uint8) ←
                (array_to_seq (temp_14955)) ;;
               '(temp_14959 : signature_t) ←
                (array_update (temp_14947) (usize 32) (temp_14957)) ;;
              ret (temp_14959)) ;;
          bnd(
            ChoiceEqualityMonad.result_bind_code error_t , unit_ChoiceEquality , _ , CEfset (
              [])) _ ⇠
          (({ code  '(temp_14961 : bytes32_t) ←
                (bytes_from_point (p_14891)) ;;
               '(temp_14964 : verification_result_t) ←
                (verify (msg_14909) (temp_14961) (sig_14962)) ;;
              @ret _ (temp_14964) } : code (CEfset ([])) [interface
              #val #[ BYTES_FROM_POINT ] : bytes_from_point_inp → bytes_from_point_out ;
              #val #[ VERIFY ] : verify_inp → verify_out ] _)) in
          ({ code @ret ((result error_t signature_t)) (
              @inl signature_t error_t (sig_14962)) } : code (CEfset (
                [])) [interface
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
            ] _) } : code (CEfset ([])) [interface
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
          #val #[ XOR_BYTES ] : xor_bytes_inp → xor_bytes_out ] _) } : code (
          CEfset ([])) [interface
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
        #val #[ XOR_BYTES ] : xor_bytes_inp → xor_bytes_out ] _) } : code (
        CEfset ([])) [interface
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
      #val #[ XOR_BYTES ] : xor_bytes_inp → xor_bytes_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_sign : package _ _ _ :=
  (seq_link sign link_rest(
      package_bytes_from_point,package_bytes_from_scalar,package_finite,package_has_even_y,package_hash_aux,package_hash_challenge,package_hash_nonce,package_point_mul_base,package_scalar_from_bytes,package_seckey_scalar_from_bytes,package_verify,package_xor_bytes)).
Fail Next Obligation.

Notation "'verification_result_t'" := ((
  result error_t unit_ChoiceEquality)) : hacspec_scope.


Notation "'verify_inp'" := (
  message_t '× public_key_t '× signature_t : choice_type) (in custom pack_type at level 2).
Notation "'verify_out'" := (
  verification_result_t : choice_type) (in custom pack_type at level 2).
Definition VERIFY : nat :=
  (15029).
Program Definition verify
   : package (CEfset ([])) [interface
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
  #val #[ X ] : x_inp → x_out ] [interface
  #val #[ VERIFY ] : verify_inp → verify_out ] :=
  ([package #def #[ VERIFY ] (temp_inp : verify_inp) : verify_out { 
    let '(
      msg_14998 , pubkey_14966 , sig_14974) := temp_inp : message_t '× public_key_t '× signature_t in
    #import {sig #[ BYTES_FROM_POINT ] : bytes_from_point_inp → bytes_from_point_out } as bytes_from_point ;;
    let bytes_from_point := fun x_0 => bytes_from_point (x_0) in
    #import {sig #[ FIELDELEM_FROM_BYTES ] : fieldelem_from_bytes_inp → fieldelem_from_bytes_out } as fieldelem_from_bytes ;;
    let fieldelem_from_bytes := fun x_0 => fieldelem_from_bytes (x_0) in
    #import {sig #[ FINITE ] : finite_inp → finite_out } as finite ;;
    let finite := fun x_0 => finite (x_0) in
    #import {sig #[ HAS_EVEN_Y ] : has_even_y_inp → has_even_y_out } as has_even_y ;;
    let has_even_y := fun x_0 => has_even_y (x_0) in
    #import {sig #[ HASH_CHALLENGE ] : hash_challenge_inp → hash_challenge_out } as hash_challenge ;;
    let hash_challenge := fun x_0 x_1 x_2 => hash_challenge (x_0,x_1,x_2) in
    #import {sig #[ LIFT_X ] : lift_x_inp → lift_x_out } as lift_x ;;
    let lift_x := fun x_0 => lift_x (x_0) in
    #import {sig #[ POINT_ADD ] : point_add_inp → point_add_out } as point_add ;;
    let point_add := fun x_0 x_1 => point_add (x_0,x_1) in
    #import {sig #[ POINT_MUL ] : point_mul_inp → point_mul_out } as point_mul ;;
    let point_mul := fun x_0 x_1 => point_mul (x_0,x_1) in
    #import {sig #[ POINT_MUL_BASE ] : point_mul_base_inp → point_mul_base_out } as point_mul_base ;;
    let point_mul_base := fun x_0 => point_mul_base (x_0) in
    #import {sig #[ SCALAR_FROM_BYTES ] : scalar_from_bytes_inp → scalar_from_bytes_out } as scalar_from_bytes ;;
    let scalar_from_bytes := fun x_0 => scalar_from_bytes (x_0) in
    #import {sig #[ SCALAR_FROM_BYTES_STRICT ] : scalar_from_bytes_strict_inp → scalar_from_bytes_strict_out } as scalar_from_bytes_strict ;;
    let scalar_from_bytes_strict := fun x_0 => scalar_from_bytes_strict (x_0) in
    #import {sig #[ X ] : x_inp → x_out } as x ;;
    let x := fun x_0 => x (x_0) in
    ({ code bnd(
        ChoiceEqualityMonad.result_bind_code error_t , field_element_t , _ , CEfset (
          [])) p_x_14971 ⇠
      (({ code  '(temp_14968 : (option field_element_t)) ←
            (fieldelem_from_bytes (pubkey_14966)) ;;
           temp_14970 ←
            (option_ok_or (temp_14968) (InvalidPublicKey)) ;;
          @ret _ (temp_14970) } : code (fset.fset0) [interface
          #val #[ FIELDELEM_FROM_BYTES ] : fieldelem_from_bytes_inp → fieldelem_from_bytes_out
          ] _)) in
      ({ code bnd(
          ChoiceEqualityMonad.result_bind_code error_t , affine_point_t , _ , CEfset (
            [])) p_14995 ⇠
        (({ code  '(temp_14973 : (result error_t affine_point_t)) ←
              (lift_x (p_x_14971)) ;;
            @ret _ (temp_14973) } : code (CEfset ([])) [interface
            #val #[ LIFT_X ] : lift_x_inp → lift_x_out ] _)) in
        ({ code bnd(
            ChoiceEqualityMonad.result_bind_code error_t , field_element_t , _ , CEfset (
              [])) r_15024 ⇠
          (({ code  '(temp_14976 : seq uint8) ←
                (array_to_seq (sig_14974)) ;;
               '(temp_14978 : bytes32_t) ←
                (array_from_slice (default : uint8) (32) (temp_14976) (
                    usize 0) (usize 32)) ;;
               '(temp_14980 : (option field_element_t)) ←
                (fieldelem_from_bytes (temp_14978)) ;;
               temp_14982 ←
                (option_ok_or (temp_14980) (InvalidSignature)) ;;
              @ret _ (temp_14982) } : code (CEfset ([])) [interface
              #val #[ FIELDELEM_FROM_BYTES ] : fieldelem_from_bytes_inp → fieldelem_from_bytes_out
              ] _)) in
          ({ code bnd(
              ChoiceEqualityMonad.result_bind_code error_t , scalar_t , _ , CEfset (
                [])) s_15003 ⇠
            (({ code  '(temp_14984 : seq uint8) ←
                  (array_to_seq (sig_14974)) ;;
                 '(temp_14986 : bytes32_t) ←
                  (array_from_slice (default : uint8) (32) (temp_14984) (
                      usize 32) (usize 32)) ;;
                 '(temp_14988 : (option scalar_t)) ←
                  (scalar_from_bytes_strict (temp_14986)) ;;
                 temp_14990 ←
                  (option_ok_or (temp_14988) (InvalidSignature)) ;;
                @ret _ (temp_14990) } : code (CEfset ([])) [interface
                #val #[ SCALAR_FROM_BYTES_STRICT ] : scalar_from_bytes_strict_inp → scalar_from_bytes_strict_out
                ] _)) in
            ({ code  '(e_15008 : scalar_t) ←
                ( '(temp_14992 : seq uint8) ←
                    (array_to_seq (sig_14974)) ;;
                   '(temp_14994 : bytes32_t) ←
                    (array_from_slice (default : uint8) (32) (temp_14992) (
                        usize 0) (usize 32)) ;;
                   '(temp_14997 : bytes32_t) ←
                    (bytes_from_point (p_14995)) ;;
                   '(temp_15000 : bytes32_t) ←
                    (hash_challenge (temp_14994) (temp_14997) (msg_14998)) ;;
                   '(temp_15002 : scalar_t) ←
                    (scalar_from_bytes (temp_15000)) ;;
                  ret (temp_15002)) ;;
              bnd(ChoiceEqualityMonad.result_bind_code error_t , (
                  field_element_t '×
                  field_element_t
                ) , _ , CEfset ([])) r_p_15019 ⇠
              (({ code  '(temp_15005 : point_t) ←
                    (point_mul_base (s_15003)) ;;
                   '(temp_15007 : scalar_t) ←
                    (nat_mod_zero ) ;;
                   '(temp_15010 : scalar_t) ←
                    ((temp_15007) -% (e_15008)) ;;
                   '(temp_15012 : point_t) ←
                    (point_mul (temp_15010) (Affine (p_14995))) ;;
                   '(temp_15014 : point_t) ←
                    (point_add (temp_15005) (temp_15012)) ;;
                   '(temp_15016 : (option affine_point_t)) ←
                    (finite (temp_15014)) ;;
                   temp_15018 ←
                    (option_ok_or (temp_15016) (InvalidSignature)) ;;
                  @ret _ (temp_15018) } : code (CEfset ([])) [interface
                  #val #[ FINITE ] : finite_inp → finite_out ;
                  #val #[ POINT_ADD ] : point_add_inp → point_add_out ;
                  #val #[ POINT_MUL ] : point_mul_inp → point_mul_out ;
                  #val #[ POINT_MUL_BASE ] : point_mul_base_inp → point_mul_base_out
                  ] _)) in
              ({ code  '(temp_15021 : bool_ChoiceEquality) ←
                  (has_even_y (r_p_15019)) ;;
                 '(temp_15023 : field_element_t) ←
                  (x (r_p_15019)) ;;
                 '(temp_15026 : bool_ChoiceEquality) ←
                  ((temp_15023) !=.? (r_15024)) ;;
                 '(temp_15028 : bool_ChoiceEquality) ←
                  ((negb (temp_15021)) || (temp_15026)) ;;
                @ret ((result error_t unit_ChoiceEquality)) ((if (
                      temp_15028):bool_ChoiceEquality then (*inline*) (
                      @inr unit_ChoiceEquality error_t (
                        InvalidSignature)) else (
                      @inl unit_ChoiceEquality error_t (tt)))) } : code (
                  CEfset ([])) [interface
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
                #val #[ X ] : x_inp → x_out ] _) } : code (CEfset (
                  [])) [interface
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
              #val #[ X ] : x_inp → x_out ] _) } : code (CEfset (
                [])) [interface
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
            #val #[ X ] : x_inp → x_out ] _) } : code (CEfset ([])) [interface
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
          #val #[ X ] : x_inp → x_out ] _) } : code (CEfset ([])) [interface
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
        #val #[ X ] : x_inp → x_out ] _) } : code (CEfset ([])) [interface
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
      #val #[ X ] : x_inp → x_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_verify : package _ _ _ :=
  (seq_link verify link_rest(
      package_bytes_from_point,package_fieldelem_from_bytes,package_finite,package_has_even_y,package_hash_challenge,package_lift_x,package_point_add,package_point_mul,package_point_mul_base,package_scalar_from_bytes,package_scalar_from_bytes_strict,package_x)).
Fail Next Obligation.

