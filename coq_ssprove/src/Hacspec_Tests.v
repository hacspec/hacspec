(** This file was automatically generated using Hacspec **)
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


Definition let_test_pure (st_2 : uint_size) : uint_size :=
  let a_3 : uint_size :=
    st_2 in 
  let st_0 : uint_size :=
    a_3 in 
  let st_0 :=
    usize 35 in 
  st_0.
Definition let_test_pure_code
  (st_2 : uint_size)
  : code fset.fset0 [interface] (@ct uint_size) :=
  lift_to_code (let_test_pure st_2).

Definition st_0_loc : ChoiceEqualityLocation :=
  ((uint_size ; 4%nat)).
Program Definition let_test_state
  (st_2 : uint_size) : code (CEfset ([st_0_loc])) [interface] (@ct (
      uint_size)) :=
  (({ code  '(a_3: uint_size ) ←
        (ret (st_2)) ;;
       '(st_0: uint_size ) ←
          (ret (a_3)) ;;
        #put st_0_loc := st_0 ;;
       st_0 ←
          ((ret (usize 35))) ;;
        #put st_0_loc := st_0 ;;
      
      @ret (uint_size) (st_0) } : code (CEfset ([st_0_loc])) [interface] _)).
Fail Next Obligation.

Program Definition let_test
  (st_2 : uint_size)
  : both (CEfset ([st_0_loc])) [interface] (uint_size) :=
  letb a_3 : uint_size := lift_to_both0 st_2 in
  letbm st_0 : uint_size loc( st_0_loc ) := lift_to_both0 a_3 in
  letbm st_0 loc( st_0_loc ) := lift_to_both0 (usize 35) in
  lift_scope (H_incl := _) (lift_to_both0 st_0)
  .
Fail Next Obligation.

Definition if_cond_pure (b_5 : bool_ChoiceEquality) : int32 :=
  (if (b_5):bool_ChoiceEquality then (@repr U32 32) else (@repr U32 4)).
Definition if_cond_pure_code
  (b_5 : bool_ChoiceEquality)
  : code fset.fset0 [interface] (@ct int32) :=
  lift_to_code (if_cond_pure b_5).


Program Definition if_cond_state
  (b_5 : bool_ChoiceEquality) : code (fset.fset0) [interface] (@ct (int32)) :=
  (({ code @ret (int32) ((if (b_5):bool_ChoiceEquality then (
            @repr U32 32) else (@repr U32 4))) } : code (
        fset.fset0) [interface] _)).
Fail Next Obligation.

Program Definition if_cond
  (b_5 : bool_ChoiceEquality)
  : both (fset.fset0) [interface] (int32) :=
  lift_scope (H_incl := _) (if is_pure (I := [interface]) (lift_to_both0 b_5)
    then lift_to_both0 (@repr U32 32)
    else lift_to_both0 (@repr U32 4))
  .
Fail Next Obligation.

Definition for_loop_pure (i_8 : uint_size) : uint_size :=
  let sum_6 : uint_size :=
    usize 0 in 
  let sum_6 :=
    Hacspec_Lib_Pre.foldi (usize 0) (i_8) sum_6
      (fun i_9 sum_6 =>
      let sum_6 :=
        ((sum_6) .+ (i_9)) in 
      (sum_6)) in 
  sum_6.
Definition for_loop_pure_code
  (i_8 : uint_size)
  : code fset.fset0 [interface] (@ct uint_size) :=
  lift_to_code (for_loop_pure i_8).

Definition sum_6_loc : ChoiceEqualityLocation :=
  ((uint_size ; 12%nat)).
Program Definition for_loop_state
  (i_8 : uint_size) : code (CEfset ([sum_6_loc])) [interface] (@ct (
      uint_size)) :=
  (({ code  '(sum_6: uint_size ) ←
          (ret (usize 0)) ;;
        #put sum_6_loc := sum_6 ;;
       sum_6 ←
        (foldi (usize 0) (i_8) sum_6 (fun i_9 (sum_6 : _) =>
            ({ code  sum_6 ←
                  (( temp_11 ←
                        ((sum_6) .+ (i_9)) ;;
                      ret (temp_11))) ;;
                #put sum_6_loc := sum_6 ;;
              
              @ret (_) (prod_ce(sum_6)) } : code (CEfset (
                  [sum_6_loc])) [interface] _))) ;;
      
      @ret (uint_size) (sum_6) } : code (CEfset ([sum_6_loc])) [interface] _)).
Fail Next Obligation.

Program Definition for_loop
  (i_8 : uint_size)
  : both (CEfset ([sum_6_loc])) [interface] (uint_size) :=
  letbm sum_6 : uint_size loc( sum_6_loc ) := lift_to_both0 (usize 0) in
  letb sum_6 :=
    foldi_both' (lift_to_both0 (usize 0)) (lift_to_both0 i_8) sum_6 (L := (
        CEfset ([sum_6_loc]))) (fun i_9 (sum_6 : _) =>
      letbm sum_6 loc( sum_6_loc ) :=
        (lift_to_both0 sum_6) .+ (lift_to_both0 i_9) in
      lift_scope (H_incl := _) (lift_to_both0 sum_6)
      ) in
  lift_scope (H_incl := _) (lift_to_both0 sum_6)
  .
Fail Next Obligation.

Definition result_test_pure (i_15 : uint_size) : (result uint_size int32) :=
  let sum_13 : uint_size :=
    usize 0 in 
  sum_13 m( _ ) ⇠ (foldibnd (usize 0) to (
      i_15) M( _ ) for sum_13 >> (fun i_16 sum_13 =>
    let sum_13 :=
      ((sum_13) .+ (i_16)) in 
    let _ : uint_size :=
      for_loop (i_16) in 
    let _ : uint_size :=
      let_test (i_16) in 
     _ m( _ ) ⇠ (@Err int32 uint_size (i_16)) ;; (Ok ((sum_13))))) ;;
  (@Ok int32 uint_size (pub_u32 (sum_13))).
Definition result_test_pure_code
  (i_15 : uint_size)
  : code fset.fset0 [interface] (@ct (result uint_size int32)) :=
  lift_to_code (result_test_pure i_15).

Definition sum_13_loc : ChoiceEqualityLocation :=
  ((uint_size ; 23%nat)).
Program Definition result_test_state
  (i_15 : uint_size) : code (CEfset (
      [st_0_loc ; sum_6_loc ; sum_13_loc])) [interface] (@ct ((
        result uint_size int32))) :=
  (({ code  '(sum_13: uint_size ) ←
          (ret (usize 0)) ;;
        #put sum_13_loc := sum_13 ;;
      bnd( ChoiceEqualityMonad.result_bind_code uint_size , int32 , int32 , CEfset (
        [st_0_loc ; sum_6_loc ; sum_13_loc])) 'sum_13 ⇠
      (foldi_bind_code (usize 0) (i_15) (
          lift_to_code (ChoiceEqualityMonad.ret sum_13)) (fun i_16 sum_13 =>
        ({ code  sum_13 ←
              (( temp_18 ←
                    ((sum_13) .+ (i_16)) ;;
                  ret (temp_18))) ;;
            #put sum_13_loc := sum_13 ;;
          
           '(_: uint_size ) ←
            ( temp_20 ←
                (for_loop (i_16)) ;;
              ret (temp_20)) ;;
           '(_: uint_size ) ←
            ( temp_22 ←
                (let_test (i_16)) ;;
              ret (temp_22)) ;;
          bnd( _ , int32 , _ , CEfset (
            [st_0_loc ; sum_6_loc ; sum_13_loc])) _ ⇠
          (({ code @ret _ (@Err int32 uint_size (
                  i_16)) } : code _ [interface] _)) in
          ({ code @ret (_) (Ok (prod_ce(sum_13
                ))) } : code _ [interface] _) } : code (CEfset (
              [st_0_loc ; sum_6_loc ; sum_13_loc])) [interface] _))) in
      ({ code @ret ((result uint_size int32)) (@Ok int32 uint_size (pub_u32 (
              sum_13))) } : code _ [interface] _) } : code (CEfset (
          [st_0_loc ; sum_6_loc ; sum_13_loc])) [interface] _)).
Fail Next Obligation.

Program Definition result_test
  (i_15 : uint_size)
  : both (CEfset ([st_0_loc ; sum_6_loc ; sum_13_loc])) [interface] ((
      result uint_size int32)) :=
  letbm sum_13 : uint_size loc( sum_13_loc ) := lift_to_both0 (usize 0) in
  letbnd(_) sum_13 :=
    foldi_bind_both' (lift_to_both0 (usize 0)) (
        lift_to_both0 i_15) sum_13 (L := (CEfset (
          [st_0_loc ; sum_6_loc ; sum_13_loc]))) (fun i_16 (sum_13 : _) =>
      letbm sum_13 loc( sum_13_loc ) :=
        (lift_to_both0 sum_13) .+ (lift_to_both0 i_16) in
      letb _ : uint_size := for_loop (lift_to_both0 i_16) in
      letb _ : uint_size := let_test (lift_to_both0 i_16) in
      letbnd(ChoiceEqualityMonad.result_bind_code uint_size) _ : int32 :=
        @Err int32 uint_size (lift_to_both0 i_16) in
      lift_scope (H_incl := _) (Ok (lift_to_both0 sum_13))
      ) in
  lift_scope (H_incl := _) (@Ok int32 uint_size (pub_u32 (is_pure (
          lift_to_both0 sum_13))))
  .
Fail Next Obligation.

Definition if_inlinecond_pure
  (v_24 : int32)
  : (result bool_ChoiceEquality int32) :=
   x_25 m( _ ) ⇠ ((if (((v_24) <.? (@repr U32 0))):bool_ChoiceEquality then (
        @Ok int32 bool_ChoiceEquality (@repr U32 4)) else (
        @Err int32 bool_ChoiceEquality (true)))) ;;
  (@Ok int32 bool_ChoiceEquality (v_24)).
Definition if_inlinecond_pure_code
  (v_24 : int32)
  : code fset.fset0 [interface] (@ct (result bool_ChoiceEquality int32)) :=
  lift_to_code (if_inlinecond_pure v_24).


Program Definition if_inlinecond_state
  (v_24 : int32) : code (fset.fset0) [interface] (@ct ((
        result bool_ChoiceEquality int32))) :=
  (({ code bnd( _ , int32 , _ , fset.fset0) x_25 ⇠
      (({ code  temp_27 ←
            ((v_24) <.? (@repr U32 0)) ;;
          @ret _ ((if (temp_27):bool_ChoiceEquality then (
                @Ok int32 bool_ChoiceEquality (@repr U32 4)) else (
                @Err int32 bool_ChoiceEquality (
                  (true : bool_ChoiceEquality))))) } : code _ [interface] _)) in
      ({ code @ret ((result bool_ChoiceEquality int32)) (
          @Ok int32 bool_ChoiceEquality (
            v_24)) } : code _ [interface] _) } : code (
        fset.fset0) [interface] _)).
Fail Next Obligation.

Program Definition if_inlinecond
  (v_24 : int32)
  : both (fset.fset0) [interface] ((result bool_ChoiceEquality int32)) :=
  letbnd(ChoiceEqualityMonad.result_bind_code bool_ChoiceEquality) x_25 : int32 :=
    if is_pure (I := [interface]) ((lift_to_both0 v_24) <.? (lift_to_both0 (
          @repr U32 0)))
    then @Ok int32 bool_ChoiceEquality (lift_to_both0 (@repr U32 4))
    else @Err int32 bool_ChoiceEquality (lift_to_both0 (
        (true : bool_ChoiceEquality))) in
  lift_scope (H_incl := _) (@Ok int32 bool_ChoiceEquality (lift_to_both0 v_24))
  .
Fail Next Obligation.

Definition if_inlinecond2_pure
  (v_28 : int32)
  : (result bool_ChoiceEquality int32) :=
  ifbnd (((v_28) <.? (@repr U32 0))) : bool_ChoiceEquality
  then (let _ : (result bool_ChoiceEquality int32) :=
      @Ok int32 bool_ChoiceEquality (@repr U32 4) in 
    (tt : unit_ChoiceEquality))
  elsebnd( _ m( _ ) ⇠ (@Err int32 bool_ChoiceEquality (true)) ;;
    (Ok ((tt : unit_ChoiceEquality)))) >> (fun 'tt =>
  @Ok int32 bool_ChoiceEquality (v_28)).
Definition if_inlinecond2_pure_code
  (v_28 : int32)
  : code fset.fset0 [interface] (@ct (result bool_ChoiceEquality int32)) :=
  lift_to_code (if_inlinecond2_pure v_28).


Program Definition if_inlinecond2_state
  (v_28 : int32) : code (fset.fset0) [interface] (@ct ((
        result bool_ChoiceEquality int32))) :=
  (({ code  temp_30 ←
        ((v_28) <.? (@repr U32 0)) ;;
      if_bind_code (A := _) (B := int32) (H_bind_code := ChoiceEqualityMonad.result_bind_code bool_ChoiceEquality) (Lx := fset.fset0) (Ly := fset.fset0) (L2 := fset.fset0) (it1 := _) (it2 := _) (
        temp_30 : bool_ChoiceEquality)
      (({ code  '(_: (result bool_ChoiceEquality int32) ) ←
            (ret (@Ok int32 bool_ChoiceEquality (@repr U32 4))) ;;
          @ret (_) (Ok ((tt : unit_ChoiceEquality))) } : code (
            fset.fset0) [interface] _))
      ( (({ code bnd( _ , int32 , _ , fset.fset0) _ ⇠
            (({ code @ret _ (@Err int32 bool_ChoiceEquality (
                    (true : bool_ChoiceEquality))) } : code _ [interface] _)) in
            ({ code @ret (_) (Ok (
                  (tt : unit_ChoiceEquality))) } : code _ [interface] _) } : code (
              fset.fset0) [interface] _))) (fun tt =>
      ({ code @ret ((result bool_ChoiceEquality int32)) (
          @Ok int32 bool_ChoiceEquality (
            v_28)) } : code _ [interface] _)) } : code (
        fset.fset0) [interface] _)).
Fail Next Obligation.

Program Definition if_inlinecond2
  (v_28 : int32)
  : both (fset.fset0) [interface] ((result bool_ChoiceEquality int32)) :=
  letbnd(_) 'tt :=
    if (lift_to_both0 v_28) <.? (lift_to_both0 (
        @repr U32 0)):bool_ChoiceEquality
    then lift_scope (L1 := fset.fset0) (L2 := fset.fset0) (H_incl := _) (
      letb _ : (result bool_ChoiceEquality int32) :=
        @Ok int32 bool_ChoiceEquality (lift_to_both0 (@repr U32 4)) in
      lift_scope (H_incl := _) (Ok (lift_to_both0 ((tt : unit_ChoiceEquality))))
      )
    else lift_scope (L1 := fset.fset0) (L2 := fset.fset0) (H_incl := _) (
      letbnd(ChoiceEqualityMonad.result_bind_code bool_ChoiceEquality) _ : int32 :=
        @Err int32 bool_ChoiceEquality (lift_to_both0 (
            (true : bool_ChoiceEquality))) in
      lift_scope (H_incl := _) (Ok (lift_to_both0 ((tt : unit_ChoiceEquality))))
      ) in
  lift_scope (H_incl := _) (@Ok int32 bool_ChoiceEquality (lift_to_both0 v_28))
  .
Fail Next Obligation.

