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


Definition state_t := nseq (uint32) (usize 16).

Definition state_idx_t :=
  nat_mod (usize 16).
Definition uint_size_in_state_idx_t(n : uint_size) : state_idx_t := int_in_nat_mod n.
Coercion uint_size_in_state_idx_t : uint_size >-> state_idx_t.

Definition constants_t := nseq (uint32) (usize 4).

Definition constants_idx_t :=
  nat_mod (usize 4).
Definition uint_size_in_constants_idx_t(n : uint_size) : constants_idx_t := int_in_nat_mod n.
Coercion uint_size_in_constants_idx_t : uint_size >-> constants_idx_t.

Definition block_t := nseq (uint8) (usize 64).

Definition cha_cha_iv_t := nseq (uint8) (usize 12).

Definition cha_cha_key_t := nseq (uint8) (usize 32).

Definition state_436_loc : ChoiceEqualityLocation :=
  (state_t ; 437%nat).
Notation "'chacha20_line_inp'" :=(
  state_idx_t '× state_idx_t '× state_idx_t '× uint_size '× state_t : choice_type) (in custom pack_type at level 2).
Notation "'chacha20_line_inp'" :=(
  state_idx_t '× state_idx_t '× state_idx_t '× uint_size '× state_t : ChoiceEquality) (at level 2).
Notation "'chacha20_line_out'" :=(
  state_t : choice_type) (in custom pack_type at level 2).
Notation "'chacha20_line_out'" :=(state_t : ChoiceEquality) (at level 2).
Definition CHACHA20_LINE : nat :=
  443.
Program Definition chacha20_line
  : both_package (CEfset ([state_436_loc])) [interface] [(CHACHA20_LINE,(
      chacha20_line_inp,chacha20_line_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(
      a_439 , b_440 , d_441 , s_442 , m_438) := temp_inp : state_idx_t '× state_idx_t '× state_idx_t '× uint_size '× state_t in
    
    ((letbm state_436 : state_t loc( state_436_loc ) := lift_to_both0 m_438 in
        letb state_436 : state_t :=
          array_upd state_436 (lift_to_both0 a_439) (is_pure ((array_index (
                  state_436) (lift_to_both0 a_439)) .+ (array_index (
                  state_436) (lift_to_both0 b_440)))) in
        letb state_436 : state_t :=
          array_upd state_436 (lift_to_both0 d_441) (is_pure ((array_index (
                  state_436) (lift_to_both0 d_441)) .^ (array_index (
                  state_436) (lift_to_both0 a_439)))) in
        letb state_436 : state_t :=
          array_upd state_436 (lift_to_both0 d_441) (is_pure (
              uint32_rotate_left (array_index (state_436) (
                  lift_to_both0 d_441)) (lift_to_both0 s_442))) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          lift_to_both0 state_436)
        ) : both (CEfset ([state_436_loc])) [interface] (state_t)))in
  both_package' _ _ (CHACHA20_LINE,(
      chacha20_line_inp,chacha20_line_out)) temp_package_both.
Fail Next Obligation.


Notation "'chacha20_quarter_round_inp'" :=(
  state_idx_t '× state_idx_t '× state_idx_t '× state_idx_t '× state_t : choice_type) (in custom pack_type at level 2).
Notation "'chacha20_quarter_round_inp'" :=(
  state_idx_t '× state_idx_t '× state_idx_t '× state_idx_t '× state_t : ChoiceEquality) (at level 2).
Notation "'chacha20_quarter_round_out'" :=(
  state_t : choice_type) (in custom pack_type at level 2).
Notation "'chacha20_quarter_round_out'" :=(
  state_t : ChoiceEquality) (at level 2).
Definition CHACHA20_QUARTER_ROUND : nat :=
  452.
Program Definition chacha20_quarter_round
  : both_package (CEfset ([])) [interface
  #val #[ CHACHA20_LINE ] : chacha20_line_inp → chacha20_line_out ] [(
    CHACHA20_QUARTER_ROUND,(
      chacha20_quarter_round_inp,chacha20_quarter_round_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(
      a_444 , b_445 , c_449 , d_446 , state_447) := temp_inp : state_idx_t '× state_idx_t '× state_idx_t '× state_idx_t '× state_t in
    
    let chacha20_line := fun x_0 x_1 x_2 x_3 x_4 => package_both chacha20_line (
      x_0,x_1,x_2,x_3,x_4) in
    ((letb state_448 : state_t :=
          chacha20_line (lift_to_both0 a_444) (lift_to_both0 b_445) (
            lift_to_both0 d_446) (lift_to_both0 (usize 16)) (
            lift_to_both0 state_447) in
        letb state_450 : state_t :=
          chacha20_line (lift_to_both0 c_449) (lift_to_both0 d_446) (
            lift_to_both0 b_445) (lift_to_both0 (usize 12)) (
            lift_to_both0 state_448) in
        letb state_451 : state_t :=
          chacha20_line (lift_to_both0 a_444) (lift_to_both0 b_445) (
            lift_to_both0 d_446) (lift_to_both0 (usize 8)) (
            lift_to_both0 state_450) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (chacha20_line (
            lift_to_both0 c_449) (lift_to_both0 d_446) (lift_to_both0 b_445) (
            lift_to_both0 (usize 7)) (lift_to_both0 state_451))
        ) : both (CEfset ([])) [interface
      #val #[ CHACHA20_LINE ] : chacha20_line_inp → chacha20_line_out ] (
        state_t)))in
  both_package' _ _ (CHACHA20_QUARTER_ROUND,(
      chacha20_quarter_round_inp,chacha20_quarter_round_out)) temp_package_both.
Fail Next Obligation.


Notation "'chacha20_double_round_inp'" :=(
  state_t : choice_type) (in custom pack_type at level 2).
Notation "'chacha20_double_round_inp'" :=(
  state_t : ChoiceEquality) (at level 2).
Notation "'chacha20_double_round_out'" :=(
  state_t : choice_type) (in custom pack_type at level 2).
Notation "'chacha20_double_round_out'" :=(
  state_t : ChoiceEquality) (at level 2).
Definition CHACHA20_DOUBLE_ROUND : nat :=
  461.
Program Definition chacha20_double_round
  : both_package (CEfset ([])) [interface
  #val #[ CHACHA20_QUARTER_ROUND ] : chacha20_quarter_round_inp → chacha20_quarter_round_out
  ] [(CHACHA20_DOUBLE_ROUND,(
      chacha20_double_round_inp,chacha20_double_round_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(state_453) := temp_inp : state_t in
    
    let chacha20_quarter_round := fun x_0 x_1 x_2 x_3 x_4 => package_both chacha20_quarter_round (
      x_0,x_1,x_2,x_3,x_4) in
    ((letb state_454 : state_t :=
          chacha20_quarter_round (lift_to_both0 (usize 0)) (lift_to_both0 (
              usize 4)) (lift_to_both0 (usize 8)) (lift_to_both0 (usize 12)) (
            lift_to_both0 state_453) in
        letb state_455 : state_t :=
          chacha20_quarter_round (lift_to_both0 (usize 1)) (lift_to_both0 (
              usize 5)) (lift_to_both0 (usize 9)) (lift_to_both0 (usize 13)) (
            lift_to_both0 state_454) in
        letb state_456 : state_t :=
          chacha20_quarter_round (lift_to_both0 (usize 2)) (lift_to_both0 (
              usize 6)) (lift_to_both0 (usize 10)) (lift_to_both0 (usize 14)) (
            lift_to_both0 state_455) in
        letb state_457 : state_t :=
          chacha20_quarter_round (lift_to_both0 (usize 3)) (lift_to_both0 (
              usize 7)) (lift_to_both0 (usize 11)) (lift_to_both0 (usize 15)) (
            lift_to_both0 state_456) in
        letb state_458 : state_t :=
          chacha20_quarter_round (lift_to_both0 (usize 0)) (lift_to_both0 (
              usize 5)) (lift_to_both0 (usize 10)) (lift_to_both0 (usize 15)) (
            lift_to_both0 state_457) in
        letb state_459 : state_t :=
          chacha20_quarter_round (lift_to_both0 (usize 1)) (lift_to_both0 (
              usize 6)) (lift_to_both0 (usize 11)) (lift_to_both0 (usize 12)) (
            lift_to_both0 state_458) in
        letb state_460 : state_t :=
          chacha20_quarter_round (lift_to_both0 (usize 2)) (lift_to_both0 (
              usize 7)) (lift_to_both0 (usize 8)) (lift_to_both0 (usize 13)) (
            lift_to_both0 state_459) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          chacha20_quarter_round (lift_to_both0 (usize 3)) (lift_to_both0 (
              usize 4)) (lift_to_both0 (usize 9)) (lift_to_both0 (usize 14)) (
            lift_to_both0 state_460))
        ) : both (CEfset ([])) [interface
      #val #[ CHACHA20_QUARTER_ROUND ] : chacha20_quarter_round_inp → chacha20_quarter_round_out
      ] (state_t)))in
  both_package' _ _ (CHACHA20_DOUBLE_ROUND,(
      chacha20_double_round_inp,chacha20_double_round_out)) temp_package_both.
Fail Next Obligation.

Definition st_462_loc : ChoiceEqualityLocation :=
  (state_t ; 463%nat).
Notation "'chacha20_rounds_inp'" :=(
  state_t : choice_type) (in custom pack_type at level 2).
Notation "'chacha20_rounds_inp'" :=(state_t : ChoiceEquality) (at level 2).
Notation "'chacha20_rounds_out'" :=(
  state_t : choice_type) (in custom pack_type at level 2).
Notation "'chacha20_rounds_out'" :=(state_t : ChoiceEquality) (at level 2).
Definition CHACHA20_ROUNDS : nat :=
  466.
Program Definition chacha20_rounds
  : both_package (CEfset ([st_462_loc])) [interface
  #val #[ CHACHA20_DOUBLE_ROUND ] : chacha20_double_round_inp → chacha20_double_round_out
  ] [(CHACHA20_ROUNDS,(chacha20_rounds_inp,chacha20_rounds_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(state_464) := temp_inp : state_t in
    
    let chacha20_double_round := fun x_0 => package_both chacha20_double_round (
      x_0) in
    ((letbm st_462 : state_t loc( st_462_loc ) := lift_to_both0 state_464 in
        letb st_462 :=
          foldi_both' (lift_to_both0 (usize 0)) (lift_to_both0 (
                usize 10)) st_462 (L := (CEfset ([st_462_loc]))) (I := (
              [interface
              #val #[ CHACHA20_DOUBLE_ROUND ] : chacha20_double_round_inp → chacha20_double_round_out
              ])) (fun i_465 st_462 =>
            letbm st_462 loc( st_462_loc ) :=
              chacha20_double_round (lift_to_both0 st_462) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 st_462)
            ) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 st_462)
        ) : both (CEfset ([st_462_loc])) [interface
      #val #[ CHACHA20_DOUBLE_ROUND ] : chacha20_double_round_inp → chacha20_double_round_out
      ] (state_t)))in
  both_package' _ _ (CHACHA20_ROUNDS,(
      chacha20_rounds_inp,chacha20_rounds_out)) temp_package_both.
Fail Next Obligation.

Definition state_467_loc : ChoiceEqualityLocation :=
  (state_t ; 468%nat).
Notation "'chacha20_core_inp'" :=(
  uint32 '× state_t : choice_type) (in custom pack_type at level 2).
Notation "'chacha20_core_inp'" :=(
  uint32 '× state_t : ChoiceEquality) (at level 2).
Notation "'chacha20_core_out'" :=(
  state_t : choice_type) (in custom pack_type at level 2).
Notation "'chacha20_core_out'" :=(state_t : ChoiceEquality) (at level 2).
Definition CHACHA20_CORE : nat :=
  472.
Program Definition chacha20_core
  : both_package (CEfset ([state_467_loc])) [interface
  #val #[ CHACHA20_ROUNDS ] : chacha20_rounds_inp → chacha20_rounds_out ] [(
    CHACHA20_CORE,(chacha20_core_inp,chacha20_core_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(ctr_470 , st0_469) := temp_inp : uint32 '× state_t in
    
    let chacha20_rounds := fun x_0 => package_both chacha20_rounds (x_0) in
    ((letbm state_467 : state_t loc( state_467_loc ) := lift_to_both0 st0_469 in
        letb state_467 : state_t :=
          array_upd state_467 (lift_to_both0 (usize 12)) (is_pure ((
                array_index (state_467) (lift_to_both0 (usize 12))) .+ (
                lift_to_both0 ctr_470))) in
        letb k_471 : state_t := chacha20_rounds (lift_to_both0 state_467) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) ((
            lift_to_both0 k_471) array_add (lift_to_both0 state_467))
        ) : both (CEfset ([state_467_loc])) [interface
      #val #[ CHACHA20_ROUNDS ] : chacha20_rounds_inp → chacha20_rounds_out
      ] (state_t)))in
  both_package' _ _ (CHACHA20_CORE,(
      chacha20_core_inp,chacha20_core_out)) temp_package_both.
Fail Next Obligation.

Definition constants_473_loc : ChoiceEqualityLocation :=
  (constants_t ; 474%nat).
Notation "'chacha20_constants_init_inp'" :=(
  unit_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'chacha20_constants_init_inp'" :=(
  unit_ChoiceEquality : ChoiceEquality) (at level 2).
Notation "'chacha20_constants_init_out'" :=(
  constants_t : choice_type) (in custom pack_type at level 2).
Notation "'chacha20_constants_init_out'" :=(
  constants_t : ChoiceEquality) (at level 2).
Definition CHACHA20_CONSTANTS_INIT : nat :=
  475.
Program Definition chacha20_constants_init
  : both_package (CEfset ([constants_473_loc])) [interface] [(
    CHACHA20_CONSTANTS_INIT,(
      chacha20_constants_init_inp,chacha20_constants_init_out))] :=
  let temp_package_both := (fun temp_inp => 
    
    ((letbm constants_473 : constants_t loc( constants_473_loc ) :=
          array_new_ (default : uint32) (4) in
        letb constants_473 : constants_t :=
          array_upd constants_473 (lift_to_both0 (usize 0)) (is_pure (secret (
                lift_to_both0 (@repr U32 1634760805)))) in
        letb constants_473 : constants_t :=
          array_upd constants_473 (lift_to_both0 (usize 1)) (is_pure (secret (
                lift_to_both0 (@repr U32 857760878)))) in
        letb constants_473 : constants_t :=
          array_upd constants_473 (lift_to_both0 (usize 2)) (is_pure (secret (
                lift_to_both0 (@repr U32 2036477234)))) in
        letb constants_473 : constants_t :=
          array_upd constants_473 (lift_to_both0 (usize 3)) (is_pure (secret (
                lift_to_both0 (@repr U32 1797285236)))) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          lift_to_both0 constants_473)
        ) : both (CEfset ([constants_473_loc])) [interface] (constants_t)))in
  both_package' _ _ (CHACHA20_CONSTANTS_INIT,(
      chacha20_constants_init_inp,chacha20_constants_init_out)) temp_package_both.
Fail Next Obligation.

Definition st_476_loc : ChoiceEqualityLocation :=
  (state_t ; 477%nat).
Notation "'chacha20_init_inp'" :=(
  cha_cha_key_t '× cha_cha_iv_t '× uint32 : choice_type) (in custom pack_type at level 2).
Notation "'chacha20_init_inp'" :=(
  cha_cha_key_t '× cha_cha_iv_t '× uint32 : ChoiceEquality) (at level 2).
Notation "'chacha20_init_out'" :=(
  state_t : choice_type) (in custom pack_type at level 2).
Notation "'chacha20_init_out'" :=(state_t : ChoiceEquality) (at level 2).
Definition CHACHA20_INIT : nat :=
  481.
Program Definition chacha20_init
  : both_package (CEfset ([st_476_loc])) [interface
  #val #[ CHACHA20_CONSTANTS_INIT ] : chacha20_constants_init_inp → chacha20_constants_init_out
  ] [(CHACHA20_INIT,(chacha20_init_inp,chacha20_init_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(
      key_478 , iv_480 , ctr_479) := temp_inp : cha_cha_key_t '× cha_cha_iv_t '× uint32 in
    
    let chacha20_constants_init := package_both chacha20_constants_init tt in
    ((letbm st_476 : state_t loc( st_476_loc ) :=
          array_new_ (default : uint32) (16) in
        letbm st_476 loc( st_476_loc ) :=
          array_update (lift_to_both0 st_476) (lift_to_both0 (usize 0)) (
            array_to_seq (chacha20_constants_init )) in
        letbm st_476 loc( st_476_loc ) :=
          array_update (lift_to_both0 st_476) (lift_to_both0 (usize 4)) (
            array_to_le_uint32s (lift_to_both0 key_478)) in
        letb st_476 : state_t :=
          array_upd st_476 (lift_to_both0 (usize 12)) (is_pure (
              lift_to_both0 ctr_479)) in
        letbm st_476 loc( st_476_loc ) :=
          array_update (lift_to_both0 st_476) (lift_to_both0 (usize 13)) (
            array_to_le_uint32s (lift_to_both0 iv_480)) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 st_476)
        ) : both (CEfset ([st_476_loc])) [interface
      #val #[ CHACHA20_CONSTANTS_INIT ] : chacha20_constants_init_inp → chacha20_constants_init_out
      ] (state_t)))in
  both_package' _ _ (CHACHA20_INIT,(
      chacha20_init_inp,chacha20_init_out)) temp_package_both.
Fail Next Obligation.


Notation "'chacha20_key_block_inp'" :=(
  state_t : choice_type) (in custom pack_type at level 2).
Notation "'chacha20_key_block_inp'" :=(state_t : ChoiceEquality) (at level 2).
Notation "'chacha20_key_block_out'" :=(
  block_t : choice_type) (in custom pack_type at level 2).
Notation "'chacha20_key_block_out'" :=(block_t : ChoiceEquality) (at level 2).
Definition CHACHA20_KEY_BLOCK : nat :=
  484.
Program Definition chacha20_key_block
  : both_package (CEfset ([])) [interface
  #val #[ CHACHA20_CORE ] : chacha20_core_inp → chacha20_core_out ] [(
    CHACHA20_KEY_BLOCK,(chacha20_key_block_inp,chacha20_key_block_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(state_482) := temp_inp : state_t in
    
    let chacha20_core := fun x_0 x_1 => package_both chacha20_core (x_0,x_1) in
    ((letb state_483 : state_t :=
          chacha20_core (secret (lift_to_both0 (@repr U32 0))) (
            lift_to_both0 state_482) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (array_from_seq (64) (
            array_to_le_bytes (lift_to_both0 state_483)))
        ) : both (CEfset ([])) [interface
      #val #[ CHACHA20_CORE ] : chacha20_core_inp → chacha20_core_out ] (
        block_t)))in
  both_package' _ _ (CHACHA20_KEY_BLOCK,(
      chacha20_key_block_inp,chacha20_key_block_out)) temp_package_both.
Fail Next Obligation.


Notation "'chacha20_key_block0_inp'" :=(
  cha_cha_key_t '× cha_cha_iv_t : choice_type) (in custom pack_type at level 2).
Notation "'chacha20_key_block0_inp'" :=(
  cha_cha_key_t '× cha_cha_iv_t : ChoiceEquality) (at level 2).
Notation "'chacha20_key_block0_out'" :=(
  block_t : choice_type) (in custom pack_type at level 2).
Notation "'chacha20_key_block0_out'" :=(block_t : ChoiceEquality) (at level 2).
Definition CHACHA20_KEY_BLOCK0 : nat :=
  488.
Program Definition chacha20_key_block0
  : both_package (CEfset ([])) [interface
  #val #[ CHACHA20_INIT ] : chacha20_init_inp → chacha20_init_out ;
  #val #[ CHACHA20_KEY_BLOCK ] : chacha20_key_block_inp → chacha20_key_block_out
  ] [(CHACHA20_KEY_BLOCK0,(chacha20_key_block0_inp,chacha20_key_block0_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(key_485 , iv_486) := temp_inp : cha_cha_key_t '× cha_cha_iv_t in
    
    let chacha20_init := fun x_0 x_1 x_2 => package_both chacha20_init (
      x_0,x_1,x_2) in
    let chacha20_key_block := fun x_0 => package_both chacha20_key_block (
      x_0) in
    ((letb state_487 : state_t :=
          chacha20_init (lift_to_both0 key_485) (lift_to_both0 iv_486) (secret (
              lift_to_both0 (@repr U32 0))) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (chacha20_key_block (
            lift_to_both0 state_487))
        ) : both (CEfset ([])) [interface
      #val #[ CHACHA20_INIT ] : chacha20_init_inp → chacha20_init_out ;
      #val #[ CHACHA20_KEY_BLOCK ] : chacha20_key_block_inp → chacha20_key_block_out
      ] (block_t)))in
  both_package' _ _ (CHACHA20_KEY_BLOCK0,(
      chacha20_key_block0_inp,chacha20_key_block0_out)) temp_package_both.
Fail Next Obligation.


Notation "'chacha20_encrypt_block_inp'" :=(
  state_t '× uint32 '× block_t : choice_type) (in custom pack_type at level 2).
Notation "'chacha20_encrypt_block_inp'" :=(
  state_t '× uint32 '× block_t : ChoiceEquality) (at level 2).
Notation "'chacha20_encrypt_block_out'" :=(
  block_t : choice_type) (in custom pack_type at level 2).
Notation "'chacha20_encrypt_block_out'" :=(
  block_t : ChoiceEquality) (at level 2).
Definition CHACHA20_ENCRYPT_BLOCK : nat :=
  495.
Program Definition chacha20_encrypt_block
  : both_package (CEfset ([])) [interface
  #val #[ CHACHA20_CORE ] : chacha20_core_inp → chacha20_core_out ] [(
    CHACHA20_ENCRYPT_BLOCK,(
      chacha20_encrypt_block_inp,chacha20_encrypt_block_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(
      st0_490 , ctr_489 , plain_492) := temp_inp : state_t '× uint32 '× block_t in
    
    let chacha20_core := fun x_0 x_1 => package_both chacha20_core (x_0,x_1) in
    ((letb st_491 : state_t :=
          chacha20_core (lift_to_both0 ctr_489) (lift_to_both0 st0_490) in
        letb pl_493 : state_t :=
          array_from_seq (16) (array_to_le_uint32s (lift_to_both0 plain_492)) in
        letb st_494 : state_t :=
          (lift_to_both0 pl_493) array_xor (lift_to_both0 st_491) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (array_from_seq (64) (
            array_to_le_bytes (lift_to_both0 st_494)))
        ) : both (CEfset ([])) [interface
      #val #[ CHACHA20_CORE ] : chacha20_core_inp → chacha20_core_out ] (
        block_t)))in
  both_package' _ _ (CHACHA20_ENCRYPT_BLOCK,(
      chacha20_encrypt_block_inp,chacha20_encrypt_block_out)) temp_package_both.
Fail Next Obligation.

Definition b_496_loc : ChoiceEqualityLocation :=
  (block_t ; 497%nat).
Notation "'chacha20_encrypt_last_inp'" :=(
  state_t '× uint32 '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'chacha20_encrypt_last_inp'" :=(
  state_t '× uint32 '× byte_seq : ChoiceEquality) (at level 2).
Notation "'chacha20_encrypt_last_out'" :=(
  byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'chacha20_encrypt_last_out'" :=(
  byte_seq : ChoiceEquality) (at level 2).
Definition CHACHA20_ENCRYPT_LAST : nat :=
  501.
Program Definition chacha20_encrypt_last
  : both_package (CEfset ([b_496_loc])) [interface
  #val #[ CHACHA20_ENCRYPT_BLOCK ] : chacha20_encrypt_block_inp → chacha20_encrypt_block_out
  ] [(CHACHA20_ENCRYPT_LAST,(
      chacha20_encrypt_last_inp,chacha20_encrypt_last_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(
      st0_499 , ctr_500 , plain_498) := temp_inp : state_t '× uint32 '× byte_seq in
    
    let chacha20_encrypt_block := fun x_0 x_1 x_2 => package_both chacha20_encrypt_block (
      x_0,x_1,x_2) in
    ((letbm b_496 : block_t loc( b_496_loc ) :=
          array_new_ (default : uint8) (64) in
        letbm b_496 loc( b_496_loc ) :=
          array_update (lift_to_both0 b_496) (lift_to_both0 (usize 0)) (
            lift_to_both0 plain_498) in
        letbm b_496 loc( b_496_loc ) :=
          chacha20_encrypt_block (lift_to_both0 st0_499) (
            lift_to_both0 ctr_500) (lift_to_both0 b_496) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (array_slice (
            lift_to_both0 b_496) (lift_to_both0 (usize 0)) (seq_len (
              lift_to_both0 plain_498)))
        ) : both (CEfset ([b_496_loc])) [interface
      #val #[ CHACHA20_ENCRYPT_BLOCK ] : chacha20_encrypt_block_inp → chacha20_encrypt_block_out
      ] (byte_seq)))in
  both_package' _ _ (CHACHA20_ENCRYPT_LAST,(
      chacha20_encrypt_last_inp,chacha20_encrypt_last_out)) temp_package_both.
Fail Next Obligation.

Definition blocks_out_502_loc : ChoiceEqualityLocation :=
  (seq uint8 ; 503%nat).
Notation "'chacha20_update_inp'" :=(
  state_t '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'chacha20_update_inp'" :=(
  state_t '× byte_seq : ChoiceEquality) (at level 2).
Notation "'chacha20_update_out'" :=(
  byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'chacha20_update_out'" :=(byte_seq : ChoiceEquality) (at level 2).
Definition CHACHA20_UPDATE : nat :=
  512.
Program Definition chacha20_update
  : both_package (CEfset ([blocks_out_502_loc])) [interface
  #val #[ CHACHA20_ENCRYPT_BLOCK ] : chacha20_encrypt_block_inp → chacha20_encrypt_block_out ;
  #val #[ CHACHA20_ENCRYPT_LAST ] : chacha20_encrypt_last_inp → chacha20_encrypt_last_out
  ] [(CHACHA20_UPDATE,(chacha20_update_inp,chacha20_update_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(st0_508 , m_504) := temp_inp : state_t '× byte_seq in
    
    let chacha20_encrypt_block := fun x_0 x_1 x_2 => package_both chacha20_encrypt_block (
      x_0,x_1,x_2) in
    let chacha20_encrypt_last := fun x_0 x_1 x_2 => package_both chacha20_encrypt_last (
      x_0,x_1,x_2) in
    ((letbm blocks_out_502 : seq uint8 loc( blocks_out_502_loc ) :=
          seq_new_ (default : uint8) (seq_len (lift_to_both0 m_504)) in
        letb n_blocks_505 : uint_size :=
          seq_num_exact_chunks (lift_to_both0 m_504) (lift_to_both0 (
              usize 64)) in
        letb blocks_out_502 :=
          foldi_both' (lift_to_both0 (usize 0)) (
              lift_to_both0 n_blocks_505) blocks_out_502 (L := (CEfset (
                [blocks_out_502_loc]))) (I := ([interface
              #val #[ CHACHA20_ENCRYPT_BLOCK ] : chacha20_encrypt_block_inp → chacha20_encrypt_block_out ;
              #val #[ CHACHA20_ENCRYPT_LAST ] : chacha20_encrypt_last_inp → chacha20_encrypt_last_out
              ])) (fun i_506 blocks_out_502 =>
            letb msg_block_507 : seq uint8 :=
              seq_get_exact_chunk (lift_to_both0 m_504) (lift_to_both0 (
                  usize 64)) (lift_to_both0 i_506) in
            letb b_509 : block_t :=
              chacha20_encrypt_block (lift_to_both0 st0_508) (secret (pub_u32 (
                    is_pure (lift_to_both0 i_506)))) (array_from_seq (64) (
                  lift_to_both0 msg_block_507)) in
            letbm blocks_out_502 loc( blocks_out_502_loc ) :=
              seq_set_exact_chunk (lift_to_both0 blocks_out_502) (
                lift_to_both0 (usize 64)) (lift_to_both0 i_506) (
                array_to_seq (lift_to_both0 b_509)) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 blocks_out_502)
            ) in
        letb last_block_510 : seq uint8 :=
          seq_get_remainder_chunk (lift_to_both0 m_504) (lift_to_both0 (
              usize 64)) in
        letb 'blocks_out_502 :=
          if (seq_len (lift_to_both0 last_block_510)) !=.? (lift_to_both0 (
              usize 0)) :bool_ChoiceEquality
          then lift_scope (L1 := CEfset ([blocks_out_502_loc])) (L2 := CEfset (
            [blocks_out_502_loc])) (I1 := [interface
          #val #[ CHACHA20_ENCRYPT_LAST ] : chacha20_encrypt_last_inp → chacha20_encrypt_last_out
          ]) (I2 := [interface
          #val #[ CHACHA20_ENCRYPT_BLOCK ] : chacha20_encrypt_block_inp → chacha20_encrypt_block_out ;
          #val #[ CHACHA20_ENCRYPT_LAST ] : chacha20_encrypt_last_inp → chacha20_encrypt_last_out
          ]) (H_loc_incl := _) (H_opsig_incl := _) (letb b_511 : seq uint8 :=
              chacha20_encrypt_last (lift_to_both0 st0_508) (secret (pub_u32 (
                    is_pure (lift_to_both0 n_blocks_505)))) (
                lift_to_both0 last_block_510) in
            letbm blocks_out_502 loc( blocks_out_502_loc ) :=
              seq_set_chunk (lift_to_both0 blocks_out_502) (lift_to_both0 (
                  usize 64)) (lift_to_both0 n_blocks_505) (
                lift_to_both0 b_511) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 blocks_out_502)
            )
          else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 blocks_out_502)
           in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          lift_to_both0 blocks_out_502)
        ) : both (CEfset ([blocks_out_502_loc])) [interface
      #val #[ CHACHA20_ENCRYPT_BLOCK ] : chacha20_encrypt_block_inp → chacha20_encrypt_block_out ;
      #val #[ CHACHA20_ENCRYPT_LAST ] : chacha20_encrypt_last_inp → chacha20_encrypt_last_out
      ] (byte_seq)))in
  both_package' _ _ (CHACHA20_UPDATE,(
      chacha20_update_inp,chacha20_update_out)) temp_package_both.
Fail Next Obligation.


Notation "'chacha20_inp'" :=(
  cha_cha_key_t '× cha_cha_iv_t '× int32 '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'chacha20_inp'" :=(
  cha_cha_key_t '× cha_cha_iv_t '× int32 '× byte_seq : ChoiceEquality) (at level 2).
Notation "'chacha20_out'" :=(
  byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'chacha20_out'" :=(byte_seq : ChoiceEquality) (at level 2).
Definition CHACHA20 : nat :=
  518.
Program Definition chacha20
  : both_package (CEfset ([])) [interface
  #val #[ CHACHA20_INIT ] : chacha20_init_inp → chacha20_init_out ;
  #val #[ CHACHA20_UPDATE ] : chacha20_update_inp → chacha20_update_out ] [(
    CHACHA20,(chacha20_inp,chacha20_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(
      key_513 , iv_514 , ctr_515 , m_517) := temp_inp : cha_cha_key_t '× cha_cha_iv_t '× int32 '× byte_seq in
    
    let chacha20_init := fun x_0 x_1 x_2 => package_both chacha20_init (
      x_0,x_1,x_2) in
    let chacha20_update := fun x_0 x_1 => package_both chacha20_update (
      x_0,x_1) in
    ((letb state_516 : state_t :=
          chacha20_init (lift_to_both0 key_513) (lift_to_both0 iv_514) (secret (
              lift_to_both0 ctr_515)) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (chacha20_update (
            lift_to_both0 state_516) (lift_to_both0 m_517))
        ) : both (CEfset ([])) [interface
      #val #[ CHACHA20_INIT ] : chacha20_init_inp → chacha20_init_out ;
      #val #[ CHACHA20_UPDATE ] : chacha20_update_inp → chacha20_update_out
      ] (byte_seq)))in
  both_package' _ _ (CHACHA20,(chacha20_inp,chacha20_out)) temp_package_both.
Fail Next Obligation.

