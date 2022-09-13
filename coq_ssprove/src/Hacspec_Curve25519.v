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

Definition mask_scalar_pure
  (s_1483 : x25519_serialized_scalar_t)
  : x25519_serialized_scalar_t :=
  let k_1481 : x25519_serialized_scalar_t :=
    s_1483 in 
  let k_1481 :=
    array_upd k_1481 (usize 0) (((array_index (k_1481) (usize 0)) .& (secret (
            @repr U8 248)))) in 
  let k_1481 :=
    array_upd k_1481 (usize 31) (((array_index (k_1481) (usize 31)) .& (secret (
            @repr U8 127)))) in 
  let k_1481 :=
    array_upd k_1481 (usize 31) (((array_index (k_1481) (usize 31)) .| (secret (
            @repr U8 64)))) in 
  k_1481.
Definition mask_scalar_pure_code
  (s_1483 : x25519_serialized_scalar_t)
  : code fset.fset0 [interface] (@ct (x25519_serialized_scalar_t)) :=
  lift_to_code (mask_scalar_pure s_1483).

Definition k_1481_loc : ChoiceEqualityLocation :=
  ((x25519_serialized_scalar_t ; 1502%nat)).
Notation "'mask_scalar_state_inp'" := (
  x25519_serialized_scalar_t : choice_type) (in custom pack_type at level 2).
Notation "'mask_scalar_state_out'" := (
  x25519_serialized_scalar_t : choice_type) (in custom pack_type at level 2).
Definition MASK_SCALAR_STATE : nat :=
  (1503).
Program Definition mask_scalar_state
   : package (CEfset ([k_1481_loc])) [interface] [interface
  #val #[ MASK_SCALAR_STATE ] : mask_scalar_state_inp → mask_scalar_state_out
  ] :=
  (
    [package #def #[ MASK_SCALAR_STATE ] (temp_inp : mask_scalar_state_inp) : mask_scalar_state_out { 
    let '(s_1483) := temp_inp : x25519_serialized_scalar_t in
    ({ code  '(k_1481 : x25519_serialized_scalar_t) ←
          (ret (s_1483)) ;;
        #put k_1481_loc := k_1481 ;;
       '(k_1481 : x25519_serialized_scalar_t) ←
        ( temp_1485 ←
            (array_index (k_1481) (usize 0)) ;;
           '(temp_1487 : int8) ←
            (secret (@repr U8 248)) ;;
           temp_1489 ←
            ((temp_1485) .& (temp_1487)) ;;
          ret (array_upd k_1481 (usize 0) (temp_1489))) ;;
      
       '(k_1481 : x25519_serialized_scalar_t) ←
        ( temp_1491 ←
            (array_index (k_1481) (usize 31)) ;;
           '(temp_1493 : int8) ←
            (secret (@repr U8 127)) ;;
           temp_1495 ←
            ((temp_1491) .& (temp_1493)) ;;
          ret (array_upd k_1481 (usize 31) (temp_1495))) ;;
      
       '(k_1481 : x25519_serialized_scalar_t) ←
        ( temp_1497 ←
            (array_index (k_1481) (usize 31)) ;;
           '(temp_1499 : int8) ←
            (secret (@repr U8 64)) ;;
           temp_1501 ←
            ((temp_1497) .| (temp_1499)) ;;
          ret (array_upd k_1481 (usize 31) (temp_1501))) ;;
      
      @ret (x25519_serialized_scalar_t) (k_1481) } : code (CEfset (
          [k_1481_loc])) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_mask_scalar_state : package _ _ _ :=
  (mask_scalar_state).
Fail Next Obligation.

Notation "'mask_scalar_inp'" :=(
  x25519_serialized_scalar_t : choice_type) (in custom pack_type at level 2).
Notation "'mask_scalar_out'" :=(
  x25519_serialized_scalar_t : choice_type) (in custom pack_type at level 2).
Definition MASK_SCALAR : nat :=
  (1504).
Program Definition mask_scalar
  (s_1483 : x25519_serialized_scalar_t)
  :both (CEfset ([k_1481_loc])) [interface] (x25519_serialized_scalar_t) :=
  letbm k_1481 : x25519_serialized_scalar_t loc( k_1481_loc ) :=
    lift_to_both0 s_1483 in
  letb k_1481 : x25519_serialized_scalar_t :=
    array_upd k_1481 (lift_to_both0 (usize 0)) (is_pure ((array_index (k_1481) (
            lift_to_both0 (usize 0))) .& (secret (lift_to_both0 (
              @repr U8 248))))) in
  letb k_1481 : x25519_serialized_scalar_t :=
    array_upd k_1481 (lift_to_both0 (usize 31)) (is_pure ((array_index (
            k_1481) (lift_to_both0 (usize 31))) .& (secret (lift_to_both0 (
              @repr U8 127))))) in
  letb k_1481 : x25519_serialized_scalar_t :=
    array_upd k_1481 (lift_to_both0 (usize 31)) (is_pure ((array_index (
            k_1481) (lift_to_both0 (usize 31))) .| (secret (lift_to_both0 (
              @repr U8 64))))) in
  lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 k_1481)
  .
Fail Next Obligation.

Definition decode_scalar_pure
  (s_1505 : x25519_serialized_scalar_t)
  : scalar_t :=
  let k_1506 : x25519_serialized_scalar_t :=
    mask_scalar (s_1505) in 
  nat_mod_from_byte_seq_le (array_to_seq (k_1506)).
Definition decode_scalar_pure_code
  (s_1505 : x25519_serialized_scalar_t)
  : code fset.fset0 [interface] (@ct (scalar_t)) :=
  lift_to_code (decode_scalar_pure s_1505).


Notation "'decode_scalar_state_inp'" := (
  x25519_serialized_scalar_t : choice_type) (in custom pack_type at level 2).
Notation "'decode_scalar_state_out'" := (
  scalar_t : choice_type) (in custom pack_type at level 2).
Definition DECODE_SCALAR_STATE : nat :=
  (1513).
Program Definition decode_scalar_state
   : package (CEfset ([])) [interface
  #val #[ MASK_SCALAR_STATE ] : mask_scalar_state_inp → mask_scalar_state_out
  ] [interface
  #val #[ DECODE_SCALAR_STATE ] : decode_scalar_state_inp → decode_scalar_state_out
  ] :=
  (
    [package #def #[ DECODE_SCALAR_STATE ] (temp_inp : decode_scalar_state_inp) : decode_scalar_state_out { 
    let '(s_1505) := temp_inp : x25519_serialized_scalar_t in
    #import {sig #[ MASK_SCALAR_STATE ] : mask_scalar_state_inp → mask_scalar_state_out } as mask_scalar_state ;;
    let mask_scalar_state := fun x_0 => mask_scalar_state (x_0) in
    ({ code  '(k_1506 : x25519_serialized_scalar_t) ←
        ( temp_1508 ←
            (mask_scalar (s_1505)) ;;
          ret (temp_1508)) ;;
       '(temp_1510 : seq uint8) ←
        (array_to_seq (k_1506)) ;;
       '(temp_1512 : scalar_t) ←
        (nat_mod_from_byte_seq_le (temp_1510)) ;;
      @ret (scalar_t) (temp_1512) } : code (CEfset ([])) [interface
      #val #[ MASK_SCALAR_STATE ] : mask_scalar_state_inp → mask_scalar_state_out
      ] _)
    }]).
Fail Next Obligation.
Program Definition package_decode_scalar_state : package _ _ _ :=
  (seq_link decode_scalar_state link_rest(package_mask_scalar_state)).
Fail Next Obligation.

Notation "'decode_scalar_inp'" :=(
  x25519_serialized_scalar_t : choice_type) (in custom pack_type at level 2).
Notation "'decode_scalar_out'" :=(
  scalar_t : choice_type) (in custom pack_type at level 2).
Definition DECODE_SCALAR : nat :=
  (1514).
Program Definition decode_scalar
  (s_1505 : x25519_serialized_scalar_t)
  :both (CEfset ([])) [interface
  #val #[ MASK_SCALAR ] : mask_scalar_inp → mask_scalar_out ] (scalar_t) :=
  #import {sig #[ MASK_SCALAR ] : mask_scalar_inp → mask_scalar_out } as mask_scalar ;;
  let mask_scalar := fun x_0 => mask_scalar (x_0) in
  letb k_1506 : x25519_serialized_scalar_t :=
    mask_scalar (lift_to_both0 s_1505) in
  lift_scope (H_loc_incl := _) (H_opsig_incl := _) (nat_mod_from_byte_seq_le (
      array_to_seq (lift_to_both0 k_1506)))
  .
Fail Next Obligation.

Definition decode_point_pure (u_1517 : x25519_serialized_point_t) : point_t :=
  let u_1515 : x25519_serialized_point_t :=
    u_1517 in 
  let u_1515 :=
    array_upd u_1515 (usize 31) (((array_index (u_1515) (usize 31)) .& (secret (
            @repr U8 127)))) in 
  prod_ce(
    nat_mod_from_byte_seq_le (array_to_seq (u_1515)),
    nat_mod_from_literal (
      0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed) (
      @repr U128 1)
  ).
Definition decode_point_pure_code
  (u_1517 : x25519_serialized_point_t)
  : code fset.fset0 [interface] (@ct (point_t)) :=
  lift_to_code (decode_point_pure u_1517).

Definition u_1515_loc : ChoiceEqualityLocation :=
  ((x25519_serialized_point_t ; 1530%nat)).
Notation "'decode_point_state_inp'" := (
  x25519_serialized_point_t : choice_type) (in custom pack_type at level 2).
Notation "'decode_point_state_out'" := (
  point_t : choice_type) (in custom pack_type at level 2).
Definition DECODE_POINT_STATE : nat :=
  (1531).
Program Definition decode_point_state
   : package (CEfset ([u_1515_loc])) [interface] [interface
  #val #[ DECODE_POINT_STATE ] : decode_point_state_inp → decode_point_state_out
  ] :=
  (
    [package #def #[ DECODE_POINT_STATE ] (temp_inp : decode_point_state_inp) : decode_point_state_out { 
    let '(u_1517) := temp_inp : x25519_serialized_point_t in
    ({ code  '(u_1515 : x25519_serialized_point_t) ←
          (ret (u_1517)) ;;
        #put u_1515_loc := u_1515 ;;
       '(u_1515 : x25519_serialized_point_t) ←
        ( temp_1519 ←
            (array_index (u_1515) (usize 31)) ;;
           '(temp_1521 : int8) ←
            (secret (@repr U8 127)) ;;
           temp_1523 ←
            ((temp_1519) .& (temp_1521)) ;;
          ret (array_upd u_1515 (usize 31) (temp_1523))) ;;
      
       '(temp_1525 : seq uint8) ←
        (array_to_seq (u_1515)) ;;
       '(temp_1527 : x25519_field_element_t) ←
        (nat_mod_from_byte_seq_le (temp_1525)) ;;
       '(temp_1529 : x25519_field_element_t) ←
        (nat_mod_from_literal (
            0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed) (
            @repr U128 1)) ;;
      @ret ((x25519_field_element_t '× x25519_field_element_t)) (prod_ce(
          temp_1527,
          temp_1529
        )) } : code (CEfset ([u_1515_loc])) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_decode_point_state : package _ _ _ :=
  (decode_point_state).
Fail Next Obligation.

Notation "'decode_point_inp'" :=(
  x25519_serialized_point_t : choice_type) (in custom pack_type at level 2).
Notation "'decode_point_out'" :=(
  point_t : choice_type) (in custom pack_type at level 2).
Definition DECODE_POINT : nat :=
  (1532).
Program Definition decode_point
  (u_1517 : x25519_serialized_point_t)
  :both (CEfset ([u_1515_loc])) [interface] (point_t) :=
  letbm u_1515 : x25519_serialized_point_t loc( u_1515_loc ) :=
    lift_to_both0 u_1517 in
  letb u_1515 : x25519_serialized_point_t :=
    array_upd u_1515 (lift_to_both0 (usize 31)) (is_pure ((array_index (
            u_1515) (lift_to_both0 (usize 31))) .& (secret (lift_to_both0 (
              @repr U8 127))))) in
  lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
      nat_mod_from_byte_seq_le (array_to_seq (lift_to_both0 u_1515)),
      nat_mod_from_literal (
        0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed) (
        lift_to_both0 (@repr U128 1))
    ))
  .
Fail Next Obligation.

Definition encode_point_pure (p_1533 : point_t) : x25519_serialized_point_t :=
  let '(x_1534, y_1535) :=
    p_1533 : (x25519_field_element_t '× x25519_field_element_t) in 
  let b_1536 : x25519_field_element_t :=
    ((x_1534) *% (nat_mod_inv (y_1535))) in 
  array_update_start (array_new_ (default : uint8) (32)) (
    nat_mod_to_byte_seq_le (b_1536)).
Definition encode_point_pure_code
  (p_1533 : point_t)
  : code fset.fset0 [interface] (@ct (x25519_serialized_point_t)) :=
  lift_to_code (encode_point_pure p_1533).


Notation "'encode_point_state_inp'" := (
  point_t : choice_type) (in custom pack_type at level 2).
Notation "'encode_point_state_out'" := (
  x25519_serialized_point_t : choice_type) (in custom pack_type at level 2).
Definition ENCODE_POINT_STATE : nat :=
  (1549).
Program Definition encode_point_state
   : package (fset.fset0) [interface] [interface
  #val #[ ENCODE_POINT_STATE ] : encode_point_state_inp → encode_point_state_out
  ] :=
  (
    [package #def #[ ENCODE_POINT_STATE ] (temp_inp : encode_point_state_inp) : encode_point_state_out { 
    let '(p_1533) := temp_inp : point_t in
    ({ code  temp_1548 ←
        (ret (p_1533)) ;;
      let '(x_1534, y_1535) :=
        (temp_1548) : (x25519_field_element_t '× x25519_field_element_t) in
       '(b_1536 : x25519_field_element_t) ←
        ( temp_1538 ←
            (nat_mod_inv (y_1535)) ;;
           '(temp_1540 : x25519_field_element_t) ←
            ((x_1534) *% (temp_1538)) ;;
          ret (temp_1540)) ;;
       '(temp_1542 : x25519_serialized_point_t) ←
        (array_new_ (default : uint8) (32)) ;;
       temp_1544 ←
        (nat_mod_to_byte_seq_le (b_1536)) ;;
       '(temp_1546 : x25519_serialized_point_t) ←
        (array_update_start (temp_1542) (temp_1544)) ;;
      @ret (x25519_serialized_point_t) (temp_1546) } : code (
        fset.fset0) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_encode_point_state : package _ _ _ :=
  (encode_point_state).
Fail Next Obligation.

Notation "'encode_point_inp'" :=(
  point_t : choice_type) (in custom pack_type at level 2).
Notation "'encode_point_out'" :=(
  x25519_serialized_point_t : choice_type) (in custom pack_type at level 2).
Definition ENCODE_POINT : nat :=
  (1550).
Program Definition encode_point
  (p_1533 : point_t)
  :both (fset.fset0) [interface] (x25519_serialized_point_t) :=
  letb '(x_1534, y_1535) : (x25519_field_element_t '× x25519_field_element_t
    ) :=
    lift_to_both0 p_1533 in
  letb b_1536 : x25519_field_element_t :=
    (lift_to_both0 x_1534) *% (nat_mod_inv (lift_to_both0 y_1535)) in
  lift_scope (H_loc_incl := _) (H_opsig_incl := _) (array_update_start (
      array_new_ (default : uint8) (32)) (nat_mod_to_byte_seq_le (
        lift_to_both0 b_1536)))
  .
Fail Next Obligation.

Definition point_add_and_double_pure
  (q_1551 : point_t)
  (np_1552 : (point_t '× point_t))
  : (point_t '× point_t) :=
  let '(nq_1553, nqp1_1554) :=
    np_1552 : (point_t '× point_t) in 
  let '(x_1_1555, z_1_1556) :=
    q_1551 : (x25519_field_element_t '× x25519_field_element_t) in 
  let '(x_2_1557, z_2_1558) :=
    nq_1553 : (x25519_field_element_t '× x25519_field_element_t) in 
  let '(x_3_1559, z_3_1560) :=
    nqp1_1554 : (x25519_field_element_t '× x25519_field_element_t) in 
  let a_1561 : x25519_field_element_t :=
    ((x_2_1557) +% (z_2_1558)) in 
  let aa_1562 : x25519_field_element_t :=
    nat_mod_pow (a_1561) (@repr U128 2) in 
  let b_1563 : x25519_field_element_t :=
    ((x_2_1557) -% (z_2_1558)) in 
  let bb_1564 : x25519_field_element_t :=
    ((b_1563) *% (b_1563)) in 
  let e_1565 : x25519_field_element_t :=
    ((aa_1562) -% (bb_1564)) in 
  let c_1566 : x25519_field_element_t :=
    ((x_3_1559) +% (z_3_1560)) in 
  let d_1567 : x25519_field_element_t :=
    ((x_3_1559) -% (z_3_1560)) in 
  let da_1568 : x25519_field_element_t :=
    ((d_1567) *% (a_1561)) in 
  let cb_1569 : x25519_field_element_t :=
    ((c_1566) *% (b_1563)) in 
  let x_3_1570 : x25519_field_element_t :=
    nat_mod_pow (((da_1568) +% (cb_1569))) (@repr U128 2) in 
  let z_3_1571 : x25519_field_element_t :=
    ((x_1_1555) *% (nat_mod_pow (((da_1568) -% (cb_1569))) (@repr U128 2))) in 
  let x_2_1572 : x25519_field_element_t :=
    ((aa_1562) *% (bb_1564)) in 
  let e121665_1573 : x25519_field_element_t :=
    nat_mod_from_literal (
      0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed) (
      @repr U128 121665) in 
  let z_2_1574 : x25519_field_element_t :=
    ((e_1565) *% (((aa_1562) +% (((e121665_1573) *% (e_1565)))))) in 
  prod_ce(prod_ce(x_2_1572, z_2_1574), prod_ce(x_3_1570, z_3_1571)).
Definition point_add_and_double_pure_code
  (q_1551 : point_t)
  (np_1552 : (point_t '× point_t))
  : code fset.fset0 [interface] (@ct ((point_t '× point_t))) :=
  lift_to_code (point_add_and_double_pure q_1551 np_1552).


Notation "'point_add_and_double_state_inp'" := (point_t '× (point_t '× point_t
  ) : choice_type) (in custom pack_type at level 2).
Notation "'point_add_and_double_state_out'" := ((point_t '× point_t
  ) : choice_type) (in custom pack_type at level 2).
Definition POINT_ADD_AND_DOUBLE_STATE : nat :=
  (1621).
Program Definition point_add_and_double_state
   : package (fset.fset0) [interface] [interface
  #val #[ POINT_ADD_AND_DOUBLE_STATE ] : point_add_and_double_state_inp → point_add_and_double_state_out
  ] :=
  (
    [package #def #[ POINT_ADD_AND_DOUBLE_STATE ] (temp_inp : point_add_and_double_state_inp) : point_add_and_double_state_out { 
    let '(q_1551 , np_1552) := temp_inp : point_t '× (point_t '× point_t) in
    ({ code  temp_1620 ←
        (ret (np_1552)) ;;
      let '(nq_1553, nqp1_1554) :=
        (temp_1620) : (point_t '× point_t) in
       temp_1618 ←
        (ret (q_1551)) ;;
      let '(x_1_1555, z_1_1556) :=
        (temp_1618) : (x25519_field_element_t '× x25519_field_element_t) in
       temp_1616 ←
        (ret (nq_1553)) ;;
      let '(x_2_1557, z_2_1558) :=
        (temp_1616) : (x25519_field_element_t '× x25519_field_element_t) in
       temp_1614 ←
        (ret (nqp1_1554)) ;;
      let '(x_3_1559, z_3_1560) :=
        (temp_1614) : (x25519_field_element_t '× x25519_field_element_t) in
       '(a_1561 : x25519_field_element_t) ←
        ( '(temp_1576 : x25519_field_element_t) ←
            ((x_2_1557) +% (z_2_1558)) ;;
          ret (temp_1576)) ;;
       '(aa_1562 : x25519_field_element_t) ←
        ( '(temp_1578 : x25519_field_element_t) ←
            (nat_mod_pow (a_1561) (@repr U128 2)) ;;
          ret (temp_1578)) ;;
       '(b_1563 : x25519_field_element_t) ←
        ( '(temp_1580 : x25519_field_element_t) ←
            ((x_2_1557) -% (z_2_1558)) ;;
          ret (temp_1580)) ;;
       '(bb_1564 : x25519_field_element_t) ←
        ( '(temp_1582 : x25519_field_element_t) ←
            ((b_1563) *% (b_1563)) ;;
          ret (temp_1582)) ;;
       '(e_1565 : x25519_field_element_t) ←
        ( '(temp_1584 : x25519_field_element_t) ←
            ((aa_1562) -% (bb_1564)) ;;
          ret (temp_1584)) ;;
       '(c_1566 : x25519_field_element_t) ←
        ( '(temp_1586 : x25519_field_element_t) ←
            ((x_3_1559) +% (z_3_1560)) ;;
          ret (temp_1586)) ;;
       '(d_1567 : x25519_field_element_t) ←
        ( '(temp_1588 : x25519_field_element_t) ←
            ((x_3_1559) -% (z_3_1560)) ;;
          ret (temp_1588)) ;;
       '(da_1568 : x25519_field_element_t) ←
        ( '(temp_1590 : x25519_field_element_t) ←
            ((d_1567) *% (a_1561)) ;;
          ret (temp_1590)) ;;
       '(cb_1569 : x25519_field_element_t) ←
        ( '(temp_1592 : x25519_field_element_t) ←
            ((c_1566) *% (b_1563)) ;;
          ret (temp_1592)) ;;
       '(x_3_1570 : x25519_field_element_t) ←
        ( '(temp_1594 : x25519_field_element_t) ←
            ((da_1568) +% (cb_1569)) ;;
           '(temp_1596 : x25519_field_element_t) ←
            (nat_mod_pow (temp_1594) (@repr U128 2)) ;;
          ret (temp_1596)) ;;
       '(z_3_1571 : x25519_field_element_t) ←
        ( '(temp_1598 : x25519_field_element_t) ←
            ((da_1568) -% (cb_1569)) ;;
           '(temp_1600 : x25519_field_element_t) ←
            (nat_mod_pow (temp_1598) (@repr U128 2)) ;;
           '(temp_1602 : x25519_field_element_t) ←
            ((x_1_1555) *% (temp_1600)) ;;
          ret (temp_1602)) ;;
       '(x_2_1572 : x25519_field_element_t) ←
        ( '(temp_1604 : x25519_field_element_t) ←
            ((aa_1562) *% (bb_1564)) ;;
          ret (temp_1604)) ;;
       '(e121665_1573 : x25519_field_element_t) ←
        ( '(temp_1606 : x25519_field_element_t) ←
            (nat_mod_from_literal (
                0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed) (
                @repr U128 121665)) ;;
          ret (temp_1606)) ;;
       '(z_2_1574 : x25519_field_element_t) ←
        ( '(temp_1608 : x25519_field_element_t) ←
            ((e121665_1573) *% (e_1565)) ;;
           '(temp_1610 : x25519_field_element_t) ←
            ((aa_1562) +% (temp_1608)) ;;
           '(temp_1612 : x25519_field_element_t) ←
            ((e_1565) *% (temp_1610)) ;;
          ret (temp_1612)) ;;
      @ret ((
          (x25519_field_element_t '× x25519_field_element_t) '×
          (x25519_field_element_t '× x25519_field_element_t)
        )) (prod_ce(prod_ce(x_2_1572, z_2_1574), prod_ce(x_3_1570, z_3_1571)
        )) } : code (fset.fset0) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_point_add_and_double_state : package _ _ _ :=
  (point_add_and_double_state).
Fail Next Obligation.

Notation "'point_add_and_double_inp'" :=(point_t '× (point_t '× point_t
  ) : choice_type) (in custom pack_type at level 2).
Notation "'point_add_and_double_out'" :=((point_t '× point_t
  ) : choice_type) (in custom pack_type at level 2).
Definition POINT_ADD_AND_DOUBLE : nat :=
  (1622).
Program Definition point_add_and_double
  (q_1551 : point_t)
  (np_1552 : (point_t '× point_t))
  :both (fset.fset0) [interface] ((point_t '× point_t)) :=
  letb '(nq_1553, nqp1_1554) : (point_t '× point_t) := lift_to_both0 np_1552 in
  letb '(x_1_1555, z_1_1556) : (
      x25519_field_element_t '×
      x25519_field_element_t
    ) :=
    lift_to_both0 q_1551 in
  letb '(x_2_1557, z_2_1558) : (
      x25519_field_element_t '×
      x25519_field_element_t
    ) :=
    lift_to_both0 nq_1553 in
  letb '(x_3_1559, z_3_1560) : (
      x25519_field_element_t '×
      x25519_field_element_t
    ) :=
    lift_to_both0 nqp1_1554 in
  letb a_1561 : x25519_field_element_t :=
    (lift_to_both0 x_2_1557) +% (lift_to_both0 z_2_1558) in
  letb aa_1562 : x25519_field_element_t :=
    nat_mod_pow (lift_to_both0 a_1561) (lift_to_both0 (@repr U128 2)) in
  letb b_1563 : x25519_field_element_t :=
    (lift_to_both0 x_2_1557) -% (lift_to_both0 z_2_1558) in
  letb bb_1564 : x25519_field_element_t :=
    (lift_to_both0 b_1563) *% (lift_to_both0 b_1563) in
  letb e_1565 : x25519_field_element_t :=
    (lift_to_both0 aa_1562) -% (lift_to_both0 bb_1564) in
  letb c_1566 : x25519_field_element_t :=
    (lift_to_both0 x_3_1559) +% (lift_to_both0 z_3_1560) in
  letb d_1567 : x25519_field_element_t :=
    (lift_to_both0 x_3_1559) -% (lift_to_both0 z_3_1560) in
  letb da_1568 : x25519_field_element_t :=
    (lift_to_both0 d_1567) *% (lift_to_both0 a_1561) in
  letb cb_1569 : x25519_field_element_t :=
    (lift_to_both0 c_1566) *% (lift_to_both0 b_1563) in
  letb x_3_1570 : x25519_field_element_t :=
    nat_mod_pow ((lift_to_both0 da_1568) +% (lift_to_both0 cb_1569)) (
      lift_to_both0 (@repr U128 2)) in
  letb z_3_1571 : x25519_field_element_t :=
    (lift_to_both0 x_1_1555) *% (nat_mod_pow ((lift_to_both0 da_1568) -% (
          lift_to_both0 cb_1569)) (lift_to_both0 (@repr U128 2))) in
  letb x_2_1572 : x25519_field_element_t :=
    (lift_to_both0 aa_1562) *% (lift_to_both0 bb_1564) in
  letb e121665_1573 : x25519_field_element_t :=
    nat_mod_from_literal (
      0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed) (
      lift_to_both0 (@repr U128 121665)) in
  letb z_2_1574 : x25519_field_element_t :=
    (lift_to_both0 e_1565) *% ((lift_to_both0 aa_1562) +% ((
          lift_to_both0 e121665_1573) *% (lift_to_both0 e_1565))) in
  lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
      prod_b(lift_to_both0 x_2_1572, lift_to_both0 z_2_1574),
      prod_b(lift_to_both0 x_3_1570, lift_to_both0 z_3_1571)
    ))
  .
Fail Next Obligation.

Definition swap_pure (x_1623 : (point_t '× point_t)) : (point_t '× point_t) :=
  let '(x0_1624, x1_1625) :=
    x_1623 : (point_t '× point_t) in 
  prod_ce(x1_1625, x0_1624).
Definition swap_pure_code
  (x_1623 : (point_t '× point_t))
  : code fset.fset0 [interface] (@ct ((point_t '× point_t))) :=
  lift_to_code (swap_pure x_1623).


Notation "'swap_state_inp'" := ((point_t '× point_t
  ) : choice_type) (in custom pack_type at level 2).
Notation "'swap_state_out'" := ((point_t '× point_t
  ) : choice_type) (in custom pack_type at level 2).
Definition SWAP_STATE : nat :=
  (1628).
Program Definition swap_state
   : package (fset.fset0) [interface] [interface
  #val #[ SWAP_STATE ] : swap_state_inp → swap_state_out ] :=
  ([package #def #[ SWAP_STATE ] (temp_inp : swap_state_inp) : swap_state_out { 
    let '(x_1623) := temp_inp : (point_t '× point_t) in
    ({ code  temp_1627 ←
        (ret (x_1623)) ;;
      let '(x0_1624, x1_1625) :=
        (temp_1627) : (point_t '× point_t) in
      @ret ((
          (x25519_field_element_t '× x25519_field_element_t) '×
          (x25519_field_element_t '× x25519_field_element_t)
        )) (prod_ce(x1_1625, x0_1624)) } : code (fset.fset0) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_swap_state : package _ _ _ :=
  (swap_state).
Fail Next Obligation.

Notation "'swap_inp'" :=((point_t '× point_t
  ) : choice_type) (in custom pack_type at level 2).
Notation "'swap_out'" :=((point_t '× point_t
  ) : choice_type) (in custom pack_type at level 2).
Definition SWAP : nat :=
  (1629).
Program Definition swap
  (x_1623 : (point_t '× point_t))
  :both (fset.fset0) [interface] ((point_t '× point_t)) :=
  letb '(x0_1624, x1_1625) : (point_t '× point_t) := lift_to_both0 x_1623 in
  lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
      lift_to_both0 x1_1625,
      lift_to_both0 x0_1624
    ))
  .
Fail Next Obligation.

Definition montgomery_ladder_pure
  (k_1632 : scalar_t)
  (init_1633 : point_t)
  : point_t :=
  let inf_1634 : (x25519_field_element_t '× x25519_field_element_t) :=
    prod_ce(
      nat_mod_from_literal (
        0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed) (
        @repr U128 1),
      nat_mod_from_literal (
        0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed) (
        @repr U128 0)
    ) in 
  let acc_1630 : (point_t '× point_t) :=
    prod_ce(inf_1634, init_1633) in 
  let acc_1630 :=
    Hacspec_Lib_Pre.foldi (usize 0) (usize 256) acc_1630
      (fun i_1635 acc_1630 =>
      let '(acc_1630) :=
        ((if (nat_mod_bit (k_1632) (((usize 255) .- (
                    i_1635)))):bool_ChoiceEquality
            then (let acc_1630 :=
                swap (acc_1630) in 
              let acc_1630 :=
                point_add_and_double (init_1633) (acc_1630) in 
              let acc_1630 :=
                swap (acc_1630) in 
              (acc_1630))
            else (let acc_1630 :=
                point_add_and_double (init_1633) (acc_1630) in 
              (acc_1630))) : T _) in 
      (acc_1630)) in 
  let '(out_1636, _) :=
    acc_1630 : ((x25519_field_element_t '× x25519_field_element_t) '× point_t
    ) in 
  out_1636.
Definition montgomery_ladder_pure_code
  (k_1632 : scalar_t)
  (init_1633 : point_t)
  : code fset.fset0 [interface] (@ct (point_t)) :=
  lift_to_code (montgomery_ladder_pure k_1632 init_1633).

Definition acc_1630_loc : ChoiceEqualityLocation :=
  (((point_t '× point_t) ; 1655%nat)).
Notation "'montgomery_ladder_state_inp'" := (
  scalar_t '× point_t : choice_type) (in custom pack_type at level 2).
Notation "'montgomery_ladder_state_out'" := (
  point_t : choice_type) (in custom pack_type at level 2).
Definition MONTGOMERY_LADDER_STATE : nat :=
  (1656).
Program Definition montgomery_ladder_state
   : package (CEfset ([acc_1630_loc])) [interface
  #val #[ POINT_ADD_AND_DOUBLE_STATE ] : point_add_and_double_state_inp → point_add_and_double_state_out ;
  #val #[ SWAP_STATE ] : swap_state_inp → swap_state_out ] [interface
  #val #[ MONTGOMERY_LADDER_STATE ] : montgomery_ladder_state_inp → montgomery_ladder_state_out
  ] :=
  (
    [package #def #[ MONTGOMERY_LADDER_STATE ] (temp_inp : montgomery_ladder_state_inp) : montgomery_ladder_state_out { 
    let '(k_1632 , init_1633) := temp_inp : scalar_t '× point_t in
    #import {sig #[ POINT_ADD_AND_DOUBLE_STATE ] : point_add_and_double_state_inp → point_add_and_double_state_out } as point_add_and_double_state ;;
    let point_add_and_double_state := fun x_0 x_1 => point_add_and_double_state (
      x_0,x_1) in
    #import {sig #[ SWAP_STATE ] : swap_state_inp → swap_state_out } as swap_state ;;
    let swap_state := fun x_0 => swap_state (x_0) in
    ({ code  '(inf_1634 : (x25519_field_element_t '× x25519_field_element_t
          )) ←
        ( '(temp_1638 : x25519_field_element_t) ←
            (nat_mod_from_literal (
                0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed) (
                @repr U128 1)) ;;
           '(temp_1640 : x25519_field_element_t) ←
            (nat_mod_from_literal (
                0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed) (
                @repr U128 0)) ;;
          ret (prod_ce(temp_1638, temp_1640))) ;;
       '(acc_1630 : (point_t '× point_t)) ←
          (ret (prod_ce(inf_1634, init_1633))) ;;
        #put acc_1630_loc := acc_1630 ;;
       '(acc_1630 : (
            ((x25519_field_element_t '× x25519_field_element_t) '× point_t)
          )) ←
        (foldi' (usize 0) (usize 256) acc_1630 (L2 := CEfset ([acc_1630_loc])) (
              I2 := [interface
              #val #[ POINT_ADD_AND_DOUBLE_STATE ] : point_add_and_double_state_inp → point_add_and_double_state_out ;
              #val #[ SWAP_STATE ] : swap_state_inp → swap_state_out
              ]) (H_loc_incl := _) (H_opsig_incl := _) (fun i_1635 acc_1630 =>
            ({ code  '(temp_1642 : uint_size) ←
                ((usize 255) .- (i_1635)) ;;
               temp_1644 ←
                (nat_mod_bit (k_1632) (temp_1642)) ;;
               '(acc_1630 : (
                    (
                      (x25519_field_element_t '× x25519_field_element_t) '×
                      point_t
                    )
                  )) ←
                (if temp_1644:bool_ChoiceEquality
                  then (*not state*) (let temp_then :=  '(acc_1630 : (
                            (x25519_field_element_t '× x25519_field_element_t
                            ) '×
                            point_t
                          )) ←
                        (( temp_1646 ←
                              (swap (acc_1630)) ;;
                            ret (temp_1646))) ;;
                      #put acc_1630_loc := acc_1630 ;;
                    
                     '(acc_1630 : (
                            (x25519_field_element_t '× x25519_field_element_t
                            ) '×
                            point_t
                          )) ←
                        (( temp_1648 ←
                              (point_add_and_double (init_1633) (acc_1630)) ;;
                            ret (temp_1648))) ;;
                      #put acc_1630_loc := acc_1630 ;;
                    
                     '(acc_1630 : (
                            (x25519_field_element_t '× x25519_field_element_t
                            ) '×
                            point_t
                          )) ←
                        (( temp_1650 ←
                              (swap (acc_1630)) ;;
                            ret (temp_1650))) ;;
                      #put acc_1630_loc := acc_1630 ;;
                    
                    @ret ((
                        (
                          (x25519_field_element_t '× x25519_field_element_t
                          ) '×
                          point_t
                        )
                      )) (acc_1630) in
                    ({ code temp_then } : code (CEfset (
                          [acc_1630_loc])) [interface] _))
                  else  (({ code  '(acc_1630 : (
                              (x25519_field_element_t '× x25519_field_element_t
                              ) '×
                              point_t
                            )) ←
                          (( temp_1652 ←
                                (point_add_and_double (init_1633) (acc_1630)) ;;
                              ret (temp_1652))) ;;
                        #put acc_1630_loc := acc_1630 ;;
                      
                      @ret ((
                          (
                            (x25519_field_element_t '× x25519_field_element_t
                            ) '×
                            point_t
                          )
                        )) (acc_1630) } : code (CEfset (
                          [acc_1630_loc])) [interface] _))) ;;
              
              @ret ((
                  (
                    (x25519_field_element_t '× x25519_field_element_t) '×
                    point_t
                  )
                )) (acc_1630) } : code (CEfset (
                  [acc_1630_loc])) [interface] _))) ;;
      
       temp_1654 ←
        (ret (acc_1630)) ;;
      let '(out_1636, _) :=
        (temp_1654) : (
        (x25519_field_element_t '× x25519_field_element_t) '×
        point_t
      ) in
      @ret ((x25519_field_element_t '× x25519_field_element_t)) (
        out_1636) } : code (CEfset ([acc_1630_loc])) [interface
      #val #[ POINT_ADD_AND_DOUBLE_STATE ] : point_add_and_double_state_inp → point_add_and_double_state_out ;
      #val #[ SWAP_STATE ] : swap_state_inp → swap_state_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_montgomery_ladder_state : package _ _ _ :=
  (seq_link montgomery_ladder_state link_rest(
      package_point_add_and_double_state,package_swap_state)).
Fail Next Obligation.

Notation "'montgomery_ladder_inp'" :=(
  scalar_t '× point_t : choice_type) (in custom pack_type at level 2).
Notation "'montgomery_ladder_out'" :=(
  point_t : choice_type) (in custom pack_type at level 2).
Definition MONTGOMERY_LADDER : nat :=
  (1657).
Program Definition montgomery_ladder
  (k_1632 : scalar_t)
  (init_1633 : point_t)
  :both (CEfset ([acc_1630_loc])) [interface
  #val #[ POINT_ADD_AND_DOUBLE ] : point_add_and_double_inp → point_add_and_double_out ;
  #val #[ SWAP ] : swap_inp → swap_out ] (point_t) :=
  #import {sig #[ POINT_ADD_AND_DOUBLE ] : point_add_and_double_inp → point_add_and_double_out } as point_add_and_double ;;
  let point_add_and_double := fun x_0 x_1 => point_add_and_double (x_0,x_1) in
  #import {sig #[ SWAP ] : swap_inp → swap_out } as swap ;;
  let swap := fun x_0 => swap (x_0) in
  letb inf_1634 : (x25519_field_element_t '× x25519_field_element_t) :=
    prod_b(
      nat_mod_from_literal (
        0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed) (
        lift_to_both0 (@repr U128 1)),
      nat_mod_from_literal (
        0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed) (
        lift_to_both0 (@repr U128 0))
    ) in
  letbm acc_1630 : (point_t '× point_t) loc( acc_1630_loc ) :=
    prod_b(lift_to_both0 inf_1634, lift_to_both0 init_1633) in
  letb acc_1630 :=
    foldi_both' (lift_to_both0 (usize 0)) (lift_to_both0 (
          usize 256)) acc_1630 (L := (CEfset ([acc_1630_loc]))) (I := (
        [interface
        #val #[ POINT_ADD_AND_DOUBLE ] : point_add_and_double_inp → point_add_and_double_out ;
        #val #[ SWAP ] : swap_inp → swap_out ])) (fun i_1635 acc_1630 =>
      letb 'acc_1630 :=
        if nat_mod_bit (lift_to_both0 k_1632) ((lift_to_both0 (usize 255)) .- (
            lift_to_both0 i_1635)) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset ([acc_1630_loc])) (L2 := CEfset (
          [acc_1630_loc])) (H_loc_incl := _) (H_opsig_incl := _)a (
          letbm acc_1630 loc( acc_1630_loc ) := swap (lift_to_both0 acc_1630) in
          letbm acc_1630 loc( acc_1630_loc ) :=
            point_add_and_double (lift_to_both0 init_1633) (
              lift_to_both0 acc_1630) in
          letbm acc_1630 loc( acc_1630_loc ) := swap (lift_to_both0 acc_1630) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 acc_1630)
          )
        else  lift_scope (L1 := CEfset ([acc_1630_loc])) (L2 := CEfset (
          [acc_1630_loc])) (H_loc_incl := _) (H_opsig_incl := _) (
          letbm acc_1630 loc( acc_1630_loc ) :=
            point_add_and_double (lift_to_both0 init_1633) (
              lift_to_both0 acc_1630) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 acc_1630)
          ) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 acc_1630)
      ) in
  letb '(out_1636, _) : (
      (x25519_field_element_t '× x25519_field_element_t) '×
      point_t
    ) :=
    lift_to_both0 acc_1630 in
  lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 out_1636)
  .
Fail Next Obligation.

Definition x25519_scalarmult_pure
  (s_1658 : x25519_serialized_scalar_t)
  (p_1659 : x25519_serialized_point_t)
  : x25519_serialized_point_t :=
  let s_1660 : scalar_t :=
    decode_scalar (s_1658) in 
  let p_1661 : (x25519_field_element_t '× x25519_field_element_t) :=
    decode_point (p_1659) in 
  let r_1662 : (x25519_field_element_t '× x25519_field_element_t) :=
    montgomery_ladder (s_1660) (p_1661) in 
  encode_point (r_1662).
Definition x25519_scalarmult_pure_code
  (s_1658 : x25519_serialized_scalar_t)
  (p_1659 : x25519_serialized_point_t)
  : code fset.fset0 [interface] (@ct (x25519_serialized_point_t)) :=
  lift_to_code (x25519_scalarmult_pure s_1658 p_1659).


Notation "'x25519_scalarmult_state_inp'" := (
  x25519_serialized_scalar_t '× x25519_serialized_point_t : choice_type) (in custom pack_type at level 2).
Notation "'x25519_scalarmult_state_out'" := (
  x25519_serialized_point_t : choice_type) (in custom pack_type at level 2).
Definition X25519_SCALARMULT_STATE : nat :=
  (1671).
Program Definition x25519_scalarmult_state
   : package (CEfset ([])) [interface
  #val #[ DECODE_POINT_STATE ] : decode_point_state_inp → decode_point_state_out ;
  #val #[ DECODE_SCALAR_STATE ] : decode_scalar_state_inp → decode_scalar_state_out ;
  #val #[ ENCODE_POINT_STATE ] : encode_point_state_inp → encode_point_state_out ;
  #val #[ MONTGOMERY_LADDER_STATE ] : montgomery_ladder_state_inp → montgomery_ladder_state_out
  ] [interface
  #val #[ X25519_SCALARMULT_STATE ] : x25519_scalarmult_state_inp → x25519_scalarmult_state_out
  ] :=
  (
    [package #def #[ X25519_SCALARMULT_STATE ] (temp_inp : x25519_scalarmult_state_inp) : x25519_scalarmult_state_out { 
    let '(
      s_1658 , p_1659) := temp_inp : x25519_serialized_scalar_t '× x25519_serialized_point_t in
    #import {sig #[ DECODE_POINT_STATE ] : decode_point_state_inp → decode_point_state_out } as decode_point_state ;;
    let decode_point_state := fun x_0 => decode_point_state (x_0) in
    #import {sig #[ DECODE_SCALAR_STATE ] : decode_scalar_state_inp → decode_scalar_state_out } as decode_scalar_state ;;
    let decode_scalar_state := fun x_0 => decode_scalar_state (x_0) in
    #import {sig #[ ENCODE_POINT_STATE ] : encode_point_state_inp → encode_point_state_out } as encode_point_state ;;
    let encode_point_state := fun x_0 => encode_point_state (x_0) in
    #import {sig #[ MONTGOMERY_LADDER_STATE ] : montgomery_ladder_state_inp → montgomery_ladder_state_out } as montgomery_ladder_state ;;
    let montgomery_ladder_state := fun x_0 x_1 => montgomery_ladder_state (
      x_0,x_1) in
    ({ code  '(s_1660 : scalar_t) ←
        ( temp_1664 ←
            (decode_scalar (s_1658)) ;;
          ret (temp_1664)) ;;
       '(p_1661 : (x25519_field_element_t '× x25519_field_element_t)) ←
        ( temp_1666 ←
            (decode_point (p_1659)) ;;
          ret (temp_1666)) ;;
       '(r_1662 : (x25519_field_element_t '× x25519_field_element_t)) ←
        ( temp_1668 ←
            (montgomery_ladder (s_1660) (p_1661)) ;;
          ret (temp_1668)) ;;
       temp_1670 ←
        (encode_point (r_1662)) ;;
      @ret (x25519_serialized_point_t) (temp_1670) } : code (CEfset (
          [])) [interface
      #val #[ DECODE_POINT_STATE ] : decode_point_state_inp → decode_point_state_out ;
      #val #[ DECODE_SCALAR_STATE ] : decode_scalar_state_inp → decode_scalar_state_out ;
      #val #[ ENCODE_POINT_STATE ] : encode_point_state_inp → encode_point_state_out ;
      #val #[ MONTGOMERY_LADDER_STATE ] : montgomery_ladder_state_inp → montgomery_ladder_state_out
      ] _)
    }]).
Fail Next Obligation.
Program Definition package_x25519_scalarmult_state : package _ _ _ :=
  (seq_link x25519_scalarmult_state link_rest(
      package_decode_point_state,package_decode_scalar_state,package_encode_point_state,package_montgomery_ladder_state)).
Fail Next Obligation.

Notation "'x25519_scalarmult_inp'" :=(
  x25519_serialized_scalar_t '× x25519_serialized_point_t : choice_type) (in custom pack_type at level 2).
Notation "'x25519_scalarmult_out'" :=(
  x25519_serialized_point_t : choice_type) (in custom pack_type at level 2).
Definition X25519_SCALARMULT : nat :=
  (1672).
Program Definition x25519_scalarmult
  (s_1658 : x25519_serialized_scalar_t)
  (p_1659 : x25519_serialized_point_t)
  :both (CEfset ([])) [interface
  #val #[ DECODE_POINT ] : decode_point_inp → decode_point_out ;
  #val #[ DECODE_SCALAR ] : decode_scalar_inp → decode_scalar_out ;
  #val #[ ENCODE_POINT ] : encode_point_inp → encode_point_out ;
  #val #[ MONTGOMERY_LADDER ] : montgomery_ladder_inp → montgomery_ladder_out
  ] (x25519_serialized_point_t) :=
  #import {sig #[ DECODE_POINT ] : decode_point_inp → decode_point_out } as decode_point ;;
  let decode_point := fun x_0 => decode_point (x_0) in
  #import {sig #[ DECODE_SCALAR ] : decode_scalar_inp → decode_scalar_out } as decode_scalar ;;
  let decode_scalar := fun x_0 => decode_scalar (x_0) in
  #import {sig #[ ENCODE_POINT ] : encode_point_inp → encode_point_out } as encode_point ;;
  let encode_point := fun x_0 => encode_point (x_0) in
  #import {sig #[ MONTGOMERY_LADDER ] : montgomery_ladder_inp → montgomery_ladder_out } as montgomery_ladder ;;
  let montgomery_ladder := fun x_0 x_1 => montgomery_ladder (x_0,x_1) in
  letb s_1660 : scalar_t := decode_scalar (lift_to_both0 s_1658) in
  letb p_1661 : (x25519_field_element_t '× x25519_field_element_t) :=
    decode_point (lift_to_both0 p_1659) in
  letb r_1662 : (x25519_field_element_t '× x25519_field_element_t) :=
    montgomery_ladder (lift_to_both0 s_1660) (lift_to_both0 p_1661) in
  lift_scope (H_loc_incl := _) (H_opsig_incl := _) (encode_point (
      lift_to_both0 r_1662))
  .
Fail Next Obligation.

Definition x25519_secret_to_public_pure
  (s_1675 : x25519_serialized_scalar_t)
  : x25519_serialized_point_t :=
  let base_1673 : x25519_serialized_point_t :=
    array_new_ (default : uint8) (32) in 
  let base_1673 :=
    array_upd base_1673 (usize 0) (secret (@repr U8 9)) in 
  x25519_scalarmult (s_1675) (base_1673).
Definition x25519_secret_to_public_pure_code
  (s_1675 : x25519_serialized_scalar_t)
  : code fset.fset0 [interface] (@ct (x25519_serialized_point_t)) :=
  lift_to_code (x25519_secret_to_public_pure s_1675).

Definition base_1673_loc : ChoiceEqualityLocation :=
  ((x25519_serialized_point_t ; 1682%nat)).
Notation "'x25519_secret_to_public_state_inp'" := (
  x25519_serialized_scalar_t : choice_type) (in custom pack_type at level 2).
Notation "'x25519_secret_to_public_state_out'" := (
  x25519_serialized_point_t : choice_type) (in custom pack_type at level 2).
Definition X25519_SECRET_TO_PUBLIC_STATE : nat :=
  (1683).
Program Definition x25519_secret_to_public_state
   : package (CEfset ([base_1673_loc])) [interface
  #val #[ X25519_SCALARMULT_STATE ] : x25519_scalarmult_state_inp → x25519_scalarmult_state_out
  ] [interface
  #val #[ X25519_SECRET_TO_PUBLIC_STATE ] : x25519_secret_to_public_state_inp → x25519_secret_to_public_state_out
  ] :=
  (
    [package #def #[ X25519_SECRET_TO_PUBLIC_STATE ] (temp_inp : x25519_secret_to_public_state_inp) : x25519_secret_to_public_state_out { 
    let '(s_1675) := temp_inp : x25519_serialized_scalar_t in
    #import {sig #[ X25519_SCALARMULT_STATE ] : x25519_scalarmult_state_inp → x25519_scalarmult_state_out } as x25519_scalarmult_state ;;
    let x25519_scalarmult_state := fun x_0 x_1 => x25519_scalarmult_state (
      x_0,x_1) in
    ({ code  '(base_1673 : x25519_serialized_point_t) ←
          ( '(temp_1677 : x25519_serialized_point_t) ←
              (array_new_ (default : uint8) (32)) ;;
            ret (temp_1677)) ;;
        #put base_1673_loc := base_1673 ;;
       '(base_1673 : x25519_serialized_point_t) ←
        ( '(temp_1679 : int8) ←
            (secret (@repr U8 9)) ;;
          ret (array_upd base_1673 (usize 0) (temp_1679))) ;;
      
       temp_1681 ←
        (x25519_scalarmult (s_1675) (base_1673)) ;;
      @ret (x25519_serialized_point_t) (temp_1681) } : code (CEfset (
          [base_1673_loc])) [interface
      #val #[ X25519_SCALARMULT_STATE ] : x25519_scalarmult_state_inp → x25519_scalarmult_state_out
      ] _)
    }]).
Fail Next Obligation.
Program Definition package_x25519_secret_to_public_state : package _ _ _ :=
  (seq_link x25519_secret_to_public_state link_rest(
      package_x25519_scalarmult_state)).
Fail Next Obligation.

Notation "'x25519_secret_to_public_inp'" :=(
  x25519_serialized_scalar_t : choice_type) (in custom pack_type at level 2).
Notation "'x25519_secret_to_public_out'" :=(
  x25519_serialized_point_t : choice_type) (in custom pack_type at level 2).
Definition X25519_SECRET_TO_PUBLIC : nat :=
  (1684).
Program Definition x25519_secret_to_public
  (s_1675 : x25519_serialized_scalar_t)
  :both (CEfset ([base_1673_loc])) [interface
  #val #[ X25519_SCALARMULT ] : x25519_scalarmult_inp → x25519_scalarmult_out
  ] (x25519_serialized_point_t) :=
  #import {sig #[ X25519_SCALARMULT ] : x25519_scalarmult_inp → x25519_scalarmult_out } as x25519_scalarmult ;;
  let x25519_scalarmult := fun x_0 x_1 => x25519_scalarmult (x_0,x_1) in
  letbm base_1673 : x25519_serialized_point_t loc( base_1673_loc ) :=
    array_new_ (default : uint8) (32) in
  letb base_1673 : x25519_serialized_point_t :=
    array_upd base_1673 (lift_to_both0 (usize 0)) (is_pure (secret (
          lift_to_both0 (@repr U8 9)))) in
  lift_scope (H_loc_incl := _) (H_opsig_incl := _) (x25519_scalarmult (
      lift_to_both0 s_1675) (lift_to_both0 base_1673))
  .
Fail Next Obligation.

