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


Definition uint32_bits_v : uint_size :=
  ((usize 4) .* (usize 8)).

Definition n_queues_v : uint_size :=
  usize 20.

Definition n_threads_v : uint_size :=
  usize 30.

Definition sentinel_v : int8 :=
  @repr U8 255.

Definition runqueue_id_t : ChoiceEquality :=
  int8.
Definition RunqueueId (x : int8) : runqueue_id_t :=
   x.

Definition thread_id_t : ChoiceEquality :=
  int8.
Definition ThreadId (x : int8) : thread_id_t :=
   x.

Definition tail_t := nseq (int8) (n_queues_v).

Definition next_ids_t := nseq (int8) (n_threads_v).

Definition clist_t : ChoiceEquality :=
  (tail_t '× next_ids_t).
Definition Clist (x : (tail_t '× next_ids_t)) : clist_t :=
   x.

Definition tail_1617_loc : ChoiceEqualityLocation :=
  (tail_t ; 1619%nat).
Definition next_idxs_1618_loc : ChoiceEqualityLocation :=
  (next_ids_t ; 1620%nat).
Notation "'clist_new_inp'" :=(
  unit_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'clist_new_inp'" :=(
  unit_ChoiceEquality : ChoiceEquality) (at level 2).
Notation "'clist_new_out'" :=(
  clist_t : choice_type) (in custom pack_type at level 2).
Notation "'clist_new_out'" :=(clist_t : ChoiceEquality) (at level 2).
Definition CLIST_NEW : nat :=
  1623.
Program Definition clist_new
  : both_package (CEfset ([tail_1617_loc ; next_idxs_1618_loc])) [interface] [(
    CLIST_NEW,(clist_new_inp,clist_new_out))] :=
  let temp_package_both := (fun temp_inp => 
    
    ((letbm tail_1617 : tail_t loc( tail_1617_loc ) :=
          array_new_ (default : int8) (n_queues_v) in
        letb tail_1617 :=
          foldi_both' (lift_to_both0 (usize 0)) (array_len (
                lift_to_both0 tail_1617)) tail_1617 (L := (CEfset (
                [tail_1617_loc ; next_idxs_1618_loc]))) (I := (
              [interface])) (fun i_1621 tail_1617 =>
            letb tail_1617 : tail_t :=
              array_upd tail_1617 (lift_to_both0 i_1621) (is_pure (
                  lift_to_both0 sentinel_v)) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 tail_1617)
            ) in
        letbm next_idxs_1618 : next_ids_t loc( next_idxs_1618_loc ) :=
          array_new_ (default : int8) (n_threads_v) in
        letb next_idxs_1618 :=
          foldi_both' (lift_to_both0 (usize 0)) (array_len (
                lift_to_both0 next_idxs_1618)) next_idxs_1618 (L := (CEfset (
                [tail_1617_loc ; next_idxs_1618_loc]))) (I := (
              [interface])) (fun i_1622 next_idxs_1618 =>
            letb next_idxs_1618 : next_ids_t :=
              array_upd next_idxs_1618 (lift_to_both0 i_1622) (is_pure (
                  lift_to_both0 sentinel_v)) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 next_idxs_1618)
            ) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (Clist (prod_b(
              lift_to_both0 tail_1617,
              lift_to_both0 next_idxs_1618
            )))
        ) : both (CEfset ([tail_1617_loc ; next_idxs_1618_loc])) [interface] (
        clist_t)))in
  both_package' _ _ (CLIST_NEW,(clist_new_inp,clist_new_out)) temp_package_both.
Fail Next Obligation.


Notation "'clist_is_empty_inp'" :=(
  clist_t '× runqueue_id_t : choice_type) (in custom pack_type at level 2).
Notation "'clist_is_empty_inp'" :=(
  clist_t '× runqueue_id_t : ChoiceEquality) (at level 2).
Notation "'clist_is_empty_out'" :=(
  bool_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'clist_is_empty_out'" :=(
  bool_ChoiceEquality : ChoiceEquality) (at level 2).
Definition CLIST_IS_EMPTY : nat :=
  1629.
Program Definition clist_is_empty
  : both_package (fset.fset0) [interface] [(CLIST_IS_EMPTY,(
      clist_is_empty_inp,clist_is_empty_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(x_1626 , rq_1624) := temp_inp : clist_t '× runqueue_id_t in
    
    ((letb RunqueueId (rq_1625) : runqueue_id_t := lift_to_both0 rq_1624 in
        letb Clist ((tail_1627, next_ids_1628)) : clist_t :=
          lift_to_both0 x_1626 in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) ((array_index (
              tail_1627) (@cast _ uint32 _ (lift_to_both0 rq_1625))) =.? (
            lift_to_both0 sentinel_v))
        ) : both (fset.fset0) [interface] (bool_ChoiceEquality)))in
  both_package' _ _ (CLIST_IS_EMPTY,(
      clist_is_empty_inp,clist_is_empty_out)) temp_package_both.
Fail Next Obligation.

Definition next_idxs_1631_loc : ChoiceEqualityLocation :=
  (next_ids_t ; 1632%nat).
Definition tail_1630_loc : ChoiceEqualityLocation :=
  (tail_t ; 1633%nat).
Notation "'clist_push_inp'" :=(
  clist_t '× thread_id_t '× runqueue_id_t : choice_type) (in custom pack_type at level 2).
Notation "'clist_push_inp'" :=(
  clist_t '× thread_id_t '× runqueue_id_t : ChoiceEquality) (at level 2).
Notation "'clist_push_out'" :=(
  clist_t : choice_type) (in custom pack_type at level 2).
Notation "'clist_push_out'" :=(clist_t : ChoiceEquality) (at level 2).
Definition CLIST_PUSH : nat :=
  1639.
Program Definition clist_push
  : both_package (CEfset ([tail_1630_loc ; next_idxs_1631_loc])) [interface] [(
    CLIST_PUSH,(clist_push_inp,clist_push_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(
      x_1638 , n_1636 , rq_1634) := temp_inp : clist_t '× thread_id_t '× runqueue_id_t in
    
    ((letb RunqueueId (rq_1635) : runqueue_id_t := lift_to_both0 rq_1634 in
        letb ThreadId (n_1637) : thread_id_t := lift_to_both0 n_1636 in
        letb Clist ((tail_1630, next_idxs_1631)) : clist_t :=
          lift_to_both0 x_1638 in
        letb '(tail_1630, next_idxs_1631) :=
          if (array_index (next_idxs_1631) (@cast _ uint32 _ (
                lift_to_both0 n_1637))) =.? (
            lift_to_both0 sentinel_v) :bool_ChoiceEquality
          then lift_scope (L1 := CEfset (
            [tail_1630_loc ; next_idxs_1631_loc])) (L2 := CEfset (
            [tail_1630_loc ; next_idxs_1631_loc])) (I1 := [interface]) (I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
            letb '(tail_1630, next_idxs_1631) :=
              if (array_index (tail_1630) (@cast _ uint32 _ (
                    lift_to_both0 rq_1635))) =.? (
                lift_to_both0 sentinel_v) :bool_ChoiceEquality
              then lift_scope (L1 := CEfset (
                [tail_1630_loc ; next_idxs_1631_loc])) (L2 := CEfset (
                [tail_1630_loc ; next_idxs_1631_loc])) (I1 := [interface]) (I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
                letb tail_1630 : tail_t :=
                  array_upd tail_1630 (@cast _ uint32 _ (
                      lift_to_both0 rq_1635)) (is_pure (
                      lift_to_both0 n_1637)) in
                letb next_idxs_1631 : next_ids_t :=
                  array_upd next_idxs_1631 (@cast _ uint32 _ (
                      lift_to_both0 n_1637)) (is_pure (lift_to_both0 n_1637)) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                    lift_to_both0 tail_1630,
                    lift_to_both0 next_idxs_1631
                  ))
                )
              else  lift_scope (L1 := CEfset (
                [tail_1630_loc ; next_idxs_1631_loc])) (L2 := CEfset (
                [tail_1630_loc ; next_idxs_1631_loc])) (I1 := [interface]) (I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
                letb next_idxs_1631 : next_ids_t :=
                  array_upd next_idxs_1631 (@cast _ uint32 _ (
                      lift_to_both0 n_1637)) (is_pure (array_index (
                        next_idxs_1631) (@cast _ uint32 _ (array_index (
                            tail_1630) (@cast _ uint32 _ (
                              lift_to_both0 rq_1635)))))) in
                letb next_idxs_1631 : next_ids_t :=
                  array_upd next_idxs_1631 (@cast _ uint32 _ (array_index (
                        tail_1630) (@cast _ uint32 _ (
                          lift_to_both0 rq_1635)))) (is_pure (
                      lift_to_both0 n_1637)) in
                letb tail_1630 : tail_t :=
                  array_upd tail_1630 (@cast _ uint32 _ (
                      lift_to_both0 rq_1635)) (is_pure (
                      lift_to_both0 n_1637)) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                    lift_to_both0 tail_1630,
                    lift_to_both0 next_idxs_1631
                  ))
                ) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                lift_to_both0 tail_1630,
                lift_to_both0 next_idxs_1631
              ))
            )
          else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
              lift_to_both0 tail_1630,
              lift_to_both0 next_idxs_1631
            ))
           in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (Clist (prod_b(
              lift_to_both0 tail_1630,
              lift_to_both0 next_idxs_1631
            )))
        ) : both (CEfset ([tail_1630_loc ; next_idxs_1631_loc])) [interface] (
        clist_t)))in
  both_package' _ _ (CLIST_PUSH,(
      clist_push_inp,clist_push_out)) temp_package_both.
Fail Next Obligation.

Definition tail_1640_loc : ChoiceEqualityLocation :=
  (tail_t ; 1643%nat).
Definition next_idxs_1641_loc : ChoiceEqualityLocation :=
  (next_ids_t ; 1644%nat).
Definition out_1642_loc : ChoiceEqualityLocation :=
  ((option (int8)) ; 1645%nat).
Notation "'clist_pop_head_inp'" :=(
  clist_t '× runqueue_id_t : choice_type) (in custom pack_type at level 2).
Notation "'clist_pop_head_inp'" :=(
  clist_t '× runqueue_id_t : ChoiceEquality) (at level 2).
Notation "'clist_pop_head_out'" :=((clist_t '× (option (int8))
  ) : choice_type) (in custom pack_type at level 2).
Notation "'clist_pop_head_out'" :=((clist_t '× (option (int8))
  ) : ChoiceEquality) (at level 2).
Definition CLIST_POP_HEAD : nat :=
  1650.
Program Definition clist_pop_head
  : both_package (CEfset (
      [tail_1640_loc ; next_idxs_1641_loc ; out_1642_loc])) [interface] [(
    CLIST_POP_HEAD,(clist_pop_head_inp,clist_pop_head_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(x_1648 , rq_1646) := temp_inp : clist_t '× runqueue_id_t in
    
    ((letb RunqueueId (rq_1647) : runqueue_id_t := lift_to_both0 rq_1646 in
        letb Clist ((tail_1640, next_idxs_1641)) : clist_t :=
          lift_to_both0 x_1648 in
        letbm out_1642 : (option (int8)) loc( out_1642_loc ) := @None int8 in
        letb '(tail_1640, next_idxs_1641, out_1642) :=
          if (array_index (tail_1640) (@cast _ uint32 _ (
                lift_to_both0 rq_1647))) =.? (
            lift_to_both0 sentinel_v) :bool_ChoiceEquality
          then lift_scope (L1 := CEfset (
            [tail_1640_loc ; next_idxs_1641_loc ; out_1642_loc])) (L2 := CEfset (
            [tail_1640_loc ; next_idxs_1641_loc ; out_1642_loc])) (I1 := [interface]) (I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                lift_to_both0 tail_1640,
                lift_to_both0 next_idxs_1641,
                lift_to_both0 out_1642
              ))
            )
          else  lift_scope (L1 := CEfset (
            [tail_1640_loc ; next_idxs_1641_loc ; out_1642_loc])) (L2 := CEfset (
            [tail_1640_loc ; next_idxs_1641_loc ; out_1642_loc])) (I1 := [interface]) (I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
            letb head_1649 : int8 :=
              array_index (next_idxs_1641) (@cast _ uint32 _ (array_index (
                    tail_1640) (@cast _ uint32 _ (lift_to_both0 rq_1647)))) in
            letb '(tail_1640, next_idxs_1641) :=
              if (lift_to_both0 head_1649) =.? (array_index (tail_1640) (
                  @cast _ uint32 _ (
                    lift_to_both0 rq_1647))) :bool_ChoiceEquality
              then lift_scope (L1 := CEfset (
                [tail_1640_loc ; next_idxs_1641_loc ; out_1642_loc])) (L2 := CEfset (
                [tail_1640_loc ; next_idxs_1641_loc ; out_1642_loc])) (I1 := [interface]) (I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
                letb tail_1640 : tail_t :=
                  array_upd tail_1640 (@cast _ uint32 _ (
                      lift_to_both0 rq_1647)) (is_pure (
                      lift_to_both0 sentinel_v)) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                    lift_to_both0 tail_1640,
                    lift_to_both0 next_idxs_1641
                  ))
                )
              else  lift_scope (L1 := CEfset (
                [tail_1640_loc ; next_idxs_1641_loc ; out_1642_loc])) (L2 := CEfset (
                [tail_1640_loc ; next_idxs_1641_loc ; out_1642_loc])) (I1 := [interface]) (I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
                letb next_idxs_1641 : next_ids_t :=
                  array_upd next_idxs_1641 (@cast _ uint32 _ (array_index (
                        tail_1640) (@cast _ uint32 _ (
                          lift_to_both0 rq_1647)))) (is_pure (array_index (
                        next_idxs_1641) (@cast _ uint32 _ (
                          lift_to_both0 head_1649)))) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                    lift_to_both0 tail_1640,
                    lift_to_both0 next_idxs_1641
                  ))
                ) in
            letb next_idxs_1641 : next_ids_t :=
              array_upd next_idxs_1641 (@cast _ uint32 _ (
                  lift_to_both0 head_1649)) (is_pure (
                  lift_to_both0 sentinel_v)) in
            letbm out_1642 loc( out_1642_loc ) :=
              @Some int8 (lift_to_both0 head_1649) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                lift_to_both0 tail_1640,
                lift_to_both0 next_idxs_1641,
                lift_to_both0 out_1642
              ))
            ) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
            Clist (prod_b(lift_to_both0 tail_1640, lift_to_both0 next_idxs_1641
              )),
            lift_to_both0 out_1642
          ))
        ) : both (CEfset (
          [tail_1640_loc ; next_idxs_1641_loc ; out_1642_loc])) [interface] ((
          clist_t '×
          (option (int8))
        ))))in
  both_package' _ _ (CLIST_POP_HEAD,(
      clist_pop_head_inp,clist_pop_head_out)) temp_package_both.
Fail Next Obligation.


Notation "'clist_peek_head_inp'" :=(
  clist_t '× runqueue_id_t : choice_type) (in custom pack_type at level 2).
Notation "'clist_peek_head_inp'" :=(
  clist_t '× runqueue_id_t : ChoiceEquality) (at level 2).
Notation "'clist_peek_head_out'" :=((option (
      int8)) : choice_type) (in custom pack_type at level 2).
Notation "'clist_peek_head_out'" :=((option (
      int8)) : ChoiceEquality) (at level 2).
Definition CLIST_PEEK_HEAD : nat :=
  1656.
Program Definition clist_peek_head
  : both_package (fset.fset0) [interface] [(CLIST_PEEK_HEAD,(
      clist_peek_head_inp,clist_peek_head_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(x_1653 , rq_1651) := temp_inp : clist_t '× runqueue_id_t in
    
    ((letb RunqueueId (rq_1652) : runqueue_id_t := lift_to_both0 rq_1651 in
        letb Clist ((tail_1654, next_idxs_1655)) : clist_t :=
          lift_to_both0 x_1653 in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          if is_pure (I := [interface]) ((array_index (tail_1654) (
                @cast _ uint32 _ (lift_to_both0 rq_1652))) =.? (
              lift_to_both0 sentinel_v))
          then @None int8
          else @Some int8 (array_index (next_idxs_1655) (@cast _ uint32 _ (
                array_index (tail_1654) (@cast _ uint32 _ (
                    lift_to_both0 rq_1652))))))
        ) : both (fset.fset0) [interface] ((option (int8)))))in
  both_package' _ _ (CLIST_PEEK_HEAD,(
      clist_peek_head_inp,clist_peek_head_out)) temp_package_both.
Fail Next Obligation.

Definition tail_1657_loc : ChoiceEqualityLocation :=
  (tail_t ; 1658%nat).
Notation "'clist_advance_inp'" :=(
  clist_t '× runqueue_id_t : choice_type) (in custom pack_type at level 2).
Notation "'clist_advance_inp'" :=(
  clist_t '× runqueue_id_t : ChoiceEquality) (at level 2).
Notation "'clist_advance_out'" :=(
  clist_t : choice_type) (in custom pack_type at level 2).
Notation "'clist_advance_out'" :=(clist_t : ChoiceEquality) (at level 2).
Definition CLIST_ADVANCE : nat :=
  1663.
Program Definition clist_advance
  : both_package (CEfset ([tail_1657_loc])) [interface] [(CLIST_ADVANCE,(
      clist_advance_inp,clist_advance_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(x_1661 , rq_1659) := temp_inp : clist_t '× runqueue_id_t in
    
    ((letb RunqueueId (rq_1660) : runqueue_id_t := lift_to_both0 rq_1659 in
        letb Clist ((tail_1657, next_idxs_1662)) : clist_t :=
          lift_to_both0 x_1661 in
        letb 'tail_1657 :=
          if (array_index (tail_1657) (@cast _ uint32 _ (
                lift_to_both0 rq_1660))) !=.? (
            lift_to_both0 sentinel_v) :bool_ChoiceEquality
          then lift_scope (L1 := CEfset ([tail_1657_loc])) (L2 := CEfset (
            [tail_1657_loc])) (I1 := [interface]) (I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
            letb tail_1657 : tail_t :=
              array_upd tail_1657 (@cast _ uint32 _ (lift_to_both0 rq_1660)) (
                is_pure (array_index (next_idxs_1662) (@cast _ uint32 _ (
                      array_index (tail_1657) (@cast _ uint32 _ (
                          lift_to_both0 rq_1660)))))) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 tail_1657)
            )
          else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 tail_1657)
           in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (Clist (prod_b(
              lift_to_both0 tail_1657,
              lift_to_both0 next_idxs_1662
            )))
        ) : both (CEfset ([tail_1657_loc])) [interface] (clist_t)))in
  both_package' _ _ (CLIST_ADVANCE,(
      clist_advance_inp,clist_advance_out)) temp_package_both.
Fail Next Obligation.

Definition run_queue_t : ChoiceEquality :=
  (int32 '× clist_t).
Definition RunQueue (x : (int32 '× clist_t)) : run_queue_t :=
   x.


Notation "'runqueue_new_inp'" :=(
  unit_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'runqueue_new_inp'" :=(
  unit_ChoiceEquality : ChoiceEquality) (at level 2).
Notation "'runqueue_new_out'" :=(
  run_queue_t : choice_type) (in custom pack_type at level 2).
Notation "'runqueue_new_out'" :=(run_queue_t : ChoiceEquality) (at level 2).
Definition RUNQUEUE_NEW : nat :=
  1664.
Program Definition runqueue_new
  : both_package (CEfset ([])) [interface
  #val #[ CLIST_NEW ] : clist_new_inp → clist_new_out ] [(RUNQUEUE_NEW,(
      runqueue_new_inp,runqueue_new_out))] :=
  let temp_package_both := (fun temp_inp => 
    
    let clist_new := package_both clist_new tt in
    ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (RunQueue (prod_b(
              lift_to_both0 (@repr U32 0),
              clist_new 
            )))
        ) : both (CEfset ([])) [interface
      #val #[ CLIST_NEW ] : clist_new_inp → clist_new_out ] (run_queue_t)))in
  both_package' _ _ (RUNQUEUE_NEW,(
      runqueue_new_inp,runqueue_new_out)) temp_package_both.
Fail Next Obligation.

Definition bitcache_1665_loc : ChoiceEqualityLocation :=
  (int32 ; 1667%nat).
Definition queues_1666_loc : ChoiceEqualityLocation :=
  (clist_t ; 1668%nat).
Notation "'runqueue_add_inp'" :=(
  run_queue_t '× thread_id_t '× runqueue_id_t : choice_type) (in custom pack_type at level 2).
Notation "'runqueue_add_inp'" :=(
  run_queue_t '× thread_id_t '× runqueue_id_t : ChoiceEquality) (at level 2).
Notation "'runqueue_add_out'" :=(
  run_queue_t : choice_type) (in custom pack_type at level 2).
Notation "'runqueue_add_out'" :=(run_queue_t : ChoiceEquality) (at level 2).
Definition RUNQUEUE_ADD : nat :=
  1673.
Program Definition runqueue_add
  : both_package (CEfset ([bitcache_1665_loc ; queues_1666_loc])) [interface
  #val #[ CLIST_PUSH ] : clist_push_inp → clist_push_out ] [(RUNQUEUE_ADD,(
      runqueue_add_inp,runqueue_add_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(
      y_1671 , n_1672 , rq_1669) := temp_inp : run_queue_t '× thread_id_t '× runqueue_id_t in
    
    let clist_push := fun x_0 x_1 x_2 => package_both clist_push (
      x_0,x_1,x_2) in
    ((letb RunqueueId (rq_u8_1670) : runqueue_id_t := lift_to_both0 rq_1669 in
        letb RunQueue ((bitcache_1665, queues_1666)) : run_queue_t :=
          lift_to_both0 y_1671 in
        letbm bitcache_1665 loc( bitcache_1665_loc ) :=
          (lift_to_both0 bitcache_1665) .| ((lift_to_both0 (
                @repr U32 1)) shift_left (@cast _ uint32 _ (
                lift_to_both0 rq_u8_1670))) in
        letbm queues_1666 loc( queues_1666_loc ) :=
          clist_push (lift_to_both0 queues_1666) (lift_to_both0 n_1672) (
            lift_to_both0 rq_1669) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (RunQueue (prod_b(
              lift_to_both0 bitcache_1665,
              lift_to_both0 queues_1666
            )))
        ) : both (CEfset ([bitcache_1665_loc ; queues_1666_loc])) [interface
      #val #[ CLIST_PUSH ] : clist_push_inp → clist_push_out ] (
        run_queue_t)))in
  both_package' _ _ (RUNQUEUE_ADD,(
      runqueue_add_inp,runqueue_add_out)) temp_package_both.
Fail Next Obligation.

Definition bitcache_1674_loc : ChoiceEqualityLocation :=
  (int32 ; 1675%nat).
Notation "'runqueue_del_inp'" :=(
  run_queue_t '× thread_id_t '× runqueue_id_t : choice_type) (in custom pack_type at level 2).
Notation "'runqueue_del_inp'" :=(
  run_queue_t '× thread_id_t '× runqueue_id_t : ChoiceEquality) (at level 2).
Notation "'runqueue_del_out'" :=(
  run_queue_t : choice_type) (in custom pack_type at level 2).
Notation "'runqueue_del_out'" :=(run_queue_t : ChoiceEquality) (at level 2).
Definition RUNQUEUE_DEL : nat :=
  1682.
Program Definition runqueue_del
  : both_package (CEfset ([bitcache_1674_loc])) [interface
  #val #[ CLIST_IS_EMPTY ] : clist_is_empty_inp → clist_is_empty_out ;
  #val #[ CLIST_POP_HEAD ] : clist_pop_head_inp → clist_pop_head_out ] [(
    RUNQUEUE_DEL,(runqueue_del_inp,runqueue_del_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(
      y_1678 , n_1683 , rq_1676) := temp_inp : run_queue_t '× thread_id_t '× runqueue_id_t in
    
    let clist_is_empty := fun x_0 x_1 => package_both clist_is_empty (
      x_0,x_1) in
    let clist_pop_head := fun x_0 x_1 => package_both clist_pop_head (
      x_0,x_1) in
    ((letb RunqueueId (rq_u8_1677) : runqueue_id_t := lift_to_both0 rq_1676 in
        letb RunQueue ((bitcache_1674, queues_1679)) : run_queue_t :=
          lift_to_both0 y_1678 in
        letb '(queues_1680, popped_1681) : (clist_t '× (option (int8))) :=
          clist_pop_head (lift_to_both0 queues_1679) (lift_to_both0 rq_1676) in
        letb 'bitcache_1674 :=
          if clist_is_empty (lift_to_both0 queues_1680) (
            lift_to_both0 rq_1676) :bool_ChoiceEquality
          then lift_scope (L1 := CEfset ([bitcache_1674_loc])) (L2 := CEfset (
            [bitcache_1674_loc])) (I1 := [interface]) (I2 := [interface
          #val #[ CLIST_IS_EMPTY ] : clist_is_empty_inp → clist_is_empty_out ;
          #val #[ CLIST_POP_HEAD ] : clist_pop_head_inp → clist_pop_head_out
          ]) (H_loc_incl := _) (H_opsig_incl := _) (
            letbm bitcache_1674 loc( bitcache_1674_loc ) :=
              (lift_to_both0 bitcache_1674) .& (not ((lift_to_both0 (
                      @repr U32 1)) shift_left (@cast _ uint32 _ (
                      lift_to_both0 rq_u8_1677)))) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 bitcache_1674)
            )
          else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 bitcache_1674)
           in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (RunQueue (prod_b(
              lift_to_both0 bitcache_1674,
              lift_to_both0 queues_1680
            )))
        ) : both (CEfset ([bitcache_1674_loc])) [interface
      #val #[ CLIST_IS_EMPTY ] : clist_is_empty_inp → clist_is_empty_out ;
      #val #[ CLIST_POP_HEAD ] : clist_pop_head_inp → clist_pop_head_out ] (
        run_queue_t)))in
  both_package' _ _ (RUNQUEUE_DEL,(
      runqueue_del_inp,runqueue_del_out)) temp_package_both.
Fail Next Obligation.


Notation "'runqueue_ffs_inp'" :=(
  int32 : choice_type) (in custom pack_type at level 2).
Notation "'runqueue_ffs_inp'" :=(int32 : ChoiceEquality) (at level 2).
Notation "'runqueue_ffs_out'" :=(
  int32 : choice_type) (in custom pack_type at level 2).
Notation "'runqueue_ffs_out'" :=(int32 : ChoiceEquality) (at level 2).
Definition RUNQUEUE_FFS : nat :=
  1685.
Program Definition runqueue_ffs
  : both_package (fset.fset0) [interface] [(RUNQUEUE_FFS,(
      runqueue_ffs_inp,runqueue_ffs_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(val_1684) := temp_inp : int32 in
    
    ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) ((pub_u32 (is_pure (
                lift_to_both0 uint32_bits_v))) .- (pub_uint32_leading_zeros (
              lift_to_both0 val_1684)))
        ) : both (fset.fset0) [interface] (int32)))in
  both_package' _ _ (RUNQUEUE_FFS,(
      runqueue_ffs_inp,runqueue_ffs_out)) temp_package_both.
Fail Next Obligation.

Definition out_1686_loc : ChoiceEqualityLocation :=
  ((option (int8)) ; 1687%nat).
Notation "'runqueue_get_next_inp'" :=(
  run_queue_t : choice_type) (in custom pack_type at level 2).
Notation "'runqueue_get_next_inp'" :=(
  run_queue_t : ChoiceEquality) (at level 2).
Notation "'runqueue_get_next_out'" :=((option (
      int8)) : choice_type) (in custom pack_type at level 2).
Notation "'runqueue_get_next_out'" :=((option (
      int8)) : ChoiceEquality) (at level 2).
Definition RUNQUEUE_GET_NEXT : nat :=
  1693.
Program Definition runqueue_get_next
  : both_package (CEfset ([out_1686_loc])) [interface
  #val #[ CLIST_PEEK_HEAD ] : clist_peek_head_inp → clist_peek_head_out ;
  #val #[ RUNQUEUE_FFS ] : runqueue_ffs_inp → runqueue_ffs_out ] [(
    RUNQUEUE_GET_NEXT,(runqueue_get_next_inp,runqueue_get_next_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(y_1688) := temp_inp : run_queue_t in
    
    let clist_peek_head := fun x_0 x_1 => package_both clist_peek_head (
      x_0,x_1) in
    let runqueue_ffs := fun x_0 => package_both runqueue_ffs (x_0) in
    ((letb RunQueue ((bitcache_1689, queues_1690)) : run_queue_t :=
          lift_to_both0 y_1688 in
        letb rq_ffs_1691 : int32 :=
          runqueue_ffs ((lift_to_both0 bitcache_1689)) in
        letbm out_1686 : (option (int8)) loc( out_1686_loc ) := @None int8 in
        letb 'out_1686 :=
          if (lift_to_both0 rq_ffs_1691) >.? (lift_to_both0 (
              @repr U32 0)) :bool_ChoiceEquality
          then lift_scope (L1 := CEfset ([out_1686_loc])) (L2 := CEfset (
            [out_1686_loc])) (I1 := [interface
          #val #[ CLIST_PEEK_HEAD ] : clist_peek_head_inp → clist_peek_head_out
          ]) (I2 := [interface
          #val #[ CLIST_PEEK_HEAD ] : clist_peek_head_inp → clist_peek_head_out ;
          #val #[ RUNQUEUE_FFS ] : runqueue_ffs_inp → runqueue_ffs_out
          ]) (H_loc_incl := _) (H_opsig_incl := _) (
            letb rq_1692 : runqueue_id_t :=
              RunqueueId (@cast _ uint8 _ ((lift_to_both0 rq_ffs_1691) .- (
                    lift_to_both0 (@repr U32 1)))) in
            letbm out_1686 loc( out_1686_loc ) :=
              clist_peek_head (lift_to_both0 queues_1690) (
                lift_to_both0 rq_1692) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 out_1686)
            )
          else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 out_1686)
           in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          lift_to_both0 out_1686)
        ) : both (CEfset ([out_1686_loc])) [interface
      #val #[ CLIST_PEEK_HEAD ] : clist_peek_head_inp → clist_peek_head_out ;
      #val #[ RUNQUEUE_FFS ] : runqueue_ffs_inp → runqueue_ffs_out ] ((
          option (int8)))))in
  both_package' _ _ (RUNQUEUE_GET_NEXT,(
      runqueue_get_next_inp,runqueue_get_next_out)) temp_package_both.
Fail Next Obligation.

Definition queues_1694_loc : ChoiceEqualityLocation :=
  (clist_t ; 1695%nat).
Notation "'runqueue_advance_inp'" :=(
  run_queue_t '× runqueue_id_t : choice_type) (in custom pack_type at level 2).
Notation "'runqueue_advance_inp'" :=(
  run_queue_t '× runqueue_id_t : ChoiceEquality) (at level 2).
Notation "'runqueue_advance_out'" :=(
  run_queue_t : choice_type) (in custom pack_type at level 2).
Notation "'runqueue_advance_out'" :=(run_queue_t : ChoiceEquality) (at level 2).
Definition RUNQUEUE_ADVANCE : nat :=
  1699.
Program Definition runqueue_advance
  : both_package (CEfset ([queues_1694_loc])) [interface
  #val #[ CLIST_ADVANCE ] : clist_advance_inp → clist_advance_out ] [(
    RUNQUEUE_ADVANCE,(runqueue_advance_inp,runqueue_advance_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(y_1696 , rq_1698) := temp_inp : run_queue_t '× runqueue_id_t in
    
    let clist_advance := fun x_0 x_1 => package_both clist_advance (x_0,x_1) in
    ((letb RunQueue ((bitcache_1697, queues_1694)) : run_queue_t :=
          lift_to_both0 y_1696 in
        letbm queues_1694 loc( queues_1694_loc ) :=
          clist_advance (lift_to_both0 queues_1694) (lift_to_both0 rq_1698) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (RunQueue (prod_b(
              lift_to_both0 bitcache_1697,
              lift_to_both0 queues_1694
            )))
        ) : both (CEfset ([queues_1694_loc])) [interface
      #val #[ CLIST_ADVANCE ] : clist_advance_inp → clist_advance_out ] (
        run_queue_t)))in
  both_package' _ _ (RUNQUEUE_ADVANCE,(
      runqueue_advance_inp,runqueue_advance_out)) temp_package_both.
Fail Next Obligation.

