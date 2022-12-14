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

Definition next_idxs_1738_loc : ChoiceEqualityLocation :=
  (next_ids_t ; 1739%nat).
Definition tail_1737_loc : ChoiceEqualityLocation :=
  (tail_t ; 1740%nat).
Notation "'clist_new_inp'" :=(
  unit_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'clist_new_inp'" :=(
  unit_ChoiceEquality : ChoiceEquality) (at level 2).
Notation "'clist_new_out'" :=(
  clist_t : choice_type) (in custom pack_type at level 2).
Notation "'clist_new_out'" :=(clist_t : ChoiceEquality) (at level 2).
Definition CLIST_NEW : nat :=
  1743.
Program Definition clist_new 
  : both (CEfset ([tail_1737_loc ; next_idxs_1738_loc])) [interface] (
    clist_t) :=
  ((letbm tail_1737 : tail_t loc( tail_1737_loc ) :=
        array_new_ (default : int8) (n_queues_v) in
      letb tail_1737 :=
        foldi_both' (lift_to_both0 (usize 0)) (array_len (
              lift_to_both0 tail_1737)) tail_1737 (L := (CEfset (
                [tail_1737_loc ; next_idxs_1738_loc]))) (I := [interface]) (
            fun i_1741 tail_1737 =>
            letb tail_1737 : tail_t :=
              array_upd tail_1737 (lift_to_both0 i_1741) (is_pure (
                  lift_to_both0 sentinel_v)) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 tail_1737)
            ) in
      letbm next_idxs_1738 : next_ids_t loc( next_idxs_1738_loc ) :=
        array_new_ (default : int8) (n_threads_v) in
      letb next_idxs_1738 :=
        foldi_both' (lift_to_both0 (usize 0)) (array_len (
              lift_to_both0 next_idxs_1738)) next_idxs_1738 (L := (CEfset (
                [tail_1737_loc ; next_idxs_1738_loc]))) (I := [interface]) (
            fun i_1742 next_idxs_1738 =>
            letb next_idxs_1738 : next_ids_t :=
              array_upd next_idxs_1738 (lift_to_both0 i_1742) (is_pure (
                  lift_to_both0 sentinel_v)) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 next_idxs_1738)
            ) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (Clist (prod_b(
            lift_to_both0 tail_1737,
            lift_to_both0 next_idxs_1738
          )))
      ) : both (CEfset ([tail_1737_loc ; next_idxs_1738_loc])) [interface] (
      clist_t)).
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
  1749.
Program Definition clist_is_empty (x_1746 : clist_t) (rq_1744 : runqueue_id_t)
  : both (fset.fset0) [interface] (bool_ChoiceEquality) :=
  ((letb RunqueueId (rq_1745) : runqueue_id_t := lift_to_both0 rq_1744 in
      letb Clist ((tail_1747, next_ids_1748)) : clist_t :=
        lift_to_both0 x_1746 in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) ((array_index (
            tail_1747) ((fun x => lift_to_both0 (repr (unsigned x)))(
              lift_to_both0 rq_1745))) =.? (lift_to_both0 sentinel_v))
      ) : both (fset.fset0) [interface] (bool_ChoiceEquality)).
Fail Next Obligation.

Definition tail_1750_loc : ChoiceEqualityLocation :=
  (tail_t ; 1752%nat).
Definition next_idxs_1751_loc : ChoiceEqualityLocation :=
  (next_ids_t ; 1753%nat).
Notation "'clist_push_inp'" :=(
  clist_t '× thread_id_t '× runqueue_id_t : choice_type) (in custom pack_type at level 2).
Notation "'clist_push_inp'" :=(
  clist_t '× thread_id_t '× runqueue_id_t : ChoiceEquality) (at level 2).
Notation "'clist_push_out'" :=(
  clist_t : choice_type) (in custom pack_type at level 2).
Notation "'clist_push_out'" :=(clist_t : ChoiceEquality) (at level 2).
Definition CLIST_PUSH : nat :=
  1759.
Program Definition clist_push (x_1758 : clist_t) (n_1756 : thread_id_t) (
    rq_1754 : runqueue_id_t)
  : both (CEfset ([tail_1750_loc ; next_idxs_1751_loc])) [interface] (
    clist_t) :=
  ((letb RunqueueId (rq_1755) : runqueue_id_t := lift_to_both0 rq_1754 in
      letb ThreadId (n_1757) : thread_id_t := lift_to_both0 n_1756 in
      letb Clist ((tail_1750, next_idxs_1751)) : clist_t :=
        lift_to_both0 x_1758 in
      letb '(tail_1750, next_idxs_1751) :=
        if (array_index (next_idxs_1751) (
            (fun x => lift_to_both0 (repr (unsigned x)))(
              lift_to_both0 n_1757))) =.? (
          lift_to_both0 sentinel_v) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset ([tail_1750_loc ; next_idxs_1751_loc])) (
          L2 := CEfset ([tail_1750_loc ; next_idxs_1751_loc])) (
          I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (letb '(
              tail_1750,
              next_idxs_1751
            ) :=
            if (array_index (tail_1750) (
                (fun x => lift_to_both0 (repr (unsigned x)))(
                  lift_to_both0 rq_1755))) =.? (
              lift_to_both0 sentinel_v) :bool_ChoiceEquality
            then lift_scope (L1 := CEfset (
                [tail_1750_loc ; next_idxs_1751_loc])) (L2 := CEfset (
                [tail_1750_loc ; next_idxs_1751_loc])) (I1 := [interface]) (
              I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
              letb tail_1750 : tail_t :=
                array_upd tail_1750 (
                  (fun x => lift_to_both0 (repr (unsigned x)))(
                    lift_to_both0 rq_1755)) (is_pure (lift_to_both0 n_1757)) in
              letb next_idxs_1751 : next_ids_t :=
                array_upd next_idxs_1751 (
                  (fun x => lift_to_both0 (repr (unsigned x)))(
                    lift_to_both0 n_1757)) (is_pure (lift_to_both0 n_1757)) in
              lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                  lift_to_both0 tail_1750,
                  lift_to_both0 next_idxs_1751
                ))
              )
            else  lift_scope (L1 := CEfset (
                [tail_1750_loc ; next_idxs_1751_loc])) (L2 := CEfset (
                [tail_1750_loc ; next_idxs_1751_loc])) (I1 := [interface]) (
              I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
              letb next_idxs_1751 : next_ids_t :=
                array_upd next_idxs_1751 (
                  (fun x => lift_to_both0 (repr (unsigned x)))(
                    lift_to_both0 n_1757)) (is_pure (array_index (
                      next_idxs_1751) (
                      (fun x => lift_to_both0 (repr (unsigned x)))(array_index (
                          tail_1750) (
                          (fun x => lift_to_both0 (repr (unsigned x)))(
                            lift_to_both0 rq_1755)))))) in
              letb next_idxs_1751 : next_ids_t :=
                array_upd next_idxs_1751 (
                  (fun x => lift_to_both0 (repr (unsigned x)))(array_index (
                      tail_1750) ((fun x => lift_to_both0 (repr (unsigned x)))(
                        lift_to_both0 rq_1755)))) (is_pure (
                    lift_to_both0 n_1757)) in
              letb tail_1750 : tail_t :=
                array_upd tail_1750 (
                  (fun x => lift_to_both0 (repr (unsigned x)))(
                    lift_to_both0 rq_1755)) (is_pure (lift_to_both0 n_1757)) in
              lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                  lift_to_both0 tail_1750,
                  lift_to_both0 next_idxs_1751
                ))
              ) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
              lift_to_both0 tail_1750,
              lift_to_both0 next_idxs_1751
            ))
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
            lift_to_both0 tail_1750,
            lift_to_both0 next_idxs_1751
          ))
         in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (Clist (prod_b(
            lift_to_both0 tail_1750,
            lift_to_both0 next_idxs_1751
          )))
      ) : both (CEfset ([tail_1750_loc ; next_idxs_1751_loc])) [interface] (
      clist_t)).
Fail Next Obligation.

Definition tail_1760_loc : ChoiceEqualityLocation :=
  (tail_t ; 1763%nat).
Definition next_idxs_1761_loc : ChoiceEqualityLocation :=
  (next_ids_t ; 1764%nat).
Definition out_1762_loc : ChoiceEqualityLocation :=
  ((option (int8)) ; 1765%nat).
Notation "'clist_pop_head_inp'" :=(
  clist_t '× runqueue_id_t : choice_type) (in custom pack_type at level 2).
Notation "'clist_pop_head_inp'" :=(
  clist_t '× runqueue_id_t : ChoiceEquality) (at level 2).
Notation "'clist_pop_head_out'" :=((clist_t '× (option (int8))
  ) : choice_type) (in custom pack_type at level 2).
Notation "'clist_pop_head_out'" :=((clist_t '× (option (int8))
  ) : ChoiceEquality) (at level 2).
Definition CLIST_POP_HEAD : nat :=
  1770.
Program Definition clist_pop_head (x_1768 : clist_t) (rq_1766 : runqueue_id_t)
  : both (CEfset (
      [tail_1760_loc ; next_idxs_1761_loc ; out_1762_loc])) [interface] ((
      clist_t '×
      (option (int8))
    )) :=
  ((letb RunqueueId (rq_1767) : runqueue_id_t := lift_to_both0 rq_1766 in
      letb Clist ((tail_1760, next_idxs_1761)) : clist_t :=
        lift_to_both0 x_1768 in
      letbm out_1762 : (option (int8)) loc( out_1762_loc ) := @None int8 in
      letb '(tail_1760, next_idxs_1761, out_1762) :=
        if (array_index (tail_1760) (
            (fun x => lift_to_both0 (repr (unsigned x)))(
              lift_to_both0 rq_1767))) =.? (
          lift_to_both0 sentinel_v) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset (
            [tail_1760_loc ; next_idxs_1761_loc ; out_1762_loc])) (
          L2 := CEfset ([tail_1760_loc ; next_idxs_1761_loc ; out_1762_loc])) (
          I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
              lift_to_both0 tail_1760,
              lift_to_both0 next_idxs_1761,
              lift_to_both0 out_1762
            ))
          )
        else  lift_scope (L1 := CEfset (
            [tail_1760_loc ; next_idxs_1761_loc ; out_1762_loc])) (
          L2 := CEfset ([tail_1760_loc ; next_idxs_1761_loc ; out_1762_loc])) (
          I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
          letb head_1769 : int8 :=
            array_index (next_idxs_1761) (
              (fun x => lift_to_both0 (repr (unsigned x)))(array_index (
                  tail_1760) ((fun x => lift_to_both0 (repr (unsigned x)))(
                    lift_to_both0 rq_1767)))) in
          letb '(tail_1760, next_idxs_1761) :=
            if (lift_to_both0 head_1769) =.? (array_index (tail_1760) (
                (fun x => lift_to_both0 (repr (unsigned x)))(
                  lift_to_both0 rq_1767))) :bool_ChoiceEquality
            then lift_scope (L1 := CEfset (
                [tail_1760_loc ; next_idxs_1761_loc ; out_1762_loc])) (
              L2 := CEfset (
                [tail_1760_loc ; next_idxs_1761_loc ; out_1762_loc])) (
              I1 := [interface]) (
              I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
              letb tail_1760 : tail_t :=
                array_upd tail_1760 (
                  (fun x => lift_to_both0 (repr (unsigned x)))(
                    lift_to_both0 rq_1767)) (is_pure (
                    lift_to_both0 sentinel_v)) in
              lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                  lift_to_both0 tail_1760,
                  lift_to_both0 next_idxs_1761
                ))
              )
            else  lift_scope (L1 := CEfset (
                [tail_1760_loc ; next_idxs_1761_loc ; out_1762_loc])) (
              L2 := CEfset (
                [tail_1760_loc ; next_idxs_1761_loc ; out_1762_loc])) (
              I1 := [interface]) (
              I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
              letb next_idxs_1761 : next_ids_t :=
                array_upd next_idxs_1761 (
                  (fun x => lift_to_both0 (repr (unsigned x)))(array_index (
                      tail_1760) ((fun x => lift_to_both0 (repr (unsigned x)))(
                        lift_to_both0 rq_1767)))) (is_pure (array_index (
                      next_idxs_1761) (
                      (fun x => lift_to_both0 (repr (unsigned x)))(
                        lift_to_both0 head_1769)))) in
              lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                  lift_to_both0 tail_1760,
                  lift_to_both0 next_idxs_1761
                ))
              ) in
          letb next_idxs_1761 : next_ids_t :=
            array_upd next_idxs_1761 (
              (fun x => lift_to_both0 (repr (unsigned x)))(
                lift_to_both0 head_1769)) (is_pure (
                lift_to_both0 sentinel_v)) in
          letbm out_1762 loc( out_1762_loc ) :=
            @Some int8 (lift_to_both0 head_1769) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
              lift_to_both0 tail_1760,
              lift_to_both0 next_idxs_1761,
              lift_to_both0 out_1762
            ))
          ) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          Clist (prod_b(lift_to_both0 tail_1760, lift_to_both0 next_idxs_1761)),
          lift_to_both0 out_1762
        ))
      ) : both (CEfset (
        [tail_1760_loc ; next_idxs_1761_loc ; out_1762_loc])) [interface] ((
        clist_t '×
        (option (int8))
      ))).
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
  1776.
Program Definition clist_peek_head (x_1773 : clist_t) (rq_1771 : runqueue_id_t)
  : both (fset.fset0) [interface] ((option (int8))) :=
  ((letb RunqueueId (rq_1772) : runqueue_id_t := lift_to_both0 rq_1771 in
      letb Clist ((tail_1774, next_idxs_1775)) : clist_t :=
        lift_to_both0 x_1773 in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        if is_pure (I := [interface]) ((array_index (tail_1774) (
              (fun x => lift_to_both0 (repr (unsigned x)))(
                lift_to_both0 rq_1772))) =.? (lift_to_both0 sentinel_v))
        then @None int8
        else @Some int8 (array_index (next_idxs_1775) (
            (fun x => lift_to_both0 (repr (unsigned x)))(array_index (
                tail_1774) ((fun x => lift_to_both0 (repr (unsigned x)))(
                  lift_to_both0 rq_1772))))))
      ) : both (fset.fset0) [interface] ((option (int8)))).
Fail Next Obligation.

Definition tail_1777_loc : ChoiceEqualityLocation :=
  (tail_t ; 1778%nat).
Notation "'clist_advance_inp'" :=(
  clist_t '× runqueue_id_t : choice_type) (in custom pack_type at level 2).
Notation "'clist_advance_inp'" :=(
  clist_t '× runqueue_id_t : ChoiceEquality) (at level 2).
Notation "'clist_advance_out'" :=(
  clist_t : choice_type) (in custom pack_type at level 2).
Notation "'clist_advance_out'" :=(clist_t : ChoiceEquality) (at level 2).
Definition CLIST_ADVANCE : nat :=
  1783.
Program Definition clist_advance (x_1781 : clist_t) (rq_1779 : runqueue_id_t)
  : both (CEfset ([tail_1777_loc])) [interface] (clist_t) :=
  ((letb RunqueueId (rq_1780) : runqueue_id_t := lift_to_both0 rq_1779 in
      letb Clist ((tail_1777, next_idxs_1782)) : clist_t :=
        lift_to_both0 x_1781 in
      letb '(tail_1777) :=
        if (array_index (tail_1777) (
            (fun x => lift_to_both0 (repr (unsigned x)))(
              lift_to_both0 rq_1780))) !=.? (
          lift_to_both0 sentinel_v) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset ([tail_1777_loc])) (L2 := CEfset (
            [tail_1777_loc])) (I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
          letb tail_1777 : tail_t :=
            array_upd tail_1777 ((fun x => lift_to_both0 (repr (unsigned x)))(
                lift_to_both0 rq_1780)) (is_pure (array_index (next_idxs_1782) (
                  (fun x => lift_to_both0 (repr (unsigned x)))(array_index (
                      tail_1777) ((fun x => lift_to_both0 (repr (unsigned x)))(
                        lift_to_both0 rq_1780)))))) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 tail_1777)
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          lift_to_both0 tail_1777)
         in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (Clist (prod_b(
            lift_to_both0 tail_1777,
            lift_to_both0 next_idxs_1782
          )))
      ) : both (CEfset ([tail_1777_loc])) [interface] (clist_t)).
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
  1784.
Program Definition runqueue_new 
  : both (CEfset ([tail_1737_loc ; next_idxs_1738_loc])) [interface] (
    run_queue_t) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (RunQueue (prod_b(
            lift_to_both0 (@repr U32 0),
            clist_new 
          )))
      ) : both (CEfset ([tail_1737_loc ; next_idxs_1738_loc])) [interface] (
      run_queue_t)).
Fail Next Obligation.

Definition bitcache_1785_loc : ChoiceEqualityLocation :=
  (int32 ; 1787%nat).
Definition queues_1786_loc : ChoiceEqualityLocation :=
  (clist_t ; 1788%nat).
Notation "'runqueue_add_inp'" :=(
  run_queue_t '× thread_id_t '× runqueue_id_t : choice_type) (in custom pack_type at level 2).
Notation "'runqueue_add_inp'" :=(
  run_queue_t '× thread_id_t '× runqueue_id_t : ChoiceEquality) (at level 2).
Notation "'runqueue_add_out'" :=(
  run_queue_t : choice_type) (in custom pack_type at level 2).
Notation "'runqueue_add_out'" :=(run_queue_t : ChoiceEquality) (at level 2).
Definition RUNQUEUE_ADD : nat :=
  1793.
Program Definition runqueue_add (y_1791 : run_queue_t) (n_1792 : thread_id_t) (
    rq_1789 : runqueue_id_t)
  : both (CEfset (
      [tail_1750_loc ; next_idxs_1751_loc ; bitcache_1785_loc ; queues_1786_loc])) [interface] (
    run_queue_t) :=
  ((letb RunqueueId (rq_u8_1790) : runqueue_id_t := lift_to_both0 rq_1789 in
      letb RunQueue ((bitcache_1785, queues_1786)) : run_queue_t :=
        lift_to_both0 y_1791 in
      letbm bitcache_1785 loc( bitcache_1785_loc ) :=
        (lift_to_both0 bitcache_1785) .| ((lift_to_both0 (
              @repr U32 1)) shift_left (
            (fun x => lift_to_both0 (repr (unsigned x)))(
              lift_to_both0 rq_u8_1790))) in
      letbm queues_1786 loc( queues_1786_loc ) :=
        clist_push (lift_to_both0 queues_1786) (lift_to_both0 n_1792) (
          lift_to_both0 rq_1789) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (RunQueue (prod_b(
            lift_to_both0 bitcache_1785,
            lift_to_both0 queues_1786
          )))
      ) : both (CEfset (
        [tail_1750_loc ; next_idxs_1751_loc ; bitcache_1785_loc ; queues_1786_loc])) [interface] (
      run_queue_t)).
Fail Next Obligation.

Definition bitcache_1794_loc : ChoiceEqualityLocation :=
  (int32 ; 1795%nat).
Notation "'runqueue_del_inp'" :=(
  run_queue_t '× thread_id_t '× runqueue_id_t : choice_type) (in custom pack_type at level 2).
Notation "'runqueue_del_inp'" :=(
  run_queue_t '× thread_id_t '× runqueue_id_t : ChoiceEquality) (at level 2).
Notation "'runqueue_del_out'" :=(
  run_queue_t : choice_type) (in custom pack_type at level 2).
Notation "'runqueue_del_out'" :=(run_queue_t : ChoiceEquality) (at level 2).
Definition RUNQUEUE_DEL : nat :=
  1802.
Program Definition runqueue_del (y_1798 : run_queue_t) (n_1803 : thread_id_t) (
    rq_1796 : runqueue_id_t)
  : both (CEfset (
      [tail_1760_loc ; next_idxs_1761_loc ; out_1762_loc ; bitcache_1794_loc])) [interface] (
    run_queue_t) :=
  ((letb RunqueueId (rq_u8_1797) : runqueue_id_t := lift_to_both0 rq_1796 in
      letb RunQueue ((bitcache_1794, queues_1799)) : run_queue_t :=
        lift_to_both0 y_1798 in
      letb '(queues_1800, popped_1801) : (clist_t '× (option (int8))) :=
        clist_pop_head (lift_to_both0 queues_1799) (lift_to_both0 rq_1796) in
      letb '(bitcache_1794) :=
        if clist_is_empty (lift_to_both0 queues_1800) (
          lift_to_both0 rq_1796) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset (
            [tail_1760_loc ; next_idxs_1761_loc ; out_1762_loc ; bitcache_1794_loc])) (
          L2 := CEfset (
            [tail_1760_loc ; next_idxs_1761_loc ; out_1762_loc ; bitcache_1794_loc])) (
          I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
          letbm bitcache_1794 loc( bitcache_1794_loc ) :=
            (lift_to_both0 bitcache_1794) .& (not ((lift_to_both0 (
                    @repr U32 1)) shift_left (
                  (fun x => lift_to_both0 (repr (unsigned x)))(
                    lift_to_both0 rq_u8_1797)))) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 bitcache_1794)
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          lift_to_both0 bitcache_1794)
         in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (RunQueue (prod_b(
            lift_to_both0 bitcache_1794,
            lift_to_both0 queues_1800
          )))
      ) : both (CEfset (
        [tail_1760_loc ; next_idxs_1761_loc ; out_1762_loc ; bitcache_1794_loc])) [interface] (
      run_queue_t)).
Fail Next Obligation.


Notation "'runqueue_ffs_inp'" :=(
  int32 : choice_type) (in custom pack_type at level 2).
Notation "'runqueue_ffs_inp'" :=(int32 : ChoiceEquality) (at level 2).
Notation "'runqueue_ffs_out'" :=(
  int32 : choice_type) (in custom pack_type at level 2).
Notation "'runqueue_ffs_out'" :=(int32 : ChoiceEquality) (at level 2).
Definition RUNQUEUE_FFS : nat :=
  1805.
Program Definition runqueue_ffs (val_1804 : int32)
  : both (fset.fset0) [interface] (int32) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) ((pub_u32 (is_pure (
              lift_to_both0 uint32_bits_v))) .- (pub_uint32_leading_zeros (
            lift_to_both0 val_1804)))
      ) : both (fset.fset0) [interface] (int32)).
Fail Next Obligation.

Definition out_1806_loc : ChoiceEqualityLocation :=
  ((option (int8)) ; 1807%nat).
Notation "'runqueue_get_next_inp'" :=(
  run_queue_t : choice_type) (in custom pack_type at level 2).
Notation "'runqueue_get_next_inp'" :=(
  run_queue_t : ChoiceEquality) (at level 2).
Notation "'runqueue_get_next_out'" :=((option (
      int8)) : choice_type) (in custom pack_type at level 2).
Notation "'runqueue_get_next_out'" :=((option (
      int8)) : ChoiceEquality) (at level 2).
Definition RUNQUEUE_GET_NEXT : nat :=
  1813.
Program Definition runqueue_get_next (y_1808 : run_queue_t)
  : both (CEfset ([out_1806_loc])) [interface] ((option (int8))) :=
  ((letb RunQueue ((bitcache_1809, queues_1810)) : run_queue_t :=
        lift_to_both0 y_1808 in
      letb rq_ffs_1811 : int32 :=
        runqueue_ffs ((lift_to_both0 bitcache_1809)) in
      letbm out_1806 : (option (int8)) loc( out_1806_loc ) := @None int8 in
      letb '(out_1806) :=
        if (lift_to_both0 rq_ffs_1811) >.? (lift_to_both0 (
            @repr U32 0)) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset ([out_1806_loc])) (L2 := CEfset (
            [out_1806_loc])) (I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
          letb rq_1812 : runqueue_id_t :=
            RunqueueId ((fun x => lift_to_both0 (repr (unsigned x)))((
                  lift_to_both0 rq_ffs_1811) .- (lift_to_both0 (
                    @repr U32 1)))) in
          letbm out_1806 loc( out_1806_loc ) :=
            clist_peek_head (lift_to_both0 queues_1810) (
              lift_to_both0 rq_1812) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 out_1806)
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          lift_to_both0 out_1806)
         in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 out_1806)
      ) : both (CEfset ([out_1806_loc])) [interface] ((option (int8)))).
Fail Next Obligation.

Definition queues_1814_loc : ChoiceEqualityLocation :=
  (clist_t ; 1815%nat).
Notation "'runqueue_advance_inp'" :=(
  run_queue_t '× runqueue_id_t : choice_type) (in custom pack_type at level 2).
Notation "'runqueue_advance_inp'" :=(
  run_queue_t '× runqueue_id_t : ChoiceEquality) (at level 2).
Notation "'runqueue_advance_out'" :=(
  run_queue_t : choice_type) (in custom pack_type at level 2).
Notation "'runqueue_advance_out'" :=(run_queue_t : ChoiceEquality) (at level 2).
Definition RUNQUEUE_ADVANCE : nat :=
  1819.
Program Definition runqueue_advance (y_1816 : run_queue_t) (
    rq_1818 : runqueue_id_t)
  : both (CEfset ([tail_1777_loc ; queues_1814_loc])) [interface] (
    run_queue_t) :=
  ((letb RunQueue ((bitcache_1817, queues_1814)) : run_queue_t :=
        lift_to_both0 y_1816 in
      letbm queues_1814 loc( queues_1814_loc ) :=
        clist_advance (lift_to_both0 queues_1814) (lift_to_both0 rq_1818) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (RunQueue (prod_b(
            lift_to_both0 bitcache_1817,
            lift_to_both0 queues_1814
          )))
      ) : both (CEfset ([tail_1777_loc ; queues_1814_loc])) [interface] (
      run_queue_t)).
Fail Next Obligation.

