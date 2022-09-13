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

Definition uint32_bits_v : (uint_size) :=
  (let temp_7277 : uint_size :=
      ((usize 4) .* (usize 8)) in
    (temp_7277)).

Definition n_queues_v : (uint_size) :=
  ((usize 20)).

Definition n_threads_v : (uint_size) :=
  ((usize 30)).

Definition sentinel_v : (int8) :=
  ((@repr U8 255)).

Definition runqueue_id_t : ChoiceEquality :=
  (int8).
Definition RunqueueId (x : int8) : runqueue_id_t :=
  ( x).

Definition thread_id_t : ChoiceEquality :=
  (int8).
Definition ThreadId (x : int8) : thread_id_t :=
  ( x).

Definition tail_t  :=
  ( nseq (int8) (n_queues_v)).

Definition next_ids_t  :=
  ( nseq (int8) (n_threads_v)).

Definition clist_t : ChoiceEquality :=
  ((tail_t '× next_ids_t)).
Definition Clist (x : (tail_t '× next_ids_t)) : clist_t :=
  ( x).

Definition next_idxs_7286_loc : ChoiceEqualityLocation :=
  ((next_ids_t ; 7290%nat)).
Definition tail_7280_loc : ChoiceEqualityLocation :=
  ((tail_t ; 7291%nat)).
Notation "'clist_new_inp'" := (
  unit_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'clist_new_out'" := (
  clist_t : choice_type) (in custom pack_type at level 2).
Definition CLIST_NEW : nat :=
  (7292).
Program Definition clist_new
   : package (CEfset (
      [tail_7280_loc ; next_idxs_7286_loc])) [interface] [interface
  #val #[ CLIST_NEW ] : clist_new_inp → clist_new_out ] :=
  ([package #def #[ CLIST_NEW ] (temp_inp : clist_new_inp) : clist_new_out { 
    ({ code  '(tail_7280 : tail_t) ←
          ( '(temp_7279 : tail_t) ←
              (array_new_ (default : int8) (n_queues_v)) ;;
            ret (temp_7279)) ;;
        #put tail_7280_loc := tail_7280 ;;
       temp_7282 ←
        (array_len (tail_7280)) ;;
       '(tail_7280 : (tail_t)) ←
        (foldi' (usize 0) (temp_7282) tail_7280 (L2 := CEfset (
                [tail_7280_loc ; next_idxs_7286_loc])) (
              I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (fun i_7283 tail_7280 =>
            ({ code  '(tail_7280 : tail_t) ←
                (ret (array_upd tail_7280 (i_7283) (sentinel_v))) ;;
              
              @ret ((tail_t)) (tail_7280) } : code (CEfset (
                  [tail_7280_loc])) [interface] _))) ;;
      
       '(next_idxs_7286 : next_ids_t) ←
          ( '(temp_7285 : next_ids_t) ←
              (array_new_ (default : int8) (n_threads_v)) ;;
            ret (temp_7285)) ;;
        #put next_idxs_7286_loc := next_idxs_7286 ;;
       temp_7288 ←
        (array_len (next_idxs_7286)) ;;
       '(next_idxs_7286 : (next_ids_t)) ←
        (foldi' (usize 0) (temp_7288) next_idxs_7286 (L2 := CEfset (
                [tail_7280_loc ; next_idxs_7286_loc])) (
              I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (fun i_7289 next_idxs_7286 =>
            ({ code  '(next_idxs_7286 : next_ids_t) ←
                (ret (array_upd next_idxs_7286 (i_7289) (sentinel_v))) ;;
              
              @ret ((next_ids_t)) (next_idxs_7286) } : code (CEfset (
                  [tail_7280_loc ; next_idxs_7286_loc])) [interface] _))) ;;
      
      @ret (clist_t) (Clist (prod_ce(tail_7280, next_idxs_7286))) } : code (
        CEfset ([tail_7280_loc ; next_idxs_7286_loc])) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_clist_new : package _ _ _ :=
  (clist_new).
Fail Next Obligation.


Notation "'clist_is_empty_inp'" := (
  clist_t '× runqueue_id_t : choice_type) (in custom pack_type at level 2).
Notation "'clist_is_empty_out'" := (
  bool_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Definition CLIST_IS_EMPTY : nat :=
  (7302).
Program Definition clist_is_empty
   : package (fset.fset0) [interface] [interface
  #val #[ CLIST_IS_EMPTY ] : clist_is_empty_inp → clist_is_empty_out ] :=
  (
    [package #def #[ CLIST_IS_EMPTY ] (temp_inp : clist_is_empty_inp) : clist_is_empty_out { 
    let '(x_7294 , rq_7293) := temp_inp : clist_t '× runqueue_id_t in
    ({ code  '(RunqueueId (rq_7295) : runqueue_id_t) ←
        (ret (rq_7293)) ;;
       '(Clist ((tail_7297, next_ids_7301)) : clist_t) ←
        (ret (x_7294)) ;;
       temp_7298 ←
        (array_index (tail_7297) (@cast _ uint32 _ (rq_7295))) ;;
       '(temp_7300 : bool_ChoiceEquality) ←
        ((temp_7298) =.? (sentinel_v)) ;;
      @ret (bool_ChoiceEquality) (temp_7300) } : code (
        fset.fset0) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_clist_is_empty : package _ _ _ :=
  (clist_is_empty).
Fail Next Obligation.

Definition tail_7314_loc : ChoiceEqualityLocation :=
  ((tail_t ; 7328%nat)).
Definition next_idxs_7308_loc : ChoiceEqualityLocation :=
  ((next_ids_t ; 7329%nat)).
Notation "'clist_push_inp'" := (
  clist_t '× thread_id_t '× runqueue_id_t : choice_type) (in custom pack_type at level 2).
Notation "'clist_push_out'" := (
  clist_t : choice_type) (in custom pack_type at level 2).
Definition CLIST_PUSH : nat :=
  (7330).
Program Definition clist_push
   : package (CEfset (
      [tail_7314_loc ; next_idxs_7308_loc])) [interface] [interface
  #val #[ CLIST_PUSH ] : clist_push_inp → clist_push_out ] :=
  ([package #def #[ CLIST_PUSH ] (temp_inp : clist_push_inp) : clist_push_out { 
    let '(
      x_7305 , n_7304 , rq_7303) := temp_inp : clist_t '× thread_id_t '× runqueue_id_t in
    ({ code  '(RunqueueId (rq_7312) : runqueue_id_t) ←
        (ret (rq_7303)) ;;
       '(ThreadId (n_7306) : thread_id_t) ←
        (ret (n_7304)) ;;
       '(Clist ((tail_7314, next_idxs_7308)) : clist_t) ←
        (ret (x_7305)) ;;
       temp_7309 ←
        (array_index (next_idxs_7308) (@cast _ uint32 _ (n_7306))) ;;
       '(temp_7311 : bool_ChoiceEquality) ←
        ((temp_7309) =.? (sentinel_v)) ;;
       temp_7327 ←
        (if temp_7311:bool_ChoiceEquality
          then (*not state*) (let temp_then :=  temp_7315 ←
              (array_index (tail_7314) (@cast _ uint32 _ (rq_7312))) ;;
             '(temp_7317 : bool_ChoiceEquality) ←
              ((temp_7315) =.? (sentinel_v)) ;;
             temp_7325 ←
              (if temp_7317:bool_ChoiceEquality
                then (*not state*) (let temp_then :=  '(tail_7314 : tail_t) ←
                    (ret (array_upd tail_7314 (@cast _ uint32 _ (rq_7312)) (
                          n_7306))) ;;
                  
                   '(next_idxs_7308 : next_ids_t) ←
                    (ret (array_upd next_idxs_7308 (@cast _ uint32 _ (n_7306)) (
                          n_7306))) ;;
                  
                  @ret ((tail_t '× next_ids_t)) (prod_ce(
                      tail_7314,
                      next_idxs_7308
                    )) in
                  ({ code temp_then } : code (CEfset (
                        [tail_7314_loc ; next_idxs_7308_loc])) [interface] _))
                else  (({ code  '(next_idxs_7308 : next_ids_t) ←
                      ( temp_7319 ←
                          (array_index (tail_7314) (@cast _ uint32 _ (
                                rq_7312))) ;;
                         temp_7321 ←
                          (array_index (next_idxs_7308) (@cast _ uint32 _ (
                                temp_7319))) ;;
                        ret (array_upd next_idxs_7308 (@cast _ uint32 _ (
                              n_7306)) (temp_7321))) ;;
                    
                     '(next_idxs_7308 : next_ids_t) ←
                      ( temp_7323 ←
                          (array_index (tail_7314) (@cast _ uint32 _ (
                                rq_7312))) ;;
                        ret (array_upd next_idxs_7308 (@cast _ uint32 _ (
                              temp_7323)) (n_7306))) ;;
                    
                     '(tail_7314 : tail_t) ←
                      (ret (array_upd tail_7314 (@cast _ uint32 _ (rq_7312)) (
                            n_7306))) ;;
                    
                    @ret ((tail_t '× next_ids_t)) (prod_ce(
                        tail_7314,
                        next_idxs_7308
                      )) } : code (CEfset (
                        [tail_7314_loc ; next_idxs_7308_loc])) [interface] _))) ;;
            let '(tail_7314, next_idxs_7308) :=
              (temp_7325) : (tail_t '× next_ids_t) in
            
            @ret ((tail_t '× next_ids_t)) (prod_ce(tail_7314, next_idxs_7308
              )) in
            ({ code temp_then } : code (CEfset (
                  [tail_7314_loc ; next_idxs_7308_loc])) [interface] _))
          else @ret ((tail_t '× next_ids_t)) (prod_ce(tail_7314, next_idxs_7308
            ))) ;;
      let '(tail_7314, next_idxs_7308) :=
        (temp_7327) : (tail_t '× next_ids_t) in
      
      @ret (clist_t) (Clist (prod_ce(tail_7314, next_idxs_7308))) } : code (
        CEfset ([tail_7314_loc ; next_idxs_7308_loc])) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_clist_push : package _ _ _ :=
  (clist_push).
Fail Next Obligation.

Definition next_idxs_7339_loc : ChoiceEqualityLocation :=
  ((next_ids_t ; 7358%nat)).
Definition out_7340_loc : ChoiceEqualityLocation :=
  (((option int8) ; 7359%nat)).
Definition tail_7335_loc : ChoiceEqualityLocation :=
  ((tail_t ; 7360%nat)).
Notation "'clist_pop_head_inp'" := (
  clist_t '× runqueue_id_t : choice_type) (in custom pack_type at level 2).
Notation "'clist_pop_head_out'" := ((clist_t '× (option int8)
  ) : choice_type) (in custom pack_type at level 2).
Definition CLIST_POP_HEAD : nat :=
  (7361).
Program Definition clist_pop_head
   : package (CEfset (
      [tail_7335_loc ; next_idxs_7339_loc ; out_7340_loc])) [interface] [interface
  #val #[ CLIST_POP_HEAD ] : clist_pop_head_inp → clist_pop_head_out ] :=
  (
    [package #def #[ CLIST_POP_HEAD ] (temp_inp : clist_pop_head_inp) : clist_pop_head_out { 
    let '(x_7332 , rq_7331) := temp_inp : clist_t '× runqueue_id_t in
    ({ code  '(RunqueueId (rq_7333) : runqueue_id_t) ←
        (ret (rq_7331)) ;;
       '(Clist ((tail_7335, next_idxs_7339)) : clist_t) ←
        (ret (x_7332)) ;;
       '(out_7340 : (option int8)) ←
          (ret (@None int8)) ;;
        #put out_7340_loc := out_7340 ;;
       temp_7336 ←
        (array_index (tail_7335) (@cast _ uint32 _ (rq_7333))) ;;
       '(temp_7338 : bool_ChoiceEquality) ←
        ((temp_7336) =.? (sentinel_v)) ;;
       temp_7357 ←
        (if temp_7338:bool_ChoiceEquality
          then (*not state*) (let temp_then := @ret ((
                tail_t '×
                next_ids_t '×
                (option int8)
              )) (prod_ce(tail_7335, next_idxs_7339, out_7340)) in
            ({ code temp_then } : code (CEfset (
                  [tail_7335_loc ; next_idxs_7339_loc ; out_7340_loc])) [interface] _))
          else  (({ code  '(head_7345 : int8) ←
                ( temp_7342 ←
                    (array_index (tail_7335) (@cast _ uint32 _ (rq_7333))) ;;
                   temp_7344 ←
                    (array_index (next_idxs_7339) (@cast _ uint32 _ (
                          temp_7342))) ;;
                  ret (temp_7344)) ;;
               temp_7347 ←
                (array_index (tail_7335) (@cast _ uint32 _ (rq_7333))) ;;
               '(temp_7349 : bool_ChoiceEquality) ←
                ((head_7345) =.? (temp_7347)) ;;
               temp_7355 ←
                (if temp_7349:bool_ChoiceEquality
                  then (*not state*) (let temp_then :=  '(
                        tail_7335 : tail_t) ←
                      (ret (array_upd tail_7335 (@cast _ uint32 _ (rq_7333)) (
                            sentinel_v))) ;;
                    
                    @ret ((tail_t '× next_ids_t)) (prod_ce(
                        tail_7335,
                        next_idxs_7339
                      )) in
                    ({ code temp_then } : code (CEfset (
                          [tail_7335_loc ; next_idxs_7339_loc ; out_7340_loc])) [interface] _))
                  else  (({ code  '(next_idxs_7339 : next_ids_t) ←
                        ( temp_7351 ←
                            (array_index (tail_7335) (@cast _ uint32 _ (
                                  rq_7333))) ;;
                           temp_7353 ←
                            (array_index (next_idxs_7339) (@cast _ uint32 _ (
                                  head_7345))) ;;
                          ret (array_upd next_idxs_7339 (@cast _ uint32 _ (
                                temp_7351)) (temp_7353))) ;;
                      
                      @ret ((tail_t '× next_ids_t)) (prod_ce(
                          tail_7335,
                          next_idxs_7339
                        )) } : code (CEfset (
                          [tail_7335_loc ; next_idxs_7339_loc ; out_7340_loc])) [interface] _))) ;;
              let '(tail_7335, next_idxs_7339) :=
                (temp_7355) : (tail_t '× next_ids_t) in
              
               '(next_idxs_7339 : next_ids_t) ←
                (ret (array_upd next_idxs_7339 (@cast _ uint32 _ (head_7345)) (
                      sentinel_v))) ;;
              
               '(out_7340 : (option int8)) ←
                  ((ret (@Some int8 (head_7345)))) ;;
                #put out_7340_loc := out_7340 ;;
              
              @ret ((tail_t '× next_ids_t '× (option int8))) (prod_ce(
                  tail_7335,
                  next_idxs_7339,
                  out_7340
                )) } : code (CEfset (
                  [tail_7335_loc ; next_idxs_7339_loc ; out_7340_loc])) [interface] _))) ;;
      let '(tail_7335, next_idxs_7339, out_7340) :=
        (temp_7357) : (tail_t '× next_ids_t '× (option int8)) in
      
      @ret ((clist_t '× (option int8))) (prod_ce(
          Clist (prod_ce(tail_7335, next_idxs_7339)),
          out_7340
        )) } : code (CEfset (
          [tail_7335_loc ; next_idxs_7339_loc ; out_7340_loc])) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_clist_pop_head : package _ _ _ :=
  (clist_pop_head).
Fail Next Obligation.


Notation "'clist_peek_head_inp'" := (
  clist_t '× runqueue_id_t : choice_type) (in custom pack_type at level 2).
Notation "'clist_peek_head_out'" := ((
    option int8) : choice_type) (in custom pack_type at level 2).
Definition CLIST_PEEK_HEAD : nat :=
  (7375).
Program Definition clist_peek_head
   : package (fset.fset0) [interface] [interface
  #val #[ CLIST_PEEK_HEAD ] : clist_peek_head_inp → clist_peek_head_out ] :=
  (
    [package #def #[ CLIST_PEEK_HEAD ] (temp_inp : clist_peek_head_inp) : clist_peek_head_out { 
    let '(x_7363 , rq_7362) := temp_inp : clist_t '× runqueue_id_t in
    ({ code  '(RunqueueId (rq_7364) : runqueue_id_t) ←
        (ret (rq_7362)) ;;
       '(Clist ((tail_7366, next_idxs_7373)) : clist_t) ←
        (ret (x_7363)) ;;
       temp_7367 ←
        (array_index (tail_7366) (@cast _ uint32 _ (rq_7364))) ;;
       '(temp_7369 : bool_ChoiceEquality) ←
        ((temp_7367) =.? (sentinel_v)) ;;
       temp_7371 ←
        (array_index (tail_7366) (@cast _ uint32 _ (rq_7364))) ;;
       temp_7374 ←
        (array_index (next_idxs_7373) (@cast _ uint32 _ (temp_7371))) ;;
      @ret ((option int8)) ((if (
            temp_7369):bool_ChoiceEquality then (*inline*) (@None int8) else (
            @Some int8 (temp_7374)))) } : code (fset.fset0) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_clist_peek_head : package _ _ _ :=
  (clist_peek_head).
Fail Next Obligation.

Definition tail_7380_loc : ChoiceEqualityLocation :=
  ((tail_t ; 7389%nat)).
Notation "'clist_advance_inp'" := (
  clist_t '× runqueue_id_t : choice_type) (in custom pack_type at level 2).
Notation "'clist_advance_out'" := (
  clist_t : choice_type) (in custom pack_type at level 2).
Definition CLIST_ADVANCE : nat :=
  (7390).
Program Definition clist_advance
   : package (CEfset ([tail_7380_loc])) [interface] [interface
  #val #[ CLIST_ADVANCE ] : clist_advance_inp → clist_advance_out ] :=
  (
    [package #def #[ CLIST_ADVANCE ] (temp_inp : clist_advance_inp) : clist_advance_out { 
    let '(x_7377 , rq_7376) := temp_inp : clist_t '× runqueue_id_t in
    ({ code  '(RunqueueId (rq_7378) : runqueue_id_t) ←
        (ret (rq_7376)) ;;
       '(Clist ((tail_7380, next_idxs_7387)) : clist_t) ←
        (ret (x_7377)) ;;
       temp_7381 ←
        (array_index (tail_7380) (@cast _ uint32 _ (rq_7378))) ;;
       '(temp_7383 : bool_ChoiceEquality) ←
        ((temp_7381) !=.? (sentinel_v)) ;;
       '(tail_7380 : (tail_t)) ←
        (if temp_7383:bool_ChoiceEquality
          then (*not state*) (let temp_then :=  '(tail_7380 : tail_t) ←
              ( temp_7385 ←
                  (array_index (tail_7380) (@cast _ uint32 _ (rq_7378))) ;;
                 temp_7388 ←
                  (array_index (next_idxs_7387) (@cast _ uint32 _ (
                        temp_7385))) ;;
                ret (array_upd tail_7380 (@cast _ uint32 _ (rq_7378)) (
                    temp_7388))) ;;
            
            @ret ((tail_t)) (tail_7380) in
            ({ code temp_then } : code (CEfset (
                  [tail_7380_loc])) [interface] _))
          else @ret ((tail_t)) (tail_7380)) ;;
      
      @ret (clist_t) (Clist (prod_ce(tail_7380, next_idxs_7387))) } : code (
        CEfset ([tail_7380_loc])) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_clist_advance : package _ _ _ :=
  (clist_advance).
Fail Next Obligation.

Definition run_queue_t : ChoiceEquality :=
  ((int32 '× clist_t)).
Definition RunQueue (x : (int32 '× clist_t)) : run_queue_t :=
  ( x).


Notation "'runqueue_new_inp'" := (
  unit_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'runqueue_new_out'" := (
  run_queue_t : choice_type) (in custom pack_type at level 2).
Definition RUNQUEUE_NEW : nat :=
  (7393).
Program Definition runqueue_new
   : package (CEfset ([])) [interface
  #val #[ CLIST_NEW ] : clist_new_inp → clist_new_out ] [interface
  #val #[ RUNQUEUE_NEW ] : runqueue_new_inp → runqueue_new_out ] :=
  (
    [package #def #[ RUNQUEUE_NEW ] (temp_inp : runqueue_new_inp) : runqueue_new_out { 
    #import {sig #[ CLIST_NEW ] : clist_new_inp → clist_new_out } as clist_new ;;
    let clist_new := clist_new tt in
    ({ code  '(temp_7392 : clist_t) ←
        (clist_new ) ;;
      @ret (run_queue_t) (RunQueue (prod_ce(@repr U32 0, temp_7392))) } : code (
        CEfset ([])) [interface
      #val #[ CLIST_NEW ] : clist_new_inp → clist_new_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_runqueue_new : package _ _ _ :=
  (seq_link runqueue_new link_rest(package_clist_new)).
Fail Next Obligation.

Definition bitcache_7396_loc : ChoiceEqualityLocation :=
  ((int32 ; 7406%nat)).
Definition queues_7402_loc : ChoiceEqualityLocation :=
  ((clist_t ; 7407%nat)).
Notation "'runqueue_add_inp'" := (
  run_queue_t '× thread_id_t '× runqueue_id_t : choice_type) (in custom pack_type at level 2).
Notation "'runqueue_add_out'" := (
  run_queue_t : choice_type) (in custom pack_type at level 2).
Definition RUNQUEUE_ADD : nat :=
  (7408).
Program Definition runqueue_add
   : package (CEfset ([bitcache_7396_loc ; queues_7402_loc])) [interface
  #val #[ CLIST_PUSH ] : clist_push_inp → clist_push_out ] [interface
  #val #[ RUNQUEUE_ADD ] : runqueue_add_inp → runqueue_add_out ] :=
  (
    [package #def #[ RUNQUEUE_ADD ] (temp_inp : runqueue_add_inp) : runqueue_add_out { 
    let '(
      y_7395 , n_7403 , rq_7394) := temp_inp : run_queue_t '× thread_id_t '× runqueue_id_t in
    #import {sig #[ CLIST_PUSH ] : clist_push_inp → clist_push_out } as clist_push ;;
    let clist_push := fun x_0 x_1 x_2 => clist_push (x_0,x_1,x_2) in
    ({ code  '(RunqueueId (rq_u8_7397) : runqueue_id_t) ←
        (ret (rq_7394)) ;;
       '(RunQueue ((bitcache_7396, queues_7402)) : run_queue_t) ←
        (ret (y_7395)) ;;
       '(bitcache_7396 : int32) ←
          (( temp_7399 ←
                ((@repr U32 1) shift_left (@cast _ uint32 _ (rq_u8_7397))) ;;
               temp_7401 ←
                ((bitcache_7396) .| (temp_7399)) ;;
              ret (temp_7401))) ;;
        #put bitcache_7396_loc := bitcache_7396 ;;
      
       '(queues_7402 : clist_t) ←
          (( '(temp_7405 : clist_t) ←
                (clist_push (queues_7402) (n_7403) (rq_7394)) ;;
              ret (temp_7405))) ;;
        #put queues_7402_loc := queues_7402 ;;
      
      @ret (run_queue_t) (RunQueue (prod_ce(bitcache_7396, queues_7402
          ))) } : code (CEfset (
          [bitcache_7396_loc ; queues_7402_loc])) [interface
      #val #[ CLIST_PUSH ] : clist_push_inp → clist_push_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_runqueue_add : package _ _ _ :=
  (seq_link runqueue_add link_rest(package_clist_push)).
Fail Next Obligation.

Definition bitcache_7417_loc : ChoiceEqualityLocation :=
  ((int32 ; 7426%nat)).
Notation "'runqueue_del_inp'" := (
  run_queue_t '× thread_id_t '× runqueue_id_t : choice_type) (in custom pack_type at level 2).
Notation "'runqueue_del_out'" := (
  run_queue_t : choice_type) (in custom pack_type at level 2).
Definition RUNQUEUE_DEL : nat :=
  (7427).
Program Definition runqueue_del
   : package (CEfset ([bitcache_7417_loc])) [interface
  #val #[ CLIST_IS_EMPTY ] : clist_is_empty_inp → clist_is_empty_out ;
  #val #[ CLIST_POP_HEAD ] : clist_pop_head_inp → clist_pop_head_out
  ] [interface #val #[ RUNQUEUE_DEL ] : runqueue_del_inp → runqueue_del_out
  ] :=
  (
    [package #def #[ RUNQUEUE_DEL ] (temp_inp : runqueue_del_inp) : runqueue_del_out { 
    let '(
      y_7410 , n_7428 , rq_7409) := temp_inp : run_queue_t '× thread_id_t '× runqueue_id_t in
    #import {sig #[ CLIST_IS_EMPTY ] : clist_is_empty_inp → clist_is_empty_out } as clist_is_empty ;;
    let clist_is_empty := fun x_0 x_1 => clist_is_empty (x_0,x_1) in
    #import {sig #[ CLIST_POP_HEAD ] : clist_pop_head_inp → clist_pop_head_out } as clist_pop_head ;;
    let clist_pop_head := fun x_0 x_1 => clist_pop_head (x_0,x_1) in
    ({ code  '(RunqueueId (rq_u8_7418) : runqueue_id_t) ←
        (ret (rq_7409)) ;;
       '(RunQueue ((bitcache_7417, queues_7411)) : run_queue_t) ←
        (ret (y_7410)) ;;
       temp_7424 ←
        ( '(temp_7413 : (clist_t '× (option int8))) ←
            (clist_pop_head (queues_7411) (rq_7409)) ;;
          ret (temp_7413)) ;;
      let '(queues_7414, popped_7425) :=
        (temp_7424) : (clist_t '× (option int8)) in
       '(temp_7416 : bool_ChoiceEquality) ←
        (clist_is_empty (queues_7414) (rq_7409)) ;;
       '(bitcache_7417 : (int32)) ←
        (if temp_7416:bool_ChoiceEquality
          then (*not state*) (let temp_then :=  '(bitcache_7417 : int32) ←
                (( temp_7420 ←
                      ((@repr U32 1) shift_left (@cast _ uint32 _ (
                            rq_u8_7418))) ;;
                     temp_7422 ←
                      ((bitcache_7417) .& (not (temp_7420))) ;;
                    ret (temp_7422))) ;;
              #put bitcache_7417_loc := bitcache_7417 ;;
            
            @ret ((int32)) (bitcache_7417) in
            ({ code temp_then } : code (CEfset (
                  [bitcache_7417_loc])) [interface] _))
          else @ret ((int32)) (bitcache_7417)) ;;
      
      @ret (run_queue_t) (RunQueue (prod_ce(bitcache_7417, queues_7414
          ))) } : code (CEfset ([bitcache_7417_loc])) [interface
      #val #[ CLIST_IS_EMPTY ] : clist_is_empty_inp → clist_is_empty_out ;
      #val #[ CLIST_POP_HEAD ] : clist_pop_head_inp → clist_pop_head_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_runqueue_del : package _ _ _ :=
  (seq_link runqueue_del link_rest(
      package_clist_is_empty,package_clist_pop_head)).
Fail Next Obligation.


Notation "'runqueue_ffs_inp'" := (
  int32 : choice_type) (in custom pack_type at level 2).
Notation "'runqueue_ffs_out'" := (
  int32 : choice_type) (in custom pack_type at level 2).
Definition RUNQUEUE_FFS : nat :=
  (7434).
Program Definition runqueue_ffs
   : package (fset.fset0) [interface] [interface
  #val #[ RUNQUEUE_FFS ] : runqueue_ffs_inp → runqueue_ffs_out ] :=
  (
    [package #def #[ RUNQUEUE_FFS ] (temp_inp : runqueue_ffs_inp) : runqueue_ffs_out { 
    let '(val_7429) := temp_inp : int32 in
    ({ code  temp_7431 ←
        (pub_uint32_leading_zeros (val_7429)) ;;
       '(temp_7433 : int32) ←
        ((pub_u32 (uint32_bits_v)) .- (temp_7431)) ;;
      @ret (int32) (temp_7433) } : code (fset.fset0) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_runqueue_ffs : package _ _ _ :=
  (runqueue_ffs).
Fail Next Obligation.

Definition out_7448_loc : ChoiceEqualityLocation :=
  (((option int8) ; 7449%nat)).
Notation "'runqueue_get_next_inp'" := (
  run_queue_t : choice_type) (in custom pack_type at level 2).
Notation "'runqueue_get_next_out'" := ((
    option int8) : choice_type) (in custom pack_type at level 2).
Definition RUNQUEUE_GET_NEXT : nat :=
  (7450).
Program Definition runqueue_get_next
   : package (CEfset ([out_7448_loc])) [interface
  #val #[ CLIST_PEEK_HEAD ] : clist_peek_head_inp → clist_peek_head_out ;
  #val #[ RUNQUEUE_FFS ] : runqueue_ffs_inp → runqueue_ffs_out ] [interface
  #val #[ RUNQUEUE_GET_NEXT ] : runqueue_get_next_inp → runqueue_get_next_out
  ] :=
  (
    [package #def #[ RUNQUEUE_GET_NEXT ] (temp_inp : runqueue_get_next_inp) : runqueue_get_next_out { 
    let '(y_7435) := temp_inp : run_queue_t in
    #import {sig #[ CLIST_PEEK_HEAD ] : clist_peek_head_inp → clist_peek_head_out } as clist_peek_head ;;
    let clist_peek_head := fun x_0 x_1 => clist_peek_head (x_0,x_1) in
    #import {sig #[ RUNQUEUE_FFS ] : runqueue_ffs_inp → runqueue_ffs_out } as runqueue_ffs ;;
    let runqueue_ffs := fun x_0 => runqueue_ffs (x_0) in
    ({ code  '(RunQueue ((bitcache_7436, queues_7444)) : run_queue_t) ←
        (ret (y_7435)) ;;
       '(rq_ffs_7439 : int32) ←
        ( '(temp_7438 : int32) ←
            (runqueue_ffs ((bitcache_7436))) ;;
          ret (temp_7438)) ;;
       '(out_7448 : (option int8)) ←
          (ret (@None int8)) ;;
        #put out_7448_loc := out_7448 ;;
       '(temp_7441 : bool_ChoiceEquality) ←
        ((rq_ffs_7439) >.? (@repr U32 0)) ;;
       '(out_7448 : ((option int8))) ←
        (if temp_7441:bool_ChoiceEquality
          then (*not state*) (let temp_then :=  '(rq_7445 : runqueue_id_t) ←
              ( '(temp_7443 : int32) ←
                  ((rq_ffs_7439) .- (@repr U32 1)) ;;
                ret (RunqueueId (@cast _ uint8 _ (temp_7443)))) ;;
             '(out_7448 : (option int8)) ←
                (( '(temp_7447 : (option int8)) ←
                      (clist_peek_head (queues_7444) (rq_7445)) ;;
                    ret (temp_7447))) ;;
              #put out_7448_loc := out_7448 ;;
            
            @ret (((option int8))) (out_7448) in
            ({ code temp_then } : code (CEfset ([out_7448_loc])) [interface
              #val #[ CLIST_PEEK_HEAD ] : clist_peek_head_inp → clist_peek_head_out
              ] _))
          else @ret (((option int8))) (out_7448)) ;;
      
      @ret ((option int8)) (out_7448) } : code (CEfset (
          [out_7448_loc])) [interface
      #val #[ CLIST_PEEK_HEAD ] : clist_peek_head_inp → clist_peek_head_out ;
      #val #[ RUNQUEUE_FFS ] : runqueue_ffs_inp → runqueue_ffs_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_runqueue_get_next : package _ _ _ :=
  (seq_link runqueue_get_next link_rest(
      package_clist_peek_head,package_runqueue_ffs)).
Fail Next Obligation.

Definition queues_7452_loc : ChoiceEqualityLocation :=
  ((clist_t ; 7457%nat)).
Notation "'runqueue_advance_inp'" := (
  run_queue_t '× runqueue_id_t : choice_type) (in custom pack_type at level 2).
Notation "'runqueue_advance_out'" := (
  run_queue_t : choice_type) (in custom pack_type at level 2).
Definition RUNQUEUE_ADVANCE : nat :=
  (7458).
Program Definition runqueue_advance
   : package (CEfset ([queues_7452_loc])) [interface
  #val #[ CLIST_ADVANCE ] : clist_advance_inp → clist_advance_out ] [interface
  #val #[ RUNQUEUE_ADVANCE ] : runqueue_advance_inp → runqueue_advance_out
  ] :=
  (
    [package #def #[ RUNQUEUE_ADVANCE ] (temp_inp : runqueue_advance_inp) : runqueue_advance_out { 
    let '(y_7451 , rq_7453) := temp_inp : run_queue_t '× runqueue_id_t in
    #import {sig #[ CLIST_ADVANCE ] : clist_advance_inp → clist_advance_out } as clist_advance ;;
    let clist_advance := fun x_0 x_1 => clist_advance (x_0,x_1) in
    ({ code  '(RunQueue ((bitcache_7456, queues_7452)) : run_queue_t) ←
        (ret (y_7451)) ;;
       '(queues_7452 : clist_t) ←
          (( '(temp_7455 : clist_t) ←
                (clist_advance (queues_7452) (rq_7453)) ;;
              ret (temp_7455))) ;;
        #put queues_7452_loc := queues_7452 ;;
      
      @ret (run_queue_t) (RunQueue (prod_ce(bitcache_7456, queues_7452
          ))) } : code (CEfset ([queues_7452_loc])) [interface
      #val #[ CLIST_ADVANCE ] : clist_advance_inp → clist_advance_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_runqueue_advance : package _ _ _ :=
  (seq_link runqueue_advance link_rest(package_clist_advance)).
Fail Next Obligation.

