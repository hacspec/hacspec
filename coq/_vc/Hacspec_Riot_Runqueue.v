(** This file was automatically generated using Hacspec **)
Set Warnings "-notation-overridden,-ambiguous-paths".
Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
Require Import Hacspec_Lib.

Definition uint32_bits_v : uint_size :=
  (usize 4) * (usize 8).

Definition n_queues_v : uint_size :=
  usize 20.

Definition n_threads_v : uint_size :=
  usize 30.

Definition sentinel_v : int8 :=
  @repr WORDSIZE8 255.

Inductive runqueue_id_t :=
| RunqueueId : int8 -> runqueue_id_t.

Inductive thread_id_t :=
| ThreadId : int8 -> thread_id_t.

Definition tail_t := nseq (int8) (n_queues_v).

Definition next_ids_t := nseq (int8) (n_threads_v).

Inductive clist_t :=
| Clist : (tail_t × next_ids_t) -> clist_t.

Definition clist_new  : clist_t :=
  let tail_1323 : tail_t :=
    array_new_ (default : int8) (n_queues_v) in 
  let tail_1323 :=
    foldi (usize 0) (array_len (tail_1323)) (fun i_1324 tail_1323 =>
      let tail_1323 :=
        array_upd tail_1323 (i_1324) (sentinel_v) in 
      (tail_1323))
    tail_1323 in 
  let next_idxs_1325 : next_ids_t :=
    array_new_ (default : int8) (n_threads_v) in 
  let next_idxs_1325 :=
    foldi (usize 0) (array_len (next_idxs_1325)) (fun i_1326 next_idxs_1325 =>
      let next_idxs_1325 :=
        array_upd next_idxs_1325 (i_1326) (sentinel_v) in 
      (next_idxs_1325))
    next_idxs_1325 in 
  Clist ((tail_1323, next_idxs_1325)).

Definition clist_is_empty (x_1327 : clist_t) (rq_1328 : runqueue_id_t) : bool :=
  let 'RunqueueId (rq_1329) :=
    rq_1328 in 
  let 'Clist ((tail_1330, next_ids_1331)) :=
    x_1327 in 
  (array_index (tail_1330) (@cast _ uint32 _ (rq_1329))) =.? (sentinel_v).

Definition clist_push
  (x_1332 : clist_t)
  (n_1333 : thread_id_t)
  (rq_1334 : runqueue_id_t)
  : clist_t :=
  let 'RunqueueId (rq_1335) :=
    rq_1334 in 
  let 'ThreadId (n_1336) :=
    n_1333 in 
  let 'Clist ((tail_1337, next_idxs_1338)) :=
    x_1332 in 
  let '(tail_1337, next_idxs_1338) :=
    if (array_index (next_idxs_1338) (@cast _ uint32 _ (n_1336))) =.? (
      sentinel_v):bool then (let '(tail_1337, next_idxs_1338) :=
        if (array_index (tail_1337) (@cast _ uint32 _ (rq_1335))) =.? (
          sentinel_v):bool then (let tail_1337 :=
            array_upd tail_1337 (@cast _ uint32 _ (rq_1335)) (n_1336) in 
          let next_idxs_1338 :=
            array_upd next_idxs_1338 (@cast _ uint32 _ (n_1336)) (n_1336) in 
          (tail_1337, next_idxs_1338)) else (let next_idxs_1338 :=
            array_upd next_idxs_1338 (@cast _ uint32 _ (n_1336)) (array_index (
                next_idxs_1338) (@cast _ uint32 _ (array_index (tail_1337) (
                    @cast _ uint32 _ (rq_1335))))) in 
          let next_idxs_1338 :=
            array_upd next_idxs_1338 (@cast _ uint32 _ (array_index (
                  tail_1337) (@cast _ uint32 _ (rq_1335)))) (n_1336) in 
          let tail_1337 :=
            array_upd tail_1337 (@cast _ uint32 _ (rq_1335)) (n_1336) in 
          (tail_1337, next_idxs_1338)) in 
      (tail_1337, next_idxs_1338)) else ((tail_1337, next_idxs_1338)) in 
  Clist ((tail_1337, next_idxs_1338)).

Definition clist_pop_head
  (x_1339 : clist_t)
  (rq_1340 : runqueue_id_t)
  : (clist_t × (option int8)) :=
  let 'RunqueueId (rq_1341) :=
    rq_1340 in 
  let 'Clist ((tail_1342, next_idxs_1343)) :=
    x_1339 in 
  let out_1344 : (option int8) :=
    @None int8 in 
  let '(tail_1342, next_idxs_1343, out_1344) :=
    if (array_index (tail_1342) (@cast _ uint32 _ (rq_1341))) =.? (
      sentinel_v):bool then ((tail_1342, next_idxs_1343, out_1344)) else (
      let head_1345 : int8 :=
        array_index (next_idxs_1343) (@cast _ uint32 _ (array_index (
              tail_1342) (@cast _ uint32 _ (rq_1341)))) in 
      let '(tail_1342, next_idxs_1343) :=
        if (head_1345) =.? (array_index (tail_1342) (@cast _ uint32 _ (
              rq_1341))):bool then (let tail_1342 :=
            array_upd tail_1342 (@cast _ uint32 _ (rq_1341)) (sentinel_v) in 
          (tail_1342, next_idxs_1343)) else (let next_idxs_1343 :=
            array_upd next_idxs_1343 (@cast _ uint32 _ (array_index (
                  tail_1342) (@cast _ uint32 _ (rq_1341)))) (array_index (
                next_idxs_1343) (@cast _ uint32 _ (head_1345))) in 
          (tail_1342, next_idxs_1343)) in 
      let next_idxs_1343 :=
        array_upd next_idxs_1343 (@cast _ uint32 _ (head_1345)) (sentinel_v) in 
      let out_1344 :=
        @Some int8 (head_1345) in 
      (tail_1342, next_idxs_1343, out_1344)) in 
  (Clist ((tail_1342, next_idxs_1343)), out_1344).

Definition clist_peek_head
  (x_1346 : clist_t)
  (rq_1347 : runqueue_id_t)
  : (option int8) :=
  let 'RunqueueId (rq_1348) :=
    rq_1347 in 
  let 'Clist ((tail_1349, next_idxs_1350)) :=
    x_1346 in 
  (if ((array_index (tail_1349) (@cast _ uint32 _ (rq_1348))) =.? (
        sentinel_v)):bool then (@None int8) else (@Some int8 (array_index (
          next_idxs_1350) (@cast _ uint32 _ (array_index (tail_1349) (
              @cast _ uint32 _ (rq_1348))))))).

Definition clist_advance
  (x_1351 : clist_t)
  (rq_1352 : runqueue_id_t)
  : clist_t :=
  let 'RunqueueId (rq_1353) :=
    rq_1352 in 
  let 'Clist ((tail_1354, next_idxs_1355)) :=
    x_1351 in 
  let '(tail_1354) :=
    if (array_index (tail_1354) (@cast _ uint32 _ (rq_1353))) !=.? (
      sentinel_v):bool then (let tail_1354 :=
        array_upd tail_1354 (@cast _ uint32 _ (rq_1353)) (array_index (
            next_idxs_1355) (@cast _ uint32 _ (array_index (tail_1354) (
                @cast _ uint32 _ (rq_1353))))) in 
      (tail_1354)) else ((tail_1354)) in 
  Clist ((tail_1354, next_idxs_1355)).

Inductive run_queue_t :=
| RunQueue : (int32 × clist_t) -> run_queue_t.

Definition runqueue_new  : run_queue_t :=
  RunQueue ((@repr WORDSIZE32 0, clist_new )).

Definition runqueue_add
  (y_1356 : run_queue_t)
  (n_1357 : thread_id_t)
  (rq_1358 : runqueue_id_t)
  : run_queue_t :=
  let 'RunqueueId (rq_u8_1359) :=
    rq_1358 in 
  let 'RunQueue ((bitcache_1360, queues_1361)) :=
    y_1356 in 
  let bitcache_1360 :=
    (bitcache_1360) .| ((@repr WORDSIZE32 1) shift_left (@cast _ uint32 _ (
          rq_u8_1359))) in 
  let queues_1361 :=
    clist_push (queues_1361) (n_1357) (rq_1358) in 
  RunQueue ((bitcache_1360, queues_1361)).

Definition runqueue_del
  (y_1362 : run_queue_t)
  (n_1363 : thread_id_t)
  (rq_1364 : runqueue_id_t)
  : run_queue_t :=
  let 'RunqueueId (rq_u8_1365) :=
    rq_1364 in 
  let 'RunQueue ((bitcache_1366, queues_1367)) :=
    y_1362 in 
  let '(queues_1368, popped_1369) :=
    clist_pop_head (queues_1367) (rq_1364) in 
  let '(bitcache_1366) :=
    if clist_is_empty (queues_1368) (rq_1364):bool then (let bitcache_1366 :=
        (bitcache_1366) .& (not ((@repr WORDSIZE32 1) shift_left (
              @cast _ uint32 _ (rq_u8_1365)))) in 
      (bitcache_1366)) else ((bitcache_1366)) in 
  RunQueue ((bitcache_1366, queues_1368)).

Definition runqueue_ffs (val_1370 : int32) : int32 :=
  (pub_u32 (uint32_bits_v)) .- (pub_uint32_leading_zeros (val_1370)).

Definition runqueue_get_next (y_1371 : run_queue_t) : (option int8) :=
  let 'RunQueue ((bitcache_1372, queues_1373)) :=
    y_1371 in 
  let rq_ffs_1374 : int32 :=
    runqueue_ffs ((bitcache_1372)) in 
  let out_1375 : (option int8) :=
    @None int8 in 
  let '(out_1375) :=
    if (rq_ffs_1374) >.? (@repr WORDSIZE32 0):bool then (
      let rq_1376 : runqueue_id_t :=
        RunqueueId (@cast _ uint8 _ ((rq_ffs_1374) .- (@repr WORDSIZE32 1))) in 
      let out_1375 :=
        clist_peek_head (queues_1373) (rq_1376) in 
      (out_1375)) else ((out_1375)) in 
  out_1375.

Definition runqueue_advance
  (y_1377 : run_queue_t)
  (rq_1378 : runqueue_id_t)
  : run_queue_t :=
  let 'RunQueue ((bitcache_1379, queues_1380)) :=
    y_1377 in 
  let queues_1380 :=
    clist_advance (queues_1380) (rq_1378) in 
  RunQueue ((bitcache_1379, queues_1380)).

