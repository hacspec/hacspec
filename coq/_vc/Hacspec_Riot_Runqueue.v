(** This file was automatically generated using Hacspec **)
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
  let tail_1265 : tail_t :=
    array_new_ (default) (n_queues_v) in 
  let tail_1265 :=
    foldi (usize 0) (array_len (tail_1265)) (fun i_1266 tail_1265 =>
      let tail_1265 :=
        array_upd tail_1265 (i_1266) (sentinel_v) in 
      (tail_1265))
    tail_1265 in 
  let next_idxs_1267 : next_ids_t :=
    array_new_ (default) (n_threads_v) in 
  let next_idxs_1267 :=
    foldi (usize 0) (array_len (next_idxs_1267)) (fun i_1268 next_idxs_1267 =>
      let next_idxs_1267 :=
        array_upd next_idxs_1267 (i_1268) (sentinel_v) in 
      (next_idxs_1267))
    next_idxs_1267 in 
  Clist ((tail_1265, next_idxs_1267)).

Definition clist_is_empty (x_1269 : clist_t) (rq_1270 : runqueue_id_t) : bool :=
  let 'RunqueueId (rq_1271) :=
    rq_1270 in 
  let 'Clist ((tail_1272, next_ids_1273)) :=
    x_1269 in 
  (array_index (tail_1272) (@cast _ uint32 _ (rq_1271))) =.? (sentinel_v).

Definition clist_push
  (x_1274 : clist_t)
  (n_1275 : thread_id_t)
  (rq_1276 : runqueue_id_t)
  : clist_t :=
  let 'RunqueueId (rq_1277) :=
    rq_1276 in 
  let 'ThreadId (n_1278) :=
    n_1275 in 
  let 'Clist ((tail_1279, next_idxs_1280)) :=
    x_1274 in 
  let '(tail_1279, next_idxs_1280) :=
    if (array_index (next_idxs_1280) (@cast _ uint32 _ (n_1278))) =.? (
      sentinel_v):bool then (let '(tail_1279, next_idxs_1280) :=
        if (array_index (tail_1279) (@cast _ uint32 _ (rq_1277))) =.? (
          sentinel_v):bool then (let tail_1279 :=
            array_upd tail_1279 (@cast _ uint32 _ (rq_1277)) (n_1278) in 
          let next_idxs_1280 :=
            array_upd next_idxs_1280 (@cast _ uint32 _ (n_1278)) (n_1278) in 
          (tail_1279, next_idxs_1280)) else (let next_idxs_1280 :=
            array_upd next_idxs_1280 (@cast _ uint32 _ (n_1278)) (array_index (
                next_idxs_1280) (@cast _ uint32 _ (array_index (tail_1279) (
                    @cast _ uint32 _ (rq_1277))))) in 
          let next_idxs_1280 :=
            array_upd next_idxs_1280 (@cast _ uint32 _ (array_index (
                  tail_1279) (@cast _ uint32 _ (rq_1277)))) (n_1278) in 
          let tail_1279 :=
            array_upd tail_1279 (@cast _ uint32 _ (rq_1277)) (n_1278) in 
          (tail_1279, next_idxs_1280)) in 
      (tail_1279, next_idxs_1280)) else ((tail_1279, next_idxs_1280)) in 
  Clist ((tail_1279, next_idxs_1280)).

Definition clist_pop_head
  (x_1281 : clist_t)
  (rq_1282 : runqueue_id_t)
  : (clist_t × (option int8)) :=
  let 'RunqueueId (rq_1283) :=
    rq_1282 in 
  let 'Clist ((tail_1284, next_idxs_1285)) :=
    x_1281 in 
  let out_1286 : (option int8) :=
    @None int8 in 
  let '(tail_1284, next_idxs_1285, out_1286) :=
    if (array_index (tail_1284) (@cast _ uint32 _ (rq_1283))) =.? (
      sentinel_v):bool then ((tail_1284, next_idxs_1285, out_1286)) else (
      let head_1287 : int8 :=
        array_index (next_idxs_1285) (@cast _ uint32 _ (array_index (
              tail_1284) (@cast _ uint32 _ (rq_1283)))) in 
      let '(tail_1284, next_idxs_1285) :=
        if (head_1287) =.? (array_index (tail_1284) (@cast _ uint32 _ (
              rq_1283))):bool then (let tail_1284 :=
            array_upd tail_1284 (@cast _ uint32 _ (rq_1283)) (sentinel_v) in 
          (tail_1284, next_idxs_1285)) else (let next_idxs_1285 :=
            array_upd next_idxs_1285 (@cast _ uint32 _ (array_index (
                  tail_1284) (@cast _ uint32 _ (rq_1283)))) (array_index (
                next_idxs_1285) (@cast _ uint32 _ (head_1287))) in 
          (tail_1284, next_idxs_1285)) in 
      let next_idxs_1285 :=
        array_upd next_idxs_1285 (@cast _ uint32 _ (head_1287)) (sentinel_v) in 
      let out_1286 :=
        @Some int8 (head_1287) in 
      (tail_1284, next_idxs_1285, out_1286)) in 
  (Clist ((tail_1284, next_idxs_1285)), out_1286).

Definition clist_peek_head
  (x_1288 : clist_t)
  (rq_1289 : runqueue_id_t)
  : (option int8) :=
  let 'RunqueueId (rq_1290) :=
    rq_1289 in 
  let 'Clist ((tail_1291, next_idxs_1292)) :=
    x_1288 in 
  (if ((array_index (tail_1291) (@cast _ uint32 _ (rq_1290))) =.? (
        sentinel_v)):bool then (@None int8) else (@Some int8 (array_index (
          next_idxs_1292) (@cast _ uint32 _ (array_index (tail_1291) (
              @cast _ uint32 _ (rq_1290))))))).

Definition clist_advance
  (x_1293 : clist_t)
  (rq_1294 : runqueue_id_t)
  : clist_t :=
  let 'RunqueueId (rq_1295) :=
    rq_1294 in 
  let 'Clist ((tail_1296, next_idxs_1297)) :=
    x_1293 in 
  let '(tail_1296) :=
    if (array_index (tail_1296) (@cast _ uint32 _ (rq_1295))) !=.? (
      sentinel_v):bool then (let tail_1296 :=
        array_upd tail_1296 (@cast _ uint32 _ (rq_1295)) (array_index (
            next_idxs_1297) (@cast _ uint32 _ (array_index (tail_1296) (
                @cast _ uint32 _ (rq_1295))))) in 
      (tail_1296)) else ((tail_1296)) in 
  Clist ((tail_1296, next_idxs_1297)).

Inductive run_queue_t :=
| RunQueue : (int32 × clist_t) -> run_queue_t.

Definition runqueue_new  : run_queue_t :=
  RunQueue ((@repr WORDSIZE32 0, clist_new )).

Definition runqueue_add
  (y_1298 : run_queue_t)
  (n_1299 : thread_id_t)
  (rq_1300 : runqueue_id_t)
  : run_queue_t :=
  let 'RunqueueId (rq_u8_1301) :=
    rq_1300 in 
  let 'RunQueue ((bitcache_1302, queues_1303)) :=
    y_1298 in 
  let bitcache_1302 :=
    (bitcache_1302) .| ((@repr WORDSIZE32 1) shift_left (@cast _ uint32 _ (
          rq_u8_1301))) in 
  let queues_1303 :=
    clist_push (queues_1303) (n_1299) (rq_1300) in 
  RunQueue ((bitcache_1302, queues_1303)).

Definition runqueue_del
  (y_1304 : run_queue_t)
  (n_1305 : thread_id_t)
  (rq_1306 : runqueue_id_t)
  : run_queue_t :=
  let 'RunqueueId (rq_u8_1307) :=
    rq_1306 in 
  let 'RunQueue ((bitcache_1308, queues_1309)) :=
    y_1304 in 
  let '(queues_1310, popped_1311) :=
    clist_pop_head (queues_1309) (rq_1306) in 
  let '(bitcache_1308) :=
    if clist_is_empty (queues_1310) (rq_1306):bool then (let bitcache_1308 :=
        (bitcache_1308) .& (not ((@repr WORDSIZE32 1) shift_left (
              @cast _ uint32 _ (rq_u8_1307)))) in 
      (bitcache_1308)) else ((bitcache_1308)) in 
  RunQueue ((bitcache_1308, queues_1310)).

Definition runqueue_ffs (val_1312 : int32) : int32 :=
  (pub_u32 (uint32_bits_v)) .- (pub_uint32_leading_zeros (val_1312)).

Definition runqueue_get_next (y_1313 : run_queue_t) : (option int8) :=
  let 'RunQueue ((bitcache_1314, queues_1315)) :=
    y_1313 in 
  let rq_ffs_1316 : int32 :=
    runqueue_ffs ((bitcache_1314)) in 
  let out_1317 : (option int8) :=
    @None int8 in 
  let '(out_1317) :=
    if (rq_ffs_1316) >.? (@repr WORDSIZE32 0):bool then (
      let rq_1318 : runqueue_id_t :=
        RunqueueId (@cast _ uint8 _ ((rq_ffs_1316) .- (@repr WORDSIZE32 1))) in 
      let out_1317 :=
        clist_peek_head (queues_1315) (rq_1318) in 
      (out_1317)) else ((out_1317)) in 
  out_1317.

Definition runqueue_advance
  (y_1319 : run_queue_t)
  (rq_1320 : runqueue_id_t)
  : run_queue_t :=
  let 'RunQueue ((bitcache_1321, queues_1322)) :=
    y_1319 in 
  let queues_1322 :=
    clist_advance (queues_1322) (rq_1320) in 
  RunQueue ((bitcache_1321, queues_1322)).

