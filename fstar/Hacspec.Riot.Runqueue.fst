module Hacspec.Riot.Runqueue

#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"

open FStar.Mul

open Hacspec.Lib

let uint32_bits:uint_size = (usize 4) * (usize 8)

let n_queues:uint_size = usize 20

let n_threads:uint_size = usize 30

let sentinel:pub_uint8 = pub_u8 0xff
noeq
type runqueue_id = | RunqueueId_runqueue_id : pub_uint8 -> runqueue_id
noeq
type thread_id = | ThreadId_thread_id : pub_uint8 -> thread_id

type tail = lseq (pub_uint8) (n_queues)

type next_ids = lseq (pub_uint8) (n_threads)
noeq
type clist = | Clist_clist : (tail & next_ids) -> clist

let clist_new () : clist =
  let tail_0 = array_new_ (pub_u8 0x0) (n_queues) in
  let tail_0 =
    foldi (usize 0)
      (array_len (tail_0))
      (fun i_1 tail_0 ->
          let tail_0 = array_upd tail_0 (i_1) (sentinel) in
          (tail_0))
      (tail_0)
  in
  let next_idxs_2 = array_new_ (pub_u8 0x0) (n_threads) in
  let next_idxs_2 =
    foldi (usize 0)
      (array_len (next_idxs_2))
      (fun i_3 next_idxs_2 ->
          let next_idxs_2 = array_upd next_idxs_2 (i_3) (sentinel) in
          (next_idxs_2))
      (next_idxs_2)
  in
  Clist_clist ((tail_0, next_idxs_2))

let clist_is_empty (x_4: clist) (rq_5: runqueue_id) : bool =
  let RunqueueId_runqueue_id rq_6 = rq_5 in
  let Clist_clist (tail_7, next_ids_8) = x_4 in
  (array_index (tail_7) (v (cast U32 PUB (rq_6)))) = (sentinel)

let clist_push (x_9: clist) (n_10: thread_id) (rq_11: runqueue_id) : clist =
  let RunqueueId_runqueue_id rq_12 = rq_11 in
  let ThreadId_thread_id n_13 = n_10 in
  let Clist_clist (tail_14, next_idxs_15) = x_9 in
  let tail_14, next_idxs_15 =
    if (array_index (next_idxs_15) (v (cast U32 PUB (n_13)))) = (sentinel)
    then
      let tail_14, next_idxs_15 =
        if (array_index (tail_14) (v (cast U32 PUB (rq_12)))) = (sentinel)
        then
          let tail_14 = array_upd tail_14 (v (cast U32 PUB (rq_12))) (n_13) in
          let next_idxs_15 = array_upd next_idxs_15 (v (cast U32 PUB (n_13))) (n_13) in
          (tail_14, next_idxs_15)
        else
          let next_idxs_15 =
            array_upd next_idxs_15
              (v (cast U32 PUB (n_13)))
              (array_index (next_idxs_15)
                  (v (cast U32 PUB (array_index (tail_14) (v (cast U32 PUB (rq_12)))))))
          in
          let next_idxs_15 =
            array_upd next_idxs_15
              (v (cast U32 PUB (array_index (tail_14) (v (cast U32 PUB (rq_12))))))
              (n_13)
          in
          let tail_14 = array_upd tail_14 (v (cast U32 PUB (rq_12))) (n_13) in
          (tail_14, next_idxs_15)
      in
      (tail_14, next_idxs_15)
    else (tail_14, next_idxs_15)
  in
  Clist_clist ((tail_14, next_idxs_15))

let clist_pop_head (x_16: clist) (rq_17: runqueue_id) : (clist & (option pub_uint8)) =
  let RunqueueId_runqueue_id rq_18 = rq_17 in
  let Clist_clist (tail_19, next_idxs_20) = x_16 in
  let out_21:(option pub_uint8) = None in
  let tail_19, next_idxs_20, out_21 =
    if (array_index (tail_19) (v (cast U32 PUB (rq_18)))) = (sentinel)
    then (tail_19, next_idxs_20, out_21)
    else
      let head_22 =
        array_index (next_idxs_20)
          (v (cast U32 PUB (array_index (tail_19) (v (cast U32 PUB (rq_18))))))
      in
      let tail_19, next_idxs_20 =
        if (head_22) = (array_index (tail_19) (v (cast U32 PUB (rq_18))))
        then
          let tail_19 = array_upd tail_19 (v (cast U32 PUB (rq_18))) (sentinel) in
          (tail_19, next_idxs_20)
        else
          let next_idxs_20 =
            array_upd next_idxs_20
              (v (cast U32 PUB (array_index (tail_19) (v (cast U32 PUB (rq_18))))))
              (array_index (next_idxs_20) (v (cast U32 PUB (head_22))))
          in
          (tail_19, next_idxs_20)
      in
      let next_idxs_20 = array_upd next_idxs_20 (v (cast U32 PUB (head_22))) (sentinel) in
      let out_21 = Some (head_22) in
      (tail_19, next_idxs_20, out_21)
  in
  (Clist_clist ((tail_19, next_idxs_20)), out_21)

let clist_peek_head (x_23: clist) (rq_24: runqueue_id) : (option pub_uint8) =
  let RunqueueId_runqueue_id rq_25 = rq_24 in
  let Clist_clist (tail_26, next_idxs_27) = x_23 in
  if ((array_index (tail_26) (v (cast U32 PUB (rq_25)))) = (sentinel))
  then (None)
  else
    (Some
      (array_index (next_idxs_27)
          (v (cast U32 PUB (array_index (tail_26) (v (cast U32 PUB (rq_25))))))))

let clist_advance (x_28: clist) (rq_29: runqueue_id) : clist =
  let RunqueueId_runqueue_id rq_30 = rq_29 in
  let Clist_clist (tail_31, next_idxs_32) = x_28 in
  let tail_31 =
    if (array_index (tail_31) (v (cast U32 PUB (rq_30)))) <> (sentinel)
    then
      let tail_31 =
        array_upd tail_31
          (v (cast U32 PUB (rq_30)))
          (array_index (next_idxs_32)
              (v (cast U32 PUB (array_index (tail_31) (v (cast U32 PUB (rq_30)))))))
      in
      (tail_31)
    else (tail_31)
  in
  Clist_clist ((tail_31, next_idxs_32))
noeq
type run_queue = | RunQueue_run_queue : (pub_uint32 & clist) -> run_queue

let runqueue_new () : run_queue = RunQueue_run_queue ((pub_u32 0x0, clist_new ()))

let runqueue_add (y_33: run_queue) (n_34: thread_id) (rq_35: runqueue_id) : run_queue =
  let RunqueueId_runqueue_id rq_u8_36 = rq_35 in
  let RunQueue_run_queue (bitcache_37, queues_38) = y_33 in
  let bitcache_37 = (bitcache_37) |. ((pub_u32 0x1) `shift_left` (cast U32 PUB (rq_u8_36))) in
  let queues_38 = clist_push (queues_38) (n_34) (rq_35) in
  RunQueue_run_queue ((bitcache_37, queues_38))

let runqueue_del (y_39: run_queue) (n_40: thread_id) (rq_41: runqueue_id) : run_queue =
  let RunqueueId_runqueue_id rq_u8_42 = rq_41 in
  let RunQueue_run_queue (bitcache_43, queues_44) = y_39 in
  let queues_45, popped_46 = clist_pop_head (queues_44) (rq_41) in
  let bitcache_43 =
    if clist_is_empty (queues_45) (rq_41)
    then
      let bitcache_43 =
        (bitcache_43) &. (~.((pub_u32 0x1) `shift_left` (cast U32 PUB (rq_u8_42))))
      in
      (bitcache_43)
    else (bitcache_43)
  in
  RunQueue_run_queue ((bitcache_43, queues_45))

let runqueue_ffs (val_47: pub_uint32) : pub_uint32 =
  (pub_u32 (uint32_bits)) -. (pub_uint32_leading_zeros (val_47))

let runqueue_get_next (y_48: run_queue) : (option pub_uint8) =
  let RunQueue_run_queue (bitcache_49, queues_50) = y_48 in
  let rq_ffs_51 = runqueue_ffs (pub_uint32_clone (bitcache_49)) in
  let out_52 = None in
  let out_52 =
    if (rq_ffs_51) >. (pub_u32 0x0)
    then
      let rq_53 = RunqueueId_runqueue_id (cast U8 PUB ((rq_ffs_51) -. (pub_u32 0x1))) in
      let out_52 = clist_peek_head (queues_50) (rq_53) in
      (out_52)
    else (out_52)
  in
  out_52

let runqueue_advance (y_54: run_queue) (rq_55: runqueue_id) : run_queue =
  let RunQueue_run_queue (bitcache_56, queues_57) = y_54 in
  let queues_57 = clist_advance (queues_57) (rq_55) in
  RunQueue_run_queue ((bitcache_56, queues_57))

