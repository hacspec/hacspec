(** This file was automatically generated using Hacspec **)
Set Warnings "-notation-overridden,-ambiguous-paths".
Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
Require Import Hacspec_Lib.

Definition block_size_v : uint_size :=
  usize 128.

Definition len_size_v : uint_size :=
  usize 16.

Definition k_size_v : uint_size :=
  usize 80.

Definition hash_size_v : uint_size :=
  (usize 512) / (usize 8).

Definition block_t := nseq (uint8) (block_size_v).

Definition op_table_type_t := nseq (uint_size) (usize 12).

Definition sha512_digest_t := nseq (uint8) (hash_size_v).

Definition round_constants_table_t := nseq (uint64) (k_size_v).

Definition hash_t := nseq (uint64) (usize 8).

Definition ch (x_2343 : uint64) (y_2344 : uint64) (z_2345 : uint64)  : uint64 :=
  ((x_2343) .& (y_2344)) .^ ((not (x_2343)) .& (z_2345)).

Definition maj
  (x_2346 : uint64)
  (y_2347 : uint64)
  (z_2348 : uint64)
  
  : uint64 :=
  ((x_2346) .& (y_2347)) .^ (((x_2346) .& (z_2348)) .^ ((y_2347) .& (z_2348))).

Definition op_table_v : op_table_type_t :=
  array_from_list uint_size (let l :=
      [
        usize 28;
        usize 34;
        usize 39;
        usize 14;
        usize 18;
        usize 41;
        usize 1;
        usize 8;
        usize 7;
        usize 19;
        usize 61;
        usize 6
      ] in  l).

Definition k_table_v : round_constants_table_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 4794697086780616226) : int64;
        secret (@repr WORDSIZE64 8158064640168781261) : int64;
        secret (@repr WORDSIZE64 13096744586834688815) : int64;
        secret (@repr WORDSIZE64 16840607885511220156) : int64;
        secret (@repr WORDSIZE64 4131703408338449720) : int64;
        secret (@repr WORDSIZE64 6480981068601479193) : int64;
        secret (@repr WORDSIZE64 10538285296894168987) : int64;
        secret (@repr WORDSIZE64 12329834152419229976) : int64;
        secret (@repr WORDSIZE64 15566598209576043074) : int64;
        secret (@repr WORDSIZE64 1334009975649890238) : int64;
        secret (@repr WORDSIZE64 2608012711638119052) : int64;
        secret (@repr WORDSIZE64 6128411473006802146) : int64;
        secret (@repr WORDSIZE64 8268148722764581231) : int64;
        secret (@repr WORDSIZE64 9286055187155687089) : int64;
        secret (@repr WORDSIZE64 11230858885718282805) : int64;
        secret (@repr WORDSIZE64 13951009754708518548) : int64;
        secret (@repr WORDSIZE64 16472876342353939154) : int64;
        secret (@repr WORDSIZE64 17275323862435702243) : int64;
        secret (@repr WORDSIZE64 1135362057144423861) : int64;
        secret (@repr WORDSIZE64 2597628984639134821) : int64;
        secret (@repr WORDSIZE64 3308224258029322869) : int64;
        secret (@repr WORDSIZE64 5365058923640841347) : int64;
        secret (@repr WORDSIZE64 6679025012923562964) : int64;
        secret (@repr WORDSIZE64 8573033837759648693) : int64;
        secret (@repr WORDSIZE64 10970295158949994411) : int64;
        secret (@repr WORDSIZE64 12119686244451234320) : int64;
        secret (@repr WORDSIZE64 12683024718118986047) : int64;
        secret (@repr WORDSIZE64 13788192230050041572) : int64;
        secret (@repr WORDSIZE64 14330467153632333762) : int64;
        secret (@repr WORDSIZE64 15395433587784984357) : int64;
        secret (@repr WORDSIZE64 489312712824947311) : int64;
        secret (@repr WORDSIZE64 1452737877330783856) : int64;
        secret (@repr WORDSIZE64 2861767655752347644) : int64;
        secret (@repr WORDSIZE64 3322285676063803686) : int64;
        secret (@repr WORDSIZE64 5560940570517711597) : int64;
        secret (@repr WORDSIZE64 5996557281743188959) : int64;
        secret (@repr WORDSIZE64 7280758554555802590) : int64;
        secret (@repr WORDSIZE64 8532644243296465576) : int64;
        secret (@repr WORDSIZE64 9350256976987008742) : int64;
        secret (@repr WORDSIZE64 10552545826968843579) : int64;
        secret (@repr WORDSIZE64 11727347734174303076) : int64;
        secret (@repr WORDSIZE64 12113106623233404929) : int64;
        secret (@repr WORDSIZE64 14000437183269869457) : int64;
        secret (@repr WORDSIZE64 14369950271660146224) : int64;
        secret (@repr WORDSIZE64 15101387698204529176) : int64;
        secret (@repr WORDSIZE64 15463397548674623760) : int64;
        secret (@repr WORDSIZE64 17586052441742319658) : int64;
        secret (@repr WORDSIZE64 1182934255886127544) : int64;
        secret (@repr WORDSIZE64 1847814050463011016) : int64;
        secret (@repr WORDSIZE64 2177327727835720531) : int64;
        secret (@repr WORDSIZE64 2830643537854262169) : int64;
        secret (@repr WORDSIZE64 3796741975233480872) : int64;
        secret (@repr WORDSIZE64 4115178125766777443) : int64;
        secret (@repr WORDSIZE64 5681478168544905931) : int64;
        secret (@repr WORDSIZE64 6601373596472566643) : int64;
        secret (@repr WORDSIZE64 7507060721942968483) : int64;
        secret (@repr WORDSIZE64 8399075790359081724) : int64;
        secret (@repr WORDSIZE64 8693463985226723168) : int64;
        secret (@repr WORDSIZE64 9568029438360202098) : int64;
        secret (@repr WORDSIZE64 10144078919501101548) : int64;
        secret (@repr WORDSIZE64 10430055236837252648) : int64;
        secret (@repr WORDSIZE64 11840083180663258601) : int64;
        secret (@repr WORDSIZE64 13761210420658862357) : int64;
        secret (@repr WORDSIZE64 14299343276471374635) : int64;
        secret (@repr WORDSIZE64 14566680578165727644) : int64;
        secret (@repr WORDSIZE64 15097957966210449927) : int64;
        secret (@repr WORDSIZE64 16922976911328602910) : int64;
        secret (@repr WORDSIZE64 17689382322260857208) : int64;
        secret (@repr WORDSIZE64 500013540394364858) : int64;
        secret (@repr WORDSIZE64 748580250866718886) : int64;
        secret (@repr WORDSIZE64 1242879168328830382) : int64;
        secret (@repr WORDSIZE64 1977374033974150939) : int64;
        secret (@repr WORDSIZE64 2944078676154940804) : int64;
        secret (@repr WORDSIZE64 3659926193048069267) : int64;
        secret (@repr WORDSIZE64 4368137639120453308) : int64;
        secret (@repr WORDSIZE64 4836135668995329356) : int64;
        secret (@repr WORDSIZE64 5532061633213252278) : int64;
        secret (@repr WORDSIZE64 6448918945643986474) : int64;
        secret (@repr WORDSIZE64 6902733635092675308) : int64;
        secret (@repr WORDSIZE64 7801388544844847127) : int64
      ] in  l).

Definition hash_init_v : hash_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 7640891576956012808) : int64;
        secret (@repr WORDSIZE64 13503953896175478587) : int64;
        secret (@repr WORDSIZE64 4354685564936845355) : int64;
        secret (@repr WORDSIZE64 11912009170470909681) : int64;
        secret (@repr WORDSIZE64 5840696475078001361) : int64;
        secret (@repr WORDSIZE64 11170449401992604703) : int64;
        secret (@repr WORDSIZE64 2270897969802886507) : int64;
        secret (@repr WORDSIZE64 6620516959819538809) : int64
      ] in  l).

Definition sigma
  (x_2349 : uint64)
  (i_2350 : uint_size)
  (op_2351 : uint_size)
  
  : uint64 :=
  let tmp_2352 : uint64 :=
    uint64_rotate_right (x_2349) (array_index (op_table_v) (((usize 3) * (
            i_2350)) + (usize 2))) in 
  let '(tmp_2352) :=
    if (op_2351) =.? (usize 0):bool then (let tmp_2352 :=
        (x_2349) shift_right (array_index (op_table_v) (((usize 3) * (
                i_2350)) + (usize 2))) in 
      (tmp_2352)) else ((tmp_2352)) in 
  ((uint64_rotate_right (x_2349) (array_index (op_table_v) ((usize 3) * (
            i_2350)))) .^ (uint64_rotate_right (x_2349) (array_index (
          op_table_v) (((usize 3) * (i_2350)) + (usize 1))))) .^ (tmp_2352).

Definition schedule (block_2353 : block_t)  : round_constants_table_t :=
  let b_2354 : seq uint64 :=
    array_to_be_uint64s (block_2353) in 
  let s_2355 : round_constants_table_t :=
    array_new_ (default : uint64) (k_size_v) in 
  let s_2355 :=
    foldi (usize 0) (k_size_v) (fun i_2356 s_2355 =>
      let '(s_2355) :=
        if (i_2356) <.? (usize 16):bool then (let s_2355 :=
            array_upd s_2355 (i_2356) (seq_index (b_2354) (i_2356)) in 
          (s_2355)) else (let t16_2357 : uint64 :=
            array_index (s_2355) ((i_2356) - (usize 16)) in 
          let t15_2358 : uint64 :=
            array_index (s_2355) ((i_2356) - (usize 15)) in 
          let t7_2359 : uint64 :=
            array_index (s_2355) ((i_2356) - (usize 7)) in 
          let t2_2360 : uint64 :=
            array_index (s_2355) ((i_2356) - (usize 2)) in 
          let s1_2361 : uint64 :=
            sigma (t2_2360) (usize 3) (usize 0) in 
          let s0_2362 : uint64 :=
            sigma (t15_2358) (usize 2) (usize 0) in 
          let s_2355 :=
            array_upd s_2355 (i_2356) ((((s1_2361) .+ (t7_2359)) .+ (
                  s0_2362)) .+ (t16_2357)) in 
          (s_2355)) in 
      (s_2355))
    s_2355 in 
  s_2355.

Definition shuffle
  (ws_2363 : round_constants_table_t)
  (hashi_2364 : hash_t)
  
  : hash_t :=
  let h_2365 : hash_t :=
    hashi_2364 in 
  let h_2365 :=
    foldi (usize 0) (k_size_v) (fun i_2366 h_2365 =>
      let a0_2367 : uint64 :=
        array_index (h_2365) (usize 0) in 
      let b0_2368 : uint64 :=
        array_index (h_2365) (usize 1) in 
      let c0_2369 : uint64 :=
        array_index (h_2365) (usize 2) in 
      let d0_2370 : uint64 :=
        array_index (h_2365) (usize 3) in 
      let e0_2371 : uint64 :=
        array_index (h_2365) (usize 4) in 
      let f0_2372 : uint64 :=
        array_index (h_2365) (usize 5) in 
      let g0_2373 : uint64 :=
        array_index (h_2365) (usize 6) in 
      let h0_2374 : uint64 :=
        array_index (h_2365) (usize 7) in 
      let t1_2375 : uint64 :=
        ((((h0_2374) .+ (sigma (e0_2371) (usize 1) (usize 1))) .+ (ch (
                e0_2371) (f0_2372) (g0_2373))) .+ (array_index (k_table_v) (
              i_2366))) .+ (array_index (ws_2363) (i_2366)) in 
      let t2_2376 : uint64 :=
        (sigma (a0_2367) (usize 0) (usize 1)) .+ (maj (a0_2367) (b0_2368) (
            c0_2369)) in 
      let h_2365 :=
        array_upd h_2365 (usize 0) ((t1_2375) .+ (t2_2376)) in 
      let h_2365 :=
        array_upd h_2365 (usize 1) (a0_2367) in 
      let h_2365 :=
        array_upd h_2365 (usize 2) (b0_2368) in 
      let h_2365 :=
        array_upd h_2365 (usize 3) (c0_2369) in 
      let h_2365 :=
        array_upd h_2365 (usize 4) ((d0_2370) .+ (t1_2375)) in 
      let h_2365 :=
        array_upd h_2365 (usize 5) (e0_2371) in 
      let h_2365 :=
        array_upd h_2365 (usize 6) (f0_2372) in 
      let h_2365 :=
        array_upd h_2365 (usize 7) (g0_2373) in 
      (h_2365))
    h_2365 in 
  h_2365.

Definition compress (block_2377 : block_t) (h_in_2378 : hash_t)  : hash_t :=
  let s_2379 : round_constants_table_t :=
    schedule (block_2377) in 
  let h_2380 : hash_t :=
    shuffle (s_2379) (h_in_2378) in 
  let h_2380 :=
    foldi (usize 0) (usize 8) (fun i_2381 h_2380 =>
      let h_2380 :=
        array_upd h_2380 (i_2381) ((array_index (h_2380) (i_2381)) .+ (
            array_index (h_in_2378) (i_2381))) in 
      (h_2380))
    h_2380 in 
  h_2380.

Definition hash (msg_2382 : byte_seq)  : sha512_digest_t :=
  let h_2383 : hash_t :=
    hash_init_v in 
  let last_block_2384 : block_t :=
    array_new_ (default : uint8) (block_size_v) in 
  let last_block_len_2385 : uint_size :=
    usize 0 in 
  let '(h_2383, last_block_2384, last_block_len_2385) :=
    foldi (usize 0) (seq_num_chunks (msg_2382) (block_size_v)) (fun i_2386 '(
        h_2383,
        last_block_2384,
        last_block_len_2385
      ) =>
      let '(block_len_2387, block_2388) :=
        seq_get_chunk (msg_2382) (block_size_v) (i_2386) in 
      let '(h_2383, last_block_2384, last_block_len_2385) :=
        if (block_len_2387) <.? (block_size_v):bool then (let last_block_2384 :=
            array_update_start (array_new_ (default : uint8) (block_size_v)) (
              block_2388) in 
          let last_block_len_2385 :=
            block_len_2387 in 
          (h_2383, last_block_2384, last_block_len_2385)) else (
          let compress_input_2389 : block_t :=
            array_from_seq (block_size_v) (block_2388) in 
          let h_2383 :=
            compress (compress_input_2389) (h_2383) in 
          (h_2383, last_block_2384, last_block_len_2385)) in 
      (h_2383, last_block_2384, last_block_len_2385))
    (h_2383, last_block_2384, last_block_len_2385) in 
  let last_block_2384 :=
    array_upd last_block_2384 (last_block_len_2385) (secret (
        @repr WORDSIZE8 128) : int8) in 
  let len_bist_2390 : uint128 :=
    secret (pub_u128 ((seq_len (msg_2382)) * (usize 8))) : int128 in 
  let '(h_2383, last_block_2384) :=
    if (last_block_len_2385) <.? ((block_size_v) - (len_size_v)):bool then (
      let last_block_2384 :=
        array_update (last_block_2384) ((block_size_v) - (len_size_v)) (
          array_to_seq (uint128_to_be_bytes (len_bist_2390))) in 
      let h_2383 :=
        compress (last_block_2384) (h_2383) in 
      (h_2383, last_block_2384)) else (let pad_block_2391 : block_t :=
        array_new_ (default : uint8) (block_size_v) in 
      let pad_block_2391 :=
        array_update (pad_block_2391) ((block_size_v) - (len_size_v)) (
          array_to_seq (uint128_to_be_bytes (len_bist_2390))) in 
      let h_2383 :=
        compress (last_block_2384) (h_2383) in 
      let h_2383 :=
        compress (pad_block_2391) (h_2383) in 
      (h_2383, last_block_2384)) in 
  array_from_seq (hash_size_v) (array_to_be_bytes (h_2383)).

Definition sha512 (msg_2392 : byte_seq)  : sha512_digest_t :=
  hash (msg_2392).

