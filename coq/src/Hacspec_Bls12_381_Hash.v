(** This file was automatically generated using Hacspec **)
Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
Require Import Hacspec_Bls12_381.

Require Import Hacspec_Lib.

Require Import Hacspec_Sha256.

Definition fp_hash_canvas_t := nseq (int8) (64).
Definition fp_hash_t :=
  nat_mod 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab.

Definition arr_fp_t := nseq (uint64) (usize 6).

Definition b_in_bytes_v : uint_size :=
  usize 32.

Definition s_in_bytes_v : uint_size :=
  usize 64.

Definition l_v : uint_size :=
  usize 64.

Definition p_1_2_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 936899308823769933) : int64;
        secret (@repr WORDSIZE64 2706051889235351147) : int64;
        secret (@repr WORDSIZE64 12843041017062132063) : int64;
        secret (@repr WORDSIZE64 12941209323636816658) : int64;
        secret (@repr WORDSIZE64 1105070755758604287) : int64;
        secret (@repr WORDSIZE64 15924587544893707605) : int64
      ] in  l).

Definition p_1_4_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 468449654411884966) : int64;
        secret (@repr WORDSIZE64 10576397981472451381) : int64;
        secret (@repr WORDSIZE64 15644892545385841839) : int64;
        secret (@repr WORDSIZE64 15693976698673184137) : int64;
        secret (@repr WORDSIZE64 552535377879302143) : int64;
        secret (@repr WORDSIZE64 17185665809301629611) : int64
      ] in  l).

Definition p_3_4_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 468449654411884966) : int64;
        secret (@repr WORDSIZE64 10576397981472451381) : int64;
        secret (@repr WORDSIZE64 15644892545385841839) : int64;
        secret (@repr WORDSIZE64 15693976698673184137) : int64;
        secret (@repr WORDSIZE64 552535377879302143) : int64;
        secret (@repr WORDSIZE64 17185665809301629610) : int64
      ] in  l).

Definition expand_message_xmd
  (msg_327 : byte_seq)
  (dst_328 : byte_seq)
  (len_in_bytes_329 : uint_size)
  : byte_seq :=
  let ell_330 : uint_size :=
    (((len_in_bytes_329) + (b_in_bytes_v)) - (usize 1)) / (b_in_bytes_v) in 
  let dst_prime_331 : seq uint8 :=
    seq_push (dst_328) (uint8_from_usize (seq_len (dst_328))) in 
  let z_pad_332 : seq uint8 :=
    seq_new_ (default) (s_in_bytes_v) in 
  let l_i_b_str_333 : seq uint8 :=
    seq_new_ (default) (usize 2) in 
  let l_i_b_str_333 :=
    seq_upd l_i_b_str_333 (usize 0) (uint8_from_usize ((len_in_bytes_329) / (
          usize 256))) in 
  let l_i_b_str_333 :=
    seq_upd l_i_b_str_333 (usize 1) (uint8_from_usize (len_in_bytes_329)) in 
  let msg_prime_334 : seq uint8 :=
    seq_concat (seq_concat (seq_concat (seq_concat (z_pad_332) (msg_327)) (
          l_i_b_str_333)) (seq_new_ (default) (usize 1))) (dst_prime_331) in 
  let b_0_335 : seq uint8 :=
    seq_from_seq (array_to_seq (hash (msg_prime_334))) in 
  let b_i_336 : seq uint8 :=
    seq_from_seq (array_to_seq (hash (seq_concat (seq_push (b_0_335) (secret (
              @repr WORDSIZE8 1) : int8)) (dst_prime_331)))) in 
  let uniform_bytes_337 : seq uint8 :=
    seq_from_seq (b_i_336) in 
  let '(b_i_336, uniform_bytes_337) :=
    foldi (usize 2) ((ell_330) + (usize 1)) (fun i_338 '(
        b_i_336,
        uniform_bytes_337
      ) =>
      let t_339 : seq uint8 :=
        seq_from_seq (b_0_335) in 
      let b_i_336 :=
        seq_from_seq (array_to_seq (hash (seq_concat (seq_push ((
                  t_339) seq_xor (b_i_336)) (uint8_from_usize (i_338))) (
              dst_prime_331)))) in 
      let uniform_bytes_337 :=
        seq_concat (uniform_bytes_337) (b_i_336) in 
      (b_i_336, uniform_bytes_337))
    (b_i_336, uniform_bytes_337) in 
  seq_truncate (uniform_bytes_337) (len_in_bytes_329).

Definition fp_hash_to_field
  (msg_340 : byte_seq)
  (dst_341 : byte_seq)
  (count_342 : uint_size)
  : seq fp_t :=
  let len_in_bytes_343 : uint_size :=
    (count_342) * (l_v) in 
  let uniform_bytes_344 : seq uint8 :=
    expand_message_xmd (msg_340) (dst_341) (len_in_bytes_343) in 
  let output_345 : seq fp_t :=
    seq_new_ (default) (count_342) in 
  let output_345 :=
    foldi (usize 0) (count_342) (fun i_346 output_345 =>
      let elm_offset_347 : uint_size :=
        (l_v) * (i_346) in 
      let tv_348 : seq uint8 :=
        seq_slice (uniform_bytes_344) (elm_offset_347) (l_v) in 
      let u_i_349 : fp_t :=
        nat_mod_from_byte_seq_be (seq_slice (nat_mod_to_byte_seq_be (
              nat_mod_from_byte_seq_be (tv_348) : fp_hash_t)) (usize 16) (
            usize 48)) : fp_t in 
      let output_345 :=
        seq_upd output_345 (i_346) (u_i_349) in 
      (output_345))
    output_345 in 
  output_345.

Definition fp_sgn0 (x_350 : fp_t) : bool :=
  ((x_350) rem (nat_mod_two )) =.? (nat_mod_one ).

Definition fp_is_square (x_351 : fp_t) : bool :=
  let c1_352 : fp_t :=
    nat_mod_from_byte_seq_be (array_to_be_bytes (p_1_2_v)) : fp_t in 
  let tv_353 : fp_t :=
    nat_mod_pow_self (x_351) (c1_352) in 
  ((tv_353) =.? (nat_mod_zero )) || ((tv_353) =.? (nat_mod_one )).

Definition fp_sqrt (x_354 : fp_t) : fp_t :=
  let c1_355 : fp_t :=
    nat_mod_from_byte_seq_be (array_to_be_bytes (p_1_4_v)) : fp_t in 
  nat_mod_pow_self (x_354) (c1_355).

Definition g1_curve_func (x_356 : fp_t) : fp_t :=
  (((x_356) *% (x_356)) *% (x_356)) +% (nat_mod_from_literal (_) (
      @repr WORDSIZE128 4) : fp_t).

Definition g1_map_to_curve_svdw (u_357 : fp_t) : g1_t :=
  let z_358 : fp_t :=
    (nat_mod_zero ) -% (nat_mod_from_literal (_) (
        @repr WORDSIZE128 3) : fp_t) in 
  let gz_359 : fp_t :=
    g1_curve_func (z_358) in 
  let tv1_360 : fp_t :=
    ((u_357) *% (u_357)) *% (gz_359) in 
  let tv2_361 : fp_t :=
    (nat_mod_one ) +% (tv1_360) in 
  let tv1_362 : fp_t :=
    (nat_mod_one ) -% (tv1_360) in 
  let tv3_363 : fp_t :=
    nat_mod_inv ((tv1_362) *% (tv2_361)) in 
  let tv4_364 : fp_t :=
    fp_sqrt (((nat_mod_zero ) -% (gz_359)) *% (((nat_mod_from_literal (_) (
              @repr WORDSIZE128 3) : fp_t) *% (z_358)) *% (z_358))) in 
  let '(tv4_364) :=
    if fp_sgn0 (tv4_364):bool then (let tv4_364 :=
        (nat_mod_zero ) -% (tv4_364) in 
      (tv4_364)) else ((tv4_364)) in 
  let tv5_365 : fp_t :=
    (((u_357) *% (tv1_362)) *% (tv3_363)) *% (tv4_364) in 
  let tv6_366 : fp_t :=
    (((nat_mod_zero ) -% (nat_mod_from_literal (_) (
            @repr WORDSIZE128 4) : fp_t)) *% (gz_359)) *% (nat_mod_inv (((
            nat_mod_from_literal (_) (@repr WORDSIZE128 3) : fp_t) *% (
            z_358)) *% (z_358))) in 
  let x1_367 : fp_t :=
    (((nat_mod_zero ) -% (z_358)) *% (nat_mod_inv (nat_mod_two ))) -% (
      tv5_365) in 
  let x2_368 : fp_t :=
    (((nat_mod_zero ) -% (z_358)) *% (nat_mod_inv (nat_mod_two ))) +% (
      tv5_365) in 
  let x3_369 : fp_t :=
    (z_358) +% (((tv6_366) *% (((tv2_361) *% (tv2_361)) *% (tv3_363))) *% (((
            tv2_361) *% (tv2_361)) *% (tv3_363))) in 
  let x_370 : fp_t :=
    (if (fp_is_square (g1_curve_func (x1_367))):bool then (x1_367) else ((if (
            fp_is_square (g1_curve_func (x2_368))):bool then (x2_368) else (
            x3_369)))) in 
  let y_371 : fp_t :=
    fp_sqrt (g1_curve_func (x_370)) in 
  let '(y_371) :=
    if (fp_sgn0 (u_357)) !=.? (fp_sgn0 (y_371)):bool then (let y_371 :=
        (nat_mod_zero ) -% (y_371) in 
      (y_371)) else ((y_371)) in 
  (x_370, y_371, false).

Definition g1_clear_cofactor (x_372 : g1_t) : g1_t :=
  let h_eff_373 : scalar_t :=
    nat_mod_from_literal (_) (
      @repr WORDSIZE128 15132376222941642753) : scalar_t in 
  g1mul (h_eff_373) (x_372).

Definition g1_hash_to_curve_svdw
  (msg_374 : byte_seq)
  (dst_375 : byte_seq)
  : g1_t :=
  let u_376 : seq fp_t :=
    fp_hash_to_field (msg_374) (dst_375) (usize 2) in 
  let q0_377 : (fp_t × fp_t × bool) :=
    g1_map_to_curve_svdw (seq_index (u_376) (usize 0)) in 
  let q1_378 : (fp_t × fp_t × bool) :=
    g1_map_to_curve_svdw (seq_index (u_376) (usize 1)) in 
  let r_379 : (fp_t × fp_t × bool) :=
    g1add (q0_377) (q1_378) in 
  let p_380 : (fp_t × fp_t × bool) :=
    g1_clear_cofactor (r_379) in 
  p_380.

Definition g1_encode_to_curve_svdw
  (msg_381 : byte_seq)
  (dst_382 : byte_seq)
  : g1_t :=
  let u_383 : seq fp_t :=
    fp_hash_to_field (msg_381) (dst_382) (usize 1) in 
  let q_384 : (fp_t × fp_t × bool) :=
    g1_map_to_curve_svdw (seq_index (u_383) (usize 0)) in 
  let p_385 : (fp_t × fp_t × bool) :=
    g1_clear_cofactor (q_384) in 
  p_385.

Definition fp2_hash_to_field
  (msg_386 : byte_seq)
  (dst_387 : byte_seq)
  (count_388 : uint_size)
  : seq fp2_t :=
  let len_in_bytes_389 : uint_size :=
    ((count_388) * (usize 2)) * (l_v) in 
  let uniform_bytes_390 : seq uint8 :=
    expand_message_xmd (msg_386) (dst_387) (len_in_bytes_389) in 
  let output_391 : seq (fp_t × fp_t) :=
    seq_new_ (default) (count_388) in 
  let output_391 :=
    foldi (usize 0) (count_388) (fun i_392 output_391 =>
      let elm_offset_393 : uint_size :=
        ((l_v) * (i_392)) * (usize 2) in 
      let tv_394 : seq uint8 :=
        seq_slice (uniform_bytes_390) (elm_offset_393) (l_v) in 
      let e_1_395 : fp_t :=
        nat_mod_from_byte_seq_be (seq_slice (nat_mod_to_byte_seq_be (
              nat_mod_from_byte_seq_be (tv_394) : fp_hash_t)) (usize 16) (
            usize 48)) : fp_t in 
      let elm_offset_396 : uint_size :=
        (l_v) * ((usize 1) + ((i_392) * (usize 2))) in 
      let tv_397 : seq uint8 :=
        seq_slice (uniform_bytes_390) (elm_offset_396) (l_v) in 
      let e_2_398 : fp_t :=
        nat_mod_from_byte_seq_be (seq_slice (nat_mod_to_byte_seq_be (
              nat_mod_from_byte_seq_be (tv_397) : fp_hash_t)) (usize 16) (
            usize 48)) : fp_t in 
      let output_391 :=
        seq_upd output_391 (i_392) ((e_1_395, e_2_398)) in 
      (output_391))
    output_391 in 
  output_391.

Definition fp2_sgn0 (x_399 : fp2_t) : bool :=
  let '(x0_400, x1_401) :=
    x_399 in 
  let sign_0_402 : bool :=
    fp_sgn0 (x0_400) in 
  let zero_0_403 : bool :=
    (x0_400) =.? (nat_mod_zero ) in 
  let sign_1_404 : bool :=
    fp_sgn0 (x1_401) in 
  (sign_0_402) || ((zero_0_403) && (sign_1_404)).

Definition fp2_is_square (x_405 : fp2_t) : bool :=
  let c1_406 : fp_t :=
    nat_mod_from_byte_seq_be (array_to_be_bytes (p_1_2_v)) : fp_t in 
  let '(x1_407, x2_408) :=
    x_405 in 
  let tv1_409 : fp_t :=
    (x1_407) *% (x1_407) in 
  let tv2_410 : fp_t :=
    (x2_408) *% (x2_408) in 
  let tv1_411 : fp_t :=
    (tv1_409) +% (tv2_410) in 
  let tv1_412 : fp_t :=
    nat_mod_pow_self (tv1_411) (c1_406) in 
  let neg1_413 : fp_t :=
    (nat_mod_zero ) -% (nat_mod_one ) in 
  (tv1_412) !=.? (neg1_413).

Definition fp2exp (n_414 : fp2_t) (k_415 : fp_t) : fp2_t :=
  let c_416 : (fp_t × fp_t) :=
    fp2fromfp (nat_mod_one ) in 
  let c_416 :=
    foldi (usize 0) (usize 381) (fun i_417 c_416 =>
      let c_416 :=
        fp2mul (c_416) (c_416) in 
      let '(c_416) :=
        if nat_mod_bit (k_415) ((usize 380) - (i_417)):bool then (let c_416 :=
            fp2mul (c_416) (n_414) in 
          (c_416)) else ((c_416)) in 
      (c_416))
    c_416 in 
  c_416.

Definition fp2_sqrt (a_418 : fp2_t) : fp2_t :=
  let c1_419 : fp_t :=
    nat_mod_from_byte_seq_be (array_to_be_bytes (p_3_4_v)) : fp_t in 
  let c2_420 : fp_t :=
    nat_mod_from_byte_seq_be (array_to_be_bytes (p_1_2_v)) : fp_t in 
  let a1_421 : (fp_t × fp_t) :=
    fp2exp (a_418) (c1_419) in 
  let alpha_422 : (fp_t × fp_t) :=
    fp2mul (a1_421) (fp2mul (a1_421) (a_418)) in 
  let x0_423 : (fp_t × fp_t) :=
    fp2mul (a1_421) (a_418) in 
  let neg1_424 : (fp_t × fp_t) :=
    ((nat_mod_zero ) -% (nat_mod_one ), nat_mod_zero ) in 
  let b_425 : (fp_t × fp_t) :=
    fp2exp (fp2add (fp2fromfp (nat_mod_one )) (alpha_422)) (c2_420) in 
  (if ((alpha_422) =.? (neg1_424)):bool then (fp2mul ((
          nat_mod_zero ,
          nat_mod_one 
        )) (x0_423)) else (fp2mul (b_425) (x0_423))).

Definition g2_curve_func (x_426 : fp2_t) : fp2_t :=
  fp2add (fp2mul (x_426) (fp2mul (x_426) (x_426))) ((
      nat_mod_from_literal (_) (@repr WORDSIZE128 4) : fp_t,
      nat_mod_from_literal (_) (@repr WORDSIZE128 4) : fp_t
    )).

Definition g2_map_to_curve_svdw (u_427 : fp2_t) : g2_t :=
  let z_428 : (fp_t × fp_t) :=
    fp2neg (fp2fromfp (nat_mod_one )) in 
  let gz_429 : (fp_t × fp_t) :=
    g2_curve_func (z_428) in 
  let tv1_430 : (fp_t × fp_t) :=
    fp2mul (fp2mul (u_427) (u_427)) (gz_429) in 
  let tv2_431 : (fp_t × fp_t) :=
    fp2add (fp2fromfp (nat_mod_one )) (tv1_430) in 
  let tv1_432 : (fp_t × fp_t) :=
    fp2sub (fp2fromfp (nat_mod_one )) (tv1_430) in 
  let tv3_433 : (fp_t × fp_t) :=
    fp2inv (fp2mul (tv1_432) (tv2_431)) in 
  let tv4_434 : (fp_t × fp_t) :=
    fp2_sqrt (fp2mul (fp2neg (gz_429)) (fp2mul (fp2fromfp (
            nat_mod_from_literal (_) (@repr WORDSIZE128 3) : fp_t)) (fp2mul (
            z_428) (z_428)))) in 
  let '(tv4_434) :=
    if fp2_sgn0 (tv4_434):bool then (let tv4_434 :=
        fp2neg (tv4_434) in 
      (tv4_434)) else ((tv4_434)) in 
  let tv5_435 : (fp_t × fp_t) :=
    fp2mul (fp2mul (fp2mul (u_427) (tv1_432)) (tv3_433)) (tv4_434) in 
  let tv6_436 : (fp_t × fp_t) :=
    fp2mul (fp2mul (fp2neg (fp2fromfp (nat_mod_from_literal (_) (
              @repr WORDSIZE128 4) : fp_t))) (gz_429)) (fp2inv (fp2mul (
          fp2fromfp (nat_mod_from_literal (_) (@repr WORDSIZE128 3) : fp_t)) (
          fp2mul (z_428) (z_428)))) in 
  let x1_437 : (fp_t × fp_t) :=
    fp2sub (fp2mul (fp2neg (z_428)) (fp2inv (fp2fromfp (nat_mod_two )))) (
      tv5_435) in 
  let x2_438 : (fp_t × fp_t) :=
    fp2add (fp2mul (fp2neg (z_428)) (fp2inv (fp2fromfp (nat_mod_two )))) (
      tv5_435) in 
  let tv7_439 : (fp_t × fp_t) :=
    fp2mul (fp2mul (tv2_431) (tv2_431)) (tv3_433) in 
  let x3_440 : (fp_t × fp_t) :=
    fp2add (z_428) (fp2mul (tv6_436) (fp2mul (tv7_439) (tv7_439))) in 
  let x_441 : (fp_t × fp_t) :=
    (if (fp2_is_square (g2_curve_func (x1_437))):bool then (x1_437) else ((if (
            fp2_is_square (g2_curve_func (x2_438))):bool then (x2_438) else (
            x3_440)))) in 
  let y_442 : (fp_t × fp_t) :=
    fp2_sqrt (g2_curve_func (x_441)) in 
  let '(y_442) :=
    if (fp2_sgn0 (u_427)) !=.? (fp2_sgn0 (y_442)):bool then (let y_442 :=
        fp2neg (y_442) in 
      (y_442)) else ((y_442)) in 
  (x_441, y_442, false).

Definition psi (p_443 : g2_t) : g2_t :=
  let c1_444 : (fp_t × fp_t) :=
    fp2inv (fp2exp ((nat_mod_one , nat_mod_one )) (((nat_mod_zero ) -% (
            nat_mod_one )) *% (nat_mod_inv (nat_mod_from_literal (_) (
              @repr WORDSIZE128 3) : fp_t)))) in 
  let c2_445 : (fp_t × fp_t) :=
    fp2inv (fp2exp ((nat_mod_one , nat_mod_one )) (((nat_mod_zero ) -% (
            nat_mod_one )) *% (nat_mod_inv (nat_mod_two )))) in 
  let '(x_446, y_447, inf_448) :=
    p_443 in 
  let qx_449 : (fp_t × fp_t) :=
    fp2mul (c1_444) (fp2conjugate (x_446)) in 
  let qy_450 : (fp_t × fp_t) :=
    fp2mul (c2_445) (fp2conjugate (y_447)) in 
  (qx_449, qy_450, inf_448).

Definition g2_clear_cofactor (p_451 : g2_t) : g2_t :=
  let c1_452 : scalar_t :=
    nat_mod_from_literal (_) (
      @repr WORDSIZE128 15132376222941642752) : scalar_t in 
  let t1_453 : ((fp_t × fp_t) × (fp_t × fp_t) × bool) :=
    g2mul (c1_452) (p_451) in 
  let t1_454 : ((fp_t × fp_t) × (fp_t × fp_t) × bool) :=
    g2neg (t1_453) in 
  let t2_455 : ((fp_t × fp_t) × (fp_t × fp_t) × bool) :=
    psi (p_451) in 
  let t3_456 : ((fp_t × fp_t) × (fp_t × fp_t) × bool) :=
    g2double (p_451) in 
  let t3_457 : ((fp_t × fp_t) × (fp_t × fp_t) × bool) :=
    psi (psi (t3_456)) in 
  let t3_458 : ((fp_t × fp_t) × (fp_t × fp_t) × bool) :=
    g2add (t3_457) (g2neg (t2_455)) in 
  let t2_459 : ((fp_t × fp_t) × (fp_t × fp_t) × bool) :=
    g2add (t1_454) (t2_455) in 
  let t2_460 : ((fp_t × fp_t) × (fp_t × fp_t) × bool) :=
    g2mul (c1_452) (t2_459) in 
  let t2_461 : ((fp_t × fp_t) × (fp_t × fp_t) × bool) :=
    g2neg (t2_460) in 
  let t3_462 : ((fp_t × fp_t) × (fp_t × fp_t) × bool) :=
    g2add (t3_458) (t2_461) in 
  let t3_463 : ((fp_t × fp_t) × (fp_t × fp_t) × bool) :=
    g2add (t3_462) (g2neg (t1_454)) in 
  let q_464 : ((fp_t × fp_t) × (fp_t × fp_t) × bool) :=
    g2add (t3_463) (g2neg (p_451)) in 
  q_464.

Definition g2_hash_to_curve_svdw
  (msg_465 : byte_seq)
  (dst_466 : byte_seq)
  : g2_t :=
  let u_467 : seq fp2_t :=
    fp2_hash_to_field (msg_465) (dst_466) (usize 2) in 
  let q0_468 : ((fp_t × fp_t) × (fp_t × fp_t) × bool) :=
    g2_map_to_curve_svdw (seq_index (u_467) (usize 0)) in 
  let q1_469 : ((fp_t × fp_t) × (fp_t × fp_t) × bool) :=
    g2_map_to_curve_svdw (seq_index (u_467) (usize 1)) in 
  let r_470 : ((fp_t × fp_t) × (fp_t × fp_t) × bool) :=
    g2add (q0_468) (q1_469) in 
  let p_471 : ((fp_t × fp_t) × (fp_t × fp_t) × bool) :=
    g2_clear_cofactor (r_470) in 
  p_471.

Definition g2_encode_to_curve_svdw
  (msg_472 : byte_seq)
  (dst_473 : byte_seq)
  : g2_t :=
  let u_474 : seq fp2_t :=
    fp2_hash_to_field (msg_472) (dst_473) (usize 1) in 
  let q_475 : ((fp_t × fp_t) × (fp_t × fp_t) × bool) :=
    g2_map_to_curve_svdw (seq_index (u_474) (usize 0)) in 
  let p_476 : ((fp_t × fp_t) × (fp_t × fp_t) × bool) :=
    g2_clear_cofactor (q_475) in 
  p_476.

Definition g1_iso_a_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 5707120929990979) : int64;
        secret (@repr WORDSIZE64 4425131892511951234) : int64;
        secret (@repr WORDSIZE64 12748169179688756904) : int64;
        secret (@repr WORDSIZE64 15629909748249821612) : int64;
        secret (@repr WORDSIZE64 10994253769421683071) : int64;
        secret (@repr WORDSIZE64 6698022561392380957) : int64
      ] in  l).

Definition g1_iso_b_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1360808972976160816) : int64;
        secret (@repr WORDSIZE64 111203405409480251) : int64;
        secret (@repr WORDSIZE64 2312248699302920304) : int64;
        secret (@repr WORDSIZE64 11581500465278574325) : int64;
        secret (@repr WORDSIZE64 6495071758858381989) : int64;
        secret (@repr WORDSIZE64 15117538217124375520) : int64
      ] in  l).

Definition g1_xnum_k_0_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1270119733718627136) : int64;
        secret (@repr WORDSIZE64 13261148298159854981) : int64;
        secret (@repr WORDSIZE64 7723742117508874335) : int64;
        secret (@repr WORDSIZE64 17465657917644792520) : int64;
        secret (@repr WORDSIZE64 6201670911048166766) : int64;
        secret (@repr WORDSIZE64 12586459670690286007) : int64
      ] in  l).

Definition g1_xnum_k_1_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1668951808976071471) : int64;
        secret (@repr WORDSIZE64 398773841247578140) : int64;
        secret (@repr WORDSIZE64 8941869963990959127) : int64;
        secret (@repr WORDSIZE64 17682789360670468203) : int64;
        secret (@repr WORDSIZE64 5204176168283587414) : int64;
        secret (@repr WORDSIZE64 16732261237459223483) : int64
      ] in  l).

Definition g1_xnum_k_2_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 960393023080265964) : int64;
        secret (@repr WORDSIZE64 2094253841180170779) : int64;
        secret (@repr WORDSIZE64 14844748873776858085) : int64;
        secret (@repr WORDSIZE64 7528018573573808732) : int64;
        secret (@repr WORDSIZE64 10776056440809943711) : int64;
        secret (@repr WORDSIZE64 16147550488514976944) : int64
      ] in  l).

Definition g1_xnum_k_3_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1691355743628586423) : int64;
        secret (@repr WORDSIZE64 5622191986793862162) : int64;
        secret (@repr WORDSIZE64 15561595211679121189) : int64;
        secret (@repr WORDSIZE64 17416319752018800771) : int64;
        secret (@repr WORDSIZE64 5996228842464768403) : int64;
        secret (@repr WORDSIZE64 14245880009877842017) : int64
      ] in  l).

Definition g1_xnum_k_4_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1051997788391994435) : int64;
        secret (@repr WORDSIZE64 7368650625050054228) : int64;
        secret (@repr WORDSIZE64 11086623519836470079) : int64;
        secret (@repr WORDSIZE64 607681821319080984) : int64;
        secret (@repr WORDSIZE64 10978131499682789316) : int64;
        secret (@repr WORDSIZE64 5842660658088809945) : int64
      ] in  l).

Definition g1_xnum_k_5_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1598992431623377919) : int64;
        secret (@repr WORDSIZE64 130921168661596853) : int64;
        secret (@repr WORDSIZE64 15797696746983946651) : int64;
        secret (@repr WORDSIZE64 11444679715590672272) : int64;
        secret (@repr WORDSIZE64 11567228658253249817) : int64;
        secret (@repr WORDSIZE64 14777367860349315459) : int64
      ] in  l).

Definition g1_xnum_k_6_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 967946631563726121) : int64;
        secret (@repr WORDSIZE64 7653628713030275775) : int64;
        secret (@repr WORDSIZE64 12760252618317466849) : int64;
        secret (@repr WORDSIZE64 10378793938173061930) : int64;
        secret (@repr WORDSIZE64 10205808941053849290) : int64;
        secret (@repr WORDSIZE64 15985511645807504772) : int64
      ] in  l).

Definition g1_xnum_k_7_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1709149555065084898) : int64;
        secret (@repr WORDSIZE64 16750075057192140371) : int64;
        secret (@repr WORDSIZE64 3849985779734105521) : int64;
        secret (@repr WORDSIZE64 11998370262181639475) : int64;
        secret (@repr WORDSIZE64 4159013751748851119) : int64;
        secret (@repr WORDSIZE64 11298218755092433038) : int64
      ] in  l).

Definition g1_xnum_k_8_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 580186936973955012) : int64;
        secret (@repr WORDSIZE64 8903813505199544589) : int64;
        secret (@repr WORDSIZE64 14140024565662700916) : int64;
        secret (@repr WORDSIZE64 11728946595272970718) : int64;
        secret (@repr WORDSIZE64 5738313744366653077) : int64;
        secret (@repr WORDSIZE64 7886252005760951063) : int64
      ] in  l).

Definition g1_xnum_k_9_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1628930385436977092) : int64;
        secret (@repr WORDSIZE64 3318087848058654498) : int64;
        secret (@repr WORDSIZE64 15937899882900905113) : int64;
        secret (@repr WORDSIZE64 7449821001803307903) : int64;
        secret (@repr WORDSIZE64 11752436998487615353) : int64;
        secret (@repr WORDSIZE64 9161465579737517214) : int64
      ] in  l).

Definition g1_xnum_k_10_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1167027828517898210) : int64;
        secret (@repr WORDSIZE64 8275623842221021965) : int64;
        secret (@repr WORDSIZE64 18049808134997311382) : int64;
        secret (@repr WORDSIZE64 15351349873550116966) : int64;
        secret (@repr WORDSIZE64 17769927732099571180) : int64;
        secret (@repr WORDSIZE64 14584871380308065147) : int64
      ] in  l).

Definition g1_xnum_k_11_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 495550047642324592) : int64;
        secret (@repr WORDSIZE64 13627494601717575229) : int64;
        secret (@repr WORDSIZE64 3591512392926246844) : int64;
        secret (@repr WORDSIZE64 2576269112800734056) : int64;
        secret (@repr WORDSIZE64 14000314106239596831) : int64;
        secret (@repr WORDSIZE64 12234233096825917993) : int64
      ] in  l).

Definition g1_xden_k_0_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 633474091881273774) : int64;
        secret (@repr WORDSIZE64 1779737893574802031) : int64;
        secret (@repr WORDSIZE64 132274872219551930) : int64;
        secret (@repr WORDSIZE64 11283074393783708770) : int64;
        secret (@repr WORDSIZE64 13067430171545714168) : int64;
        secret (@repr WORDSIZE64 11041975239630265116) : int64
      ] in  l).

Definition g1_xden_k_1_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1321272531362356291) : int64;
        secret (@repr WORDSIZE64 5238936591227237942) : int64;
        secret (@repr WORDSIZE64 8089002360232247308) : int64;
        secret (@repr WORDSIZE64 82967328719421271) : int64;
        secret (@repr WORDSIZE64 1430641118356186857) : int64;
        secret (@repr WORDSIZE64 16557527386785790975) : int64
      ] in  l).

Definition g1_xden_k_2_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 804282852993868382) : int64;
        secret (@repr WORDSIZE64 9311163821600184607) : int64;
        secret (@repr WORDSIZE64 8037026956533927121) : int64;
        secret (@repr WORDSIZE64 18205324308570099372) : int64;
        secret (@repr WORDSIZE64 15466434890074226396) : int64;
        secret (@repr WORDSIZE64 18213183315621985817) : int64
      ] in  l).

Definition g1_xden_k_3_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 234844145893171966) : int64;
        secret (@repr WORDSIZE64 14428037799351479124) : int64;
        secret (@repr WORDSIZE64 6559532710647391569) : int64;
        secret (@repr WORDSIZE64 6110444250091843536) : int64;
        secret (@repr WORDSIZE64 5293652763671852484) : int64;
        secret (@repr WORDSIZE64 1373009181854280920) : int64
      ] in  l).

Definition g1_xden_k_4_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1416629893867312296) : int64;
        secret (@repr WORDSIZE64 751851957792514173) : int64;
        secret (@repr WORDSIZE64 18437674587247370939) : int64;
        secret (@repr WORDSIZE64 10190314345946351322) : int64;
        secret (@repr WORDSIZE64 11228207967368476701) : int64;
        secret (@repr WORDSIZE64 6025034940388909598) : int64
      ] in  l).

Definition g1_xden_k_5_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1041270466333271993) : int64;
        secret (@repr WORDSIZE64 6140956605115975401) : int64;
        secret (@repr WORDSIZE64 4131830461445745997) : int64;
        secret (@repr WORDSIZE64 739642499118176303) : int64;
        secret (@repr WORDSIZE64 8358912131254619921) : int64;
        secret (@repr WORDSIZE64 13847998906088228005) : int64
      ] in  l).

Definition g1_xden_k_6_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 536714149743900185) : int64;
        secret (@repr WORDSIZE64 1098328982230230817) : int64;
        secret (@repr WORDSIZE64 6273329123533496713) : int64;
        secret (@repr WORDSIZE64 5633448088282521244) : int64;
        secret (@repr WORDSIZE64 16894043798660571244) : int64;
        secret (@repr WORDSIZE64 17016134625831438906) : int64
      ] in  l).

Definition g1_xden_k_7_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1488347500898461874) : int64;
        secret (@repr WORDSIZE64 3509418672874520985) : int64;
        secret (@repr WORDSIZE64 7962192351555381416) : int64;
        secret (@repr WORDSIZE64 1843909372225399896) : int64;
        secret (@repr WORDSIZE64 1127511003250156243) : int64;
        secret (@repr WORDSIZE64 1294742680819751518) : int64
      ] in  l).

Definition g1_xden_k_8_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 725340084226051970) : int64;
        secret (@repr WORDSIZE64 6814521545734988748) : int64;
        secret (@repr WORDSIZE64 16176803544133875307) : int64;
        secret (@repr WORDSIZE64 8363199516777220149) : int64;
        secret (@repr WORDSIZE64 252877309218538352) : int64;
        secret (@repr WORDSIZE64 5149562959837648449) : int64
      ] in  l).

Definition g1_xden_k_9_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 675470927100193492) : int64;
        secret (@repr WORDSIZE64 5146891164735334016) : int64;
        secret (@repr WORDSIZE64 17762958817130696759) : int64;
        secret (@repr WORDSIZE64 8565656522589412373) : int64;
        secret (@repr WORDSIZE64 10599026333335446784) : int64;
        secret (@repr WORDSIZE64 3270603789344496906) : int64
      ] in  l).

Definition g1_ynum_k_0_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 652344406751465184) : int64;
        secret (@repr WORDSIZE64 2710356675495255290) : int64;
        secret (@repr WORDSIZE64 1273695771440998738) : int64;
        secret (@repr WORDSIZE64 3121750372618945491) : int64;
        secret (@repr WORDSIZE64 14775319642720936898) : int64;
        secret (@repr WORDSIZE64 13733803417833814835) : int64
      ] in  l).

Definition g1_ynum_k_1_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1389807578337138705) : int64;
        secret (@repr WORDSIZE64 15352831428748068483) : int64;
        secret (@repr WORDSIZE64 1307144967559264317) : int64;
        secret (@repr WORDSIZE64 1121505450578652468) : int64;
        secret (@repr WORDSIZE64 15475889019760388287) : int64;
        secret (@repr WORDSIZE64 16183658160488302230) : int64
      ] in  l).

Definition g1_ynum_k_2_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 57553299067792998) : int64;
        secret (@repr WORDSIZE64 17628079362768849300) : int64;
        secret (@repr WORDSIZE64 2689461337731570914) : int64;
        secret (@repr WORDSIZE64 14070580367580990887) : int64;
        secret (@repr WORDSIZE64 15162865775551710499) : int64;
        secret (@repr WORDSIZE64 13321614990632673782) : int64
      ] in  l).

Definition g1_ynum_k_3_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 141972750621744161) : int64;
        secret (@repr WORDSIZE64 8689824239172478807) : int64;
        secret (@repr WORDSIZE64 15288216298323671324) : int64;
        secret (@repr WORDSIZE64 712874875091754233) : int64;
        secret (@repr WORDSIZE64 16014900032503684588) : int64;
        secret (@repr WORDSIZE64 11976580453200426187) : int64
      ] in  l).

Definition g1_ynum_k_4_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 633886036738506515) : int64;
        secret (@repr WORDSIZE64 6678644607214234052) : int64;
        secret (@repr WORDSIZE64 1825425679455244472) : int64;
        secret (@repr WORDSIZE64 8755912272271186652) : int64;
        secret (@repr WORDSIZE64 3379943669301788840) : int64;
        secret (@repr WORDSIZE64 4735212769449148123) : int64
      ] in  l).

Definition g1_ynum_k_5_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1612358804494830442) : int64;
        secret (@repr WORDSIZE64 2454990789666711200) : int64;
        secret (@repr WORDSIZE64 8405916841409361853) : int64;
        secret (@repr WORDSIZE64 8525415512662168654) : int64;
        secret (@repr WORDSIZE64 2323684950984523890) : int64;
        secret (@repr WORDSIZE64 11074978966450447856) : int64
      ] in  l).

Definition g1_ynum_k_6_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 336375361001233340) : int64;
        secret (@repr WORDSIZE64 12882959944969186108) : int64;
        secret (@repr WORDSIZE64 16671121624101127371) : int64;
        secret (@repr WORDSIZE64 5922586712221110071) : int64;
        secret (@repr WORDSIZE64 5163511947597922654) : int64;
        secret (@repr WORDSIZE64 14511152726087948018) : int64
      ] in  l).

Definition g1_ynum_k_7_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 686738286210365551) : int64;
        secret (@repr WORDSIZE64 16039894141796533876) : int64;
        secret (@repr WORDSIZE64 1660145734357211167) : int64;
        secret (@repr WORDSIZE64 18231571463891878950) : int64;
        secret (@repr WORDSIZE64 4825120264949852469) : int64;
        secret (@repr WORDSIZE64 11627815551290637097) : int64
      ] in  l).

Definition g1_ynum_k_8_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 719520515476580427) : int64;
        secret (@repr WORDSIZE64 16756942182913253819) : int64;
        secret (@repr WORDSIZE64 10320769399998235244) : int64;
        secret (@repr WORDSIZE64 2200974244968450750) : int64;
        secret (@repr WORDSIZE64 7626373186594408355) : int64;
        secret (@repr WORDSIZE64 6933025920263103879) : int64
      ] in  l).

Definition g1_ynum_k_9_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1016611174344998325) : int64;
        secret (@repr WORDSIZE64 2466492548686891555) : int64;
        secret (@repr WORDSIZE64 14135124294293452542) : int64;
        secret (@repr WORDSIZE64 475233659467912251) : int64;
        secret (@repr WORDSIZE64 11186783513499056751) : int64;
        secret (@repr WORDSIZE64 3147922594245844016) : int64
      ] in  l).

Definition g1_ynum_k_10_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1833315000454533566) : int64;
        secret (@repr WORDSIZE64 1007974600900082579) : int64;
        secret (@repr WORDSIZE64 14785260176242854207) : int64;
        secret (@repr WORDSIZE64 15066861003931772432) : int64;
        secret (@repr WORDSIZE64 3584647998681889532) : int64;
        secret (@repr WORDSIZE64 16722834201330696498) : int64
      ] in  l).

Definition g1_ynum_k_11_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1780164921828767454) : int64;
        secret (@repr WORDSIZE64 13337622794239929804) : int64;
        secret (@repr WORDSIZE64 5923739534552515142) : int64;
        secret (@repr WORDSIZE64 3345046972101780530) : int64;
        secret (@repr WORDSIZE64 5321510883028162054) : int64;
        secret (@repr WORDSIZE64 14846055306840460686) : int64
      ] in  l).

Definition g1_ynum_k_12_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 799438051374502809) : int64;
        secret (@repr WORDSIZE64 15083972834952036164) : int64;
        secret (@repr WORDSIZE64 8838227588559581326) : int64;
        secret (@repr WORDSIZE64 13846054168121598783) : int64;
        secret (@repr WORDSIZE64 488730451382505970) : int64;
        secret (@repr WORDSIZE64 958146249756188408) : int64
      ] in  l).

Definition g1_ynum_k_13_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 163716820423854747) : int64;
        secret (@repr WORDSIZE64 8285498163857659356) : int64;
        secret (@repr WORDSIZE64 8465424830341846400) : int64;
        secret (@repr WORDSIZE64 1433942577299613084) : int64;
        secret (@repr WORDSIZE64 14325828012864645732) : int64;
        secret (@repr WORDSIZE64 4817114329354076467) : int64
      ] in  l).

Definition g1_ynum_k_14_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 414658151749832465) : int64;
        secret (@repr WORDSIZE64 189531577938912252) : int64;
        secret (@repr WORDSIZE64 6802473390048830824) : int64;
        secret (@repr WORDSIZE64 15684647020317539556) : int64;
        secret (@repr WORDSIZE64 7755485098777620407) : int64;
        secret (@repr WORDSIZE64 9685868895687483979) : int64
      ] in  l).

Definition g1_ynum_k_15_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1578157964224562126) : int64;
        secret (@repr WORDSIZE64 5666948055268535989) : int64;
        secret (@repr WORDSIZE64 14634479491382401593) : int64;
        secret (@repr WORDSIZE64 6317940024988860850) : int64;
        secret (@repr WORDSIZE64 13142913832013798519) : int64;
        secret (@repr WORDSIZE64 338991247778166276) : int64
      ] in  l).

Definition g1_yden_k_0_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1590100849350973618) : int64;
        secret (@repr WORDSIZE64 5915497081334721257) : int64;
        secret (@repr WORDSIZE64 6924968209373727718) : int64;
        secret (@repr WORDSIZE64 17204633670617869946) : int64;
        secret (@repr WORDSIZE64 572916540828819565) : int64;
        secret (@repr WORDSIZE64 92203205520679873) : int64
      ] in  l).

Definition g1_yden_k_1_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1829261189398470686) : int64;
        secret (@repr WORDSIZE64 1877083417397643448) : int64;
        secret (@repr WORDSIZE64 9640042925497046428) : int64;
        secret (@repr WORDSIZE64 11862766565471805471) : int64;
        secret (@repr WORDSIZE64 8693114993904885301) : int64;
        secret (@repr WORDSIZE64 3672140328108400701) : int64
      ] in  l).

Definition g1_yden_k_2_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 400243331105348135) : int64;
        secret (@repr WORDSIZE64 8046435537999802711) : int64;
        secret (@repr WORDSIZE64 8702226981475745585) : int64;
        secret (@repr WORDSIZE64 879791671491744492) : int64;
        secret (@repr WORDSIZE64 11994630442058346377) : int64;
        secret (@repr WORDSIZE64 2172204746352322546) : int64
      ] in  l).

Definition g1_yden_k_3_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1637008473169220501) : int64;
        secret (@repr WORDSIZE64 17441636237435581649) : int64;
        secret (@repr WORDSIZE64 15066165676546511630) : int64;
        secret (@repr WORDSIZE64 1314387578457599809) : int64;
        secret (@repr WORDSIZE64 8247046336453711789) : int64;
        secret (@repr WORDSIZE64 12164906044230685718) : int64
      ] in  l).

Definition g1_yden_k_4_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 855930740911588324) : int64;
        secret (@repr WORDSIZE64 12685735333705453020) : int64;
        secret (@repr WORDSIZE64 14326404096614579120) : int64;
        secret (@repr WORDSIZE64 6066025509460822294) : int64;
        secret (@repr WORDSIZE64 11676450493790612973) : int64;
        secret (@repr WORDSIZE64 15724621714793234461) : int64
      ] in  l).

Definition g1_yden_k_5_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 637792788410719021) : int64;
        secret (@repr WORDSIZE64 11507373155986977154) : int64;
        secret (@repr WORDSIZE64 13186912195705886849) : int64;
        secret (@repr WORDSIZE64 14262012144631372388) : int64;
        secret (@repr WORDSIZE64 5328758613570342114) : int64;
        secret (@repr WORDSIZE64 199925847119476652) : int64
      ] in  l).

Definition g1_yden_k_6_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1612297190139091759) : int64;
        secret (@repr WORDSIZE64 14103733843373163083) : int64;
        secret (@repr WORDSIZE64 6840121186619029743) : int64;
        secret (@repr WORDSIZE64 6760859324815900753) : int64;
        secret (@repr WORDSIZE64 15418807805142572985) : int64;
        secret (@repr WORDSIZE64 4402853133867972444) : int64
      ] in  l).

Definition g1_yden_k_7_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1631410310868805610) : int64;
        secret (@repr WORDSIZE64 269334146695233390) : int64;
        secret (@repr WORDSIZE64 16547411811928854487) : int64;
        secret (@repr WORDSIZE64 18353100669930795314) : int64;
        secret (@repr WORDSIZE64 13339932232668798692) : int64;
        secret (@repr WORDSIZE64 6984591927261867737) : int64
      ] in  l).

Definition g1_yden_k_8_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1758313625630302499) : int64;
        secret (@repr WORDSIZE64 1881349400343039172) : int64;
        secret (@repr WORDSIZE64 18013005311323887904) : int64;
        secret (@repr WORDSIZE64 12377427846571989832) : int64;
        secret (@repr WORDSIZE64 5967237584920922243) : int64;
        secret (@repr WORDSIZE64 7720081932193848650) : int64
      ] in  l).

Definition g1_yden_k_9_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1619701357752249884) : int64;
        secret (@repr WORDSIZE64 16898074901591262352) : int64;
        secret (@repr WORDSIZE64 3609344159736760251) : int64;
        secret (@repr WORDSIZE64 5983130161189999867) : int64;
        secret (@repr WORDSIZE64 14355327869992416094) : int64;
        secret (@repr WORDSIZE64 3778226018344582997) : int64
      ] in  l).

Definition g1_yden_k_10_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 347606589330687421) : int64;
        secret (@repr WORDSIZE64 5255719044972187933) : int64;
        secret (@repr WORDSIZE64 11271894388753671721) : int64;
        secret (@repr WORDSIZE64 1033887512062764488) : int64;
        secret (@repr WORDSIZE64 8189165486932690436) : int64;
        secret (@repr WORDSIZE64 70004379462101672) : int64
      ] in  l).

Definition g1_yden_k_11_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 778202887894139711) : int64;
        secret (@repr WORDSIZE64 17691595219776375879) : int64;
        secret (@repr WORDSIZE64 9193253711563866834) : int64;
        secret (@repr WORDSIZE64 10092455202333888821) : int64;
        secret (@repr WORDSIZE64 1655469341950262250) : int64;
        secret (@repr WORDSIZE64 10845992994110574738) : int64
      ] in  l).

Definition g1_yden_k_12_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 781015344221683683) : int64;
        secret (@repr WORDSIZE64 14078588081290548374) : int64;
        secret (@repr WORDSIZE64 6067271023149908518) : int64;
        secret (@repr WORDSIZE64 9033357708497886086) : int64;
        secret (@repr WORDSIZE64 10592474449179118273) : int64;
        secret (@repr WORDSIZE64 2204988348113831372) : int64
      ] in  l).

Definition g1_yden_k_13_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 172830037692534587) : int64;
        secret (@repr WORDSIZE64 7101012286790006514) : int64;
        secret (@repr WORDSIZE64 13787308004332873665) : int64;
        secret (@repr WORDSIZE64 14660498759553796110) : int64;
        secret (@repr WORDSIZE64 4757234684169342080) : int64;
        secret (@repr WORDSIZE64 15130647872920159991) : int64
      ] in  l).

Definition g1_yden_k_14_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1013206390650290238) : int64;
        secret (@repr WORDSIZE64 7720336747103001025) : int64;
        secret (@repr WORDSIZE64 8197694151986493523) : int64;
        secret (@repr WORDSIZE64 3625112747029342752) : int64;
        secret (@repr WORDSIZE64 6675167463148394368) : int64;
        secret (@repr WORDSIZE64 4905905684016745359) : int64
      ] in  l).

Definition g1_simple_swu_iso (u_477 : fp_t) : (fp_t × fp_t) :=
  let z_478 : fp_t :=
    nat_mod_from_literal (_) (@repr WORDSIZE128 11) : fp_t in 
  let a_479 : fp_t :=
    nat_mod_from_byte_seq_be (array_to_be_bytes (g1_iso_a_v)) : fp_t in 
  let b_480 : fp_t :=
    nat_mod_from_byte_seq_be (array_to_be_bytes (g1_iso_b_v)) : fp_t in 
  let tv1_481 : fp_t :=
    nat_mod_inv ((((z_478) *% (z_478)) *% (nat_mod_exp (u_477) (
            @repr WORDSIZE32 4))) +% (((z_478) *% (u_477)) *% (u_477))) in 
  let x1_482 : fp_t :=
    (((nat_mod_zero ) -% (b_480)) *% (nat_mod_inv (a_479))) *% ((
        nat_mod_one ) +% (tv1_481)) in 
  let '(x1_482) :=
    if (tv1_481) =.? (nat_mod_zero ):bool then (let x1_482 :=
        (b_480) *% (nat_mod_inv ((z_478) *% (a_479))) in 
      (x1_482)) else ((x1_482)) in 
  let gx1_483 : fp_t :=
    ((nat_mod_exp (x1_482) (@repr WORDSIZE32 3)) +% ((a_479) *% (x1_482))) +% (
      b_480) in 
  let x2_484 : fp_t :=
    (((z_478) *% (u_477)) *% (u_477)) *% (x1_482) in 
  let gx2_485 : fp_t :=
    ((nat_mod_exp (x2_484) (@repr WORDSIZE32 3)) +% ((a_479) *% (x2_484))) +% (
      b_480) in 
  let '(x_486, y_487) :=
    (if (fp_is_square (gx1_483)):bool then ((x1_482, fp_sqrt (gx1_483))) else ((
          x2_484,
          fp_sqrt (gx2_485)
        ))) in 
  let '(y_487) :=
    if (fp_sgn0 (u_477)) !=.? (fp_sgn0 (y_487)):bool then (let y_487 :=
        (nat_mod_zero ) -% (y_487) in 
      (y_487)) else ((y_487)) in 
  (x_486, y_487).

Definition g1_isogeny_map (x_488 : fp_t) (y_489 : fp_t) : g1_t :=
  let xnum_k_490 : seq fp_t :=
    seq_new_ (default) (usize 12) in 
  let xnum_k_490 :=
    seq_upd xnum_k_490 (usize 0) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_xnum_k_0_v)) : fp_t) in 
  let xnum_k_490 :=
    seq_upd xnum_k_490 (usize 1) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_xnum_k_1_v)) : fp_t) in 
  let xnum_k_490 :=
    seq_upd xnum_k_490 (usize 2) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_xnum_k_2_v)) : fp_t) in 
  let xnum_k_490 :=
    seq_upd xnum_k_490 (usize 3) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_xnum_k_3_v)) : fp_t) in 
  let xnum_k_490 :=
    seq_upd xnum_k_490 (usize 4) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_xnum_k_4_v)) : fp_t) in 
  let xnum_k_490 :=
    seq_upd xnum_k_490 (usize 5) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_xnum_k_5_v)) : fp_t) in 
  let xnum_k_490 :=
    seq_upd xnum_k_490 (usize 6) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_xnum_k_6_v)) : fp_t) in 
  let xnum_k_490 :=
    seq_upd xnum_k_490 (usize 7) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_xnum_k_7_v)) : fp_t) in 
  let xnum_k_490 :=
    seq_upd xnum_k_490 (usize 8) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_xnum_k_8_v)) : fp_t) in 
  let xnum_k_490 :=
    seq_upd xnum_k_490 (usize 9) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_xnum_k_9_v)) : fp_t) in 
  let xnum_k_490 :=
    seq_upd xnum_k_490 (usize 10) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_xnum_k_10_v)) : fp_t) in 
  let xnum_k_490 :=
    seq_upd xnum_k_490 (usize 11) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_xnum_k_11_v)) : fp_t) in 
  let xden_k_491 : seq fp_t :=
    seq_new_ (default) (usize 10) in 
  let xden_k_491 :=
    seq_upd xden_k_491 (usize 0) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_xden_k_0_v)) : fp_t) in 
  let xden_k_491 :=
    seq_upd xden_k_491 (usize 1) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_xden_k_1_v)) : fp_t) in 
  let xden_k_491 :=
    seq_upd xden_k_491 (usize 2) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_xden_k_2_v)) : fp_t) in 
  let xden_k_491 :=
    seq_upd xden_k_491 (usize 3) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_xden_k_3_v)) : fp_t) in 
  let xden_k_491 :=
    seq_upd xden_k_491 (usize 4) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_xden_k_4_v)) : fp_t) in 
  let xden_k_491 :=
    seq_upd xden_k_491 (usize 5) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_xden_k_5_v)) : fp_t) in 
  let xden_k_491 :=
    seq_upd xden_k_491 (usize 6) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_xden_k_6_v)) : fp_t) in 
  let xden_k_491 :=
    seq_upd xden_k_491 (usize 7) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_xden_k_7_v)) : fp_t) in 
  let xden_k_491 :=
    seq_upd xden_k_491 (usize 8) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_xden_k_8_v)) : fp_t) in 
  let xden_k_491 :=
    seq_upd xden_k_491 (usize 9) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_xden_k_9_v)) : fp_t) in 
  let ynum_k_492 : seq fp_t :=
    seq_new_ (default) (usize 16) in 
  let ynum_k_492 :=
    seq_upd ynum_k_492 (usize 0) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_ynum_k_0_v)) : fp_t) in 
  let ynum_k_492 :=
    seq_upd ynum_k_492 (usize 1) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_ynum_k_1_v)) : fp_t) in 
  let ynum_k_492 :=
    seq_upd ynum_k_492 (usize 2) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_ynum_k_2_v)) : fp_t) in 
  let ynum_k_492 :=
    seq_upd ynum_k_492 (usize 3) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_ynum_k_3_v)) : fp_t) in 
  let ynum_k_492 :=
    seq_upd ynum_k_492 (usize 4) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_ynum_k_4_v)) : fp_t) in 
  let ynum_k_492 :=
    seq_upd ynum_k_492 (usize 5) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_ynum_k_5_v)) : fp_t) in 
  let ynum_k_492 :=
    seq_upd ynum_k_492 (usize 6) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_ynum_k_6_v)) : fp_t) in 
  let ynum_k_492 :=
    seq_upd ynum_k_492 (usize 7) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_ynum_k_7_v)) : fp_t) in 
  let ynum_k_492 :=
    seq_upd ynum_k_492 (usize 8) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_ynum_k_8_v)) : fp_t) in 
  let ynum_k_492 :=
    seq_upd ynum_k_492 (usize 9) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_ynum_k_9_v)) : fp_t) in 
  let ynum_k_492 :=
    seq_upd ynum_k_492 (usize 10) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_ynum_k_10_v)) : fp_t) in 
  let ynum_k_492 :=
    seq_upd ynum_k_492 (usize 11) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_ynum_k_11_v)) : fp_t) in 
  let ynum_k_492 :=
    seq_upd ynum_k_492 (usize 12) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_ynum_k_12_v)) : fp_t) in 
  let ynum_k_492 :=
    seq_upd ynum_k_492 (usize 13) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_ynum_k_13_v)) : fp_t) in 
  let ynum_k_492 :=
    seq_upd ynum_k_492 (usize 14) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_ynum_k_14_v)) : fp_t) in 
  let ynum_k_492 :=
    seq_upd ynum_k_492 (usize 15) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_ynum_k_15_v)) : fp_t) in 
  let yden_k_493 : seq fp_t :=
    seq_new_ (default) (usize 15) in 
  let yden_k_493 :=
    seq_upd yden_k_493 (usize 0) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_yden_k_0_v)) : fp_t) in 
  let yden_k_493 :=
    seq_upd yden_k_493 (usize 1) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_yden_k_1_v)) : fp_t) in 
  let yden_k_493 :=
    seq_upd yden_k_493 (usize 2) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_yden_k_2_v)) : fp_t) in 
  let yden_k_493 :=
    seq_upd yden_k_493 (usize 3) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_yden_k_3_v)) : fp_t) in 
  let yden_k_493 :=
    seq_upd yden_k_493 (usize 4) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_yden_k_4_v)) : fp_t) in 
  let yden_k_493 :=
    seq_upd yden_k_493 (usize 5) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_yden_k_5_v)) : fp_t) in 
  let yden_k_493 :=
    seq_upd yden_k_493 (usize 6) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_yden_k_6_v)) : fp_t) in 
  let yden_k_493 :=
    seq_upd yden_k_493 (usize 7) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_yden_k_7_v)) : fp_t) in 
  let yden_k_493 :=
    seq_upd yden_k_493 (usize 8) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_yden_k_8_v)) : fp_t) in 
  let yden_k_493 :=
    seq_upd yden_k_493 (usize 9) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_yden_k_9_v)) : fp_t) in 
  let yden_k_493 :=
    seq_upd yden_k_493 (usize 10) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_yden_k_10_v)) : fp_t) in 
  let yden_k_493 :=
    seq_upd yden_k_493 (usize 11) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_yden_k_11_v)) : fp_t) in 
  let yden_k_493 :=
    seq_upd yden_k_493 (usize 12) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_yden_k_12_v)) : fp_t) in 
  let yden_k_493 :=
    seq_upd yden_k_493 (usize 13) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_yden_k_13_v)) : fp_t) in 
  let yden_k_493 :=
    seq_upd yden_k_493 (usize 14) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_yden_k_14_v)) : fp_t) in 
  let xnum_494 : fp_t :=
    nat_mod_zero  in 
  let xx_495 : fp_t :=
    nat_mod_one  in 
  let '(xnum_494, xx_495) :=
    foldi (usize 0) (seq_len (xnum_k_490)) (fun i_496 '(xnum_494, xx_495) =>
      let xnum_494 :=
        (xnum_494) +% ((xx_495) *% (seq_index (xnum_k_490) (i_496))) in 
      let xx_495 :=
        (xx_495) *% (x_488) in 
      (xnum_494, xx_495))
    (xnum_494, xx_495) in 
  let xden_497 : fp_t :=
    nat_mod_zero  in 
  let xx_498 : fp_t :=
    nat_mod_one  in 
  let '(xden_497, xx_498) :=
    foldi (usize 0) (seq_len (xden_k_491)) (fun i_499 '(xden_497, xx_498) =>
      let xden_497 :=
        (xden_497) +% ((xx_498) *% (seq_index (xden_k_491) (i_499))) in 
      let xx_498 :=
        (xx_498) *% (x_488) in 
      (xden_497, xx_498))
    (xden_497, xx_498) in 
  let xden_497 :=
    (xden_497) +% (xx_498) in 
  let ynum_500 : fp_t :=
    nat_mod_zero  in 
  let xx_501 : fp_t :=
    nat_mod_one  in 
  let '(ynum_500, xx_501) :=
    foldi (usize 0) (seq_len (ynum_k_492)) (fun i_502 '(ynum_500, xx_501) =>
      let ynum_500 :=
        (ynum_500) +% ((xx_501) *% (seq_index (ynum_k_492) (i_502))) in 
      let xx_501 :=
        (xx_501) *% (x_488) in 
      (ynum_500, xx_501))
    (ynum_500, xx_501) in 
  let yden_503 : fp_t :=
    nat_mod_zero  in 
  let xx_504 : fp_t :=
    nat_mod_one  in 
  let '(yden_503, xx_504) :=
    foldi (usize 0) (seq_len (yden_k_493)) (fun i_505 '(yden_503, xx_504) =>
      let yden_503 :=
        (yden_503) +% ((xx_504) *% (seq_index (yden_k_493) (i_505))) in 
      let xx_504 :=
        (xx_504) *% (x_488) in 
      (yden_503, xx_504))
    (yden_503, xx_504) in 
  let yden_503 :=
    (yden_503) +% (xx_504) in 
  let xr_506 : fp_t :=
    (xnum_494) *% (nat_mod_inv (xden_497)) in 
  let yr_507 : fp_t :=
    ((y_489) *% (ynum_500)) *% (nat_mod_inv (yden_503)) in 
  let inf_508 : bool :=
    false in 
  let '(inf_508) :=
    if ((xden_497) =.? (nat_mod_zero )) || ((yden_503) =.? (
        nat_mod_zero )):bool then (let inf_508 :=
        true in 
      (inf_508)) else ((inf_508)) in 
  (xr_506, yr_507, inf_508).

Definition g1_map_to_curve_sswu (u_509 : fp_t) : g1_t :=
  let '(xp_510, yp_511) :=
    g1_simple_swu_iso (u_509) in 
  let p_512 : (fp_t × fp_t × bool) :=
    g1_isogeny_map (xp_510) (yp_511) in 
  p_512.

Definition g1_hash_to_curve_sswu
  (msg_513 : byte_seq)
  (dst_514 : byte_seq)
  : g1_t :=
  let u_515 : seq fp_t :=
    fp_hash_to_field (msg_513) (dst_514) (usize 2) in 
  let q0_516 : (fp_t × fp_t × bool) :=
    g1_map_to_curve_sswu (seq_index (u_515) (usize 0)) in 
  let q1_517 : (fp_t × fp_t × bool) :=
    g1_map_to_curve_sswu (seq_index (u_515) (usize 1)) in 
  let r_518 : (fp_t × fp_t × bool) :=
    g1add (q0_516) (q1_517) in 
  let p_519 : (fp_t × fp_t × bool) :=
    g1_clear_cofactor (r_518) in 
  p_519.

Definition g1_encode_to_curve_sswu
  (msg_520 : byte_seq)
  (dst_521 : byte_seq)
  : g1_t :=
  let u_522 : seq fp_t :=
    fp_hash_to_field (msg_520) (dst_521) (usize 1) in 
  let q_523 : (fp_t × fp_t × bool) :=
    g1_map_to_curve_sswu (seq_index (u_522) (usize 0)) in 
  let p_524 : (fp_t × fp_t × bool) :=
    g1_clear_cofactor (q_523) in 
  p_524.

Definition g2_xnum_k_0_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 416399692810564414) : int64;
        secret (@repr WORDSIZE64 13500519111022079365) : int64;
        secret (@repr WORDSIZE64 3658379999393219626) : int64;
        secret (@repr WORDSIZE64 9850925049107374429) : int64;
        secret (@repr WORDSIZE64 6640057249351452444) : int64;
        secret (@repr WORDSIZE64 7077594464397203414) : int64
      ] in  l).

Definition g2_xnum_k_1_i_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1249199078431693244) : int64;
        secret (@repr WORDSIZE64 3608069185647134863) : int64;
        secret (@repr WORDSIZE64 10975139998179658879) : int64;
        secret (@repr WORDSIZE64 11106031073612571672) : int64;
        secret (@repr WORDSIZE64 1473427674344805717) : int64;
        secret (@repr WORDSIZE64 2786039319482058522) : int64
      ] in  l).

Definition g2_xnum_k_2_r_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1249199078431693244) : int64;
        secret (@repr WORDSIZE64 3608069185647134863) : int64;
        secret (@repr WORDSIZE64 10975139998179658879) : int64;
        secret (@repr WORDSIZE64 11106031073612571672) : int64;
        secret (@repr WORDSIZE64 1473427674344805717) : int64;
        secret (@repr WORDSIZE64 2786039319482058526) : int64
      ] in  l).

Definition g2_xnum_k_2_i_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 624599539215846622) : int64;
        secret (@repr WORDSIZE64 1804034592823567431) : int64;
        secret (@repr WORDSIZE64 14710942035944605247) : int64;
        secret (@repr WORDSIZE64 14776387573661061644) : int64;
        secret (@repr WORDSIZE64 736713837172402858) : int64;
        secret (@repr WORDSIZE64 10616391696595805069) : int64
      ] in  l).

Definition g2_xnum_k_3_r_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1665598771242257658) : int64;
        secret (@repr WORDSIZE64 17108588296669214228) : int64;
        secret (@repr WORDSIZE64 14633519997572878506) : int64;
        secret (@repr WORDSIZE64 2510212049010394485) : int64;
        secret (@repr WORDSIZE64 8113484923696258161) : int64;
        secret (@repr WORDSIZE64 9863633783879261905) : int64
      ] in  l).

Definition g2_xden_k_0_i_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1873798617647539866) : int64;
        secret (@repr WORDSIZE64 5412103778470702295) : int64;
        secret (@repr WORDSIZE64 7239337960414712511) : int64;
        secret (@repr WORDSIZE64 7435674573564081700) : int64;
        secret (@repr WORDSIZE64 2210141511517208575) : int64;
        secret (@repr WORDSIZE64 13402431016077863523) : int64
      ] in  l).

Definition g2_xden_k_1_i_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1873798617647539866) : int64;
        secret (@repr WORDSIZE64 5412103778470702295) : int64;
        secret (@repr WORDSIZE64 7239337960414712511) : int64;
        secret (@repr WORDSIZE64 7435674573564081700) : int64;
        secret (@repr WORDSIZE64 2210141511517208575) : int64;
        secret (@repr WORDSIZE64 13402431016077863583) : int64
      ] in  l).

Definition g2_ynum_k_0_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1526798873638736187) : int64;
        secret (@repr WORDSIZE64 6459500568425337235) : int64;
        secret (@repr WORDSIZE64 1116230615302104219) : int64;
        secret (@repr WORDSIZE64 17673314439684154624) : int64;
        secret (@repr WORDSIZE64 18197961889718808424) : int64;
        secret (@repr WORDSIZE64 1355520937843676934) : int64
      ] in  l).

Definition g2_ynum_k_1_i_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 416399692810564414) : int64;
        secret (@repr WORDSIZE64 13500519111022079365) : int64;
        secret (@repr WORDSIZE64 3658379999393219626) : int64;
        secret (@repr WORDSIZE64 9850925049107374429) : int64;
        secret (@repr WORDSIZE64 6640057249351452444) : int64;
        secret (@repr WORDSIZE64 7077594464397203390) : int64
      ] in  l).

Definition g2_ynum_k_2_r_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1249199078431693244) : int64;
        secret (@repr WORDSIZE64 3608069185647134863) : int64;
        secret (@repr WORDSIZE64 10975139998179658879) : int64;
        secret (@repr WORDSIZE64 11106031073612571672) : int64;
        secret (@repr WORDSIZE64 1473427674344805717) : int64;
        secret (@repr WORDSIZE64 2786039319482058524) : int64
      ] in  l).

Definition g2_ynum_k_2_i_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 624599539215846622) : int64;
        secret (@repr WORDSIZE64 1804034592823567431) : int64;
        secret (@repr WORDSIZE64 14710942035944605247) : int64;
        secret (@repr WORDSIZE64 14776387573661061644) : int64;
        secret (@repr WORDSIZE64 736713837172402858) : int64;
        secret (@repr WORDSIZE64 10616391696595805071) : int64
      ] in  l).

Definition g2_ynum_k_3_r_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1318599027233453979) : int64;
        secret (@repr WORDSIZE64 18155985086623849168) : int64;
        secret (@repr WORDSIZE64 8510412652460270214) : int64;
        secret (@repr WORDSIZE64 12747851915130467410) : int64;
        secret (@repr WORDSIZE64 5654561228188306393) : int64;
        secret (@repr WORDSIZE64 16263467779354626832) : int64
      ] in  l).

Definition g2_yden_k_0_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1873798617647539866) : int64;
        secret (@repr WORDSIZE64 5412103778470702295) : int64;
        secret (@repr WORDSIZE64 7239337960414712511) : int64;
        secret (@repr WORDSIZE64 7435674573564081700) : int64;
        secret (@repr WORDSIZE64 2210141511517208575) : int64;
        secret (@repr WORDSIZE64 13402431016077863163) : int64
      ] in  l).

Definition g2_yden_k_1_i_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1873798617647539866) : int64;
        secret (@repr WORDSIZE64 5412103778470702295) : int64;
        secret (@repr WORDSIZE64 7239337960414712511) : int64;
        secret (@repr WORDSIZE64 7435674573564081700) : int64;
        secret (@repr WORDSIZE64 2210141511517208575) : int64;
        secret (@repr WORDSIZE64 13402431016077863379) : int64
      ] in  l).

Definition g2_yden_k_2_i_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1873798617647539866) : int64;
        secret (@repr WORDSIZE64 5412103778470702295) : int64;
        secret (@repr WORDSIZE64 7239337960414712511) : int64;
        secret (@repr WORDSIZE64 7435674573564081700) : int64;
        secret (@repr WORDSIZE64 2210141511517208575) : int64;
        secret (@repr WORDSIZE64 13402431016077863577) : int64
      ] in  l).

Definition g2_simple_swu_iso (u_525 : fp2_t) : (fp2_t × fp2_t) :=
  let z_526 : (fp_t × fp_t) :=
    fp2neg ((nat_mod_two , nat_mod_one )) in 
  let a_527 : (fp_t × fp_t) :=
    (nat_mod_zero , nat_mod_from_literal (_) (@repr WORDSIZE128 240) : fp_t) in 
  let b_528 : (fp_t × fp_t) :=
    (
      nat_mod_from_literal (_) (@repr WORDSIZE128 1012) : fp_t,
      nat_mod_from_literal (_) (@repr WORDSIZE128 1012) : fp_t
    ) in 
  let tv1_529 : (fp_t × fp_t) :=
    fp2inv (fp2add (fp2mul (fp2mul (z_526) (z_526)) (fp2mul (fp2mul (u_525) (
              u_525)) (fp2mul (u_525) (u_525)))) (fp2mul (z_526) (fp2mul (
            u_525) (u_525)))) in 
  let x1_530 : (fp_t × fp_t) :=
    fp2mul (fp2mul (fp2neg (b_528)) (fp2inv (a_527))) (fp2add (fp2fromfp (
          nat_mod_one )) (tv1_529)) in 
  let '(x1_530) :=
    if (tv1_529) =.? (fp2zero ):bool then (let x1_530 :=
        fp2mul (b_528) (fp2inv (fp2mul (z_526) (a_527))) in 
      (x1_530)) else ((x1_530)) in 
  let gx1_531 : (fp_t × fp_t) :=
    fp2add (fp2add (fp2mul (fp2mul (x1_530) (x1_530)) (x1_530)) (fp2mul (
          a_527) (x1_530))) (b_528) in 
  let x2_532 : (fp_t × fp_t) :=
    fp2mul (fp2mul (z_526) (fp2mul (u_525) (u_525))) (x1_530) in 
  let gx2_533 : (fp_t × fp_t) :=
    fp2add (fp2add (fp2mul (fp2mul (x2_532) (x2_532)) (x2_532)) (fp2mul (
          a_527) (x2_532))) (b_528) in 
  let '(x_534, y_535) :=
    (if (fp2_is_square (gx1_531)):bool then ((x1_530, fp2_sqrt (gx1_531)
        )) else ((x2_532, fp2_sqrt (gx2_533)))) in 
  let '(y_535) :=
    if (fp2_sgn0 (u_525)) !=.? (fp2_sgn0 (y_535)):bool then (let y_535 :=
        fp2neg (y_535) in 
      (y_535)) else ((y_535)) in 
  (x_534, y_535).

Definition g2_isogeny_map (x_536 : fp2_t) (y_537 : fp2_t) : g2_t :=
  let xnum_k_538 : seq (fp_t × fp_t) :=
    seq_new_ (default) (usize 4) in 
  let xnum_k_538 :=
    seq_upd xnum_k_538 (usize 0) ((
        nat_mod_from_byte_seq_be (array_to_be_bytes (g2_xnum_k_0_v)) : fp_t,
        nat_mod_from_byte_seq_be (array_to_be_bytes (g2_xnum_k_0_v)) : fp_t
      )) in 
  let xnum_k_538 :=
    seq_upd xnum_k_538 (usize 1) ((
        nat_mod_zero ,
        nat_mod_from_byte_seq_be (array_to_be_bytes (g2_xnum_k_1_i_v)) : fp_t
      )) in 
  let xnum_k_538 :=
    seq_upd xnum_k_538 (usize 2) ((
        nat_mod_from_byte_seq_be (array_to_be_bytes (g2_xnum_k_2_r_v)) : fp_t,
        nat_mod_from_byte_seq_be (array_to_be_bytes (g2_xnum_k_2_i_v)) : fp_t
      )) in 
  let xnum_k_538 :=
    seq_upd xnum_k_538 (usize 3) ((
        nat_mod_from_byte_seq_be (array_to_be_bytes (g2_xnum_k_3_r_v)) : fp_t,
        nat_mod_zero 
      )) in 
  let xden_k_539 : seq (fp_t × fp_t) :=
    seq_new_ (default) (usize 2) in 
  let xden_k_539 :=
    seq_upd xden_k_539 (usize 0) ((
        nat_mod_zero ,
        nat_mod_from_byte_seq_be (array_to_be_bytes (g2_xden_k_0_i_v)) : fp_t
      )) in 
  let xden_k_539 :=
    seq_upd xden_k_539 (usize 1) ((
        nat_mod_from_literal (_) (@repr WORDSIZE128 12) : fp_t,
        nat_mod_from_byte_seq_be (array_to_be_bytes (g2_xden_k_1_i_v)) : fp_t
      )) in 
  let ynum_k_540 : seq (fp_t × fp_t) :=
    seq_new_ (default) (usize 4) in 
  let ynum_k_540 :=
    seq_upd ynum_k_540 (usize 0) ((
        nat_mod_from_byte_seq_be (array_to_be_bytes (g2_ynum_k_0_v)) : fp_t,
        nat_mod_from_byte_seq_be (array_to_be_bytes (g2_ynum_k_0_v)) : fp_t
      )) in 
  let ynum_k_540 :=
    seq_upd ynum_k_540 (usize 1) ((
        nat_mod_zero ,
        nat_mod_from_byte_seq_be (array_to_be_bytes (g2_ynum_k_1_i_v)) : fp_t
      )) in 
  let ynum_k_540 :=
    seq_upd ynum_k_540 (usize 2) ((
        nat_mod_from_byte_seq_be (array_to_be_bytes (g2_ynum_k_2_r_v)) : fp_t,
        nat_mod_from_byte_seq_be (array_to_be_bytes (g2_ynum_k_2_i_v)) : fp_t
      )) in 
  let ynum_k_540 :=
    seq_upd ynum_k_540 (usize 3) ((
        nat_mod_from_byte_seq_be (array_to_be_bytes (g2_ynum_k_3_r_v)) : fp_t,
        nat_mod_zero 
      )) in 
  let yden_k_541 : seq (fp_t × fp_t) :=
    seq_new_ (default) (usize 3) in 
  let yden_k_541 :=
    seq_upd yden_k_541 (usize 0) ((
        nat_mod_from_byte_seq_be (array_to_be_bytes (g2_yden_k_0_v)) : fp_t,
        nat_mod_from_byte_seq_be (array_to_be_bytes (g2_yden_k_0_v)) : fp_t
      )) in 
  let yden_k_541 :=
    seq_upd yden_k_541 (usize 1) ((
        nat_mod_zero ,
        nat_mod_from_byte_seq_be (array_to_be_bytes (g2_yden_k_1_i_v)) : fp_t
      )) in 
  let yden_k_541 :=
    seq_upd yden_k_541 (usize 2) ((
        nat_mod_from_literal (_) (@repr WORDSIZE128 18) : fp_t,
        nat_mod_from_byte_seq_be (array_to_be_bytes (g2_yden_k_2_i_v)) : fp_t
      )) in 
  let xnum_542 : (fp_t × fp_t) :=
    fp2zero  in 
  let xx_543 : (fp_t × fp_t) :=
    fp2fromfp (nat_mod_one ) in 
  let '(xnum_542, xx_543) :=
    foldi (usize 0) (seq_len (xnum_k_538)) (fun i_544 '(xnum_542, xx_543) =>
      let xnum_542 :=
        fp2add (xnum_542) (fp2mul (xx_543) (seq_index (xnum_k_538) (i_544))) in 
      let xx_543 :=
        fp2mul (xx_543) (x_536) in 
      (xnum_542, xx_543))
    (xnum_542, xx_543) in 
  let xden_545 : (fp_t × fp_t) :=
    fp2zero  in 
  let xx_546 : (fp_t × fp_t) :=
    fp2fromfp (nat_mod_one ) in 
  let '(xden_545, xx_546) :=
    foldi (usize 0) (seq_len (xden_k_539)) (fun i_547 '(xden_545, xx_546) =>
      let xden_545 :=
        fp2add (xden_545) (fp2mul (xx_546) (seq_index (xden_k_539) (i_547))) in 
      let xx_546 :=
        fp2mul (xx_546) (x_536) in 
      (xden_545, xx_546))
    (xden_545, xx_546) in 
  let xden_545 :=
    fp2add (xden_545) (xx_546) in 
  let ynum_548 : (fp_t × fp_t) :=
    fp2zero  in 
  let xx_549 : (fp_t × fp_t) :=
    fp2fromfp (nat_mod_one ) in 
  let '(ynum_548, xx_549) :=
    foldi (usize 0) (seq_len (ynum_k_540)) (fun i_550 '(ynum_548, xx_549) =>
      let ynum_548 :=
        fp2add (ynum_548) (fp2mul (xx_549) (seq_index (ynum_k_540) (i_550))) in 
      let xx_549 :=
        fp2mul (xx_549) (x_536) in 
      (ynum_548, xx_549))
    (ynum_548, xx_549) in 
  let yden_551 : (fp_t × fp_t) :=
    fp2zero  in 
  let xx_552 : (fp_t × fp_t) :=
    fp2fromfp (nat_mod_one ) in 
  let '(yden_551, xx_552) :=
    foldi (usize 0) (seq_len (yden_k_541)) (fun i_553 '(yden_551, xx_552) =>
      let yden_551 :=
        fp2add (yden_551) (fp2mul (xx_552) (seq_index (yden_k_541) (i_553))) in 
      let xx_552 :=
        fp2mul (xx_552) (x_536) in 
      (yden_551, xx_552))
    (yden_551, xx_552) in 
  let yden_551 :=
    fp2add (yden_551) (xx_552) in 
  let xr_554 : (fp_t × fp_t) :=
    fp2mul (xnum_542) (fp2inv (xden_545)) in 
  let yr_555 : (fp_t × fp_t) :=
    fp2mul (y_537) (fp2mul (ynum_548) (fp2inv (yden_551))) in 
  let inf_556 : bool :=
    false in 
  let '(inf_556) :=
    if ((xden_545) =.? (fp2zero )) || ((yden_551) =.? (fp2zero )):bool then (
      let inf_556 :=
        true in 
      (inf_556)) else ((inf_556)) in 
  (xr_554, yr_555, inf_556).

Definition g2_map_to_curve_sswu (u_557 : fp2_t) : g2_t :=
  let '(xp_558, yp_559) :=
    g2_simple_swu_iso (u_557) in 
  let p_560 : ((fp_t × fp_t) × (fp_t × fp_t) × bool) :=
    g2_isogeny_map (xp_558) (yp_559) in 
  p_560.

Definition g2_hash_to_curve_sswu
  (msg_561 : byte_seq)
  (dst_562 : byte_seq)
  : g2_t :=
  let u_563 : seq fp2_t :=
    fp2_hash_to_field (msg_561) (dst_562) (usize 2) in 
  let q0_564 : ((fp_t × fp_t) × (fp_t × fp_t) × bool) :=
    g2_map_to_curve_sswu (seq_index (u_563) (usize 0)) in 
  let q1_565 : ((fp_t × fp_t) × (fp_t × fp_t) × bool) :=
    g2_map_to_curve_sswu (seq_index (u_563) (usize 1)) in 
  let r_566 : ((fp_t × fp_t) × (fp_t × fp_t) × bool) :=
    g2add (q0_564) (q1_565) in 
  let p_567 : ((fp_t × fp_t) × (fp_t × fp_t) × bool) :=
    g2_clear_cofactor (r_566) in 
  p_567.

Definition g2_encode_to_curve_sswu
  (msg_568 : byte_seq)
  (dst_569 : byte_seq)
  : g2_t :=
  let u_570 : seq fp2_t :=
    fp2_hash_to_field (msg_568) (dst_569) (usize 1) in 
  let q_571 : ((fp_t × fp_t) × (fp_t × fp_t) × bool) :=
    g2_map_to_curve_sswu (seq_index (u_570) (usize 0)) in 
  let p_572 : ((fp_t × fp_t) × (fp_t × fp_t) × bool) :=
    g2_clear_cofactor (q_571) in 
  p_572.

