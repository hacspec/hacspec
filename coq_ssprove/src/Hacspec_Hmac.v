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

Require Import Hacspec_Sha256.

Definition block_len_v : (uint_size) :=
  ((k_size_v)).

Definition prk_t  :=
  ( nseq (uint8) (hash_size_v)).

Definition block_t  :=
  ( nseq (uint8) (block_len_v)).

Definition i_pad_v : (block_t) :=
  (let temp_4173 : int8 :=
      (secret (@repr U8 54)) in
    let temp_4175 : int8 :=
      (secret (@repr U8 54)) in
    let temp_4177 : int8 :=
      (secret (@repr U8 54)) in
    let temp_4179 : int8 :=
      (secret (@repr U8 54)) in
    let temp_4181 : int8 :=
      (secret (@repr U8 54)) in
    let temp_4183 : int8 :=
      (secret (@repr U8 54)) in
    let temp_4185 : int8 :=
      (secret (@repr U8 54)) in
    let temp_4187 : int8 :=
      (secret (@repr U8 54)) in
    let temp_4189 : int8 :=
      (secret (@repr U8 54)) in
    let temp_4191 : int8 :=
      (secret (@repr U8 54)) in
    let temp_4193 : int8 :=
      (secret (@repr U8 54)) in
    let temp_4195 : int8 :=
      (secret (@repr U8 54)) in
    let temp_4197 : int8 :=
      (secret (@repr U8 54)) in
    let temp_4199 : int8 :=
      (secret (@repr U8 54)) in
    let temp_4201 : int8 :=
      (secret (@repr U8 54)) in
    let temp_4203 : int8 :=
      (secret (@repr U8 54)) in
    let temp_4205 : int8 :=
      (secret (@repr U8 54)) in
    let temp_4207 : int8 :=
      (secret (@repr U8 54)) in
    let temp_4209 : int8 :=
      (secret (@repr U8 54)) in
    let temp_4211 : int8 :=
      (secret (@repr U8 54)) in
    let temp_4213 : int8 :=
      (secret (@repr U8 54)) in
    let temp_4215 : int8 :=
      (secret (@repr U8 54)) in
    let temp_4217 : int8 :=
      (secret (@repr U8 54)) in
    let temp_4219 : int8 :=
      (secret (@repr U8 54)) in
    let temp_4221 : int8 :=
      (secret (@repr U8 54)) in
    let temp_4223 : int8 :=
      (secret (@repr U8 54)) in
    let temp_4225 : int8 :=
      (secret (@repr U8 54)) in
    let temp_4227 : int8 :=
      (secret (@repr U8 54)) in
    let temp_4229 : int8 :=
      (secret (@repr U8 54)) in
    let temp_4231 : int8 :=
      (secret (@repr U8 54)) in
    let temp_4233 : int8 :=
      (secret (@repr U8 54)) in
    let temp_4235 : int8 :=
      (secret (@repr U8 54)) in
    let temp_4237 : int8 :=
      (secret (@repr U8 54)) in
    let temp_4239 : int8 :=
      (secret (@repr U8 54)) in
    let temp_4241 : int8 :=
      (secret (@repr U8 54)) in
    let temp_4243 : int8 :=
      (secret (@repr U8 54)) in
    let temp_4245 : int8 :=
      (secret (@repr U8 54)) in
    let temp_4247 : int8 :=
      (secret (@repr U8 54)) in
    let temp_4249 : int8 :=
      (secret (@repr U8 54)) in
    let temp_4251 : int8 :=
      (secret (@repr U8 54)) in
    let temp_4253 : int8 :=
      (secret (@repr U8 54)) in
    let temp_4255 : int8 :=
      (secret (@repr U8 54)) in
    let temp_4257 : int8 :=
      (secret (@repr U8 54)) in
    let temp_4259 : int8 :=
      (secret (@repr U8 54)) in
    let temp_4261 : int8 :=
      (secret (@repr U8 54)) in
    let temp_4263 : int8 :=
      (secret (@repr U8 54)) in
    let temp_4265 : int8 :=
      (secret (@repr U8 54)) in
    let temp_4267 : int8 :=
      (secret (@repr U8 54)) in
    let temp_4269 : int8 :=
      (secret (@repr U8 54)) in
    let temp_4271 : int8 :=
      (secret (@repr U8 54)) in
    let temp_4273 : int8 :=
      (secret (@repr U8 54)) in
    let temp_4275 : int8 :=
      (secret (@repr U8 54)) in
    let temp_4277 : int8 :=
      (secret (@repr U8 54)) in
    let temp_4279 : int8 :=
      (secret (@repr U8 54)) in
    let temp_4281 : int8 :=
      (secret (@repr U8 54)) in
    let temp_4283 : int8 :=
      (secret (@repr U8 54)) in
    let temp_4285 : int8 :=
      (secret (@repr U8 54)) in
    let temp_4287 : int8 :=
      (secret (@repr U8 54)) in
    let temp_4289 : int8 :=
      (secret (@repr U8 54)) in
    let temp_4291 : int8 :=
      (secret (@repr U8 54)) in
    let temp_4293 : int8 :=
      (secret (@repr U8 54)) in
    let temp_4295 : int8 :=
      (secret (@repr U8 54)) in
    let temp_4297 : int8 :=
      (secret (@repr U8 54)) in
    let temp_4299 : int8 :=
      (secret (@repr U8 54)) in
    let temp_4301 : nseq uint8 64 :=
      (array_from_list uint8 [
          temp_4173;
          temp_4175;
          temp_4177;
          temp_4179;
          temp_4181;
          temp_4183;
          temp_4185;
          temp_4187;
          temp_4189;
          temp_4191;
          temp_4193;
          temp_4195;
          temp_4197;
          temp_4199;
          temp_4201;
          temp_4203;
          temp_4205;
          temp_4207;
          temp_4209;
          temp_4211;
          temp_4213;
          temp_4215;
          temp_4217;
          temp_4219;
          temp_4221;
          temp_4223;
          temp_4225;
          temp_4227;
          temp_4229;
          temp_4231;
          temp_4233;
          temp_4235;
          temp_4237;
          temp_4239;
          temp_4241;
          temp_4243;
          temp_4245;
          temp_4247;
          temp_4249;
          temp_4251;
          temp_4253;
          temp_4255;
          temp_4257;
          temp_4259;
          temp_4261;
          temp_4263;
          temp_4265;
          temp_4267;
          temp_4269;
          temp_4271;
          temp_4273;
          temp_4275;
          temp_4277;
          temp_4279;
          temp_4281;
          temp_4283;
          temp_4285;
          temp_4287;
          temp_4289;
          temp_4291;
          temp_4293;
          temp_4295;
          temp_4297;
          temp_4299
        ]) in
    (temp_4301)).

Definition o_pad_v : (block_t) :=
  (let temp_4303 : int8 :=
      (secret (@repr U8 92)) in
    let temp_4305 : int8 :=
      (secret (@repr U8 92)) in
    let temp_4307 : int8 :=
      (secret (@repr U8 92)) in
    let temp_4309 : int8 :=
      (secret (@repr U8 92)) in
    let temp_4311 : int8 :=
      (secret (@repr U8 92)) in
    let temp_4313 : int8 :=
      (secret (@repr U8 92)) in
    let temp_4315 : int8 :=
      (secret (@repr U8 92)) in
    let temp_4317 : int8 :=
      (secret (@repr U8 92)) in
    let temp_4319 : int8 :=
      (secret (@repr U8 92)) in
    let temp_4321 : int8 :=
      (secret (@repr U8 92)) in
    let temp_4323 : int8 :=
      (secret (@repr U8 92)) in
    let temp_4325 : int8 :=
      (secret (@repr U8 92)) in
    let temp_4327 : int8 :=
      (secret (@repr U8 92)) in
    let temp_4329 : int8 :=
      (secret (@repr U8 92)) in
    let temp_4331 : int8 :=
      (secret (@repr U8 92)) in
    let temp_4333 : int8 :=
      (secret (@repr U8 92)) in
    let temp_4335 : int8 :=
      (secret (@repr U8 92)) in
    let temp_4337 : int8 :=
      (secret (@repr U8 92)) in
    let temp_4339 : int8 :=
      (secret (@repr U8 92)) in
    let temp_4341 : int8 :=
      (secret (@repr U8 92)) in
    let temp_4343 : int8 :=
      (secret (@repr U8 92)) in
    let temp_4345 : int8 :=
      (secret (@repr U8 92)) in
    let temp_4347 : int8 :=
      (secret (@repr U8 92)) in
    let temp_4349 : int8 :=
      (secret (@repr U8 92)) in
    let temp_4351 : int8 :=
      (secret (@repr U8 92)) in
    let temp_4353 : int8 :=
      (secret (@repr U8 92)) in
    let temp_4355 : int8 :=
      (secret (@repr U8 92)) in
    let temp_4357 : int8 :=
      (secret (@repr U8 92)) in
    let temp_4359 : int8 :=
      (secret (@repr U8 92)) in
    let temp_4361 : int8 :=
      (secret (@repr U8 92)) in
    let temp_4363 : int8 :=
      (secret (@repr U8 92)) in
    let temp_4365 : int8 :=
      (secret (@repr U8 92)) in
    let temp_4367 : int8 :=
      (secret (@repr U8 92)) in
    let temp_4369 : int8 :=
      (secret (@repr U8 92)) in
    let temp_4371 : int8 :=
      (secret (@repr U8 92)) in
    let temp_4373 : int8 :=
      (secret (@repr U8 92)) in
    let temp_4375 : int8 :=
      (secret (@repr U8 92)) in
    let temp_4377 : int8 :=
      (secret (@repr U8 92)) in
    let temp_4379 : int8 :=
      (secret (@repr U8 92)) in
    let temp_4381 : int8 :=
      (secret (@repr U8 92)) in
    let temp_4383 : int8 :=
      (secret (@repr U8 92)) in
    let temp_4385 : int8 :=
      (secret (@repr U8 92)) in
    let temp_4387 : int8 :=
      (secret (@repr U8 92)) in
    let temp_4389 : int8 :=
      (secret (@repr U8 92)) in
    let temp_4391 : int8 :=
      (secret (@repr U8 92)) in
    let temp_4393 : int8 :=
      (secret (@repr U8 92)) in
    let temp_4395 : int8 :=
      (secret (@repr U8 92)) in
    let temp_4397 : int8 :=
      (secret (@repr U8 92)) in
    let temp_4399 : int8 :=
      (secret (@repr U8 92)) in
    let temp_4401 : int8 :=
      (secret (@repr U8 92)) in
    let temp_4403 : int8 :=
      (secret (@repr U8 92)) in
    let temp_4405 : int8 :=
      (secret (@repr U8 92)) in
    let temp_4407 : int8 :=
      (secret (@repr U8 92)) in
    let temp_4409 : int8 :=
      (secret (@repr U8 92)) in
    let temp_4411 : int8 :=
      (secret (@repr U8 92)) in
    let temp_4413 : int8 :=
      (secret (@repr U8 92)) in
    let temp_4415 : int8 :=
      (secret (@repr U8 92)) in
    let temp_4417 : int8 :=
      (secret (@repr U8 92)) in
    let temp_4419 : int8 :=
      (secret (@repr U8 92)) in
    let temp_4421 : int8 :=
      (secret (@repr U8 92)) in
    let temp_4423 : int8 :=
      (secret (@repr U8 92)) in
    let temp_4425 : int8 :=
      (secret (@repr U8 92)) in
    let temp_4427 : int8 :=
      (secret (@repr U8 92)) in
    let temp_4429 : int8 :=
      (secret (@repr U8 92)) in
    let temp_4431 : nseq uint8 64 :=
      (array_from_list uint8 [
          temp_4303;
          temp_4305;
          temp_4307;
          temp_4309;
          temp_4311;
          temp_4313;
          temp_4315;
          temp_4317;
          temp_4319;
          temp_4321;
          temp_4323;
          temp_4325;
          temp_4327;
          temp_4329;
          temp_4331;
          temp_4333;
          temp_4335;
          temp_4337;
          temp_4339;
          temp_4341;
          temp_4343;
          temp_4345;
          temp_4347;
          temp_4349;
          temp_4351;
          temp_4353;
          temp_4355;
          temp_4357;
          temp_4359;
          temp_4361;
          temp_4363;
          temp_4365;
          temp_4367;
          temp_4369;
          temp_4371;
          temp_4373;
          temp_4375;
          temp_4377;
          temp_4379;
          temp_4381;
          temp_4383;
          temp_4385;
          temp_4387;
          temp_4389;
          temp_4391;
          temp_4393;
          temp_4395;
          temp_4397;
          temp_4399;
          temp_4401;
          temp_4403;
          temp_4405;
          temp_4407;
          temp_4409;
          temp_4411;
          temp_4413;
          temp_4415;
          temp_4417;
          temp_4419;
          temp_4421;
          temp_4423;
          temp_4425;
          temp_4427;
          temp_4429
        ]) in
    (temp_4431)).


Notation "'k_block_inp'" := (
  byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'k_block_out'" := (
  block_t : choice_type) (in custom pack_type at level 2).
Definition K_BLOCK : nat :=
  (4449).
Program Definition k_block
   : package (fset.fset0) [interface #val #[ HASH ] : hash_inp → hash_out
  ] [interface #val #[ K_BLOCK ] : k_block_inp → k_block_out ] :=
  ([package #def #[ K_BLOCK ] (temp_inp : k_block_inp) : k_block_out { 
    let '(k_4432) := temp_inp : byte_seq in
    #import {sig #[ HASH ] : hash_inp → hash_out } as hash ;;
    let hash := fun x_0 => hash (x_0) in
    ({ code  '(temp_4434 : uint_size) ←
        (seq_len (k_4432)) ;;
       '(temp_4436 : bool_ChoiceEquality) ←
        ((temp_4434) >.? (block_len_v)) ;;
       '(temp_4438 : block_t) ←
        (array_new_ (default : uint8) (block_len_v)) ;;
       '(temp_4440 : sha256_digest_t) ←
        (hash (k_4432)) ;;
       '(temp_4442 : seq uint8) ←
        (array_to_seq (temp_4440)) ;;
       '(temp_4444 : block_t) ←
        (array_update_start (temp_4438) (temp_4442)) ;;
       '(temp_4446 : block_t) ←
        (array_new_ (default : uint8) (block_len_v)) ;;
       '(temp_4448 : block_t) ←
        (array_update_start (temp_4446) (k_4432)) ;;
      @ret (block_t) ((if (temp_4436):bool_ChoiceEquality then (*inline*) (
            temp_4444) else (temp_4448))) } : code (fset.fset0) [interface
      #val #[ HASH ] : hash_inp → hash_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_k_block : package _ _ _ :=
  (seq_link k_block link_rest(package_hash)).
Fail Next Obligation.

Definition h_in_4472_loc : ChoiceEqualityLocation :=
  ((seq uint8 ; 4484%nat)).
Definition h_in_4460_loc : ChoiceEqualityLocation :=
  ((seq uint8 ; 4485%nat)).
Notation "'hmac_inp'" := (
  byte_seq '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'hmac_out'" := (prk_t : choice_type) (in custom pack_type at level 2).
Definition HMAC : nat :=
  (4486).
Program Definition hmac
   : package (CEfset ([h_in_4460_loc ; h_in_4472_loc])) [interface
  #val #[ HASH ] : hash_inp → hash_out ;
  #val #[ K_BLOCK ] : k_block_inp → k_block_out ] [interface
  #val #[ HMAC ] : hmac_inp → hmac_out ] :=
  ([package #def #[ HMAC ] (temp_inp : hmac_inp) : hmac_out { 
    let '(k_4450 , txt_4461) := temp_inp : byte_seq '× byte_seq in
    #import {sig #[ HASH ] : hash_inp → hash_out } as hash ;;
    let hash := fun x_0 => hash (x_0) in
    #import {sig #[ K_BLOCK ] : k_block_inp → k_block_out } as k_block ;;
    let k_block := fun x_0 => k_block (x_0) in
    ({ code  '(k_block_4453 : block_t) ←
        ( '(temp_4452 : block_t) ←
            (k_block (k_4450)) ;;
          ret (temp_4452)) ;;
       '(h_in_4460 : seq uint8) ←
          ( '(temp_4455 : block_t) ←
              ((k_block_4453) array_xor (i_pad_v)) ;;
             '(temp_4457 : seq uint8) ←
              (array_to_seq (temp_4455)) ;;
             '(temp_4459 : byte_seq) ←
              (seq_from_seq (temp_4457)) ;;
            ret (temp_4459)) ;;
        #put h_in_4460_loc := h_in_4460 ;;
       '(h_in_4460 : seq uint8) ←
          (( '(temp_4463 : seq uint8) ←
                (seq_concat (h_in_4460) (txt_4461)) ;;
              ret (temp_4463))) ;;
        #put h_in_4460_loc := h_in_4460 ;;
      
       '(h_inner_4473 : sha256_digest_t) ←
        ( temp_4465 ←
            (hash (h_in_4460)) ;;
          ret (temp_4465)) ;;
       '(h_in_4472 : seq uint8) ←
          ( '(temp_4467 : block_t) ←
              ((k_block_4453) array_xor (o_pad_v)) ;;
             '(temp_4469 : seq uint8) ←
              (array_to_seq (temp_4467)) ;;
             '(temp_4471 : byte_seq) ←
              (seq_from_seq (temp_4469)) ;;
            ret (temp_4471)) ;;
        #put h_in_4472_loc := h_in_4472 ;;
       '(h_in_4472 : seq uint8) ←
          (( '(temp_4475 : seq uint8) ←
                (array_to_seq (h_inner_4473)) ;;
               '(temp_4477 : seq uint8) ←
                (seq_concat (h_in_4472) (temp_4475)) ;;
              ret (temp_4477))) ;;
        #put h_in_4472_loc := h_in_4472 ;;
      
       '(temp_4479 : sha256_digest_t) ←
        (hash (h_in_4472)) ;;
       '(temp_4481 : seq uint8) ←
        (array_to_seq (temp_4479)) ;;
       '(temp_4483 : prk_t) ←
        (array_from_seq (hash_size_v) (temp_4481)) ;;
      @ret (prk_t) (temp_4483) } : code (CEfset (
          [h_in_4460_loc ; h_in_4472_loc])) [interface
      #val #[ HASH ] : hash_inp → hash_out ;
      #val #[ K_BLOCK ] : k_block_inp → k_block_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_hmac : package _ _ _ :=
  (seq_link hmac link_rest(package_hash,package_k_block)).
Fail Next Obligation.

