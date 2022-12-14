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


Require Import Hacspec_Aes.

Require Import Hacspec_Gf128.

Notation "'aes_gcm_byte_seq_result_t'" := ((
  result int8 byte_seq)) : hacspec_scope.

Definition invalid_tag_v : int8 :=
  @repr U8 1.

Definition padded_msg_351_loc : ChoiceEqualityLocation :=
  (seq uint8 ; 352%nat).
Notation "'pad_aad_msg_inp'" :=(
  byte_seq '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'pad_aad_msg_inp'" :=(
  byte_seq '× byte_seq : ChoiceEquality) (at level 2).
Notation "'pad_aad_msg_out'" :=(
  byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'pad_aad_msg_out'" :=(byte_seq : ChoiceEquality) (at level 2).
Definition PAD_AAD_MSG : nat :=
  359.
Program Definition pad_aad_msg (aad_353 : byte_seq) (msg_355 : byte_seq)
  : both (CEfset ([padded_msg_351_loc])) [interface] (byte_seq) :=
  ((letb laad_354 : uint_size := seq_len (lift_to_both0 aad_353) in
      letb lmsg_356 : uint_size := seq_len (lift_to_both0 msg_355) in
      letb pad_aad_357 : uint_size :=
        if is_pure (I := [interface]) (((lift_to_both0 laad_354) %% (
              lift_to_both0 (usize 16))) =.? (lift_to_both0 (usize 0)))
        then lift_to_both0 laad_354
        else (lift_to_both0 laad_354) .+ ((lift_to_both0 (usize 16)) .- ((
              lift_to_both0 laad_354) %% (lift_to_both0 (usize 16)))) in
      letb pad_msg_358 : uint_size :=
        if is_pure (I := [interface]) (((lift_to_both0 lmsg_356) %% (
              lift_to_both0 (usize 16))) =.? (lift_to_both0 (usize 0)))
        then lift_to_both0 lmsg_356
        else (lift_to_both0 lmsg_356) .+ ((lift_to_both0 (usize 16)) .- ((
              lift_to_both0 lmsg_356) %% (lift_to_both0 (usize 16)))) in
      letbm padded_msg_351 : seq uint8 loc( padded_msg_351_loc ) :=
        seq_new_ (default : uint8) (((lift_to_both0 pad_aad_357) .+ (
              lift_to_both0 pad_msg_358)) .+ (lift_to_both0 (usize 16))) in
      letbm padded_msg_351 loc( padded_msg_351_loc ) :=
        seq_update (lift_to_both0 padded_msg_351) (lift_to_both0 (usize 0)) (
          lift_to_both0 aad_353) in
      letbm padded_msg_351 loc( padded_msg_351_loc ) :=
        seq_update (lift_to_both0 padded_msg_351) (lift_to_both0 pad_aad_357) (
          lift_to_both0 msg_355) in
      letbm padded_msg_351 loc( padded_msg_351_loc ) :=
        seq_update (lift_to_both0 padded_msg_351) ((
            lift_to_both0 pad_aad_357) .+ (lift_to_both0 pad_msg_358)) (
          array_to_seq (uint64_to_be_bytes ((secret (pub_u64 (is_pure (
                    lift_to_both0 laad_354)))) .* (secret (lift_to_both0 (
                  @repr U64 8)))))) in
      letbm padded_msg_351 loc( padded_msg_351_loc ) :=
        seq_update (lift_to_both0 padded_msg_351) (((
              lift_to_both0 pad_aad_357) .+ (lift_to_both0 pad_msg_358)) .+ (
            lift_to_both0 (usize 8))) (array_to_seq (uint64_to_be_bytes ((
              secret (pub_u64 (is_pure (lift_to_both0 lmsg_356)))) .* (secret (
                lift_to_both0 (@repr U64 8)))))) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        lift_to_both0 padded_msg_351)
      ) : both (CEfset ([padded_msg_351_loc])) [interface] (byte_seq)).
Fail Next Obligation.


Notation "'encrypt_aes_inp'" :=(
  byte_seq '× aes_nonce_t '× byte_seq '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'encrypt_aes_inp'" :=(
  byte_seq '× aes_nonce_t '× byte_seq '× byte_seq : ChoiceEquality) (at level 2).
Notation "'encrypt_aes_out'" :=((byte_seq '× gf128_tag_t
  ) : choice_type) (in custom pack_type at level 2).
Notation "'encrypt_aes_out'" :=((byte_seq '× gf128_tag_t
  ) : ChoiceEquality) (at level 2).
Definition ENCRYPT_AES : nat :=
  371.
Program Definition encrypt_aes (key_361 : byte_seq) (iv_363 : aes_nonce_t) (
    aad_367 : byte_seq) (msg_365 : byte_seq)
  : both (CEfset ([padded_msg_351_loc])) [interface] ((byte_seq '× gf128_tag_t
    )) :=
  ((letb iv0_360 : aes_nonce_t := array_new_ (default : uint8) (_) in
      letb mac_key_362 : block_t :=
        result_unwrap (aes_ctr_key_block (lift_to_both0 key_361) (
            lift_to_both0 iv0_360) (secret (lift_to_both0 (@repr U32 0))) (
            lift_to_both0 key_length_v) (lift_to_both0 rounds_v) (
            lift_to_both0 key_schedule_length_v) (lift_to_both0 key_length_v) (
            lift_to_both0 iterations_v)) in
      letb tag_mix_364 : block_t :=
        result_unwrap (aes_ctr_key_block (lift_to_both0 key_361) ((
              lift_to_both0 iv_363)) (secret (lift_to_both0 (@repr U32 1))) (
            lift_to_both0 key_length_v) (lift_to_both0 rounds_v) (
            lift_to_both0 key_schedule_length_v) (lift_to_both0 key_length_v) (
            lift_to_both0 iterations_v)) in
      letb cipher_text_366 : seq uint8 :=
        aes128_encrypt (array_from_seq (_) (lift_to_both0 key_361)) (
          lift_to_both0 iv_363) (secret (lift_to_both0 (@repr U32 2))) (
          lift_to_both0 msg_365) in
      letb padded_msg_368 : seq uint8 :=
        pad_aad_msg (lift_to_both0 aad_367) (lift_to_both0 cipher_text_366) in
      letb tag_369 : gf128_tag_t :=
        gmac (lift_to_both0 padded_msg_368) (array_from_seq (_) (
            array_to_seq (lift_to_both0 mac_key_362))) in
      letb tag_370 : block_t :=
        xor_block (array_from_seq (_) (array_to_seq (lift_to_both0 tag_369))) (
          lift_to_both0 tag_mix_364) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 cipher_text_366,
          array_from_seq (_) (array_to_seq (lift_to_both0 tag_370))
        ))
      ) : both (CEfset ([padded_msg_351_loc])) [interface] ((
        byte_seq '×
        gf128_tag_t
      ))).
Fail Next Obligation.


Notation "'encrypt_aes128_inp'" :=(
  key128_t '× aes_nonce_t '× byte_seq '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'encrypt_aes128_inp'" :=(
  key128_t '× aes_nonce_t '× byte_seq '× byte_seq : ChoiceEquality) (at level 2).
Notation "'encrypt_aes128_out'" :=((byte_seq '× gf128_tag_t
  ) : choice_type) (in custom pack_type at level 2).
Notation "'encrypt_aes128_out'" :=((byte_seq '× gf128_tag_t
  ) : ChoiceEquality) (at level 2).
Definition ENCRYPT_AES128 : nat :=
  376.
Program Definition encrypt_aes128 (key_372 : key128_t) (iv_373 : aes_nonce_t) (
    aad_374 : byte_seq) (msg_375 : byte_seq)
  : both (CEfset ([padded_msg_351_loc])) [interface] ((byte_seq '× gf128_tag_t
    )) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (encrypt_aes (
          seq_from_seq (array_to_seq (lift_to_both0 key_372))) (
          lift_to_both0 iv_373) (lift_to_both0 aad_374) (lift_to_both0 msg_375))
      ) : both (CEfset ([padded_msg_351_loc])) [interface] ((
        byte_seq '×
        gf128_tag_t
      ))).
Fail Next Obligation.


Notation "'decrypt_aes_inp'" :=(
  byte_seq '× aes_nonce_t '× byte_seq '× byte_seq '× gf128_tag_t : choice_type) (in custom pack_type at level 2).
Notation "'decrypt_aes_inp'" :=(
  byte_seq '× aes_nonce_t '× byte_seq '× byte_seq '× gf128_tag_t : ChoiceEquality) (at level 2).
Notation "'decrypt_aes_out'" :=(
  aes_gcm_byte_seq_result_t : choice_type) (in custom pack_type at level 2).
Notation "'decrypt_aes_out'" :=(
  aes_gcm_byte_seq_result_t : ChoiceEquality) (at level 2).
Definition DECRYPT_AES : nat :=
  389.
Program Definition decrypt_aes (key_378 : byte_seq) (iv_380 : aes_nonce_t) (
    aad_382 : byte_seq) (cipher_text_383 : byte_seq) (tag_388 : gf128_tag_t)
  : both (CEfset ([padded_msg_351_loc])) [interface] (
    aes_gcm_byte_seq_result_t) :=
  ((letb iv0_377 : aes_nonce_t := array_new_ (default : uint8) (_) in
      letbnd(_) mac_key_379 : block_t :=
        aes_ctr_key_block (lift_to_both0 key_378) (lift_to_both0 iv0_377) (
          secret (lift_to_both0 (@repr U32 0))) (lift_to_both0 key_length_v) (
          lift_to_both0 rounds_v) (lift_to_both0 key_schedule_length_v) (
          lift_to_both0 key_length_v) (lift_to_both0 iterations_v) in
      letbnd(_) tag_mix_381 : block_t :=
        aes_ctr_key_block (lift_to_both0 key_378) ((lift_to_both0 iv_380)) (
          secret (lift_to_both0 (@repr U32 1))) (lift_to_both0 key_length_v) (
          lift_to_both0 rounds_v) (lift_to_both0 key_schedule_length_v) (
          lift_to_both0 key_length_v) (lift_to_both0 iterations_v) in
      letb padded_msg_384 : seq uint8 :=
        pad_aad_msg (lift_to_both0 aad_382) (lift_to_both0 cipher_text_383) in
      letb my_tag_385 : gf128_tag_t :=
        gmac (lift_to_both0 padded_msg_384) (array_from_seq (_) (
            array_to_seq (lift_to_both0 mac_key_379))) in
      letb my_tag_386 : block_t :=
        xor_block (array_from_seq (_) (
            array_to_seq (lift_to_both0 my_tag_385))) (
          lift_to_both0 tag_mix_381) in
      letb ptxt_387 : seq uint8 :=
        aes128_decrypt (array_from_seq (_) (lift_to_both0 key_378)) (
          lift_to_both0 iv_380) (secret (lift_to_both0 (@repr U32 2))) (
          lift_to_both0 cipher_text_383) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        if is_pure (I := [interface]) (array_declassify_eq (
            lift_to_both0 my_tag_386) (array_from_seq (_) (
              array_to_seq (lift_to_both0 tag_388))))
        then @Ok byte_seq int8 (lift_to_both0 ptxt_387)
        else @Err byte_seq int8 (lift_to_both0 invalid_tag_v))
      ) : both (CEfset ([padded_msg_351_loc])) [interface] (
      aes_gcm_byte_seq_result_t)).
Fail Next Obligation.


Notation "'decrypt_aes128_inp'" :=(
  key128_t '× aes_nonce_t '× byte_seq '× byte_seq '× gf128_tag_t : choice_type) (in custom pack_type at level 2).
Notation "'decrypt_aes128_inp'" :=(
  key128_t '× aes_nonce_t '× byte_seq '× byte_seq '× gf128_tag_t : ChoiceEquality) (at level 2).
Notation "'decrypt_aes128_out'" :=(
  aes_gcm_byte_seq_result_t : choice_type) (in custom pack_type at level 2).
Notation "'decrypt_aes128_out'" :=(
  aes_gcm_byte_seq_result_t : ChoiceEquality) (at level 2).
Definition DECRYPT_AES128 : nat :=
  395.
Program Definition decrypt_aes128 (key_390 : key128_t) (iv_391 : aes_nonce_t) (
    aad_392 : byte_seq) (cipher_text_393 : byte_seq) (tag_394 : gf128_tag_t)
  : both (CEfset ([padded_msg_351_loc])) [interface] (
    aes_gcm_byte_seq_result_t) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (decrypt_aes (
          seq_from_seq (array_to_seq (lift_to_both0 key_390))) (
          lift_to_both0 iv_391) (lift_to_both0 aad_392) (
          lift_to_both0 cipher_text_393) (lift_to_both0 tag_394))
      ) : both (CEfset ([padded_msg_351_loc])) [interface] (
      aes_gcm_byte_seq_result_t)).
Fail Next Obligation.

