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

Definition pad_aad_msg_pure
  (aad_578 : byte_seq)
  (msg_579 : byte_seq)
  : byte_seq :=
  let laad_580 : uint_size :=
    seq_len (aad_578) in 
  let lmsg_581 : uint_size :=
    seq_len (msg_579) in 
  let pad_aad_582 : uint_size :=
    (if (((((laad_580) %% (usize 16))) =.? (
            usize 0))):bool_ChoiceEquality then (laad_580) else (((
            laad_580) .+ (((usize 16) .- (((laad_580) %% (usize 16)))))))) in 
  let pad_msg_583 : uint_size :=
    (if (((((lmsg_581) %% (usize 16))) =.? (
            usize 0))):bool_ChoiceEquality then (lmsg_581) else (((
            lmsg_581) .+ (((usize 16) .- (((lmsg_581) %% (usize 16)))))))) in 
  let padded_msg_576 : seq uint8 :=
    seq_new_ (default : uint8) (((((pad_aad_582) .+ (pad_msg_583))) .+ (
          usize 16))) in 
  let padded_msg_576 :=
    seq_update (padded_msg_576) (usize 0) (aad_578) in 
  let padded_msg_576 :=
    seq_update (padded_msg_576) (pad_aad_582) (msg_579) in 
  let padded_msg_576 :=
    seq_update (padded_msg_576) (((pad_aad_582) .+ (pad_msg_583))) (
      array_to_seq (uint64_to_be_bytes (((secret (pub_u64 (laad_580))) .* (
            secret (@repr U64 8)))))) in 
  let padded_msg_576 :=
    seq_update (padded_msg_576) (((((pad_aad_582) .+ (pad_msg_583))) .+ (
          usize 8))) (array_to_seq (uint64_to_be_bytes (((secret (pub_u64 (
                lmsg_581))) .* (secret (@repr U64 8)))))) in 
  padded_msg_576.
Definition pad_aad_msg_pure_code
  (aad_578 : byte_seq)
  (msg_579 : byte_seq)
  : code fset.fset0 [interface] (@ct (byte_seq)) :=
  lift_to_code (pad_aad_msg_pure aad_578 msg_579).

Definition padded_msg_576_loc : ChoiceEqualityLocation :=
  ((seq uint8 ; 648%nat)).
Notation "'pad_aad_msg_state_inp'" := (
  byte_seq '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'pad_aad_msg_state_out'" := (
  byte_seq : choice_type) (in custom pack_type at level 2).
Definition PAD_AAD_MSG_STATE : nat :=
  (649).
Program Definition pad_aad_msg_state
   : package (CEfset ([padded_msg_576_loc])) [interface] [interface
  #val #[ PAD_AAD_MSG_STATE ] : pad_aad_msg_state_inp → pad_aad_msg_state_out
  ] :=
  (
    [package #def #[ PAD_AAD_MSG_STATE ] (temp_inp : pad_aad_msg_state_inp) : pad_aad_msg_state_out { 
    let '(aad_578 , msg_579) := temp_inp : byte_seq '× byte_seq in
    ({ code  '(laad_580 : uint_size) ←
        ( '(temp_585 : uint_size) ←
            (seq_len (aad_578)) ;;
          ret (temp_585)) ;;
       '(lmsg_581 : uint_size) ←
        ( '(temp_587 : uint_size) ←
            (seq_len (msg_579)) ;;
          ret (temp_587)) ;;
       '(pad_aad_582 : uint_size) ←
        ( '(temp_589 : uint_size) ←
            ((laad_580) %% (usize 16)) ;;
           '(temp_591 : bool_ChoiceEquality) ←
            ((temp_589) =.? (usize 0)) ;;
           '(temp_593 : uint_size) ←
            ((laad_580) %% (usize 16)) ;;
           '(temp_595 : uint_size) ←
            ((usize 16) .- (temp_593)) ;;
           '(temp_597 : uint_size) ←
            ((laad_580) .+ (temp_595)) ;;
          ret ((if (temp_591):bool_ChoiceEquality then (*inline*) (
                laad_580) else (temp_597)))) ;;
       '(pad_msg_583 : uint_size) ←
        ( '(temp_599 : uint_size) ←
            ((lmsg_581) %% (usize 16)) ;;
           '(temp_601 : bool_ChoiceEquality) ←
            ((temp_599) =.? (usize 0)) ;;
           '(temp_603 : uint_size) ←
            ((lmsg_581) %% (usize 16)) ;;
           '(temp_605 : uint_size) ←
            ((usize 16) .- (temp_603)) ;;
           '(temp_607 : uint_size) ←
            ((lmsg_581) .+ (temp_605)) ;;
          ret ((if (temp_601):bool_ChoiceEquality then (*inline*) (
                lmsg_581) else (temp_607)))) ;;
       '(padded_msg_576 : seq uint8) ←
          ( '(temp_609 : uint_size) ←
              ((pad_aad_582) .+ (pad_msg_583)) ;;
             '(temp_611 : uint_size) ←
              ((temp_609) .+ (usize 16)) ;;
             temp_613 ←
              (seq_new_ (default : uint8) (temp_611)) ;;
            ret (temp_613)) ;;
        #put padded_msg_576_loc := padded_msg_576 ;;
       '(padded_msg_576 : seq uint8) ←
          (( '(temp_615 : seq uint8) ←
                (seq_update (padded_msg_576) (usize 0) (aad_578)) ;;
              ret (temp_615))) ;;
        #put padded_msg_576_loc := padded_msg_576 ;;
      
       '(padded_msg_576 : seq uint8) ←
          (( '(temp_617 : seq uint8) ←
                (seq_update (padded_msg_576) (pad_aad_582) (msg_579)) ;;
              ret (temp_617))) ;;
        #put padded_msg_576_loc := padded_msg_576 ;;
      
       '(padded_msg_576 : seq uint8) ←
          (( '(temp_619 : uint_size) ←
                ((pad_aad_582) .+ (pad_msg_583)) ;;
               '(temp_621 : int64) ←
                (secret (pub_u64 (laad_580))) ;;
               '(temp_623 : int64) ←
                (secret (@repr U64 8)) ;;
               '(temp_625 : uint64) ←
                ((temp_621) .* (temp_623)) ;;
               '(temp_627 : uint64_word_t) ←
                (uint64_to_be_bytes (temp_625)) ;;
               '(temp_629 : seq uint8) ←
                (array_to_seq (temp_627)) ;;
               '(temp_631 : seq uint8) ←
                (seq_update (padded_msg_576) (temp_619) (temp_629)) ;;
              ret (temp_631))) ;;
        #put padded_msg_576_loc := padded_msg_576 ;;
      
       '(padded_msg_576 : seq uint8) ←
          (( '(temp_633 : uint_size) ←
                ((pad_aad_582) .+ (pad_msg_583)) ;;
               '(temp_635 : uint_size) ←
                ((temp_633) .+ (usize 8)) ;;
               '(temp_637 : int64) ←
                (secret (pub_u64 (lmsg_581))) ;;
               '(temp_639 : int64) ←
                (secret (@repr U64 8)) ;;
               '(temp_641 : uint64) ←
                ((temp_637) .* (temp_639)) ;;
               '(temp_643 : uint64_word_t) ←
                (uint64_to_be_bytes (temp_641)) ;;
               '(temp_645 : seq uint8) ←
                (array_to_seq (temp_643)) ;;
               '(temp_647 : seq uint8) ←
                (seq_update (padded_msg_576) (temp_635) (temp_645)) ;;
              ret (temp_647))) ;;
        #put padded_msg_576_loc := padded_msg_576 ;;
      
      @ret (seq uint8) (padded_msg_576) } : code (CEfset (
          [padded_msg_576_loc])) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_pad_aad_msg_state : package _ _ _ :=
  (pad_aad_msg_state).
Fail Next Obligation.

Notation "'pad_aad_msg_inp'" :=(
  byte_seq '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'pad_aad_msg_out'" :=(
  byte_seq : choice_type) (in custom pack_type at level 2).
Definition PAD_AAD_MSG : nat :=
  (650).
Program Definition pad_aad_msg
  (aad_578 : byte_seq)
  (msg_579 : byte_seq)
  :both (CEfset ([padded_msg_576_loc])) [interface] (byte_seq) :=
  letb laad_580 : uint_size := seq_len (lift_to_both0 aad_578) in
  letb lmsg_581 : uint_size := seq_len (lift_to_both0 msg_579) in
  letb pad_aad_582 : uint_size :=
    if is_pure (I := [interface]) (((lift_to_both0 laad_580) %% (lift_to_both0 (
            usize 16))) =.? (lift_to_both0 (usize 0)))
    then lift_to_both0 laad_580
    else (lift_to_both0 laad_580) .+ ((lift_to_both0 (usize 16)) .- ((
          lift_to_both0 laad_580) %% (lift_to_both0 (usize 16)))) in
  letb pad_msg_583 : uint_size :=
    if is_pure (I := [interface]) (((lift_to_both0 lmsg_581) %% (lift_to_both0 (
            usize 16))) =.? (lift_to_both0 (usize 0)))
    then lift_to_both0 lmsg_581
    else (lift_to_both0 lmsg_581) .+ ((lift_to_both0 (usize 16)) .- ((
          lift_to_both0 lmsg_581) %% (lift_to_both0 (usize 16)))) in
  letbm padded_msg_576 : seq uint8 loc( padded_msg_576_loc ) :=
    seq_new_ (default : uint8) (((lift_to_both0 pad_aad_582) .+ (
          lift_to_both0 pad_msg_583)) .+ (lift_to_both0 (usize 16))) in
  letbm padded_msg_576 loc( padded_msg_576_loc ) :=
    seq_update (lift_to_both0 padded_msg_576) (lift_to_both0 (usize 0)) (
      lift_to_both0 aad_578) in
  letbm padded_msg_576 loc( padded_msg_576_loc ) :=
    seq_update (lift_to_both0 padded_msg_576) (lift_to_both0 pad_aad_582) (
      lift_to_both0 msg_579) in
  letbm padded_msg_576 loc( padded_msg_576_loc ) :=
    seq_update (lift_to_both0 padded_msg_576) ((lift_to_both0 pad_aad_582) .+ (
        lift_to_both0 pad_msg_583)) (array_to_seq (uint64_to_be_bytes ((secret (
            pub_u64 (is_pure (lift_to_both0 laad_580)))) .* (secret (
            lift_to_both0 (@repr U64 8)))))) in
  letbm padded_msg_576 loc( padded_msg_576_loc ) :=
    seq_update (lift_to_both0 padded_msg_576) (((lift_to_both0 pad_aad_582) .+ (
          lift_to_both0 pad_msg_583)) .+ (lift_to_both0 (usize 8))) (
      array_to_seq (uint64_to_be_bytes ((secret (pub_u64 (is_pure (
                lift_to_both0 lmsg_581)))) .* (secret (lift_to_both0 (
              @repr U64 8)))))) in
  lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
    lift_to_both0 padded_msg_576)
  .
Fail Next Obligation.

Definition encrypt_aes_pure
  (key_651 : byte_seq)
  (iv_652 : aes_nonce_t)
  (aad_653 : byte_seq)
  (msg_654 : byte_seq)
  : (byte_seq '× gf128_tag_t) :=
  let iv0_655 : aes_nonce_t :=
    array_new_ (default : uint8) (_) in 
  let mac_key_656 : block_t :=
    result_unwrap (aes_ctr_key_block (key_651) (iv0_655) (secret (
          @repr U32 0)) (key_length_v) (rounds_v) (key_schedule_length_v) (
        key_length_v) (iterations_v)) in 
  let tag_mix_657 : block_t :=
    result_unwrap (aes_ctr_key_block (key_651) ((iv_652)) (secret (
          @repr U32 1)) (key_length_v) (rounds_v) (key_schedule_length_v) (
        key_length_v) (iterations_v)) in 
  let cipher_text_658 : seq uint8 :=
    aes128_encrypt (array_from_seq (_) (key_651)) (iv_652) (secret (
        @repr U32 2)) (msg_654) in 
  let padded_msg_659 : seq uint8 :=
    pad_aad_msg (aad_653) (cipher_text_658) in 
  let tag_660 : gf128_tag_t :=
    gmac (padded_msg_659) (array_from_seq (_) (array_to_seq (mac_key_656))) in 
  let tag_661 : block_t :=
    xor_block (array_from_seq (_) (array_to_seq (tag_660))) (tag_mix_657) in 
  prod_ce(cipher_text_658, array_from_seq (_) (array_to_seq (tag_661))).
Definition encrypt_aes_pure_code
  (key_651 : byte_seq)
  (iv_652 : aes_nonce_t)
  (aad_653 : byte_seq)
  (msg_654 : byte_seq)
  : code fset.fset0 [interface] (@ct ((byte_seq '× gf128_tag_t))) :=
  lift_to_code (encrypt_aes_pure key_651 iv_652 aad_653 msg_654).


Notation "'encrypt_aes_state_inp'" := (
  byte_seq '× aes_nonce_t '× byte_seq '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'encrypt_aes_state_out'" := ((byte_seq '× gf128_tag_t
  ) : choice_type) (in custom pack_type at level 2).
Definition ENCRYPT_AES_STATE : nat :=
  (700).
Program Definition encrypt_aes_state
   : package (CEfset ([])) [interface
  #val #[ PAD_AAD_MSG_STATE ] : pad_aad_msg_state_inp → pad_aad_msg_state_out
  ] [interface
  #val #[ ENCRYPT_AES_STATE ] : encrypt_aes_state_inp → encrypt_aes_state_out
  ] :=
  (
    [package #def #[ ENCRYPT_AES_STATE ] (temp_inp : encrypt_aes_state_inp) : encrypt_aes_state_out { 
    let '(
      key_651 , iv_652 , aad_653 , msg_654) := temp_inp : byte_seq '× aes_nonce_t '× byte_seq '× byte_seq in
    #import {sig #[ PAD_AAD_MSG_STATE ] : pad_aad_msg_state_inp → pad_aad_msg_state_out } as pad_aad_msg_state ;;
    let pad_aad_msg_state := fun x_0 x_1 => pad_aad_msg_state (x_0,x_1) in
    ({ code  '(iv0_655 : aes_nonce_t) ←
        ( '(temp_663 : aes_nonce_t) ←
            (array_new_ (default : uint8) (_)) ;;
          ret (temp_663)) ;;
       '(mac_key_656 : block_t) ←
        ( '(temp_665 : int32) ←
            (secret (@repr U32 0)) ;;
           temp_667 ←
            (aes_ctr_key_block (key_651) (iv0_655) (temp_665) (key_length_v) (
                rounds_v) (key_schedule_length_v) (key_length_v) (
                iterations_v)) ;;
           temp_669 ←
            (result_unwrap (temp_667)) ;;
          ret (temp_669)) ;;
       '(tag_mix_657 : block_t) ←
        ( '(temp_671 : int32) ←
            (secret (@repr U32 1)) ;;
           temp_673 ←
            (aes_ctr_key_block (key_651) ((iv_652)) (temp_671) (key_length_v) (
                rounds_v) (key_schedule_length_v) (key_length_v) (
                iterations_v)) ;;
           temp_675 ←
            (result_unwrap (temp_673)) ;;
          ret (temp_675)) ;;
       '(cipher_text_658 : seq uint8) ←
        ( '(temp_677 : key128_t) ←
            (array_from_seq (_) (key_651)) ;;
           '(temp_679 : int32) ←
            (secret (@repr U32 2)) ;;
           temp_681 ←
            (aes128_encrypt (temp_677) (iv_652) (temp_679) (msg_654)) ;;
          ret (temp_681)) ;;
       '(padded_msg_659 : seq uint8) ←
        ( temp_683 ←
            (pad_aad_msg (aad_653) (cipher_text_658)) ;;
          ret (temp_683)) ;;
       '(tag_660 : gf128_tag_t) ←
        ( '(temp_685 : seq uint8) ←
            (array_to_seq (mac_key_656)) ;;
           '(temp_687 : gf128_key_t) ←
            (array_from_seq (_) (temp_685)) ;;
           temp_689 ←
            (gmac (padded_msg_659) (temp_687)) ;;
          ret (temp_689)) ;;
       '(tag_661 : block_t) ←
        ( '(temp_691 : seq uint8) ←
            (array_to_seq (tag_660)) ;;
           '(temp_693 : block_t) ←
            (array_from_seq (_) (temp_691)) ;;
           temp_695 ←
            (xor_block (temp_693) (tag_mix_657)) ;;
          ret (temp_695)) ;;
       '(temp_697 : seq uint8) ←
        (array_to_seq (tag_661)) ;;
       '(temp_699 : gf128_tag_t) ←
        (array_from_seq (_) (temp_697)) ;;
      @ret ((seq uint8 '× gf128_tag_t)) (prod_ce(cipher_text_658, temp_699
        )) } : code (CEfset ([])) [interface
      #val #[ PAD_AAD_MSG_STATE ] : pad_aad_msg_state_inp → pad_aad_msg_state_out
      ] _)
    }]).
Fail Next Obligation.
Program Definition package_encrypt_aes_state : package _ _ _ :=
  (seq_link encrypt_aes_state link_rest(package_pad_aad_msg_state)).
Fail Next Obligation.

Notation "'encrypt_aes_inp'" :=(
  byte_seq '× aes_nonce_t '× byte_seq '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'encrypt_aes_out'" :=((byte_seq '× gf128_tag_t
  ) : choice_type) (in custom pack_type at level 2).
Definition ENCRYPT_AES : nat :=
  (701).
Program Definition encrypt_aes
  (key_651 : byte_seq)
  (iv_652 : aes_nonce_t)
  (aad_653 : byte_seq)
  (msg_654 : byte_seq)
  :both (CEfset ([])) [interface
  #val #[ AES128_ENCRYPT ] : aes128_encrypt_inp → aes128_encrypt_out ;
  #val #[ AES_CTR_KEY_BLOCK ] : aes_ctr_key_block_inp → aes_ctr_key_block_out ;
  #val #[ GMAC ] : gmac_inp → gmac_out ;
  #val #[ PAD_AAD_MSG ] : pad_aad_msg_inp → pad_aad_msg_out ;
  #val #[ XOR_BLOCK ] : xor_block_inp → xor_block_out ] ((
      byte_seq '×
      gf128_tag_t
    )) :=
  #import {sig #[ AES128_ENCRYPT ] : aes128_encrypt_inp → aes128_encrypt_out } as aes128_encrypt ;;
  let aes128_encrypt := fun x_0 x_1 x_2 x_3 => aes128_encrypt (
    x_0,x_1,x_2,x_3) in
  #import {sig #[ AES_CTR_KEY_BLOCK ] : aes_ctr_key_block_inp → aes_ctr_key_block_out } as aes_ctr_key_block ;;
  let aes_ctr_key_block := fun x_0 x_1 x_2 x_3 x_4 x_5 x_6 x_7 => aes_ctr_key_block (
    x_0,x_1,x_2,x_3,x_4,x_5,x_6,x_7) in
  #import {sig #[ GMAC ] : gmac_inp → gmac_out } as gmac ;;
  let gmac := fun x_0 x_1 => gmac (x_0,x_1) in
  #import {sig #[ PAD_AAD_MSG ] : pad_aad_msg_inp → pad_aad_msg_out } as pad_aad_msg ;;
  let pad_aad_msg := fun x_0 x_1 => pad_aad_msg (x_0,x_1) in
  #import {sig #[ XOR_BLOCK ] : xor_block_inp → xor_block_out } as xor_block ;;
  let xor_block := fun x_0 x_1 => xor_block (x_0,x_1) in
  letb iv0_655 : aes_nonce_t := array_new_ (default : uint8) (_) in
  letb mac_key_656 : block_t :=
    result_unwrap (aes_ctr_key_block (lift_to_both0 key_651) (
        lift_to_both0 iv0_655) (secret (lift_to_both0 (@repr U32 0))) (
        lift_to_both0 key_length_v) (lift_to_both0 rounds_v) (
        lift_to_both0 key_schedule_length_v) (lift_to_both0 key_length_v) (
        lift_to_both0 iterations_v)) in
  letb tag_mix_657 : block_t :=
    result_unwrap (aes_ctr_key_block (lift_to_both0 key_651) ((
          lift_to_both0 iv_652)) (secret (lift_to_both0 (@repr U32 1))) (
        lift_to_both0 key_length_v) (lift_to_both0 rounds_v) (
        lift_to_both0 key_schedule_length_v) (lift_to_both0 key_length_v) (
        lift_to_both0 iterations_v)) in
  letb cipher_text_658 : seq uint8 :=
    aes128_encrypt (array_from_seq (_) (lift_to_both0 key_651)) (
      lift_to_both0 iv_652) (secret (lift_to_both0 (@repr U32 2))) (
      lift_to_both0 msg_654) in
  letb padded_msg_659 : seq uint8 :=
    pad_aad_msg (lift_to_both0 aad_653) (lift_to_both0 cipher_text_658) in
  letb tag_660 : gf128_tag_t :=
    gmac (lift_to_both0 padded_msg_659) (array_from_seq (_) (
        array_to_seq (lift_to_both0 mac_key_656))) in
  letb tag_661 : block_t :=
    xor_block (array_from_seq (_) (array_to_seq (lift_to_both0 tag_660))) (
      lift_to_both0 tag_mix_657) in
  lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
      lift_to_both0 cipher_text_658,
      array_from_seq (_) (array_to_seq (lift_to_both0 tag_661))
    ))
  .
Fail Next Obligation.

Definition encrypt_aes128_pure
  (key_702 : key128_t)
  (iv_703 : aes_nonce_t)
  (aad_704 : byte_seq)
  (msg_705 : byte_seq)
  : (byte_seq '× gf128_tag_t) :=
  encrypt_aes (seq_from_seq (array_to_seq (key_702))) (iv_703) (aad_704) (
    msg_705).
Definition encrypt_aes128_pure_code
  (key_702 : key128_t)
  (iv_703 : aes_nonce_t)
  (aad_704 : byte_seq)
  (msg_705 : byte_seq)
  : code fset.fset0 [interface] (@ct ((byte_seq '× gf128_tag_t))) :=
  lift_to_code (encrypt_aes128_pure key_702 iv_703 aad_704 msg_705).


Notation "'encrypt_aes128_state_inp'" := (
  key128_t '× aes_nonce_t '× byte_seq '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'encrypt_aes128_state_out'" := ((byte_seq '× gf128_tag_t
  ) : choice_type) (in custom pack_type at level 2).
Definition ENCRYPT_AES128_STATE : nat :=
  (712).
Program Definition encrypt_aes128_state
   : package (CEfset ([])) [interface
  #val #[ ENCRYPT_AES_STATE ] : encrypt_aes_state_inp → encrypt_aes_state_out
  ] [interface
  #val #[ ENCRYPT_AES128_STATE ] : encrypt_aes128_state_inp → encrypt_aes128_state_out
  ] :=
  (
    [package #def #[ ENCRYPT_AES128_STATE ] (temp_inp : encrypt_aes128_state_inp) : encrypt_aes128_state_out { 
    let '(
      key_702 , iv_703 , aad_704 , msg_705) := temp_inp : key128_t '× aes_nonce_t '× byte_seq '× byte_seq in
    #import {sig #[ ENCRYPT_AES_STATE ] : encrypt_aes_state_inp → encrypt_aes_state_out } as encrypt_aes_state ;;
    let encrypt_aes_state := fun x_0 x_1 x_2 x_3 => encrypt_aes_state (
      x_0,x_1,x_2,x_3) in
    ({ code  '(temp_707 : seq uint8) ←
        (array_to_seq (key_702)) ;;
       '(temp_709 : byte_seq) ←
        (seq_from_seq (temp_707)) ;;
       temp_711 ←
        (encrypt_aes (temp_709) (iv_703) (aad_704) (msg_705)) ;;
      @ret ((byte_seq '× gf128_tag_t)) (temp_711) } : code (CEfset (
          [])) [interface
      #val #[ ENCRYPT_AES_STATE ] : encrypt_aes_state_inp → encrypt_aes_state_out
      ] _)
    }]).
Fail Next Obligation.
Program Definition package_encrypt_aes128_state : package _ _ _ :=
  (seq_link encrypt_aes128_state link_rest(package_encrypt_aes_state)).
Fail Next Obligation.

Notation "'encrypt_aes128_inp'" :=(
  key128_t '× aes_nonce_t '× byte_seq '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'encrypt_aes128_out'" :=((byte_seq '× gf128_tag_t
  ) : choice_type) (in custom pack_type at level 2).
Definition ENCRYPT_AES128 : nat :=
  (713).
Program Definition encrypt_aes128
  (key_702 : key128_t)
  (iv_703 : aes_nonce_t)
  (aad_704 : byte_seq)
  (msg_705 : byte_seq)
  :both (CEfset ([])) [interface
  #val #[ ENCRYPT_AES ] : encrypt_aes_inp → encrypt_aes_out ] ((
      byte_seq '×
      gf128_tag_t
    )) :=
  #import {sig #[ ENCRYPT_AES ] : encrypt_aes_inp → encrypt_aes_out } as encrypt_aes ;;
  let encrypt_aes := fun x_0 x_1 x_2 x_3 => encrypt_aes (x_0,x_1,x_2,x_3) in
  lift_scope (H_loc_incl := _) (H_opsig_incl := _) (encrypt_aes (seq_from_seq (
        array_to_seq (lift_to_both0 key_702))) (lift_to_both0 iv_703) (
      lift_to_both0 aad_704) (lift_to_both0 msg_705))
  .
Fail Next Obligation.

Definition decrypt_aes_pure
  (key_714 : byte_seq)
  (iv_715 : aes_nonce_t)
  (aad_716 : byte_seq)
  (cipher_text_717 : byte_seq)
  (tag_718 : gf128_tag_t)
  : aes_gcm_byte_seq_result_t :=
  let iv0_719 : aes_nonce_t :=
    array_new_ (default : uint8) (_) in 
   mac_key_720 m( _ ) ⇠ (aes_ctr_key_block (key_714) (iv0_719) (secret (
        @repr U32 0)) (key_length_v) (rounds_v) (key_schedule_length_v) (
      key_length_v) (iterations_v)) ;;
  ( tag_mix_721 m( _ ) ⇠ (aes_ctr_key_block (key_714) ((iv_715)) (secret (
          @repr U32 1)) (key_length_v) (rounds_v) (key_schedule_length_v) (
        key_length_v) (iterations_v)) ;;
    (let padded_msg_722 : seq uint8 :=
        pad_aad_msg (aad_716) (cipher_text_717) in 
      let my_tag_723 : gf128_tag_t :=
        gmac (padded_msg_722) (array_from_seq (_) (
            array_to_seq (mac_key_720))) in 
      let my_tag_724 : block_t :=
        xor_block (array_from_seq (_) (array_to_seq (my_tag_723))) (
          tag_mix_721) in 
      let ptxt_725 : seq uint8 :=
        aes128_decrypt (array_from_seq (_) (key_714)) (iv_715) (secret (
            @repr U32 2)) (cipher_text_717) in 
      (if (array_declassify_eq (my_tag_724) (array_from_seq (_) (
              array_to_seq (tag_718)))):bool_ChoiceEquality then (
          @Ok byte_seq int8 (ptxt_725)) else (@Err byte_seq int8 (
            invalid_tag_v))))).
Definition decrypt_aes_pure_code
  (key_714 : byte_seq)
  (iv_715 : aes_nonce_t)
  (aad_716 : byte_seq)
  (cipher_text_717 : byte_seq)
  (tag_718 : gf128_tag_t)
  : code fset.fset0 [interface] (@ct (aes_gcm_byte_seq_result_t)) :=
  lift_to_code (decrypt_aes_pure key_714
    iv_715
    aad_716
    cipher_text_717
    tag_718).


Notation "'decrypt_aes_state_inp'" := (
  byte_seq '× aes_nonce_t '× byte_seq '× byte_seq '× gf128_tag_t : choice_type) (in custom pack_type at level 2).
Notation "'decrypt_aes_state_out'" := (
  aes_gcm_byte_seq_result_t : choice_type) (in custom pack_type at level 2).
Definition DECRYPT_AES_STATE : nat :=
  (762).
Program Definition decrypt_aes_state
   : package (CEfset ([])) [interface
  #val #[ PAD_AAD_MSG_STATE ] : pad_aad_msg_state_inp → pad_aad_msg_state_out
  ] [interface
  #val #[ DECRYPT_AES_STATE ] : decrypt_aes_state_inp → decrypt_aes_state_out
  ] :=
  (
    [package #def #[ DECRYPT_AES_STATE ] (temp_inp : decrypt_aes_state_inp) : decrypt_aes_state_out { 
    let '(
      key_714 , iv_715 , aad_716 , cipher_text_717 , tag_718) := temp_inp : byte_seq '× aes_nonce_t '× byte_seq '× byte_seq '× gf128_tag_t in
    #import {sig #[ PAD_AAD_MSG_STATE ] : pad_aad_msg_state_inp → pad_aad_msg_state_out } as pad_aad_msg_state ;;
    let pad_aad_msg_state := fun x_0 x_1 => pad_aad_msg_state (x_0,x_1) in
    ({ code  '(iv0_719 : aes_nonce_t) ←
        ( '(temp_727 : aes_nonce_t) ←
            (array_new_ (default : uint8) (_)) ;;
          ret (temp_727)) ;;
      bnd(ChoiceEqualityMonad.result_bind_code int8 , block_t , _ , CEfset (
          [])) mac_key_720 ⇠
      (({ code  '(temp_729 : int32) ←
            (secret (@repr U32 0)) ;;
           temp_731 ←
            (aes_ctr_key_block (key_714) (iv0_719) (temp_729) (key_length_v) (
                rounds_v) (key_schedule_length_v) (key_length_v) (
                iterations_v)) ;;
          @ret _ (temp_731) } : code (fset.fset0) [interface
          #val #[ AES_CTR_KEY_BLOCK ] : aes_ctr_key_block_inp → aes_ctr_key_block_out
          ] _)) in
      ({ code bnd(
          ChoiceEqualityMonad.result_bind_code int8 , block_t , _ , CEfset (
            [])) tag_mix_721 ⇠
        (({ code  '(temp_733 : int32) ←
              (secret (@repr U32 1)) ;;
             temp_735 ←
              (aes_ctr_key_block (key_714) ((iv_715)) (temp_733) (
                  key_length_v) (rounds_v) (key_schedule_length_v) (
                  key_length_v) (iterations_v)) ;;
            @ret _ (temp_735) } : code (fset.fset0) [interface
            #val #[ AES_CTR_KEY_BLOCK ] : aes_ctr_key_block_inp → aes_ctr_key_block_out
            ] _)) in
        ({ code  '(padded_msg_722 : seq uint8) ←
            ( temp_737 ←
                (pad_aad_msg (aad_716) (cipher_text_717)) ;;
              ret (temp_737)) ;;
           '(my_tag_723 : gf128_tag_t) ←
            ( '(temp_739 : seq uint8) ←
                (array_to_seq (mac_key_720)) ;;
               '(temp_741 : gf128_key_t) ←
                (array_from_seq (_) (temp_739)) ;;
               temp_743 ←
                (gmac (padded_msg_722) (temp_741)) ;;
              ret (temp_743)) ;;
           '(my_tag_724 : block_t) ←
            ( '(temp_745 : seq uint8) ←
                (array_to_seq (my_tag_723)) ;;
               '(temp_747 : block_t) ←
                (array_from_seq (_) (temp_745)) ;;
               temp_749 ←
                (xor_block (temp_747) (tag_mix_721)) ;;
              ret (temp_749)) ;;
           '(ptxt_725 : seq uint8) ←
            ( '(temp_751 : key128_t) ←
                (array_from_seq (_) (key_714)) ;;
               '(temp_753 : int32) ←
                (secret (@repr U32 2)) ;;
               temp_755 ←
                (aes128_decrypt (temp_751) (iv_715) (temp_753) (
                    cipher_text_717)) ;;
              ret (temp_755)) ;;
           '(temp_757 : seq uint8) ←
            (array_to_seq (tag_718)) ;;
           '(temp_759 : block_t) ←
            (array_from_seq (_) (temp_757)) ;;
           temp_761 ←
            (array_declassify_eq (my_tag_724) (temp_759)) ;;
          @ret ((result int8 byte_seq)) ((if (
                temp_761):bool_ChoiceEquality then (*inline*) (
                @inl byte_seq int8 (ptxt_725)) else (@inr byte_seq int8 (
                  invalid_tag_v)))) } : code (CEfset ([])) [interface
          #val #[ PAD_AAD_MSG_STATE ] : pad_aad_msg_state_inp → pad_aad_msg_state_out
          ] _) } : code (CEfset ([])) [interface
        #val #[ PAD_AAD_MSG_STATE ] : pad_aad_msg_state_inp → pad_aad_msg_state_out
        ] _) } : code (CEfset ([])) [interface
      #val #[ PAD_AAD_MSG_STATE ] : pad_aad_msg_state_inp → pad_aad_msg_state_out
      ] _)
    }]).
Fail Next Obligation.
Program Definition package_decrypt_aes_state : package _ _ _ :=
  (seq_link decrypt_aes_state link_rest(package_pad_aad_msg_state)).
Fail Next Obligation.

Notation "'decrypt_aes_inp'" :=(
  byte_seq '× aes_nonce_t '× byte_seq '× byte_seq '× gf128_tag_t : choice_type) (in custom pack_type at level 2).
Notation "'decrypt_aes_out'" :=(
  aes_gcm_byte_seq_result_t : choice_type) (in custom pack_type at level 2).
Definition DECRYPT_AES : nat :=
  (763).
Program Definition decrypt_aes
  (key_714 : byte_seq)
  (iv_715 : aes_nonce_t)
  (aad_716 : byte_seq)
  (cipher_text_717 : byte_seq)
  (tag_718 : gf128_tag_t)
  :both (CEfset ([])) [interface
  #val #[ AES128_DECRYPT ] : aes128_decrypt_inp → aes128_decrypt_out ;
  #val #[ AES_CTR_KEY_BLOCK ] : aes_ctr_key_block_inp → aes_ctr_key_block_out ;
  #val #[ GMAC ] : gmac_inp → gmac_out ;
  #val #[ PAD_AAD_MSG ] : pad_aad_msg_inp → pad_aad_msg_out ;
  #val #[ XOR_BLOCK ] : xor_block_inp → xor_block_out ] (
    aes_gcm_byte_seq_result_t) :=
  #import {sig #[ AES128_DECRYPT ] : aes128_decrypt_inp → aes128_decrypt_out } as aes128_decrypt ;;
  let aes128_decrypt := fun x_0 x_1 x_2 x_3 => aes128_decrypt (
    x_0,x_1,x_2,x_3) in
  #import {sig #[ AES_CTR_KEY_BLOCK ] : aes_ctr_key_block_inp → aes_ctr_key_block_out } as aes_ctr_key_block ;;
  let aes_ctr_key_block := fun x_0 x_1 x_2 x_3 x_4 x_5 x_6 x_7 => aes_ctr_key_block (
    x_0,x_1,x_2,x_3,x_4,x_5,x_6,x_7) in
  #import {sig #[ GMAC ] : gmac_inp → gmac_out } as gmac ;;
  let gmac := fun x_0 x_1 => gmac (x_0,x_1) in
  #import {sig #[ PAD_AAD_MSG ] : pad_aad_msg_inp → pad_aad_msg_out } as pad_aad_msg ;;
  let pad_aad_msg := fun x_0 x_1 => pad_aad_msg (x_0,x_1) in
  #import {sig #[ XOR_BLOCK ] : xor_block_inp → xor_block_out } as xor_block ;;
  let xor_block := fun x_0 x_1 => xor_block (x_0,x_1) in
  letb iv0_719 : aes_nonce_t := array_new_ (default : uint8) (_) in
  letbnd(ChoiceEqualityMonad.result_bind_both int8) mac_key_720 : block_t :=
    aes_ctr_key_block (lift_to_both0 key_714) (lift_to_both0 iv0_719) (secret (
        lift_to_both0 (@repr U32 0))) (lift_to_both0 key_length_v) (
      lift_to_both0 rounds_v) (lift_to_both0 key_schedule_length_v) (
      lift_to_both0 key_length_v) (lift_to_both0 iterations_v) in
  letbnd(ChoiceEqualityMonad.result_bind_both int8) tag_mix_721 : block_t :=
    aes_ctr_key_block (lift_to_both0 key_714) ((lift_to_both0 iv_715)) (secret (
        lift_to_both0 (@repr U32 1))) (lift_to_both0 key_length_v) (
      lift_to_both0 rounds_v) (lift_to_both0 key_schedule_length_v) (
      lift_to_both0 key_length_v) (lift_to_both0 iterations_v) in
  letb padded_msg_722 : seq uint8 :=
    pad_aad_msg (lift_to_both0 aad_716) (lift_to_both0 cipher_text_717) in
  letb my_tag_723 : gf128_tag_t :=
    gmac (lift_to_both0 padded_msg_722) (array_from_seq (_) (
        array_to_seq (lift_to_both0 mac_key_720))) in
  letb my_tag_724 : block_t :=
    xor_block (array_from_seq (_) (array_to_seq (lift_to_both0 my_tag_723))) (
      lift_to_both0 tag_mix_721) in
  letb ptxt_725 : seq uint8 :=
    aes128_decrypt (array_from_seq (_) (lift_to_both0 key_714)) (
      lift_to_both0 iv_715) (secret (lift_to_both0 (@repr U32 2))) (
      lift_to_both0 cipher_text_717) in
  lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
    if is_pure (I := [interface]) (array_declassify_eq (
        lift_to_both0 my_tag_724) (array_from_seq (_) (
          array_to_seq (lift_to_both0 tag_718))))
    then @Ok byte_seq int8 (lift_to_both0 ptxt_725)
    else @Err byte_seq int8 (lift_to_both0 invalid_tag_v))
  .
Fail Next Obligation.

Definition decrypt_aes128_pure
  (key_764 : key128_t)
  (iv_765 : aes_nonce_t)
  (aad_766 : byte_seq)
  (cipher_text_767 : byte_seq)
  (tag_768 : gf128_tag_t)
  : aes_gcm_byte_seq_result_t :=
  decrypt_aes (seq_from_seq (array_to_seq (key_764))) (iv_765) (aad_766) (
    cipher_text_767) (tag_768).
Definition decrypt_aes128_pure_code
  (key_764 : key128_t)
  (iv_765 : aes_nonce_t)
  (aad_766 : byte_seq)
  (cipher_text_767 : byte_seq)
  (tag_768 : gf128_tag_t)
  : code fset.fset0 [interface] (@ct (aes_gcm_byte_seq_result_t)) :=
  lift_to_code (decrypt_aes128_pure key_764
    iv_765
    aad_766
    cipher_text_767
    tag_768).


Notation "'decrypt_aes128_state_inp'" := (
  key128_t '× aes_nonce_t '× byte_seq '× byte_seq '× gf128_tag_t : choice_type) (in custom pack_type at level 2).
Notation "'decrypt_aes128_state_out'" := (
  aes_gcm_byte_seq_result_t : choice_type) (in custom pack_type at level 2).
Definition DECRYPT_AES128_STATE : nat :=
  (775).
Program Definition decrypt_aes128_state
   : package (CEfset ([])) [interface
  #val #[ DECRYPT_AES_STATE ] : decrypt_aes_state_inp → decrypt_aes_state_out
  ] [interface
  #val #[ DECRYPT_AES128_STATE ] : decrypt_aes128_state_inp → decrypt_aes128_state_out
  ] :=
  (
    [package #def #[ DECRYPT_AES128_STATE ] (temp_inp : decrypt_aes128_state_inp) : decrypt_aes128_state_out { 
    let '(
      key_764 , iv_765 , aad_766 , cipher_text_767 , tag_768) := temp_inp : key128_t '× aes_nonce_t '× byte_seq '× byte_seq '× gf128_tag_t in
    #import {sig #[ DECRYPT_AES_STATE ] : decrypt_aes_state_inp → decrypt_aes_state_out } as decrypt_aes_state ;;
    let decrypt_aes_state := fun x_0 x_1 x_2 x_3 x_4 => decrypt_aes_state (
      x_0,x_1,x_2,x_3,x_4) in
    ({ code  '(temp_770 : seq uint8) ←
        (array_to_seq (key_764)) ;;
       '(temp_772 : byte_seq) ←
        (seq_from_seq (temp_770)) ;;
       temp_774 ←
        (decrypt_aes (temp_772) (iv_765) (aad_766) (cipher_text_767) (
            tag_768)) ;;
      @ret (aes_gcm_byte_seq_result_t) (temp_774) } : code (CEfset (
          [])) [interface
      #val #[ DECRYPT_AES_STATE ] : decrypt_aes_state_inp → decrypt_aes_state_out
      ] _)
    }]).
Fail Next Obligation.
Program Definition package_decrypt_aes128_state : package _ _ _ :=
  (seq_link decrypt_aes128_state link_rest(package_decrypt_aes_state)).
Fail Next Obligation.

Notation "'decrypt_aes128_inp'" :=(
  key128_t '× aes_nonce_t '× byte_seq '× byte_seq '× gf128_tag_t : choice_type) (in custom pack_type at level 2).
Notation "'decrypt_aes128_out'" :=(
  aes_gcm_byte_seq_result_t : choice_type) (in custom pack_type at level 2).
Definition DECRYPT_AES128 : nat :=
  (776).
Program Definition decrypt_aes128
  (key_764 : key128_t)
  (iv_765 : aes_nonce_t)
  (aad_766 : byte_seq)
  (cipher_text_767 : byte_seq)
  (tag_768 : gf128_tag_t)
  :both (CEfset ([])) [interface
  #val #[ DECRYPT_AES ] : decrypt_aes_inp → decrypt_aes_out ] (
    aes_gcm_byte_seq_result_t) :=
  #import {sig #[ DECRYPT_AES ] : decrypt_aes_inp → decrypt_aes_out } as decrypt_aes ;;
  let decrypt_aes := fun x_0 x_1 x_2 x_3 x_4 => decrypt_aes (
    x_0,x_1,x_2,x_3,x_4) in
  lift_scope (H_loc_incl := _) (H_opsig_incl := _) (decrypt_aes (seq_from_seq (
        array_to_seq (lift_to_both0 key_764))) (lift_to_both0 iv_765) (
      lift_to_both0 aad_766) (lift_to_both0 cipher_text_767) (
      lift_to_both0 tag_768))
  .
Fail Next Obligation.

