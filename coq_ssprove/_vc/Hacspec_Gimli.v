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


Definition state_t := nseq (uint32) (usize 12).

Definition state_idx_t :=
  nat_mod (usize 12).
Definition uint_size_in_state_idx_t(n : uint_size) : state_idx_t := int_in_nat_mod n.
Coercion uint_size_in_state_idx_t : uint_size >-> state_idx_t.


Notation "'swap_inp'" :=(
  state_t '× state_idx_t '× state_idx_t : choice_type) (in custom pack_type at level 2).
Notation "'swap_inp'" :=(
  state_t '× state_idx_t '× state_idx_t : ChoiceEquality) (at level 2).
Notation "'swap_out'" :=(
  state_t : choice_type) (in custom pack_type at level 2).
Notation "'swap_out'" :=(state_t : ChoiceEquality) (at level 2).
Definition SWAP : nat :=
  1455.
Program Definition swap (s_1452 : state_t) (i_1451 : state_idx_t) (
    j_1454 : state_idx_t)
  : both (fset.fset0) [interface] (state_t) :=
  ((letb tmp_1453 : uint32 := array_index (s_1452) (lift_to_both0 i_1451) in
      letb s_1452 : state_t :=
        array_upd s_1452 (lift_to_both0 i_1451) (is_pure (array_index (s_1452) (
              lift_to_both0 j_1454))) in
      letb s_1452 : state_t :=
        array_upd s_1452 (lift_to_both0 j_1454) (is_pure (
            lift_to_both0 tmp_1453)) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 s_1452)
      ) : both (fset.fset0) [interface] (state_t)).
Fail Next Obligation.


Notation "'gimli_round_inp'" :=(
  state_t '× int32 : choice_type) (in custom pack_type at level 2).
Notation "'gimli_round_inp'" :=(
  state_t '× int32 : ChoiceEquality) (at level 2).
Notation "'gimli_round_out'" :=(
  state_t : choice_type) (in custom pack_type at level 2).
Notation "'gimli_round_out'" :=(state_t : ChoiceEquality) (at level 2).
Definition GIMLI_ROUND : nat :=
  1462.
Program Definition gimli_round (s_1456 : state_t) (r_1461 : int32)
  : both (fset.fset0) [interface] (state_t) :=
  ((letb s_1456 :=
        foldi_both' (lift_to_both0 (usize 0)) (lift_to_both0 (usize 4)) s_1456 (
            L := (fset.fset0)) (I := [interface]) (fun col_1457 s_1456 =>
            letb x_1458 : uint32 :=
              uint32_rotate_left (array_index (s_1456) (
                  lift_to_both0 col_1457)) (lift_to_both0 (usize 24)) in
            letb y_1459 : uint32 :=
              uint32_rotate_left (array_index (s_1456) ((
                    lift_to_both0 col_1457) .+ (lift_to_both0 (usize 4)))) (
                lift_to_both0 (usize 9)) in
            letb z_1460 : uint32 :=
              array_index (s_1456) ((lift_to_both0 col_1457) .+ (lift_to_both0 (
                    usize 8))) in
            letb s_1456 : state_t :=
              array_upd s_1456 ((lift_to_both0 col_1457) .+ (lift_to_both0 (
                    usize 8))) (is_pure (((lift_to_both0 x_1458) .^ ((
                        lift_to_both0 z_1460) shift_left (lift_to_both0 (
                          usize 1)))) .^ (((lift_to_both0 y_1459) .& (
                        lift_to_both0 z_1460)) shift_left (lift_to_both0 (
                        usize 2))))) in
            letb s_1456 : state_t :=
              array_upd s_1456 ((lift_to_both0 col_1457) .+ (lift_to_both0 (
                    usize 4))) (is_pure (((lift_to_both0 y_1459) .^ (
                      lift_to_both0 x_1458)) .^ (((lift_to_both0 x_1458) .| (
                        lift_to_both0 z_1460)) shift_left (lift_to_both0 (
                        usize 1))))) in
            letb s_1456 : state_t :=
              array_upd s_1456 (lift_to_both0 col_1457) (is_pure (((
                      lift_to_both0 z_1460) .^ (lift_to_both0 y_1459)) .^ (((
                        lift_to_both0 x_1458) .& (
                        lift_to_both0 y_1459)) shift_left (lift_to_both0 (
                        usize 3))))) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 s_1456)
            ) in
      letb '(s_1456) :=
        if ((lift_to_both0 r_1461) .& (lift_to_both0 (@repr U32 3))) =.? (
          lift_to_both0 (@repr U32 0)) :bool_ChoiceEquality
        then lift_scope (L1 := fset.fset0) (L2 := fset.fset0) (
          I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
          letbm s_1456 loc( s_1456_loc ) :=
            swap (lift_to_both0 s_1456) (lift_to_both0 (usize 0)) (
              lift_to_both0 (usize 1)) in
          letbm s_1456 loc( s_1456_loc ) :=
            swap (lift_to_both0 s_1456) (lift_to_both0 (usize 2)) (
              lift_to_both0 (usize 3)) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 s_1456)
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          lift_to_both0 s_1456)
         in
      letb '(s_1456) :=
        if ((lift_to_both0 r_1461) .& (lift_to_both0 (@repr U32 3))) =.? (
          lift_to_both0 (@repr U32 2)) :bool_ChoiceEquality
        then lift_scope (L1 := fset.fset0) (L2 := fset.fset0) (
          I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
          letbm s_1456 loc( s_1456_loc ) :=
            swap (lift_to_both0 s_1456) (lift_to_both0 (usize 0)) (
              lift_to_both0 (usize 2)) in
          letbm s_1456 loc( s_1456_loc ) :=
            swap (lift_to_both0 s_1456) (lift_to_both0 (usize 1)) (
              lift_to_both0 (usize 3)) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 s_1456)
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          lift_to_both0 s_1456)
         in
      letb '(s_1456) :=
        if ((lift_to_both0 r_1461) .& (lift_to_both0 (@repr U32 3))) =.? (
          lift_to_both0 (@repr U32 0)) :bool_ChoiceEquality
        then lift_scope (L1 := fset.fset0) (L2 := fset.fset0) (
          I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
          letb s_1456 : state_t :=
            array_upd s_1456 (lift_to_both0 (usize 0)) (is_pure ((array_index (
                    s_1456) (lift_to_both0 (usize 0))) .^ ((secret (
                      lift_to_both0 (@repr U32 2654435584))) .| (secret (
                      lift_to_both0 r_1461))))) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 s_1456)
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          lift_to_both0 s_1456)
         in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 s_1456)
      ) : both (fset.fset0) [interface] (state_t)).
Fail Next Obligation.


Notation "'gimli_inp'" :=(
  state_t : choice_type) (in custom pack_type at level 2).
Notation "'gimli_inp'" :=(state_t : ChoiceEquality) (at level 2).
Notation "'gimli_out'" :=(
  state_t : choice_type) (in custom pack_type at level 2).
Notation "'gimli_out'" :=(state_t : ChoiceEquality) (at level 2).
Definition GIMLI : nat :=
  1466.
Program Definition gimli (s_1463 : state_t)
  : both (fset.fset0) [interface] (state_t) :=
  ((letb s_1463 :=
        foldi_both' (lift_to_both0 (usize 0)) (lift_to_both0 (
              usize 24)) s_1463 (L := (fset.fset0)) (I := [interface]) (
            fun rnd_1464 s_1463 =>
            letb rnd_1465 : int32 :=
              pub_u32 (is_pure ((lift_to_both0 (usize 24)) .- (
                    lift_to_both0 rnd_1464))) in
            letbm s_1463 loc( s_1463_loc ) :=
              gimli_round (lift_to_both0 s_1463) (lift_to_both0 rnd_1465) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 s_1463)
            ) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 s_1463)
      ) : both (fset.fset0) [interface] (state_t)).
Fail Next Obligation.

Definition block_t := nseq (uint8) (usize 16).

Definition digest_t := nseq (uint8) (usize 32).


Notation "'absorb_block_inp'" :=(
  block_t '× state_t : choice_type) (in custom pack_type at level 2).
Notation "'absorb_block_inp'" :=(
  block_t '× state_t : ChoiceEquality) (at level 2).
Notation "'absorb_block_out'" :=(
  state_t : choice_type) (in custom pack_type at level 2).
Notation "'absorb_block_out'" :=(state_t : ChoiceEquality) (at level 2).
Definition ABSORB_BLOCK : nat :=
  1470.
Program Definition absorb_block (input_block_1467 : block_t) (s_1469 : state_t)
  : both (fset.fset0) [interface] (state_t) :=
  ((letb input_bytes_1468 : seq uint32 :=
        array_to_le_uint32s (lift_to_both0 input_block_1467) in
      letb s_1469 : state_t :=
        array_upd s_1469 (lift_to_both0 (usize 0)) (is_pure ((array_index (
                s_1469) (lift_to_both0 (usize 0))) .^ (seq_index (
                input_bytes_1468) (lift_to_both0 (usize 0))))) in
      letb s_1469 : state_t :=
        array_upd s_1469 (lift_to_both0 (usize 1)) (is_pure ((array_index (
                s_1469) (lift_to_both0 (usize 1))) .^ (seq_index (
                input_bytes_1468) (lift_to_both0 (usize 1))))) in
      letb s_1469 : state_t :=
        array_upd s_1469 (lift_to_both0 (usize 2)) (is_pure ((array_index (
                s_1469) (lift_to_both0 (usize 2))) .^ (seq_index (
                input_bytes_1468) (lift_to_both0 (usize 2))))) in
      letb s_1469 : state_t :=
        array_upd s_1469 (lift_to_both0 (usize 3)) (is_pure ((array_index (
                s_1469) (lift_to_both0 (usize 3))) .^ (seq_index (
                input_bytes_1468) (lift_to_both0 (usize 3))))) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (gimli (
          lift_to_both0 s_1469))
      ) : both (fset.fset0) [interface] (state_t)).
Fail Next Obligation.

Definition block_1471_loc : ChoiceEqualityLocation :=
  (block_t ; 1472%nat).
Notation "'squeeze_block_inp'" :=(
  state_t : choice_type) (in custom pack_type at level 2).
Notation "'squeeze_block_inp'" :=(state_t : ChoiceEquality) (at level 2).
Notation "'squeeze_block_out'" :=(
  block_t : choice_type) (in custom pack_type at level 2).
Notation "'squeeze_block_out'" :=(block_t : ChoiceEquality) (at level 2).
Definition SQUEEZE_BLOCK : nat :=
  1477.
Program Definition squeeze_block (s_1474 : state_t)
  : both (CEfset ([block_1471_loc])) [interface] (block_t) :=
  ((letbm block_1471 : block_t loc( block_1471_loc ) :=
        array_new_ (default : uint8) (16) in
      letb block_1471 :=
        foldi_both' (lift_to_both0 (usize 0)) (lift_to_both0 (
              usize 4)) block_1471 (L := (CEfset ([block_1471_loc]))) (
            I := [interface]) (fun i_1473 block_1471 =>
            letb s_i_1475 : uint32 :=
              array_index (s_1474) (lift_to_both0 i_1473) in
            letb s_i_bytes_1476 : seq uint8 :=
              uint32_to_le_bytes (lift_to_both0 s_i_1475) in
            letb block_1471 : block_t :=
              array_upd block_1471 ((lift_to_both0 (usize 4)) .* (
                  lift_to_both0 i_1473)) (is_pure (seq_index (s_i_bytes_1476) (
                    lift_to_both0 (usize 0)))) in
            letb block_1471 : block_t :=
              array_upd block_1471 (((lift_to_both0 (usize 4)) .* (
                    lift_to_both0 i_1473)) .+ (lift_to_both0 (usize 1))) (
                is_pure (seq_index (s_i_bytes_1476) (lift_to_both0 (
                      usize 1)))) in
            letb block_1471 : block_t :=
              array_upd block_1471 (((lift_to_both0 (usize 4)) .* (
                    lift_to_both0 i_1473)) .+ (lift_to_both0 (usize 2))) (
                is_pure (seq_index (s_i_bytes_1476) (lift_to_both0 (
                      usize 2)))) in
            letb block_1471 : block_t :=
              array_upd block_1471 (((lift_to_both0 (usize 4)) .* (
                    lift_to_both0 i_1473)) .+ (lift_to_both0 (usize 3))) (
                is_pure (seq_index (s_i_bytes_1476) (lift_to_both0 (
                      usize 3)))) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 block_1471)
            ) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        lift_to_both0 block_1471)
      ) : both (CEfset ([block_1471_loc])) [interface] (block_t)).
Fail Next Obligation.

Definition input_block_padded_1478_loc : ChoiceEqualityLocation :=
  (block_t ; 1479%nat).
Notation "'gimli_hash_state_inp'" :=(
  byte_seq '× state_t : choice_type) (in custom pack_type at level 2).
Notation "'gimli_hash_state_inp'" :=(
  byte_seq '× state_t : ChoiceEquality) (at level 2).
Notation "'gimli_hash_state_out'" :=(
  state_t : choice_type) (in custom pack_type at level 2).
Notation "'gimli_hash_state_out'" :=(state_t : ChoiceEquality) (at level 2).
Definition GIMLI_HASH_STATE : nat :=
  1489.
Program Definition gimli_hash_state (input_1481 : byte_seq) (s_1483 : state_t)
  : both (CEfset ([input_block_padded_1478_loc])) [interface] (state_t) :=
  ((letb rate_1480 : uint_size := array_length  in
      letb chunks_1482 : uint_size :=
        seq_num_exact_chunks (lift_to_both0 input_1481) (
          lift_to_both0 rate_1480) in
      letb s_1483 :=
        foldi_both' (lift_to_both0 (usize 0)) (
            lift_to_both0 chunks_1482) s_1483 (L := (CEfset (
                [input_block_padded_1478_loc]))) (I := [interface]) (
            fun i_1484 s_1483 =>
            letb input_block_1485 : seq uint8 :=
              seq_get_exact_chunk (lift_to_both0 input_1481) (
                lift_to_both0 rate_1480) (lift_to_both0 i_1484) in
            letb full_block_1486 : block_t :=
              array_from_seq (16) (lift_to_both0 input_block_1485) in
            letbm s_1483 loc( s_1483_loc ) :=
              absorb_block (lift_to_both0 full_block_1486) (
                lift_to_both0 s_1483) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 s_1483)
            ) in
      letb input_block_1487 : seq uint8 :=
        seq_get_remainder_chunk (lift_to_both0 input_1481) (
          lift_to_both0 rate_1480) in
      letb input_block_padded_1488 : block_t :=
        array_new_ (default : uint8) (16) in
      letbm input_block_padded_1478 : block_t loc( input_block_padded_1478_loc ) :=
        array_update_start (lift_to_both0 input_block_padded_1488) (
          lift_to_both0 input_block_1487) in
      letb input_block_padded_1478 : block_t :=
        array_upd input_block_padded_1478 (seq_len (
            lift_to_both0 input_block_1487)) (is_pure (secret (lift_to_both0 (
                @repr U8 1)))) in
      letb s_1483 : state_t :=
        array_upd s_1483 (lift_to_both0 (usize 11)) (is_pure ((array_index (
                s_1483) (lift_to_both0 (usize 11))) .^ (secret (lift_to_both0 (
                  @repr U32 16777216))))) in
      letbm s_1483 loc( s_1483_loc ) :=
        absorb_block (lift_to_both0 input_block_padded_1478) (
          lift_to_both0 s_1483) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 s_1483)
      ) : both (CEfset ([input_block_padded_1478_loc])) [interface] (state_t)).
Fail Next Obligation.


Notation "'gimli_hash_inp'" :=(
  byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'gimli_hash_inp'" :=(byte_seq : ChoiceEquality) (at level 2).
Notation "'gimli_hash_out'" :=(
  digest_t : choice_type) (in custom pack_type at level 2).
Notation "'gimli_hash_out'" :=(digest_t : ChoiceEquality) (at level 2).
Definition GIMLI_HASH : nat :=
  1496.
Program Definition gimli_hash (input_bytes_1491 : byte_seq)
  : both (CEfset ([block_1471_loc ; input_block_padded_1478_loc])) [interface] (
    digest_t) :=
  ((letb s_1490 : state_t := array_new_ (default : uint32) (12) in
      letb s_1492 : state_t :=
        gimli_hash_state (lift_to_both0 input_bytes_1491) (
          lift_to_both0 s_1490) in
      letb output_1493 : digest_t := array_new_ (default : uint8) (32) in
      letb output_1494 : digest_t :=
        array_update_start (lift_to_both0 output_1493) (
          array_to_seq (squeeze_block (lift_to_both0 s_1492))) in
      letb s_1495 : state_t := gimli (lift_to_both0 s_1492) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (array_update (
          lift_to_both0 output_1494) (array_length ) (
          array_to_seq (squeeze_block (lift_to_both0 s_1495))))
      ) : both (CEfset (
        [block_1471_loc ; input_block_padded_1478_loc])) [interface] (
      digest_t)).
Fail Next Obligation.

Definition nonce_t := nseq (uint8) (usize 16).

Definition key_t := nseq (uint8) (usize 32).

Definition tag_t := nseq (uint8) (usize 16).


Notation "'process_ad_inp'" :=(
  byte_seq '× state_t : choice_type) (in custom pack_type at level 2).
Notation "'process_ad_inp'" :=(
  byte_seq '× state_t : ChoiceEquality) (at level 2).
Notation "'process_ad_out'" :=(
  state_t : choice_type) (in custom pack_type at level 2).
Notation "'process_ad_out'" :=(state_t : ChoiceEquality) (at level 2).
Definition PROCESS_AD : nat :=
  1499.
Program Definition process_ad (ad_1497 : byte_seq) (s_1498 : state_t)
  : both (CEfset ([input_block_padded_1478_loc])) [interface] (state_t) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (gimli_hash_state (
          lift_to_both0 ad_1497) (lift_to_both0 s_1498))
      ) : both (CEfset ([input_block_padded_1478_loc])) [interface] (state_t)).
Fail Next Obligation.

Definition ciphertext_1500_loc : ChoiceEqualityLocation :=
  (seq uint8 ; 1502%nat).
Definition msg_block_padded_1501_loc : ChoiceEqualityLocation :=
  (block_t ; 1503%nat).
Notation "'process_msg_inp'" :=(
  byte_seq '× state_t : choice_type) (in custom pack_type at level 2).
Notation "'process_msg_inp'" :=(
  byte_seq '× state_t : ChoiceEquality) (at level 2).
Notation "'process_msg_out'" :=((state_t '× byte_seq
  ) : choice_type) (in custom pack_type at level 2).
Notation "'process_msg_out'" :=((state_t '× byte_seq
  ) : ChoiceEquality) (at level 2).
Definition PROCESS_MSG : nat :=
  1516.
Program Definition process_msg (message_1504 : byte_seq) (s_1507 : state_t)
  : both (CEfset (
      [block_1471_loc ; ciphertext_1500_loc ; msg_block_padded_1501_loc])) [interface] (
    (state_t '× byte_seq)) :=
  ((letbm ciphertext_1500 : seq uint8 loc( ciphertext_1500_loc ) :=
        seq_new_ (default : uint8) (seq_len (lift_to_both0 message_1504)) in
      letb rate_1505 : uint_size := array_length  in
      letb num_chunks_1506 : uint_size :=
        seq_num_exact_chunks (lift_to_both0 message_1504) (
          lift_to_both0 rate_1505) in
      letb '(s_1507, ciphertext_1500) :=
        foldi_both' (lift_to_both0 (usize 0)) (
            lift_to_both0 num_chunks_1506) prod_ce(s_1507, ciphertext_1500) (
            L := (CEfset (
                [block_1471_loc ; ciphertext_1500_loc ; msg_block_padded_1501_loc]))) (
            I := [interface]) (fun i_1508 '(s_1507, ciphertext_1500) =>
            letb key_block_1509 : block_t :=
              squeeze_block (lift_to_both0 s_1507) in
            letb msg_block_1510 : seq uint8 :=
              seq_get_exact_chunk (lift_to_both0 message_1504) (
                lift_to_both0 rate_1505) (lift_to_both0 i_1508) in
            letb msg_block_1511 : block_t :=
              array_from_seq (16) (lift_to_both0 msg_block_1510) in
            letbm ciphertext_1500 loc( ciphertext_1500_loc ) :=
              seq_set_exact_chunk (lift_to_both0 ciphertext_1500) (
                lift_to_both0 rate_1505) (lift_to_both0 i_1508) (array_to_seq ((
                  lift_to_both0 msg_block_1511) array_xor (
                  lift_to_both0 key_block_1509))) in
            letbm s_1507 loc( s_1507_loc ) :=
              absorb_block (lift_to_both0 msg_block_1511) (
                lift_to_both0 s_1507) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                lift_to_both0 s_1507,
                lift_to_both0 ciphertext_1500
              ))
            ) in
      letb key_block_1512 : block_t := squeeze_block (lift_to_both0 s_1507) in
      letb last_block_1513 : seq uint8 :=
        seq_get_remainder_chunk (lift_to_both0 message_1504) (
          lift_to_both0 rate_1505) in
      letb block_len_1514 : uint_size :=
        seq_len (lift_to_both0 last_block_1513) in
      letb msg_block_padded_1515 : block_t :=
        array_new_ (default : uint8) (16) in
      letbm msg_block_padded_1501 : block_t loc( msg_block_padded_1501_loc ) :=
        array_update_start (lift_to_both0 msg_block_padded_1515) (
          lift_to_both0 last_block_1513) in
      letbm ciphertext_1500 loc( ciphertext_1500_loc ) :=
        seq_set_chunk (lift_to_both0 ciphertext_1500) (
          lift_to_both0 rate_1505) (lift_to_both0 num_chunks_1506) (
          array_slice_range ((lift_to_both0 msg_block_padded_1501) array_xor (
              lift_to_both0 key_block_1512)) (prod_b(
              lift_to_both0 (usize 0),
              lift_to_both0 block_len_1514
            ))) in
      letb msg_block_padded_1501 : block_t :=
        array_upd msg_block_padded_1501 (lift_to_both0 block_len_1514) (
          is_pure ((array_index (msg_block_padded_1501) (
                lift_to_both0 block_len_1514)) .^ (secret (lift_to_both0 (
                  @repr U8 1))))) in
      letb s_1507 : state_t :=
        array_upd s_1507 (lift_to_both0 (usize 11)) (is_pure ((array_index (
                s_1507) (lift_to_both0 (usize 11))) .^ (secret (lift_to_both0 (
                  @repr U32 16777216))))) in
      letbm s_1507 loc( s_1507_loc ) :=
        absorb_block (lift_to_both0 msg_block_padded_1501) (
          lift_to_both0 s_1507) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 s_1507,
          lift_to_both0 ciphertext_1500
        ))
      ) : both (CEfset (
        [block_1471_loc ; ciphertext_1500_loc ; msg_block_padded_1501_loc])) [interface] (
      (state_t '× byte_seq))).
Fail Next Obligation.

Definition msg_block_1518_loc : ChoiceEqualityLocation :=
  (block_t ; 1519%nat).
Definition message_1517_loc : ChoiceEqualityLocation :=
  (seq uint8 ; 1520%nat).
Notation "'process_ct_inp'" :=(
  byte_seq '× state_t : choice_type) (in custom pack_type at level 2).
Notation "'process_ct_inp'" :=(
  byte_seq '× state_t : ChoiceEquality) (at level 2).
Notation "'process_ct_out'" :=((state_t '× byte_seq
  ) : choice_type) (in custom pack_type at level 2).
Notation "'process_ct_out'" :=((state_t '× byte_seq
  ) : ChoiceEquality) (at level 2).
Definition PROCESS_CT : nat :=
  1536.
Program Definition process_ct (ciphertext_1521 : byte_seq) (s_1524 : state_t)
  : both (CEfset (
      [block_1471_loc ; message_1517_loc ; msg_block_1518_loc])) [interface] ((
      state_t '×
      byte_seq
    )) :=
  ((letbm message_1517 : seq uint8 loc( message_1517_loc ) :=
        seq_new_ (default : uint8) (seq_len (lift_to_both0 ciphertext_1521)) in
      letb rate_1522 : uint_size := array_length  in
      letb num_chunks_1523 : uint_size :=
        seq_num_exact_chunks (lift_to_both0 ciphertext_1521) (
          lift_to_both0 rate_1522) in
      letb '(s_1524, message_1517) :=
        foldi_both' (lift_to_both0 (usize 0)) (
            lift_to_both0 num_chunks_1523) prod_ce(s_1524, message_1517) (L := (
              CEfset (
                [block_1471_loc ; message_1517_loc ; msg_block_1518_loc]))) (
            I := [interface]) (fun i_1525 '(s_1524, message_1517) =>
            letb key_block_1526 : block_t :=
              squeeze_block (lift_to_both0 s_1524) in
            letb ct_block_1527 : seq uint8 :=
              seq_get_exact_chunk (lift_to_both0 ciphertext_1521) (
                lift_to_both0 rate_1522) (lift_to_both0 i_1525) in
            letb ct_block_1528 : block_t :=
              array_from_seq (16) (lift_to_both0 ct_block_1527) in
            letb msg_block_1529 : block_t :=
              (lift_to_both0 ct_block_1528) array_xor (
                lift_to_both0 key_block_1526) in
            letbm message_1517 loc( message_1517_loc ) :=
              seq_set_exact_chunk (lift_to_both0 message_1517) (
                lift_to_both0 rate_1522) (lift_to_both0 i_1525) (array_to_seq ((
                  lift_to_both0 ct_block_1528) array_xor (
                  lift_to_both0 key_block_1526))) in
            letbm s_1524 loc( s_1524_loc ) :=
              absorb_block (lift_to_both0 msg_block_1529) (
                lift_to_both0 s_1524) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                lift_to_both0 s_1524,
                lift_to_both0 message_1517
              ))
            ) in
      letb key_block_1530 : block_t := squeeze_block (lift_to_both0 s_1524) in
      letb ct_final_1531 : seq uint8 :=
        seq_get_remainder_chunk (lift_to_both0 ciphertext_1521) (
          lift_to_both0 rate_1522) in
      letb block_len_1532 : uint_size :=
        seq_len (lift_to_both0 ct_final_1531) in
      letb ct_block_padded_1533 : block_t :=
        array_new_ (default : uint8) (16) in
      letb ct_block_padded_1534 : block_t :=
        array_update_start (lift_to_both0 ct_block_padded_1533) (
          lift_to_both0 ct_final_1531) in
      letb msg_block_1535 : block_t :=
        (lift_to_both0 ct_block_padded_1534) array_xor (
          lift_to_both0 key_block_1530) in
      letbm message_1517 loc( message_1517_loc ) :=
        seq_set_chunk (lift_to_both0 message_1517) (lift_to_both0 rate_1522) (
          lift_to_both0 num_chunks_1523) (array_slice_range (
            lift_to_both0 msg_block_1535) (prod_b(
              lift_to_both0 (usize 0),
              lift_to_both0 block_len_1532
            ))) in
      letbm msg_block_1518 : block_t loc( msg_block_1518_loc ) :=
        array_from_slice_range (default : uint8) (16) (
          array_to_seq (lift_to_both0 msg_block_1535)) (prod_b(
            lift_to_both0 (usize 0),
            lift_to_both0 block_len_1532
          )) in
      letb msg_block_1518 : block_t :=
        array_upd msg_block_1518 (lift_to_both0 block_len_1532) (is_pure ((
              array_index (msg_block_1518) (lift_to_both0 block_len_1532)) .^ (
              secret (lift_to_both0 (@repr U8 1))))) in
      letb s_1524 : state_t :=
        array_upd s_1524 (lift_to_both0 (usize 11)) (is_pure ((array_index (
                s_1524) (lift_to_both0 (usize 11))) .^ (secret (lift_to_both0 (
                  @repr U32 16777216))))) in
      letbm s_1524 loc( s_1524_loc ) :=
        absorb_block (lift_to_both0 msg_block_1518) (lift_to_both0 s_1524) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 s_1524,
          lift_to_both0 message_1517
        ))
      ) : both (CEfset (
        [block_1471_loc ; message_1517_loc ; msg_block_1518_loc])) [interface] (
      (state_t '× byte_seq))).
Fail Next Obligation.

Definition uints_1537_loc : ChoiceEqualityLocation :=
  (seq uint32 ; 1538%nat).
Notation "'nonce_to_u32s_inp'" :=(
  nonce_t : choice_type) (in custom pack_type at level 2).
Notation "'nonce_to_u32s_inp'" :=(nonce_t : ChoiceEquality) (at level 2).
Notation "'nonce_to_u32s_out'" :=(
  seq uint32 : choice_type) (in custom pack_type at level 2).
Notation "'nonce_to_u32s_out'" :=(seq uint32 : ChoiceEquality) (at level 2).
Definition NONCE_TO_U32S : nat :=
  1540.
Program Definition nonce_to_u32s (nonce_1539 : nonce_t)
  : both (CEfset ([uints_1537_loc])) [interface] (seq uint32) :=
  ((letbm uints_1537 : seq uint32 loc( uints_1537_loc ) :=
        seq_new_ (default : uint32) (lift_to_both0 (usize 4)) in
      letb uints_1537 : seq uint32 :=
        seq_upd uints_1537 (lift_to_both0 (usize 0)) (is_pure (
            uint32_from_le_bytes (array_from_slice_range (default : uint8) (4) (
                array_to_seq (lift_to_both0 nonce_1539)) (prod_b(
                  lift_to_both0 (usize 0),
                  lift_to_both0 (usize 4)
                ))))) in
      letb uints_1537 : seq uint32 :=
        seq_upd uints_1537 (lift_to_both0 (usize 1)) (is_pure (
            uint32_from_le_bytes (array_from_slice_range (default : uint8) (4) (
                array_to_seq (lift_to_both0 nonce_1539)) (prod_b(
                  lift_to_both0 (usize 4),
                  lift_to_both0 (usize 8)
                ))))) in
      letb uints_1537 : seq uint32 :=
        seq_upd uints_1537 (lift_to_both0 (usize 2)) (is_pure (
            uint32_from_le_bytes (array_from_slice_range (default : uint8) (4) (
                array_to_seq (lift_to_both0 nonce_1539)) (prod_b(
                  lift_to_both0 (usize 8),
                  lift_to_both0 (usize 12)
                ))))) in
      letb uints_1537 : seq uint32 :=
        seq_upd uints_1537 (lift_to_both0 (usize 3)) (is_pure (
            uint32_from_le_bytes (array_from_slice_range (default : uint8) (4) (
                array_to_seq (lift_to_both0 nonce_1539)) (prod_b(
                  lift_to_both0 (usize 12),
                  lift_to_both0 (usize 16)
                ))))) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        lift_to_both0 uints_1537)
      ) : both (CEfset ([uints_1537_loc])) [interface] (seq uint32)).
Fail Next Obligation.

Definition uints_1541_loc : ChoiceEqualityLocation :=
  (seq uint32 ; 1542%nat).
Notation "'key_to_u32s_inp'" :=(
  key_t : choice_type) (in custom pack_type at level 2).
Notation "'key_to_u32s_inp'" :=(key_t : ChoiceEquality) (at level 2).
Notation "'key_to_u32s_out'" :=(
  seq uint32 : choice_type) (in custom pack_type at level 2).
Notation "'key_to_u32s_out'" :=(seq uint32 : ChoiceEquality) (at level 2).
Definition KEY_TO_U32S : nat :=
  1544.
Program Definition key_to_u32s (key_1543 : key_t)
  : both (CEfset ([uints_1541_loc])) [interface] (seq uint32) :=
  ((letbm uints_1541 : seq uint32 loc( uints_1541_loc ) :=
        seq_new_ (default : uint32) (lift_to_both0 (usize 8)) in
      letb uints_1541 : seq uint32 :=
        seq_upd uints_1541 (lift_to_both0 (usize 0)) (is_pure (
            uint32_from_le_bytes (array_from_slice_range (default : uint8) (4) (
                array_to_seq (lift_to_both0 key_1543)) (prod_b(
                  lift_to_both0 (usize 0),
                  lift_to_both0 (usize 4)
                ))))) in
      letb uints_1541 : seq uint32 :=
        seq_upd uints_1541 (lift_to_both0 (usize 1)) (is_pure (
            uint32_from_le_bytes (array_from_slice_range (default : uint8) (4) (
                array_to_seq (lift_to_both0 key_1543)) (prod_b(
                  lift_to_both0 (usize 4),
                  lift_to_both0 (usize 8)
                ))))) in
      letb uints_1541 : seq uint32 :=
        seq_upd uints_1541 (lift_to_both0 (usize 2)) (is_pure (
            uint32_from_le_bytes (array_from_slice_range (default : uint8) (4) (
                array_to_seq (lift_to_both0 key_1543)) (prod_b(
                  lift_to_both0 (usize 8),
                  lift_to_both0 (usize 12)
                ))))) in
      letb uints_1541 : seq uint32 :=
        seq_upd uints_1541 (lift_to_both0 (usize 3)) (is_pure (
            uint32_from_le_bytes (array_from_slice_range (default : uint8) (4) (
                array_to_seq (lift_to_both0 key_1543)) (prod_b(
                  lift_to_both0 (usize 12),
                  lift_to_both0 (usize 16)
                ))))) in
      letb uints_1541 : seq uint32 :=
        seq_upd uints_1541 (lift_to_both0 (usize 4)) (is_pure (
            uint32_from_le_bytes (array_from_slice_range (default : uint8) (4) (
                array_to_seq (lift_to_both0 key_1543)) (prod_b(
                  lift_to_both0 (usize 16),
                  lift_to_both0 (usize 20)
                ))))) in
      letb uints_1541 : seq uint32 :=
        seq_upd uints_1541 (lift_to_both0 (usize 5)) (is_pure (
            uint32_from_le_bytes (array_from_slice_range (default : uint8) (4) (
                array_to_seq (lift_to_both0 key_1543)) (prod_b(
                  lift_to_both0 (usize 20),
                  lift_to_both0 (usize 24)
                ))))) in
      letb uints_1541 : seq uint32 :=
        seq_upd uints_1541 (lift_to_both0 (usize 6)) (is_pure (
            uint32_from_le_bytes (array_from_slice_range (default : uint8) (4) (
                array_to_seq (lift_to_both0 key_1543)) (prod_b(
                  lift_to_both0 (usize 24),
                  lift_to_both0 (usize 28)
                ))))) in
      letb uints_1541 : seq uint32 :=
        seq_upd uints_1541 (lift_to_both0 (usize 7)) (is_pure (
            uint32_from_le_bytes (array_from_slice_range (default : uint8) (4) (
                array_to_seq (lift_to_both0 key_1543)) (prod_b(
                  lift_to_both0 (usize 28),
                  lift_to_both0 (usize 32)
                ))))) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        lift_to_both0 uints_1541)
      ) : both (CEfset ([uints_1541_loc])) [interface] (seq uint32)).
Fail Next Obligation.


Notation "'gimli_aead_encrypt_inp'" :=(
  byte_seq '× byte_seq '× nonce_t '× key_t : choice_type) (in custom pack_type at level 2).
Notation "'gimli_aead_encrypt_inp'" :=(
  byte_seq '× byte_seq '× nonce_t '× key_t : ChoiceEquality) (at level 2).
Notation "'gimli_aead_encrypt_out'" :=((byte_seq '× tag_t
  ) : choice_type) (in custom pack_type at level 2).
Notation "'gimli_aead_encrypt_out'" :=((byte_seq '× tag_t
  ) : ChoiceEquality) (at level 2).
Definition GIMLI_AEAD_ENCRYPT : nat :=
  1556.
Program Definition gimli_aead_encrypt (message_1551 : byte_seq) (
    ad_1549 : byte_seq) (nonce_1545 : nonce_t) (key_1546 : key_t)
  : both (CEfset (
      [block_1471_loc ; input_block_padded_1478_loc ; ciphertext_1500_loc ; msg_block_padded_1501_loc ; uints_1537_loc ; uints_1541_loc])) [interface] (
    (byte_seq '× tag_t)) :=
  ((letb s_1547 : state_t :=
        array_from_seq (12) (seq_concat (nonce_to_u32s (
              lift_to_both0 nonce_1545)) (key_to_u32s (
              lift_to_both0 key_1546))) in
      letb s_1548 : state_t := gimli (lift_to_both0 s_1547) in
      letb s_1550 : state_t :=
        process_ad (lift_to_both0 ad_1549) (lift_to_both0 s_1548) in
      letb '(s_1552, ciphertext_1553) : (state_t '× byte_seq) :=
        process_msg (lift_to_both0 message_1551) (lift_to_both0 s_1550) in
      letb tag_1554 : block_t := squeeze_block (lift_to_both0 s_1552) in
      letb tag_1555 : tag_t :=
        array_from_seq (16) (array_to_seq (lift_to_both0 tag_1554)) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 ciphertext_1553,
          lift_to_both0 tag_1555
        ))
      ) : both (CEfset (
        [block_1471_loc ; input_block_padded_1478_loc ; ciphertext_1500_loc ; msg_block_padded_1501_loc ; uints_1537_loc ; uints_1541_loc])) [interface] (
      (byte_seq '× tag_t))).
Fail Next Obligation.

Definition out_1557_loc : ChoiceEqualityLocation :=
  (seq uint8 ; 1558%nat).
Notation "'gimli_aead_decrypt_inp'" :=(
  byte_seq '× byte_seq '× tag_t '× nonce_t '× key_t : choice_type) (in custom pack_type at level 2).
Notation "'gimli_aead_decrypt_inp'" :=(
  byte_seq '× byte_seq '× tag_t '× nonce_t '× key_t : ChoiceEquality) (at level 2).
Notation "'gimli_aead_decrypt_out'" :=(
  byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'gimli_aead_decrypt_out'" :=(byte_seq : ChoiceEquality) (at level 2).
Definition GIMLI_AEAD_DECRYPT : nat :=
  1571.
Program Definition gimli_aead_decrypt (ciphertext_1565 : byte_seq) (
    ad_1563 : byte_seq) (tag_1570 : tag_t) (nonce_1559 : nonce_t) (
    key_1560 : key_t)
  : both (CEfset (
      [block_1471_loc ; input_block_padded_1478_loc ; message_1517_loc ; msg_block_1518_loc ; uints_1537_loc ; uints_1541_loc ; out_1557_loc])) [interface] (
    byte_seq) :=
  ((letb s_1561 : state_t :=
        array_from_seq (12) (seq_concat (nonce_to_u32s (
              lift_to_both0 nonce_1559)) (key_to_u32s (
              lift_to_both0 key_1560))) in
      letb s_1562 : state_t := gimli (lift_to_both0 s_1561) in
      letb s_1564 : state_t :=
        process_ad (lift_to_both0 ad_1563) (lift_to_both0 s_1562) in
      letb '(s_1566, message_1567) : (state_t '× byte_seq) :=
        process_ct (lift_to_both0 ciphertext_1565) (lift_to_both0 s_1564) in
      letb my_tag_1568 : block_t := squeeze_block (lift_to_both0 s_1566) in
      letb my_tag_1569 : tag_t :=
        array_from_seq (16) (array_to_seq (lift_to_both0 my_tag_1568)) in
      letbm out_1557 : seq uint8 loc( out_1557_loc ) :=
        seq_new_ (default : uint8) (lift_to_both0 (usize 0)) in
      letb '(out_1557) :=
        if array_equal (lift_to_both0 my_tag_1569) (
          lift_to_both0 tag_1570) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset (
            [block_1471_loc ; input_block_padded_1478_loc ; message_1517_loc ; msg_block_1518_loc ; uints_1537_loc ; uints_1541_loc ; out_1557_loc])) (
          L2 := CEfset (
            [block_1471_loc ; input_block_padded_1478_loc ; message_1517_loc ; msg_block_1518_loc ; uints_1537_loc ; uints_1541_loc ; out_1557_loc])) (
          I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
          letbm out_1557 loc( out_1557_loc ) := lift_to_both0 message_1567 in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 out_1557)
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          lift_to_both0 out_1557)
         in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 out_1557)
      ) : both (CEfset (
        [block_1471_loc ; input_block_padded_1478_loc ; message_1517_loc ; msg_block_1518_loc ; uints_1537_loc ; uints_1541_loc ; out_1557_loc])) [interface] (
      byte_seq)).
Fail Next Obligation.

