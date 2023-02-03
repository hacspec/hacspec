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


Definition schedule_t := nseq (uint32) (usize 80).

Definition block_words_v : uint_size :=
  ((usize 512) ./ (usize 32)).

Definition hash_words_v : uint_size :=
  ((usize 160) ./ (usize 32)).

Definition block_t := nseq (uint32) (block_words_v).

Definition hash_t := nseq (uint32) (hash_words_v).

Definition block_bytes_v : uint_size :=
  ((usize 512) ./ (usize 8)).

Definition hash_bytes_v : uint_size :=
  ((usize 160) ./ (usize 8)).

Definition block_bytes_t := nseq (uint8) (block_bytes_v).

Definition sha1_digest_t := nseq (uint8) (hash_bytes_v).

Definition bitlength_bytes_v : uint_size :=
  ((usize 64) ./ (usize 8)).


Notation "'ch_inp'" :=(
  uint32 '× uint32 '× uint32 : choice_type) (in custom pack_type at level 2).
Notation "'ch_inp'" :=(
  uint32 '× uint32 '× uint32 : ChoiceEquality) (at level 2).
Notation "'ch_out'" :=(uint32 : choice_type) (in custom pack_type at level 2).
Notation "'ch_out'" :=(uint32 : ChoiceEquality) (at level 2).
Definition CH : nat :=
  1575.
Program Definition ch (x_1572 : uint32) (y_1573 : uint32) (z_1574 : uint32)
  : both (fset.fset0) [interface] (uint32) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (((
            lift_to_both0 x_1572) .& (lift_to_both0 y_1573)) .^ ((not (
              lift_to_both0 x_1572)) .& (lift_to_both0 z_1574)))
      ) : both (fset.fset0) [interface] (uint32)).
Fail Next Obligation.


Notation "'parity_inp'" :=(
  uint32 '× uint32 '× uint32 : choice_type) (in custom pack_type at level 2).
Notation "'parity_inp'" :=(
  uint32 '× uint32 '× uint32 : ChoiceEquality) (at level 2).
Notation "'parity_out'" :=(
  uint32 : choice_type) (in custom pack_type at level 2).
Notation "'parity_out'" :=(uint32 : ChoiceEquality) (at level 2).
Definition PARITY : nat :=
  1579.
Program Definition parity (x_1576 : uint32) (y_1577 : uint32) (z_1578 : uint32)
  : both (fset.fset0) [interface] (uint32) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (((
            lift_to_both0 x_1576) .^ (lift_to_both0 y_1577)) .^ (
          lift_to_both0 z_1578))
      ) : both (fset.fset0) [interface] (uint32)).
Fail Next Obligation.


Notation "'maj_inp'" :=(
  uint32 '× uint32 '× uint32 : choice_type) (in custom pack_type at level 2).
Notation "'maj_inp'" :=(
  uint32 '× uint32 '× uint32 : ChoiceEquality) (at level 2).
Notation "'maj_out'" :=(uint32 : choice_type) (in custom pack_type at level 2).
Notation "'maj_out'" :=(uint32 : ChoiceEquality) (at level 2).
Definition MAJ : nat :=
  1583.
Program Definition maj (x_1580 : uint32) (y_1581 : uint32) (z_1582 : uint32)
  : both (fset.fset0) [interface] (uint32) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) ((((
              lift_to_both0 x_1580) .& (lift_to_both0 y_1581)) .^ ((
              lift_to_both0 x_1580) .& (lift_to_both0 z_1582))) .^ ((
            lift_to_both0 y_1581) .& (lift_to_both0 z_1582)))
      ) : both (fset.fset0) [interface] (uint32)).
Fail Next Obligation.

Definition hash_init_v : hash_t :=
  @array_from_list uint32 [
    (secret (@repr U32 1732584193)) : uint32;
    (secret (@repr U32 4023233417)) : uint32;
    (secret (@repr U32 2562383102)) : uint32;
    (secret (@repr U32 271733878)) : uint32;
    (secret (@repr U32 3285377520)) : uint32
  ].

Definition t_1590_loc : ChoiceEqualityLocation :=
  (uint32 ; 1591%nat).
Definition w_1584_loc : ChoiceEqualityLocation :=
  (schedule_t ; 1592%nat).
Definition a_1585_loc : ChoiceEqualityLocation :=
  (uint32 ; 1593%nat).
Definition d_1588_loc : ChoiceEqualityLocation :=
  (uint32 ; 1594%nat).
Definition e_1589_loc : ChoiceEqualityLocation :=
  (uint32 ; 1595%nat).
Definition c_1587_loc : ChoiceEqualityLocation :=
  (uint32 ; 1596%nat).
Definition b_1586_loc : ChoiceEqualityLocation :=
  (uint32 ; 1597%nat).
Notation "'compress_inp'" :=(
  block_bytes_t '× hash_t : choice_type) (in custom pack_type at level 2).
Notation "'compress_inp'" :=(
  block_bytes_t '× hash_t : ChoiceEquality) (at level 2).
Notation "'compress_out'" :=(
  hash_t : choice_type) (in custom pack_type at level 2).
Notation "'compress_out'" :=(hash_t : ChoiceEquality) (at level 2).
Definition COMPRESS : nat :=
  1603.
Program Definition compress (m_bytes_1598 : block_bytes_t) (h_1601 : hash_t)
  : both (CEfset (
      [w_1584_loc ; a_1585_loc ; b_1586_loc ; c_1587_loc ; d_1588_loc ; e_1589_loc ; t_1590_loc])) [interface] (
    hash_t) :=
  ((letb m_1599 : seq uint32 :=
        array_to_be_uint32s (lift_to_both0 m_bytes_1598) in
      letbm w_1584 : schedule_t loc( w_1584_loc ) :=
        array_new_ (default : uint32) (80) in
      letb w_1584 :=
        foldi_both' (lift_to_both0 (usize 0)) (lift_to_both0 (
              usize 80)) w_1584 (L := (CEfset (
                [w_1584_loc ; a_1585_loc ; b_1586_loc ; c_1587_loc ; d_1588_loc ; e_1589_loc ; t_1590_loc]))) (
            I := [interface]) (fun t_1600 w_1584 =>
            letb '(w_1584) :=
              if (lift_to_both0 t_1600) <.? (lift_to_both0 (
                  usize 16)) :bool_ChoiceEquality
              then lift_scope (L1 := CEfset ([w_1584_loc])) (L2 := CEfset (
                  [w_1584_loc])) (I1 := [interface]) (
                I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
                letb w_1584 : schedule_t :=
                  array_upd w_1584 (lift_to_both0 t_1600) (is_pure (seq_index (
                        m_1599) (lift_to_both0 t_1600))) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                  lift_to_both0 w_1584)
                )
              else  lift_scope (L1 := CEfset ([w_1584_loc])) (L2 := CEfset (
                  [w_1584_loc])) (I1 := [interface]) (
                I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
                letb w_1584 : schedule_t :=
                  array_upd w_1584 (lift_to_both0 t_1600) (is_pure (
                      uint32_rotate_left ((((array_index (w_1584) ((
                                  lift_to_both0 t_1600) .- (lift_to_both0 (
                                    usize 3)))) .^ (array_index (w_1584) ((
                                  lift_to_both0 t_1600) .- (lift_to_both0 (
                                    usize 8))))) .^ (array_index (w_1584) ((
                                lift_to_both0 t_1600) .- (lift_to_both0 (
                                  usize 14))))) .^ (array_index (w_1584) ((
                              lift_to_both0 t_1600) .- (lift_to_both0 (
                                usize 16))))) (lift_to_both0 (usize 1)))) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                  lift_to_both0 w_1584)
                ) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 w_1584)
            ) in
      letbm a_1585 : uint32 loc( a_1585_loc ) :=
        array_index (h_1601) (lift_to_both0 (usize 0)) in
      letbm b_1586 : uint32 loc( b_1586_loc ) :=
        array_index (h_1601) (lift_to_both0 (usize 1)) in
      letbm c_1587 : uint32 loc( c_1587_loc ) :=
        array_index (h_1601) (lift_to_both0 (usize 2)) in
      letbm d_1588 : uint32 loc( d_1588_loc ) :=
        array_index (h_1601) (lift_to_both0 (usize 3)) in
      letbm e_1589 : uint32 loc( e_1589_loc ) :=
        array_index (h_1601) (lift_to_both0 (usize 4)) in
      letb '(a_1585, b_1586, c_1587, d_1588, e_1589) :=
        foldi_both' (lift_to_both0 (usize 0)) (lift_to_both0 (
              usize 80)) prod_ce(a_1585, b_1586, c_1587, d_1588, e_1589) (L := (
              CEfset (
                [w_1584_loc ; a_1585_loc ; b_1586_loc ; c_1587_loc ; d_1588_loc ; e_1589_loc ; t_1590_loc]))) (
            I := [interface]) (fun t_1602 '(
              a_1585,
              b_1586,
              c_1587,
              d_1588,
              e_1589
            ) =>
            letbm t_1590 : uint32 loc( t_1590_loc ) := uint32_zero  in
            letb '(t_1590) :=
              if ((lift_to_both0 (usize 0)) <=.? (lift_to_both0 t_1602)) && ((
                  lift_to_both0 t_1602) <.? (lift_to_both0 (
                    usize 20))) :bool_ChoiceEquality
              then lift_scope (L1 := CEfset (
                  [w_1584_loc ; a_1585_loc ; b_1586_loc ; c_1587_loc ; d_1588_loc ; e_1589_loc ; t_1590_loc])) (
                L2 := CEfset (
                  [w_1584_loc ; a_1585_loc ; b_1586_loc ; c_1587_loc ; d_1588_loc ; e_1589_loc ; t_1590_loc])) (
                I1 := [interface]) (
                I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
                letbm t_1590 loc( t_1590_loc ) :=
                  ((((uint32_rotate_left (lift_to_both0 a_1585) (lift_to_both0 (
                              usize 5))) .+ (ch (lift_to_both0 b_1586) (
                            lift_to_both0 c_1587) (lift_to_both0 d_1588))) .+ (
                        lift_to_both0 e_1589)) .+ (secret (lift_to_both0 (
                          @repr U32 1518500249)))) .+ (array_index (w_1584) (
                      lift_to_both0 t_1602)) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                  lift_to_both0 t_1590)
                )
              else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                lift_to_both0 t_1590)
               in
            letb '(t_1590) :=
              if ((lift_to_both0 (usize 20)) <=.? (lift_to_both0 t_1602)) && ((
                  lift_to_both0 t_1602) <.? (lift_to_both0 (
                    usize 40))) :bool_ChoiceEquality
              then lift_scope (L1 := CEfset (
                  [w_1584_loc ; a_1585_loc ; b_1586_loc ; c_1587_loc ; d_1588_loc ; e_1589_loc ; t_1590_loc])) (
                L2 := CEfset (
                  [w_1584_loc ; a_1585_loc ; b_1586_loc ; c_1587_loc ; d_1588_loc ; e_1589_loc ; t_1590_loc])) (
                I1 := [interface]) (
                I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
                letbm t_1590 loc( t_1590_loc ) :=
                  ((((uint32_rotate_left (lift_to_both0 a_1585) (lift_to_both0 (
                              usize 5))) .+ (parity (lift_to_both0 b_1586) (
                            lift_to_both0 c_1587) (lift_to_both0 d_1588))) .+ (
                        lift_to_both0 e_1589)) .+ (secret (lift_to_both0 (
                          @repr U32 1859775393)))) .+ (array_index (w_1584) (
                      lift_to_both0 t_1602)) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                  lift_to_both0 t_1590)
                )
              else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                lift_to_both0 t_1590)
               in
            letb '(t_1590) :=
              if ((lift_to_both0 (usize 40)) <=.? (lift_to_both0 t_1602)) && ((
                  lift_to_both0 t_1602) <.? (lift_to_both0 (
                    usize 60))) :bool_ChoiceEquality
              then lift_scope (L1 := CEfset (
                  [w_1584_loc ; a_1585_loc ; b_1586_loc ; c_1587_loc ; d_1588_loc ; e_1589_loc ; t_1590_loc])) (
                L2 := CEfset (
                  [w_1584_loc ; a_1585_loc ; b_1586_loc ; c_1587_loc ; d_1588_loc ; e_1589_loc ; t_1590_loc])) (
                I1 := [interface]) (
                I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
                letbm t_1590 loc( t_1590_loc ) :=
                  ((((uint32_rotate_left (lift_to_both0 a_1585) (lift_to_both0 (
                              usize 5))) .+ (maj (lift_to_both0 b_1586) (
                            lift_to_both0 c_1587) (lift_to_both0 d_1588))) .+ (
                        lift_to_both0 e_1589)) .+ (secret (lift_to_both0 (
                          @repr U32 2400959708)))) .+ (array_index (w_1584) (
                      lift_to_both0 t_1602)) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                  lift_to_both0 t_1590)
                )
              else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                lift_to_both0 t_1590)
               in
            letb '(t_1590) :=
              if ((lift_to_both0 (usize 60)) <=.? (lift_to_both0 t_1602)) && ((
                  lift_to_both0 t_1602) <.? (lift_to_both0 (
                    usize 80))) :bool_ChoiceEquality
              then lift_scope (L1 := CEfset (
                  [w_1584_loc ; a_1585_loc ; b_1586_loc ; c_1587_loc ; d_1588_loc ; e_1589_loc ; t_1590_loc])) (
                L2 := CEfset (
                  [w_1584_loc ; a_1585_loc ; b_1586_loc ; c_1587_loc ; d_1588_loc ; e_1589_loc ; t_1590_loc])) (
                I1 := [interface]) (
                I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
                letbm t_1590 loc( t_1590_loc ) :=
                  ((((uint32_rotate_left (lift_to_both0 a_1585) (lift_to_both0 (
                              usize 5))) .+ (parity (lift_to_both0 b_1586) (
                            lift_to_both0 c_1587) (lift_to_both0 d_1588))) .+ (
                        lift_to_both0 e_1589)) .+ (secret (lift_to_both0 (
                          @repr U32 3395469782)))) .+ (array_index (w_1584) (
                      lift_to_both0 t_1602)) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                  lift_to_both0 t_1590)
                )
              else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                lift_to_both0 t_1590)
               in
            letbm e_1589 loc( e_1589_loc ) := lift_to_both0 d_1588 in
            letbm d_1588 loc( d_1588_loc ) := lift_to_both0 c_1587 in
            letbm c_1587 loc( c_1587_loc ) :=
              uint32_rotate_left (lift_to_both0 b_1586) (lift_to_both0 (
                  usize 30)) in
            letbm b_1586 loc( b_1586_loc ) := lift_to_both0 a_1585 in
            letbm a_1585 loc( a_1585_loc ) := lift_to_both0 t_1590 in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                lift_to_both0 a_1585,
                lift_to_both0 b_1586,
                lift_to_both0 c_1587,
                lift_to_both0 d_1588,
                lift_to_both0 e_1589
              ))
            ) in
      letb h_1601 : hash_t :=
        array_upd h_1601 (lift_to_both0 (usize 0)) (is_pure ((
              lift_to_both0 a_1585) .+ (array_index (h_1601) (lift_to_both0 (
                  usize 0))))) in
      letb h_1601 : hash_t :=
        array_upd h_1601 (lift_to_both0 (usize 1)) (is_pure ((
              lift_to_both0 b_1586) .+ (array_index (h_1601) (lift_to_both0 (
                  usize 1))))) in
      letb h_1601 : hash_t :=
        array_upd h_1601 (lift_to_both0 (usize 2)) (is_pure ((
              lift_to_both0 c_1587) .+ (array_index (h_1601) (lift_to_both0 (
                  usize 2))))) in
      letb h_1601 : hash_t :=
        array_upd h_1601 (lift_to_both0 (usize 3)) (is_pure ((
              lift_to_both0 d_1588) .+ (array_index (h_1601) (lift_to_both0 (
                  usize 3))))) in
      letb h_1601 : hash_t :=
        array_upd h_1601 (lift_to_both0 (usize 4)) (is_pure ((
              lift_to_both0 e_1589) .+ (array_index (h_1601) (lift_to_both0 (
                  usize 4))))) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 h_1601)
      ) : both (CEfset (
        [w_1584_loc ; a_1585_loc ; b_1586_loc ; c_1587_loc ; d_1588_loc ; e_1589_loc ; t_1590_loc])) [interface] (
      hash_t)).
Fail Next Obligation.

Definition pad_block_1606_loc : ChoiceEqualityLocation :=
  (block_bytes_t ; 1607%nat).
Definition block_bytes_1605_loc : ChoiceEqualityLocation :=
  (block_bytes_t ; 1608%nat).
Definition h_1604_loc : ChoiceEqualityLocation :=
  (hash_t ; 1609%nat).
Notation "'hash_inp'" :=(
  byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'hash_inp'" :=(byte_seq : ChoiceEquality) (at level 2).
Notation "'hash_out'" :=(
  sha1_digest_t : choice_type) (in custom pack_type at level 2).
Notation "'hash_out'" :=(sha1_digest_t : ChoiceEquality) (at level 2).
Definition HASH : nat :=
  1616.
Program Definition hash (msg_1610 : byte_seq)
  : both (CEfset (
      [w_1584_loc ; a_1585_loc ; b_1586_loc ; c_1587_loc ; d_1588_loc ; e_1589_loc ; t_1590_loc ; h_1604_loc ; block_bytes_1605_loc ; pad_block_1606_loc])) [interface] (
    sha1_digest_t) :=
  ((letbm h_1604 : hash_t loc( h_1604_loc ) := lift_to_both0 hash_init_v in
      letb h_1604 :=
        foldi_both' (lift_to_both0 (usize 0)) (seq_num_exact_chunks (
              lift_to_both0 msg_1610) (lift_to_both0 block_bytes_v)) h_1604 (
            L := (CEfset (
                [w_1584_loc ; a_1585_loc ; b_1586_loc ; c_1587_loc ; d_1588_loc ; e_1589_loc ; t_1590_loc ; h_1604_loc ; block_bytes_1605_loc ; pad_block_1606_loc]))) (
            I := [interface]) (fun i_1611 h_1604 =>
            letb raw_bytes_1612 : seq uint8 :=
              seq_get_exact_chunk (lift_to_both0 msg_1610) (
                lift_to_both0 block_bytes_v) (lift_to_both0 i_1611) in
            letb block_bytes_1613 : block_bytes_t :=
              array_from_seq (block_bytes_v) (lift_to_both0 raw_bytes_1612) in
            letbm h_1604 loc( h_1604_loc ) :=
              compress (lift_to_both0 block_bytes_1613) (
                lift_to_both0 h_1604) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 h_1604)
            ) in
      letb raw_bytes_1614 : seq uint8 :=
        seq_get_remainder_chunk (lift_to_both0 msg_1610) (
          lift_to_both0 block_bytes_v) in
      letbm block_bytes_1605 : block_bytes_t loc( block_bytes_1605_loc ) :=
        array_update_start (array_new_ (default : uint8) (block_bytes_v)) (
          lift_to_both0 raw_bytes_1614) in
      letb block_bytes_1605 : block_bytes_t :=
        array_upd block_bytes_1605 (seq_len (lift_to_both0 raw_bytes_1614)) (
          is_pure (secret (lift_to_both0 (@repr U8 128)))) in
      letb message_bitlength_1615 : uint64 :=
        secret (pub_u64 (is_pure ((seq_len (lift_to_both0 msg_1610)) .* (
                lift_to_both0 (usize 8))))) in
      letb '(h_1604, block_bytes_1605) :=
        if (seq_len (lift_to_both0 raw_bytes_1614)) <.? ((
            lift_to_both0 block_bytes_v) .- (
            lift_to_both0 bitlength_bytes_v)) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset (
            [w_1584_loc ; a_1585_loc ; b_1586_loc ; c_1587_loc ; d_1588_loc ; e_1589_loc ; t_1590_loc ; h_1604_loc ; block_bytes_1605_loc])) (
          L2 := CEfset (
            [w_1584_loc ; a_1585_loc ; b_1586_loc ; c_1587_loc ; d_1588_loc ; e_1589_loc ; t_1590_loc ; h_1604_loc ; block_bytes_1605_loc ; pad_block_1606_loc])) (
          I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
          letbm block_bytes_1605 loc( block_bytes_1605_loc ) :=
            array_update (lift_to_both0 block_bytes_1605) ((
                lift_to_both0 block_bytes_v) .- (
                lift_to_both0 bitlength_bytes_v)) (
              array_to_seq (uint64_to_be_bytes (
                lift_to_both0 message_bitlength_1615))) in
          letbm h_1604 loc( h_1604_loc ) :=
            compress (lift_to_both0 block_bytes_1605) (lift_to_both0 h_1604) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
              lift_to_both0 h_1604,
              lift_to_both0 block_bytes_1605
            ))
          )
        else  lift_scope (L1 := CEfset (
            [w_1584_loc ; a_1585_loc ; b_1586_loc ; c_1587_loc ; d_1588_loc ; e_1589_loc ; t_1590_loc ; h_1604_loc ; block_bytes_1605_loc ; pad_block_1606_loc])) (
          L2 := CEfset (
            [w_1584_loc ; a_1585_loc ; b_1586_loc ; c_1587_loc ; d_1588_loc ; e_1589_loc ; t_1590_loc ; h_1604_loc ; block_bytes_1605_loc ; pad_block_1606_loc])) (
          I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
          letbm h_1604 loc( h_1604_loc ) :=
            compress (lift_to_both0 block_bytes_1605) (lift_to_both0 h_1604) in
          letbm pad_block_1606 : block_bytes_t loc( pad_block_1606_loc ) :=
            array_new_ (default : uint8) (block_bytes_v) in
          letbm pad_block_1606 loc( pad_block_1606_loc ) :=
            array_update (lift_to_both0 pad_block_1606) ((
                lift_to_both0 block_bytes_v) .- (
                lift_to_both0 bitlength_bytes_v)) (
              array_to_seq (uint64_to_be_bytes (
                lift_to_both0 message_bitlength_1615))) in
          letbm h_1604 loc( h_1604_loc ) :=
            compress (lift_to_both0 pad_block_1606) (lift_to_both0 h_1604) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
              lift_to_both0 h_1604,
              lift_to_both0 block_bytes_1605
            ))
          ) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (array_from_seq (
          hash_bytes_v) (array_to_be_bytes (lift_to_both0 h_1604)))
      ) : both (CEfset (
        [w_1584_loc ; a_1585_loc ; b_1586_loc ; c_1587_loc ; d_1588_loc ; e_1589_loc ; t_1590_loc ; h_1604_loc ; block_bytes_1605_loc ; pad_block_1606_loc])) [interface] (
      sha1_digest_t)).
Fail Next Obligation.


Notation "'sha1_inp'" :=(
  byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'sha1_inp'" :=(byte_seq : ChoiceEquality) (at level 2).
Notation "'sha1_out'" :=(
  sha1_digest_t : choice_type) (in custom pack_type at level 2).
Notation "'sha1_out'" :=(sha1_digest_t : ChoiceEquality) (at level 2).
Definition SHA1 : nat :=
  1618.
Program Definition sha1 (msg_1617 : byte_seq)
  : both (CEfset (
      [w_1584_loc ; a_1585_loc ; b_1586_loc ; c_1587_loc ; d_1588_loc ; e_1589_loc ; t_1590_loc ; h_1604_loc ; block_bytes_1605_loc ; pad_block_1606_loc])) [interface] (
    sha1_digest_t) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (hash (
          lift_to_both0 msg_1617))
      ) : both (CEfset (
        [w_1584_loc ; a_1585_loc ; b_1586_loc ; c_1587_loc ; d_1588_loc ; e_1589_loc ; t_1590_loc ; h_1604_loc ; block_bytes_1605_loc ; pad_block_1606_loc])) [interface] (
      sha1_digest_t)).
Fail Next Obligation.

