(** This file was automatically generated using Hacspec **)
Set Warnings "-notation-overridden,-ambiguous-paths".
From Crypt Require Import choice_type Package Prelude.
Import PackageNotation.
From extructures Require Import ord fset.
From mathcomp Require Import ssrZ word.
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
  1374.
Program Definition ch
  : both_package (fset.fset0) [interface] [(CH,(ch_inp,ch_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(
      x_1371 , y_1372 , z_1373) := temp_inp : uint32 '× uint32 '× uint32 in
    
    ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (((
              lift_to_both0 x_1371) .& (lift_to_both0 y_1372)) .^ ((not (
                lift_to_both0 x_1371)) .& (lift_to_both0 z_1373)))
        ) : both (fset.fset0) [interface] (uint32)))in
  both_package' _ _ (CH,(ch_inp,ch_out)) temp_package_both.
Fail Next Obligation.


Notation "'parity_inp'" :=(
  uint32 '× uint32 '× uint32 : choice_type) (in custom pack_type at level 2).
Notation "'parity_inp'" :=(
  uint32 '× uint32 '× uint32 : ChoiceEquality) (at level 2).
Notation "'parity_out'" :=(
  uint32 : choice_type) (in custom pack_type at level 2).
Notation "'parity_out'" :=(uint32 : ChoiceEquality) (at level 2).
Definition PARITY : nat :=
  1378.
Program Definition parity
  : both_package (fset.fset0) [interface] [(PARITY,(parity_inp,parity_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(
      x_1375 , y_1376 , z_1377) := temp_inp : uint32 '× uint32 '× uint32 in
    
    ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (((
              lift_to_both0 x_1375) .^ (lift_to_both0 y_1376)) .^ (
            lift_to_both0 z_1377))
        ) : both (fset.fset0) [interface] (uint32)))in
  both_package' _ _ (PARITY,(parity_inp,parity_out)) temp_package_both.
Fail Next Obligation.


Notation "'maj_inp'" :=(
  uint32 '× uint32 '× uint32 : choice_type) (in custom pack_type at level 2).
Notation "'maj_inp'" :=(
  uint32 '× uint32 '× uint32 : ChoiceEquality) (at level 2).
Notation "'maj_out'" :=(uint32 : choice_type) (in custom pack_type at level 2).
Notation "'maj_out'" :=(uint32 : ChoiceEquality) (at level 2).
Definition MAJ : nat :=
  1382.
Program Definition maj
  : both_package (fset.fset0) [interface] [(MAJ,(maj_inp,maj_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(
      x_1379 , y_1380 , z_1381) := temp_inp : uint32 '× uint32 '× uint32 in
    
    ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) ((((
                lift_to_both0 x_1379) .& (lift_to_both0 y_1380)) .^ ((
                lift_to_both0 x_1379) .& (lift_to_both0 z_1381))) .^ ((
              lift_to_both0 y_1380) .& (lift_to_both0 z_1381)))
        ) : both (fset.fset0) [interface] (uint32)))in
  both_package' _ _ (MAJ,(maj_inp,maj_out)) temp_package_both.
Fail Next Obligation.

Definition hash_init_v : hash_t :=
  array_from_list uint32 [
    (secret (@repr U32 1732584193)) : uint32;
    (secret (@repr U32 4023233417)) : uint32;
    (secret (@repr U32 2562383102)) : uint32;
    (secret (@repr U32 271733878)) : uint32;
    (secret (@repr U32 3285377520)) : uint32
  ].

Definition e_1388_loc : ChoiceEqualityLocation :=
  (uint32 ; 1390%nat).
Definition d_1387_loc : ChoiceEqualityLocation :=
  (uint32 ; 1391%nat).
Definition b_1385_loc : ChoiceEqualityLocation :=
  (uint32 ; 1392%nat).
Definition c_1386_loc : ChoiceEqualityLocation :=
  (uint32 ; 1393%nat).
Definition t_1389_loc : ChoiceEqualityLocation :=
  (uint32 ; 1394%nat).
Definition w_1383_loc : ChoiceEqualityLocation :=
  (schedule_t ; 1395%nat).
Definition a_1384_loc : ChoiceEqualityLocation :=
  (uint32 ; 1396%nat).
Notation "'compress_inp'" :=(
  block_bytes_t '× hash_t : choice_type) (in custom pack_type at level 2).
Notation "'compress_inp'" :=(
  block_bytes_t '× hash_t : ChoiceEquality) (at level 2).
Notation "'compress_out'" :=(
  hash_t : choice_type) (in custom pack_type at level 2).
Notation "'compress_out'" :=(hash_t : ChoiceEquality) (at level 2).
Definition COMPRESS : nat :=
  1402.
Program Definition compress
  : both_package (CEfset (
      [w_1383_loc ; a_1384_loc ; b_1385_loc ; c_1386_loc ; d_1387_loc ; e_1388_loc ; t_1389_loc])) [interface
  #val #[ CH ] : ch_inp → ch_out ; #val #[ MAJ ] : maj_inp → maj_out ;
  #val #[ PARITY ] : parity_inp → parity_out ] [(COMPRESS,(
      compress_inp,compress_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(m_bytes_1397 , h_1400) := temp_inp : block_bytes_t '× hash_t in
    
    let ch := fun x_0 x_1 x_2 => package_both ch (x_0,x_1,x_2) in
    let maj := fun x_0 x_1 x_2 => package_both maj (x_0,x_1,x_2) in
    let parity := fun x_0 x_1 x_2 => package_both parity (x_0,x_1,x_2) in
    ((letb m_1398 : seq uint32 :=
          array_to_be_uint32s (lift_to_both0 m_bytes_1397) in
        letbm w_1383 : schedule_t loc( w_1383_loc ) :=
          array_new_ (default : uint32) (80) in
        letb w_1383 :=
          foldi_both' (lift_to_both0 (usize 0)) (lift_to_both0 (
                usize 80)) w_1383 (L := (CEfset (
                [w_1383_loc ; a_1384_loc ; b_1385_loc ; c_1386_loc ; d_1387_loc ; e_1388_loc ; t_1389_loc]))) (I := (
              [interface #val #[ CH ] : ch_inp → ch_out ;
              #val #[ MAJ ] : maj_inp → maj_out ;
              #val #[ PARITY ] : parity_inp → parity_out
              ])) (fun t_1399 w_1383 =>
            letb 'w_1383 :=
              if (lift_to_both0 t_1399) <.? (lift_to_both0 (
                  usize 16)) :bool_ChoiceEquality
              then lift_scope (L1 := CEfset ([w_1383_loc])) (L2 := CEfset (
                [w_1383_loc])) (I1 := [interface]) (I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
                letb w_1383 : schedule_t :=
                  array_upd w_1383 (lift_to_both0 t_1399) (is_pure (seq_index (
                        m_1398) (lift_to_both0 t_1399))) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                  lift_to_both0 w_1383)
                )
              else  lift_scope (L1 := CEfset ([w_1383_loc])) (L2 := CEfset (
                [w_1383_loc])) (I1 := [interface]) (I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
                letb w_1383 : schedule_t :=
                  array_upd w_1383 (lift_to_both0 t_1399) (is_pure (
                      uint32_rotate_left ((((array_index (w_1383) ((
                                  lift_to_both0 t_1399) .- (lift_to_both0 (
                                    usize 3)))) .^ (array_index (w_1383) ((
                                  lift_to_both0 t_1399) .- (lift_to_both0 (
                                    usize 8))))) .^ (array_index (w_1383) ((
                                lift_to_both0 t_1399) .- (lift_to_both0 (
                                  usize 14))))) .^ (array_index (w_1383) ((
                              lift_to_both0 t_1399) .- (lift_to_both0 (
                                usize 16))))) (lift_to_both0 (usize 1)))) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                  lift_to_both0 w_1383)
                ) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 w_1383)
            ) in
        letbm a_1384 : uint32 loc( a_1384_loc ) :=
          array_index (h_1400) (lift_to_both0 (usize 0)) in
        letbm b_1385 : uint32 loc( b_1385_loc ) :=
          array_index (h_1400) (lift_to_both0 (usize 1)) in
        letbm c_1386 : uint32 loc( c_1386_loc ) :=
          array_index (h_1400) (lift_to_both0 (usize 2)) in
        letbm d_1387 : uint32 loc( d_1387_loc ) :=
          array_index (h_1400) (lift_to_both0 (usize 3)) in
        letbm e_1388 : uint32 loc( e_1388_loc ) :=
          array_index (h_1400) (lift_to_both0 (usize 4)) in
        letb '(a_1384, b_1385, c_1386, d_1387, e_1388) :=
          foldi_both' (lift_to_both0 (usize 0)) (lift_to_both0 (
                usize 80)) prod_ce(a_1384, b_1385, c_1386, d_1387, e_1388
            ) (L := (CEfset (
                [w_1383_loc ; a_1384_loc ; b_1385_loc ; c_1386_loc ; d_1387_loc ; e_1388_loc ; t_1389_loc]))) (I := (
              [interface #val #[ CH ] : ch_inp → ch_out ;
              #val #[ MAJ ] : maj_inp → maj_out ;
              #val #[ PARITY ] : parity_inp → parity_out ])) (fun t_1401 '(
              a_1384,
              b_1385,
              c_1386,
              d_1387,
              e_1388
            ) =>
            letbm t_1389 : uint32 loc( t_1389_loc ) := uint32_zero  in
            letb 't_1389 :=
              if ((lift_to_both0 (usize 0)) <=.? (lift_to_both0 t_1401)) && ((
                  lift_to_both0 t_1401) <.? (lift_to_both0 (
                    usize 20))) :bool_ChoiceEquality
              then lift_scope (L1 := CEfset (
                [w_1383_loc ; a_1384_loc ; b_1385_loc ; c_1386_loc ; d_1387_loc ; e_1388_loc ; t_1389_loc])) (L2 := CEfset (
                [w_1383_loc ; a_1384_loc ; b_1385_loc ; c_1386_loc ; d_1387_loc ; e_1388_loc ; t_1389_loc])) (I1 := [interface
              #val #[ CH ] : ch_inp → ch_out ]) (I2 := [interface
              #val #[ CH ] : ch_inp → ch_out ;
              #val #[ MAJ ] : maj_inp → maj_out ;
              #val #[ PARITY ] : parity_inp → parity_out
              ]) (H_loc_incl := _) (H_opsig_incl := _) (
                letbm t_1389 loc( t_1389_loc ) :=
                  ((((uint32_rotate_left (lift_to_both0 a_1384) (lift_to_both0 (
                              usize 5))) .+ (ch (lift_to_both0 b_1385) (
                            lift_to_both0 c_1386) (lift_to_both0 d_1387))) .+ (
                        lift_to_both0 e_1388)) .+ (secret (lift_to_both0 (
                          @repr U32 1518500249)))) .+ (array_index (w_1383) (
                      lift_to_both0 t_1401)) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                  lift_to_both0 t_1389)
                )
              else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                lift_to_both0 t_1389)
               in
            letb 't_1389 :=
              if ((lift_to_both0 (usize 20)) <=.? (lift_to_both0 t_1401)) && ((
                  lift_to_both0 t_1401) <.? (lift_to_both0 (
                    usize 40))) :bool_ChoiceEquality
              then lift_scope (L1 := CEfset (
                [w_1383_loc ; a_1384_loc ; b_1385_loc ; c_1386_loc ; d_1387_loc ; e_1388_loc ; t_1389_loc])) (L2 := CEfset (
                [w_1383_loc ; a_1384_loc ; b_1385_loc ; c_1386_loc ; d_1387_loc ; e_1388_loc ; t_1389_loc])) (I1 := [interface
              #val #[ PARITY ] : parity_inp → parity_out ]) (I2 := [interface
              #val #[ CH ] : ch_inp → ch_out ;
              #val #[ MAJ ] : maj_inp → maj_out ;
              #val #[ PARITY ] : parity_inp → parity_out
              ]) (H_loc_incl := _) (H_opsig_incl := _) (
                letbm t_1389 loc( t_1389_loc ) :=
                  ((((uint32_rotate_left (lift_to_both0 a_1384) (lift_to_both0 (
                              usize 5))) .+ (parity (lift_to_both0 b_1385) (
                            lift_to_both0 c_1386) (lift_to_both0 d_1387))) .+ (
                        lift_to_both0 e_1388)) .+ (secret (lift_to_both0 (
                          @repr U32 1859775393)))) .+ (array_index (w_1383) (
                      lift_to_both0 t_1401)) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                  lift_to_both0 t_1389)
                )
              else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                lift_to_both0 t_1389)
               in
            letb 't_1389 :=
              if ((lift_to_both0 (usize 40)) <=.? (lift_to_both0 t_1401)) && ((
                  lift_to_both0 t_1401) <.? (lift_to_both0 (
                    usize 60))) :bool_ChoiceEquality
              then lift_scope (L1 := CEfset (
                [w_1383_loc ; a_1384_loc ; b_1385_loc ; c_1386_loc ; d_1387_loc ; e_1388_loc ; t_1389_loc])) (L2 := CEfset (
                [w_1383_loc ; a_1384_loc ; b_1385_loc ; c_1386_loc ; d_1387_loc ; e_1388_loc ; t_1389_loc])) (I1 := [interface
              #val #[ MAJ ] : maj_inp → maj_out ]) (I2 := [interface
              #val #[ CH ] : ch_inp → ch_out ;
              #val #[ MAJ ] : maj_inp → maj_out ;
              #val #[ PARITY ] : parity_inp → parity_out
              ]) (H_loc_incl := _) (H_opsig_incl := _) (
                letbm t_1389 loc( t_1389_loc ) :=
                  ((((uint32_rotate_left (lift_to_both0 a_1384) (lift_to_both0 (
                              usize 5))) .+ (maj (lift_to_both0 b_1385) (
                            lift_to_both0 c_1386) (lift_to_both0 d_1387))) .+ (
                        lift_to_both0 e_1388)) .+ (secret (lift_to_both0 (
                          @repr U32 2400959708)))) .+ (array_index (w_1383) (
                      lift_to_both0 t_1401)) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                  lift_to_both0 t_1389)
                )
              else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                lift_to_both0 t_1389)
               in
            letb 't_1389 :=
              if ((lift_to_both0 (usize 60)) <=.? (lift_to_both0 t_1401)) && ((
                  lift_to_both0 t_1401) <.? (lift_to_both0 (
                    usize 80))) :bool_ChoiceEquality
              then lift_scope (L1 := CEfset (
                [w_1383_loc ; a_1384_loc ; b_1385_loc ; c_1386_loc ; d_1387_loc ; e_1388_loc ; t_1389_loc])) (L2 := CEfset (
                [w_1383_loc ; a_1384_loc ; b_1385_loc ; c_1386_loc ; d_1387_loc ; e_1388_loc ; t_1389_loc])) (I1 := [interface
              #val #[ PARITY ] : parity_inp → parity_out ]) (I2 := [interface
              #val #[ CH ] : ch_inp → ch_out ;
              #val #[ MAJ ] : maj_inp → maj_out ;
              #val #[ PARITY ] : parity_inp → parity_out
              ]) (H_loc_incl := _) (H_opsig_incl := _) (
                letbm t_1389 loc( t_1389_loc ) :=
                  ((((uint32_rotate_left (lift_to_both0 a_1384) (lift_to_both0 (
                              usize 5))) .+ (parity (lift_to_both0 b_1385) (
                            lift_to_both0 c_1386) (lift_to_both0 d_1387))) .+ (
                        lift_to_both0 e_1388)) .+ (secret (lift_to_both0 (
                          @repr U32 3395469782)))) .+ (array_index (w_1383) (
                      lift_to_both0 t_1401)) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                  lift_to_both0 t_1389)
                )
              else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                lift_to_both0 t_1389)
               in
            letbm e_1388 loc( e_1388_loc ) := lift_to_both0 d_1387 in
            letbm d_1387 loc( d_1387_loc ) := lift_to_both0 c_1386 in
            letbm c_1386 loc( c_1386_loc ) :=
              uint32_rotate_left (lift_to_both0 b_1385) (lift_to_both0 (
                  usize 30)) in
            letbm b_1385 loc( b_1385_loc ) := lift_to_both0 a_1384 in
            letbm a_1384 loc( a_1384_loc ) := lift_to_both0 t_1389 in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                lift_to_both0 a_1384,
                lift_to_both0 b_1385,
                lift_to_both0 c_1386,
                lift_to_both0 d_1387,
                lift_to_both0 e_1388
              ))
            ) in
        letb h_1400 : hash_t :=
          array_upd h_1400 (lift_to_both0 (usize 0)) (is_pure ((
                lift_to_both0 a_1384) .+ (array_index (h_1400) (lift_to_both0 (
                    usize 0))))) in
        letb h_1400 : hash_t :=
          array_upd h_1400 (lift_to_both0 (usize 1)) (is_pure ((
                lift_to_both0 b_1385) .+ (array_index (h_1400) (lift_to_both0 (
                    usize 1))))) in
        letb h_1400 : hash_t :=
          array_upd h_1400 (lift_to_both0 (usize 2)) (is_pure ((
                lift_to_both0 c_1386) .+ (array_index (h_1400) (lift_to_both0 (
                    usize 2))))) in
        letb h_1400 : hash_t :=
          array_upd h_1400 (lift_to_both0 (usize 3)) (is_pure ((
                lift_to_both0 d_1387) .+ (array_index (h_1400) (lift_to_both0 (
                    usize 3))))) in
        letb h_1400 : hash_t :=
          array_upd h_1400 (lift_to_both0 (usize 4)) (is_pure ((
                lift_to_both0 e_1388) .+ (array_index (h_1400) (lift_to_both0 (
                    usize 4))))) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 h_1400)
        ) : both (CEfset (
          [w_1383_loc ; a_1384_loc ; b_1385_loc ; c_1386_loc ; d_1387_loc ; e_1388_loc ; t_1389_loc])) [interface
      #val #[ CH ] : ch_inp → ch_out ; #val #[ MAJ ] : maj_inp → maj_out ;
      #val #[ PARITY ] : parity_inp → parity_out ] (hash_t)))in
  both_package' _ _ (COMPRESS,(compress_inp,compress_out)) temp_package_both.
Fail Next Obligation.

Definition pad_block_1405_loc : ChoiceEqualityLocation :=
  (block_bytes_t ; 1406%nat).
Definition block_bytes_1404_loc : ChoiceEqualityLocation :=
  (block_bytes_t ; 1407%nat).
Definition h_1403_loc : ChoiceEqualityLocation :=
  (hash_t ; 1408%nat).
Notation "'hash_inp'" :=(
  byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'hash_inp'" :=(byte_seq : ChoiceEquality) (at level 2).
Notation "'hash_out'" :=(
  sha1_digest_t : choice_type) (in custom pack_type at level 2).
Notation "'hash_out'" :=(sha1_digest_t : ChoiceEquality) (at level 2).
Definition HASH : nat :=
  1415.
Program Definition hash
  : both_package (CEfset (
      [h_1403_loc ; block_bytes_1404_loc ; pad_block_1405_loc])) [interface
  #val #[ COMPRESS ] : compress_inp → compress_out ] [(HASH,(
      hash_inp,hash_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(msg_1409) := temp_inp : byte_seq in
    
    let compress := fun x_0 x_1 => package_both compress (x_0,x_1) in
    ((letbm h_1403 : hash_t loc( h_1403_loc ) := lift_to_both0 hash_init_v in
        letb h_1403 :=
          foldi_both' (lift_to_both0 (usize 0)) (seq_num_exact_chunks (
                lift_to_both0 msg_1409) (
                lift_to_both0 block_bytes_v)) h_1403 (L := (CEfset (
                [h_1403_loc ; block_bytes_1404_loc ; pad_block_1405_loc]))) (I := (
              [interface #val #[ COMPRESS ] : compress_inp → compress_out
              ])) (fun i_1410 h_1403 =>
            letb raw_bytes_1411 : seq uint8 :=
              seq_get_exact_chunk (lift_to_both0 msg_1409) (
                lift_to_both0 block_bytes_v) (lift_to_both0 i_1410) in
            letb block_bytes_1412 : block_bytes_t :=
              array_from_seq (block_bytes_v) (lift_to_both0 raw_bytes_1411) in
            letbm h_1403 loc( h_1403_loc ) :=
              compress (lift_to_both0 block_bytes_1412) (
                lift_to_both0 h_1403) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 h_1403)
            ) in
        letb raw_bytes_1413 : seq uint8 :=
          seq_get_remainder_chunk (lift_to_both0 msg_1409) (
            lift_to_both0 block_bytes_v) in
        letbm block_bytes_1404 : block_bytes_t loc( block_bytes_1404_loc ) :=
          array_update_start (array_new_ (default : uint8) (block_bytes_v)) (
            lift_to_both0 raw_bytes_1413) in
        letb block_bytes_1404 : block_bytes_t :=
          array_upd block_bytes_1404 (seq_len (lift_to_both0 raw_bytes_1413)) (
            is_pure (secret (lift_to_both0 (@repr U8 128)))) in
        letb message_bitlength_1414 : uint64 :=
          secret (pub_u64 (is_pure ((seq_len (lift_to_both0 msg_1409)) .* (
                  lift_to_both0 (usize 8))))) in
        letb '(h_1403, block_bytes_1404) :=
          if (seq_len (lift_to_both0 raw_bytes_1413)) <.? ((
              lift_to_both0 block_bytes_v) .- (
              lift_to_both0 bitlength_bytes_v)) :bool_ChoiceEquality
          then lift_scope (L1 := CEfset (
            [h_1403_loc ; block_bytes_1404_loc])) (L2 := CEfset (
            [h_1403_loc ; block_bytes_1404_loc ; pad_block_1405_loc])) (I1 := [interface
          #val #[ COMPRESS ] : compress_inp → compress_out
          ]) (I2 := [interface
          #val #[ COMPRESS ] : compress_inp → compress_out
          ]) (H_loc_incl := _) (H_opsig_incl := _) (
            letbm block_bytes_1404 loc( block_bytes_1404_loc ) :=
              array_update (lift_to_both0 block_bytes_1404) ((
                  lift_to_both0 block_bytes_v) .- (
                  lift_to_both0 bitlength_bytes_v)) (
                array_to_seq (uint64_to_be_bytes (
                  lift_to_both0 message_bitlength_1414))) in
            letbm h_1403 loc( h_1403_loc ) :=
              compress (lift_to_both0 block_bytes_1404) (
                lift_to_both0 h_1403) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                lift_to_both0 h_1403,
                lift_to_both0 block_bytes_1404
              ))
            )
          else  lift_scope (L1 := CEfset (
            [h_1403_loc ; block_bytes_1404_loc ; pad_block_1405_loc])) (L2 := CEfset (
            [h_1403_loc ; block_bytes_1404_loc ; pad_block_1405_loc])) (I1 := [interface
          #val #[ COMPRESS ] : compress_inp → compress_out
          ]) (I2 := [interface
          #val #[ COMPRESS ] : compress_inp → compress_out
          ]) (H_loc_incl := _) (H_opsig_incl := _) (
            letbm h_1403 loc( h_1403_loc ) :=
              compress (lift_to_both0 block_bytes_1404) (
                lift_to_both0 h_1403) in
            letbm pad_block_1405 : block_bytes_t loc( pad_block_1405_loc ) :=
              array_new_ (default : uint8) (block_bytes_v) in
            letbm pad_block_1405 loc( pad_block_1405_loc ) :=
              array_update (lift_to_both0 pad_block_1405) ((
                  lift_to_both0 block_bytes_v) .- (
                  lift_to_both0 bitlength_bytes_v)) (
                array_to_seq (uint64_to_be_bytes (
                  lift_to_both0 message_bitlength_1414))) in
            letbm h_1403 loc( h_1403_loc ) :=
              compress (lift_to_both0 pad_block_1405) (lift_to_both0 h_1403) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                lift_to_both0 h_1403,
                lift_to_both0 block_bytes_1404
              ))
            ) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (array_from_seq (
            hash_bytes_v) (array_to_be_bytes (lift_to_both0 h_1403)))
        ) : both (CEfset (
          [h_1403_loc ; block_bytes_1404_loc ; pad_block_1405_loc])) [interface
      #val #[ COMPRESS ] : compress_inp → compress_out ] (sha1_digest_t)))in
  both_package' _ _ (HASH,(hash_inp,hash_out)) temp_package_both.
Fail Next Obligation.


Notation "'sha1_inp'" :=(
  byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'sha1_inp'" :=(byte_seq : ChoiceEquality) (at level 2).
Notation "'sha1_out'" :=(
  sha1_digest_t : choice_type) (in custom pack_type at level 2).
Notation "'sha1_out'" :=(sha1_digest_t : ChoiceEquality) (at level 2).
Definition SHA1 : nat :=
  1417.
Program Definition sha1
  : both_package (CEfset ([])) [interface #val #[ HASH ] : hash_inp → hash_out
  ] [(SHA1,(sha1_inp,sha1_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(msg_1416) := temp_inp : byte_seq in
    
    let hash := fun x_0 => package_both hash (x_0) in
    ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (hash (
            lift_to_both0 msg_1416))
        ) : both (CEfset ([])) [interface #val #[ HASH ] : hash_inp → hash_out
      ] (sha1_digest_t)))in
  both_package' _ _ (SHA1,(sha1_inp,sha1_out)) temp_package_both.
Fail Next Obligation.

