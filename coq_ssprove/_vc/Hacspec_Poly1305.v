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


Definition poly_key_t := nseq (uint8) (usize 32).

Definition blocksize_v : uint_size :=
  usize 16.

Definition poly_block_t := nseq (uint8) (usize 16).

Definition poly1305_tag_t := nseq (uint8) (usize 16).

Notation "'sub_block_t'" := (byte_seq) : hacspec_scope.

Notation "'block_index_t'" := (uint_size) : hacspec_scope.

Definition field_canvas_t := nseq (int8) (usize 17).
Definition field_element_t := nat_mod 0x03fffffffffffffffffffffffffffffffb.

Notation "'poly_state_t'" := ((
  field_element_t '×
  field_element_t '×
  poly_key_t
)) : hacspec_scope.

Definition n_554_loc : ChoiceEqualityLocation :=
  (uint128 ; 555%nat).
Notation "'poly1305_encode_r_inp'" :=(
  poly_block_t : choice_type) (in custom pack_type at level 2).
Notation "'poly1305_encode_r_inp'" :=(
  poly_block_t : ChoiceEquality) (at level 2).
Notation "'poly1305_encode_r_out'" :=(
  field_element_t : choice_type) (in custom pack_type at level 2).
Notation "'poly1305_encode_r_out'" :=(
  field_element_t : ChoiceEquality) (at level 2).
Definition POLY1305_ENCODE_R : nat :=
  557.
Program Definition poly1305_encode_r
  : both_package (CEfset ([n_554_loc])) [interface] [(POLY1305_ENCODE_R,(
      poly1305_encode_r_inp,poly1305_encode_r_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(b_556) := temp_inp : poly_block_t in
    
    ((letbm n_554 : uint128 loc( n_554_loc ) :=
          uint128_from_le_bytes (array_from_seq (16) (
              array_to_seq (lift_to_both0 b_556))) in
        letbm n_554 loc( n_554_loc ) :=
          (lift_to_both0 n_554) .& (secret (lift_to_both0 (
                @repr U128 21267647620597763993911028882763415551))) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          nat_mod_from_secret_literal (lift_to_both0 n_554))
        ) : both (CEfset ([n_554_loc])) [interface] (field_element_t)))in
  both_package' _ _ (POLY1305_ENCODE_R,(
      poly1305_encode_r_inp,poly1305_encode_r_out)) temp_package_both.
Fail Next Obligation.


Notation "'poly1305_encode_block_inp'" :=(
  poly_block_t : choice_type) (in custom pack_type at level 2).
Notation "'poly1305_encode_block_inp'" :=(
  poly_block_t : ChoiceEquality) (at level 2).
Notation "'poly1305_encode_block_out'" :=(
  field_element_t : choice_type) (in custom pack_type at level 2).
Notation "'poly1305_encode_block_out'" :=(
  field_element_t : ChoiceEquality) (at level 2).
Definition POLY1305_ENCODE_BLOCK : nat :=
  561.
Program Definition poly1305_encode_block
  : both_package (fset.fset0) [interface] [(POLY1305_ENCODE_BLOCK,(
      poly1305_encode_block_inp,poly1305_encode_block_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(b_558) := temp_inp : poly_block_t in
    
    ((letb n_559 : uint128 :=
          uint128_from_le_bytes (array_from_seq (16) (
              array_to_seq (lift_to_both0 b_558))) in
        letb f_560 : field_element_t :=
          nat_mod_from_secret_literal (lift_to_both0 n_559) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) ((
            lift_to_both0 f_560) +% (nat_mod_pow2 (
              0x03fffffffffffffffffffffffffffffffb) (lift_to_both0 (
                usize 128))))
        ) : both (fset.fset0) [interface] (field_element_t)))in
  both_package' _ _ (POLY1305_ENCODE_BLOCK,(
      poly1305_encode_block_inp,poly1305_encode_block_out)) temp_package_both.
Fail Next Obligation.


Notation "'poly1305_encode_last_inp'" :=(
  block_index_t '× sub_block_t : choice_type) (in custom pack_type at level 2).
Notation "'poly1305_encode_last_inp'" :=(
  block_index_t '× sub_block_t : ChoiceEquality) (at level 2).
Notation "'poly1305_encode_last_out'" :=(
  field_element_t : choice_type) (in custom pack_type at level 2).
Notation "'poly1305_encode_last_out'" :=(
  field_element_t : ChoiceEquality) (at level 2).
Definition POLY1305_ENCODE_LAST : nat :=
  566.
Program Definition poly1305_encode_last
  : both_package (fset.fset0) [interface] [(POLY1305_ENCODE_LAST,(
      poly1305_encode_last_inp,poly1305_encode_last_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(pad_len_565 , b_562) := temp_inp : block_index_t '× sub_block_t in
    
    ((letb n_563 : uint128 :=
          uint128_from_le_bytes (array_from_slice (default : uint8) (16) (
              lift_to_both0 b_562) (lift_to_both0 (usize 0)) (seq_len (
                lift_to_both0 b_562))) in
        letb f_564 : field_element_t :=
          nat_mod_from_secret_literal (lift_to_both0 n_563) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) ((
            lift_to_both0 f_564) +% (nat_mod_pow2 (
              0x03fffffffffffffffffffffffffffffffb) ((lift_to_both0 (
                  usize 8)) .* (lift_to_both0 pad_len_565))))
        ) : both (fset.fset0) [interface] (field_element_t)))in
  both_package' _ _ (POLY1305_ENCODE_LAST,(
      poly1305_encode_last_inp,poly1305_encode_last_out)) temp_package_both.
Fail Next Obligation.


Notation "'poly1305_init_inp'" :=(
  poly_key_t : choice_type) (in custom pack_type at level 2).
Notation "'poly1305_init_inp'" :=(poly_key_t : ChoiceEquality) (at level 2).
Notation "'poly1305_init_out'" :=(
  poly_state_t : choice_type) (in custom pack_type at level 2).
Notation "'poly1305_init_out'" :=(poly_state_t : ChoiceEquality) (at level 2).
Definition POLY1305_INIT : nat :=
  569.
Program Definition poly1305_init
  : both_package (CEfset ([])) [interface
  #val #[ POLY1305_ENCODE_R ] : poly1305_encode_r_inp → poly1305_encode_r_out
  ] [(POLY1305_INIT,(poly1305_init_inp,poly1305_init_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(k_567) := temp_inp : poly_key_t in
    
    let poly1305_encode_r := fun x_0 => package_both poly1305_encode_r (x_0) in
    ((letb r_568 : field_element_t :=
          poly1305_encode_r (array_from_slice (default : uint8) (16) (
              array_to_seq (lift_to_both0 k_567)) (lift_to_both0 (usize 0)) (
              lift_to_both0 (usize 16))) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
            nat_mod_zero ,
            lift_to_both0 r_568,
            lift_to_both0 k_567
          ))
        ) : both (CEfset ([])) [interface
      #val #[ POLY1305_ENCODE_R ] : poly1305_encode_r_inp → poly1305_encode_r_out
      ] (poly_state_t)))in
  both_package' _ _ (POLY1305_INIT,(
      poly1305_init_inp,poly1305_init_out)) temp_package_both.
Fail Next Obligation.


Notation "'poly1305_update_block_inp'" :=(
  poly_block_t '× poly_state_t : choice_type) (in custom pack_type at level 2).
Notation "'poly1305_update_block_inp'" :=(
  poly_block_t '× poly_state_t : ChoiceEquality) (at level 2).
Notation "'poly1305_update_block_out'" :=(
  poly_state_t : choice_type) (in custom pack_type at level 2).
Notation "'poly1305_update_block_out'" :=(
  poly_state_t : ChoiceEquality) (at level 2).
Definition POLY1305_UPDATE_BLOCK : nat :=
  575.
Program Definition poly1305_update_block
  : both_package (fset.fset0) [interface
  #val #[ POLY1305_ENCODE_BLOCK ] : poly1305_encode_block_inp → poly1305_encode_block_out
  ] [(POLY1305_UPDATE_BLOCK,(
      poly1305_update_block_inp,poly1305_update_block_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(b_574 , st_570) := temp_inp : poly_block_t '× poly_state_t in
    
    let poly1305_encode_block := fun x_0 => package_both poly1305_encode_block (
      x_0) in
    ((letb '(acc_571, r_572, k_573) : (
            field_element_t '×
            field_element_t '×
            poly_key_t
          ) :=
          lift_to_both0 st_570 in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
            ((poly1305_encode_block (lift_to_both0 b_574)) +% (
                lift_to_both0 acc_571)) *% (lift_to_both0 r_572),
            lift_to_both0 r_572,
            lift_to_both0 k_573
          ))
        ) : both (fset.fset0) [interface
      #val #[ POLY1305_ENCODE_BLOCK ] : poly1305_encode_block_inp → poly1305_encode_block_out
      ] (poly_state_t)))in
  both_package' _ _ (POLY1305_UPDATE_BLOCK,(
      poly1305_update_block_inp,poly1305_update_block_out)) temp_package_both.
Fail Next Obligation.

Definition st_576_loc : ChoiceEqualityLocation :=
  ((field_element_t '× field_element_t '× poly_key_t) ; 577%nat).
Notation "'poly1305_update_blocks_inp'" :=(
  byte_seq '× poly_state_t : choice_type) (in custom pack_type at level 2).
Notation "'poly1305_update_blocks_inp'" :=(
  byte_seq '× poly_state_t : ChoiceEquality) (at level 2).
Notation "'poly1305_update_blocks_out'" :=(
  poly_state_t : choice_type) (in custom pack_type at level 2).
Notation "'poly1305_update_blocks_out'" :=(
  poly_state_t : ChoiceEquality) (at level 2).
Definition POLY1305_UPDATE_BLOCKS : nat :=
  583.
Program Definition poly1305_update_blocks
  : both_package (CEfset ([st_576_loc])) [interface
  #val #[ POLY1305_UPDATE_BLOCK ] : poly1305_update_block_inp → poly1305_update_block_out
  ] [(POLY1305_UPDATE_BLOCKS,(
      poly1305_update_blocks_inp,poly1305_update_blocks_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(m_579 , st_578) := temp_inp : byte_seq '× poly_state_t in
    
    let poly1305_update_block := fun x_0 x_1 => package_both poly1305_update_block (
      x_0,x_1) in
    ((letbm st_576 : (field_element_t '× field_element_t '× poly_key_t
          ) loc( st_576_loc ) :=
          lift_to_both0 st_578 in
        letb n_blocks_580 : uint_size :=
          (seq_len (lift_to_both0 m_579)) ./ (lift_to_both0 blocksize_v) in
        letb st_576 :=
          foldi_both' (lift_to_both0 (usize 0)) (
              lift_to_both0 n_blocks_580) st_576 (L := (CEfset (
                [st_576_loc]))) (I := ([interface
              #val #[ POLY1305_UPDATE_BLOCK ] : poly1305_update_block_inp → poly1305_update_block_out
              ])) (fun i_581 st_576 =>
            letb block_582 : poly_block_t :=
              array_from_seq (16) (seq_get_exact_chunk (lift_to_both0 m_579) (
                  lift_to_both0 blocksize_v) (lift_to_both0 i_581)) in
            letbm st_576 loc( st_576_loc ) :=
              poly1305_update_block (lift_to_both0 block_582) (
                lift_to_both0 st_576) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 st_576)
            ) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 st_576)
        ) : both (CEfset ([st_576_loc])) [interface
      #val #[ POLY1305_UPDATE_BLOCK ] : poly1305_update_block_inp → poly1305_update_block_out
      ] (poly_state_t)))in
  both_package' _ _ (POLY1305_UPDATE_BLOCKS,(
      poly1305_update_blocks_inp,poly1305_update_blocks_out)) temp_package_both.
Fail Next Obligation.

Definition st_584_loc : ChoiceEqualityLocation :=
  ((field_element_t '× field_element_t '× poly_key_t) ; 585%nat).
Notation "'poly1305_update_last_inp'" :=(
  uint_size '× sub_block_t '× poly_state_t : choice_type) (in custom pack_type at level 2).
Notation "'poly1305_update_last_inp'" :=(
  uint_size '× sub_block_t '× poly_state_t : ChoiceEquality) (at level 2).
Notation "'poly1305_update_last_out'" :=(
  poly_state_t : choice_type) (in custom pack_type at level 2).
Notation "'poly1305_update_last_out'" :=(
  poly_state_t : ChoiceEquality) (at level 2).
Definition POLY1305_UPDATE_LAST : nat :=
  592.
Program Definition poly1305_update_last
  : both_package (CEfset ([st_584_loc])) [interface
  #val #[ POLY1305_ENCODE_LAST ] : poly1305_encode_last_inp → poly1305_encode_last_out
  ] [(POLY1305_UPDATE_LAST,(
      poly1305_update_last_inp,poly1305_update_last_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(
      pad_len_591 , b_587 , st_586) := temp_inp : uint_size '× sub_block_t '× poly_state_t in
    
    let poly1305_encode_last := fun x_0 x_1 => package_both poly1305_encode_last (
      x_0,x_1) in
    ((letbm st_584 : (field_element_t '× field_element_t '× poly_key_t
          ) loc( st_584_loc ) :=
          lift_to_both0 st_586 in
        letb 'st_584 :=
          if (seq_len (lift_to_both0 b_587)) !=.? (lift_to_both0 (
              usize 0)) :bool_ChoiceEquality
          then lift_scope (L1 := CEfset ([st_584_loc])) (L2 := CEfset (
            [st_584_loc])) (I1 := [interface
          #val #[ POLY1305_ENCODE_LAST ] : poly1305_encode_last_inp → poly1305_encode_last_out
          ]) (I2 := [interface
          #val #[ POLY1305_ENCODE_LAST ] : poly1305_encode_last_inp → poly1305_encode_last_out
          ]) (H_loc_incl := _) (H_opsig_incl := _) (letb '(acc_588, r_589, k_590
              ) : (field_element_t '× field_element_t '× poly_key_t) :=
              lift_to_both0 st_584 in
            letbm st_584 loc( st_584_loc ) :=
              prod_b(
                ((poly1305_encode_last (lift_to_both0 pad_len_591) (
                      lift_to_both0 b_587)) +% (lift_to_both0 acc_588)) *% (
                  lift_to_both0 r_589),
                lift_to_both0 r_589,
                lift_to_both0 k_590
              ) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 st_584)
            )
          else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 st_584)
           in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 st_584)
        ) : both (CEfset ([st_584_loc])) [interface
      #val #[ POLY1305_ENCODE_LAST ] : poly1305_encode_last_inp → poly1305_encode_last_out
      ] (poly_state_t)))in
  both_package' _ _ (POLY1305_UPDATE_LAST,(
      poly1305_update_last_inp,poly1305_update_last_out)) temp_package_both.
Fail Next Obligation.


Notation "'poly1305_update_inp'" :=(
  byte_seq '× poly_state_t : choice_type) (in custom pack_type at level 2).
Notation "'poly1305_update_inp'" :=(
  byte_seq '× poly_state_t : ChoiceEquality) (at level 2).
Notation "'poly1305_update_out'" :=(
  poly_state_t : choice_type) (in custom pack_type at level 2).
Notation "'poly1305_update_out'" :=(poly_state_t : ChoiceEquality) (at level 2).
Definition POLY1305_UPDATE : nat :=
  597.
Program Definition poly1305_update
  : both_package (CEfset ([])) [interface
  #val #[ POLY1305_UPDATE_BLOCKS ] : poly1305_update_blocks_inp → poly1305_update_blocks_out ;
  #val #[ POLY1305_UPDATE_LAST ] : poly1305_update_last_inp → poly1305_update_last_out
  ] [(POLY1305_UPDATE,(poly1305_update_inp,poly1305_update_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(m_593 , st_594) := temp_inp : byte_seq '× poly_state_t in
    
    let poly1305_update_blocks := fun x_0 x_1 => package_both poly1305_update_blocks (
      x_0,x_1) in
    let poly1305_update_last := fun x_0 x_1 x_2 => package_both poly1305_update_last (
      x_0,x_1,x_2) in
    ((letb st_595 : (field_element_t '× field_element_t '× poly_key_t) :=
          poly1305_update_blocks (lift_to_both0 m_593) (lift_to_both0 st_594) in
        letb last_596 : seq uint8 :=
          seq_get_remainder_chunk (lift_to_both0 m_593) (
            lift_to_both0 blocksize_v) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (poly1305_update_last (
            seq_len (lift_to_both0 last_596)) (lift_to_both0 last_596) (
            lift_to_both0 st_595))
        ) : both (CEfset ([])) [interface
      #val #[ POLY1305_UPDATE_BLOCKS ] : poly1305_update_blocks_inp → poly1305_update_blocks_out ;
      #val #[ POLY1305_UPDATE_LAST ] : poly1305_update_last_inp → poly1305_update_last_out
      ] (poly_state_t)))in
  both_package' _ _ (POLY1305_UPDATE,(
      poly1305_update_inp,poly1305_update_out)) temp_package_both.
Fail Next Obligation.


Notation "'poly1305_finish_inp'" :=(
  poly_state_t : choice_type) (in custom pack_type at level 2).
Notation "'poly1305_finish_inp'" :=(poly_state_t : ChoiceEquality) (at level 2).
Notation "'poly1305_finish_out'" :=(
  poly1305_tag_t : choice_type) (in custom pack_type at level 2).
Notation "'poly1305_finish_out'" :=(
  poly1305_tag_t : ChoiceEquality) (at level 2).
Definition POLY1305_FINISH : nat :=
  604.
Program Definition poly1305_finish
  : both_package (fset.fset0) [interface] [(POLY1305_FINISH,(
      poly1305_finish_inp,poly1305_finish_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(st_598) := temp_inp : poly_state_t in
    
    ((letb '(acc_599, _, k_600) : (
            field_element_t '×
            field_element_t '×
            poly_key_t
          ) :=
          lift_to_both0 st_598 in
        letb n_601 : uint128 :=
          uint128_from_le_bytes (array_from_slice (default : uint8) (16) (
              array_to_seq (lift_to_both0 k_600)) (lift_to_both0 (usize 16)) (
              lift_to_both0 (usize 16))) in
        letb aby_602 : seq uint8 :=
          nat_mod_to_byte_seq_le (lift_to_both0 acc_599) in
        letb a_603 : uint128 :=
          uint128_from_le_bytes (array_from_slice (default : uint8) (16) (
              lift_to_both0 aby_602) (lift_to_both0 (usize 0)) (lift_to_both0 (
                usize 16))) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (array_from_seq (16) (
            array_to_seq (uint128_to_le_bytes ((lift_to_both0 a_603) .+ (
                lift_to_both0 n_601)))))
        ) : both (fset.fset0) [interface] (poly1305_tag_t)))in
  both_package' _ _ (POLY1305_FINISH,(
      poly1305_finish_inp,poly1305_finish_out)) temp_package_both.
Fail Next Obligation.

Definition st_605_loc : ChoiceEqualityLocation :=
  ((field_element_t '× field_element_t '× poly_key_t) ; 606%nat).
Notation "'poly1305_inp'" :=(
  byte_seq '× poly_key_t : choice_type) (in custom pack_type at level 2).
Notation "'poly1305_inp'" :=(
  byte_seq '× poly_key_t : ChoiceEquality) (at level 2).
Notation "'poly1305_out'" :=(
  poly1305_tag_t : choice_type) (in custom pack_type at level 2).
Notation "'poly1305_out'" :=(poly1305_tag_t : ChoiceEquality) (at level 2).
Definition POLY1305 : nat :=
  609.
Program Definition poly1305
  : both_package (CEfset ([st_605_loc])) [interface
  #val #[ POLY1305_FINISH ] : poly1305_finish_inp → poly1305_finish_out ;
  #val #[ POLY1305_INIT ] : poly1305_init_inp → poly1305_init_out ;
  #val #[ POLY1305_UPDATE ] : poly1305_update_inp → poly1305_update_out ] [(
    POLY1305,(poly1305_inp,poly1305_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(m_608 , key_607) := temp_inp : byte_seq '× poly_key_t in
    
    let poly1305_finish := fun x_0 => package_both poly1305_finish (x_0) in
    let poly1305_init := fun x_0 => package_both poly1305_init (x_0) in
    let poly1305_update := fun x_0 x_1 => package_both poly1305_update (
      x_0,x_1) in
    ((letbm st_605 : (field_element_t '× field_element_t '× poly_key_t
          ) loc( st_605_loc ) :=
          poly1305_init (lift_to_both0 key_607) in
        letbm st_605 loc( st_605_loc ) :=
          poly1305_update (lift_to_both0 m_608) (lift_to_both0 st_605) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (poly1305_finish (
            lift_to_both0 st_605))
        ) : both (CEfset ([st_605_loc])) [interface
      #val #[ POLY1305_FINISH ] : poly1305_finish_inp → poly1305_finish_out ;
      #val #[ POLY1305_INIT ] : poly1305_init_inp → poly1305_init_out ;
      #val #[ POLY1305_UPDATE ] : poly1305_update_inp → poly1305_update_out
      ] (poly1305_tag_t)))in
  both_package' _ _ (POLY1305,(poly1305_inp,poly1305_out)) temp_package_both.
Fail Next Obligation.

