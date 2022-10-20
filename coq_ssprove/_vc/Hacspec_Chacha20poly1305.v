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


Require Import Hacspec_Chacha20.

Require Import Hacspec_Poly1305.

Definition error_t : ChoiceEquality :=
  unit_ChoiceEquality.
Definition InvalidTag : error_t :=
   tt.

Notation "'cha_cha_poly_key_t'" := (cha_cha_key_t) : hacspec_scope.

Notation "'cha_cha_poly_iv_t'" := (cha_cha_iv_t) : hacspec_scope.

Notation "'byte_seq_result_t'" := ((result error_t byte_seq)) : hacspec_scope.


Notation "'init_inp'" :=(
  cha_cha_poly_key_t '× cha_cha_poly_iv_t : choice_type) (in custom pack_type at level 2).
Notation "'init_inp'" :=(
  cha_cha_poly_key_t '× cha_cha_poly_iv_t : ChoiceEquality) (at level 2).
Notation "'init_out'" :=(
  poly_state_t : choice_type) (in custom pack_type at level 2).
Notation "'init_out'" :=(poly_state_t : ChoiceEquality) (at level 2).
Definition INIT : nat :=
  523.
Program Definition init
  : both_package (fset.fset0) [interface
  #val #[ CHACHA20_KEY_BLOCK0 ] : chacha20_key_block0_inp → chacha20_key_block0_out ;
  #val #[ POLY1305_INIT ] : poly1305_init_inp → poly1305_init_out ] [(INIT,(
      init_inp,init_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(
      key_519 , iv_520) := temp_inp : cha_cha_poly_key_t '× cha_cha_poly_iv_t in
    
    let chacha20_key_block0 := fun x_0 x_1 => package_both chacha20_key_block0 (
      x_0,x_1) in
    let poly1305_init := fun x_0 => package_both poly1305_init (x_0) in
    ((letb key_block0_521 : block_t :=
          chacha20_key_block0 (lift_to_both0 key_519) (lift_to_both0 iv_520) in
        letb poly_key_522 : poly_key_t :=
          array_from_slice (default : uint8) (32) (
            array_to_seq (lift_to_both0 key_block0_521)) (lift_to_both0 (
              usize 0)) (lift_to_both0 (usize 32)) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (poly1305_init (
            lift_to_both0 poly_key_522))
        ) : both (fset.fset0) [interface
      #val #[ CHACHA20_KEY_BLOCK0 ] : chacha20_key_block0_inp → chacha20_key_block0_out ;
      #val #[ POLY1305_INIT ] : poly1305_init_inp → poly1305_init_out ] (
        poly_state_t)))in
  both_package' _ _ (INIT,(init_inp,init_out)) temp_package_both.
Fail Next Obligation.


Notation "'poly1305_update_padded_inp'" :=(
  byte_seq '× poly_state_t : choice_type) (in custom pack_type at level 2).
Notation "'poly1305_update_padded_inp'" :=(
  byte_seq '× poly_state_t : ChoiceEquality) (at level 2).
Notation "'poly1305_update_padded_out'" :=(
  poly_state_t : choice_type) (in custom pack_type at level 2).
Notation "'poly1305_update_padded_out'" :=(
  poly_state_t : ChoiceEquality) (at level 2).
Definition POLY1305_UPDATE_PADDED : nat :=
  528.
Program Definition poly1305_update_padded
  : both_package (fset.fset0) [interface
  #val #[ POLY1305_UPDATE_BLOCKS ] : poly1305_update_blocks_inp → poly1305_update_blocks_out ;
  #val #[ POLY1305_UPDATE_LAST ] : poly1305_update_last_inp → poly1305_update_last_out
  ] [(POLY1305_UPDATE_PADDED,(
      poly1305_update_padded_inp,poly1305_update_padded_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(m_524 , st_525) := temp_inp : byte_seq '× poly_state_t in
    
    let poly1305_update_blocks := fun x_0 x_1 => package_both poly1305_update_blocks (
      x_0,x_1) in
    let poly1305_update_last := fun x_0 x_1 x_2 => package_both poly1305_update_last (
      x_0,x_1,x_2) in
    ((letb st_526 : (field_element_t '× field_element_t '× poly_key_t) :=
          poly1305_update_blocks (lift_to_both0 m_524) (lift_to_both0 st_525) in
        letb last_527 : seq uint8 :=
          seq_get_remainder_chunk (lift_to_both0 m_524) (lift_to_both0 (
              usize 16)) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (poly1305_update_last (
            lift_to_both0 (usize 16)) (lift_to_both0 last_527) (
            lift_to_both0 st_526))
        ) : both (fset.fset0) [interface
      #val #[ POLY1305_UPDATE_BLOCKS ] : poly1305_update_blocks_inp → poly1305_update_blocks_out ;
      #val #[ POLY1305_UPDATE_LAST ] : poly1305_update_last_inp → poly1305_update_last_out
      ] (poly_state_t)))in
  both_package' _ _ (POLY1305_UPDATE_PADDED,(
      poly1305_update_padded_inp,poly1305_update_padded_out)) temp_package_both.
Fail Next Obligation.

Definition last_block_529_loc : ChoiceEqualityLocation :=
  (poly_block_t ; 530%nat).
Notation "'finish_inp'" :=(
  uint_size '× uint_size '× poly_state_t : choice_type) (in custom pack_type at level 2).
Notation "'finish_inp'" :=(
  uint_size '× uint_size '× poly_state_t : ChoiceEquality) (at level 2).
Notation "'finish_out'" :=(
  poly1305_tag_t : choice_type) (in custom pack_type at level 2).
Notation "'finish_out'" :=(poly1305_tag_t : ChoiceEquality) (at level 2).
Definition FINISH : nat :=
  535.
Program Definition finish
  : both_package (CEfset ([last_block_529_loc])) [interface
  #val #[ POLY1305_FINISH ] : poly1305_finish_inp → poly1305_finish_out ;
  #val #[ POLY1305_UPDATE_BLOCK ] : poly1305_update_block_inp → poly1305_update_block_out
  ] [(FINISH,(finish_inp,finish_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(
      aad_len_531 , cipher_len_532 , st_533) := temp_inp : uint_size '× uint_size '× poly_state_t in
    
    let poly1305_finish := fun x_0 => package_both poly1305_finish (x_0) in
    let poly1305_update_block := fun x_0 x_1 => package_both poly1305_update_block (
      x_0,x_1) in
    ((letbm last_block_529 : poly_block_t loc( last_block_529_loc ) :=
          array_new_ (default : uint8) (16) in
        letbm last_block_529 loc( last_block_529_loc ) :=
          array_update (lift_to_both0 last_block_529) (lift_to_both0 (
              usize 0)) (array_to_seq (uint64_to_le_bytes (secret (pub_u64 (
                  is_pure (lift_to_both0 aad_len_531)))))) in
        letbm last_block_529 loc( last_block_529_loc ) :=
          array_update (lift_to_both0 last_block_529) (lift_to_both0 (
              usize 8)) (array_to_seq (uint64_to_le_bytes (secret (pub_u64 (
                  is_pure (lift_to_both0 cipher_len_532)))))) in
        letb st_534 : (field_element_t '× field_element_t '× poly_key_t) :=
          poly1305_update_block (lift_to_both0 last_block_529) (
            lift_to_both0 st_533) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (poly1305_finish (
            lift_to_both0 st_534))
        ) : both (CEfset ([last_block_529_loc])) [interface
      #val #[ POLY1305_FINISH ] : poly1305_finish_inp → poly1305_finish_out ;
      #val #[ POLY1305_UPDATE_BLOCK ] : poly1305_update_block_inp → poly1305_update_block_out
      ] (poly1305_tag_t)))in
  both_package' _ _ (FINISH,(finish_inp,finish_out)) temp_package_both.
Fail Next Obligation.

Definition poly_st_536_loc : ChoiceEqualityLocation :=
  ((field_element_t '× field_element_t '× poly_key_t) ; 537%nat).
Notation "'chacha20_poly1305_encrypt_inp'" :=(
  cha_cha_poly_key_t '× cha_cha_poly_iv_t '× byte_seq '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'chacha20_poly1305_encrypt_inp'" :=(
  cha_cha_poly_key_t '× cha_cha_poly_iv_t '× byte_seq '× byte_seq : ChoiceEquality) (at level 2).
Notation "'chacha20_poly1305_encrypt_out'" :=((byte_seq '× poly1305_tag_t
  ) : choice_type) (in custom pack_type at level 2).
Notation "'chacha20_poly1305_encrypt_out'" :=((byte_seq '× poly1305_tag_t
  ) : ChoiceEquality) (at level 2).
Definition CHACHA20_POLY1305_ENCRYPT : nat :=
  544.
Program Definition chacha20_poly1305_encrypt
  : both_package (CEfset ([poly_st_536_loc])) [interface
  #val #[ CHACHA20 ] : chacha20_inp → chacha20_out ;
  #val #[ FINISH ] : finish_inp → finish_out ;
  #val #[ INIT ] : init_inp → init_out ;
  #val #[ POLY1305_UPDATE_PADDED ] : poly1305_update_padded_inp → poly1305_update_padded_out
  ] [(CHACHA20_POLY1305_ENCRYPT,(
      chacha20_poly1305_encrypt_inp,chacha20_poly1305_encrypt_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(
      key_538 , iv_539 , aad_542 , msg_540) := temp_inp : cha_cha_poly_key_t '× cha_cha_poly_iv_t '× byte_seq '× byte_seq in
    
    let chacha20 := fun x_0 x_1 x_2 x_3 => package_both chacha20 (
      x_0,x_1,x_2,x_3) in
    let finish := fun x_0 x_1 x_2 => package_both finish (x_0,x_1,x_2) in
    let init := fun x_0 x_1 => package_both init (x_0,x_1) in
    let poly1305_update_padded := fun x_0 x_1 => package_both poly1305_update_padded (
      x_0,x_1) in
    ((letb cipher_text_541 : seq uint8 :=
          chacha20 (lift_to_both0 key_538) (lift_to_both0 iv_539) (
            lift_to_both0 (@repr U32 1)) (lift_to_both0 msg_540) in
        letbm poly_st_536 : (field_element_t '× field_element_t '× poly_key_t
          ) loc( poly_st_536_loc ) :=
          init (lift_to_both0 key_538) (lift_to_both0 iv_539) in
        letbm poly_st_536 loc( poly_st_536_loc ) :=
          poly1305_update_padded (lift_to_both0 aad_542) (
            lift_to_both0 poly_st_536) in
        letbm poly_st_536 loc( poly_st_536_loc ) :=
          poly1305_update_padded (lift_to_both0 cipher_text_541) (
            lift_to_both0 poly_st_536) in
        letb tag_543 : poly1305_tag_t :=
          finish (seq_len (lift_to_both0 aad_542)) (seq_len (
              lift_to_both0 cipher_text_541)) (lift_to_both0 poly_st_536) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
            lift_to_both0 cipher_text_541,
            lift_to_both0 tag_543
          ))
        ) : both (CEfset ([poly_st_536_loc])) [interface
      #val #[ CHACHA20 ] : chacha20_inp → chacha20_out ;
      #val #[ FINISH ] : finish_inp → finish_out ;
      #val #[ INIT ] : init_inp → init_out ;
      #val #[ POLY1305_UPDATE_PADDED ] : poly1305_update_padded_inp → poly1305_update_padded_out
      ] ((byte_seq '× poly1305_tag_t))))in
  both_package' _ _ (CHACHA20_POLY1305_ENCRYPT,(
      chacha20_poly1305_encrypt_inp,chacha20_poly1305_encrypt_out)) temp_package_both.
Fail Next Obligation.

Definition poly_st_545_loc : ChoiceEqualityLocation :=
  ((field_element_t '× field_element_t '× poly_key_t) ; 546%nat).
Notation "'chacha20_poly1305_decrypt_inp'" :=(
  cha_cha_poly_key_t '× cha_cha_poly_iv_t '× byte_seq '× byte_seq '× poly1305_tag_t : choice_type) (in custom pack_type at level 2).
Notation "'chacha20_poly1305_decrypt_inp'" :=(
  cha_cha_poly_key_t '× cha_cha_poly_iv_t '× byte_seq '× byte_seq '× poly1305_tag_t : ChoiceEquality) (at level 2).
Notation "'chacha20_poly1305_decrypt_out'" :=(
  byte_seq_result_t : choice_type) (in custom pack_type at level 2).
Notation "'chacha20_poly1305_decrypt_out'" :=(
  byte_seq_result_t : ChoiceEquality) (at level 2).
Definition CHACHA20_POLY1305_DECRYPT : nat :=
  553.
Program Definition chacha20_poly1305_decrypt
  : both_package (CEfset ([poly_st_545_loc])) [interface
  #val #[ CHACHA20 ] : chacha20_inp → chacha20_out ;
  #val #[ FINISH ] : finish_inp → finish_out ;
  #val #[ INIT ] : init_inp → init_out ;
  #val #[ POLY1305_UPDATE_PADDED ] : poly1305_update_padded_inp → poly1305_update_padded_out
  ] [(CHACHA20_POLY1305_DECRYPT,(
      chacha20_poly1305_decrypt_inp,chacha20_poly1305_decrypt_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(
      key_547 , iv_548 , aad_549 , cipher_text_550 , tag_552) := temp_inp : cha_cha_poly_key_t '× cha_cha_poly_iv_t '× byte_seq '× byte_seq '× poly1305_tag_t in
    
    let chacha20 := fun x_0 x_1 x_2 x_3 => package_both chacha20 (
      x_0,x_1,x_2,x_3) in
    let finish := fun x_0 x_1 x_2 => package_both finish (x_0,x_1,x_2) in
    let init := fun x_0 x_1 => package_both init (x_0,x_1) in
    let poly1305_update_padded := fun x_0 x_1 => package_both poly1305_update_padded (
      x_0,x_1) in
    ((letbm poly_st_545 : (field_element_t '× field_element_t '× poly_key_t
          ) loc( poly_st_545_loc ) :=
          init (lift_to_both0 key_547) (lift_to_both0 iv_548) in
        letbm poly_st_545 loc( poly_st_545_loc ) :=
          poly1305_update_padded (lift_to_both0 aad_549) (
            lift_to_both0 poly_st_545) in
        letbm poly_st_545 loc( poly_st_545_loc ) :=
          poly1305_update_padded (lift_to_both0 cipher_text_550) (
            lift_to_both0 poly_st_545) in
        letb my_tag_551 : poly1305_tag_t :=
          finish (seq_len (lift_to_both0 aad_549)) (seq_len (
              lift_to_both0 cipher_text_550)) (lift_to_both0 poly_st_545) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          if is_pure (I := [interface]) (array_declassify_eq (
              lift_to_both0 my_tag_551) (lift_to_both0 tag_552))
          then @Ok byte_seq error_t (chacha20 (lift_to_both0 key_547) (
              lift_to_both0 iv_548) (lift_to_both0 (@repr U32 1)) (
              lift_to_both0 cipher_text_550))
          else @Err byte_seq error_t (InvalidTag))
        ) : both (CEfset ([poly_st_545_loc])) [interface
      #val #[ CHACHA20 ] : chacha20_inp → chacha20_out ;
      #val #[ FINISH ] : finish_inp → finish_out ;
      #val #[ INIT ] : init_inp → init_out ;
      #val #[ POLY1305_UPDATE_PADDED ] : poly1305_update_padded_inp → poly1305_update_padded_out
      ] (byte_seq_result_t)))in
  both_package' _ _ (CHACHA20_POLY1305_DECRYPT,(
      chacha20_poly1305_decrypt_inp,chacha20_poly1305_decrypt_out)) temp_package_both.
Fail Next Obligation.

