(** This file was automatically generated using Hacspec **)
From Crypt Require Import choice_type Package Prelude.
Import PackageNotation.
From extructures Require Import ord fset.
From CoqWord Require Import ssrZ word.
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

Definition poly1305_encode_r_pure (b_2 : poly_block_t) : field_element_t :=
  let n_0 : uint128 :=
    uint128_from_le_bytes (array_from_seq (16) (array_to_seq (b_2))) in 
  let n_0 :=
    ((n_0) .& (secret (@repr U128 21267647620597763993911028882763415551))) in 
  nat_mod_from_secret_literal (n_0).
Definition poly1305_encode_r_pure_code
  (b_2 : poly_block_t)
  : code fset.fset0 [interface] (@ct field_element_t) :=
  lift_to_code (poly1305_encode_r_pure b_2).

Definition n_0_loc : ChoiceEqualityLocation :=
  ((uint128 ; 15%nat)).
Program Definition poly1305_encode_r_state
  (b_2 : poly_block_t) : code (CEfset ([n_0_loc])) [interface] (@ct (
      field_element_t)) :=
  (({ code  '(n_0: uint128 ) ←
          ( '(temp_4: seq uint8 ) ←
              (array_to_seq (b_2)) ;;
             temp_6 ←
              (array_from_seq (16) (temp_4)) ;;
             temp_8 ←
              (uint128_from_le_bytes (temp_6)) ;;
            ret (temp_8)) ;;
        #put n_0_loc := n_0 ;;
       n_0 ←
          (( '(temp_10: int128 ) ←
                (secret (@repr U128 21267647620597763993911028882763415551)) ;;
               temp_12 ←
                ((n_0) .& (temp_10)) ;;
              ret (temp_12))) ;;
        #put n_0_loc := n_0 ;;
      
       temp_14 ←
        (nat_mod_from_secret_literal (n_0)) ;;
      @ret (field_element_t)(temp_14) } : code (CEfset (
          [n_0_loc])) [interface] _)).
Fail Next Obligation.

Program Definition poly1305_encode_r
  (b_2 : poly_block_t)
  : both (CEfset ([n_0_loc])) [interface] (field_element_t) :=
  letbm n_0 : uint128 loc( n_0_loc ) :=
    uint128_from_le_bytes (array_from_seq (16) (
        array_to_seq (lift_to_both0 b_2))) in
  letbm n_0 loc( n_0_loc ) :=
    (lift_to_both0 n_0) .& (secret (lift_to_both0 (
          @repr U128 21267647620597763993911028882763415551))) in
  lift_scope (L2 := (CEfset ([n_0_loc]))) (H_incl := _) (
    nat_mod_from_secret_literal (lift_to_both0 n_0))
  .
Fail Next Obligation.

Definition poly1305_encode_block_pure (b_16 : poly_block_t) : field_element_t :=
  let n_17 : uint128 :=
    uint128_from_le_bytes (array_from_seq (16) (array_to_seq (b_16))) in 
  let f_18 : field_element_t :=
    nat_mod_from_secret_literal (n_17) in 
  ((f_18) +% (nat_mod_pow2 (0x03fffffffffffffffffffffffffffffffb) (usize 128))).
Definition poly1305_encode_block_pure_code
  (b_16 : poly_block_t)
  : code fset.fset0 [interface] (@ct field_element_t) :=
  lift_to_code (poly1305_encode_block_pure b_16).


Program Definition poly1305_encode_block_state
  (b_16 : poly_block_t) : code (fset.fset0) [interface] (@ct (
      field_element_t)) :=
  (({ code  '(n_17: uint128 ) ←
        ( '(temp_20: seq uint8 ) ←
            (array_to_seq (b_16)) ;;
           temp_22 ←
            (array_from_seq (16) (temp_20)) ;;
           temp_24 ←
            (uint128_from_le_bytes (temp_22)) ;;
          ret (temp_24)) ;;
       '(f_18: field_element_t ) ←
        ( temp_26 ←
            (nat_mod_from_secret_literal (n_17)) ;;
          ret (temp_26)) ;;
       '(temp_28: field_element_t ) ←
        (nat_mod_pow2 (0x03fffffffffffffffffffffffffffffffb) (usize 128)) ;;
       temp_30 ←
        ((f_18) +% (temp_28)) ;;
      @ret (field_element_t)(temp_30) } : code (fset.fset0) [interface] _)).
Fail Next Obligation.

Program Definition poly1305_encode_block
  (b_16 : poly_block_t)
  : both (fset.fset0) [interface] (field_element_t) :=
  letb n_17 : uint128 :=
    uint128_from_le_bytes (array_from_seq (16) (
        array_to_seq (lift_to_both0 b_16))) in
  letb f_18 : field_element_t :=
    nat_mod_from_secret_literal (lift_to_both0 n_17) in
  lift_scope (L2 := (fset.fset0)) (H_incl := _) ((lift_to_both0 f_18) +% (
      nat_mod_pow2 (0x03fffffffffffffffffffffffffffffffb) (lift_to_both0 (
          usize 128))))
  .
Fail Next Obligation.

Definition poly1305_encode_last_pure
  (pad_len_31 : block_index_t)
  (b_32 : sub_block_t)
  : field_element_t :=
  let n_33 : uint128 :=
    uint128_from_le_bytes (array_from_slice (default) (16) (b_32) (usize 0) (
        seq_len (b_32))) in 
  let f_34 : field_element_t :=
    nat_mod_from_secret_literal (n_33) in 
  ((f_34) +% (nat_mod_pow2 (0x03fffffffffffffffffffffffffffffffb) (((
            usize 8) .* (pad_len_31))))).
Definition poly1305_encode_last_pure_code
  (pad_len_31 : block_index_t)
  (b_32 : sub_block_t)
  : code fset.fset0 [interface] (@ct field_element_t) :=
  lift_to_code (poly1305_encode_last_pure pad_len_31 b_32).


Program Definition poly1305_encode_last_state
  (pad_len_31 : block_index_t)
  (b_32 : sub_block_t) : code (fset.fset0) [interface] (@ct (
      field_element_t)) :=
  (({ code  '(n_33: uint128 ) ←
        ( temp_36 ←
            (seq_len (b_32)) ;;
           temp_38 ←
            (array_from_slice (default) (16) (b_32) (usize 0) (temp_36)) ;;
           temp_40 ←
            (uint128_from_le_bytes (temp_38)) ;;
          ret (temp_40)) ;;
       '(f_34: field_element_t ) ←
        ( temp_42 ←
            (nat_mod_from_secret_literal (n_33)) ;;
          ret (temp_42)) ;;
       temp_44 ←
        ((usize 8) .* (pad_len_31)) ;;
       '(temp_46: field_element_t ) ←
        (nat_mod_pow2 (0x03fffffffffffffffffffffffffffffffb) (temp_44)) ;;
       temp_48 ←
        ((f_34) +% (temp_46)) ;;
      @ret (field_element_t)(temp_48) } : code (fset.fset0) [interface] _)).
Fail Next Obligation.

Program Definition poly1305_encode_last
  (pad_len_31 : block_index_t)
  (b_32 : sub_block_t)
  : both (fset.fset0) [interface] (field_element_t) :=
  letb n_33 : uint128 :=
    uint128_from_le_bytes (array_from_slice (default) (16) (
        lift_to_both0 b_32) (lift_to_both0 (usize 0)) (seq_len (
          lift_to_both0 b_32))) in
  letb f_34 : field_element_t :=
    nat_mod_from_secret_literal (lift_to_both0 n_33) in
  lift_scope (L2 := (fset.fset0)) (H_incl := _) ((lift_to_both0 f_34) +% (
      nat_mod_pow2 (0x03fffffffffffffffffffffffffffffffb) ((lift_to_both0 (
            usize 8)) .* (lift_to_both0 pad_len_31))))
  .
Fail Next Obligation.

Definition poly1305_init_pure (k_49 : poly_key_t) : poly_state_t :=
  let r_50 : field_element_t :=
    poly1305_encode_r (array_from_slice (default) (16) (array_to_seq (k_49)) (
        usize 0) (usize 16)) in 
  prod_ce(nat_mod_zero , r_50, k_49).
Definition poly1305_init_pure_code
  (k_49 : poly_key_t)
  : code fset.fset0 [interface] (@ct poly_state_t) :=
  lift_to_code (poly1305_init_pure k_49).


Program Definition poly1305_init_state
  (k_49 : poly_key_t) : code (CEfset ([n_0_loc])) [interface] (@ct (
      poly_state_t)) :=
  (({ code  '(r_50: field_element_t ) ←
        ( '(temp_52: seq uint8 ) ←
            (array_to_seq (k_49)) ;;
           temp_54 ←
            (array_from_slice (default) (16) (temp_52) (usize 0) (usize 16)) ;;
           temp_56 ←
            (poly1305_encode_r (temp_54)) ;;
          ret (temp_56)) ;;
       temp_58 ←
        (nat_mod_zero ) ;;
      @ret ((field_element_t '× field_element_t '× poly_key_t))((
          temp_58,
          r_50,
          k_49
        )) } : code (CEfset ([n_0_loc])) [interface] _)).
Fail Next Obligation.

Program Definition poly1305_init
  (k_49 : poly_key_t)
  : both (CEfset ([n_0_loc])) [interface] (poly_state_t) :=
  letb r_50 : field_element_t :=
    poly1305_encode_r (array_from_slice (default) (16) (
        array_to_seq (lift_to_both0 k_49)) (lift_to_both0 (usize 0)) (
        lift_to_both0 (usize 16))) in
  lift_scope (L2 := (CEfset ([n_0_loc]))) (H_incl := _) (prod_b(
      nat_mod_zero ,
      lift_to_both0 r_50,
      lift_to_both0 k_49
    ))
  .
Fail Next Obligation.

Definition poly1305_update_block_pure
  (b_59 : poly_block_t)
  (st_60 : poly_state_t)
  : poly_state_t :=
  let '(acc_61, r_62, k_63) :=
    st_60 : (field_element_t '× field_element_t '× poly_key_t) in 
  prod_ce(((((poly1305_encode_block (b_59)) +% (acc_61))) *% (r_62)), r_62, k_63
  ).
Definition poly1305_update_block_pure_code
  (b_59 : poly_block_t)
  (st_60 : poly_state_t)
  : code fset.fset0 [interface] (@ct poly_state_t) :=
  lift_to_code (poly1305_update_block_pure b_59 st_60).


Program Definition poly1305_update_block_state
  (b_59 : poly_block_t)
  (st_60 : poly_state_t) : code (fset.fset0) [interface] (@ct (poly_state_t)) :=
  (({ code  '((acc_61, r_62, k_63): (
            field_element_t '×
            field_element_t '×
            poly_key_t
          ) ) ←
        (ret (st_60)) ;;
       temp_65 ←
        (poly1305_encode_block (b_59)) ;;
       temp_67 ←
        ((temp_65) +% (acc_61)) ;;
       temp_69 ←
        ((temp_67) *% (r_62)) ;;
      @ret ((field_element_t '× field_element_t '× poly_key_t))((
          temp_69,
          r_62,
          k_63
        )) } : code (fset.fset0) [interface] _)).
Fail Next Obligation.

Program Definition poly1305_update_block
  (b_59 : poly_block_t)
  (st_60 : poly_state_t)
  : both (fset.fset0) [interface] (poly_state_t) :=
  letb '(acc_61, r_62, k_63) : (
      field_element_t '×
      field_element_t '×
      poly_key_t
    ) :=
    lift_to_both0 st_60 in
  lift_scope (L2 := (fset.fset0)) (H_incl := _) (prod_b(
      ((poly1305_encode_block (lift_to_both0 b_59)) +% (
          lift_to_both0 acc_61)) *% (lift_to_both0 r_62),
      lift_to_both0 r_62,
      lift_to_both0 k_63
    ))
  .
Fail Next Obligation.

Definition poly1305_update_blocks_pure
  (m_72 : byte_seq)
  (st_73 : poly_state_t)
  : poly_state_t :=
  let st_70 : (field_element_t '× field_element_t '× poly_key_t) :=
    st_73 in 
  let n_blocks_74 : uint_size :=
    ((seq_len (m_72)) ./ (blocksize_v)) in 
  let st_70 :=
    Hacspec_Lib_Pre.foldi (usize 0) (n_blocks_74) st_70
      (fun i_75 st_70 =>
      let block_76 : poly_block_t :=
        array_from_seq (16) (seq_get_exact_chunk (m_72) (blocksize_v) (
            i_75)) in 
      let st_70 :=
        poly1305_update_block (block_76) (st_70) in 
      (st_70)) in 
  st_70.
Definition poly1305_update_blocks_pure_code
  (m_72 : byte_seq)
  (st_73 : poly_state_t)
  : code fset.fset0 [interface] (@ct poly_state_t) :=
  lift_to_code (poly1305_update_blocks_pure m_72 st_73).

Definition st_70_loc : ChoiceEqualityLocation :=
  (((field_element_t '× field_element_t '× poly_key_t) ; 87%nat)).
Program Definition poly1305_update_blocks_state
  (m_72 : byte_seq)
  (st_73 : poly_state_t) : code (CEfset ([st_70_loc])) [interface] (@ct (
      poly_state_t)) :=
  (({ code  '(st_70: (field_element_t '× field_element_t '× poly_key_t) ) ←
          (ret (st_73)) ;;
        #put st_70_loc := st_70 ;;
       '(n_blocks_74: uint_size ) ←
        ( temp_78 ←
            (seq_len (m_72)) ;;
           temp_80 ←
            ((temp_78) ./ (blocksize_v)) ;;
          ret (temp_80)) ;;
       st_70 ←
        (foldi (usize 0) (n_blocks_74) st_70 (fun i_75 (st_70 : _) =>
            ({ code  '(block_76: poly_block_t ) ←
                ( temp_82 ←
                    (seq_get_exact_chunk (m_72) (blocksize_v) (i_75)) ;;
                   temp_84 ←
                    (array_from_seq (16) (temp_82)) ;;
                  ret (temp_84)) ;;
               st_70 ←
                  (( temp_86 ←
                        (poly1305_update_block (block_76) (st_70)) ;;
                      ret (temp_86))) ;;
                #put st_70_loc := st_70 ;;
              
              @ret (_)((st_70)) } : code (CEfset (
                  [st_70_loc])) [interface] _))) ;;
      
      @ret ((field_element_t '× field_element_t '× poly_key_t))(
        st_70) } : code (CEfset ([st_70_loc])) [interface] _)).
Fail Next Obligation.

Program Definition poly1305_update_blocks
  (m_72 : byte_seq)
  (st_73 : poly_state_t)
  : both (CEfset ([st_70_loc])) [interface] (poly_state_t) :=
  letbm st_70 : (field_element_t '× field_element_t '× poly_key_t
    ) loc( st_70_loc ) :=
    lift_to_both0 st_73 in
  letb n_blocks_74 : uint_size :=
    (seq_len (lift_to_both0 m_72)) ./ (lift_to_both0 blocksize_v) in
  letb st_70 :=
    foldi_both (lift_to_both0 (usize 0)) (
        lift_to_both0 n_blocks_74) st_70 (L := (CEfset (
          [st_70_loc]))) (fun i_75 (st_70 : _) =>
      letb block_76 : poly_block_t :=
        array_from_seq (16) (seq_get_exact_chunk (lift_to_both0 m_72) (
            lift_to_both0 blocksize_v) (lift_to_both0 i_75)) in
      letbm st_70 loc( st_70_loc ) :=
        poly1305_update_block (lift_to_both0 block_76) (lift_to_both0 st_70) in
      lift_scope (L2 := (CEfset ([st_70_loc]))) (H_incl := _) (
        lift_to_both0 st_70)
      ) in
  lift_scope (L2 := (CEfset ([st_70_loc]))) (H_incl := _) (lift_to_both0 st_70)
  .
Fail Next Obligation.

Definition poly1305_update_last_pure
  (pad_len_90 : uint_size)
  (b_91 : sub_block_t)
  (st_92 : poly_state_t)
  : poly_state_t :=
  let st_88 : (field_element_t '× field_element_t '× poly_key_t) :=
    st_92 in 
  let '(st_88) :=
    if (((seq_len (b_91)) !=.? (usize 0))):bool_ChoiceEquality
    then (let '(acc_93, r_94, k_95) :=
        st_88 : (field_element_t '× field_element_t '× poly_key_t) in 
      let st_88 :=
        prod_ce(
          ((((poly1305_encode_last (pad_len_90) (b_91)) +% (acc_93))) *% (
              r_94)),
          r_94,
          k_95
        ) in 
      (st_88))
    else ((st_88)) in 
  st_88.
Definition poly1305_update_last_pure_code
  (pad_len_90 : uint_size)
  (b_91 : sub_block_t)
  (st_92 : poly_state_t)
  : code fset.fset0 [interface] (@ct poly_state_t) :=
  lift_to_code (poly1305_update_last_pure pad_len_90 b_91 st_92).

Definition st_88_loc : ChoiceEqualityLocation :=
  (((field_element_t '× field_element_t '× poly_key_t) ; 106%nat)).
Program Definition poly1305_update_last_state
  (pad_len_90 : uint_size)
  (b_91 : sub_block_t)
  (st_92 : poly_state_t) : code (CEfset ([st_88_loc])) [interface] (@ct (
      poly_state_t)) :=
  (({ code  '(st_88: (field_element_t '× field_element_t '× poly_key_t) ) ←
          (ret (st_92)) ;;
        #put st_88_loc := st_88 ;;
       temp_97 ←
        (seq_len (b_91)) ;;
       temp_99 ←
        ((temp_97) !=.? (usize 0)) ;;
       '(st_88) ←
        (if temp_99:bool_ChoiceEquality then (({ code  '((acc_93, r_94, k_95): (
                    field_element_t '×
                    field_element_t '×
                    poly_key_t
                  ) ) ←
                (ret (st_88)) ;;
               st_88 ←
                  (( temp_101 ←
                        (poly1305_encode_last (pad_len_90) (b_91)) ;;
                       temp_103 ←
                        ((temp_101) +% (acc_93)) ;;
                       temp_105 ←
                        ((temp_103) *% (r_94)) ;;
                      ret ((temp_105, r_94, k_95)))) ;;
                #put st_88_loc := st_88 ;;
              
              @ret (_)((st_88)) } : code (CEfset (
                  [st_88_loc])) [interface] _)) else (@ret (_)((st_88)))) ;;
      
      @ret ((field_element_t '× field_element_t '× poly_key_t))(
        st_88) } : code (CEfset ([st_88_loc])) [interface] _)).
Fail Next Obligation.

Program Definition poly1305_update_last
  (pad_len_90 : uint_size)
  (b_91 : sub_block_t)
  (st_92 : poly_state_t)
  : both (CEfset ([st_88_loc])) [interface] (poly_state_t) :=
  letbm st_88 : (field_element_t '× field_element_t '× poly_key_t
    ) loc( st_88_loc ) :=
    lift_to_both0 st_92 in
  letb '(st_88) :=
    if (seq_len (lift_to_both0 b_91)) !=.? (lift_to_both0 (
        usize 0)):bool_ChoiceEquality
    then lift_scope (L1 := CEfset ([st_88_loc])) (L2 := CEfset (
      [st_88_loc])) (H_incl := _) (letb '(acc_93, r_94, k_95) : (
          field_element_t '×
          field_element_t '×
          poly_key_t
        ) :=
        lift_to_both0 st_88 in
      letbm st_88 loc( st_88_loc ) :=
        prod_b(
          ((poly1305_encode_last (lift_to_both0 pad_len_90) (
                lift_to_both0 b_91)) +% (lift_to_both0 acc_93)) *% (
            lift_to_both0 r_94),
          lift_to_both0 r_94,
          lift_to_both0 k_95
        ) in
      lift_scope (L2 := (CEfset ([st_88_loc]))) (H_incl := _) (
        lift_to_both0 st_88)
      )
    else (lift_scope (L2 := (CEfset ([st_88_loc]))) (H_incl := _) (
        lift_to_both0 st_88)
      ) in
  lift_scope (L2 := (CEfset ([st_88_loc]))) (H_incl := _) (lift_to_both0 st_88)
  .
Fail Next Obligation.

Definition poly1305_update_pure
  (m_107 : byte_seq)
  (st_108 : poly_state_t)
  : poly_state_t :=
  let st_109 : (field_element_t '× field_element_t '× poly_key_t) :=
    poly1305_update_blocks (m_107) (st_108) in 
  let last_110 : seq uint8 :=
    seq_get_remainder_chunk (m_107) (blocksize_v) in 
  poly1305_update_last (seq_len (last_110)) (last_110) (st_109).
Definition poly1305_update_pure_code
  (m_107 : byte_seq)
  (st_108 : poly_state_t)
  : code fset.fset0 [interface] (@ct poly_state_t) :=
  lift_to_code (poly1305_update_pure m_107 st_108).


Program Definition poly1305_update_state
  (m_107 : byte_seq)
  (st_108 : poly_state_t) : code (CEfset (
      [st_70_loc ; st_88_loc])) [interface] (@ct (poly_state_t)) :=
  (({ code  '(st_109: (field_element_t '× field_element_t '× poly_key_t) ) ←
        ( temp_112 ←
            (poly1305_update_blocks (m_107) (st_108)) ;;
          ret (temp_112)) ;;
       '(last_110: seq uint8 ) ←
        ( temp_114 ←
            (seq_get_remainder_chunk (m_107) (blocksize_v)) ;;
          ret (temp_114)) ;;
       temp_116 ←
        (seq_len (last_110)) ;;
       temp_118 ←
        (poly1305_update_last (temp_116) (last_110) (st_109)) ;;
      @ret (poly_state_t)(temp_118) } : code (CEfset (
          [st_70_loc ; st_88_loc])) [interface] _)).
Fail Next Obligation.

Program Definition poly1305_update
  (m_107 : byte_seq)
  (st_108 : poly_state_t)
  : both (CEfset ([st_70_loc ; st_88_loc])) [interface] (poly_state_t) :=
  letb st_109 : (field_element_t '× field_element_t '× poly_key_t) :=
    poly1305_update_blocks (lift_to_both0 m_107) (lift_to_both0 st_108) in
  letb last_110 : seq uint8 :=
    seq_get_remainder_chunk (lift_to_both0 m_107) (lift_to_both0 blocksize_v) in
  lift_scope (L2 := (CEfset ([st_70_loc ; st_88_loc]))) (H_incl := _) (
    poly1305_update_last (seq_len (lift_to_both0 last_110)) (
      lift_to_both0 last_110) (lift_to_both0 st_109))
  .
Fail Next Obligation.

Definition poly1305_finish_pure (st_119 : poly_state_t) : poly1305_tag_t :=
  let '(acc_120, _, k_121) :=
    st_119 : (field_element_t '× field_element_t '× poly_key_t) in 
  let n_122 : uint128 :=
    uint128_from_le_bytes (array_from_slice (default) (16) (
        array_to_seq (k_121)) (usize 16) (usize 16)) in 
  let aby_123 : seq uint8 :=
    nat_mod_to_byte_seq_le (acc_120) in 
  let a_124 : uint128 :=
    uint128_from_le_bytes (array_from_slice (default) (16) (aby_123) (usize 0) (
        usize 16)) in 
  array_from_seq (16) (array_to_seq (uint128_to_le_bytes (((a_124) .+ (
          n_122))))).
Definition poly1305_finish_pure_code
  (st_119 : poly_state_t)
  : code fset.fset0 [interface] (@ct poly1305_tag_t) :=
  lift_to_code (poly1305_finish_pure st_119).


Program Definition poly1305_finish_state
  (st_119 : poly_state_t) : code (fset.fset0) [interface] (@ct (
      poly1305_tag_t)) :=
  (({ code  '((acc_120, _, k_121): (
            field_element_t '×
            field_element_t '×
            poly_key_t
          ) ) ←
        (ret (st_119)) ;;
       '(n_122: uint128 ) ←
        ( '(temp_126: seq uint8 ) ←
            (array_to_seq (k_121)) ;;
           temp_128 ←
            (array_from_slice (default) (16) (temp_126) (usize 16) (
                usize 16)) ;;
           temp_130 ←
            (uint128_from_le_bytes (temp_128)) ;;
          ret (temp_130)) ;;
       '(aby_123: seq uint8 ) ←
        ( temp_132 ←
            (nat_mod_to_byte_seq_le (acc_120)) ;;
          ret (temp_132)) ;;
       '(a_124: uint128 ) ←
        ( temp_134 ←
            (array_from_slice (default) (16) (aby_123) (usize 0) (usize 16)) ;;
           temp_136 ←
            (uint128_from_le_bytes (temp_134)) ;;
          ret (temp_136)) ;;
       temp_138 ←
        ((a_124) .+ (n_122)) ;;
       temp_140 ←
        (uint128_to_le_bytes (temp_138)) ;;
       '(temp_142: seq uint8 ) ←
        (array_to_seq (temp_140)) ;;
       temp_144 ←
        (array_from_seq (16) (temp_142)) ;;
      @ret (poly1305_tag_t)(temp_144) } : code (fset.fset0) [interface] _)).
Fail Next Obligation.

Program Definition poly1305_finish
  (st_119 : poly_state_t)
  : both (fset.fset0) [interface] (poly1305_tag_t) :=
  letb '(acc_120, _, k_121) : (
      field_element_t '×
      field_element_t '×
      poly_key_t
    ) :=
    lift_to_both0 st_119 in
  letb n_122 : uint128 :=
    uint128_from_le_bytes (array_from_slice (default) (16) (
        array_to_seq (lift_to_both0 k_121)) (lift_to_both0 (usize 16)) (
        lift_to_both0 (usize 16))) in
  letb aby_123 : seq uint8 := nat_mod_to_byte_seq_le (lift_to_both0 acc_120) in
  letb a_124 : uint128 :=
    uint128_from_le_bytes (array_from_slice (default) (16) (
        lift_to_both0 aby_123) (lift_to_both0 (usize 0)) (lift_to_both0 (
          usize 16))) in
  lift_scope (L2 := (fset.fset0)) (H_incl := _) (array_from_seq (16) (
      array_to_seq (uint128_to_le_bytes ((lift_to_both0 a_124) .+ (
          lift_to_both0 n_122)))))
  .
Fail Next Obligation.

Definition poly1305_pure
  (m_147 : byte_seq)
  (key_148 : poly_key_t)
  : poly1305_tag_t :=
  let st_145 : (field_element_t '× field_element_t '× poly_key_t) :=
    poly1305_init (key_148) in 
  let st_145 :=
    poly1305_update (m_147) (st_145) in 
  poly1305_finish (st_145).
Definition poly1305_pure_code
  (m_147 : byte_seq)
  (key_148 : poly_key_t)
  : code fset.fset0 [interface] (@ct poly1305_tag_t) :=
  lift_to_code (poly1305_pure m_147 key_148).

Definition st_145_loc : ChoiceEqualityLocation :=
  (((field_element_t '× field_element_t '× poly_key_t) ; 155%nat)).
Program Definition poly1305_state
  (m_147 : byte_seq)
  (key_148 : poly_key_t) : code (CEfset (
      [n_0_loc ; st_70_loc ; st_88_loc ; st_145_loc])) [interface] (@ct (
      poly1305_tag_t)) :=
  (({ code  '(st_145: (field_element_t '× field_element_t '× poly_key_t) ) ←
          ( temp_150 ←
              (poly1305_init (key_148)) ;;
            ret (temp_150)) ;;
        #put st_145_loc := st_145 ;;
       st_145 ←
          (( temp_152 ←
                (poly1305_update (m_147) (st_145)) ;;
              ret (temp_152))) ;;
        #put st_145_loc := st_145 ;;
      
       temp_154 ←
        (poly1305_finish (st_145)) ;;
      @ret (poly1305_tag_t)(temp_154) } : code (CEfset (
          [n_0_loc ; st_70_loc ; st_88_loc ; st_145_loc])) [interface] _)).
Fail Next Obligation.

Program Definition poly1305
  (m_147 : byte_seq)
  (key_148 : poly_key_t)
  : both (CEfset ([n_0_loc ; st_70_loc ; st_88_loc ; st_145_loc])) [interface] (
    poly1305_tag_t) :=
  letbm st_145 : (field_element_t '× field_element_t '× poly_key_t
    ) loc( st_145_loc ) :=
    poly1305_init (lift_to_both0 key_148) in
  letbm st_145 loc( st_145_loc ) :=
    poly1305_update (lift_to_both0 m_147) (lift_to_both0 st_145) in
  lift_scope (L2 := (CEfset (
      [n_0_loc ; st_70_loc ; st_88_loc ; st_145_loc]))) (H_incl := _) (
    poly1305_finish (lift_to_both0 st_145))
  .
Fail Next Obligation.

