(** This file was automatically generated using Hacspec **)
From Crypt Require Import choice_type Package Prelude.
Import PackageNotation.
From extructures Require Import ord fset.

Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
Require Import Hacspec_Lib.

Definition poly_key_t := nseq (uint8) (usize 32).

Definition blocksize_v : uint_size :=
  (usize 16).

Definition poly_block_t := nseq (uint8) (usize 16).

Definition poly1305_tag_t := nseq (uint8) (usize 16).

Notation "'sub_block_t'" := (byte_seq) : hacspec_scope.

Notation "'block_index_t'" := (uint_size) : hacspec_scope.

Definition field_canvas_t := nseq (int8) (17).
Definition field_element_t := nat_mod 0x03fffffffffffffffffffffffffffffffb.

Notation "'poly_state_t'" := ((
  field_element_t '×
  field_element_t '×
  poly_key_t
)) : hacspec_scope.

Definition n_5_loc : Location :=
  (choice_type_from_type uint128 ; 12%nat).
Program Definition poly1305_encode_r
  (b_0 : poly_block_t)
  : code (fset [ n_5_loc]) [interface] (choice_type_from_type (
      field_element_t)) :=
  ({code
     temp_2 ←
      (array_from_seq (16) (array_to_seq (b_0))) ;; 
    let temp_1 := type_from_choice_type_elem temp_2 in
     temp_4 ←
      (uint128_from_le_bytes (temp_1)) ;; 
    let temp_3 := type_from_choice_type_elem temp_4 in
    #put n_5_loc := choice_type_from_type_elem
      (temp_3) ;;
    n_5 ← get n_5_loc ;;
    let n_5 := type_from_choice_type_elem (n_5) in
     temp_7 ←
      (secret (@repr WORDSIZE128 21267647620597763993911028882763415551)) ;; 
    let temp_6 := type_from_choice_type_elem temp_7 : int128 in
    let n_5 :=
      ((n_5) .& (temp_6)) in 
     temp_9 ←
      (nat_mod_from_secret_literal (n_5)) ;; 
    let temp_8 := type_from_choice_type_elem temp_9 in
    pkg_core_definition.ret (choice_type_from_type_elem (temp_8))
    } : code ((fset [ n_5_loc])) [interface] _).
Admit Obligations.


Program Definition poly1305_encode_block
  (b_13 : poly_block_t)
  : code fset.fset0 [interface] (choice_type_from_type (field_element_t)) :=
  ({code
     temp_15 ←
      (array_from_seq (16) (array_to_seq (b_13))) ;; 
    let temp_14 := type_from_choice_type_elem temp_15 in
     temp_17 ←
      (uint128_from_le_bytes (temp_14)) ;; 
    let temp_16 := type_from_choice_type_elem temp_17 in
    let n_18 : uint128 :=
      (temp_16) in 
     temp_20 ←
      (nat_mod_from_secret_literal (n_18)) ;; 
    let temp_19 := type_from_choice_type_elem temp_20 in
    let f_21 : field_element_t :=
      (temp_19) in 
     temp_23 ←
      (nat_mod_pow2 (0x03fffffffffffffffffffffffffffffffb) (usize 128)) ;; 
    let temp_22 := type_from_choice_type_elem temp_23 : field_element_t in
    pkg_core_definition.ret (choice_type_from_type_elem ((f_21) +% (temp_22)))
    } : code (fset.fset0) [interface] _).
Admit Obligations.


Program Definition poly1305_encode_last
  (pad_len_33 : block_index_t)
  (b_24 : sub_block_t)
  : code fset.fset0 [interface] (choice_type_from_type (field_element_t)) :=
  ({code
     temp_26 ←
      (array_from_slice (default) (16) (b_24) (usize 0) (seq_len (b_24))) ;; 
    let temp_25 := type_from_choice_type_elem temp_26 in
     temp_28 ←
      (uint128_from_le_bytes (temp_25)) ;; 
    let temp_27 := type_from_choice_type_elem temp_28 in
    let n_29 : uint128 :=
      (temp_27) in 
     temp_31 ←
      (nat_mod_from_secret_literal (n_29)) ;; 
    let temp_30 := type_from_choice_type_elem temp_31 in
    let f_32 : field_element_t :=
      (temp_30) in 
     temp_35 ←
      (nat_mod_pow2 (0x03fffffffffffffffffffffffffffffffb) ((usize 8) * (
            pad_len_33))) ;; 
    let temp_34 := type_from_choice_type_elem temp_35 : field_element_t in
    pkg_core_definition.ret (choice_type_from_type_elem ((f_32) +% (temp_34)))
    } : code (fset.fset0) [interface] _).
Admit Obligations.


Program Definition poly1305_init
  (k_36 : poly_key_t)
  : code (fset [ n_5_loc]) [interface] (choice_type_from_type (poly_state_t)) :=
  ({code
     temp_38 ←
      (array_from_slice (default) (16) (array_to_seq (k_36)) (usize 0) (
          usize 16)) ;; 
    let temp_37 := type_from_choice_type_elem temp_38 in
     temp_40 ←
      (poly1305_encode_r (temp_37)) ;; 
    let temp_39 := type_from_choice_type_elem temp_40 in
    let r_43 : field_element_t :=
      (temp_39) in 
     temp_42 ←
      (nat_mod_zero ) ;; 
    let temp_41 := type_from_choice_type_elem temp_42 in
    pkg_core_definition.ret (choice_type_from_type_elem ((temp_41, r_43, k_36)))
    } : code ((fset [ n_5_loc])) [interface] _).
Admit Obligations.


Program Definition poly1305_update_block
  (b_47 : poly_block_t)
  (st_46 : poly_state_t)
  : code fset.fset0 [interface] (choice_type_from_type (poly_state_t)) :=
  ({code
    let '(acc_50, r_51, k_52) :=
      (st_46) in 
     temp_49 ←
      (poly1305_encode_block (b_47)) ;; 
    let temp_48 := type_from_choice_type_elem temp_49 in
    pkg_core_definition.ret (choice_type_from_type_elem ((
        ((temp_48) +% (acc_50)) *% (r_51),
        r_51,
        k_52
      )))
    } : code (fset.fset0) [interface] _).
Admit Obligations.

Definition st_60_loc : Location :=
  (choice_type_from_type poly_state_t ; 66%nat).
Program Definition poly1305_update_blocks
  (m_54 : byte_seq)
  (st_53 : poly_state_t)
  : code (fset [ st_60_loc]) [interface] (choice_type_from_type (
      poly_state_t)) :=
  ({code
    #put st_60_loc := choice_type_from_type_elem
      (st_53) ;;
    st_60 ← get st_60_loc ;;
    let st_60 := type_from_choice_type_elem (st_60) in
    let n_blocks_55 : uint_size :=
      ((seq_len (m_54)) / (blocksize_v)) in 
     temp_63 ←
      (foldi (usize 0) (n_blocks_55) (fun i_56 st_60 =>
          {code
           temp_58 ←
            (array_from_seq (16) (seq_get_exact_chunk (m_54) ( (blocksize_v)) (
                   (i_56)))) ;; 
          let temp_57 := type_from_choice_type_elem temp_58 in
          let block_59 : poly_block_t :=
            (temp_57) in 
           temp_62 ←
            (poly1305_update_block (block_59) (st_60)) ;; 
          let temp_61 := type_from_choice_type_elem temp_62 in
          let st_60 :=
            (temp_61) in 
          pkg_core_definition.ret (choice_type_from_type_elem ((st_60)))
          } : code (fset.fset0) [interface] _)
        st_60) ;; 
    let st_60 := type_from_choice_type_elem temp_63 in
    
    pkg_core_definition.ret (choice_type_from_type_elem (st_60))
    } : code ((fset [ st_60_loc])) [interface] _).
Admit Obligations.

Definition st_68_loc : Location :=
  (choice_type_from_type poly_state_t ; 79%nat).
Program Definition poly1305_update_last
  (pad_len_70 : uint_size)
  (b_69 : sub_block_t)
  (st_67 : poly_state_t)
  : code (fset [ st_68_loc]) [interface] (choice_type_from_type (
      poly_state_t)) :=
  ({code
    #put st_68_loc := choice_type_from_type_elem
      (st_67) ;;
    st_68 ← get st_68_loc ;;
    let st_68 := type_from_choice_type_elem (st_68) in
     temp_76 ←
      (if (seq_len (b_69)) !=.? (usize 0):bool then ({code
          let '(acc_73, r_74, k_75) :=
            (st_68) in 
           temp_72 ←
            (poly1305_encode_last (pad_len_70) (b_69)) ;; 
          let temp_71 := type_from_choice_type_elem temp_72 in
          let st_68 :=
            ((((temp_71) +% (acc_73)) *% (r_74), r_74, k_75)) in 
          pkg_core_definition.ret (choice_type_from_type_elem ((st_68)))
          } : code (fset.fset0) [interface] _) else (
          pkg_core_definition.ret (choice_type_from_type_elem ((st_68))))) ;; 
    let '(st_68) := type_from_choice_type_elem temp_76 in
    
    pkg_core_definition.ret (choice_type_from_type_elem (st_68))
    } : code ((fset [ st_68_loc])) [interface] _).
Admit Obligations.


Program Definition poly1305_update
  (m_80 : byte_seq)
  (st_81 : poly_state_t)
  : code (fset [ st_60_loc ; st_68_loc]) [interface] (choice_type_from_type (
      poly_state_t)) :=
  ({code
     temp_83 ←
      (poly1305_update_blocks (m_80) (st_81)) ;; 
    let temp_82 := type_from_choice_type_elem temp_83 in
    let st_85 : (field_element_t '× field_element_t '× poly_key_t) :=
      (temp_82) in 
    let last_84 : seq uint8 :=
      (seq_get_remainder_chunk (m_80) ( (blocksize_v))) in 
     temp_87 ←
      (poly1305_update_last (seq_len (last_84)) (last_84) (st_85)) ;; 
    let temp_86 := type_from_choice_type_elem temp_87 in
    pkg_core_definition.ret (choice_type_from_type_elem (temp_86))
    } : code ((fset [ st_60_loc ; st_68_loc])) [interface] _).
Admit Obligations.


Program Definition poly1305_finish
  (st_92 : poly_state_t)
  : code fset.fset0 [interface] (choice_type_from_type (poly1305_tag_t)) :=
  ({code
    let '(acc_98, _, k_93) :=
      (st_92) in 
     temp_95 ←
      (array_from_slice (default) (16) (array_to_seq (k_93)) (usize 16) (
          usize 16)) ;; 
    let temp_94 := type_from_choice_type_elem temp_95 in
     temp_97 ←
      (uint128_from_le_bytes (temp_94)) ;; 
    let temp_96 := type_from_choice_type_elem temp_97 in
    let n_105 : uint128 :=
      (temp_96) in 
    let aby_99 : seq uint8 :=
      (nat_mod_to_byte_seq_le (acc_98)) in 
     temp_101 ←
      (array_from_slice (default) (16) (aby_99) (usize 0) (usize 16)) ;; 
    let temp_100 := type_from_choice_type_elem temp_101 in
     temp_103 ←
      (uint128_from_le_bytes (temp_100)) ;; 
    let temp_102 := type_from_choice_type_elem temp_103 in
    let a_104 : uint128 :=
      (temp_102) in 
     temp_107 ←
      (uint128_to_le_bytes ((a_104) .+ (n_105))) ;; 
    let temp_106 := type_from_choice_type_elem temp_107 in
     temp_109 ←
      (array_from_seq (16) (array_to_seq (temp_106))) ;; 
    let temp_108 := type_from_choice_type_elem temp_109 in
    pkg_core_definition.ret (choice_type_from_type_elem (temp_108))
    } : code (fset.fset0) [interface] _).
Admit Obligations.

Definition st_114_loc : Location :=
  (choice_type_from_type poly_state_t ; 127%nat).
Program Definition poly1305
  (m_113 : byte_seq)
  (key_110 : poly_key_t)
  : code (fset [ n_5_loc ; st_114_loc ; st_60_loc ; st_68_loc]) [interface] (
    choice_type_from_type (poly1305_tag_t)) :=
  ({code
     temp_112 ←
      (poly1305_init (key_110)) ;; 
    let temp_111 := type_from_choice_type_elem temp_112 in
    #put st_114_loc := choice_type_from_type_elem
      (temp_111) ;;
    st_114 ← get st_114_loc ;;
    let st_114 := type_from_choice_type_elem (st_114) in
     temp_116 ←
      (poly1305_update (m_113) (st_114)) ;; 
    let temp_115 := type_from_choice_type_elem temp_116 in
    let st_114 :=
      (temp_115) in 
     temp_118 ←
      (poly1305_finish (st_114)) ;; 
    let temp_117 := type_from_choice_type_elem temp_118 in
    pkg_core_definition.ret (choice_type_from_type_elem (temp_117))
    } : code ((
        fset [ n_5_loc ; st_114_loc ; st_60_loc ; st_68_loc])) [interface] _).
Admit Obligations.

