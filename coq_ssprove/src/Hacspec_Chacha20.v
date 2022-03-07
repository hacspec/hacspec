(** This file was automatically generated using Hacspec **)
From Crypt Require Import choice_type Package Prelude.
Import PackageNotation.
From extructures Require Import ord fset.
From CoqWord Require Import ssrZ word.
From Jasmin Require Import word.
Require Import ChoiceEquality.

From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope list_scope.
Open Scope Z_scope.
Open Scope bool_scope.

Require Import Hacspec_Lib_Comparable.
Require Import Hacspec_Lib_Pre.
Require Import Hacspec_Lib.

Open Scope hacspec_scope.


Obligation Tactic :=
(intros ; do 2 ssprove_valid'_2) ||
(try (Tactics.program_simpl; fail); simpl). (* Old Obligation Tactic *)

Require Import Hacspec_Lib.

Definition state_t := nseq (uint32) (usize 16).

Definition state_idx_t :=
  (nat_mod (usize 16)).
Definition uint_size_in_state_idx_t(n : uint_size) : state_idx_t := int_in_nat_mod n.
Coercion uint_size_in_state_idx_t : uint_size >-> state_idx_t.

Definition constants_t := nseq (uint32) (usize 4).

Definition constants_idx_t :=
  (nat_mod (usize 4)).
Definition uint_size_in_constants_idx_t(n : uint_size) : constants_idx_t := int_in_nat_mod n.
Coercion uint_size_in_constants_idx_t : uint_size >-> constants_idx_t.

Definition block_t := nseq (uint8) (usize 64).

Definition cha_cha_iv_t := nseq (uint8) (usize 12).

Definition cha_cha_key_t := nseq (uint8) (usize 32).

Definition state_2_loc : Location :=
  (state_t : choice_type ; 7%nat).
Program Definition chacha20_line
  (a_1 : state_idx_t)
  (b_3 : state_idx_t)
  (d_4 : state_idx_t)
  (s_5 : uint_size)
  (m_0 : state_t)
  : code (fset (path.sort leb [ state_2_loc])) [interface] (@ct (state_t)) :=
  (({code #put state_2_loc := 
        (m_0) ;;
      state_2 ← get state_2_loc ;;
      let state_2 : state_t :=
        (state_2) in
       state_2 ←
        (array_upd state_2 (a_1) ((array_index (state_2) (a_1)) .+ (
              array_index (state_2) (b_3)))) ;;
      let state_2 : state_t :=
        (state_2) in
      
       state_2 ←
        (array_upd state_2 (d_4) ((array_index (state_2) (d_4)) .^ (
              array_index (state_2) (a_1)))) ;;
      let state_2 : state_t :=
        (state_2) in
      
       temp_6 ←
        (uint32_rotate_left (array_index (state_2) (d_4)) (s_5)) ;;
       state_2 ←
        (array_upd state_2 (d_4) (temp_6)) ;;
      let state_2 : state_t :=
        (state_2) in
      
      @pkg_core_definition.ret (state_t) ( (state_2)) } : code (fset (
          path.sort leb [ state_2_loc])) [interface] _)).
Fail Next Obligation.


Program Definition chacha20_quarter_round
  (a_8 : state_idx_t)
  (b_9 : state_idx_t)
  (c_13 : state_idx_t)
  (d_10 : state_idx_t)
  (state_11 : state_t)
  : code (fset (path.sort leb [ state_2_loc])) [interface] (@ct (state_t)) :=
  (({code  temp_12 ←
        (chacha20_line (a_8) (b_9) (d_10) (usize 16) (state_11)) ;;
      let state_14 : state_t :=
        (temp_12) in
       temp_15 ←
        (chacha20_line (c_13) (d_10) (b_9) (usize 12) (state_14)) ;;
      let state_16 : state_t :=
        (temp_15) in
       temp_17 ←
        (chacha20_line (a_8) (b_9) (d_10) (usize 8) (state_16)) ;;
      let state_18 : state_t :=
        (temp_17) in
       temp_19 ←
        (chacha20_line (c_13) (d_10) (b_9) (usize 7) (state_18)) ;;
      @pkg_core_definition.ret (state_t) ( (temp_19)) } : code (fset (
          path.sort leb [ state_2_loc])) [interface] _)).
Fail Next Obligation.


Program Definition chacha20_double_round
  (state_20 : state_t)
  : code (fset (path.sort leb [ state_2_loc])) [interface] (@ct (state_t)) :=
  (({code  temp_21 ←
        (chacha20_quarter_round (usize 0) (usize 4) (usize 8) (usize 12) (
            state_20)) ;;
      let state_22 : state_t :=
        (temp_21) in
       temp_23 ←
        (chacha20_quarter_round (usize 1) (usize 5) (usize 9) (usize 13) (
            state_22)) ;;
      let state_24 : state_t :=
        (temp_23) in
       temp_25 ←
        (chacha20_quarter_round (usize 2) (usize 6) (usize 10) (usize 14) (
            state_24)) ;;
      let state_26 : state_t :=
        (temp_25) in
       temp_27 ←
        (chacha20_quarter_round (usize 3) (usize 7) (usize 11) (usize 15) (
            state_26)) ;;
      let state_28 : state_t :=
        (temp_27) in
       temp_29 ←
        (chacha20_quarter_round (usize 0) (usize 5) (usize 10) (usize 15) (
            state_28)) ;;
      let state_30 : state_t :=
        (temp_29) in
       temp_31 ←
        (chacha20_quarter_round (usize 1) (usize 6) (usize 11) (usize 12) (
            state_30)) ;;
      let state_32 : state_t :=
        (temp_31) in
       temp_33 ←
        (chacha20_quarter_round (usize 2) (usize 7) (usize 8) (usize 13) (
            state_32)) ;;
      let state_34 : state_t :=
        (temp_33) in
       temp_35 ←
        (chacha20_quarter_round (usize 3) (usize 4) (usize 9) (usize 14) (
            state_34)) ;;
      @pkg_core_definition.ret (state_t) ( (temp_35)) } : code (fset (
          path.sort leb [ state_2_loc])) [interface] _)).
Fail Next Obligation.

Definition st_37_loc : Location :=
  (state_t : choice_type ; 40%nat).
Program Definition chacha20_rounds
  (state_36 : state_t)
  : code (fset (path.sort leb [ state_2_loc ; st_37_loc])) [interface] (@ct (
      state_t)) :=
  (({code #put st_37_loc := 
        (state_36) ;;
      st_37 ← get st_37_loc ;;
      let st_37 : state_t :=
        (st_37) in
       st_37 ←
        (foldi (usize 0) (usize 10) (fun i_39 (st_37 : _) =>
            ({code  temp_38 ←
                (chacha20_double_round (st_37)) ;;
              st_37 ← get st_37_loc ;;
              
              #put st_37_loc := 
                (temp_38) ;;
              st_37 ← get st_37_loc ;;
              
              @pkg_core_definition.ret (_) ( ((st_37))) } : code (fset (
                  path.sort leb [ state_2_loc ; st_37_loc])) [interface] _))
          st_37) ;;
      
      @pkg_core_definition.ret (state_t) ( (st_37)) } : code (fset (
          path.sort leb [ state_2_loc ; st_37_loc])) [interface] _)).
Fail Next Obligation.

Definition state_42_loc : Location :=
  (state_t : choice_type ; 46%nat).
Program Definition chacha20_core
  (ctr_43 : uint32)
  (st0_41 : state_t)
  : code (fset (
      path.sort leb [ state_42_loc ; state_2_loc ; st_37_loc])) [interface] (
    @ct (state_t)) :=
  (({code #put state_42_loc := 
        (st0_41) ;;
      state_42 ← get state_42_loc ;;
      let state_42 : state_t :=
        (state_42) in
       state_42 ←
        (array_upd state_42 (usize 12) ((array_index (state_42) (usize 12)) .+ (
              ctr_43))) ;;
      let state_42 : state_t :=
        (state_42) in
      
       temp_44 ←
        (chacha20_rounds (state_42)) ;;
      let k_45 : state_t :=
        (temp_44) in
      @pkg_core_definition.ret (state_t) ( ((k_45) array_add (
          state_42))) } : code (fset (
          path.sort leb [ state_42_loc ; state_2_loc ; st_37_loc])) [interface] _)).
Fail Next Obligation.

Definition constants_52_loc : Location :=
  (constants_t : choice_type ; 53%nat).
Program Definition chacha20_constants_init
  
  : code (fset (path.sort leb [ constants_52_loc])) [interface] (@ct (
      constants_t)) :=
  (({code  temp_47 ←
        (array_new_ (default) (4)) ;;
      #put constants_52_loc := 
        (temp_47) ;;
      constants_52 ← get constants_52_loc ;;
      let constants_52 : constants_t :=
        (constants_52) in
       temp_48 ←
        (secret (@repr U32 1634760805)) ;;
      let temp_48 : int32 :=
        (temp_48) in
       constants_52 ←
        (array_upd constants_52 (usize 0) (temp_48)) ;;
      let constants_52 : constants_t :=
        (constants_52) in
      
       temp_49 ←
        (secret (@repr U32 857760878)) ;;
      let temp_49 : int32 :=
        (temp_49) in
       constants_52 ←
        (array_upd constants_52 (usize 1) (temp_49)) ;;
      let constants_52 : constants_t :=
        (constants_52) in
      
       temp_50 ←
        (secret (@repr U32 2036477234)) ;;
      let temp_50 : int32 :=
        (temp_50) in
       constants_52 ←
        (array_upd constants_52 (usize 2) (temp_50)) ;;
      let constants_52 : constants_t :=
        (constants_52) in
      
       temp_51 ←
        (secret (@repr U32 1797285236)) ;;
      let temp_51 : int32 :=
        (temp_51) in
       constants_52 ←
        (array_upd constants_52 (usize 3) (temp_51)) ;;
      let constants_52 : constants_t :=
        (constants_52) in
      
      @pkg_core_definition.ret (constants_t) ( (constants_52)) } : code (fset (
          path.sort leb [ constants_52_loc])) [interface] _)).
Fail Next Obligation.

Definition st_55_loc : Location :=
  (state_t : choice_type ; 66%nat).
Program Definition chacha20_init
  (key_59 : cha_cha_key_t)
  (iv_63 : cha_cha_iv_t)
  (ctr_62 : uint32)
  : code (fset (path.sort leb [ st_55_loc ; constants_52_loc])) [interface] (
    @ct (state_t)) :=
  (({code  temp_54 ←
        (array_new_ (default) (16)) ;;
      #put st_55_loc := 
        (temp_54) ;;
      st_55 ← get st_55_loc ;;
      let st_55 : state_t :=
        (st_55) in
       temp_56 ←
        (chacha20_constants_init ) ;;
       temp_57 ←
        (array_to_seq (temp_56)) ;;
      let temp_57 : seq uint32 :=
        (temp_57) in
       temp_58 ←
        (array_update (st_55) (usize 0) (temp_57)) ;;
      st_55 ← get st_55_loc ;;
      
      #put st_55_loc := 
        (temp_58) ;;
      st_55 ← get st_55_loc ;;
      
       temp_60 ←
        (array_to_le_uint32s (key_59)) ;;
       temp_61 ←
        (array_update (st_55) (usize 4) (temp_60)) ;;
      st_55 ← get st_55_loc ;;
      
      #put st_55_loc := 
        (temp_61) ;;
      st_55 ← get st_55_loc ;;
      
       st_55 ←
        (array_upd st_55 (usize 12) (ctr_62)) ;;
      let st_55 : state_t :=
        (st_55) in
      
       temp_64 ←
        (array_to_le_uint32s (iv_63)) ;;
       temp_65 ←
        (array_update (st_55) (usize 13) (temp_64)) ;;
      st_55 ← get st_55_loc ;;
      
      #put st_55_loc := 
        (temp_65) ;;
      st_55 ← get st_55_loc ;;
      
      @pkg_core_definition.ret (state_t) ( (st_55)) } : code (fset (
          path.sort leb [ st_55_loc ; constants_52_loc])) [interface] _)).
Fail Next Obligation.


Program Definition chacha20_key_block
  (state_68 : state_t)
  : code (fset (
      path.sort leb [ state_42_loc ; state_2_loc ; st_37_loc])) [interface] (
    @ct (block_t)) :=
  (({code  temp_67 ←
        (secret (@repr U32 0)) ;;
      let temp_67 : int32 :=
        (temp_67) in
       temp_69 ←
        (chacha20_core (temp_67) (state_68)) ;;
      let state_70 : state_t :=
        (temp_69) in
       temp_71 ←
        (array_to_le_bytes (state_70)) ;;
       temp_72 ←
        (array_from_seq (64) (temp_71)) ;;
      @pkg_core_definition.ret (block_t) ( (temp_72)) } : code (fset (
          path.sort leb [ state_42_loc ; state_2_loc ; st_37_loc])) [interface] _)).
Fail Next Obligation.


Program Definition chacha20_key_block0
  (key_73 : cha_cha_key_t)
  (iv_74 : cha_cha_iv_t)
  : code (fset (
      path.sort leb [ state_42_loc ; st_37_loc ; constants_52_loc ; state_2_loc ; st_55_loc])) [interface] (
    @ct (block_t)) :=
  (({code  temp_75 ←
        (secret (@repr U32 0)) ;;
      let temp_75 : int32 :=
        (temp_75) in
       temp_76 ←
        (chacha20_init (key_73) (iv_74) (temp_75)) ;;
      let state_77 : state_t :=
        (temp_76) in
       temp_78 ←
        (chacha20_key_block (state_77)) ;;
      @pkg_core_definition.ret (block_t) ( (temp_78)) } : code (fset (
          path.sort leb [ state_42_loc ; st_37_loc ; constants_52_loc ; state_2_loc ; st_55_loc])) [interface] _)).
Fail Next Obligation.


Program Definition chacha20_encrypt_block
  (st0_80 : state_t)
  (ctr_79 : uint32)
  (plain_82 : block_t)
  : code (fset (
      path.sort leb [ state_42_loc ; state_2_loc ; st_37_loc])) [interface] (
    @ct (block_t)) :=
  (({code  temp_81 ←
        (chacha20_core (ctr_79) (st0_80)) ;;
      let st_86 : state_t :=
        (temp_81) in
       temp_83 ←
        (array_to_le_uint32s (plain_82)) ;;
       temp_84 ←
        (array_from_seq (16) (temp_83)) ;;
      let pl_85 : state_t :=
        (temp_84) in
      let st_87 : state_t :=
        ((pl_85) array_xor (st_86)) in
       temp_88 ←
        (array_to_le_bytes (st_87)) ;;
       temp_89 ←
        (array_from_seq (64) (temp_88)) ;;
      @pkg_core_definition.ret (block_t) ( (temp_89)) } : code (fset (
          path.sort leb [ state_42_loc ; state_2_loc ; st_37_loc])) [interface] _)).
Fail Next Obligation.

Definition b_91_loc : Location :=
  (block_t : choice_type ; 99%nat).
Program Definition chacha20_encrypt_last
  (st0_94 : state_t)
  (ctr_95 : uint32)
  (plain_92 : byte_seq)
  : code (fset (
      path.sort leb [ st_37_loc ; b_91_loc ; state_42_loc ; state_2_loc])) [interface] (
    @ct (byte_seq)) :=
  (({code  temp_90 ←
        (array_new_ (default) (64)) ;;
      #put b_91_loc := 
        (temp_90) ;;
      b_91 ← get b_91_loc ;;
      let b_91 : block_t :=
        (b_91) in
       temp_93 ←
        (array_update (b_91) (usize 0) (plain_92)) ;;
      b_91 ← get b_91_loc ;;
      
      #put b_91_loc := 
        (temp_93) ;;
      b_91 ← get b_91_loc ;;
      
       temp_96 ←
        (chacha20_encrypt_block (st0_94) (ctr_95) (b_91)) ;;
      b_91 ← get b_91_loc ;;
      
      #put b_91_loc := 
        (temp_96) ;;
      b_91 ← get b_91_loc ;;
      
       temp_97 ←
        (seq_len (plain_92)) ;;
       temp_98 ←
        (array_slice (b_91) (usize 0) (temp_97)) ;;
      @pkg_core_definition.ret (seq uint8) ( (temp_98)) } : code (fset (
          path.sort leb [ st_37_loc ; b_91_loc ; state_42_loc ; state_2_loc])) [interface] _)).
Fail Next Obligation.

Definition blocks_out_112_loc : Location :=
  (seq uint8 : choice_type ; 123%nat).
Program Definition chacha20_update
  (st0_107 : state_t)
  (m_100 : byte_seq)
  : code (fset (
      path.sort leb [ b_91_loc ; state_2_loc ; state_42_loc ; st_37_loc ; blocks_out_112_loc])) [interface] (
    @ct (byte_seq)) :=
  (({code  temp_101 ←
        (seq_len (m_100)) ;;
       temp_102 ←
        (seq_new_ (default) (temp_101)) ;;
      #put blocks_out_112_loc := 
        (temp_102) ;;
      blocks_out_112 ← get blocks_out_112_loc ;;
      let blocks_out_112 : seq uint8 :=
        (blocks_out_112) in
       temp_103 ←
        (seq_num_exact_chunks (m_100) (usize 64)) ;;
      let n_blocks_104 : uint_size :=
        (temp_103) in
       blocks_out_112 ←
        (foldi (usize 0) (n_blocks_104) (fun i_105 (blocks_out_112 : _) =>
            ({code  temp_106 ←
                (seq_get_exact_chunk (m_100) (usize 64) (i_105)) ;;
              let msg_block_109 : seq uint8 :=
                (temp_106) in
               temp_108 ←
                (secret (pub_u32 (i_105))) ;;
              let temp_108 : int32 :=
                (temp_108) in
               temp_110 ←
                (array_from_seq (64) (msg_block_109)) ;;
               temp_111 ←
                (chacha20_encrypt_block (st0_107) (temp_108) (temp_110)) ;;
              let b_113 : block_t :=
                (temp_111) in
               temp_114 ←
                (array_to_seq (b_113)) ;;
              let temp_114 : seq uint8 :=
                (temp_114) in
               temp_115 ←
                (seq_set_exact_chunk (blocks_out_112) (usize 64) (i_105) (
                    temp_114)) ;;
              blocks_out_112 ← get blocks_out_112_loc ;;
              
              #put blocks_out_112_loc := 
                (temp_115) ;;
              blocks_out_112 ← get blocks_out_112_loc ;;
              
              @pkg_core_definition.ret (_) ( ((blocks_out_112))) } : code (
                fset (
                  path.sort leb [ blocks_out_112_loc ; st_37_loc ; state_2_loc ; state_42_loc])) [interface] _))
          blocks_out_112) ;;
      
       temp_116 ←
        (seq_get_remainder_chunk (m_100) (usize 64)) ;;
      let last_block_117 : seq uint8 :=
        (temp_116) in
       temp_118 ←
        (seq_len (last_block_117)) ;;
       '(blocks_out_112) ←
        (if (temp_118) !=.? (usize 0):bool_ChoiceEquality then ((
              {code  temp_119 ←
                (secret (pub_u32 (n_blocks_104))) ;;
              let temp_119 : int32 :=
                (temp_119) in
               temp_120 ←
                (chacha20_encrypt_last (st0_107) (temp_119) (last_block_117)) ;;
              let b_121 : seq uint8 :=
                (temp_120) in
               temp_122 ←
                (seq_set_chunk (blocks_out_112) (usize 64) (n_blocks_104) (
                    b_121)) ;;
              blocks_out_112 ← get blocks_out_112_loc ;;
              
              #put blocks_out_112_loc := 
                (temp_122) ;;
              blocks_out_112 ← get blocks_out_112_loc ;;
              
              @pkg_core_definition.ret (_) ( ((blocks_out_112))) } : code (
                fset (
                  path.sort leb [ state_42_loc ; blocks_out_112_loc ; st_37_loc ; b_91_loc ; state_2_loc])) [interface] _)) else (
            @pkg_core_definition.ret (_) ( ((blocks_out_112))))) ;;
      
      @pkg_core_definition.ret (seq uint8) ( (blocks_out_112)) } : code (fset (
          path.sort leb [ b_91_loc ; state_2_loc ; state_42_loc ; st_37_loc ; blocks_out_112_loc])) [interface] _)).
Fail Next Obligation.


Program Definition chacha20
  (key_124 : cha_cha_key_t)
  (iv_125 : cha_cha_iv_t)
  (ctr_126 : int32)
  (m_130 : byte_seq)
  : code (fset (
      path.sort leb [ state_42_loc ; constants_52_loc ; st_55_loc ; state_2_loc ; b_91_loc ; blocks_out_112_loc ; st_37_loc])) [interface] (
    @ct (byte_seq)) :=
  (({code  temp_127 ←
        (secret (ctr_126)) ;;
      let temp_127 : int32 :=
        (temp_127) in
       temp_128 ←
        (chacha20_init (key_124) (iv_125) (temp_127)) ;;
      let state_129 : state_t :=
        (temp_128) in
       temp_131 ←
        (chacha20_update (state_129) (m_130)) ;;
      @pkg_core_definition.ret (byte_seq) ( (temp_131)) } : code (fset (
          path.sort leb [ state_42_loc ; constants_52_loc ; st_55_loc ; state_2_loc ; b_91_loc ; blocks_out_112_loc ; st_37_loc])) [interface] _)).
Fail Next Obligation.

