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
Require Import Hacspec_Lib.

Definition state_t  :=
  ( nseq (uint32) (usize 12)).

Definition state_idx_t  :=
  (nat_mod (usize 12)).
Definition uint_size_in_state_idx_t(n : uint_size) : state_idx_t := int_in_nat_mod n.
Coercion uint_size_in_state_idx_t : uint_size >-> state_idx_t.


Notation "'swap_inp'" := (
  state_t '× state_idx_t '× state_idx_t : choice_type) (in custom pack_type at level 2).
Notation "'swap_out'" := (
  state_t : choice_type) (in custom pack_type at level 2).
Definition SWAP : nat :=
  (6086).
Program Definition swap
   : package (fset.fset0) [interface] [interface
  #val #[ SWAP ] : swap_inp → swap_out ] :=
  ([package #def #[ SWAP ] (temp_inp : swap_inp) : swap_out { 
    let '(
      s_6080 , i_6078 , j_6082) := temp_inp : state_t '× state_idx_t '× state_idx_t in
    ({ code  '(tmp_6085 : uint32) ←
        ( temp_6081 ←
            (array_index (s_6080) (i_6078)) ;;
          ret (temp_6081)) ;;
       '(s_6080 : state_t) ←
        ( temp_6084 ←
            (array_index (s_6080) (j_6082)) ;;
          ret (array_upd s_6080 (i_6078) (temp_6084))) ;;
      
       '(s_6080 : state_t) ←
        (ret (array_upd s_6080 (j_6082) (tmp_6085))) ;;
      
      @ret (state_t) (s_6080) } : code (fset.fset0) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_swap : package _ _ _ :=
  (swap).
Fail Next Obligation.


Notation "'gimli_round_inp'" := (
  state_t '× int32 : choice_type) (in custom pack_type at level 2).
Notation "'gimli_round_out'" := (
  state_t : choice_type) (in custom pack_type at level 2).
Definition GIMLI_ROUND : nat :=
  (6167).
Program Definition gimli_round
   : package (fset.fset0) [interface #val #[ SWAP ] : swap_inp → swap_out
  ] [interface #val #[ GIMLI_ROUND ] : gimli_round_inp → gimli_round_out ] :=
  (
    [package #def #[ GIMLI_ROUND ] (temp_inp : gimli_round_inp) : gimli_round_out { 
    let '(s_6089 , r_6136) := temp_inp : state_t '× int32 in
    #import {sig #[ SWAP ] : swap_inp → swap_out } as swap ;;
    let swap := fun x_0 x_1 x_2 => swap (x_0,x_1,x_2) in
    ({ code  '(s_6089 : (state_t)) ←
        (foldi' (usize 0) (usize 4) s_6089 (L2 := fset.fset0) (I2 := [interface
              #val #[ SWAP ] : swap_inp → swap_out
              ]) (H_loc_incl := _) (H_opsig_incl := _) (fun col_6087 s_6089 =>
            ({ code  '(x_6105 : uint32) ←
                ( temp_6090 ←
                    (array_index (s_6089) (col_6087)) ;;
                   temp_6092 ←
                    (uint32_rotate_left (temp_6090) (usize 24)) ;;
                  ret (temp_6092)) ;;
               '(y_6111 : uint32) ←
                ( '(temp_6094 : uint_size) ←
                    ((col_6087) .+ (usize 4)) ;;
                   temp_6096 ←
                    (array_index (s_6089) (temp_6094)) ;;
                   temp_6098 ←
                    (uint32_rotate_left (temp_6096) (usize 9)) ;;
                  ret (temp_6098)) ;;
               '(z_6106 : uint32) ←
                ( '(temp_6100 : uint_size) ←
                    ((col_6087) .+ (usize 8)) ;;
                   temp_6102 ←
                    (array_index (s_6089) (temp_6100)) ;;
                  ret (temp_6102)) ;;
               '(s_6089 : state_t) ←
                ( '(temp_6104 : uint_size) ←
                    ((col_6087) .+ (usize 8)) ;;
                   temp_6108 ←
                    ((z_6106) shift_left (usize 1)) ;;
                   temp_6110 ←
                    ((x_6105) .^ (temp_6108)) ;;
                   temp_6113 ←
                    ((y_6111) .& (z_6106)) ;;
                   temp_6115 ←
                    ((temp_6113) shift_left (usize 2)) ;;
                   temp_6117 ←
                    ((temp_6110) .^ (temp_6115)) ;;
                  ret (array_upd s_6089 (temp_6104) (temp_6117))) ;;
              
               '(s_6089 : state_t) ←
                ( '(temp_6119 : uint_size) ←
                    ((col_6087) .+ (usize 4)) ;;
                   temp_6121 ←
                    ((y_6111) .^ (x_6105)) ;;
                   temp_6123 ←
                    ((x_6105) .| (z_6106)) ;;
                   temp_6125 ←
                    ((temp_6123) shift_left (usize 1)) ;;
                   temp_6127 ←
                    ((temp_6121) .^ (temp_6125)) ;;
                  ret (array_upd s_6089 (temp_6119) (temp_6127))) ;;
              
               '(s_6089 : state_t) ←
                ( temp_6129 ←
                    ((z_6106) .^ (y_6111)) ;;
                   temp_6131 ←
                    ((x_6105) .& (y_6111)) ;;
                   temp_6133 ←
                    ((temp_6131) shift_left (usize 3)) ;;
                   temp_6135 ←
                    ((temp_6129) .^ (temp_6133)) ;;
                  ret (array_upd s_6089 (col_6087) (temp_6135))) ;;
              
              @ret ((state_t)) (s_6089) } : code (
                fset.fset0) [interface] _))) ;;
      
       temp_6138 ←
        ((r_6136) .& (@repr U32 3)) ;;
       '(temp_6140 : bool_ChoiceEquality) ←
        ((temp_6138) =.? (@repr U32 0)) ;;
       '(s_6089 : (state_t)) ←
        (if temp_6140:bool_ChoiceEquality
          then (*not state*) (let temp_then :=  '(s_6089 : state_t) ←
                (( '(temp_6142 : state_t) ←
                      (swap (s_6089) (usize 0) (usize 1)) ;;
                    ret (temp_6142))) ;;
              #put s_6089_loc := s_6089 ;;
            
             '(s_6089 : state_t) ←
                (( '(temp_6144 : state_t) ←
                      (swap (s_6089) (usize 2) (usize 3)) ;;
                    ret (temp_6144))) ;;
              #put s_6089_loc := s_6089 ;;
            
            @ret ((state_t)) (s_6089) in
            ({ code temp_then } : code (fset.fset0) [interface
              #val #[ SWAP ] : swap_inp → swap_out ] _))
          else @ret ((state_t)) (s_6089)) ;;
      
       temp_6146 ←
        ((r_6136) .& (@repr U32 3)) ;;
       '(temp_6148 : bool_ChoiceEquality) ←
        ((temp_6146) =.? (@repr U32 2)) ;;
       '(s_6089 : (state_t)) ←
        (if temp_6148:bool_ChoiceEquality
          then (*not state*) (let temp_then :=  '(s_6089 : state_t) ←
                (( '(temp_6150 : state_t) ←
                      (swap (s_6089) (usize 0) (usize 2)) ;;
                    ret (temp_6150))) ;;
              #put s_6089_loc := s_6089 ;;
            
             '(s_6089 : state_t) ←
                (( '(temp_6152 : state_t) ←
                      (swap (s_6089) (usize 1) (usize 3)) ;;
                    ret (temp_6152))) ;;
              #put s_6089_loc := s_6089 ;;
            
            @ret ((state_t)) (s_6089) in
            ({ code temp_then } : code (fset.fset0) [interface
              #val #[ SWAP ] : swap_inp → swap_out ] _))
          else @ret ((state_t)) (s_6089)) ;;
      
       temp_6154 ←
        ((r_6136) .& (@repr U32 3)) ;;
       '(temp_6156 : bool_ChoiceEquality) ←
        ((temp_6154) =.? (@repr U32 0)) ;;
       '(s_6089 : (state_t)) ←
        (if temp_6156:bool_ChoiceEquality
          then (*not state*) (let temp_then :=  '(s_6089 : state_t) ←
              ( temp_6158 ←
                  (array_index (s_6089) (usize 0)) ;;
                 '(temp_6160 : int32) ←
                  (secret (@repr U32 2654435584)) ;;
                 '(temp_6162 : int32) ←
                  (secret (r_6136)) ;;
                 temp_6164 ←
                  ((temp_6160) .| (temp_6162)) ;;
                 temp_6166 ←
                  ((temp_6158) .^ (temp_6164)) ;;
                ret (array_upd s_6089 (usize 0) (temp_6166))) ;;
            
            @ret ((state_t)) (s_6089) in
            ({ code temp_then } : code (fset.fset0) [interface] _))
          else @ret ((state_t)) (s_6089)) ;;
      
      @ret (state_t) (s_6089) } : code (fset.fset0) [interface
      #val #[ SWAP ] : swap_inp → swap_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_gimli_round : package _ _ _ :=
  (seq_link gimli_round link_rest(package_swap)).
Fail Next Obligation.


Notation "'gimli_inp'" := (
  state_t : choice_type) (in custom pack_type at level 2).
Notation "'gimli_out'" := (
  state_t : choice_type) (in custom pack_type at level 2).
Definition GIMLI : nat :=
  (6175).
Program Definition gimli
   : package (fset.fset0) [interface
  #val #[ GIMLI_ROUND ] : gimli_round_inp → gimli_round_out ] [interface
  #val #[ GIMLI ] : gimli_inp → gimli_out ] :=
  ([package #def #[ GIMLI ] (temp_inp : gimli_inp) : gimli_out { 
    let '(s_6171) := temp_inp : state_t in
    #import {sig #[ GIMLI_ROUND ] : gimli_round_inp → gimli_round_out } as gimli_round ;;
    let gimli_round := fun x_0 x_1 => gimli_round (x_0,x_1) in
    ({ code  '(s_6171 : (state_t)) ←
        (foldi' (usize 0) (usize 24) s_6171 (L2 := fset.fset0) (I2 := [interface
              #val #[ GIMLI_ROUND ] : gimli_round_inp → gimli_round_out
              ]) (H_loc_incl := _) (H_opsig_incl := _) (fun rnd_6168 s_6171 =>
            ({ code  '(rnd_6172 : int32) ←
                ( '(temp_6170 : uint_size) ←
                    ((usize 24) .- (rnd_6168)) ;;
                  ret (pub_u32 (temp_6170))) ;;
               '(s_6171 : state_t) ←
                  (( '(temp_6174 : state_t) ←
                        (gimli_round (s_6171) (rnd_6172)) ;;
                      ret (temp_6174))) ;;
                #put s_6171_loc := s_6171 ;;
              
              @ret ((state_t)) (s_6171) } : code (fset.fset0) [interface
              #val #[ GIMLI_ROUND ] : gimli_round_inp → gimli_round_out
              ] _))) ;;
      
      @ret (state_t) (s_6171) } : code (fset.fset0) [interface
      #val #[ GIMLI_ROUND ] : gimli_round_inp → gimli_round_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_gimli : package _ _ _ :=
  (seq_link gimli link_rest(package_gimli_round)).
Fail Next Obligation.

Definition block_t  :=
  ( nseq (uint8) (usize 16)).

Definition digest_t  :=
  ( nseq (uint8) (usize 32)).


Notation "'absorb_block_inp'" := (
  block_t '× state_t : choice_type) (in custom pack_type at level 2).
Notation "'absorb_block_out'" := (
  state_t : choice_type) (in custom pack_type at level 2).
Definition ABSORB_BLOCK : nat :=
  (6207).
Program Definition absorb_block
   : package (fset.fset0) [interface #val #[ GIMLI ] : gimli_inp → gimli_out
  ] [interface #val #[ ABSORB_BLOCK ] : absorb_block_inp → absorb_block_out
  ] :=
  (
    [package #def #[ ABSORB_BLOCK ] (temp_inp : absorb_block_inp) : absorb_block_out { 
    let '(input_block_6176 , s_6180) := temp_inp : block_t '× state_t in
    #import {sig #[ GIMLI ] : gimli_inp → gimli_out } as gimli ;;
    let gimli := fun x_0 => gimli (x_0) in
    ({ code  '(input_bytes_6183 : seq uint32) ←
        ( temp_6178 ←
            (array_to_le_uint32s (input_block_6176)) ;;
          ret (temp_6178)) ;;
       '(s_6180 : state_t) ←
        ( temp_6181 ←
            (array_index (s_6180) (usize 0)) ;;
           '(temp_6184 : uint32) ←
            (seq_index (input_bytes_6183) (usize 0)) ;;
           temp_6186 ←
            ((temp_6181) .^ (temp_6184)) ;;
          ret (array_upd s_6180 (usize 0) (temp_6186))) ;;
      
       '(s_6180 : state_t) ←
        ( temp_6188 ←
            (array_index (s_6180) (usize 1)) ;;
           '(temp_6190 : uint32) ←
            (seq_index (input_bytes_6183) (usize 1)) ;;
           temp_6192 ←
            ((temp_6188) .^ (temp_6190)) ;;
          ret (array_upd s_6180 (usize 1) (temp_6192))) ;;
      
       '(s_6180 : state_t) ←
        ( temp_6194 ←
            (array_index (s_6180) (usize 2)) ;;
           '(temp_6196 : uint32) ←
            (seq_index (input_bytes_6183) (usize 2)) ;;
           temp_6198 ←
            ((temp_6194) .^ (temp_6196)) ;;
          ret (array_upd s_6180 (usize 2) (temp_6198))) ;;
      
       '(s_6180 : state_t) ←
        ( temp_6200 ←
            (array_index (s_6180) (usize 3)) ;;
           '(temp_6202 : uint32) ←
            (seq_index (input_bytes_6183) (usize 3)) ;;
           temp_6204 ←
            ((temp_6200) .^ (temp_6202)) ;;
          ret (array_upd s_6180 (usize 3) (temp_6204))) ;;
      
       '(temp_6206 : state_t) ←
        (gimli (s_6180)) ;;
      @ret (state_t) (temp_6206) } : code (fset.fset0) [interface
      #val #[ GIMLI ] : gimli_inp → gimli_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_absorb_block : package _ _ _ :=
  (seq_link absorb_block link_rest(package_gimli)).
Fail Next Obligation.

Definition block_6240_loc : ChoiceEqualityLocation :=
  ((block_t ; 6241%nat)).
Notation "'squeeze_block_inp'" := (
  state_t : choice_type) (in custom pack_type at level 2).
Notation "'squeeze_block_out'" := (
  block_t : choice_type) (in custom pack_type at level 2).
Definition SQUEEZE_BLOCK : nat :=
  (6242).
Program Definition squeeze_block
   : package (CEfset ([block_6240_loc])) [interface] [interface
  #val #[ SQUEEZE_BLOCK ] : squeeze_block_inp → squeeze_block_out ] :=
  (
    [package #def #[ SQUEEZE_BLOCK ] (temp_inp : squeeze_block_inp) : squeeze_block_out { 
    let '(s_6212) := temp_inp : state_t in
    ({ code  '(block_6240 : block_t) ←
          ( '(temp_6209 : block_t) ←
              (array_new_ (default : uint8) (16)) ;;
            ret (temp_6209)) ;;
        #put block_6240_loc := block_6240 ;;
       '(block_6240 : (block_t)) ←
        (foldi' (usize 0) (usize 4) block_6240 (L2 := CEfset (
                [block_6240_loc])) (
              I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (fun i_6210 block_6240 =>
            ({ code  '(s_i_6214 : uint32) ←
                ( temp_6213 ←
                    (array_index (s_6212) (i_6210)) ;;
                  ret (temp_6213)) ;;
               '(s_i_bytes_6220 : seq uint8) ←
                ( temp_6216 ←
                    (uint32_to_le_bytes (s_i_6214)) ;;
                  ret (temp_6216)) ;;
               '(block_6240 : block_t) ←
                ( '(temp_6218 : uint_size) ←
                    ((usize 4) .* (i_6210)) ;;
                   '(temp_6221 : uint8) ←
                    (seq_index (s_i_bytes_6220) (usize 0)) ;;
                  ret (array_upd block_6240 (temp_6218) (temp_6221))) ;;
              
               '(block_6240 : block_t) ←
                ( '(temp_6223 : uint_size) ←
                    ((usize 4) .* (i_6210)) ;;
                   '(temp_6225 : uint_size) ←
                    ((temp_6223) .+ (usize 1)) ;;
                   '(temp_6227 : uint8) ←
                    (seq_index (s_i_bytes_6220) (usize 1)) ;;
                  ret (array_upd block_6240 (temp_6225) (temp_6227))) ;;
              
               '(block_6240 : block_t) ←
                ( '(temp_6229 : uint_size) ←
                    ((usize 4) .* (i_6210)) ;;
                   '(temp_6231 : uint_size) ←
                    ((temp_6229) .+ (usize 2)) ;;
                   '(temp_6233 : uint8) ←
                    (seq_index (s_i_bytes_6220) (usize 2)) ;;
                  ret (array_upd block_6240 (temp_6231) (temp_6233))) ;;
              
               '(block_6240 : block_t) ←
                ( '(temp_6235 : uint_size) ←
                    ((usize 4) .* (i_6210)) ;;
                   '(temp_6237 : uint_size) ←
                    ((temp_6235) .+ (usize 3)) ;;
                   '(temp_6239 : uint8) ←
                    (seq_index (s_i_bytes_6220) (usize 3)) ;;
                  ret (array_upd block_6240 (temp_6237) (temp_6239))) ;;
              
              @ret ((block_t)) (block_6240) } : code (CEfset (
                  [block_6240_loc])) [interface] _))) ;;
      
      @ret (block_t) (block_6240) } : code (CEfset (
          [block_6240_loc])) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_squeeze_block : package _ _ _ :=
  (squeeze_block).
Fail Next Obligation.

Definition input_block_padded_6278_loc : ChoiceEqualityLocation :=
  ((block_t ; 6281%nat)).
Notation "'gimli_hash_state_inp'" := (
  byte_seq '× state_t : choice_type) (in custom pack_type at level 2).
Notation "'gimli_hash_state_out'" := (
  state_t : choice_type) (in custom pack_type at level 2).
Definition GIMLI_HASH_STATE : nat :=
  (6282).
Program Definition gimli_hash_state
   : package (CEfset ([input_block_padded_6278_loc])) [interface
  #val #[ ABSORB_BLOCK ] : absorb_block_inp → absorb_block_out ] [interface
  #val #[ GIMLI_HASH_STATE ] : gimli_hash_state_inp → gimli_hash_state_out
  ] :=
  (
    [package #def #[ GIMLI_HASH_STATE ] (temp_inp : gimli_hash_state_inp) : gimli_hash_state_out { 
    let '(input_6245 , s_6257) := temp_inp : byte_seq '× state_t in
    #import {sig #[ ABSORB_BLOCK ] : absorb_block_inp → absorb_block_out } as absorb_block ;;
    let absorb_block := fun x_0 x_1 => absorb_block (x_0,x_1) in
    ({ code  '(rate_6246 : uint_size) ←
        ( '(temp_6244 : uint_size) ←
            (array_length ) ;;
          ret (temp_6244)) ;;
       '(chunks_6249 : uint_size) ←
        ( '(temp_6248 : uint_size) ←
            (seq_num_exact_chunks (input_6245) (rate_6246)) ;;
          ret (temp_6248)) ;;
       '(s_6257 : (state_t)) ←
        (foldi' (usize 0) (chunks_6249) s_6257 (L2 := CEfset (
                [input_block_padded_6278_loc])) (I2 := [interface
              #val #[ ABSORB_BLOCK ] : absorb_block_inp → absorb_block_out
              ]) (H_loc_incl := _) (H_opsig_incl := _) (fun i_6250 s_6257 =>
            ({ code  '(input_block_6253 : seq uint8) ←
                ( '(temp_6252 : byte_seq) ←
                    (seq_get_exact_chunk (input_6245) (rate_6246) (i_6250)) ;;
                  ret (temp_6252)) ;;
               '(full_block_6256 : block_t) ←
                ( '(temp_6255 : block_t) ←
                    (array_from_seq (16) (input_block_6253)) ;;
                  ret (temp_6255)) ;;
               '(s_6257 : state_t) ←
                  (( '(temp_6259 : state_t) ←
                        (absorb_block (full_block_6256) (s_6257)) ;;
                      ret (temp_6259))) ;;
                #put s_6257_loc := s_6257 ;;
              
              @ret ((state_t)) (s_6257) } : code (fset.fset0) [interface
              #val #[ ABSORB_BLOCK ] : absorb_block_inp → absorb_block_out
              ] _))) ;;
      
       '(input_block_6265 : seq uint8) ←
        ( '(temp_6261 : byte_seq) ←
            (seq_get_remainder_chunk (input_6245) (rate_6246)) ;;
          ret (temp_6261)) ;;
       '(input_block_padded_6264 : block_t) ←
        ( '(temp_6263 : block_t) ←
            (array_new_ (default : uint8) (16)) ;;
          ret (temp_6263)) ;;
       '(input_block_padded_6278 : block_t) ←
          ( '(temp_6267 : block_t) ←
              (array_update_start (input_block_padded_6264) (
                  input_block_6265)) ;;
            ret (temp_6267)) ;;
        #put input_block_padded_6278_loc := input_block_padded_6278 ;;
       '(input_block_padded_6278 : block_t) ←
        ( '(temp_6269 : uint_size) ←
            (seq_len (input_block_6265)) ;;
           '(temp_6271 : int8) ←
            (secret (@repr U8 1)) ;;
          ret (array_upd input_block_padded_6278 (temp_6269) (temp_6271))) ;;
      
       '(s_6257 : state_t) ←
        ( temp_6273 ←
            (array_index (s_6257) (usize 11)) ;;
           '(temp_6275 : int32) ←
            (secret (@repr U32 16777216)) ;;
           temp_6277 ←
            ((temp_6273) .^ (temp_6275)) ;;
          ret (array_upd s_6257 (usize 11) (temp_6277))) ;;
      
       '(s_6257 : state_t) ←
          (( '(temp_6280 : state_t) ←
                (absorb_block (input_block_padded_6278) (s_6257)) ;;
              ret (temp_6280))) ;;
        #put s_6257_loc := s_6257 ;;
      
      @ret (state_t) (s_6257) } : code (CEfset (
          [input_block_padded_6278_loc])) [interface
      #val #[ ABSORB_BLOCK ] : absorb_block_inp → absorb_block_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_gimli_hash_state : package _ _ _ :=
  (seq_link gimli_hash_state link_rest(package_absorb_block)).
Fail Next Obligation.


Notation "'gimli_hash_inp'" := (
  byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'gimli_hash_out'" := (
  digest_t : choice_type) (in custom pack_type at level 2).
Definition GIMLI_HASH : nat :=
  (6311).
Program Definition gimli_hash
   : package (CEfset ([])) [interface
  #val #[ GIMLI ] : gimli_inp → gimli_out ;
  #val #[ GIMLI_HASH_STATE ] : gimli_hash_state_inp → gimli_hash_state_out ;
  #val #[ SQUEEZE_BLOCK ] : squeeze_block_inp → squeeze_block_out ] [interface
  #val #[ GIMLI_HASH ] : gimli_hash_inp → gimli_hash_out ] :=
  ([package #def #[ GIMLI_HASH ] (temp_inp : gimli_hash_inp) : gimli_hash_out { 
    let '(input_bytes_6285) := temp_inp : byte_seq in
    #import {sig #[ GIMLI ] : gimli_inp → gimli_out } as gimli ;;
    let gimli := fun x_0 => gimli (x_0) in
    #import {sig #[ GIMLI_HASH_STATE ] : gimli_hash_state_inp → gimli_hash_state_out } as gimli_hash_state ;;
    let gimli_hash_state := fun x_0 x_1 => gimli_hash_state (x_0,x_1) in
    #import {sig #[ SQUEEZE_BLOCK ] : squeeze_block_inp → squeeze_block_out } as squeeze_block ;;
    let squeeze_block := fun x_0 => squeeze_block (x_0) in
    ({ code  '(s_6286 : state_t) ←
        ( '(temp_6284 : state_t) ←
            (array_new_ (default : uint32) (12)) ;;
          ret (temp_6284)) ;;
       '(s_6292 : state_t) ←
        ( '(temp_6288 : state_t) ←
            (gimli_hash_state (input_bytes_6285) (s_6286)) ;;
          ret (temp_6288)) ;;
       '(output_6291 : digest_t) ←
        ( '(temp_6290 : digest_t) ←
            (array_new_ (default : uint8) (32)) ;;
          ret (temp_6290)) ;;
       '(output_6301 : digest_t) ←
        ( '(temp_6294 : block_t) ←
            (squeeze_block (s_6292)) ;;
           '(temp_6296 : seq uint8) ←
            (array_to_seq (temp_6294)) ;;
           '(temp_6298 : digest_t) ←
            (array_update_start (output_6291) (temp_6296)) ;;
          ret (temp_6298)) ;;
       '(s_6304 : state_t) ←
        ( '(temp_6300 : state_t) ←
            (gimli (s_6292)) ;;
          ret (temp_6300)) ;;
       '(temp_6303 : uint_size) ←
        (array_length ) ;;
       '(temp_6306 : block_t) ←
        (squeeze_block (s_6304)) ;;
       '(temp_6308 : seq uint8) ←
        (array_to_seq (temp_6306)) ;;
       '(temp_6310 : digest_t) ←
        (array_update (output_6301) (temp_6303) (temp_6308)) ;;
      @ret (digest_t) (temp_6310) } : code (CEfset ([])) [interface
      #val #[ GIMLI ] : gimli_inp → gimli_out ;
      #val #[ GIMLI_HASH_STATE ] : gimli_hash_state_inp → gimli_hash_state_out ;
      #val #[ SQUEEZE_BLOCK ] : squeeze_block_inp → squeeze_block_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_gimli_hash : package _ _ _ :=
  (seq_link gimli_hash link_rest(
      package_gimli,package_gimli_hash_state,package_squeeze_block)).
Fail Next Obligation.

Definition nonce_t  :=
  ( nseq (uint8) (usize 16)).

Definition key_t  :=
  ( nseq (uint8) (usize 32)).

Definition tag_t  :=
  ( nseq (uint8) (usize 16)).


Notation "'process_ad_inp'" := (
  byte_seq '× state_t : choice_type) (in custom pack_type at level 2).
Notation "'process_ad_out'" := (
  state_t : choice_type) (in custom pack_type at level 2).
Definition PROCESS_AD : nat :=
  (6316).
Program Definition process_ad
   : package (CEfset ([])) [interface
  #val #[ GIMLI_HASH_STATE ] : gimli_hash_state_inp → gimli_hash_state_out
  ] [interface #val #[ PROCESS_AD ] : process_ad_inp → process_ad_out ] :=
  ([package #def #[ PROCESS_AD ] (temp_inp : process_ad_inp) : process_ad_out { 
    let '(ad_6312 , s_6313) := temp_inp : byte_seq '× state_t in
    #import {sig #[ GIMLI_HASH_STATE ] : gimli_hash_state_inp → gimli_hash_state_out } as gimli_hash_state ;;
    let gimli_hash_state := fun x_0 x_1 => gimli_hash_state (x_0,x_1) in
    ({ code  '(temp_6315 : state_t) ←
        (gimli_hash_state (ad_6312) (s_6313)) ;;
      @ret (state_t) (temp_6315) } : code (CEfset ([])) [interface
      #val #[ GIMLI_HASH_STATE ] : gimli_hash_state_inp → gimli_hash_state_out
      ] _)
    }]).
Fail Next Obligation.
Program Definition package_process_ad : package _ _ _ :=
  (seq_link process_ad link_rest(package_gimli_hash_state)).
Fail Next Obligation.

Definition ciphertext_6337_loc : ChoiceEqualityLocation :=
  ((seq uint8 ; 6385%nat)).
Definition msg_block_padded_6360_loc : ChoiceEqualityLocation :=
  ((block_t ; 6386%nat)).
Notation "'process_msg_inp'" := (
  byte_seq '× state_t : choice_type) (in custom pack_type at level 2).
Notation "'process_msg_out'" := ((state_t '× byte_seq
  ) : choice_type) (in custom pack_type at level 2).
Definition PROCESS_MSG : nat :=
  (6387).
Program Definition process_msg
   : package (CEfset (
      [ciphertext_6337_loc ; msg_block_padded_6360_loc])) [interface
  #val #[ ABSORB_BLOCK ] : absorb_block_inp → absorb_block_out ;
  #val #[ SQUEEZE_BLOCK ] : squeeze_block_inp → squeeze_block_out ] [interface
  #val #[ PROCESS_MSG ] : process_msg_inp → process_msg_out ] :=
  (
    [package #def #[ PROCESS_MSG ] (temp_inp : process_msg_inp) : process_msg_out { 
    let '(message_6317 , s_6328) := temp_inp : byte_seq '× state_t in
    #import {sig #[ ABSORB_BLOCK ] : absorb_block_inp → absorb_block_out } as absorb_block ;;
    let absorb_block := fun x_0 x_1 => absorb_block (x_0,x_1) in
    #import {sig #[ SQUEEZE_BLOCK ] : squeeze_block_inp → squeeze_block_out } as squeeze_block ;;
    let squeeze_block := fun x_0 => squeeze_block (x_0) in
    ({ code  '(ciphertext_6337 : seq uint8) ←
          ( '(temp_6319 : uint_size) ←
              (seq_len (message_6317)) ;;
             temp_6321 ←
              (seq_new_ (default : uint8) (temp_6319)) ;;
            ret (temp_6321)) ;;
        #put ciphertext_6337_loc := ciphertext_6337 ;;
       '(rate_6324 : uint_size) ←
        ( '(temp_6323 : uint_size) ←
            (array_length ) ;;
          ret (temp_6323)) ;;
       '(num_chunks_6327 : uint_size) ←
        ( '(temp_6326 : uint_size) ←
            (seq_num_exact_chunks (message_6317) (rate_6324)) ;;
          ret (temp_6326)) ;;
       temp_6384 ←
        (foldi' (usize 0) (num_chunks_6327) prod_ce(s_6328, ciphertext_6337) (
              L2 := CEfset (
                [ciphertext_6337_loc ; msg_block_padded_6360_loc])) (
              I2 := [interface
              #val #[ ABSORB_BLOCK ] : absorb_block_inp → absorb_block_out ;
              #val #[ SQUEEZE_BLOCK ] : squeeze_block_inp → squeeze_block_out
              ]) (H_loc_incl := _) (H_opsig_incl := _) (fun i_6331 '(
              s_6328,
              ciphertext_6337
            ) =>
            ({ code  '(key_block_6339 : block_t) ←
                ( '(temp_6330 : block_t) ←
                    (squeeze_block (s_6328)) ;;
                  ret (temp_6330)) ;;
               '(msg_block_6334 : seq uint8) ←
                ( '(temp_6333 : byte_seq) ←
                    (seq_get_exact_chunk (message_6317) (rate_6324) (i_6331)) ;;
                  ret (temp_6333)) ;;
               '(msg_block_6338 : block_t) ←
                ( '(temp_6336 : block_t) ←
                    (array_from_seq (16) (msg_block_6334)) ;;
                  ret (temp_6336)) ;;
               '(ciphertext_6337 : seq uint8) ←
                  (( temp_6341 ←
                        ((msg_block_6338) array_xor (key_block_6339)) ;;
                       '(temp_6343 : seq uint8) ←
                        (array_to_seq (temp_6341)) ;;
                       '(temp_6345 : seq uint8) ←
                        (seq_set_exact_chunk (ciphertext_6337) (rate_6324) (
                            i_6331) (temp_6343)) ;;
                      ret (temp_6345))) ;;
                #put ciphertext_6337_loc := ciphertext_6337 ;;
              
               '(s_6328 : state_t) ←
                  (( '(temp_6347 : state_t) ←
                        (absorb_block (msg_block_6338) (s_6328)) ;;
                      ret (temp_6347))) ;;
                #put s_6328_loc := s_6328 ;;
              
              @ret ((state_t '× seq uint8)) (prod_ce(s_6328, ciphertext_6337
                )) } : code (CEfset ([ciphertext_6337_loc])) [interface
              #val #[ ABSORB_BLOCK ] : absorb_block_inp → absorb_block_out ;
              #val #[ SQUEEZE_BLOCK ] : squeeze_block_inp → squeeze_block_out
              ] _))) ;;
      let '(s_6328, ciphertext_6337) :=
        (temp_6384) : (state_t '× seq uint8) in
      
       '(key_block_6361 : block_t) ←
        ( '(temp_6349 : block_t) ←
            (squeeze_block (s_6328)) ;;
          ret (temp_6349)) ;;
       '(last_block_6352 : seq uint8) ←
        ( '(temp_6351 : byte_seq) ←
            (seq_get_remainder_chunk (message_6317) (rate_6324)) ;;
          ret (temp_6351)) ;;
       '(block_len_6364 : uint_size) ←
        ( '(temp_6354 : uint_size) ←
            (seq_len (last_block_6352)) ;;
          ret (temp_6354)) ;;
       '(msg_block_padded_6357 : block_t) ←
        ( '(temp_6356 : block_t) ←
            (array_new_ (default : uint8) (16)) ;;
          ret (temp_6356)) ;;
       '(msg_block_padded_6360 : block_t) ←
          ( '(temp_6359 : block_t) ←
              (array_update_start (msg_block_padded_6357) (last_block_6352)) ;;
            ret (temp_6359)) ;;
        #put msg_block_padded_6360_loc := msg_block_padded_6360 ;;
       '(ciphertext_6337 : seq uint8) ←
          (( temp_6363 ←
                ((msg_block_padded_6360) array_xor (key_block_6361)) ;;
               '(temp_6366 : seq uint8) ←
                (array_slice_range (temp_6363) (prod_ce(usize 0, block_len_6364
                    ))) ;;
               '(temp_6368 : seq uint8) ←
                (seq_set_chunk (ciphertext_6337) (rate_6324) (num_chunks_6327) (
                    temp_6366)) ;;
              ret (temp_6368))) ;;
        #put ciphertext_6337_loc := ciphertext_6337 ;;
      
       '(msg_block_padded_6360 : block_t) ←
        ( temp_6370 ←
            (array_index (msg_block_padded_6360) (block_len_6364)) ;;
           '(temp_6372 : int8) ←
            (secret (@repr U8 1)) ;;
           temp_6374 ←
            ((temp_6370) .^ (temp_6372)) ;;
          ret (array_upd msg_block_padded_6360 (block_len_6364) (temp_6374))) ;;
      
       '(s_6328 : state_t) ←
        ( temp_6376 ←
            (array_index (s_6328) (usize 11)) ;;
           '(temp_6378 : int32) ←
            (secret (@repr U32 16777216)) ;;
           temp_6380 ←
            ((temp_6376) .^ (temp_6378)) ;;
          ret (array_upd s_6328 (usize 11) (temp_6380))) ;;
      
       '(s_6328 : state_t) ←
          (( '(temp_6382 : state_t) ←
                (absorb_block (msg_block_padded_6360) (s_6328)) ;;
              ret (temp_6382))) ;;
        #put s_6328_loc := s_6328 ;;
      
      @ret ((state_t '× seq uint8)) (prod_ce(s_6328, ciphertext_6337
        )) } : code (CEfset (
          [ciphertext_6337_loc ; msg_block_padded_6360_loc])) [interface
      #val #[ ABSORB_BLOCK ] : absorb_block_inp → absorb_block_out ;
      #val #[ SQUEEZE_BLOCK ] : squeeze_block_inp → squeeze_block_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_process_msg : package _ _ _ :=
  (seq_link process_msg link_rest(package_absorb_block,package_squeeze_block)).
Fail Next Obligation.

Definition msg_block_6449_loc : ChoiceEqualityLocation :=
  ((block_t ; 6465%nat)).
Definition message_6412_loc : ChoiceEqualityLocation :=
  ((seq uint8 ; 6466%nat)).
Notation "'process_ct_inp'" := (
  byte_seq '× state_t : choice_type) (in custom pack_type at level 2).
Notation "'process_ct_out'" := ((state_t '× byte_seq
  ) : choice_type) (in custom pack_type at level 2).
Definition PROCESS_CT : nat :=
  (6467).
Program Definition process_ct
   : package (CEfset ([message_6412_loc ; msg_block_6449_loc])) [interface
  #val #[ ABSORB_BLOCK ] : absorb_block_inp → absorb_block_out ;
  #val #[ SQUEEZE_BLOCK ] : squeeze_block_inp → squeeze_block_out ] [interface
  #val #[ PROCESS_CT ] : process_ct_inp → process_ct_out ] :=
  ([package #def #[ PROCESS_CT ] (temp_inp : process_ct_inp) : process_ct_out { 
    let '(ciphertext_6388 , s_6399) := temp_inp : byte_seq '× state_t in
    #import {sig #[ ABSORB_BLOCK ] : absorb_block_inp → absorb_block_out } as absorb_block ;;
    let absorb_block := fun x_0 x_1 => absorb_block (x_0,x_1) in
    #import {sig #[ SQUEEZE_BLOCK ] : squeeze_block_inp → squeeze_block_out } as squeeze_block ;;
    let squeeze_block := fun x_0 => squeeze_block (x_0) in
    ({ code  '(message_6412 : seq uint8) ←
          ( '(temp_6390 : uint_size) ←
              (seq_len (ciphertext_6388)) ;;
             temp_6392 ←
              (seq_new_ (default : uint8) (temp_6390)) ;;
            ret (temp_6392)) ;;
        #put message_6412_loc := message_6412 ;;
       '(rate_6395 : uint_size) ←
        ( '(temp_6394 : uint_size) ←
            (array_length ) ;;
          ret (temp_6394)) ;;
       '(num_chunks_6398 : uint_size) ←
        ( '(temp_6397 : uint_size) ←
            (seq_num_exact_chunks (ciphertext_6388) (rate_6395)) ;;
          ret (temp_6397)) ;;
       temp_6464 ←
        (foldi' (usize 0) (num_chunks_6398) prod_ce(s_6399, message_6412) (
              L2 := CEfset ([message_6412_loc ; msg_block_6449_loc])) (
              I2 := [interface
              #val #[ ABSORB_BLOCK ] : absorb_block_inp → absorb_block_out ;
              #val #[ SQUEEZE_BLOCK ] : squeeze_block_inp → squeeze_block_out
              ]) (H_loc_incl := _) (H_opsig_incl := _) (fun i_6402 '(
              s_6399,
              message_6412
            ) =>
            ({ code  '(key_block_6409 : block_t) ←
                ( '(temp_6401 : block_t) ←
                    (squeeze_block (s_6399)) ;;
                  ret (temp_6401)) ;;
               '(ct_block_6405 : seq uint8) ←
                ( '(temp_6404 : byte_seq) ←
                    (seq_get_exact_chunk (ciphertext_6388) (rate_6395) (
                        i_6402)) ;;
                  ret (temp_6404)) ;;
               '(ct_block_6408 : block_t) ←
                ( '(temp_6407 : block_t) ←
                    (array_from_seq (16) (ct_block_6405)) ;;
                  ret (temp_6407)) ;;
               '(msg_block_6419 : block_t) ←
                ( temp_6411 ←
                    ((ct_block_6408) array_xor (key_block_6409)) ;;
                  ret (temp_6411)) ;;
               '(message_6412 : seq uint8) ←
                  (( temp_6414 ←
                        ((ct_block_6408) array_xor (key_block_6409)) ;;
                       '(temp_6416 : seq uint8) ←
                        (array_to_seq (temp_6414)) ;;
                       '(temp_6418 : seq uint8) ←
                        (seq_set_exact_chunk (message_6412) (rate_6395) (
                            i_6402) (temp_6416)) ;;
                      ret (temp_6418))) ;;
                #put message_6412_loc := message_6412 ;;
              
               '(s_6399 : state_t) ←
                  (( '(temp_6421 : state_t) ←
                        (absorb_block (msg_block_6419) (s_6399)) ;;
                      ret (temp_6421))) ;;
                #put s_6399_loc := s_6399 ;;
              
              @ret ((state_t '× seq uint8)) (prod_ce(s_6399, message_6412
                )) } : code (CEfset ([message_6412_loc])) [interface
              #val #[ ABSORB_BLOCK ] : absorb_block_inp → absorb_block_out ;
              #val #[ SQUEEZE_BLOCK ] : squeeze_block_inp → squeeze_block_out
              ] _))) ;;
      let '(s_6399, message_6412) :=
        (temp_6464) : (state_t '× seq uint8) in
      
       '(key_block_6435 : block_t) ←
        ( '(temp_6423 : block_t) ←
            (squeeze_block (s_6399)) ;;
          ret (temp_6423)) ;;
       '(ct_final_6426 : seq uint8) ←
        ( '(temp_6425 : byte_seq) ←
            (seq_get_remainder_chunk (ciphertext_6388) (rate_6395)) ;;
          ret (temp_6425)) ;;
       '(block_len_6439 : uint_size) ←
        ( '(temp_6428 : uint_size) ←
            (seq_len (ct_final_6426)) ;;
          ret (temp_6428)) ;;
       '(ct_block_padded_6431 : block_t) ←
        ( '(temp_6430 : block_t) ←
            (array_new_ (default : uint8) (16)) ;;
          ret (temp_6430)) ;;
       '(ct_block_padded_6434 : block_t) ←
        ( '(temp_6433 : block_t) ←
            (array_update_start (ct_block_padded_6431) (ct_final_6426)) ;;
          ret (temp_6433)) ;;
       '(msg_block_6438 : block_t) ←
        ( temp_6437 ←
            ((ct_block_padded_6434) array_xor (key_block_6435)) ;;
          ret (temp_6437)) ;;
       '(message_6412 : seq uint8) ←
          (( '(temp_6441 : seq uint8) ←
                (array_slice_range (msg_block_6438) (prod_ce(
                      usize 0,
                      block_len_6439
                    ))) ;;
               '(temp_6443 : seq uint8) ←
                (seq_set_chunk (message_6412) (rate_6395) (num_chunks_6398) (
                    temp_6441)) ;;
              ret (temp_6443))) ;;
        #put message_6412_loc := message_6412 ;;
      
       '(msg_block_6449 : block_t) ←
          ( '(temp_6445 : seq uint8) ←
              (array_to_seq (msg_block_6438)) ;;
             '(temp_6447 : block_t) ←
              (array_from_slice_range (default : uint8) (16) (temp_6445) (
                  prod_ce(usize 0, block_len_6439))) ;;
            ret (temp_6447)) ;;
        #put msg_block_6449_loc := msg_block_6449 ;;
       '(msg_block_6449 : block_t) ←
        ( temp_6450 ←
            (array_index (msg_block_6449) (block_len_6439)) ;;
           '(temp_6452 : int8) ←
            (secret (@repr U8 1)) ;;
           temp_6454 ←
            ((temp_6450) .^ (temp_6452)) ;;
          ret (array_upd msg_block_6449 (block_len_6439) (temp_6454))) ;;
      
       '(s_6399 : state_t) ←
        ( temp_6456 ←
            (array_index (s_6399) (usize 11)) ;;
           '(temp_6458 : int32) ←
            (secret (@repr U32 16777216)) ;;
           temp_6460 ←
            ((temp_6456) .^ (temp_6458)) ;;
          ret (array_upd s_6399 (usize 11) (temp_6460))) ;;
      
       '(s_6399 : state_t) ←
          (( '(temp_6462 : state_t) ←
                (absorb_block (msg_block_6449) (s_6399)) ;;
              ret (temp_6462))) ;;
        #put s_6399_loc := s_6399 ;;
      
      @ret ((state_t '× seq uint8)) (prod_ce(s_6399, message_6412)) } : code (
        CEfset ([message_6412_loc ; msg_block_6449_loc])) [interface
      #val #[ ABSORB_BLOCK ] : absorb_block_inp → absorb_block_out ;
      #val #[ SQUEEZE_BLOCK ] : squeeze_block_inp → squeeze_block_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_process_ct : package _ _ _ :=
  (seq_link process_ct link_rest(package_absorb_block,package_squeeze_block)).
Fail Next Obligation.

Definition uints_6495_loc : ChoiceEqualityLocation :=
  ((seq uint32 ; 6496%nat)).
Notation "'nonce_to_u32s_inp'" := (
  nonce_t : choice_type) (in custom pack_type at level 2).
Notation "'nonce_to_u32s_out'" := (
  seq uint32 : choice_type) (in custom pack_type at level 2).
Definition NONCE_TO_U32S : nat :=
  (6497).
Program Definition nonce_to_u32s
   : package (CEfset ([uints_6495_loc])) [interface] [interface
  #val #[ NONCE_TO_U32S ] : nonce_to_u32s_inp → nonce_to_u32s_out ] :=
  (
    [package #def #[ NONCE_TO_U32S ] (temp_inp : nonce_to_u32s_inp) : nonce_to_u32s_out { 
    let '(nonce_6470) := temp_inp : nonce_t in
    ({ code  '(uints_6495 : seq uint32) ←
          ( temp_6469 ←
              (seq_new_ (default : uint32) (usize 4)) ;;
            ret (temp_6469)) ;;
        #put uints_6495_loc := uints_6495 ;;
       '(uints_6495 : seq uint32) ←
        ( '(temp_6472 : seq uint8) ←
            (array_to_seq (nonce_6470)) ;;
           '(temp_6474 : uint32_word_t) ←
            (array_from_slice_range (default : uint8) (4) (temp_6472) (prod_ce(
                  usize 0,
                  usize 4
                ))) ;;
           '(temp_6476 : int32) ←
            (uint32_from_le_bytes (temp_6474)) ;;
          ret (seq_upd uints_6495 (usize 0) (temp_6476))) ;;
      
       '(uints_6495 : seq uint32) ←
        ( '(temp_6478 : seq uint8) ←
            (array_to_seq (nonce_6470)) ;;
           '(temp_6480 : uint32_word_t) ←
            (array_from_slice_range (default : uint8) (4) (temp_6478) (prod_ce(
                  usize 4,
                  usize 8
                ))) ;;
           '(temp_6482 : int32) ←
            (uint32_from_le_bytes (temp_6480)) ;;
          ret (seq_upd uints_6495 (usize 1) (temp_6482))) ;;
      
       '(uints_6495 : seq uint32) ←
        ( '(temp_6484 : seq uint8) ←
            (array_to_seq (nonce_6470)) ;;
           '(temp_6486 : uint32_word_t) ←
            (array_from_slice_range (default : uint8) (4) (temp_6484) (prod_ce(
                  usize 8,
                  usize 12
                ))) ;;
           '(temp_6488 : int32) ←
            (uint32_from_le_bytes (temp_6486)) ;;
          ret (seq_upd uints_6495 (usize 2) (temp_6488))) ;;
      
       '(uints_6495 : seq uint32) ←
        ( '(temp_6490 : seq uint8) ←
            (array_to_seq (nonce_6470)) ;;
           '(temp_6492 : uint32_word_t) ←
            (array_from_slice_range (default : uint8) (4) (temp_6490) (prod_ce(
                  usize 12,
                  usize 16
                ))) ;;
           '(temp_6494 : int32) ←
            (uint32_from_le_bytes (temp_6492)) ;;
          ret (seq_upd uints_6495 (usize 3) (temp_6494))) ;;
      
      @ret (seq uint32) (uints_6495) } : code (CEfset (
          [uints_6495_loc])) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_nonce_to_u32s : package _ _ _ :=
  (nonce_to_u32s).
Fail Next Obligation.

Definition uints_6549_loc : ChoiceEqualityLocation :=
  ((seq uint32 ; 6550%nat)).
Notation "'key_to_u32s_inp'" := (
  key_t : choice_type) (in custom pack_type at level 2).
Notation "'key_to_u32s_out'" := (
  seq uint32 : choice_type) (in custom pack_type at level 2).
Definition KEY_TO_U32S : nat :=
  (6551).
Program Definition key_to_u32s
   : package (CEfset ([uints_6549_loc])) [interface] [interface
  #val #[ KEY_TO_U32S ] : key_to_u32s_inp → key_to_u32s_out ] :=
  (
    [package #def #[ KEY_TO_U32S ] (temp_inp : key_to_u32s_inp) : key_to_u32s_out { 
    let '(key_6500) := temp_inp : key_t in
    ({ code  '(uints_6549 : seq uint32) ←
          ( temp_6499 ←
              (seq_new_ (default : uint32) (usize 8)) ;;
            ret (temp_6499)) ;;
        #put uints_6549_loc := uints_6549 ;;
       '(uints_6549 : seq uint32) ←
        ( '(temp_6502 : seq uint8) ←
            (array_to_seq (key_6500)) ;;
           '(temp_6504 : uint32_word_t) ←
            (array_from_slice_range (default : uint8) (4) (temp_6502) (prod_ce(
                  usize 0,
                  usize 4
                ))) ;;
           '(temp_6506 : int32) ←
            (uint32_from_le_bytes (temp_6504)) ;;
          ret (seq_upd uints_6549 (usize 0) (temp_6506))) ;;
      
       '(uints_6549 : seq uint32) ←
        ( '(temp_6508 : seq uint8) ←
            (array_to_seq (key_6500)) ;;
           '(temp_6510 : uint32_word_t) ←
            (array_from_slice_range (default : uint8) (4) (temp_6508) (prod_ce(
                  usize 4,
                  usize 8
                ))) ;;
           '(temp_6512 : int32) ←
            (uint32_from_le_bytes (temp_6510)) ;;
          ret (seq_upd uints_6549 (usize 1) (temp_6512))) ;;
      
       '(uints_6549 : seq uint32) ←
        ( '(temp_6514 : seq uint8) ←
            (array_to_seq (key_6500)) ;;
           '(temp_6516 : uint32_word_t) ←
            (array_from_slice_range (default : uint8) (4) (temp_6514) (prod_ce(
                  usize 8,
                  usize 12
                ))) ;;
           '(temp_6518 : int32) ←
            (uint32_from_le_bytes (temp_6516)) ;;
          ret (seq_upd uints_6549 (usize 2) (temp_6518))) ;;
      
       '(uints_6549 : seq uint32) ←
        ( '(temp_6520 : seq uint8) ←
            (array_to_seq (key_6500)) ;;
           '(temp_6522 : uint32_word_t) ←
            (array_from_slice_range (default : uint8) (4) (temp_6520) (prod_ce(
                  usize 12,
                  usize 16
                ))) ;;
           '(temp_6524 : int32) ←
            (uint32_from_le_bytes (temp_6522)) ;;
          ret (seq_upd uints_6549 (usize 3) (temp_6524))) ;;
      
       '(uints_6549 : seq uint32) ←
        ( '(temp_6526 : seq uint8) ←
            (array_to_seq (key_6500)) ;;
           '(temp_6528 : uint32_word_t) ←
            (array_from_slice_range (default : uint8) (4) (temp_6526) (prod_ce(
                  usize 16,
                  usize 20
                ))) ;;
           '(temp_6530 : int32) ←
            (uint32_from_le_bytes (temp_6528)) ;;
          ret (seq_upd uints_6549 (usize 4) (temp_6530))) ;;
      
       '(uints_6549 : seq uint32) ←
        ( '(temp_6532 : seq uint8) ←
            (array_to_seq (key_6500)) ;;
           '(temp_6534 : uint32_word_t) ←
            (array_from_slice_range (default : uint8) (4) (temp_6532) (prod_ce(
                  usize 20,
                  usize 24
                ))) ;;
           '(temp_6536 : int32) ←
            (uint32_from_le_bytes (temp_6534)) ;;
          ret (seq_upd uints_6549 (usize 5) (temp_6536))) ;;
      
       '(uints_6549 : seq uint32) ←
        ( '(temp_6538 : seq uint8) ←
            (array_to_seq (key_6500)) ;;
           '(temp_6540 : uint32_word_t) ←
            (array_from_slice_range (default : uint8) (4) (temp_6538) (prod_ce(
                  usize 24,
                  usize 28
                ))) ;;
           '(temp_6542 : int32) ←
            (uint32_from_le_bytes (temp_6540)) ;;
          ret (seq_upd uints_6549 (usize 6) (temp_6542))) ;;
      
       '(uints_6549 : seq uint32) ←
        ( '(temp_6544 : seq uint8) ←
            (array_to_seq (key_6500)) ;;
           '(temp_6546 : uint32_word_t) ←
            (array_from_slice_range (default : uint8) (4) (temp_6544) (prod_ce(
                  usize 28,
                  usize 32
                ))) ;;
           '(temp_6548 : int32) ←
            (uint32_from_le_bytes (temp_6546)) ;;
          ret (seq_upd uints_6549 (usize 7) (temp_6548))) ;;
      
      @ret (seq uint32) (uints_6549) } : code (CEfset (
          [uints_6549_loc])) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_key_to_u32s : package _ _ _ :=
  (key_to_u32s).
Fail Next Obligation.


Notation "'gimli_aead_encrypt_inp'" := (
  byte_seq '× byte_seq '× nonce_t '× key_t : choice_type) (in custom pack_type at level 2).
Notation "'gimli_aead_encrypt_out'" := ((byte_seq '× tag_t
  ) : choice_type) (in custom pack_type at level 2).
Definition GIMLI_AEAD_ENCRYPT : nat :=
  (6585).
Program Definition gimli_aead_encrypt
   : package (CEfset ([])) [interface
  #val #[ GIMLI ] : gimli_inp → gimli_out ;
  #val #[ KEY_TO_U32S ] : key_to_u32s_inp → key_to_u32s_out ;
  #val #[ NONCE_TO_U32S ] : nonce_to_u32s_inp → nonce_to_u32s_out ;
  #val #[ PROCESS_AD ] : process_ad_inp → process_ad_out ;
  #val #[ PROCESS_MSG ] : process_msg_inp → process_msg_out ;
  #val #[ SQUEEZE_BLOCK ] : squeeze_block_inp → squeeze_block_out ] [interface
  #val #[ GIMLI_AEAD_ENCRYPT ] : gimli_aead_encrypt_inp → gimli_aead_encrypt_out
  ] :=
  (
    [package #def #[ GIMLI_AEAD_ENCRYPT ] (temp_inp : gimli_aead_encrypt_inp) : gimli_aead_encrypt_out { 
    let '(
      message_6569 , ad_6565 , nonce_6552 , key_6555) := temp_inp : byte_seq '× byte_seq '× nonce_t '× key_t in
    #import {sig #[ GIMLI ] : gimli_inp → gimli_out } as gimli ;;
    let gimli := fun x_0 => gimli (x_0) in
    #import {sig #[ KEY_TO_U32S ] : key_to_u32s_inp → key_to_u32s_out } as key_to_u32s ;;
    let key_to_u32s := fun x_0 => key_to_u32s (x_0) in
    #import {sig #[ NONCE_TO_U32S ] : nonce_to_u32s_inp → nonce_to_u32s_out } as nonce_to_u32s ;;
    let nonce_to_u32s := fun x_0 => nonce_to_u32s (x_0) in
    #import {sig #[ PROCESS_AD ] : process_ad_inp → process_ad_out } as process_ad ;;
    let process_ad := fun x_0 x_1 => process_ad (x_0,x_1) in
    #import {sig #[ PROCESS_MSG ] : process_msg_inp → process_msg_out } as process_msg ;;
    let process_msg := fun x_0 x_1 => process_msg (x_0,x_1) in
    #import {sig #[ SQUEEZE_BLOCK ] : squeeze_block_inp → squeeze_block_out } as squeeze_block ;;
    let squeeze_block := fun x_0 => squeeze_block (x_0) in
    ({ code  '(s_6562 : state_t) ←
        ( '(temp_6554 : seq uint32) ←
            (nonce_to_u32s (nonce_6552)) ;;
           '(temp_6557 : seq uint32) ←
            (key_to_u32s (key_6555)) ;;
           '(temp_6559 : seq uint32) ←
            (seq_concat (temp_6554) (temp_6557)) ;;
           '(temp_6561 : state_t) ←
            (array_from_seq (12) (temp_6559)) ;;
          ret (temp_6561)) ;;
       '(s_6566 : state_t) ←
        ( '(temp_6564 : state_t) ←
            (gimli (s_6562)) ;;
          ret (temp_6564)) ;;
       '(s_6570 : state_t) ←
        ( '(temp_6568 : state_t) ←
            (process_ad (ad_6565) (s_6566)) ;;
          ret (temp_6568)) ;;
       temp_6584 ←
        ( '(temp_6572 : (state_t '× byte_seq)) ←
            (process_msg (message_6569) (s_6570)) ;;
          ret (temp_6572)) ;;
      let '(s_6573, ciphertext_6581) :=
        (temp_6584) : (state_t '× byte_seq) in
       '(tag_6576 : block_t) ←
        ( '(temp_6575 : block_t) ←
            (squeeze_block (s_6573)) ;;
          ret (temp_6575)) ;;
       '(tag_6582 : tag_t) ←
        ( '(temp_6578 : seq uint8) ←
            (array_to_seq (tag_6576)) ;;
           '(temp_6580 : tag_t) ←
            (array_from_seq (16) (temp_6578)) ;;
          ret (temp_6580)) ;;
      @ret ((seq uint8 '× tag_t)) (prod_ce(ciphertext_6581, tag_6582
        )) } : code (CEfset ([])) [interface
      #val #[ GIMLI ] : gimli_inp → gimli_out ;
      #val #[ KEY_TO_U32S ] : key_to_u32s_inp → key_to_u32s_out ;
      #val #[ NONCE_TO_U32S ] : nonce_to_u32s_inp → nonce_to_u32s_out ;
      #val #[ PROCESS_AD ] : process_ad_inp → process_ad_out ;
      #val #[ PROCESS_MSG ] : process_msg_inp → process_msg_out ;
      #val #[ SQUEEZE_BLOCK ] : squeeze_block_inp → squeeze_block_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_gimli_aead_encrypt : package _ _ _ :=
  (seq_link gimli_aead_encrypt link_rest(
      package_gimli,package_key_to_u32s,package_nonce_to_u32s,package_process_ad,package_process_msg,package_squeeze_block)).
Fail Next Obligation.

Definition out_6622_loc : ChoiceEqualityLocation :=
  ((seq uint8 ; 6625%nat)).
Notation "'gimli_aead_decrypt_inp'" := (
  byte_seq '× byte_seq '× tag_t '× nonce_t '× key_t : choice_type) (in custom pack_type at level 2).
Notation "'gimli_aead_decrypt_out'" := (
  byte_seq : choice_type) (in custom pack_type at level 2).
Definition GIMLI_AEAD_DECRYPT : nat :=
  (6626).
Program Definition gimli_aead_decrypt
   : package (CEfset ([out_6622_loc])) [interface
  #val #[ GIMLI ] : gimli_inp → gimli_out ;
  #val #[ KEY_TO_U32S ] : key_to_u32s_inp → key_to_u32s_out ;
  #val #[ NONCE_TO_U32S ] : nonce_to_u32s_inp → nonce_to_u32s_out ;
  #val #[ PROCESS_AD ] : process_ad_inp → process_ad_out ;
  #val #[ PROCESS_CT ] : process_ct_inp → process_ct_out ;
  #val #[ SQUEEZE_BLOCK ] : squeeze_block_inp → squeeze_block_out ] [interface
  #val #[ GIMLI_AEAD_DECRYPT ] : gimli_aead_decrypt_inp → gimli_aead_decrypt_out
  ] :=
  (
    [package #def #[ GIMLI_AEAD_DECRYPT ] (temp_inp : gimli_aead_decrypt_inp) : gimli_aead_decrypt_out { 
    let '(
      ciphertext_6603 , ad_6599 , tag_6618 , nonce_6586 , key_6589) := temp_inp : byte_seq '× byte_seq '× tag_t '× nonce_t '× key_t in
    #import {sig #[ GIMLI ] : gimli_inp → gimli_out } as gimli ;;
    let gimli := fun x_0 => gimli (x_0) in
    #import {sig #[ KEY_TO_U32S ] : key_to_u32s_inp → key_to_u32s_out } as key_to_u32s ;;
    let key_to_u32s := fun x_0 => key_to_u32s (x_0) in
    #import {sig #[ NONCE_TO_U32S ] : nonce_to_u32s_inp → nonce_to_u32s_out } as nonce_to_u32s ;;
    let nonce_to_u32s := fun x_0 => nonce_to_u32s (x_0) in
    #import {sig #[ PROCESS_AD ] : process_ad_inp → process_ad_out } as process_ad ;;
    let process_ad := fun x_0 x_1 => process_ad (x_0,x_1) in
    #import {sig #[ PROCESS_CT ] : process_ct_inp → process_ct_out } as process_ct ;;
    let process_ct := fun x_0 x_1 => process_ct (x_0,x_1) in
    #import {sig #[ SQUEEZE_BLOCK ] : squeeze_block_inp → squeeze_block_out } as squeeze_block ;;
    let squeeze_block := fun x_0 => squeeze_block (x_0) in
    ({ code  '(s_6596 : state_t) ←
        ( '(temp_6588 : seq uint32) ←
            (nonce_to_u32s (nonce_6586)) ;;
           '(temp_6591 : seq uint32) ←
            (key_to_u32s (key_6589)) ;;
           '(temp_6593 : seq uint32) ←
            (seq_concat (temp_6588) (temp_6591)) ;;
           '(temp_6595 : state_t) ←
            (array_from_seq (12) (temp_6593)) ;;
          ret (temp_6595)) ;;
       '(s_6600 : state_t) ←
        ( '(temp_6598 : state_t) ←
            (gimli (s_6596)) ;;
          ret (temp_6598)) ;;
       '(s_6604 : state_t) ←
        ( '(temp_6602 : state_t) ←
            (process_ad (ad_6599) (s_6600)) ;;
          ret (temp_6602)) ;;
       temp_6624 ←
        ( '(temp_6606 : (state_t '× byte_seq)) ←
            (process_ct (ciphertext_6603) (s_6604)) ;;
          ret (temp_6606)) ;;
      let '(s_6607, message_6621) :=
        (temp_6624) : (state_t '× byte_seq) in
       '(my_tag_6610 : block_t) ←
        ( '(temp_6609 : block_t) ←
            (squeeze_block (s_6607)) ;;
          ret (temp_6609)) ;;
       '(my_tag_6617 : tag_t) ←
        ( '(temp_6612 : seq uint8) ←
            (array_to_seq (my_tag_6610)) ;;
           '(temp_6614 : tag_t) ←
            (array_from_seq (16) (temp_6612)) ;;
          ret (temp_6614)) ;;
       '(out_6622 : seq uint8) ←
          ( temp_6616 ←
              (seq_new_ (default : uint8) (usize 0)) ;;
            ret (temp_6616)) ;;
        #put out_6622_loc := out_6622 ;;
       temp_6620 ←
        (array_equal (my_tag_6617) (tag_6618)) ;;
       '(out_6622 : (seq uint8)) ←
        (if temp_6620:bool_ChoiceEquality
          then (*not state*) (let temp_then :=  '(out_6622 : seq uint8) ←
                ((ret (message_6621))) ;;
              #put out_6622_loc := out_6622 ;;
            
            @ret ((seq uint8)) (out_6622) in
            ({ code temp_then } : code (CEfset ([out_6622_loc])) [interface] _))
          else @ret ((seq uint8)) (out_6622)) ;;
      
      @ret (seq uint8) (out_6622) } : code (CEfset ([out_6622_loc])) [interface
      #val #[ GIMLI ] : gimli_inp → gimli_out ;
      #val #[ KEY_TO_U32S ] : key_to_u32s_inp → key_to_u32s_out ;
      #val #[ NONCE_TO_U32S ] : nonce_to_u32s_inp → nonce_to_u32s_out ;
      #val #[ PROCESS_AD ] : process_ad_inp → process_ad_out ;
      #val #[ PROCESS_CT ] : process_ct_inp → process_ct_out ;
      #val #[ SQUEEZE_BLOCK ] : squeeze_block_inp → squeeze_block_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_gimli_aead_decrypt : package _ _ _ :=
  (seq_link gimli_aead_decrypt link_rest(
      package_gimli,package_key_to_u32s,package_nonce_to_u32s,package_process_ad,package_process_ct,package_squeeze_block)).
Fail Next Obligation.

