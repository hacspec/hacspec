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

Definition riotboot_magic_v : (int32) :=
  ((@repr U32 1414482258)).

Notation "'fletcher_t'" := ((int32 '× int32)) : hacspec_scope.


Notation "'new_fletcher_inp'" := (
  unit_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'new_fletcher_out'" := (
  fletcher_t : choice_type) (in custom pack_type at level 2).
Definition NEW_FLETCHER : nat :=
  (7083).
Program Definition new_fletcher
   : package (fset.fset0) [interface] [interface
  #val #[ NEW_FLETCHER ] : new_fletcher_inp → new_fletcher_out ] :=
  (
    [package #def #[ NEW_FLETCHER ] (temp_inp : new_fletcher_inp) : new_fletcher_out { 
    ({ code @ret ((int32 '× int32)) (prod_ce(@repr U32 65535, @repr U32 65535
        )) } : code (fset.fset0) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_new_fletcher : package _ _ _ :=
  (new_fletcher).
Fail Next Obligation.


Notation "'max_chunk_size_inp'" := (
  unit_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'max_chunk_size_out'" := (
  uint_size : choice_type) (in custom pack_type at level 2).
Definition MAX_CHUNK_SIZE : nat :=
  (7084).
Program Definition max_chunk_size
   : package (fset.fset0) [interface] [interface
  #val #[ MAX_CHUNK_SIZE ] : max_chunk_size_inp → max_chunk_size_out ] :=
  (
    [package #def #[ MAX_CHUNK_SIZE ] (temp_inp : max_chunk_size_inp) : max_chunk_size_out { 
    ({ code @ret (uint_size) (usize 360) } : code (fset.fset0) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_max_chunk_size : package _ _ _ :=
  (max_chunk_size).
Fail Next Obligation.


Notation "'reduce_u32_inp'" := (
  int32 : choice_type) (in custom pack_type at level 2).
Notation "'reduce_u32_out'" := (
  int32 : choice_type) (in custom pack_type at level 2).
Definition REDUCE_U32 : nat :=
  (7092).
Program Definition reduce_u32
   : package (fset.fset0) [interface] [interface
  #val #[ REDUCE_U32 ] : reduce_u32_inp → reduce_u32_out ] :=
  ([package #def #[ REDUCE_U32 ] (temp_inp : reduce_u32_inp) : reduce_u32_out { 
    let '(x_7085) := temp_inp : int32 in
    ({ code  temp_7087 ←
        ((x_7085) .& (@repr U32 65535)) ;;
       temp_7089 ←
        ((x_7085) shift_right (@repr U32 16)) ;;
       '(temp_7091 : int32) ←
        ((temp_7087) .+ (temp_7089)) ;;
      @ret (int32) (temp_7091) } : code (fset.fset0) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_reduce_u32 : package _ _ _ :=
  (reduce_u32).
Fail Next Obligation.


Notation "'combine_inp'" := (
  int32 '× int32 : choice_type) (in custom pack_type at level 2).
Notation "'combine_out'" := (
  int32 : choice_type) (in custom pack_type at level 2).
Definition COMBINE : nat :=
  (7099).
Program Definition combine
   : package (fset.fset0) [interface] [interface
  #val #[ COMBINE ] : combine_inp → combine_out ] :=
  ([package #def #[ COMBINE ] (temp_inp : combine_inp) : combine_out { 
    let '(lower_7093 , upper_7094) := temp_inp : int32 '× int32 in
    ({ code  temp_7096 ←
        ((upper_7094) shift_left (@repr U32 16)) ;;
       temp_7098 ←
        ((lower_7093) .| (temp_7096)) ;;
      @ret (int32) (temp_7098) } : code (fset.fset0) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_combine : package _ _ _ :=
  (combine).
Fail Next Obligation.

Definition intermediate_b_7120_loc : ChoiceEqualityLocation :=
  ((int32 ; 7139%nat)).
Definition b_7111_loc : ChoiceEqualityLocation :=
  ((int32 ; 7140%nat)).
Definition intermediate_a_7113_loc : ChoiceEqualityLocation :=
  ((int32 ; 7141%nat)).
Definition a_7110_loc : ChoiceEqualityLocation :=
  ((int32 ; 7142%nat)).
Notation "'update_fletcher_inp'" := (
  fletcher_t '× seq int16 : choice_type) (in custom pack_type at level 2).
Notation "'update_fletcher_out'" := (
  fletcher_t : choice_type) (in custom pack_type at level 2).
Definition UPDATE_FLETCHER : nat :=
  (7143).
Program Definition update_fletcher
   : package (CEfset (
      [a_7110_loc ; b_7111_loc ; intermediate_a_7113_loc ; intermediate_b_7120_loc])) [interface
  #val #[ MAX_CHUNK_SIZE ] : max_chunk_size_inp → max_chunk_size_out ;
  #val #[ REDUCE_U32 ] : reduce_u32_inp → reduce_u32_out ] [interface
  #val #[ UPDATE_FLETCHER ] : update_fletcher_inp → update_fletcher_out ] :=
  (
    [package #def #[ UPDATE_FLETCHER ] (temp_inp : update_fletcher_inp) : update_fletcher_out { 
    let '(f_7102 , data_7103) := temp_inp : fletcher_t '× seq int16 in
    #import {sig #[ MAX_CHUNK_SIZE ] : max_chunk_size_inp → max_chunk_size_out } as max_chunk_size ;;
    let max_chunk_size := max_chunk_size tt in
    #import {sig #[ REDUCE_U32 ] : reduce_u32_inp → reduce_u32_out } as reduce_u32 ;;
    let reduce_u32 := fun x_0 => reduce_u32 (x_0) in
    ({ code  '(max_chunk_size_7104 : uint_size) ←
        ( '(temp_7101 : uint_size) ←
            (max_chunk_size ) ;;
          ret (temp_7101)) ;;
       temp_7138 ←
        (ret (f_7102)) ;;
      let '(a_7110, b_7111) :=
        (temp_7138) : (int32 '× int32) in
       '(temp_7106 : uint_size) ←
        (seq_num_chunks (data_7103) (max_chunk_size_7104)) ;;
       temp_7136 ←
        (foldi' (usize 0) (temp_7106) prod_ce(a_7110, b_7111) (L2 := CEfset (
                [a_7110_loc ; b_7111_loc ; intermediate_a_7113_loc ; intermediate_b_7120_loc])) (
              I2 := [interface
              #val #[ MAX_CHUNK_SIZE ] : max_chunk_size_inp → max_chunk_size_out ;
              #val #[ REDUCE_U32 ] : reduce_u32_inp → reduce_u32_out
              ]) (H_loc_incl := _) (H_opsig_incl := _) (fun i_7107 '(
              a_7110,
              b_7111
            ) =>
            ({ code  temp_7130 ←
                ( '(temp_7109 : (uint_size '× seq int16)) ←
                    (seq_get_chunk (data_7103) (max_chunk_size_7104) (
                        i_7107)) ;;
                  ret (temp_7109)) ;;
              let '(chunk_len_7112, chunk_7116) :=
                (temp_7130) : (uint_size '× seq int16) in
               '(intermediate_a_7113 : int32) ←
                  (ret (a_7110)) ;;
                #put intermediate_a_7113_loc := intermediate_a_7113 ;;
               '(intermediate_b_7120 : int32) ←
                  (ret (b_7111)) ;;
                #put intermediate_b_7120_loc := intermediate_b_7120 ;;
               temp_7128 ←
                (foldi' (usize 0) (chunk_len_7112) prod_ce(
                      intermediate_a_7113,
                      intermediate_b_7120
                    ) (L2 := CEfset (
                        [a_7110_loc ; b_7111_loc ; intermediate_a_7113_loc ; intermediate_b_7120_loc])) (
                      I2 := [interface
                      #val #[ REDUCE_U32 ] : reduce_u32_inp → reduce_u32_out
                      ]) (H_loc_incl := _) (H_opsig_incl := _) (fun j_7114 '(
                      intermediate_a_7113,
                      intermediate_b_7120
                    ) =>
                    ({ code  '(intermediate_a_7113 : int32) ←
                          (( '(temp_7117 : int16) ←
                                (seq_index (chunk_7116) (j_7114)) ;;
                               '(temp_7119 : int32) ←
                                ((intermediate_a_7113) .+ (@cast _ uint32 _ (
                                      temp_7117))) ;;
                              ret (temp_7119))) ;;
                        #put intermediate_a_7113_loc := intermediate_a_7113 ;;
                      
                       '(intermediate_b_7120 : int32) ←
                          (( '(temp_7122 : int32) ←
                                ((intermediate_b_7120) .+ (
                                    intermediate_a_7113)) ;;
                              ret (temp_7122))) ;;
                        #put intermediate_b_7120_loc := intermediate_b_7120 ;;
                      
                      @ret ((int32 '× int32)) (prod_ce(
                          intermediate_a_7113,
                          intermediate_b_7120
                        )) } : code (CEfset (
                          [a_7110_loc ; b_7111_loc ; intermediate_a_7113_loc ; intermediate_b_7120_loc])) [interface] _))) ;;
              let '(intermediate_a_7113, intermediate_b_7120) :=
                (temp_7128) : (int32 '× int32) in
              
               '(a_7110 : int32) ←
                  (( '(temp_7124 : int32) ←
                        (reduce_u32 (intermediate_a_7113)) ;;
                      ret (temp_7124))) ;;
                #put a_7110_loc := a_7110 ;;
              
               '(b_7111 : int32) ←
                  (( '(temp_7126 : int32) ←
                        (reduce_u32 (intermediate_b_7120)) ;;
                      ret (temp_7126))) ;;
                #put b_7111_loc := b_7111 ;;
              
              @ret ((int32 '× int32)) (prod_ce(a_7110, b_7111)) } : code (
                CEfset (
                  [a_7110_loc ; b_7111_loc ; intermediate_a_7113_loc ; intermediate_b_7120_loc])) [interface
              #val #[ REDUCE_U32 ] : reduce_u32_inp → reduce_u32_out ] _))) ;;
      let '(a_7110, b_7111) :=
        (temp_7136) : (int32 '× int32) in
      
       '(a_7110 : int32) ←
          (( '(temp_7132 : int32) ←
                (reduce_u32 (a_7110)) ;;
              ret (temp_7132))) ;;
        #put a_7110_loc := a_7110 ;;
      
       '(b_7111 : int32) ←
          (( '(temp_7134 : int32) ←
                (reduce_u32 (b_7111)) ;;
              ret (temp_7134))) ;;
        #put b_7111_loc := b_7111 ;;
      
      @ret ((int32 '× int32)) (prod_ce(a_7110, b_7111)) } : code (CEfset (
          [a_7110_loc ; b_7111_loc ; intermediate_a_7113_loc ; intermediate_b_7120_loc])) [interface
      #val #[ MAX_CHUNK_SIZE ] : max_chunk_size_inp → max_chunk_size_out ;
      #val #[ REDUCE_U32 ] : reduce_u32_inp → reduce_u32_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_update_fletcher : package _ _ _ :=
  (seq_link update_fletcher link_rest(
      package_max_chunk_size,package_reduce_u32)).
Fail Next Obligation.


Notation "'value_inp'" := (
  fletcher_t : choice_type) (in custom pack_type at level 2).
Notation "'value_out'" := (
  int32 : choice_type) (in custom pack_type at level 2).
Definition VALUE : nat :=
  (7151).
Program Definition value
   : package (fset.fset0) [interface
  #val #[ COMBINE ] : combine_inp → combine_out ] [interface
  #val #[ VALUE ] : value_inp → value_out ] :=
  ([package #def #[ VALUE ] (temp_inp : value_inp) : value_out { 
    let '(x_7144) := temp_inp : fletcher_t in
    #import {sig #[ COMBINE ] : combine_inp → combine_out } as combine ;;
    let combine := fun x_0 x_1 => combine (x_0,x_1) in
    ({ code  temp_7150 ←
        (ret (x_7144)) ;;
      let '(a_7145, b_7146) :=
        (temp_7150) : (int32 '× int32) in
       '(temp_7148 : int32) ←
        (combine (a_7145) (b_7146)) ;;
      @ret (int32) (temp_7148) } : code (fset.fset0) [interface
      #val #[ COMBINE ] : combine_inp → combine_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_value : package _ _ _ :=
  (seq_link value link_rest(package_combine)).
Fail Next Obligation.

Notation "'header_t'" := ((int32 '× int32 '× int32 '× int32
)) : hacspec_scope.

Definition u16_seq_7214_loc : ChoiceEqualityLocation :=
  ((seq int16 ; 7217%nat)).
Notation "'header_as_u16_slice_inp'" := (
  header_t : choice_type) (in custom pack_type at level 2).
Notation "'header_as_u16_slice_out'" := (
  seq int16 : choice_type) (in custom pack_type at level 2).
Definition HEADER_AS_U16_SLICE : nat :=
  (7218).
Program Definition header_as_u16_slice
   : package (CEfset ([u16_seq_7214_loc])) [interface] [interface
  #val #[ HEADER_AS_U16_SLICE ] : header_as_u16_slice_inp → header_as_u16_slice_out
  ] :=
  (
    [package #def #[ HEADER_AS_U16_SLICE ] (temp_inp : header_as_u16_slice_inp) : header_as_u16_slice_out { 
    let '(h_7152) := temp_inp : header_t in
    ({ code  temp_7216 ←
        (ret (h_7152)) ;;
      let '(magic_7153, seq_number_7156, start_addr_7159, _) :=
        (temp_7216) : (int32 '× int32 '× int32 '× int32) in
       '(magic_7165 : u32_word_t) ←
        ( temp_7155 ←
            (u32_to_be_bytes (magic_7153)) ;;
          ret (temp_7155)) ;;
       '(seq_number_7171 : u32_word_t) ←
        ( temp_7158 ←
            (u32_to_be_bytes (seq_number_7156)) ;;
          ret (temp_7158)) ;;
       '(start_addr_7177 : u32_word_t) ←
        ( temp_7161 ←
            (u32_to_be_bytes (start_addr_7159)) ;;
          ret (temp_7161)) ;;
       '(u8_seq_7164 : seq int8) ←
        ( temp_7163 ←
            (seq_new_ (default : int8) (usize 12)) ;;
          ret (temp_7163)) ;;
       '(u8_seq_7170 : seq int8) ←
        ( '(temp_7167 : seq int8) ←
            (array_to_seq (magic_7165)) ;;
           '(temp_7169 : seq int8) ←
            (seq_update_slice (u8_seq_7164) (usize 0) (temp_7167) (usize 0) (
                usize 4)) ;;
          ret (temp_7169)) ;;
       '(u8_seq_7176 : seq int8) ←
        ( '(temp_7173 : seq int8) ←
            (array_to_seq (seq_number_7171)) ;;
           '(temp_7175 : seq int8) ←
            (seq_update_slice (u8_seq_7170) (usize 4) (temp_7173) (usize 0) (
                usize 4)) ;;
          ret (temp_7175)) ;;
       '(u8_seq_7184 : seq int8) ←
        ( '(temp_7179 : seq int8) ←
            (array_to_seq (start_addr_7177)) ;;
           '(temp_7181 : seq int8) ←
            (seq_update_slice (u8_seq_7176) (usize 8) (temp_7179) (usize 0) (
                usize 4)) ;;
          ret (temp_7181)) ;;
       '(u16_seq_7214 : seq int16) ←
          ( temp_7183 ←
              (seq_new_ (default : int16) (usize 6)) ;;
            ret (temp_7183)) ;;
        #put u16_seq_7214_loc := u16_seq_7214 ;;
       '(u16_seq_7214 : (seq int16)) ←
        (foldi' (usize 0) (usize 3) u16_seq_7214 (L2 := CEfset (
                [u16_seq_7214_loc])) (
              I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (fun i_7185 u16_seq_7214 =>
            ({ code  '(u16_word_7192 : u16_word_t) ←
                ( '(temp_7187 : uint_size) ←
                    ((i_7185) .* (usize 4)) ;;
                   '(temp_7189 : seq int8) ←
                    (seq_slice (u8_seq_7184) (temp_7187) (usize 2)) ;;
                   '(temp_7191 : u16_word_t) ←
                    (array_from_seq (2) (temp_7189)) ;;
                  ret (temp_7191)) ;;
               '(u16_value_7199 : int16) ←
                ( temp_7194 ←
                    (u16_from_be_bytes (u16_word_7192)) ;;
                  ret (temp_7194)) ;;
               '(u16_seq_7214 : seq int16) ←
                ( '(temp_7196 : uint_size) ←
                    ((usize 2) .* (i_7185)) ;;
                   '(temp_7198 : uint_size) ←
                    ((temp_7196) .+ (usize 1)) ;;
                  ret (seq_upd u16_seq_7214 (temp_7198) (u16_value_7199))) ;;
              
               '(u16_word_7208 : u16_word_t) ←
                ( '(temp_7201 : uint_size) ←
                    ((i_7185) .* (usize 4)) ;;
                   '(temp_7203 : uint_size) ←
                    ((temp_7201) .+ (usize 2)) ;;
                   '(temp_7205 : seq int8) ←
                    (seq_slice (u8_seq_7184) (temp_7203) (usize 2)) ;;
                   '(temp_7207 : u16_word_t) ←
                    (array_from_seq (2) (temp_7205)) ;;
                  ret (temp_7207)) ;;
               '(u16_value_7213 : int16) ←
                ( temp_7210 ←
                    (u16_from_be_bytes (u16_word_7208)) ;;
                  ret (temp_7210)) ;;
               '(u16_seq_7214 : seq int16) ←
                ( '(temp_7212 : uint_size) ←
                    ((usize 2) .* (i_7185)) ;;
                  ret (seq_upd u16_seq_7214 (temp_7212) (u16_value_7213))) ;;
              
              @ret ((seq int16)) (u16_seq_7214) } : code (CEfset (
                  [u16_seq_7214_loc])) [interface] _))) ;;
      
      @ret (seq int16) (u16_seq_7214) } : code (CEfset (
          [u16_seq_7214_loc])) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_header_as_u16_slice : package _ _ _ :=
  (header_as_u16_slice).
Fail Next Obligation.

Definition result_7240_loc : ChoiceEqualityLocation :=
  ((bool_ChoiceEquality ; 7243%nat)).
Notation "'is_valid_header_inp'" := (
  header_t : choice_type) (in custom pack_type at level 2).
Notation "'is_valid_header_out'" := (
  bool_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Definition IS_VALID_HEADER : nat :=
  (7244).
Program Definition is_valid_header
   : package (CEfset ([result_7240_loc])) [interface
  #val #[ HEADER_AS_U16_SLICE ] : header_as_u16_slice_inp → header_as_u16_slice_out ;
  #val #[ NEW_FLETCHER ] : new_fletcher_inp → new_fletcher_out ;
  #val #[ UPDATE_FLETCHER ] : update_fletcher_inp → update_fletcher_out ;
  #val #[ VALUE ] : value_inp → value_out ] [interface
  #val #[ IS_VALID_HEADER ] : is_valid_header_inp → is_valid_header_out ] :=
  (
    [package #def #[ IS_VALID_HEADER ] (temp_inp : is_valid_header_inp) : is_valid_header_out { 
    let '(h_7219) := temp_inp : header_t in
    #import {sig #[ HEADER_AS_U16_SLICE ] : header_as_u16_slice_inp → header_as_u16_slice_out } as header_as_u16_slice ;;
    let header_as_u16_slice := fun x_0 => header_as_u16_slice (x_0) in
    #import {sig #[ NEW_FLETCHER ] : new_fletcher_inp → new_fletcher_out } as new_fletcher ;;
    let new_fletcher := new_fletcher tt in
    #import {sig #[ UPDATE_FLETCHER ] : update_fletcher_inp → update_fletcher_out } as update_fletcher ;;
    let update_fletcher := fun x_0 x_1 => update_fletcher (x_0,x_1) in
    #import {sig #[ VALUE ] : value_inp → value_out } as value ;;
    let value := fun x_0 => value (x_0) in
    ({ code  temp_7242 ←
        (ret (h_7219)) ;;
      let '(magic_number_7220, seq_number_7221, start_addr_7222, checksum_7223
        ) :=
        (temp_7242) : (int32 '× int32 '× int32 '× int32) in
       '(slice_7231 : seq int16) ←
        ( '(temp_7225 : seq int16) ←
            (header_as_u16_slice (prod_ce(
                  magic_number_7220,
                  seq_number_7221,
                  start_addr_7222,
                  checksum_7223
                ))) ;;
          ret (temp_7225)) ;;
       '(result_7240 : bool_ChoiceEquality) ←
          (ret ((false : bool_ChoiceEquality))) ;;
        #put result_7240_loc := result_7240 ;;
       '(temp_7227 : bool_ChoiceEquality) ←
        ((magic_number_7220) =.? (riotboot_magic_v)) ;;
       '(result_7240 : (bool_ChoiceEquality)) ←
        (if temp_7227:bool_ChoiceEquality
          then (*not state*) (let temp_then :=  '(fletcher_7230 : (
                  int32 '×
                  int32
                )) ←
              ( '(temp_7229 : fletcher_t) ←
                  (new_fletcher ) ;;
                ret (temp_7229)) ;;
             '(fletcher_7234 : (int32 '× int32)) ←
              ( '(temp_7233 : fletcher_t) ←
                  (update_fletcher (fletcher_7230) (slice_7231)) ;;
                ret (temp_7233)) ;;
             '(sum_7237 : int32) ←
              ( '(temp_7236 : int32) ←
                  (value (fletcher_7234)) ;;
                ret (temp_7236)) ;;
             '(result_7240 : bool_ChoiceEquality) ←
                (( '(temp_7239 : bool_ChoiceEquality) ←
                      ((sum_7237) =.? (checksum_7223)) ;;
                    ret (temp_7239))) ;;
              #put result_7240_loc := result_7240 ;;
            
            @ret ((bool_ChoiceEquality)) (result_7240) in
            ({ code temp_then } : code (CEfset ([result_7240_loc])) [interface
              #val #[ NEW_FLETCHER ] : new_fletcher_inp → new_fletcher_out ;
              #val #[ UPDATE_FLETCHER ] : update_fletcher_inp → update_fletcher_out ;
              #val #[ VALUE ] : value_inp → value_out ] _))
          else @ret ((bool_ChoiceEquality)) (result_7240)) ;;
      
      @ret (bool_ChoiceEquality) (result_7240) } : code (CEfset (
          [result_7240_loc])) [interface
      #val #[ HEADER_AS_U16_SLICE ] : header_as_u16_slice_inp → header_as_u16_slice_out ;
      #val #[ NEW_FLETCHER ] : new_fletcher_inp → new_fletcher_out ;
      #val #[ UPDATE_FLETCHER ] : update_fletcher_inp → update_fletcher_out ;
      #val #[ VALUE ] : value_inp → value_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_is_valid_header : package _ _ _ :=
  (seq_link is_valid_header link_rest(
      package_header_as_u16_slice,package_new_fletcher,package_update_fletcher,package_value)).
Fail Next Obligation.

Definition image_7259_loc : ChoiceEqualityLocation :=
  ((int32 ; 7273%nat)).
Definition image_found_7258_loc : ChoiceEqualityLocation :=
  ((bool_ChoiceEquality ; 7274%nat)).
Notation "'choose_image_inp'" := (
  seq header_t : choice_type) (in custom pack_type at level 2).
Notation "'choose_image_out'" := ((bool_ChoiceEquality '× int32
  ) : choice_type) (in custom pack_type at level 2).
Definition CHOOSE_IMAGE : nat :=
  (7275).
Program Definition choose_image
   : package (CEfset ([image_7259_loc ; image_found_7258_loc])) [interface
  #val #[ IS_VALID_HEADER ] : is_valid_header_inp → is_valid_header_out
  ] [interface #val #[ CHOOSE_IMAGE ] : choose_image_inp → choose_image_out
  ] :=
  (
    [package #def #[ CHOOSE_IMAGE ] (temp_inp : choose_image_inp) : choose_image_out { 
    let '(images_7245) := temp_inp : seq header_t in
    #import {sig #[ IS_VALID_HEADER ] : is_valid_header_inp → is_valid_header_out } as is_valid_header ;;
    let is_valid_header := fun x_0 => is_valid_header (x_0) in
    ({ code  '(image_7259 : int32) ←
          (ret (@repr U32 0)) ;;
        #put image_7259_loc := image_7259 ;;
       '(image_found_7258 : bool_ChoiceEquality) ←
          (ret ((false : bool_ChoiceEquality))) ;;
        #put image_found_7258_loc := image_found_7258 ;;
       '(temp_7247 : uint_size) ←
        (seq_len (images_7245)) ;;
       temp_7272 ←
        (foldi' (usize 0) (temp_7247) prod_ce(image_7259, image_found_7258) (
              L2 := CEfset ([image_7259_loc ; image_found_7258_loc])) (
              I2 := [interface
              #val #[ IS_VALID_HEADER ] : is_valid_header_inp → is_valid_header_out
              ]) (H_loc_incl := _) (H_opsig_incl := _) (fun i_7248 '(
              image_7259,
              image_found_7258
            ) =>
            ({ code  '(header_7251 : (int32 '× int32 '× int32 '× int32)) ←
                ( '(temp_7250 : header_t) ←
                    (seq_index (images_7245) (i_7248)) ;;
                  ret (temp_7250)) ;;
               temp_7270 ←
                (ret (header_7251)) ;;
              let '(
                  magic_number_7252,
                  seq_number_7253,
                  start_addr_7254,
                  checksum_7255
                ) :=
                (temp_7270) : (int32 '× int32 '× int32 '× int32) in
               '(temp_7257 : bool_ChoiceEquality) ←
                (is_valid_header (prod_ce(
                      magic_number_7252,
                      seq_number_7253,
                      start_addr_7254,
                      checksum_7255
                    ))) ;;
               temp_7268 ←
                (if temp_7257:bool_ChoiceEquality
                  then (*not state*) (let temp_then :=  '(
                        change_image_7264 : bool_ChoiceEquality) ←
                      ( '(temp_7261 : bool_ChoiceEquality) ←
                          ((seq_number_7253) <=.? (image_7259)) ;;
                         '(temp_7263 : bool_ChoiceEquality) ←
                          ((image_found_7258) && (temp_7261)) ;;
                        ret (negb (temp_7263))) ;;
                     temp_7266 ←
                      (if change_image_7264:bool_ChoiceEquality
                        then (*not state*) (let temp_then :=  '(
                                image_7259 : int32) ←
                              ((ret (start_addr_7254))) ;;
                            #put image_7259_loc := image_7259 ;;
                          
                           '(image_found_7258 : bool_ChoiceEquality) ←
                              ((ret ((true : bool_ChoiceEquality)))) ;;
                            #put image_found_7258_loc := image_found_7258 ;;
                          
                          @ret ((int32 '× bool_ChoiceEquality)) (prod_ce(
                              image_7259,
                              image_found_7258
                            )) in
                          ({ code temp_then } : code (CEfset (
                                [image_7259_loc ; image_found_7258_loc])) [interface] _))
                        else @ret ((int32 '× bool_ChoiceEquality)) (prod_ce(
                            image_7259,
                            image_found_7258
                          ))) ;;
                    let '(image_7259, image_found_7258) :=
                      (temp_7266) : (int32 '× bool_ChoiceEquality) in
                    
                    @ret ((int32 '× bool_ChoiceEquality)) (prod_ce(
                        image_7259,
                        image_found_7258
                      )) in
                    ({ code temp_then } : code (CEfset (
                          [image_7259_loc ; image_found_7258_loc])) [interface] _))
                  else @ret ((int32 '× bool_ChoiceEquality)) (prod_ce(
                      image_7259,
                      image_found_7258
                    ))) ;;
              let '(image_7259, image_found_7258) :=
                (temp_7268) : (int32 '× bool_ChoiceEquality) in
              
              @ret ((int32 '× bool_ChoiceEquality)) (prod_ce(
                  image_7259,
                  image_found_7258
                )) } : code (CEfset (
                  [image_7259_loc ; image_found_7258_loc])) [interface
              #val #[ IS_VALID_HEADER ] : is_valid_header_inp → is_valid_header_out
              ] _))) ;;
      let '(image_7259, image_found_7258) :=
        (temp_7272) : (int32 '× bool_ChoiceEquality) in
      
      @ret ((bool_ChoiceEquality '× int32)) (prod_ce(
          image_found_7258,
          image_7259
        )) } : code (CEfset (
          [image_7259_loc ; image_found_7258_loc])) [interface
      #val #[ IS_VALID_HEADER ] : is_valid_header_inp → is_valid_header_out
      ] _)
    }]).
Fail Next Obligation.
Program Definition package_choose_image : package _ _ _ :=
  (seq_link choose_image link_rest(package_is_valid_header)).
Fail Next Obligation.

