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

Notation "'dim_type_t'" := (uint_size) : hacspec_scope.

Notation "'scalar_t'" := (int128) : hacspec_scope.

Notation "'dims_t'" := ((dim_type_t '× dim_type_t)) : hacspec_scope.

Notation "'matrix_t'" := ((dims_t '× seq scalar_t)) : hacspec_scope.

Notation "'mat_res_t'" := ((result int8 matrix_t)) : hacspec_scope.

Notation "'scal_res_t'" := ((result int8 scalar_t)) : hacspec_scope.

Definition dimension_sequence_length_mismatch_v : (int8) :=
  ((@repr U8 10)).

Definition index_out_of_bounds_v : (int8) :=
  ((@repr U8 11)).

Definition slice_out_of_bounds_v : (int8) :=
  ((@repr U8 12)).

Definition dimension_mismatch_v : (int8) :=
  ((@repr U8 13)).


Notation "'new__inp'" := (
  dim_type_t '× dim_type_t '× seq scalar_t : choice_type) (in custom pack_type at level 2).
Notation "'new__out'" := (
  mat_res_t : choice_type) (in custom pack_type at level 2).
Definition NEW : nat :=
  (5734).
Program Definition new_
   : package (fset.fset0) [interface] [interface
  #val #[ NEW ] : new__inp → new__out ] :=
  ([package #def #[ NEW ] (temp_inp : new__inp) : new__out { 
    let '(
      rows_5724 , cols_5725 , seq_5719) := temp_inp : dim_type_t '× dim_type_t '× seq scalar_t in
    ({ code  '(temp_5721 : uint_size) ←
        (seq_len (seq_5719)) ;;
       '(temp_5723 : bool_ChoiceEquality) ←
        ((temp_5721) >.? (usize 0)) ;;
       '(temp_5727 : dim_type_t) ←
        ((rows_5724) .* (cols_5725)) ;;
       '(temp_5729 : uint_size) ←
        (seq_len (seq_5719)) ;;
       '(temp_5731 : bool_ChoiceEquality) ←
        ((temp_5727) =.? (temp_5729)) ;;
       '(temp_5733 : bool_ChoiceEquality) ←
        ((temp_5723) && (temp_5731)) ;;
      @ret ((result int8 matrix_t)) ((if (
            temp_5733):bool_ChoiceEquality then (*inline*) (@inl matrix_t int8 (
              prod_ce(prod_ce(rows_5724, cols_5725), seq_5719))) else (
            @inr matrix_t int8 (
              dimension_sequence_length_mismatch_v)))) } : code (
        fset.fset0) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_new_ : package _ _ _ :=
  (new_).
Fail Next Obligation.

Definition ret_5745_loc : ChoiceEqualityLocation :=
  ((seq int128 ; 5746%nat)).
Notation "'repeat_inp'" := (
  dim_type_t '× dim_type_t '× scalar_t : choice_type) (in custom pack_type at level 2).
Notation "'repeat_out'" := (
  matrix_t : choice_type) (in custom pack_type at level 2).
Definition REPEAT : nat :=
  (5747).
Program Definition repeat
   : package (CEfset ([ret_5745_loc])) [interface
  #val #[ NEW ] : new__inp → new__out ] [interface
  #val #[ REPEAT ] : repeat_inp → repeat_out ] :=
  ([package #def #[ REPEAT ] (temp_inp : repeat_inp) : repeat_out { 
    let '(
      n_5735 , m_5736 , scalar_5744) := temp_inp : dim_type_t '× dim_type_t '× scalar_t in
    #import {sig #[ NEW ] : new__inp → new__out } as new_ ;;
    let new_ := fun x_0 x_1 x_2 => new_ (x_0,x_1,x_2) in
    ({ code  '(ret_5745 : seq int128) ←
          ( '(temp_5738 : dim_type_t) ←
              ((n_5735) .* (m_5736)) ;;
             '(temp_5740 : mat_res_t) ←
              (seq_new_ (default : scalar_t) (temp_5738)) ;;
            ret (temp_5740)) ;;
        #put ret_5745_loc := ret_5745 ;;
       '(temp_5742 : dim_type_t) ←
        ((n_5735) .* (m_5736)) ;;
       '(ret_5745 : (seq int128)) ←
        (foldi' (usize 0) (temp_5742) ret_5745 (L2 := CEfset ([ret_5745_loc])) (
              I2 := [interface #val #[ NEW ] : new__inp → new__out
              ]) (H_loc_incl := _) (H_opsig_incl := _) (fun i_5743 ret_5745 =>
            ({ code  '(ret_5745 : seq int128) ←
                (ret (seq_upd ret_5745 (i_5743) (scalar_5744))) ;;
              
              @ret ((seq int128)) (ret_5745) } : code (CEfset (
                  [ret_5745_loc])) [interface] _))) ;;
      
      @ret (((dim_type_t '× dim_type_t) '× seq int128)) (prod_ce(
          prod_ce(n_5735, m_5736),
          ret_5745
        )) } : code (CEfset ([ret_5745_loc])) [interface
      #val #[ NEW ] : new__inp → new__out ] _)
    }]).
Fail Next Obligation.
Program Definition package_repeat : package _ _ _ :=
  (seq_link repeat link_rest(package_new_)).
Fail Next Obligation.


Notation "'zeros_inp'" := (
  dim_type_t '× dim_type_t : choice_type) (in custom pack_type at level 2).
Notation "'zeros_out'" := (
  matrix_t : choice_type) (in custom pack_type at level 2).
Definition ZEROS : nat :=
  (5754).
Program Definition zeros
   : package (CEfset ([])) [interface
  #val #[ REPEAT ] : repeat_inp → repeat_out ] [interface
  #val #[ ZEROS ] : zeros_inp → zeros_out ] :=
  ([package #def #[ ZEROS ] (temp_inp : zeros_inp) : zeros_out { 
    let '(n_5748 , m_5749) := temp_inp : dim_type_t '× dim_type_t in
    #import {sig #[ REPEAT ] : repeat_inp → repeat_out } as repeat ;;
    let repeat := fun x_0 x_1 x_2 => repeat (x_0,x_1,x_2) in
    ({ code  temp_5751 ←
        (pub_int128_zero ) ;;
       '(temp_5753 : matrix_t) ←
        (repeat (n_5748) (m_5749) (temp_5751)) ;;
      @ret (matrix_t) (temp_5753) } : code (CEfset ([])) [interface
      #val #[ REPEAT ] : repeat_inp → repeat_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_zeros : package _ _ _ :=
  (seq_link zeros link_rest(package_repeat)).
Fail Next Obligation.


Notation "'ones_inp'" := (
  dim_type_t '× dim_type_t : choice_type) (in custom pack_type at level 2).
Notation "'ones_out'" := (
  matrix_t : choice_type) (in custom pack_type at level 2).
Definition ONES : nat :=
  (5761).
Program Definition ones
   : package (CEfset ([])) [interface
  #val #[ REPEAT ] : repeat_inp → repeat_out ] [interface
  #val #[ ONES ] : ones_inp → ones_out ] :=
  ([package #def #[ ONES ] (temp_inp : ones_inp) : ones_out { 
    let '(n_5755 , m_5756) := temp_inp : dim_type_t '× dim_type_t in
    #import {sig #[ REPEAT ] : repeat_inp → repeat_out } as repeat ;;
    let repeat := fun x_0 x_1 x_2 => repeat (x_0,x_1,x_2) in
    ({ code  temp_5758 ←
        (pub_int128_one ) ;;
       '(temp_5760 : matrix_t) ←
        (repeat (n_5755) (m_5756) (temp_5758)) ;;
      @ret (matrix_t) (temp_5760) } : code (CEfset ([])) [interface
      #val #[ REPEAT ] : repeat_inp → repeat_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_ones : package _ _ _ :=
  (seq_link ones link_rest(package_repeat)).
Fail Next Obligation.

Definition ret_5780_loc : ChoiceEqualityLocation :=
  ((seq int128 ; 5781%nat)).
Notation "'identity_inp'" := (
  dim_type_t '× dim_type_t : choice_type) (in custom pack_type at level 2).
Notation "'identity_out'" := (
  matrix_t : choice_type) (in custom pack_type at level 2).
Definition IDENTITY : nat :=
  (5782).
Program Definition identity
   : package (CEfset ([ret_5780_loc])) [interface
  #val #[ MIN ] : min_inp → min_out ; #val #[ NEW ] : new__inp → new__out
  ] [interface #val #[ IDENTITY ] : identity_inp → identity_out ] :=
  ([package #def #[ IDENTITY ] (temp_inp : identity_inp) : identity_out { 
    let '(n_5762 , m_5763) := temp_inp : dim_type_t '× dim_type_t in
    #import {sig #[ MIN ] : min_inp → min_out } as min ;;
    let min := fun x_0 x_1 => min (x_0,x_1) in
    #import {sig #[ NEW ] : new__inp → new__out } as new_ ;;
    let new_ := fun x_0 x_1 x_2 => new_ (x_0,x_1,x_2) in
    ({ code  '(ret_5780 : seq int128) ←
          ( '(temp_5765 : dim_type_t) ←
              ((n_5762) .* (m_5763)) ;;
             '(temp_5767 : mat_res_t) ←
              (seq_new_ (default : scalar_t) (temp_5765)) ;;
            ret (temp_5767)) ;;
        #put ret_5780_loc := ret_5780 ;;
       temp_5769 ←
        (min (n_5762) (m_5763)) ;;
       '(ret_5780 : (seq int128)) ←
        (foldi' (usize 0) (temp_5769) ret_5780 (L2 := CEfset ([ret_5780_loc])) (
              I2 := [interface #val #[ MIN ] : min_inp → min_out ;
              #val #[ NEW ] : new__inp → new__out
              ]) (H_loc_incl := _) (H_opsig_incl := _) (fun i_5770 ret_5780 =>
            ({ code  '(index_5777 : uint_size) ←
                ( temp_5772 ←
                    (min (n_5762) (m_5763)) ;;
                   '(temp_5774 : uint_size) ←
                    ((i_5770) .* (temp_5772)) ;;
                   '(temp_5776 : uint_size) ←
                    ((temp_5774) .+ (i_5770)) ;;
                  ret (temp_5776)) ;;
               '(ret_5780 : seq int128) ←
                ( temp_5779 ←
                    (pub_int128_one ) ;;
                  ret (seq_upd ret_5780 (index_5777) (temp_5779))) ;;
              
              @ret ((seq int128)) (ret_5780) } : code (CEfset (
                  [ret_5780_loc])) [interface
              #val #[ MIN ] : min_inp → min_out ] _))) ;;
      
      @ret (((dim_type_t '× dim_type_t) '× seq int128)) (prod_ce(
          prod_ce(n_5762, m_5763),
          ret_5780
        )) } : code (CEfset ([ret_5780_loc])) [interface
      #val #[ MIN ] : min_inp → min_out ;
      #val #[ NEW ] : new__inp → new__out ] _)
    }]).
Fail Next Obligation.
Program Definition package_identity : package _ _ _ :=
  (seq_link identity link_rest(package_min,package_new_)).
Fail Next Obligation.


Notation "'index_inp'" := (
  matrix_t '× dim_type_t '× dim_type_t : choice_type) (in custom pack_type at level 2).
Notation "'index_out'" := (
  scal_res_t : choice_type) (in custom pack_type at level 2).
Definition INDEX : nat :=
  (5805).
Program Definition index
   : package (fset.fset0) [interface] [interface
  #val #[ INDEX ] : index_inp → index_out ] :=
  ([package #def #[ INDEX ] (temp_inp : index_inp) : index_out { 
    let '(
      m_5783 , i_5785 , j_5789) := temp_inp : matrix_t '× dim_type_t '× dim_type_t in
    ({ code  temp_5804 ←
        (ret (m_5783)) ;;
      let '(dim_5784, seq_5799) :=
        (temp_5804) : (dims_t '× seq scalar_t) in
       temp_5802 ←
        (ret (dim_5784)) ;;
      let '(rows_5793, cols_5786) :=
        (temp_5802) : (dim_type_t '× dim_type_t) in
       '(index_5792 : uint_size) ←
        ( '(temp_5788 : dim_type_t) ←
            ((i_5785) .* (cols_5786)) ;;
           '(temp_5791 : dim_type_t) ←
            ((temp_5788) .+ (j_5789)) ;;
          ret (temp_5791)) ;;
       '(temp_5795 : uint_size) ←
        ((rows_5793) .* (cols_5786)) ;;
       '(temp_5797 : bool_ChoiceEquality) ←
        ((index_5792) >=.? (temp_5795)) ;;
       '(temp_5800 : scalar_t) ←
        (seq_index (seq_5799) (index_5792)) ;;
      @ret ((result int8 scalar_t)) ((if (
            temp_5797):bool_ChoiceEquality then (*inline*) (@inr scalar_t int8 (
              index_out_of_bounds_v)) else (@inl scalar_t int8 (
              temp_5800)))) } : code (fset.fset0) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_index : package _ _ _ :=
  (index).
Fail Next Obligation.

Definition ret_5829_loc : ChoiceEqualityLocation :=
  ((seq int128 ; 5834%nat)).
Notation "'transpose_inp'" := (
  matrix_t : choice_type) (in custom pack_type at level 2).
Notation "'transpose_out'" := (
  matrix_t : choice_type) (in custom pack_type at level 2).
Definition TRANSPOSE : nat :=
  (5835).
Program Definition transpose
   : package (CEfset ([ret_5829_loc])) [interface
  #val #[ NEW ] : new__inp → new__out ] [interface
  #val #[ TRANSPOSE ] : transpose_inp → transpose_out ] :=
  ([package #def #[ TRANSPOSE ] (temp_inp : transpose_inp) : transpose_out { 
    let '(matrix_5806) := temp_inp : matrix_t in
    #import {sig #[ NEW ] : new__inp → new__out } as new_ ;;
    let new_ := fun x_0 x_1 x_2 => new_ (x_0,x_1,x_2) in
    ({ code  temp_5833 ←
        (ret (matrix_5806)) ;;
      let '(dim_5807, seq_5808) :=
        (temp_5833) : (dims_t '× seq scalar_t) in
       temp_5831 ←
        (ret (dim_5807)) ;;
      let '(rows_5813, cols_5814) :=
        (temp_5831) : (dim_type_t '× dim_type_t) in
       '(ret_5829 : seq int128) ←
          ( '(temp_5810 : uint_size) ←
              (seq_len (seq_5808)) ;;
             '(temp_5812 : mat_res_t) ←
              (seq_new_ (default : scalar_t) (temp_5810)) ;;
            ret (temp_5812)) ;;
        #put ret_5829_loc := ret_5829 ;;
       '(ret_5829 : (seq int128)) ←
        (foldi' (usize 0) (rows_5813) ret_5829 (L2 := CEfset ([ret_5829_loc])) (
              I2 := [interface #val #[ NEW ] : new__inp → new__out
              ]) (H_loc_incl := _) (H_opsig_incl := _) (fun i_5815 ret_5829 =>
            ({ code  '(ret_5829 : (seq int128)) ←
                (foldi' (usize 0) (cols_5814) ret_5829 (L2 := CEfset (
                        [ret_5829_loc])) (
                      I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (fun j_5818 ret_5829 =>
                    ({ code  '(seq_index_5826 : uint_size) ←
                        ( '(temp_5817 : uint_size) ←
                            ((i_5815) .* (cols_5814)) ;;
                           '(temp_5820 : uint_size) ←
                            ((temp_5817) .+ (j_5818)) ;;
                          ret (temp_5820)) ;;
                       '(ret_index_5825 : uint_size) ←
                        ( '(temp_5822 : uint_size) ←
                            ((j_5818) .* (rows_5813)) ;;
                           '(temp_5824 : uint_size) ←
                            ((temp_5822) .+ (i_5815)) ;;
                          ret (temp_5824)) ;;
                       '(ret_5829 : seq int128) ←
                        ( '(temp_5828 : scalar_t) ←
                            (seq_index (seq_5808) (seq_index_5826)) ;;
                          ret (seq_upd ret_5829 (ret_index_5825) (
                              temp_5828))) ;;
                      
                      @ret ((seq int128)) (ret_5829) } : code (CEfset (
                          [ret_5829_loc])) [interface] _))) ;;
              
              @ret ((seq int128)) (ret_5829) } : code (CEfset (
                  [ret_5829_loc])) [interface] _))) ;;
      
      @ret (((uint_size '× uint_size) '× seq int128)) (prod_ce(
          prod_ce(cols_5814, rows_5813),
          ret_5829
        )) } : code (CEfset ([ret_5829_loc])) [interface
      #val #[ NEW ] : new__inp → new__out ] _)
    }]).
Fail Next Obligation.
Program Definition package_transpose : package _ _ _ :=
  (seq_link transpose link_rest(package_new_)).
Fail Next Obligation.

Definition ret_5882_loc : ChoiceEqualityLocation :=
  ((seq int128 ; 5896%nat)).
Definition res_5883_loc : ChoiceEqualityLocation :=
  (((result int8 matrix_t) ; 5897%nat)).
Notation "'slice_inp'" := (
  matrix_t '× dims_t '× dims_t : choice_type) (in custom pack_type at level 2).
Notation "'slice_out'" := (
  mat_res_t : choice_type) (in custom pack_type at level 2).
Definition SLICE : nat :=
  (5898).
Program Definition slice
   : package (CEfset ([ret_5882_loc ; res_5883_loc])) [interface
  #val #[ NEW ] : new__inp → new__out ] [interface
  #val #[ SLICE ] : slice_inp → slice_out ] :=
  ([package #def #[ SLICE ] (temp_inp : slice_inp) : slice_out { 
    let '(
      matrix_5836 , start_5838 , len_5839) := temp_inp : matrix_t '× dims_t '× dims_t in
    #import {sig #[ NEW ] : new__inp → new__out } as new_ ;;
    let new_ := fun x_0 x_1 x_2 => new_ (x_0,x_1,x_2) in
    ({ code  temp_5895 ←
        (ret (matrix_5836)) ;;
      let '(dim_5837, seq_5880) :=
        (temp_5895) : (dims_t '× seq scalar_t) in
       temp_5893 ←
        (ret (dim_5837)) ;;
      let '(rows_5858, cols_5841) :=
        (temp_5893) : (dim_type_t '× dim_type_t) in
       temp_5891 ←
        (ret (start_5838)) ;;
      let '(start_row_5840, start_col_5844) :=
        (temp_5891) : (dim_type_t '× dim_type_t) in
       temp_5889 ←
        (ret (len_5839)) ;;
      let '(len_rows_5847, len_cols_5848) :=
        (temp_5889) : (dim_type_t '× dim_type_t) in
       '(start_index_5853 : uint_size) ←
        ( '(temp_5843 : uint_size) ←
            ((start_row_5840) .* (cols_5841)) ;;
           '(temp_5846 : uint_size) ←
            ((temp_5843) .+ (start_col_5844)) ;;
          ret (temp_5846)) ;;
       '(ret_5882 : seq int128) ←
          ( '(temp_5850 : uint_size) ←
              ((len_rows_5847) .* (len_cols_5848)) ;;
             '(temp_5852 : mat_res_t) ←
              (seq_new_ (default : scalar_t) (temp_5850)) ;;
            ret (temp_5852)) ;;
        #put ret_5882_loc := ret_5882 ;;
       '(res_5883 : (result int8 matrix_t)) ←
          (ret (@inr matrix_t int8 (slice_out_of_bounds_v))) ;;
        #put res_5883_loc := res_5883 ;;
       '(temp_5855 : uint_size) ←
        ((len_rows_5847) .* (len_cols_5848)) ;;
       '(temp_5857 : uint_size) ←
        ((start_index_5853) .+ (temp_5855)) ;;
       '(temp_5860 : uint_size) ←
        ((rows_5858) .* (cols_5841)) ;;
       '(temp_5862 : bool_ChoiceEquality) ←
        ((temp_5857) <=.? (temp_5860)) ;;
       temp_5887 ←
        (if temp_5862:bool_ChoiceEquality
          then (*not state*) (let temp_then :=  '(ret_5882 : (seq int128)) ←
              (foldi' (usize 0) (len_rows_5847) ret_5882 (L2 := CEfset (
                      [ret_5882_loc ; res_5883_loc])) (I2 := [interface
                    #val #[ NEW ] : new__inp → new__out
                    ]) (H_loc_incl := _) (H_opsig_incl := _) (fun i_5863 ret_5882 =>
                  ({ code  '(ret_5882 : (seq int128)) ←
                      (foldi' (usize 0) (len_cols_5848) ret_5882 (L2 := CEfset (
                              [ret_5882_loc ; res_5883_loc])) (
                            I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (fun j_5866 ret_5882 =>
                          ({ code  '(ret_index_5877 : uint_size) ←
                              ( '(temp_5865 : uint_size) ←
                                  ((i_5863) .* (len_cols_5848)) ;;
                                 '(temp_5868 : uint_size) ←
                                  ((temp_5865) .+ (j_5866)) ;;
                                ret (temp_5868)) ;;
                             '(seq_index_5878 : uint_size) ←
                              ( '(temp_5870 : uint_size) ←
                                  ((start_row_5840) .+ (i_5863)) ;;
                                 '(temp_5872 : uint_size) ←
                                  ((temp_5870) .* (cols_5841)) ;;
                                 '(temp_5874 : uint_size) ←
                                  ((start_col_5844) .+ (j_5866)) ;;
                                 '(temp_5876 : uint_size) ←
                                  ((temp_5872) .+ (temp_5874)) ;;
                                ret (temp_5876)) ;;
                             '(ret_5882 : seq int128) ←
                              ( '(temp_5881 : scalar_t) ←
                                  (seq_index (seq_5880) (seq_index_5878)) ;;
                                ret (seq_upd ret_5882 (ret_index_5877) (
                                    temp_5881))) ;;
                            
                            @ret ((seq int128)) (ret_5882) } : code (CEfset (
                                [ret_5882_loc ; res_5883_loc])) [interface] _))) ;;
                    
                    @ret ((seq int128)) (ret_5882) } : code (CEfset (
                        [ret_5882_loc ; res_5883_loc])) [interface] _))) ;;
            
             '(res_5883 : (result int8 matrix_t)) ←
                (( '(temp_5885 : mat_res_t) ←
                      (new_ (len_rows_5847) (len_cols_5848) (ret_5882)) ;;
                    ret (temp_5885))) ;;
              #put res_5883_loc := res_5883 ;;
            
            @ret ((seq int128 '× (result int8 matrix_t))) (prod_ce(
                ret_5882,
                res_5883
              )) in
            ({ code temp_then } : code (CEfset (
                  [ret_5882_loc ; res_5883_loc])) [interface
              #val #[ NEW ] : new__inp → new__out ] _))
          else @ret ((seq int128 '× (result int8 matrix_t))) (prod_ce(
              ret_5882,
              res_5883
            ))) ;;
      let '(ret_5882, res_5883) :=
        (temp_5887) : (seq int128 '× (result int8 matrix_t)) in
      
      @ret ((result int8 matrix_t)) (res_5883) } : code (CEfset (
          [ret_5882_loc ; res_5883_loc])) [interface
      #val #[ NEW ] : new__inp → new__out ] _)
    }]).
Fail Next Obligation.
Program Definition package_slice : package _ _ _ :=
  (seq_link slice link_rest(package_new_)).
Fail Next Obligation.

Definition ret_5913_loc : ChoiceEqualityLocation :=
  ((seq int128 ; 5917%nat)).
Notation "'scale_inp'" := (
  matrix_t '× scalar_t : choice_type) (in custom pack_type at level 2).
Notation "'scale_out'" := (
  matrix_t : choice_type) (in custom pack_type at level 2).
Definition SCALE : nat :=
  (5918).
Program Definition scale
   : package (CEfset ([ret_5913_loc])) [interface
  #val #[ NEW ] : new__inp → new__out ] [interface
  #val #[ SCALE ] : scale_inp → scale_out ] :=
  ([package #def #[ SCALE ] (temp_inp : scale_inp) : scale_out { 
    let '(matrix_5899 , scalar_5908) := temp_inp : matrix_t '× scalar_t in
    #import {sig #[ NEW ] : new__inp → new__out } as new_ ;;
    let new_ := fun x_0 x_1 x_2 => new_ (x_0,x_1,x_2) in
    ({ code  temp_5916 ←
        (ret (matrix_5899)) ;;
      let '(dim_5914, seq_5900) :=
        (temp_5916) : (dims_t '× seq scalar_t) in
       '(ret_5913 : seq int128) ←
          ( '(temp_5902 : uint_size) ←
              (seq_len (seq_5900)) ;;
             '(temp_5904 : mat_res_t) ←
              (seq_new_ (default : scalar_t) (temp_5902)) ;;
            ret (temp_5904)) ;;
        #put ret_5913_loc := ret_5913 ;;
       '(temp_5906 : uint_size) ←
        (seq_len (seq_5900)) ;;
       '(ret_5913 : (seq int128)) ←
        (foldi' (usize 0) (temp_5906) ret_5913 (L2 := CEfset ([ret_5913_loc])) (
              I2 := [interface #val #[ NEW ] : new__inp → new__out
              ]) (H_loc_incl := _) (H_opsig_incl := _) (fun i_5907 ret_5913 =>
            ({ code  '(ret_5913 : seq int128) ←
                ( '(temp_5910 : scalar_t) ←
                    (seq_index (seq_5900) (i_5907)) ;;
                   '(temp_5912 : scalar_t) ←
                    ((scalar_5908) .* (temp_5910)) ;;
                  ret (seq_upd ret_5913 (i_5907) (temp_5912))) ;;
              
              @ret ((seq int128)) (ret_5913) } : code (CEfset (
                  [ret_5913_loc])) [interface] _))) ;;
      
      @ret (((dim_type_t '× dim_type_t) '× seq int128)) (prod_ce(
          dim_5914,
          ret_5913
        )) } : code (CEfset ([ret_5913_loc])) [interface
      #val #[ NEW ] : new__inp → new__out ] _)
    }]).
Fail Next Obligation.
Program Definition package_scale : package _ _ _ :=
  (seq_link scale link_rest(package_new_)).
Fail Next Obligation.

Definition res_5941_loc : ChoiceEqualityLocation :=
  (((result int8 matrix_t) ; 5948%nat)).
Definition ret_5940_loc : ChoiceEqualityLocation :=
  ((seq int128 ; 5949%nat)).
Notation "'add_inp'" := (
  matrix_t '× matrix_t : choice_type) (in custom pack_type at level 2).
Notation "'add_out'" := (
  mat_res_t : choice_type) (in custom pack_type at level 2).
Definition ADD : nat :=
  (5950).
Program Definition add
   : package (CEfset ([ret_5940_loc ; res_5941_loc])) [interface
  #val #[ NEW ] : new__inp → new__out ] [interface
  #val #[ ADD ] : add_inp → add_out ] :=
  ([package #def #[ ADD ] (temp_inp : add_inp) : add_out { 
    let '(matrix_1_5919 , matrix_2_5920) := temp_inp : matrix_t '× matrix_t in
    #import {sig #[ NEW ] : new__inp → new__out } as new_ ;;
    let new_ := fun x_0 x_1 x_2 => new_ (x_0,x_1,x_2) in
    ({ code  temp_5947 ←
        (ret (matrix_1_5919)) ;;
      let '(m1_dim_5926, m1_s_5921) :=
        (temp_5947) : (dims_t '× seq scalar_t) in
       temp_5945 ←
        (ret (matrix_2_5920)) ;;
      let '(m2_dim_5927, m2_s_5936) :=
        (temp_5945) : (dims_t '× seq scalar_t) in
       '(ret_5940 : seq int128) ←
          ( '(temp_5923 : uint_size) ←
              (seq_len (m1_s_5921)) ;;
             '(temp_5925 : mat_res_t) ←
              (seq_new_ (default : scalar_t) (temp_5923)) ;;
            ret (temp_5925)) ;;
        #put ret_5940_loc := ret_5940 ;;
       '(res_5941 : (result int8 matrix_t)) ←
          (ret (@inr matrix_t int8 (dimension_mismatch_v))) ;;
        #put res_5941_loc := res_5941 ;;
       '(temp_5929 : bool_ChoiceEquality) ←
        ((m1_dim_5926) =.? (m2_dim_5927)) ;;
       temp_5943 ←
        (if temp_5929:bool_ChoiceEquality
          then (*not state*) (let temp_then :=  '(temp_5931 : uint_size) ←
              (seq_len (m1_s_5921)) ;;
             '(ret_5940 : (seq int128)) ←
              (foldi' (usize 0) (temp_5931) ret_5940 (L2 := CEfset (
                      [ret_5940_loc ; res_5941_loc])) (
                    I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (fun i_5932 ret_5940 =>
                  ({ code  '(ret_5940 : seq int128) ←
                      ( '(temp_5934 : scalar_t) ←
                          (seq_index (m1_s_5921) (i_5932)) ;;
                         '(temp_5937 : scalar_t) ←
                          (seq_index (m2_s_5936) (i_5932)) ;;
                         '(temp_5939 : scalar_t) ←
                          ((temp_5934) .+ (temp_5937)) ;;
                        ret (seq_upd ret_5940 (i_5932) (temp_5939))) ;;
                    
                    @ret ((seq int128)) (ret_5940) } : code (CEfset (
                        [ret_5940_loc ; res_5941_loc])) [interface] _))) ;;
            
             '(res_5941 : (result int8 matrix_t)) ←
                ((ret (@inl matrix_t int8 (prod_ce(m1_dim_5926, ret_5940))))) ;;
              #put res_5941_loc := res_5941 ;;
            
            @ret ((seq int128 '× (result int8 matrix_t))) (prod_ce(
                ret_5940,
                res_5941
              )) in
            ({ code temp_then } : code (CEfset (
                  [ret_5940_loc ; res_5941_loc])) [interface] _))
          else @ret ((seq int128 '× (result int8 matrix_t))) (prod_ce(
              ret_5940,
              res_5941
            ))) ;;
      let '(ret_5940, res_5941) :=
        (temp_5943) : (seq int128 '× (result int8 matrix_t)) in
      
      @ret ((result int8 matrix_t)) (res_5941) } : code (CEfset (
          [ret_5940_loc ; res_5941_loc])) [interface
      #val #[ NEW ] : new__inp → new__out ] _)
    }]).
Fail Next Obligation.
Program Definition package_add : package _ _ _ :=
  (seq_link add link_rest(package_new_)).
Fail Next Obligation.

Definition ret_5972_loc : ChoiceEqualityLocation :=
  ((seq int128 ; 5980%nat)).
Definition res_5973_loc : ChoiceEqualityLocation :=
  (((result int8 matrix_t) ; 5981%nat)).
Notation "'sub_inp'" := (
  matrix_t '× matrix_t : choice_type) (in custom pack_type at level 2).
Notation "'sub_out'" := (
  mat_res_t : choice_type) (in custom pack_type at level 2).
Definition SUB : nat :=
  (5982).
Program Definition sub
   : package (CEfset ([ret_5972_loc ; res_5973_loc])) [interface
  #val #[ NEW ] : new__inp → new__out ] [interface
  #val #[ SUB ] : sub_inp → sub_out ] :=
  ([package #def #[ SUB ] (temp_inp : sub_inp) : sub_out { 
    let '(matrix_1_5951 , matrix_2_5952) := temp_inp : matrix_t '× matrix_t in
    #import {sig #[ NEW ] : new__inp → new__out } as new_ ;;
    let new_ := fun x_0 x_1 x_2 => new_ (x_0,x_1,x_2) in
    ({ code  temp_5979 ←
        (ret (matrix_1_5951)) ;;
      let '(m1_dim_5958, m1_s_5953) :=
        (temp_5979) : (dims_t '× seq scalar_t) in
       temp_5977 ←
        (ret (matrix_2_5952)) ;;
      let '(m2_dim_5959, m2_s_5968) :=
        (temp_5977) : (dims_t '× seq scalar_t) in
       '(ret_5972 : seq int128) ←
          ( '(temp_5955 : uint_size) ←
              (seq_len (m1_s_5953)) ;;
             '(temp_5957 : mat_res_t) ←
              (seq_new_ (default : scalar_t) (temp_5955)) ;;
            ret (temp_5957)) ;;
        #put ret_5972_loc := ret_5972 ;;
       '(res_5973 : (result int8 matrix_t)) ←
          (ret (@inr matrix_t int8 (dimension_mismatch_v))) ;;
        #put res_5973_loc := res_5973 ;;
       '(temp_5961 : bool_ChoiceEquality) ←
        ((m1_dim_5958) =.? (m2_dim_5959)) ;;
       temp_5975 ←
        (if temp_5961:bool_ChoiceEquality
          then (*not state*) (let temp_then :=  '(temp_5963 : uint_size) ←
              (seq_len (m1_s_5953)) ;;
             '(ret_5972 : (seq int128)) ←
              (foldi' (usize 0) (temp_5963) ret_5972 (L2 := CEfset (
                      [ret_5972_loc ; res_5973_loc])) (
                    I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (fun i_5964 ret_5972 =>
                  ({ code  '(ret_5972 : seq int128) ←
                      ( '(temp_5966 : scalar_t) ←
                          (seq_index (m1_s_5953) (i_5964)) ;;
                         '(temp_5969 : scalar_t) ←
                          (seq_index (m2_s_5968) (i_5964)) ;;
                         '(temp_5971 : scalar_t) ←
                          ((temp_5966) .- (temp_5969)) ;;
                        ret (seq_upd ret_5972 (i_5964) (temp_5971))) ;;
                    
                    @ret ((seq int128)) (ret_5972) } : code (CEfset (
                        [ret_5972_loc ; res_5973_loc])) [interface] _))) ;;
            
             '(res_5973 : (result int8 matrix_t)) ←
                ((ret (@inl matrix_t int8 (prod_ce(m1_dim_5958, ret_5972))))) ;;
              #put res_5973_loc := res_5973 ;;
            
            @ret ((seq int128 '× (result int8 matrix_t))) (prod_ce(
                ret_5972,
                res_5973
              )) in
            ({ code temp_then } : code (CEfset (
                  [ret_5972_loc ; res_5973_loc])) [interface] _))
          else @ret ((seq int128 '× (result int8 matrix_t))) (prod_ce(
              ret_5972,
              res_5973
            ))) ;;
      let '(ret_5972, res_5973) :=
        (temp_5975) : (seq int128 '× (result int8 matrix_t)) in
      
      @ret ((result int8 matrix_t)) (res_5973) } : code (CEfset (
          [ret_5972_loc ; res_5973_loc])) [interface
      #val #[ NEW ] : new__inp → new__out ] _)
    }]).
Fail Next Obligation.
Program Definition package_sub : package _ _ _ :=
  (seq_link sub link_rest(package_new_)).
Fail Next Obligation.

Definition ret_6004_loc : ChoiceEqualityLocation :=
  ((seq int128 ; 6012%nat)).
Definition res_6005_loc : ChoiceEqualityLocation :=
  (((result int8 matrix_t) ; 6013%nat)).
Notation "'component_mul_inp'" := (
  matrix_t '× matrix_t : choice_type) (in custom pack_type at level 2).
Notation "'component_mul_out'" := (
  mat_res_t : choice_type) (in custom pack_type at level 2).
Definition COMPONENT_MUL : nat :=
  (6014).
Program Definition component_mul
   : package (CEfset ([ret_6004_loc ; res_6005_loc])) [interface
  #val #[ NEW ] : new__inp → new__out ] [interface
  #val #[ COMPONENT_MUL ] : component_mul_inp → component_mul_out ] :=
  (
    [package #def #[ COMPONENT_MUL ] (temp_inp : component_mul_inp) : component_mul_out { 
    let '(matrix_1_5983 , matrix_2_5984) := temp_inp : matrix_t '× matrix_t in
    #import {sig #[ NEW ] : new__inp → new__out } as new_ ;;
    let new_ := fun x_0 x_1 x_2 => new_ (x_0,x_1,x_2) in
    ({ code  temp_6011 ←
        (ret (matrix_1_5983)) ;;
      let '(m1_dim_5990, m1_s_5985) :=
        (temp_6011) : (dims_t '× seq scalar_t) in
       temp_6009 ←
        (ret (matrix_2_5984)) ;;
      let '(m2_dim_5991, m2_s_6000) :=
        (temp_6009) : (dims_t '× seq scalar_t) in
       '(ret_6004 : seq int128) ←
          ( '(temp_5987 : uint_size) ←
              (seq_len (m1_s_5985)) ;;
             '(temp_5989 : mat_res_t) ←
              (seq_new_ (default : scalar_t) (temp_5987)) ;;
            ret (temp_5989)) ;;
        #put ret_6004_loc := ret_6004 ;;
       '(res_6005 : (result int8 matrix_t)) ←
          (ret (@inr matrix_t int8 (dimension_mismatch_v))) ;;
        #put res_6005_loc := res_6005 ;;
       '(temp_5993 : bool_ChoiceEquality) ←
        ((m1_dim_5990) =.? (m2_dim_5991)) ;;
       temp_6007 ←
        (if temp_5993:bool_ChoiceEquality
          then (*not state*) (let temp_then :=  '(temp_5995 : uint_size) ←
              (seq_len (m1_s_5985)) ;;
             '(ret_6004 : (seq int128)) ←
              (foldi' (usize 0) (temp_5995) ret_6004 (L2 := CEfset (
                      [ret_6004_loc ; res_6005_loc])) (
                    I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (fun i_5996 ret_6004 =>
                  ({ code  '(ret_6004 : seq int128) ←
                      ( '(temp_5998 : scalar_t) ←
                          (seq_index (m1_s_5985) (i_5996)) ;;
                         '(temp_6001 : scalar_t) ←
                          (seq_index (m2_s_6000) (i_5996)) ;;
                         '(temp_6003 : scalar_t) ←
                          ((temp_5998) .* (temp_6001)) ;;
                        ret (seq_upd ret_6004 (i_5996) (temp_6003))) ;;
                    
                    @ret ((seq int128)) (ret_6004) } : code (CEfset (
                        [ret_6004_loc ; res_6005_loc])) [interface] _))) ;;
            
             '(res_6005 : (result int8 matrix_t)) ←
                ((ret (@inl matrix_t int8 (prod_ce(m1_dim_5990, ret_6004))))) ;;
              #put res_6005_loc := res_6005 ;;
            
            @ret ((seq int128 '× (result int8 matrix_t))) (prod_ce(
                ret_6004,
                res_6005
              )) in
            ({ code temp_then } : code (CEfset (
                  [ret_6004_loc ; res_6005_loc])) [interface] _))
          else @ret ((seq int128 '× (result int8 matrix_t))) (prod_ce(
              ret_6004,
              res_6005
            ))) ;;
      let '(ret_6004, res_6005) :=
        (temp_6007) : (seq int128 '× (result int8 matrix_t)) in
      
      @ret ((result int8 matrix_t)) (res_6005) } : code (CEfset (
          [ret_6004_loc ; res_6005_loc])) [interface
      #val #[ NEW ] : new__inp → new__out ] _)
    }]).
Fail Next Obligation.
Program Definition package_component_mul : package _ _ _ :=
  (seq_link component_mul link_rest(package_new_)).
Fail Next Obligation.

Definition acc_6046_loc : ChoiceEqualityLocation :=
  ((int128 ; 6074%nat)).
Definition ret_6059_loc : ChoiceEqualityLocation :=
  ((seq int128 ; 6075%nat)).
Definition res_6060_loc : ChoiceEqualityLocation :=
  (((result int8 matrix_t) ; 6076%nat)).
Notation "'mul_inp'" := (
  matrix_t '× matrix_t : choice_type) (in custom pack_type at level 2).
Notation "'mul_out'" := (
  mat_res_t : choice_type) (in custom pack_type at level 2).
Definition MUL : nat :=
  (6077).
Program Definition mul
   : package (CEfset ([ret_6059_loc ; res_6060_loc ; acc_6046_loc])) [interface
  #val #[ NEW ] : new__inp → new__out ] [interface
  #val #[ MUL ] : mul_inp → mul_out ] :=
  ([package #def #[ MUL ] (temp_inp : mul_inp) : mul_out { 
    let '(matrix_1_6015 , matrix_2_6016) := temp_inp : matrix_t '× matrix_t in
    #import {sig #[ NEW ] : new__inp → new__out } as new_ ;;
    let new_ := fun x_0 x_1 x_2 => new_ (x_0,x_1,x_2) in
    ({ code  temp_6073 ←
        (ret (matrix_1_6015)) ;;
      let '(dim_1_6017, seq_1_6049) :=
        (temp_6073) : (dims_t '× seq scalar_t) in
       temp_6071 ←
        (ret (matrix_2_6016)) ;;
      let '(dim_2_6018, seq_2_6053) :=
        (temp_6071) : (dims_t '× seq scalar_t) in
       temp_6069 ←
        (ret (dim_1_6017)) ;;
      let '(l_6019, m_6025) :=
        (temp_6069) : (dim_type_t '× dim_type_t) in
       temp_6067 ←
        (ret (dim_2_6018)) ;;
      let '(m_6026, n_6020) :=
        (temp_6067) : (dim_type_t '× dim_type_t) in
       '(ret_6059 : seq int128) ←
          ( '(temp_6022 : uint_size) ←
              ((l_6019) .* (n_6020)) ;;
             '(temp_6024 : mat_res_t) ←
              (seq_new_ (default : scalar_t) (temp_6022)) ;;
            ret (temp_6024)) ;;
        #put ret_6059_loc := ret_6059 ;;
       '(res_6060 : (result int8 matrix_t)) ←
          (ret (@inr matrix_t int8 (dimension_mismatch_v))) ;;
        #put res_6060_loc := res_6060 ;;
       '(temp_6028 : bool_ChoiceEquality) ←
        ((m_6025) =.? (m_6026)) ;;
       temp_6065 ←
        (if temp_6028:bool_ChoiceEquality
          then (*not state*) (let temp_then :=  '(ret_6059 : (seq int128)) ←
              (foldi' (usize 0) (l_6019) ret_6059 (L2 := CEfset (
                      [ret_6059_loc ; res_6060_loc ; acc_6046_loc])) (
                    I2 := [interface #val #[ NEW ] : new__inp → new__out
                    ]) (H_loc_incl := _) (H_opsig_incl := _) (fun i_6031 ret_6059 =>
                  ({ code  '(ret_6059 : (seq int128)) ←
                      (foldi' (usize 0) (n_6020) ret_6059 (L2 := CEfset (
                              [ret_6059_loc ; res_6060_loc ; acc_6046_loc])) (
                            I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (fun j_6034 ret_6059 =>
                          ({ code  '(acc_6046 : int128) ←
                                ( temp_6030 ←
                                    (pub_int128_zero ) ;;
                                  ret (temp_6030)) ;;
                              #put acc_6046_loc := acc_6046 ;;
                             '(index_6061 : uint_size) ←
                              ( '(temp_6033 : uint_size) ←
                                  ((i_6031) .* (n_6020)) ;;
                                 '(temp_6036 : uint_size) ←
                                  ((temp_6033) .+ (j_6034)) ;;
                                ret (temp_6036)) ;;
                             '(acc_6046 : (int128)) ←
                              (foldi' (usize 0) (m_6025) acc_6046 (
                                    L2 := CEfset (
                                      [ret_6059_loc ; res_6060_loc ; acc_6046_loc])) (
                                    I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (fun k_6039 acc_6046 =>
                                  ({ code  '(index_1_6047 : uint_size) ←
                                      ( '(temp_6038 : uint_size) ←
                                          ((i_6031) .* (m_6025)) ;;
                                         '(temp_6041 : uint_size) ←
                                          ((temp_6038) .+ (k_6039)) ;;
                                        ret (temp_6041)) ;;
                                     '(index_2_6051 : uint_size) ←
                                      ( '(temp_6043 : uint_size) ←
                                          ((k_6039) .* (n_6020)) ;;
                                         '(temp_6045 : uint_size) ←
                                          ((temp_6043) .+ (j_6034)) ;;
                                        ret (temp_6045)) ;;
                                     '(acc_6046 : int128) ←
                                        (( '(temp_6050 : scalar_t) ←
                                              (seq_index (seq_1_6049) (
                                                  index_1_6047)) ;;
                                             '(temp_6054 : scalar_t) ←
                                              (seq_index (seq_2_6053) (
                                                  index_2_6051)) ;;
                                             '(temp_6056 : scalar_t) ←
                                              ((temp_6050) .* (temp_6054)) ;;
                                             '(temp_6058 : int128) ←
                                              ((acc_6046) .+ (temp_6056)) ;;
                                            ret (temp_6058))) ;;
                                      #put acc_6046_loc := acc_6046 ;;
                                    
                                    @ret ((int128)) (acc_6046) } : code (
                                      CEfset (
                                        [ret_6059_loc ; res_6060_loc ; acc_6046_loc])) [interface] _))) ;;
                            
                             '(ret_6059 : seq int128) ←
                              (ret (seq_upd ret_6059 (index_6061) (
                                    acc_6046))) ;;
                            
                            @ret ((seq int128)) (ret_6059) } : code (CEfset (
                                [ret_6059_loc ; res_6060_loc ; acc_6046_loc])) [interface] _))) ;;
                    
                    @ret ((seq int128)) (ret_6059) } : code (CEfset (
                        [ret_6059_loc ; res_6060_loc ; acc_6046_loc])) [interface] _))) ;;
            
             '(res_6060 : (result int8 matrix_t)) ←
                (( '(temp_6063 : mat_res_t) ←
                      (new_ (l_6019) (n_6020) (ret_6059)) ;;
                    ret (temp_6063))) ;;
              #put res_6060_loc := res_6060 ;;
            
            @ret ((seq int128 '× (result int8 matrix_t))) (prod_ce(
                ret_6059,
                res_6060
              )) in
            ({ code temp_then } : code (CEfset (
                  [ret_6059_loc ; res_6060_loc ; acc_6046_loc])) [interface
              #val #[ NEW ] : new__inp → new__out ] _))
          else @ret ((seq int128 '× (result int8 matrix_t))) (prod_ce(
              ret_6059,
              res_6060
            ))) ;;
      let '(ret_6059, res_6060) :=
        (temp_6065) : (seq int128 '× (result int8 matrix_t)) in
      
      @ret ((result int8 matrix_t)) (res_6060) } : code (CEfset (
          [ret_6059_loc ; res_6060_loc ; acc_6046_loc])) [interface
      #val #[ NEW ] : new__inp → new__out ] _)
    }]).
Fail Next Obligation.
Program Definition package_mul : package _ _ _ :=
  (seq_link mul link_rest(package_new_)).
Fail Next Obligation.

