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


Notation "'dim_type_t'" := (uint_size) : hacspec_scope.

Notation "'scalar_t'" := (int128) : hacspec_scope.

Notation "'dims_t'" := ((dim_type_t '× dim_type_t)) : hacspec_scope.

Notation "'matrix_t'" := ((dims_t '× seq scalar_t)) : hacspec_scope.

Notation "'mat_res_t'" := ((result int8 matrix_t)) : hacspec_scope.

Notation "'scal_res_t'" := ((result int8 scalar_t)) : hacspec_scope.

Definition dimension_sequence_length_mismatch_v : int8 :=
  @repr U8 10.

Definition index_out_of_bounds_v : int8 :=
  @repr U8 11.

Definition slice_out_of_bounds_v : int8 :=
  @repr U8 12.

Definition dimension_mismatch_v : int8 :=
  @repr U8 13.


Notation "'new__inp'" :=(
  dim_type_t '× dim_type_t '× seq scalar_t : choice_type) (in custom pack_type at level 2).
Notation "'new__inp'" :=(
  dim_type_t '× dim_type_t '× seq scalar_t : ChoiceEquality) (at level 2).
Notation "'new__out'" :=(
  mat_res_t : choice_type) (in custom pack_type at level 2).
Notation "'new__out'" :=(mat_res_t : ChoiceEquality) (at level 2).
Definition NEW : nat :=
  1120.
Program Definition new_
  : both_package (fset.fset0) [interface] [(NEW,(new__inp,new__out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(
      rows_1118 , cols_1119 , seq_1117) := temp_inp : dim_type_t '× dim_type_t '× seq scalar_t in
    
    ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          if is_pure (I := [interface]) (((seq_len (
                  lift_to_both0 seq_1117)) >.? (lift_to_both0 (usize 0))) && (((
                  lift_to_both0 rows_1118) .* (lift_to_both0 cols_1119)) =.? (
                seq_len (lift_to_both0 seq_1117))))
          then @Ok matrix_t int8 (prod_b(
              prod_b(lift_to_both0 rows_1118, lift_to_both0 cols_1119),
              lift_to_both0 seq_1117
            ))
          else @Err matrix_t int8 (
            lift_to_both0 dimension_sequence_length_mismatch_v))
        ) : both (fset.fset0) [interface] (mat_res_t)))in
  both_package' _ _ (NEW,(new__inp,new__out)) temp_package_both.
Fail Next Obligation.

Definition ret_1121_loc : ChoiceEqualityLocation :=
  (seq int128 ; 1122%nat).
Notation "'repeat_inp'" :=(
  dim_type_t '× dim_type_t '× scalar_t : choice_type) (in custom pack_type at level 2).
Notation "'repeat_inp'" :=(
  dim_type_t '× dim_type_t '× scalar_t : ChoiceEquality) (at level 2).
Notation "'repeat_out'" :=(
  matrix_t : choice_type) (in custom pack_type at level 2).
Notation "'repeat_out'" :=(matrix_t : ChoiceEquality) (at level 2).
Definition REPEAT : nat :=
  1127.
Program Definition repeat
  : both_package (CEfset ([ret_1121_loc])) [interface
  #val #[ NEW ] : new__inp → new__out ] [(REPEAT,(repeat_inp,repeat_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(
      n_1123 , m_1124 , scalar_1126) := temp_inp : dim_type_t '× dim_type_t '× scalar_t in
    
    let new_ := fun x_0 x_1 x_2 => package_both new_ (x_0,x_1,x_2) in
    ((letbm ret_1121 : seq int128 loc( ret_1121_loc ) :=
          seq_new_ (default : scalar_t) ((lift_to_both0 n_1123) .* (
              lift_to_both0 m_1124)) in
        letb ret_1121 :=
          foldi_both' (lift_to_both0 (usize 0)) ((lift_to_both0 n_1123) .* (
                lift_to_both0 m_1124)) ret_1121 (L := (CEfset (
                [ret_1121_loc]))) (I := ([interface
              #val #[ NEW ] : new__inp → new__out ])) (fun i_1125 ret_1121 =>
            letb ret_1121 : seq int128 :=
              seq_upd ret_1121 (lift_to_both0 i_1125) (is_pure (
                  lift_to_both0 scalar_1126)) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 ret_1121)
            ) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
            prod_b(lift_to_both0 n_1123, lift_to_both0 m_1124),
            lift_to_both0 ret_1121
          ))
        ) : both (CEfset ([ret_1121_loc])) [interface
      #val #[ NEW ] : new__inp → new__out ] (matrix_t)))in
  both_package' _ _ (REPEAT,(repeat_inp,repeat_out)) temp_package_both.
Fail Next Obligation.


Notation "'zeros_inp'" :=(
  dim_type_t '× dim_type_t : choice_type) (in custom pack_type at level 2).
Notation "'zeros_inp'" :=(
  dim_type_t '× dim_type_t : ChoiceEquality) (at level 2).
Notation "'zeros_out'" :=(
  matrix_t : choice_type) (in custom pack_type at level 2).
Notation "'zeros_out'" :=(matrix_t : ChoiceEquality) (at level 2).
Definition ZEROS : nat :=
  1130.
Program Definition zeros
  : both_package (CEfset ([])) [interface
  #val #[ REPEAT ] : repeat_inp → repeat_out ] [(ZEROS,(
      zeros_inp,zeros_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(n_1128 , m_1129) := temp_inp : dim_type_t '× dim_type_t in
    
    let repeat := fun x_0 x_1 x_2 => package_both repeat (x_0,x_1,x_2) in
    ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (repeat (
            lift_to_both0 n_1128) (lift_to_both0 m_1129) (pub_int128_zero ))
        ) : both (CEfset ([])) [interface
      #val #[ REPEAT ] : repeat_inp → repeat_out ] (matrix_t)))in
  both_package' _ _ (ZEROS,(zeros_inp,zeros_out)) temp_package_both.
Fail Next Obligation.


Notation "'ones_inp'" :=(
  dim_type_t '× dim_type_t : choice_type) (in custom pack_type at level 2).
Notation "'ones_inp'" :=(
  dim_type_t '× dim_type_t : ChoiceEquality) (at level 2).
Notation "'ones_out'" :=(
  matrix_t : choice_type) (in custom pack_type at level 2).
Notation "'ones_out'" :=(matrix_t : ChoiceEquality) (at level 2).
Definition ONES : nat :=
  1133.
Program Definition ones
  : both_package (CEfset ([])) [interface
  #val #[ REPEAT ] : repeat_inp → repeat_out ] [(ONES,(ones_inp,ones_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(n_1131 , m_1132) := temp_inp : dim_type_t '× dim_type_t in
    
    let repeat := fun x_0 x_1 x_2 => package_both repeat (x_0,x_1,x_2) in
    ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (repeat (
            lift_to_both0 n_1131) (lift_to_both0 m_1132) (pub_int128_one ))
        ) : both (CEfset ([])) [interface
      #val #[ REPEAT ] : repeat_inp → repeat_out ] (matrix_t)))in
  both_package' _ _ (ONES,(ones_inp,ones_out)) temp_package_both.
Fail Next Obligation.

Definition ret_1134_loc : ChoiceEqualityLocation :=
  (seq int128 ; 1135%nat).
Notation "'identity_inp'" :=(
  dim_type_t '× dim_type_t : choice_type) (in custom pack_type at level 2).
Notation "'identity_inp'" :=(
  dim_type_t '× dim_type_t : ChoiceEquality) (at level 2).
Notation "'identity_out'" :=(
  matrix_t : choice_type) (in custom pack_type at level 2).
Notation "'identity_out'" :=(matrix_t : ChoiceEquality) (at level 2).
Definition IDENTITY : nat :=
  1140.
Program Definition identity
  : both_package (CEfset ([ret_1134_loc])) [interface
  #val #[ MIN ] : min_inp → min_out ; #val #[ NEW ] : new__inp → new__out
  ] [(IDENTITY,(identity_inp,identity_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(n_1136 , m_1137) := temp_inp : dim_type_t '× dim_type_t in
    
    let min := fun x_0 x_1 => package_both min (x_0,x_1) in
    let new_ := fun x_0 x_1 x_2 => package_both new_ (x_0,x_1,x_2) in
    ((letbm ret_1134 : seq int128 loc( ret_1134_loc ) :=
          seq_new_ (default : scalar_t) ((lift_to_both0 n_1136) .* (
              lift_to_both0 m_1137)) in
        letb ret_1134 :=
          foldi_both' (lift_to_both0 (usize 0)) (min (lift_to_both0 n_1136) (
                lift_to_both0 m_1137)) ret_1134 (L := (CEfset (
                [ret_1134_loc]))) (I := ([interface
              #val #[ MIN ] : min_inp → min_out ;
              #val #[ NEW ] : new__inp → new__out ])) (fun i_1138 ret_1134 =>
            letb index_1139 : uint_size :=
              ((lift_to_both0 i_1138) .* (min (lift_to_both0 n_1136) (
                    lift_to_both0 m_1137))) .+ (lift_to_both0 i_1138) in
            letb ret_1134 : seq int128 :=
              seq_upd ret_1134 (lift_to_both0 index_1139) (is_pure (
                  pub_int128_one )) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 ret_1134)
            ) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
            prod_b(lift_to_both0 n_1136, lift_to_both0 m_1137),
            lift_to_both0 ret_1134
          ))
        ) : both (CEfset ([ret_1134_loc])) [interface
      #val #[ MIN ] : min_inp → min_out ;
      #val #[ NEW ] : new__inp → new__out ] (matrix_t)))in
  both_package' _ _ (IDENTITY,(identity_inp,identity_out)) temp_package_both.
Fail Next Obligation.


Notation "'index_inp'" :=(
  matrix_t '× dim_type_t '× dim_type_t : choice_type) (in custom pack_type at level 2).
Notation "'index_inp'" :=(
  matrix_t '× dim_type_t '× dim_type_t : ChoiceEquality) (at level 2).
Notation "'index_out'" :=(
  scal_res_t : choice_type) (in custom pack_type at level 2).
Notation "'index_out'" :=(scal_res_t : ChoiceEquality) (at level 2).
Definition INDEX : nat :=
  1149.
Program Definition index
  : both_package (fset.fset0) [interface] [(INDEX,(index_inp,index_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(
      m_1141 , i_1146 , j_1147) := temp_inp : matrix_t '× dim_type_t '× dim_type_t in
    
    ((letb '(dim_1142, seq_1143) : (dims_t '× seq scalar_t) :=
          lift_to_both0 m_1141 in
        letb '(rows_1144, cols_1145) : (dim_type_t '× dim_type_t) :=
          lift_to_both0 dim_1142 in
        letb index_1148 : uint_size :=
          ((lift_to_both0 i_1146) .* (lift_to_both0 cols_1145)) .+ (
            lift_to_both0 j_1147) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          if is_pure (I := [interface]) ((lift_to_both0 index_1148) >=.? ((
                lift_to_both0 rows_1144) .* (lift_to_both0 cols_1145)))
          then @Err scalar_t int8 (lift_to_both0 index_out_of_bounds_v)
          else @Ok scalar_t int8 (seq_index (seq_1143) (
              lift_to_both0 index_1148)))
        ) : both (fset.fset0) [interface] (scal_res_t)))in
  both_package' _ _ (INDEX,(index_inp,index_out)) temp_package_both.
Fail Next Obligation.

Definition ret_1150_loc : ChoiceEqualityLocation :=
  (seq int128 ; 1151%nat).
Notation "'transpose_inp'" :=(
  matrix_t : choice_type) (in custom pack_type at level 2).
Notation "'transpose_inp'" :=(matrix_t : ChoiceEquality) (at level 2).
Notation "'transpose_out'" :=(
  matrix_t : choice_type) (in custom pack_type at level 2).
Notation "'transpose_out'" :=(matrix_t : ChoiceEquality) (at level 2).
Definition TRANSPOSE : nat :=
  1161.
Program Definition transpose
  : both_package (CEfset ([ret_1150_loc])) [interface
  #val #[ NEW ] : new__inp → new__out ] [(TRANSPOSE,(
      transpose_inp,transpose_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(matrix_1152) := temp_inp : matrix_t in
    
    let new_ := fun x_0 x_1 x_2 => package_both new_ (x_0,x_1,x_2) in
    ((letb '(dim_1153, seq_1154) : (dims_t '× seq scalar_t) :=
          lift_to_both0 matrix_1152 in
        letb '(rows_1155, cols_1156) : (dim_type_t '× dim_type_t) :=
          lift_to_both0 dim_1153 in
        letbm ret_1150 : seq int128 loc( ret_1150_loc ) :=
          seq_new_ (default : scalar_t) (seq_len (lift_to_both0 seq_1154)) in
        letb ret_1150 :=
          foldi_both' (lift_to_both0 (usize 0)) (
              lift_to_both0 rows_1155) ret_1150 (L := (CEfset (
                [ret_1150_loc]))) (I := ([interface
              #val #[ NEW ] : new__inp → new__out ])) (fun i_1157 ret_1150 =>
            letb ret_1150 :=
              foldi_both' (lift_to_both0 (usize 0)) (
                  lift_to_both0 cols_1156) ret_1150 (L := (CEfset (
                    [ret_1150_loc]))) (I := (
                  [interface])) (fun j_1158 ret_1150 =>
                letb seq_index_1159 : uint_size :=
                  ((lift_to_both0 i_1157) .* (lift_to_both0 cols_1156)) .+ (
                    lift_to_both0 j_1158) in
                letb ret_index_1160 : uint_size :=
                  ((lift_to_both0 j_1158) .* (lift_to_both0 rows_1155)) .+ (
                    lift_to_both0 i_1157) in
                letb ret_1150 : seq int128 :=
                  seq_upd ret_1150 (lift_to_both0 ret_index_1160) (is_pure (
                      seq_index (seq_1154) (lift_to_both0 seq_index_1159))) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                  lift_to_both0 ret_1150)
                ) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 ret_1150)
            ) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
            prod_b(lift_to_both0 cols_1156, lift_to_both0 rows_1155),
            lift_to_both0 ret_1150
          ))
        ) : both (CEfset ([ret_1150_loc])) [interface
      #val #[ NEW ] : new__inp → new__out ] (matrix_t)))in
  both_package' _ _ (TRANSPOSE,(transpose_inp,transpose_out)) temp_package_both.
Fail Next Obligation.

Definition ret_1162_loc : ChoiceEqualityLocation :=
  (seq int128 ; 1164%nat).
Definition res_1163_loc : ChoiceEqualityLocation :=
  ((result (int8) (matrix_t)) ; 1165%nat).
Notation "'slice_inp'" :=(
  matrix_t '× dims_t '× dims_t : choice_type) (in custom pack_type at level 2).
Notation "'slice_inp'" :=(
  matrix_t '× dims_t '× dims_t : ChoiceEquality) (at level 2).
Notation "'slice_out'" :=(
  mat_res_t : choice_type) (in custom pack_type at level 2).
Notation "'slice_out'" :=(mat_res_t : ChoiceEquality) (at level 2).
Definition SLICE : nat :=
  1182.
Program Definition slice
  : both_package (CEfset ([ret_1162_loc ; res_1163_loc])) [interface
  #val #[ NEW ] : new__inp → new__out ] [(SLICE,(slice_inp,slice_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(
      matrix_1166 , start_1171 , len_1174) := temp_inp : matrix_t '× dims_t '× dims_t in
    
    let new_ := fun x_0 x_1 x_2 => package_both new_ (x_0,x_1,x_2) in
    ((letb '(dim_1167, seq_1168) : (dims_t '× seq scalar_t) :=
          lift_to_both0 matrix_1166 in
        letb '(rows_1169, cols_1170) : (dim_type_t '× dim_type_t) :=
          lift_to_both0 dim_1167 in
        letb '(start_row_1172, start_col_1173) : (dim_type_t '× dim_type_t) :=
          lift_to_both0 start_1171 in
        letb '(len_rows_1175, len_cols_1176) : (dim_type_t '× dim_type_t) :=
          lift_to_both0 len_1174 in
        letb start_index_1177 : uint_size :=
          ((lift_to_both0 start_row_1172) .* (lift_to_both0 cols_1170)) .+ (
            lift_to_both0 start_col_1173) in
        letbm ret_1162 : seq int128 loc( ret_1162_loc ) :=
          seq_new_ (default : scalar_t) ((lift_to_both0 len_rows_1175) .* (
              lift_to_both0 len_cols_1176)) in
        letbm res_1163 : (result (int8) (matrix_t)) loc( res_1163_loc ) :=
          @Err matrix_t int8 (lift_to_both0 slice_out_of_bounds_v) in
        letb '(ret_1162, res_1163) :=
          if ((lift_to_both0 start_index_1177) .+ ((
                lift_to_both0 len_rows_1175) .* (
                lift_to_both0 len_cols_1176))) <=.? ((
              lift_to_both0 rows_1169) .* (
              lift_to_both0 cols_1170)) :bool_ChoiceEquality
          then lift_scope (L1 := CEfset (
            [ret_1162_loc ; res_1163_loc])) (L2 := CEfset (
            [ret_1162_loc ; res_1163_loc])) (I1 := [interface
          #val #[ NEW ] : new__inp → new__out ]) (I2 := [interface
          #val #[ NEW ] : new__inp → new__out
          ]) (H_loc_incl := _) (H_opsig_incl := _) (letb ret_1162 :=
              foldi_both' (lift_to_both0 (usize 0)) (
                  lift_to_both0 len_rows_1175) ret_1162 (L := (CEfset (
                    [ret_1162_loc ; res_1163_loc]))) (I := ([interface
                  #val #[ NEW ] : new__inp → new__out
                  ])) (fun i_1178 ret_1162 =>
                letb ret_1162 :=
                  foldi_both' (lift_to_both0 (usize 0)) (
                      lift_to_both0 len_cols_1176) ret_1162 (L := (CEfset (
                        [ret_1162_loc ; res_1163_loc]))) (I := (
                      [interface])) (fun j_1179 ret_1162 =>
                    letb ret_index_1180 : uint_size :=
                      ((lift_to_both0 i_1178) .* (
                          lift_to_both0 len_cols_1176)) .+ (
                        lift_to_both0 j_1179) in
                    letb seq_index_1181 : uint_size :=
                      (((lift_to_both0 start_row_1172) .+ (
                            lift_to_both0 i_1178)) .* (
                          lift_to_both0 cols_1170)) .+ ((
                          lift_to_both0 start_col_1173) .+ (
                          lift_to_both0 j_1179)) in
                    letb ret_1162 : seq int128 :=
                      seq_upd ret_1162 (lift_to_both0 ret_index_1180) (is_pure (
                          seq_index (seq_1168) (
                            lift_to_both0 seq_index_1181))) in
                    lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                      lift_to_both0 ret_1162)
                    ) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                  lift_to_both0 ret_1162)
                ) in
            letbm res_1163 loc( res_1163_loc ) :=
              new_ (lift_to_both0 len_rows_1175) (lift_to_both0 len_cols_1176) (
                lift_to_both0 ret_1162) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                lift_to_both0 ret_1162,
                lift_to_both0 res_1163
              ))
            )
          else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
              lift_to_both0 ret_1162,
              lift_to_both0 res_1163
            ))
           in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          lift_to_both0 res_1163)
        ) : both (CEfset ([ret_1162_loc ; res_1163_loc])) [interface
      #val #[ NEW ] : new__inp → new__out ] (mat_res_t)))in
  both_package' _ _ (SLICE,(slice_inp,slice_out)) temp_package_both.
Fail Next Obligation.

Definition ret_1183_loc : ChoiceEqualityLocation :=
  (seq int128 ; 1184%nat).
Notation "'scale_inp'" :=(
  matrix_t '× scalar_t : choice_type) (in custom pack_type at level 2).
Notation "'scale_inp'" :=(matrix_t '× scalar_t : ChoiceEquality) (at level 2).
Notation "'scale_out'" :=(
  matrix_t : choice_type) (in custom pack_type at level 2).
Notation "'scale_out'" :=(matrix_t : ChoiceEquality) (at level 2).
Definition SCALE : nat :=
  1190.
Program Definition scale
  : both_package (CEfset ([ret_1183_loc])) [interface
  #val #[ NEW ] : new__inp → new__out ] [(SCALE,(scale_inp,scale_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(matrix_1185 , scalar_1189) := temp_inp : matrix_t '× scalar_t in
    
    let new_ := fun x_0 x_1 x_2 => package_both new_ (x_0,x_1,x_2) in
    ((letb '(dim_1186, seq_1187) : (dims_t '× seq scalar_t) :=
          lift_to_both0 matrix_1185 in
        letbm ret_1183 : seq int128 loc( ret_1183_loc ) :=
          seq_new_ (default : scalar_t) (seq_len (lift_to_both0 seq_1187)) in
        letb ret_1183 :=
          foldi_both' (lift_to_both0 (usize 0)) (seq_len (
                lift_to_both0 seq_1187)) ret_1183 (L := (CEfset (
                [ret_1183_loc]))) (I := ([interface
              #val #[ NEW ] : new__inp → new__out ])) (fun i_1188 ret_1183 =>
            letb ret_1183 : seq int128 :=
              seq_upd ret_1183 (lift_to_both0 i_1188) (is_pure ((
                    lift_to_both0 scalar_1189) .* (seq_index (seq_1187) (
                      lift_to_both0 i_1188)))) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 ret_1183)
            ) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
            lift_to_both0 dim_1186,
            lift_to_both0 ret_1183
          ))
        ) : both (CEfset ([ret_1183_loc])) [interface
      #val #[ NEW ] : new__inp → new__out ] (matrix_t)))in
  both_package' _ _ (SCALE,(scale_inp,scale_out)) temp_package_both.
Fail Next Obligation.

Definition res_1192_loc : ChoiceEqualityLocation :=
  ((result (int8) (matrix_t)) ; 1193%nat).
Definition ret_1191_loc : ChoiceEqualityLocation :=
  (seq int128 ; 1194%nat).
Notation "'add_inp'" :=(
  matrix_t '× matrix_t : choice_type) (in custom pack_type at level 2).
Notation "'add_inp'" :=(matrix_t '× matrix_t : ChoiceEquality) (at level 2).
Notation "'add_out'" :=(
  mat_res_t : choice_type) (in custom pack_type at level 2).
Notation "'add_out'" :=(mat_res_t : ChoiceEquality) (at level 2).
Definition ADD : nat :=
  1202.
Program Definition add
  : both_package (CEfset ([ret_1191_loc ; res_1192_loc])) [interface
  #val #[ NEW ] : new__inp → new__out ] [(ADD,(add_inp,add_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(matrix_1_1195 , matrix_2_1198) := temp_inp : matrix_t '× matrix_t in
    
    let new_ := fun x_0 x_1 x_2 => package_both new_ (x_0,x_1,x_2) in
    ((letb '(m1_dim_1196, m1_s_1197) : (dims_t '× seq scalar_t) :=
          lift_to_both0 matrix_1_1195 in
        letb '(m2_dim_1199, m2_s_1200) : (dims_t '× seq scalar_t) :=
          lift_to_both0 matrix_2_1198 in
        letbm ret_1191 : seq int128 loc( ret_1191_loc ) :=
          seq_new_ (default : scalar_t) (seq_len (lift_to_both0 m1_s_1197)) in
        letbm res_1192 : (result (int8) (matrix_t)) loc( res_1192_loc ) :=
          @Err matrix_t int8 (lift_to_both0 dimension_mismatch_v) in
        letb '(ret_1191, res_1192) :=
          if (lift_to_both0 m1_dim_1196) =.? (
            lift_to_both0 m2_dim_1199) :bool_ChoiceEquality
          then lift_scope (L1 := CEfset (
            [ret_1191_loc ; res_1192_loc])) (L2 := CEfset (
            [ret_1191_loc ; res_1192_loc])) (I1 := [interface]) (I2 := [interface
          #val #[ NEW ] : new__inp → new__out
          ]) (H_loc_incl := _) (H_opsig_incl := _) (letb ret_1191 :=
              foldi_both' (lift_to_both0 (usize 0)) (seq_len (
                    lift_to_both0 m1_s_1197)) ret_1191 (L := (CEfset (
                    [ret_1191_loc ; res_1192_loc]))) (I := (
                  [interface])) (fun i_1201 ret_1191 =>
                letb ret_1191 : seq int128 :=
                  seq_upd ret_1191 (lift_to_both0 i_1201) (is_pure ((seq_index (
                          m1_s_1197) (lift_to_both0 i_1201)) .+ (seq_index (
                          m2_s_1200) (lift_to_both0 i_1201)))) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                  lift_to_both0 ret_1191)
                ) in
            letbm res_1192 loc( res_1192_loc ) :=
              @Ok matrix_t int8 (prod_b(
                  lift_to_both0 m1_dim_1196,
                  lift_to_both0 ret_1191
                )) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                lift_to_both0 ret_1191,
                lift_to_both0 res_1192
              ))
            )
          else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
              lift_to_both0 ret_1191,
              lift_to_both0 res_1192
            ))
           in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          lift_to_both0 res_1192)
        ) : both (CEfset ([ret_1191_loc ; res_1192_loc])) [interface
      #val #[ NEW ] : new__inp → new__out ] (mat_res_t)))in
  both_package' _ _ (ADD,(add_inp,add_out)) temp_package_both.
Fail Next Obligation.

Definition ret_1203_loc : ChoiceEqualityLocation :=
  (seq int128 ; 1205%nat).
Definition res_1204_loc : ChoiceEqualityLocation :=
  ((result (int8) (matrix_t)) ; 1206%nat).
Notation "'sub_inp'" :=(
  matrix_t '× matrix_t : choice_type) (in custom pack_type at level 2).
Notation "'sub_inp'" :=(matrix_t '× matrix_t : ChoiceEquality) (at level 2).
Notation "'sub_out'" :=(
  mat_res_t : choice_type) (in custom pack_type at level 2).
Notation "'sub_out'" :=(mat_res_t : ChoiceEquality) (at level 2).
Definition SUB : nat :=
  1214.
Program Definition sub
  : both_package (CEfset ([ret_1203_loc ; res_1204_loc])) [interface
  #val #[ NEW ] : new__inp → new__out ] [(SUB,(sub_inp,sub_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(matrix_1_1207 , matrix_2_1210) := temp_inp : matrix_t '× matrix_t in
    
    let new_ := fun x_0 x_1 x_2 => package_both new_ (x_0,x_1,x_2) in
    ((letb '(m1_dim_1208, m1_s_1209) : (dims_t '× seq scalar_t) :=
          lift_to_both0 matrix_1_1207 in
        letb '(m2_dim_1211, m2_s_1212) : (dims_t '× seq scalar_t) :=
          lift_to_both0 matrix_2_1210 in
        letbm ret_1203 : seq int128 loc( ret_1203_loc ) :=
          seq_new_ (default : scalar_t) (seq_len (lift_to_both0 m1_s_1209)) in
        letbm res_1204 : (result (int8) (matrix_t)) loc( res_1204_loc ) :=
          @Err matrix_t int8 (lift_to_both0 dimension_mismatch_v) in
        letb '(ret_1203, res_1204) :=
          if (lift_to_both0 m1_dim_1208) =.? (
            lift_to_both0 m2_dim_1211) :bool_ChoiceEquality
          then lift_scope (L1 := CEfset (
            [ret_1203_loc ; res_1204_loc])) (L2 := CEfset (
            [ret_1203_loc ; res_1204_loc])) (I1 := [interface]) (I2 := [interface
          #val #[ NEW ] : new__inp → new__out
          ]) (H_loc_incl := _) (H_opsig_incl := _) (letb ret_1203 :=
              foldi_both' (lift_to_both0 (usize 0)) (seq_len (
                    lift_to_both0 m1_s_1209)) ret_1203 (L := (CEfset (
                    [ret_1203_loc ; res_1204_loc]))) (I := (
                  [interface])) (fun i_1213 ret_1203 =>
                letb ret_1203 : seq int128 :=
                  seq_upd ret_1203 (lift_to_both0 i_1213) (is_pure ((seq_index (
                          m1_s_1209) (lift_to_both0 i_1213)) .- (seq_index (
                          m2_s_1212) (lift_to_both0 i_1213)))) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                  lift_to_both0 ret_1203)
                ) in
            letbm res_1204 loc( res_1204_loc ) :=
              @Ok matrix_t int8 (prod_b(
                  lift_to_both0 m1_dim_1208,
                  lift_to_both0 ret_1203
                )) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                lift_to_both0 ret_1203,
                lift_to_both0 res_1204
              ))
            )
          else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
              lift_to_both0 ret_1203,
              lift_to_both0 res_1204
            ))
           in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          lift_to_both0 res_1204)
        ) : both (CEfset ([ret_1203_loc ; res_1204_loc])) [interface
      #val #[ NEW ] : new__inp → new__out ] (mat_res_t)))in
  both_package' _ _ (SUB,(sub_inp,sub_out)) temp_package_both.
Fail Next Obligation.

Definition res_1216_loc : ChoiceEqualityLocation :=
  ((result (int8) (matrix_t)) ; 1217%nat).
Definition ret_1215_loc : ChoiceEqualityLocation :=
  (seq int128 ; 1218%nat).
Notation "'component_mul_inp'" :=(
  matrix_t '× matrix_t : choice_type) (in custom pack_type at level 2).
Notation "'component_mul_inp'" :=(
  matrix_t '× matrix_t : ChoiceEquality) (at level 2).
Notation "'component_mul_out'" :=(
  mat_res_t : choice_type) (in custom pack_type at level 2).
Notation "'component_mul_out'" :=(mat_res_t : ChoiceEquality) (at level 2).
Definition COMPONENT_MUL : nat :=
  1226.
Program Definition component_mul
  : both_package (CEfset ([ret_1215_loc ; res_1216_loc])) [interface
  #val #[ NEW ] : new__inp → new__out ] [(COMPONENT_MUL,(
      component_mul_inp,component_mul_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(matrix_1_1219 , matrix_2_1222) := temp_inp : matrix_t '× matrix_t in
    
    let new_ := fun x_0 x_1 x_2 => package_both new_ (x_0,x_1,x_2) in
    ((letb '(m1_dim_1220, m1_s_1221) : (dims_t '× seq scalar_t) :=
          lift_to_both0 matrix_1_1219 in
        letb '(m2_dim_1223, m2_s_1224) : (dims_t '× seq scalar_t) :=
          lift_to_both0 matrix_2_1222 in
        letbm ret_1215 : seq int128 loc( ret_1215_loc ) :=
          seq_new_ (default : scalar_t) (seq_len (lift_to_both0 m1_s_1221)) in
        letbm res_1216 : (result (int8) (matrix_t)) loc( res_1216_loc ) :=
          @Err matrix_t int8 (lift_to_both0 dimension_mismatch_v) in
        letb '(ret_1215, res_1216) :=
          if (lift_to_both0 m1_dim_1220) =.? (
            lift_to_both0 m2_dim_1223) :bool_ChoiceEquality
          then lift_scope (L1 := CEfset (
            [ret_1215_loc ; res_1216_loc])) (L2 := CEfset (
            [ret_1215_loc ; res_1216_loc])) (I1 := [interface]) (I2 := [interface
          #val #[ NEW ] : new__inp → new__out
          ]) (H_loc_incl := _) (H_opsig_incl := _) (letb ret_1215 :=
              foldi_both' (lift_to_both0 (usize 0)) (seq_len (
                    lift_to_both0 m1_s_1221)) ret_1215 (L := (CEfset (
                    [ret_1215_loc ; res_1216_loc]))) (I := (
                  [interface])) (fun i_1225 ret_1215 =>
                letb ret_1215 : seq int128 :=
                  seq_upd ret_1215 (lift_to_both0 i_1225) (is_pure ((seq_index (
                          m1_s_1221) (lift_to_both0 i_1225)) .* (seq_index (
                          m2_s_1224) (lift_to_both0 i_1225)))) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                  lift_to_both0 ret_1215)
                ) in
            letbm res_1216 loc( res_1216_loc ) :=
              @Ok matrix_t int8 (prod_b(
                  lift_to_both0 m1_dim_1220,
                  lift_to_both0 ret_1215
                )) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                lift_to_both0 ret_1215,
                lift_to_both0 res_1216
              ))
            )
          else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
              lift_to_both0 ret_1215,
              lift_to_both0 res_1216
            ))
           in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          lift_to_both0 res_1216)
        ) : both (CEfset ([ret_1215_loc ; res_1216_loc])) [interface
      #val #[ NEW ] : new__inp → new__out ] (mat_res_t)))in
  both_package' _ _ (COMPONENT_MUL,(
      component_mul_inp,component_mul_out)) temp_package_both.
Fail Next Obligation.

Definition res_1228_loc : ChoiceEqualityLocation :=
  ((result (int8) (matrix_t)) ; 1230%nat).
Definition acc_1229_loc : ChoiceEqualityLocation :=
  (int128 ; 1231%nat).
Definition ret_1227_loc : ChoiceEqualityLocation :=
  (seq int128 ; 1232%nat).
Notation "'mul_inp'" :=(
  matrix_t '× matrix_t : choice_type) (in custom pack_type at level 2).
Notation "'mul_inp'" :=(matrix_t '× matrix_t : ChoiceEquality) (at level 2).
Notation "'mul_out'" :=(
  mat_res_t : choice_type) (in custom pack_type at level 2).
Notation "'mul_out'" :=(mat_res_t : ChoiceEquality) (at level 2).
Definition MUL : nat :=
  1249.
Program Definition mul
  : both_package (CEfset (
      [ret_1227_loc ; res_1228_loc ; acc_1229_loc])) [interface
  #val #[ NEW ] : new__inp → new__out ] [(MUL,(mul_inp,mul_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(matrix_1_1233 , matrix_2_1236) := temp_inp : matrix_t '× matrix_t in
    
    let new_ := fun x_0 x_1 x_2 => package_both new_ (x_0,x_1,x_2) in
    ((letb '(dim_1_1234, seq_1_1235) : (dims_t '× seq scalar_t) :=
          lift_to_both0 matrix_1_1233 in
        letb '(dim_2_1237, seq_2_1238) : (dims_t '× seq scalar_t) :=
          lift_to_both0 matrix_2_1236 in
        letb '(l_1239, m_1240) : (dim_type_t '× dim_type_t) :=
          lift_to_both0 dim_1_1234 in
        letb '(m_1241, n_1242) : (dim_type_t '× dim_type_t) :=
          lift_to_both0 dim_2_1237 in
        letbm ret_1227 : seq int128 loc( ret_1227_loc ) :=
          seq_new_ (default : scalar_t) ((lift_to_both0 l_1239) .* (
              lift_to_both0 n_1242)) in
        letbm res_1228 : (result (int8) (matrix_t)) loc( res_1228_loc ) :=
          @Err matrix_t int8 (lift_to_both0 dimension_mismatch_v) in
        letb '(ret_1227, res_1228) :=
          if (lift_to_both0 m_1240) =.? (
            lift_to_both0 m_1241) :bool_ChoiceEquality
          then lift_scope (L1 := CEfset (
            [ret_1227_loc ; res_1228_loc ; acc_1229_loc])) (L2 := CEfset (
            [ret_1227_loc ; res_1228_loc ; acc_1229_loc])) (I1 := [interface
          #val #[ NEW ] : new__inp → new__out ]) (I2 := [interface
          #val #[ NEW ] : new__inp → new__out
          ]) (H_loc_incl := _) (H_opsig_incl := _) (letb ret_1227 :=
              foldi_both' (lift_to_both0 (usize 0)) (
                  lift_to_both0 l_1239) ret_1227 (L := (CEfset (
                    [ret_1227_loc ; res_1228_loc ; acc_1229_loc]))) (I := (
                  [interface #val #[ NEW ] : new__inp → new__out
                  ])) (fun i_1243 ret_1227 =>
                letb ret_1227 :=
                  foldi_both' (lift_to_both0 (usize 0)) (
                      lift_to_both0 n_1242) ret_1227 (L := (CEfset (
                        [ret_1227_loc ; res_1228_loc ; acc_1229_loc]))) (I := (
                      [interface])) (fun j_1244 ret_1227 =>
                    letbm acc_1229 : int128 loc( acc_1229_loc ) :=
                      pub_int128_zero  in
                    letb index_1245 : uint_size :=
                      ((lift_to_both0 i_1243) .* (lift_to_both0 n_1242)) .+ (
                        lift_to_both0 j_1244) in
                    letb acc_1229 :=
                      foldi_both' (lift_to_both0 (usize 0)) (
                          lift_to_both0 m_1240) acc_1229 (L := (CEfset (
                            [ret_1227_loc ; res_1228_loc ; acc_1229_loc]))) (I := (
                          [interface])) (fun k_1246 acc_1229 =>
                        letb index_1_1247 : uint_size :=
                          ((lift_to_both0 i_1243) .* (
                              lift_to_both0 m_1240)) .+ (
                            lift_to_both0 k_1246) in
                        letb index_2_1248 : uint_size :=
                          ((lift_to_both0 k_1246) .* (
                              lift_to_both0 n_1242)) .+ (
                            lift_to_both0 j_1244) in
                        letbm acc_1229 loc( acc_1229_loc ) :=
                          (lift_to_both0 acc_1229) .+ ((seq_index (seq_1_1235) (
                                lift_to_both0 index_1_1247)) .* (seq_index (
                                seq_2_1238) (lift_to_both0 index_2_1248))) in
                        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                          lift_to_both0 acc_1229)
                        ) in
                    letb ret_1227 : seq int128 :=
                      seq_upd ret_1227 (lift_to_both0 index_1245) (is_pure (
                          lift_to_both0 acc_1229)) in
                    lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                      lift_to_both0 ret_1227)
                    ) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                  lift_to_both0 ret_1227)
                ) in
            letbm res_1228 loc( res_1228_loc ) :=
              new_ (lift_to_both0 l_1239) (lift_to_both0 n_1242) (
                lift_to_both0 ret_1227) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                lift_to_both0 ret_1227,
                lift_to_both0 res_1228
              ))
            )
          else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
              lift_to_both0 ret_1227,
              lift_to_both0 res_1228
            ))
           in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          lift_to_both0 res_1228)
        ) : both (CEfset (
          [ret_1227_loc ; res_1228_loc ; acc_1229_loc])) [interface
      #val #[ NEW ] : new__inp → new__out ] (mat_res_t)))in
  both_package' _ _ (MUL,(mul_inp,mul_out)) temp_package_both.
Fail Next Obligation.

