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


Require Import Hacspec_Sha3.

Definition strobe_r_v : int8 :=
  @repr U8 166.

Definition flag_i_v : int8 :=
  @repr U8 1.

Definition flag_a_v : int8 :=
  ((@repr U8 1) shift_left (usize 1)).

Definition flag_c_v : int8 :=
  ((@repr U8 1) shift_left (usize 2)).

Definition flag_m_v : int8 :=
  ((@repr U8 1) shift_left (usize 4)).

Definition flag_k_v : int8 :=
  ((@repr U8 1) shift_left (usize 5)).

Notation "'state_uint64_t'" := (state_t) : hacspec_scope.

Definition state_uint8_t := nseq (uint8) (usize 200).

Notation "'strobe_t'" := ((state_uint8_t '× int8 '× int8 '× int8
)) : hacspec_scope.

Definition word_1251_loc : ChoiceEqualityLocation :=
  (uint64_word_t ; 1252%nat).
Definition new_state_1250_loc : ChoiceEqualityLocation :=
  (state_t ; 1253%nat).
Notation "'transmute_state_to_u64_inp'" :=(
  state_uint8_t : choice_type) (in custom pack_type at level 2).
Notation "'transmute_state_to_u64_inp'" :=(
  state_uint8_t : ChoiceEquality) (at level 2).
Notation "'transmute_state_to_u64_out'" :=(
  state_uint64_t : choice_type) (in custom pack_type at level 2).
Notation "'transmute_state_to_u64_out'" :=(
  state_uint64_t : ChoiceEquality) (at level 2).
Definition TRANSMUTE_STATE_TO_U64 : nat :=
  1257.
Program Definition transmute_state_to_u64 (state_1256 : state_uint8_t)
  : both (CEfset ([new_state_1250_loc ; word_1251_loc])) [interface] (
    state_uint64_t) :=
  ((letbm new_state_1250 : state_t loc( new_state_1250_loc ) :=
        array_new_ (default : uint64) (25) in
      letb new_state_1250 :=
        foldi_both' (lift_to_both0 (usize 0)) (array_len (
              lift_to_both0 new_state_1250)) new_state_1250 (L := (CEfset (
                [new_state_1250_loc ; word_1251_loc]))) (I := [interface]) (
            fun i_1254 new_state_1250 =>
            letbm word_1251 : uint64_word_t loc( word_1251_loc ) :=
              array_new_ (default : uint8) (8) in
            letb word_1251 :=
              foldi_both' (lift_to_both0 (usize 0)) (array_len (
                    lift_to_both0 word_1251)) word_1251 (L := (CEfset (
                      [new_state_1250_loc ; word_1251_loc]))) (
                  I := [interface]) (fun j_1255 word_1251 =>
                  letb word_1251 : uint64_word_t :=
                    array_upd word_1251 (lift_to_both0 j_1255) (is_pure (
                        array_index (state_1256) (((lift_to_both0 i_1254) .* (
                              lift_to_both0 (usize 8))) .+ (
                            lift_to_both0 j_1255)))) in
                  lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                    lift_to_both0 word_1251)
                  ) in
            letb new_state_1250 : state_t :=
              array_upd new_state_1250 (lift_to_both0 i_1254) (is_pure (
                  uint64_from_le_bytes (lift_to_both0 word_1251))) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 new_state_1250)
            ) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        lift_to_both0 new_state_1250)
      ) : both (CEfset ([new_state_1250_loc ; word_1251_loc])) [interface] (
      state_uint64_t)).
Fail Next Obligation.

Definition new_state_1258_loc : ChoiceEqualityLocation :=
  (state_uint8_t ; 1259%nat).
Notation "'transmute_state_to_u8_inp'" :=(
  state_uint64_t : choice_type) (in custom pack_type at level 2).
Notation "'transmute_state_to_u8_inp'" :=(
  state_uint64_t : ChoiceEquality) (at level 2).
Notation "'transmute_state_to_u8_out'" :=(
  state_uint8_t : choice_type) (in custom pack_type at level 2).
Notation "'transmute_state_to_u8_out'" :=(
  state_uint8_t : ChoiceEquality) (at level 2).
Definition TRANSMUTE_STATE_TO_U8 : nat :=
  1264.
Program Definition transmute_state_to_u8 (state_1260 : state_uint64_t)
  : both (CEfset ([new_state_1258_loc])) [interface] (state_uint8_t) :=
  ((letbm new_state_1258 : state_uint8_t loc( new_state_1258_loc ) :=
        array_new_ (default : uint8) (200) in
      letb new_state_1258 :=
        foldi_both' (lift_to_both0 (usize 0)) (array_len (
              lift_to_both0 state_1260)) new_state_1258 (L := (CEfset (
                [new_state_1258_loc]))) (I := [interface]) (
            fun i_1261 new_state_1258 =>
            letb bytes_1262 : seq uint8 :=
              uint64_to_le_bytes (array_index (state_1260) (
                  lift_to_both0 i_1261)) in
            letb new_state_1258 :=
              foldi_both' (lift_to_both0 (usize 0)) (seq_len (
                    lift_to_both0 bytes_1262)) new_state_1258 (L := (CEfset (
                      [new_state_1258_loc]))) (I := [interface]) (
                  fun j_1263 new_state_1258 =>
                  letb new_state_1258 : state_uint8_t :=
                    array_upd new_state_1258 (((lift_to_both0 i_1261) .* (
                          lift_to_both0 (usize 8))) .+ (lift_to_both0 j_1263)) (
                      is_pure (seq_index (bytes_1262) (
                          lift_to_both0 j_1263))) in
                  lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                    lift_to_both0 new_state_1258)
                  ) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 new_state_1258)
            ) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        lift_to_both0 new_state_1258)
      ) : both (CEfset ([new_state_1258_loc])) [interface] (state_uint8_t)).
Fail Next Obligation.

Definition pos_begin_1267_loc : ChoiceEqualityLocation :=
  (int8 ; 1268%nat).
Definition state_1265_loc : ChoiceEqualityLocation :=
  (state_uint8_t ; 1269%nat).
Definition pos_1266_loc : ChoiceEqualityLocation :=
  (int8 ; 1270%nat).
Notation "'run_f_inp'" :=(
  strobe_t : choice_type) (in custom pack_type at level 2).
Notation "'run_f_inp'" :=(strobe_t : ChoiceEquality) (at level 2).
Notation "'run_f_out'" :=(
  strobe_t : choice_type) (in custom pack_type at level 2).
Notation "'run_f_out'" :=(strobe_t : ChoiceEquality) (at level 2).
Definition RUN_F : nat :=
  1274.
Program Definition run_f (strobe_1271 : strobe_t)
  : both (CEfset (
      [new_state_1250_loc ; word_1251_loc ; new_state_1258_loc ; state_1265_loc ; pos_1266_loc ; pos_begin_1267_loc])) [interface] (
    strobe_t) :=
  ((letb '(state_1265, pos_1266, pos_begin_1267, cur_fl_1272) : (
          state_uint8_t '×
          int8 '×
          int8 '×
          int8
        ) :=
        lift_to_both0 strobe_1271 in
      letb state_1265 : state_uint8_t :=
        array_upd state_1265 (lift_to_both0 pos_1266) (is_pure ((array_index (
                state_1265) (lift_to_both0 pos_1266)) .^ (secret (
                lift_to_both0 pos_begin_1267)))) in
      letb state_1265 : state_uint8_t :=
        array_upd state_1265 ((lift_to_both0 pos_1266) .+ (lift_to_both0 (
              @repr U8 1))) (is_pure ((array_index (state_1265) ((
                  lift_to_both0 pos_1266) .+ (lift_to_both0 (@repr U8 1)))) .^ (
              secret (lift_to_both0 (@repr U8 4))))) in
      letb state_1265 : state_uint8_t :=
        array_upd state_1265 ((lift_to_both0 strobe_r_v) .+ (lift_to_both0 (
              @repr U8 1))) (is_pure ((array_index (state_1265) ((
                  lift_to_both0 strobe_r_v) .+ (lift_to_both0 (
                    @repr U8 1)))) .^ (secret (lift_to_both0 (
                  @repr U8 128))))) in
      letb state_uint64_1273 : state_t :=
        transmute_state_to_u64 (lift_to_both0 state_1265) in
      letbm state_1265 loc( state_1265_loc ) :=
        transmute_state_to_u8 (keccakf1600 (lift_to_both0 state_uint64_1273)) in
      letbm pos_1266 loc( pos_1266_loc ) := lift_to_both0 (@repr U8 0) in
      letbm pos_begin_1267 loc( pos_begin_1267_loc ) :=
        lift_to_both0 (@repr U8 0) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 state_1265,
          lift_to_both0 pos_1266,
          lift_to_both0 pos_begin_1267,
          lift_to_both0 cur_fl_1272
        ))
      ) : both (CEfset (
        [new_state_1250_loc ; word_1251_loc ; new_state_1258_loc ; state_1265_loc ; pos_1266_loc ; pos_begin_1267_loc])) [interface] (
      strobe_t)).
Fail Next Obligation.

Definition pos_1276_loc : ChoiceEqualityLocation :=
  (int8 ; 1279%nat).
Definition pos_begin_1277_loc : ChoiceEqualityLocation :=
  (int8 ; 1280%nat).
Definition cur_fl_1278_loc : ChoiceEqualityLocation :=
  (int8 ; 1281%nat).
Definition state_1275_loc : ChoiceEqualityLocation :=
  (state_uint8_t ; 1282%nat).
Notation "'absorb_inp'" :=(
  strobe_t '× seq uint8 : choice_type) (in custom pack_type at level 2).
Notation "'absorb_inp'" :=(
  strobe_t '× seq uint8 : ChoiceEquality) (at level 2).
Notation "'absorb_out'" :=(
  strobe_t : choice_type) (in custom pack_type at level 2).
Notation "'absorb_out'" :=(strobe_t : ChoiceEquality) (at level 2).
Definition ABSORB : nat :=
  1290.
Program Definition absorb (strobe_1283 : strobe_t) (data_1284 : seq uint8)
  : both (CEfset (
      [new_state_1250_loc ; word_1251_loc ; new_state_1258_loc ; state_1265_loc ; pos_1266_loc ; pos_begin_1267_loc ; state_1275_loc ; pos_1276_loc ; pos_begin_1277_loc ; cur_fl_1278_loc])) [interface] (
    strobe_t) :=
  ((letb '(state_1275, pos_1276, pos_begin_1277, cur_fl_1278) : (
          state_uint8_t '×
          int8 '×
          int8 '×
          int8
        ) :=
        lift_to_both0 strobe_1283 in
      letb '(state_1275, pos_1276, pos_begin_1277, cur_fl_1278) :=
        foldi_both' (lift_to_both0 (usize 0)) (seq_len (
              lift_to_both0 data_1284)) prod_ce(
            state_1275,
            pos_1276,
            pos_begin_1277,
            cur_fl_1278
          ) (L := (CEfset (
                [new_state_1250_loc ; word_1251_loc ; new_state_1258_loc ; state_1265_loc ; pos_1266_loc ; pos_begin_1267_loc ; state_1275_loc ; pos_1276_loc ; pos_begin_1277_loc ; cur_fl_1278_loc]))) (
            I := [interface]) (fun i_1285 '(
              state_1275,
              pos_1276,
              pos_begin_1277,
              cur_fl_1278
            ) =>
            letb state_1275 : state_uint8_t :=
              array_upd state_1275 (lift_to_both0 pos_1276) (is_pure ((
                    array_index (state_1275) (lift_to_both0 pos_1276)) .^ (
                    seq_index (data_1284) (lift_to_both0 i_1285)))) in
            letbm pos_1276 loc( pos_1276_loc ) :=
              (lift_to_both0 pos_1276) .+ (lift_to_both0 (@repr U8 1)) in
            letb '(state_1275, pos_1276, pos_begin_1277, cur_fl_1278) :=
              if (lift_to_both0 pos_1276) =.? (
                lift_to_both0 strobe_r_v) :bool_ChoiceEquality
              then lift_scope (L1 := CEfset (
                  [new_state_1250_loc ; word_1251_loc ; new_state_1258_loc ; state_1265_loc ; pos_1266_loc ; pos_begin_1267_loc ; state_1275_loc ; pos_1276_loc ; pos_begin_1277_loc ; cur_fl_1278_loc])) (
                L2 := CEfset (
                  [new_state_1250_loc ; word_1251_loc ; new_state_1258_loc ; state_1265_loc ; pos_1266_loc ; pos_begin_1267_loc ; state_1275_loc ; pos_1276_loc ; pos_begin_1277_loc ; cur_fl_1278_loc])) (
                I1 := [interface]) (
                I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
                letb '(s_1286, p_1287, pb_1288, cf_1289) : (
                    state_uint8_t '×
                    int8 '×
                    int8 '×
                    int8
                  ) :=
                  run_f (prod_b(
                      lift_to_both0 state_1275,
                      lift_to_both0 pos_1276,
                      lift_to_both0 pos_begin_1277,
                      lift_to_both0 cur_fl_1278
                    )) in
                letbm state_1275 loc( state_1275_loc ) :=
                  lift_to_both0 s_1286 in
                letbm pos_1276 loc( pos_1276_loc ) := lift_to_both0 p_1287 in
                letbm pos_begin_1277 loc( pos_begin_1277_loc ) :=
                  lift_to_both0 pb_1288 in
                letbm cur_fl_1278 loc( cur_fl_1278_loc ) :=
                  lift_to_both0 cf_1289 in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                    lift_to_both0 state_1275,
                    lift_to_both0 pos_1276,
                    lift_to_both0 pos_begin_1277,
                    lift_to_both0 cur_fl_1278
                  ))
                )
              else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                  lift_to_both0 state_1275,
                  lift_to_both0 pos_1276,
                  lift_to_both0 pos_begin_1277,
                  lift_to_both0 cur_fl_1278
                ))
               in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                lift_to_both0 state_1275,
                lift_to_both0 pos_1276,
                lift_to_both0 pos_begin_1277,
                lift_to_both0 cur_fl_1278
              ))
            ) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 state_1275,
          lift_to_both0 pos_1276,
          lift_to_both0 pos_begin_1277,
          lift_to_both0 cur_fl_1278
        ))
      ) : both (CEfset (
        [new_state_1250_loc ; word_1251_loc ; new_state_1258_loc ; state_1265_loc ; pos_1266_loc ; pos_begin_1267_loc ; state_1275_loc ; pos_1276_loc ; pos_begin_1277_loc ; cur_fl_1278_loc])) [interface] (
      strobe_t)).
Fail Next Obligation.

Definition pos_begin_1293_loc : ChoiceEqualityLocation :=
  (int8 ; 1295%nat).
Definition cur_fl_1294_loc : ChoiceEqualityLocation :=
  (int8 ; 1296%nat).
Definition pos_1292_loc : ChoiceEqualityLocation :=
  (int8 ; 1297%nat).
Definition state_1291_loc : ChoiceEqualityLocation :=
  (state_uint8_t ; 1298%nat).
Notation "'squeeze_inp'" :=(
  strobe_t '× seq uint8 : choice_type) (in custom pack_type at level 2).
Notation "'squeeze_inp'" :=(
  strobe_t '× seq uint8 : ChoiceEquality) (at level 2).
Notation "'squeeze_out'" :=((strobe_t '× seq uint8
  ) : choice_type) (in custom pack_type at level 2).
Notation "'squeeze_out'" :=((strobe_t '× seq uint8
  ) : ChoiceEquality) (at level 2).
Definition SQUEEZE : nat :=
  1306.
Program Definition squeeze (strobe_1299 : strobe_t) (data_1300 : seq uint8)
  : both (CEfset (
      [new_state_1250_loc ; word_1251_loc ; new_state_1258_loc ; state_1265_loc ; pos_1266_loc ; pos_begin_1267_loc ; state_1291_loc ; pos_1292_loc ; pos_begin_1293_loc ; cur_fl_1294_loc])) [interface] (
    (strobe_t '× seq uint8)) :=
  ((letb '(state_1291, pos_1292, pos_begin_1293, cur_fl_1294) : (
          state_uint8_t '×
          int8 '×
          int8 '×
          int8
        ) :=
        lift_to_both0 strobe_1299 in
      letb '(data_1300, state_1291, pos_1292, pos_begin_1293, cur_fl_1294) :=
        foldi_both' (lift_to_both0 (usize 0)) (seq_len (
              lift_to_both0 data_1300)) prod_ce(
            data_1300,
            state_1291,
            pos_1292,
            pos_begin_1293,
            cur_fl_1294
          ) (L := (CEfset (
                [new_state_1250_loc ; word_1251_loc ; new_state_1258_loc ; state_1265_loc ; pos_1266_loc ; pos_begin_1267_loc ; state_1291_loc ; pos_1292_loc ; pos_begin_1293_loc ; cur_fl_1294_loc]))) (
            I := [interface]) (fun i_1301 '(
              data_1300,
              state_1291,
              pos_1292,
              pos_begin_1293,
              cur_fl_1294
            ) =>
            letb data_1300 : seq uint8 :=
              seq_upd data_1300 (lift_to_both0 i_1301) (is_pure (array_index (
                    state_1291) (lift_to_both0 pos_1292))) in
            letb state_1291 : state_uint8_t :=
              array_upd state_1291 (lift_to_both0 pos_1292) (is_pure (
                  uint8_classify (lift_to_both0 (@repr U8 0)))) in
            letbm pos_1292 loc( pos_1292_loc ) :=
              (lift_to_both0 pos_1292) .+ (lift_to_both0 (@repr U8 1)) in
            letb '(state_1291, pos_1292, pos_begin_1293, cur_fl_1294) :=
              if (lift_to_both0 pos_1292) =.? (
                lift_to_both0 strobe_r_v) :bool_ChoiceEquality
              then lift_scope (L1 := CEfset (
                  [new_state_1250_loc ; word_1251_loc ; new_state_1258_loc ; state_1265_loc ; pos_1266_loc ; pos_begin_1267_loc ; state_1291_loc ; pos_1292_loc ; pos_begin_1293_loc ; cur_fl_1294_loc])) (
                L2 := CEfset (
                  [new_state_1250_loc ; word_1251_loc ; new_state_1258_loc ; state_1265_loc ; pos_1266_loc ; pos_begin_1267_loc ; state_1291_loc ; pos_1292_loc ; pos_begin_1293_loc ; cur_fl_1294_loc])) (
                I1 := [interface]) (
                I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
                letb '(s_1302, p_1303, pb_1304, cf_1305) : (
                    state_uint8_t '×
                    int8 '×
                    int8 '×
                    int8
                  ) :=
                  run_f (prod_b(
                      (lift_to_both0 state_1291),
                      lift_to_both0 pos_1292,
                      lift_to_both0 pos_begin_1293,
                      lift_to_both0 cur_fl_1294
                    )) in
                letbm state_1291 loc( state_1291_loc ) :=
                  lift_to_both0 s_1302 in
                letbm pos_1292 loc( pos_1292_loc ) := lift_to_both0 p_1303 in
                letbm pos_begin_1293 loc( pos_begin_1293_loc ) :=
                  lift_to_both0 pb_1304 in
                letbm cur_fl_1294 loc( cur_fl_1294_loc ) :=
                  lift_to_both0 cf_1305 in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                    lift_to_both0 state_1291,
                    lift_to_both0 pos_1292,
                    lift_to_both0 pos_begin_1293,
                    lift_to_both0 cur_fl_1294
                  ))
                )
              else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                  lift_to_both0 state_1291,
                  lift_to_both0 pos_1292,
                  lift_to_both0 pos_begin_1293,
                  lift_to_both0 cur_fl_1294
                ))
               in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                lift_to_both0 data_1300,
                lift_to_both0 state_1291,
                lift_to_both0 pos_1292,
                lift_to_both0 pos_begin_1293,
                lift_to_both0 cur_fl_1294
              ))
            ) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          prod_b(
            lift_to_both0 state_1291,
            lift_to_both0 pos_1292,
            lift_to_both0 pos_begin_1293,
            lift_to_both0 cur_fl_1294
          ),
          lift_to_both0 data_1300
        ))
      ) : both (CEfset (
        [new_state_1250_loc ; word_1251_loc ; new_state_1258_loc ; state_1265_loc ; pos_1266_loc ; pos_begin_1267_loc ; state_1291_loc ; pos_1292_loc ; pos_begin_1293_loc ; cur_fl_1294_loc])) [interface] (
      (strobe_t '× seq uint8))).
Fail Next Obligation.

Definition pos_1308_loc : ChoiceEqualityLocation :=
  (int8 ; 1313%nat).
Definition pos_begin_1309_loc : ChoiceEqualityLocation :=
  (int8 ; 1314%nat).
Definition cur_fl_1310_loc : ChoiceEqualityLocation :=
  (int8 ; 1315%nat).
Definition state_1307_loc : ChoiceEqualityLocation :=
  (state_uint8_t ; 1316%nat).
Definition ret_1311_loc : ChoiceEqualityLocation :=
  ((state_uint8_t '× int8 '× int8 '× int8) ; 1317%nat).
Definition data_1312_loc : ChoiceEqualityLocation :=
  (seq uint8 ; 1318%nat).
Notation "'begin_op_inp'" :=(
  strobe_t '× int8 '× bool_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'begin_op_inp'" :=(
  strobe_t '× int8 '× bool_ChoiceEquality : ChoiceEquality) (at level 2).
Notation "'begin_op_out'" :=(
  strobe_t : choice_type) (in custom pack_type at level 2).
Notation "'begin_op_out'" :=(strobe_t : ChoiceEquality) (at level 2).
Definition BEGIN_OP : nat :=
  1328.
Program Definition begin_op (strobe_1319 : strobe_t) (flags_1322 : int8) (
    more_1320 : bool_ChoiceEquality)
  : both (CEfset (
      [new_state_1250_loc ; word_1251_loc ; new_state_1258_loc ; state_1265_loc ; pos_1266_loc ; pos_begin_1267_loc ; state_1275_loc ; pos_1276_loc ; pos_begin_1277_loc ; cur_fl_1278_loc ; state_1307_loc ; pos_1308_loc ; pos_begin_1309_loc ; cur_fl_1310_loc ; ret_1311_loc ; data_1312_loc])) [interface] (
    strobe_t) :=
  ((letb '(state_1307, pos_1308, pos_begin_1309, cur_fl_1310) : (
          state_uint8_t '×
          int8 '×
          int8 '×
          int8
        ) :=
        lift_to_both0 strobe_1319 in
      letbm ret_1311 : (state_uint8_t '× int8 '× int8 '× int8
        ) loc( ret_1311_loc ) :=
        prod_b(
          lift_to_both0 state_1307,
          lift_to_both0 pos_1308,
          lift_to_both0 pos_begin_1309,
          lift_to_both0 cur_fl_1310
        ) in
      letb '(state_1307, pos_1308, pos_begin_1309, cur_fl_1310, ret_1311) :=
        if negb (lift_to_both0 more_1320) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset (
            [new_state_1250_loc ; word_1251_loc ; new_state_1258_loc ; state_1265_loc ; pos_1266_loc ; pos_begin_1267_loc ; state_1275_loc ; pos_1276_loc ; pos_begin_1277_loc ; cur_fl_1278_loc ; state_1307_loc ; pos_1308_loc ; pos_begin_1309_loc ; cur_fl_1310_loc ; ret_1311_loc ; data_1312_loc])) (
          L2 := CEfset (
            [new_state_1250_loc ; word_1251_loc ; new_state_1258_loc ; state_1265_loc ; pos_1266_loc ; pos_begin_1267_loc ; state_1275_loc ; pos_1276_loc ; pos_begin_1277_loc ; cur_fl_1278_loc ; state_1307_loc ; pos_1308_loc ; pos_begin_1309_loc ; cur_fl_1310_loc ; ret_1311_loc ; data_1312_loc])) (
          I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
          letb old_begin_1321 : int8 := lift_to_both0 pos_begin_1309 in
          letbm pos_begin_1309 loc( pos_begin_1309_loc ) :=
            (lift_to_both0 pos_1308) .+ (lift_to_both0 (@repr U8 1)) in
          letbm cur_fl_1310 loc( cur_fl_1310_loc ) :=
            lift_to_both0 flags_1322 in
          letbm data_1312 : seq uint8 loc( data_1312_loc ) :=
            seq_new_ (default : uint8) (lift_to_both0 (usize 2)) in
          letb data_1312 : seq uint8 :=
            seq_upd data_1312 (lift_to_both0 (usize 0)) (is_pure (secret (
                  lift_to_both0 old_begin_1321))) in
          letb data_1312 : seq uint8 :=
            seq_upd data_1312 (lift_to_both0 (usize 1)) (is_pure (secret (
                  lift_to_both0 flags_1322))) in
          letb '(s_1323, p_1324, pb_1325, cf_1326) : (
              state_uint8_t '×
              int8 '×
              int8 '×
              int8
            ) :=
            absorb (prod_b(
                lift_to_both0 state_1307,
                lift_to_both0 pos_1308,
                lift_to_both0 pos_begin_1309,
                lift_to_both0 cur_fl_1310
              )) (lift_to_both0 data_1312) in
          letbm state_1307 loc( state_1307_loc ) := lift_to_both0 s_1323 in
          letbm pos_1308 loc( pos_1308_loc ) := lift_to_both0 p_1324 in
          letbm pos_begin_1309 loc( pos_begin_1309_loc ) :=
            lift_to_both0 pb_1325 in
          letbm cur_fl_1310 loc( cur_fl_1310_loc ) := lift_to_both0 cf_1326 in
          letb force_f_1327 : bool_ChoiceEquality :=
            (lift_to_both0 (@repr U8 0)) !=.? ((lift_to_both0 flags_1322) .& ((
                  lift_to_both0 flag_c_v) .| (lift_to_both0 flag_k_v))) in
          letb '(ret_1311) :=
            if (lift_to_both0 force_f_1327) && ((lift_to_both0 pos_1308) !=.? (
                lift_to_both0 (@repr U8 0))) :bool_ChoiceEquality
            then lift_scope (L1 := CEfset (
                [new_state_1250_loc ; word_1251_loc ; new_state_1258_loc ; state_1265_loc ; pos_1266_loc ; pos_begin_1267_loc ; state_1275_loc ; pos_1276_loc ; pos_begin_1277_loc ; cur_fl_1278_loc ; state_1307_loc ; pos_1308_loc ; pos_begin_1309_loc ; cur_fl_1310_loc ; ret_1311_loc ; data_1312_loc])) (
              L2 := CEfset (
                [new_state_1250_loc ; word_1251_loc ; new_state_1258_loc ; state_1265_loc ; pos_1266_loc ; pos_begin_1267_loc ; state_1275_loc ; pos_1276_loc ; pos_begin_1277_loc ; cur_fl_1278_loc ; state_1307_loc ; pos_1308_loc ; pos_begin_1309_loc ; cur_fl_1310_loc ; ret_1311_loc ; data_1312_loc])) (
              I1 := [interface]) (
              I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
              letbm ret_1311 loc( ret_1311_loc ) :=
                run_f (prod_b(
                    lift_to_both0 state_1307,
                    lift_to_both0 pos_1308,
                    lift_to_both0 pos_begin_1309,
                    lift_to_both0 cur_fl_1310
                  )) in
              lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                lift_to_both0 ret_1311)
              )
            else  lift_scope (L1 := CEfset (
                [new_state_1250_loc ; word_1251_loc ; new_state_1258_loc ; state_1265_loc ; pos_1266_loc ; pos_begin_1267_loc ; state_1275_loc ; pos_1276_loc ; pos_begin_1277_loc ; cur_fl_1278_loc ; state_1307_loc ; pos_1308_loc ; pos_begin_1309_loc ; cur_fl_1310_loc ; ret_1311_loc ; data_1312_loc])) (
              L2 := CEfset (
                [new_state_1250_loc ; word_1251_loc ; new_state_1258_loc ; state_1265_loc ; pos_1266_loc ; pos_begin_1267_loc ; state_1275_loc ; pos_1276_loc ; pos_begin_1277_loc ; cur_fl_1278_loc ; state_1307_loc ; pos_1308_loc ; pos_begin_1309_loc ; cur_fl_1310_loc ; ret_1311_loc ; data_1312_loc])) (
              I1 := [interface]) (
              I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
              letbm ret_1311 loc( ret_1311_loc ) :=
                prod_b(
                  lift_to_both0 state_1307,
                  lift_to_both0 pos_1308,
                  lift_to_both0 pos_begin_1309,
                  lift_to_both0 cur_fl_1310
                ) in
              lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                lift_to_both0 ret_1311)
              ) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
              lift_to_both0 state_1307,
              lift_to_both0 pos_1308,
              lift_to_both0 pos_begin_1309,
              lift_to_both0 cur_fl_1310,
              lift_to_both0 ret_1311
            ))
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
            lift_to_both0 state_1307,
            lift_to_both0 pos_1308,
            lift_to_both0 pos_begin_1309,
            lift_to_both0 cur_fl_1310,
            lift_to_both0 ret_1311
          ))
         in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 ret_1311)
      ) : both (CEfset (
        [new_state_1250_loc ; word_1251_loc ; new_state_1258_loc ; state_1265_loc ; pos_1266_loc ; pos_begin_1267_loc ; state_1275_loc ; pos_1276_loc ; pos_begin_1277_loc ; cur_fl_1278_loc ; state_1307_loc ; pos_1308_loc ; pos_begin_1309_loc ; cur_fl_1310_loc ; ret_1311_loc ; data_1312_loc])) [interface] (
      strobe_t)).
Fail Next Obligation.

Definition st_1329_loc : ChoiceEqualityLocation :=
  (state_uint8_t ; 1330%nat).
Notation "'new_strobe_inp'" :=(
  seq uint8 : choice_type) (in custom pack_type at level 2).
Notation "'new_strobe_inp'" :=(seq uint8 : ChoiceEquality) (at level 2).
Notation "'new_strobe_out'" :=(
  strobe_t : choice_type) (in custom pack_type at level 2).
Notation "'new_strobe_out'" :=(strobe_t : ChoiceEquality) (at level 2).
Definition NEW_STROBE : nat :=
  1333.
Program Definition new_strobe (protocol_label_1332 : seq uint8)
  : both (CEfset (
      [new_state_1250_loc ; word_1251_loc ; new_state_1258_loc ; st_1329_loc])) [interface] (
    strobe_t) :=
  ((letbm st_1329 : state_uint8_t loc( st_1329_loc ) :=
        array_new_ (default : uint8) (200) in
      letbm st_1329 loc( st_1329_loc ) :=
        array_set_chunk (lift_to_both0 st_1329) (lift_to_both0 (usize 6)) (
          lift_to_both0 (usize 0)) ([
            secret (lift_to_both0 (@repr U8 1));
            secret (lift_to_both0 (@repr U8 168));
            secret (lift_to_both0 (@repr U8 1));
            secret (lift_to_both0 (@repr U8 0));
            secret (lift_to_both0 (@repr U8 1));
            secret (lift_to_both0 (@repr U8 96))
          ]) in
      letbm st_1329 loc( st_1329_loc ) :=
        array_set_chunk (lift_to_both0 st_1329) (lift_to_both0 (usize 6)) (
          lift_to_both0 (usize 1)) ([
            secret (lift_to_both0 (@repr U8 83));
            secret (lift_to_both0 (@repr U8 84));
            secret (lift_to_both0 (@repr U8 82));
            secret (lift_to_both0 (@repr U8 79));
            secret (lift_to_both0 (@repr U8 66));
            secret (lift_to_both0 (@repr U8 69))
          ]) in
      letbm st_1329 loc( st_1329_loc ) :=
        array_set_chunk (lift_to_both0 st_1329) (lift_to_both0 (usize 6)) (
          lift_to_both0 (usize 2)) ([
            secret (lift_to_both0 (@repr U8 118));
            secret (lift_to_both0 (@repr U8 49));
            secret (lift_to_both0 (@repr U8 46));
            secret (lift_to_both0 (@repr U8 48));
            secret (lift_to_both0 (@repr U8 46));
            secret (lift_to_both0 (@repr U8 50))
          ]) in
      letb st_uint64_1331 : state_t :=
        transmute_state_to_u64 (lift_to_both0 st_1329) in
      letbm st_1329 loc( st_1329_loc ) :=
        transmute_state_to_u8 (keccakf1600 (lift_to_both0 st_uint64_1331)) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (meta_ad (prod_b(
            lift_to_both0 st_1329,
            lift_to_both0 (@repr U8 0),
            lift_to_both0 (@repr U8 0),
            lift_to_both0 (@repr U8 0)
          )) (lift_to_both0 protocol_label_1332) (lift_to_both0 (
            (false : bool_ChoiceEquality))))
      ) : both (CEfset (
        [new_state_1250_loc ; word_1251_loc ; new_state_1258_loc ; st_1329_loc])) [interface] (
      strobe_t)).
Fail Next Obligation.


Notation "'meta_ad_inp'" :=(
  strobe_t '× seq uint8 '× bool_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'meta_ad_inp'" :=(
  strobe_t '× seq uint8 '× bool_ChoiceEquality : ChoiceEquality) (at level 2).
Notation "'meta_ad_out'" :=(
  strobe_t : choice_type) (in custom pack_type at level 2).
Notation "'meta_ad_out'" :=(strobe_t : ChoiceEquality) (at level 2).
Definition META_AD : nat :=
  1337.
Program Definition meta_ad (strobe_1334 : strobe_t) (data_1336 : seq uint8) (
    more_1335 : bool_ChoiceEquality)
  : both (CEfset (
      [new_state_1250_loc ; word_1251_loc ; new_state_1258_loc ; state_1265_loc ; pos_1266_loc ; pos_begin_1267_loc ; state_1275_loc ; pos_1276_loc ; pos_begin_1277_loc ; cur_fl_1278_loc ; state_1307_loc ; pos_1308_loc ; pos_begin_1309_loc ; cur_fl_1310_loc ; ret_1311_loc ; data_1312_loc])) [interface] (
    strobe_t) :=
  ((letbm strobe_1334 loc( strobe_1334_loc ) :=
        begin_op (lift_to_both0 strobe_1334) ((lift_to_both0 flag_m_v) .| (
            lift_to_both0 flag_a_v)) (lift_to_both0 more_1335) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (absorb (
          lift_to_both0 strobe_1334) (lift_to_both0 data_1336))
      ) : both (CEfset (
        [new_state_1250_loc ; word_1251_loc ; new_state_1258_loc ; state_1265_loc ; pos_1266_loc ; pos_begin_1267_loc ; state_1275_loc ; pos_1276_loc ; pos_begin_1277_loc ; cur_fl_1278_loc ; state_1307_loc ; pos_1308_loc ; pos_begin_1309_loc ; cur_fl_1310_loc ; ret_1311_loc ; data_1312_loc])) [interface] (
      strobe_t)).
Fail Next Obligation.


Notation "'ad_inp'" :=(
  strobe_t '× seq uint8 '× bool_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'ad_inp'" :=(
  strobe_t '× seq uint8 '× bool_ChoiceEquality : ChoiceEquality) (at level 2).
Notation "'ad_out'" :=(strobe_t : choice_type) (in custom pack_type at level 2).
Notation "'ad_out'" :=(strobe_t : ChoiceEquality) (at level 2).
Definition AD : nat :=
  1341.
Program Definition ad (strobe_1338 : strobe_t) (data_1340 : seq uint8) (
    more_1339 : bool_ChoiceEquality)
  : both (CEfset (
      [new_state_1250_loc ; word_1251_loc ; new_state_1258_loc ; state_1265_loc ; pos_1266_loc ; pos_begin_1267_loc ; state_1275_loc ; pos_1276_loc ; pos_begin_1277_loc ; cur_fl_1278_loc ; state_1307_loc ; pos_1308_loc ; pos_begin_1309_loc ; cur_fl_1310_loc ; ret_1311_loc ; data_1312_loc])) [interface] (
    strobe_t) :=
  ((letbm strobe_1338 loc( strobe_1338_loc ) :=
        begin_op (lift_to_both0 strobe_1338) (lift_to_both0 flag_a_v) (
          lift_to_both0 more_1339) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (absorb (
          lift_to_both0 strobe_1338) (lift_to_both0 data_1340))
      ) : both (CEfset (
        [new_state_1250_loc ; word_1251_loc ; new_state_1258_loc ; state_1265_loc ; pos_1266_loc ; pos_begin_1267_loc ; state_1275_loc ; pos_1276_loc ; pos_begin_1277_loc ; cur_fl_1278_loc ; state_1307_loc ; pos_1308_loc ; pos_begin_1309_loc ; cur_fl_1310_loc ; ret_1311_loc ; data_1312_loc])) [interface] (
      strobe_t)).
Fail Next Obligation.


Notation "'prf_inp'" :=(
  strobe_t '× seq uint8 '× bool_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'prf_inp'" :=(
  strobe_t '× seq uint8 '× bool_ChoiceEquality : ChoiceEquality) (at level 2).
Notation "'prf_out'" :=((strobe_t '× seq uint8
  ) : choice_type) (in custom pack_type at level 2).
Notation "'prf_out'" :=((strobe_t '× seq uint8) : ChoiceEquality) (at level 2).
Definition PRF : nat :=
  1345.
Program Definition prf (strobe_1342 : strobe_t) (data_1344 : seq uint8) (
    more_1343 : bool_ChoiceEquality)
  : both (CEfset (
      [new_state_1250_loc ; word_1251_loc ; new_state_1258_loc ; state_1265_loc ; pos_1266_loc ; pos_begin_1267_loc ; state_1275_loc ; pos_1276_loc ; pos_begin_1277_loc ; cur_fl_1278_loc ; state_1291_loc ; pos_1292_loc ; pos_begin_1293_loc ; cur_fl_1294_loc ; state_1307_loc ; pos_1308_loc ; pos_begin_1309_loc ; cur_fl_1310_loc ; ret_1311_loc ; data_1312_loc])) [interface] (
    (strobe_t '× seq uint8)) :=
  ((letbm strobe_1342 loc( strobe_1342_loc ) :=
        begin_op (lift_to_both0 strobe_1342) (((lift_to_both0 flag_i_v) .| (
              lift_to_both0 flag_a_v)) .| (lift_to_both0 flag_c_v)) (
          lift_to_both0 more_1343) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (squeeze (
          lift_to_both0 strobe_1342) (lift_to_both0 data_1344))
      ) : both (CEfset (
        [new_state_1250_loc ; word_1251_loc ; new_state_1258_loc ; state_1265_loc ; pos_1266_loc ; pos_begin_1267_loc ; state_1275_loc ; pos_1276_loc ; pos_begin_1277_loc ; cur_fl_1278_loc ; state_1291_loc ; pos_1292_loc ; pos_begin_1293_loc ; cur_fl_1294_loc ; state_1307_loc ; pos_1308_loc ; pos_begin_1309_loc ; cur_fl_1310_loc ; ret_1311_loc ; data_1312_loc])) [interface] (
      (strobe_t '× seq uint8))).
Fail Next Obligation.

