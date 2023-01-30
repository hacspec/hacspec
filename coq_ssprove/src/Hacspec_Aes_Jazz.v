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


Definition s_box_t := nseq (int8) (usize 256).

Definition r_con_t := nseq (int8) (usize 15).

Definition p_bytes256_t := nseq (int8) (usize 256).

Definition sbox_v : s_box_t :=
  @array_from_list int8 [
    (@repr U8 99) : int8;
    (@repr U8 124) : int8;
    (@repr U8 119) : int8;
    (@repr U8 123) : int8;
    (@repr U8 242) : int8;
    (@repr U8 107) : int8;
    (@repr U8 111) : int8;
    (@repr U8 197) : int8;
    (@repr U8 48) : int8;
    (@repr U8 1) : int8;
    (@repr U8 103) : int8;
    (@repr U8 43) : int8;
    (@repr U8 254) : int8;
    (@repr U8 215) : int8;
    (@repr U8 171) : int8;
    (@repr U8 118) : int8;
    (@repr U8 202) : int8;
    (@repr U8 130) : int8;
    (@repr U8 201) : int8;
    (@repr U8 125) : int8;
    (@repr U8 250) : int8;
    (@repr U8 89) : int8;
    (@repr U8 71) : int8;
    (@repr U8 240) : int8;
    (@repr U8 173) : int8;
    (@repr U8 212) : int8;
    (@repr U8 162) : int8;
    (@repr U8 175) : int8;
    (@repr U8 156) : int8;
    (@repr U8 164) : int8;
    (@repr U8 114) : int8;
    (@repr U8 192) : int8;
    (@repr U8 183) : int8;
    (@repr U8 253) : int8;
    (@repr U8 147) : int8;
    (@repr U8 38) : int8;
    (@repr U8 54) : int8;
    (@repr U8 63) : int8;
    (@repr U8 247) : int8;
    (@repr U8 204) : int8;
    (@repr U8 52) : int8;
    (@repr U8 165) : int8;
    (@repr U8 229) : int8;
    (@repr U8 241) : int8;
    (@repr U8 113) : int8;
    (@repr U8 216) : int8;
    (@repr U8 49) : int8;
    (@repr U8 21) : int8;
    (@repr U8 4) : int8;
    (@repr U8 199) : int8;
    (@repr U8 35) : int8;
    (@repr U8 195) : int8;
    (@repr U8 24) : int8;
    (@repr U8 150) : int8;
    (@repr U8 5) : int8;
    (@repr U8 154) : int8;
    (@repr U8 7) : int8;
    (@repr U8 18) : int8;
    (@repr U8 128) : int8;
    (@repr U8 226) : int8;
    (@repr U8 235) : int8;
    (@repr U8 39) : int8;
    (@repr U8 178) : int8;
    (@repr U8 117) : int8;
    (@repr U8 9) : int8;
    (@repr U8 131) : int8;
    (@repr U8 44) : int8;
    (@repr U8 26) : int8;
    (@repr U8 27) : int8;
    (@repr U8 110) : int8;
    (@repr U8 90) : int8;
    (@repr U8 160) : int8;
    (@repr U8 82) : int8;
    (@repr U8 59) : int8;
    (@repr U8 214) : int8;
    (@repr U8 179) : int8;
    (@repr U8 41) : int8;
    (@repr U8 227) : int8;
    (@repr U8 47) : int8;
    (@repr U8 132) : int8;
    (@repr U8 83) : int8;
    (@repr U8 209) : int8;
    (@repr U8 0) : int8;
    (@repr U8 237) : int8;
    (@repr U8 32) : int8;
    (@repr U8 252) : int8;
    (@repr U8 177) : int8;
    (@repr U8 91) : int8;
    (@repr U8 106) : int8;
    (@repr U8 203) : int8;
    (@repr U8 190) : int8;
    (@repr U8 57) : int8;
    (@repr U8 74) : int8;
    (@repr U8 76) : int8;
    (@repr U8 88) : int8;
    (@repr U8 207) : int8;
    (@repr U8 208) : int8;
    (@repr U8 239) : int8;
    (@repr U8 170) : int8;
    (@repr U8 251) : int8;
    (@repr U8 67) : int8;
    (@repr U8 77) : int8;
    (@repr U8 51) : int8;
    (@repr U8 133) : int8;
    (@repr U8 69) : int8;
    (@repr U8 249) : int8;
    (@repr U8 2) : int8;
    (@repr U8 127) : int8;
    (@repr U8 80) : int8;
    (@repr U8 60) : int8;
    (@repr U8 159) : int8;
    (@repr U8 168) : int8;
    (@repr U8 81) : int8;
    (@repr U8 163) : int8;
    (@repr U8 64) : int8;
    (@repr U8 143) : int8;
    (@repr U8 146) : int8;
    (@repr U8 157) : int8;
    (@repr U8 56) : int8;
    (@repr U8 245) : int8;
    (@repr U8 188) : int8;
    (@repr U8 182) : int8;
    (@repr U8 218) : int8;
    (@repr U8 33) : int8;
    (@repr U8 16) : int8;
    (@repr U8 255) : int8;
    (@repr U8 243) : int8;
    (@repr U8 210) : int8;
    (@repr U8 205) : int8;
    (@repr U8 12) : int8;
    (@repr U8 19) : int8;
    (@repr U8 236) : int8;
    (@repr U8 95) : int8;
    (@repr U8 151) : int8;
    (@repr U8 68) : int8;
    (@repr U8 23) : int8;
    (@repr U8 196) : int8;
    (@repr U8 167) : int8;
    (@repr U8 126) : int8;
    (@repr U8 61) : int8;
    (@repr U8 100) : int8;
    (@repr U8 93) : int8;
    (@repr U8 25) : int8;
    (@repr U8 115) : int8;
    (@repr U8 96) : int8;
    (@repr U8 129) : int8;
    (@repr U8 79) : int8;
    (@repr U8 220) : int8;
    (@repr U8 34) : int8;
    (@repr U8 42) : int8;
    (@repr U8 144) : int8;
    (@repr U8 136) : int8;
    (@repr U8 70) : int8;
    (@repr U8 238) : int8;
    (@repr U8 184) : int8;
    (@repr U8 20) : int8;
    (@repr U8 222) : int8;
    (@repr U8 94) : int8;
    (@repr U8 11) : int8;
    (@repr U8 219) : int8;
    (@repr U8 224) : int8;
    (@repr U8 50) : int8;
    (@repr U8 58) : int8;
    (@repr U8 10) : int8;
    (@repr U8 73) : int8;
    (@repr U8 6) : int8;
    (@repr U8 36) : int8;
    (@repr U8 92) : int8;
    (@repr U8 194) : int8;
    (@repr U8 211) : int8;
    (@repr U8 172) : int8;
    (@repr U8 98) : int8;
    (@repr U8 145) : int8;
    (@repr U8 149) : int8;
    (@repr U8 228) : int8;
    (@repr U8 121) : int8;
    (@repr U8 231) : int8;
    (@repr U8 200) : int8;
    (@repr U8 55) : int8;
    (@repr U8 109) : int8;
    (@repr U8 141) : int8;
    (@repr U8 213) : int8;
    (@repr U8 78) : int8;
    (@repr U8 169) : int8;
    (@repr U8 108) : int8;
    (@repr U8 86) : int8;
    (@repr U8 244) : int8;
    (@repr U8 234) : int8;
    (@repr U8 101) : int8;
    (@repr U8 122) : int8;
    (@repr U8 174) : int8;
    (@repr U8 8) : int8;
    (@repr U8 186) : int8;
    (@repr U8 120) : int8;
    (@repr U8 37) : int8;
    (@repr U8 46) : int8;
    (@repr U8 28) : int8;
    (@repr U8 166) : int8;
    (@repr U8 180) : int8;
    (@repr U8 198) : int8;
    (@repr U8 232) : int8;
    (@repr U8 221) : int8;
    (@repr U8 116) : int8;
    (@repr U8 31) : int8;
    (@repr U8 75) : int8;
    (@repr U8 189) : int8;
    (@repr U8 139) : int8;
    (@repr U8 138) : int8;
    (@repr U8 112) : int8;
    (@repr U8 62) : int8;
    (@repr U8 181) : int8;
    (@repr U8 102) : int8;
    (@repr U8 72) : int8;
    (@repr U8 3) : int8;
    (@repr U8 246) : int8;
    (@repr U8 14) : int8;
    (@repr U8 97) : int8;
    (@repr U8 53) : int8;
    (@repr U8 87) : int8;
    (@repr U8 185) : int8;
    (@repr U8 134) : int8;
    (@repr U8 193) : int8;
    (@repr U8 29) : int8;
    (@repr U8 158) : int8;
    (@repr U8 225) : int8;
    (@repr U8 248) : int8;
    (@repr U8 152) : int8;
    (@repr U8 17) : int8;
    (@repr U8 105) : int8;
    (@repr U8 217) : int8;
    (@repr U8 142) : int8;
    (@repr U8 148) : int8;
    (@repr U8 155) : int8;
    (@repr U8 30) : int8;
    (@repr U8 135) : int8;
    (@repr U8 233) : int8;
    (@repr U8 206) : int8;
    (@repr U8 85) : int8;
    (@repr U8 40) : int8;
    (@repr U8 223) : int8;
    (@repr U8 140) : int8;
    (@repr U8 161) : int8;
    (@repr U8 137) : int8;
    (@repr U8 13) : int8;
    (@repr U8 191) : int8;
    (@repr U8 230) : int8;
    (@repr U8 66) : int8;
    (@repr U8 104) : int8;
    (@repr U8 65) : int8;
    (@repr U8 153) : int8;
    (@repr U8 45) : int8;
    (@repr U8 15) : int8;
    (@repr U8 176) : int8;
    (@repr U8 84) : int8;
    (@repr U8 187) : int8;
    (@repr U8 22) : int8
  ].

Definition rcon_v : r_con_t :=
  @array_from_list int8 [
    (@repr U8 141) : int8;
    (@repr U8 1) : int8;
    (@repr U8 2) : int8;
    (@repr U8 4) : int8;
    (@repr U8 8) : int8;
    (@repr U8 16) : int8;
    (@repr U8 32) : int8;
    (@repr U8 64) : int8;
    (@repr U8 128) : int8;
    (@repr U8 27) : int8;
    (@repr U8 54) : int8;
    (@repr U8 108) : int8;
    (@repr U8 216) : int8;
    (@repr U8 171) : int8;
    (@repr U8 77) : int8
  ].


Notation "'index_u32_inp'" :=(
  int128 '× uint_size : choice_type) (in custom pack_type at level 2).
Notation "'index_u32_inp'" :=(
  int128 '× uint_size : ChoiceEquality) (at level 2).
Notation "'index_u32_out'" :=(
  int32 : choice_type) (in custom pack_type at level 2).
Notation "'index_u32_out'" :=(int32 : ChoiceEquality) (at level 2).
Definition INDEX_U32 : nat :=
  211.
Program Definition index_u32 (s_209 : int128) (i_210 : uint_size)
  : both (fset.fset0) [interface] (int32) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        (fun x => lift_to_both0 (repr (unsigned x)))(((
              lift_to_both0 s_209) shift_right ((lift_to_both0 i_210) .* (
                lift_to_both0 (usize 32)))) .% ((lift_to_both0 (
                @repr U128 1)) shift_left (lift_to_both0 (usize 32)))))
      ) : both (fset.fset0) [interface] (int32)).
Fail Next Obligation.


Notation "'index_u8_inp'" :=(
  int32 '× uint_size : choice_type) (in custom pack_type at level 2).
Notation "'index_u8_inp'" :=(int32 '× uint_size : ChoiceEquality) (at level 2).
Notation "'index_u8_out'" :=(
  int8 : choice_type) (in custom pack_type at level 2).
Notation "'index_u8_out'" :=(int8 : ChoiceEquality) (at level 2).
Definition INDEX_U8 : nat :=
  214.
Program Definition index_u8 (s_212 : int32) (i_213 : uint_size)
  : both (fset.fset0) [interface] (int8) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        (fun x => lift_to_both0 (repr (unsigned x)))(((
              lift_to_both0 s_212) shift_right ((lift_to_both0 i_213) .* (
                lift_to_both0 (usize 8)))) .% ((lift_to_both0 (
                @repr U32 1)) shift_left (lift_to_both0 (usize 8)))))
      ) : both (fset.fset0) [interface] (int8)).
Fail Next Obligation.


Notation "'rebuild_u32_inp'" :=(
  int8 '× int8 '× int8 '× int8 : choice_type) (in custom pack_type at level 2).
Notation "'rebuild_u32_inp'" :=(
  int8 '× int8 '× int8 '× int8 : ChoiceEquality) (at level 2).
Notation "'rebuild_u32_out'" :=(
  int32 : choice_type) (in custom pack_type at level 2).
Notation "'rebuild_u32_out'" :=(int32 : ChoiceEquality) (at level 2).
Definition REBUILD_U32 : nat :=
  219.
Program Definition rebuild_u32 (s0_215 : int8) (s1_216 : int8) (s2_217 : int8) (
    s3_218 : int8)
  : both (fset.fset0) [interface] (int32) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) ((
          (fun x => lift_to_both0 (repr (unsigned x)))(
            lift_to_both0 s0_215)) .| (((
              (fun x => lift_to_both0 (repr (unsigned x)))(
                lift_to_both0 s1_216)) shift_left (lift_to_both0 (
                usize 8))) .| ((((fun x => lift_to_both0 (repr (unsigned x)))(
                  lift_to_both0 s2_217)) shift_left (lift_to_both0 (
                  usize 16))) .| (((fun x => lift_to_both0 (repr (unsigned x)))(
                  lift_to_both0 s3_218)) shift_left (lift_to_both0 (
                  usize 24))))))
      ) : both (fset.fset0) [interface] (int32)).
Fail Next Obligation.


Notation "'rebuild_u128_inp'" :=(
  int32 '× int32 '× int32 '× int32 : choice_type) (in custom pack_type at level 2).
Notation "'rebuild_u128_inp'" :=(
  int32 '× int32 '× int32 '× int32 : ChoiceEquality) (at level 2).
Notation "'rebuild_u128_out'" :=(
  int128 : choice_type) (in custom pack_type at level 2).
Notation "'rebuild_u128_out'" :=(int128 : ChoiceEquality) (at level 2).
Definition REBUILD_U128 : nat :=
  224.
Program Definition rebuild_u128 (s0_220 : int32) (s1_221 : int32) (
    s2_222 : int32) (s3_223 : int32)
  : both (fset.fset0) [interface] (int128) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) ((
          (fun x => lift_to_both0 (repr (unsigned x)))(
            lift_to_both0 s0_220)) .| (((
              (fun x => lift_to_both0 (repr (unsigned x)))(
                lift_to_both0 s1_221)) shift_left (lift_to_both0 (
                usize 32))) .| ((((fun x => lift_to_both0 (repr (unsigned x)))(
                  lift_to_both0 s2_222)) shift_left (lift_to_both0 (
                  usize 64))) .| (((fun x => lift_to_both0 (repr (unsigned x)))(
                  lift_to_both0 s3_223)) shift_left (lift_to_both0 (
                  usize 96))))))
      ) : both (fset.fset0) [interface] (int128)).
Fail Next Obligation.


Notation "'subword_inp'" :=(
  int32 : choice_type) (in custom pack_type at level 2).
Notation "'subword_inp'" :=(int32 : ChoiceEquality) (at level 2).
Notation "'subword_out'" :=(
  int32 : choice_type) (in custom pack_type at level 2).
Notation "'subword_out'" :=(int32 : ChoiceEquality) (at level 2).
Definition SUBWORD : nat :=
  226.
Program Definition subword (v_225 : int32)
  : both (fset.fset0) [interface] (int32) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (rebuild_u32 (array_index (
            sbox_v) (index_u8 (lift_to_both0 v_225) (lift_to_both0 (
                usize 0)))) (array_index (sbox_v) (index_u8 (
              lift_to_both0 v_225) (lift_to_both0 (usize 1)))) (array_index (
            sbox_v) (index_u8 (lift_to_both0 v_225) (lift_to_both0 (
                usize 2)))) (array_index (sbox_v) (index_u8 (
              lift_to_both0 v_225) (lift_to_both0 (usize 3)))))
      ) : both (fset.fset0) [interface] (int32)).
Fail Next Obligation.


Notation "'rotword_inp'" :=(
  int32 : choice_type) (in custom pack_type at level 2).
Notation "'rotword_inp'" :=(int32 : ChoiceEquality) (at level 2).
Notation "'rotword_out'" :=(
  int32 : choice_type) (in custom pack_type at level 2).
Notation "'rotword_out'" :=(int32 : ChoiceEquality) (at level 2).
Definition ROTWORD : nat :=
  228.
Program Definition rotword (v_227 : int32)
  : both (fset.fset0) [interface] (int32) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (((
            lift_to_both0 v_227) shift_right (lift_to_both0 (usize 8))) .| ((
            lift_to_both0 v_227) shift_left (lift_to_both0 (usize 24))))
      ) : both (fset.fset0) [interface] (int32)).
Fail Next Obligation.


Notation "'vpshufd1_inp'" :=(
  int128 '× int8 '× uint_size : choice_type) (in custom pack_type at level 2).
Notation "'vpshufd1_inp'" :=(
  int128 '× int8 '× uint_size : ChoiceEquality) (at level 2).
Notation "'vpshufd1_out'" :=(
  int32 : choice_type) (in custom pack_type at level 2).
Notation "'vpshufd1_out'" :=(int32 : ChoiceEquality) (at level 2).
Definition VPSHUFD1 : nat :=
  232.
Program Definition vpshufd1 (s_229 : int128) (o_230 : int8) (i_231 : uint_size)
  : both (fset.fset0) [interface] (int32) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (index_u32 ((
            lift_to_both0 s_229) shift_right ((lift_to_both0 (usize 32)) .* (
              (fun x => lift_to_both0 (repr (unsigned x)))(((
                    lift_to_both0 o_230) shift_right ((lift_to_both0 (
                        usize 2)) .* (lift_to_both0 i_231))) .% (lift_to_both0 (
                    @repr U8 4)))))) (lift_to_both0 (usize 0)))
      ) : both (fset.fset0) [interface] (int32)).
Fail Next Obligation.


Notation "'vpshufd_inp'" :=(
  int128 '× int8 : choice_type) (in custom pack_type at level 2).
Notation "'vpshufd_inp'" :=(int128 '× int8 : ChoiceEquality) (at level 2).
Notation "'vpshufd_out'" :=(
  int128 : choice_type) (in custom pack_type at level 2).
Notation "'vpshufd_out'" :=(int128 : ChoiceEquality) (at level 2).
Definition VPSHUFD : nat :=
  239.
Program Definition vpshufd (s_233 : int128) (o_234 : int8)
  : both (fset.fset0) [interface] (int128) :=
  ((letb d1_235 : int32 :=
        vpshufd1 (lift_to_both0 s_233) (lift_to_both0 o_234) (lift_to_both0 (
            usize 0)) in
      letb d2_236 : int32 :=
        vpshufd1 (lift_to_both0 s_233) (lift_to_both0 o_234) (lift_to_both0 (
            usize 1)) in
      letb d3_237 : int32 :=
        vpshufd1 (lift_to_both0 s_233) (lift_to_both0 o_234) (lift_to_both0 (
            usize 2)) in
      letb d4_238 : int32 :=
        vpshufd1 (lift_to_both0 s_233) (lift_to_both0 o_234) (lift_to_both0 (
            usize 3)) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (rebuild_u128 (
          lift_to_both0 d1_235) (lift_to_both0 d2_236) (lift_to_both0 d3_237) (
          lift_to_both0 d4_238))
      ) : both (fset.fset0) [interface] (int128)).
Fail Next Obligation.


Notation "'vshufps_inp'" :=(
  int128 '× int128 '× int8 : choice_type) (in custom pack_type at level 2).
Notation "'vshufps_inp'" :=(
  int128 '× int128 '× int8 : ChoiceEquality) (at level 2).
Notation "'vshufps_out'" :=(
  int128 : choice_type) (in custom pack_type at level 2).
Notation "'vshufps_out'" :=(int128 : ChoiceEquality) (at level 2).
Definition VSHUFPS : nat :=
  247.
Program Definition vshufps (s1_240 : int128) (s2_244 : int128) (o_241 : int8)
  : both (fset.fset0) [interface] (int128) :=
  ((letb d1_242 : int32 :=
        vpshufd1 (lift_to_both0 s1_240) (lift_to_both0 o_241) (lift_to_both0 (
            usize 0)) in
      letb d2_243 : int32 :=
        vpshufd1 (lift_to_both0 s1_240) (lift_to_both0 o_241) (lift_to_both0 (
            usize 1)) in
      letb d3_245 : int32 :=
        vpshufd1 (lift_to_both0 s2_244) (lift_to_both0 o_241) (lift_to_both0 (
            usize 2)) in
      letb d4_246 : int32 :=
        vpshufd1 (lift_to_both0 s2_244) (lift_to_both0 o_241) (lift_to_both0 (
            usize 3)) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (rebuild_u128 (
          lift_to_both0 d1_242) (lift_to_both0 d2_243) (lift_to_both0 d3_245) (
          lift_to_both0 d4_246))
      ) : both (fset.fset0) [interface] (int128)).
Fail Next Obligation.


Notation "'key_combine_inp'" :=(
  int128 '× int128 '× int128 : choice_type) (in custom pack_type at level 2).
Notation "'key_combine_inp'" :=(
  int128 '× int128 '× int128 : ChoiceEquality) (at level 2).
Notation "'key_combine_out'" :=((int128 '× int128
  ) : choice_type) (in custom pack_type at level 2).
Notation "'key_combine_out'" :=((int128 '× int128
  ) : ChoiceEquality) (at level 2).
Definition KEY_COMBINE : nat :=
  257.
Program Definition key_combine (rkey_251 : int128) (temp1_248 : int128) (
    temp2_250 : int128)
  : both (fset.fset0) [interface] ((int128 '× int128)) :=
  ((letb temp1_249 : int128 :=
        vpshufd (lift_to_both0 temp1_248) (lift_to_both0 (@repr U8 255)) in
      letb temp2_252 : int128 :=
        vshufps (lift_to_both0 temp2_250) (lift_to_both0 rkey_251) (
          lift_to_both0 (@repr U8 16)) in
      letb rkey_253 : int128 :=
        (lift_to_both0 rkey_251) .^ (lift_to_both0 temp2_252) in
      letb temp2_254 : int128 :=
        vshufps (lift_to_both0 temp2_252) (lift_to_both0 rkey_253) (
          lift_to_both0 (@repr U8 140)) in
      letb rkey_255 : int128 :=
        (lift_to_both0 rkey_253) .^ (lift_to_both0 temp2_254) in
      letb rkey_256 : int128 :=
        (lift_to_both0 rkey_255) .^ (lift_to_both0 temp1_249) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 rkey_256,
          lift_to_both0 temp2_254
        ))
      ) : both (fset.fset0) [interface] ((int128 '× int128))).
Fail Next Obligation.


Notation "'aeskeygenassist_inp'" :=(
  int128 '× int8 : choice_type) (in custom pack_type at level 2).
Notation "'aeskeygenassist_inp'" :=(
  int128 '× int8 : ChoiceEquality) (at level 2).
Notation "'aeskeygenassist_out'" :=(
  int128 : choice_type) (in custom pack_type at level 2).
Notation "'aeskeygenassist_out'" :=(int128 : ChoiceEquality) (at level 2).
Definition AESKEYGENASSIST : nat :=
  266.
Program Definition aeskeygenassist (v1_258 : int128) (v2_262 : int8)
  : both (fset.fset0) [interface] (int128) :=
  ((letb x1_259 : int32 :=
        index_u32 (lift_to_both0 v1_258) (lift_to_both0 (usize 1)) in
      letb x3_260 : int32 :=
        index_u32 (lift_to_both0 v1_258) (lift_to_both0 (usize 3)) in
      letb y0_261 : int32 := subword (lift_to_both0 x1_259) in
      letb y1_263 : int32 :=
        (rotword (lift_to_both0 y0_261)) .^ (
          (fun x => lift_to_both0 (repr (unsigned x)))(lift_to_both0 v2_262)) in
      letb y2_264 : int32 := subword (lift_to_both0 x3_260) in
      letb y3_265 : int32 :=
        (rotword (lift_to_both0 y2_264)) .^ (
          (fun x => lift_to_both0 (repr (unsigned x)))(lift_to_both0 v2_262)) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (rebuild_u128 (
          lift_to_both0 y0_261) (lift_to_both0 y1_263) (lift_to_both0 y2_264) (
          lift_to_both0 y3_265))
      ) : both (fset.fset0) [interface] (int128)).
Fail Next Obligation.


Notation "'key_expand_inp'" :=(
  int8 '× int128 '× int128 : choice_type) (in custom pack_type at level 2).
Notation "'key_expand_inp'" :=(
  int8 '× int128 '× int128 : ChoiceEquality) (at level 2).
Notation "'key_expand_out'" :=((int128 '× int128
  ) : choice_type) (in custom pack_type at level 2).
Notation "'key_expand_out'" :=((int128 '× int128
  ) : ChoiceEquality) (at level 2).
Definition KEY_EXPAND : nat :=
  273.
Program Definition key_expand (rcon_268 : int8) (rkey_267 : int128) (
    temp2_270 : int128)
  : both (fset.fset0) [interface] ((int128 '× int128)) :=
  ((letb temp1_269 : int128 :=
        aeskeygenassist (lift_to_both0 rkey_267) (lift_to_both0 rcon_268) in
      letb '(rkey_271, temp2_272) : (int128 '× int128) :=
        key_combine (lift_to_both0 rkey_267) (lift_to_both0 temp1_269) (
          lift_to_both0 temp2_270) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 rkey_271,
          lift_to_both0 temp2_272
        ))
      ) : both (fset.fset0) [interface] ((int128 '× int128))).
Fail Next Obligation.

Notation "'key_list_t'" := (seq int128) : hacspec_scope.

Definition key_275_loc : ChoiceEqualityLocation :=
  (int128 ; 277%nat).
Definition temp2_276_loc : ChoiceEqualityLocation :=
  (int128 ; 278%nat).
Definition rkeys_274_loc : ChoiceEqualityLocation :=
  (key_list_t ; 279%nat).
Notation "'keys_expand_inp'" :=(
  int128 : choice_type) (in custom pack_type at level 2).
Notation "'keys_expand_inp'" :=(int128 : ChoiceEquality) (at level 2).
Notation "'keys_expand_out'" :=(
  key_list_t : choice_type) (in custom pack_type at level 2).
Notation "'keys_expand_out'" :=(key_list_t : ChoiceEquality) (at level 2).
Definition KEYS_EXPAND : nat :=
  285.
Program Definition keys_expand (key_280 : int128)
  : both (CEfset ([rkeys_274_loc ; key_275_loc ; temp2_276_loc])) [interface] (
    key_list_t) :=
  ((letbm rkeys_274 : key_list_t loc( rkeys_274_loc ) :=
        seq_new_ (default : int128) (lift_to_both0 (usize 0)) in
      letbm key_275 : int128 loc( key_275_loc ) := lift_to_both0 key_280 in
      letbm temp2_276 : int128 loc( temp2_276_loc ) :=
        lift_to_both0 (@repr U128 0) in
      letbm rkeys_274 loc( rkeys_274_loc ) :=
        seq_push (lift_to_both0 rkeys_274) (lift_to_both0 key_275) in
      letb '(rkeys_274, key_275, temp2_276) :=
        foldi_both' (lift_to_both0 (usize 1)) (lift_to_both0 (
              usize 11)) prod_ce(rkeys_274, key_275, temp2_276) (L := (CEfset (
                [rkeys_274_loc ; key_275_loc ; temp2_276_loc]))) (
            I := [interface]) (fun round_281 '(rkeys_274, key_275, temp2_276) =>
            letb rcon_282 : int8 :=
              array_index (rcon_v) (lift_to_both0 round_281) in
            letb '(key_temp_283, temp2_temp_284) : (int128 '× int128) :=
              key_expand (lift_to_both0 rcon_282) (lift_to_both0 key_275) (
                lift_to_both0 temp2_276) in
            letbm key_275 loc( key_275_loc ) := lift_to_both0 key_temp_283 in
            letbm temp2_276 loc( temp2_276_loc ) :=
              lift_to_both0 temp2_temp_284 in
            letbm rkeys_274 loc( rkeys_274_loc ) :=
              seq_push (lift_to_both0 rkeys_274) (lift_to_both0 key_275) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                lift_to_both0 rkeys_274,
                lift_to_both0 key_275,
                lift_to_both0 temp2_276
              ))
            ) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 rkeys_274)
      ) : both (CEfset (
        [rkeys_274_loc ; key_275_loc ; temp2_276_loc])) [interface] (
      key_list_t)).
Fail Next Obligation.


Notation "'subbytes_inp'" :=(
  int128 : choice_type) (in custom pack_type at level 2).
Notation "'subbytes_inp'" :=(int128 : ChoiceEquality) (at level 2).
Notation "'subbytes_out'" :=(
  int128 : choice_type) (in custom pack_type at level 2).
Notation "'subbytes_out'" :=(int128 : ChoiceEquality) (at level 2).
Definition SUBBYTES : nat :=
  287.
Program Definition subbytes (s_286 : int128)
  : both (fset.fset0) [interface] (int128) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (rebuild_u128 (subword (
            index_u32 (lift_to_both0 s_286) (lift_to_both0 (usize 0)))) (
          subword (index_u32 (lift_to_both0 s_286) (lift_to_both0 (usize 1)))) (
          subword (index_u32 (lift_to_both0 s_286) (lift_to_both0 (usize 2)))) (
          subword (index_u32 (lift_to_both0 s_286) (lift_to_both0 (usize 3)))))
      ) : both (fset.fset0) [interface] (int128)).
Fail Next Obligation.


Notation "'matrix_index_inp'" :=(
  int128 '× uint_size '× uint_size : choice_type) (in custom pack_type at level 2).
Notation "'matrix_index_inp'" :=(
  int128 '× uint_size '× uint_size : ChoiceEquality) (at level 2).
Notation "'matrix_index_out'" :=(
  int8 : choice_type) (in custom pack_type at level 2).
Notation "'matrix_index_out'" :=(int8 : ChoiceEquality) (at level 2).
Definition MATRIX_INDEX : nat :=
  291.
Program Definition matrix_index (s_288 : int128) (i_290 : uint_size) (
    j_289 : uint_size)
  : both (fset.fset0) [interface] (int8) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (index_u8 (index_u32 (
            lift_to_both0 s_288) (lift_to_both0 j_289)) (lift_to_both0 i_290))
      ) : both (fset.fset0) [interface] (int8)).
Fail Next Obligation.


Notation "'shiftrows_inp'" :=(
  int128 : choice_type) (in custom pack_type at level 2).
Notation "'shiftrows_inp'" :=(int128 : ChoiceEquality) (at level 2).
Notation "'shiftrows_out'" :=(
  int128 : choice_type) (in custom pack_type at level 2).
Notation "'shiftrows_out'" :=(int128 : ChoiceEquality) (at level 2).
Definition SHIFTROWS : nat :=
  297.
Program Definition shiftrows (s_292 : int128)
  : both (fset.fset0) [interface] (int128) :=
  ((letb c0_293 : int32 :=
        rebuild_u32 (matrix_index (lift_to_both0 s_292) (lift_to_both0 (
              usize 0)) (lift_to_both0 (usize 0))) (matrix_index (
            lift_to_both0 s_292) (lift_to_both0 (usize 1)) (lift_to_both0 (
              usize 1))) (matrix_index (lift_to_both0 s_292) (lift_to_both0 (
              usize 2)) (lift_to_both0 (usize 2))) (matrix_index (
            lift_to_both0 s_292) (lift_to_both0 (usize 3)) (lift_to_both0 (
              usize 3))) in
      letb c1_294 : int32 :=
        rebuild_u32 (matrix_index (lift_to_both0 s_292) (lift_to_both0 (
              usize 0)) (lift_to_both0 (usize 1))) (matrix_index (
            lift_to_both0 s_292) (lift_to_both0 (usize 1)) (lift_to_both0 (
              usize 2))) (matrix_index (lift_to_both0 s_292) (lift_to_both0 (
              usize 2)) (lift_to_both0 (usize 3))) (matrix_index (
            lift_to_both0 s_292) (lift_to_both0 (usize 3)) (lift_to_both0 (
              usize 0))) in
      letb c2_295 : int32 :=
        rebuild_u32 (matrix_index (lift_to_both0 s_292) (lift_to_both0 (
              usize 0)) (lift_to_both0 (usize 2))) (matrix_index (
            lift_to_both0 s_292) (lift_to_both0 (usize 1)) (lift_to_both0 (
              usize 3))) (matrix_index (lift_to_both0 s_292) (lift_to_both0 (
              usize 2)) (lift_to_both0 (usize 0))) (matrix_index (
            lift_to_both0 s_292) (lift_to_both0 (usize 3)) (lift_to_both0 (
              usize 1))) in
      letb c3_296 : int32 :=
        rebuild_u32 (matrix_index (lift_to_both0 s_292) (lift_to_both0 (
              usize 0)) (lift_to_both0 (usize 3))) (matrix_index (
            lift_to_both0 s_292) (lift_to_both0 (usize 1)) (lift_to_both0 (
              usize 0))) (matrix_index (lift_to_both0 s_292) (lift_to_both0 (
              usize 2)) (lift_to_both0 (usize 1))) (matrix_index (
            lift_to_both0 s_292) (lift_to_both0 (usize 3)) (lift_to_both0 (
              usize 2))) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (rebuild_u128 (
          lift_to_both0 c0_293) (lift_to_both0 c1_294) (lift_to_both0 c2_295) (
          lift_to_both0 c3_296))
      ) : both (fset.fset0) [interface] (int128)).
Fail Next Obligation.


Notation "'xtime_inp'" :=(int8 : choice_type) (in custom pack_type at level 2).
Notation "'xtime_inp'" :=(int8 : ChoiceEquality) (at level 2).
Notation "'xtime_out'" :=(int8 : choice_type) (in custom pack_type at level 2).
Notation "'xtime_out'" :=(int8 : ChoiceEquality) (at level 2).
Definition XTIME : nat :=
  303.
Program Definition xtime (x_298 : int8)
  : both (fset.fset0) [interface] (int8) :=
  ((letb x1_299 : int8 :=
        (lift_to_both0 x_298) shift_left (lift_to_both0 (usize 1)) in
      letb x7_300 : int8 :=
        (lift_to_both0 x_298) shift_right (lift_to_both0 (usize 7)) in
      letb x71_301 : int8 :=
        (lift_to_both0 x7_300) .& (lift_to_both0 (@repr U8 1)) in
      letb x711b_302 : int8 :=
        (lift_to_both0 x71_301) .* (lift_to_both0 (@repr U8 27)) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) ((
          lift_to_both0 x1_299) .^ (lift_to_both0 x711b_302))
      ) : both (fset.fset0) [interface] (int8)).
Fail Next Obligation.


Notation "'mixcolumn_inp'" :=(
  uint_size '× int128 : choice_type) (in custom pack_type at level 2).
Notation "'mixcolumn_inp'" :=(
  uint_size '× int128 : ChoiceEquality) (at level 2).
Notation "'mixcolumn_out'" :=(
  int32 : choice_type) (in custom pack_type at level 2).
Notation "'mixcolumn_out'" :=(int32 : ChoiceEquality) (at level 2).
Definition MIXCOLUMN : nat :=
  315.
Program Definition mixcolumn (c_305 : uint_size) (state_304 : int128)
  : both (fset.fset0) [interface] (int32) :=
  ((letb s0_306 : int8 :=
        matrix_index (lift_to_both0 state_304) (lift_to_both0 (usize 0)) (
          lift_to_both0 c_305) in
      letb s1_307 : int8 :=
        matrix_index (lift_to_both0 state_304) (lift_to_both0 (usize 1)) (
          lift_to_both0 c_305) in
      letb s2_308 : int8 :=
        matrix_index (lift_to_both0 state_304) (lift_to_both0 (usize 2)) (
          lift_to_both0 c_305) in
      letb s3_309 : int8 :=
        matrix_index (lift_to_both0 state_304) (lift_to_both0 (usize 3)) (
          lift_to_both0 c_305) in
      letb tmp_310 : int8 :=
        (((lift_to_both0 s0_306) .^ (lift_to_both0 s1_307)) .^ (
            lift_to_both0 s2_308)) .^ (lift_to_both0 s3_309) in
      letb r0_311 : int8 :=
        ((lift_to_both0 s0_306) .^ (lift_to_both0 tmp_310)) .^ (xtime ((
              lift_to_both0 s0_306) .^ (lift_to_both0 s1_307))) in
      letb r1_312 : int8 :=
        ((lift_to_both0 s1_307) .^ (lift_to_both0 tmp_310)) .^ (xtime ((
              lift_to_both0 s1_307) .^ (lift_to_both0 s2_308))) in
      letb r2_313 : int8 :=
        ((lift_to_both0 s2_308) .^ (lift_to_both0 tmp_310)) .^ (xtime ((
              lift_to_both0 s2_308) .^ (lift_to_both0 s3_309))) in
      letb r3_314 : int8 :=
        ((lift_to_both0 s3_309) .^ (lift_to_both0 tmp_310)) .^ (xtime ((
              lift_to_both0 s3_309) .^ (lift_to_both0 s0_306))) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (rebuild_u32 (
          lift_to_both0 r0_311) (lift_to_both0 r1_312) (lift_to_both0 r2_313) (
          lift_to_both0 r3_314))
      ) : both (fset.fset0) [interface] (int32)).
Fail Next Obligation.


Notation "'mixcolumns_inp'" :=(
  int128 : choice_type) (in custom pack_type at level 2).
Notation "'mixcolumns_inp'" :=(int128 : ChoiceEquality) (at level 2).
Notation "'mixcolumns_out'" :=(
  int128 : choice_type) (in custom pack_type at level 2).
Notation "'mixcolumns_out'" :=(int128 : ChoiceEquality) (at level 2).
Definition MIXCOLUMNS : nat :=
  321.
Program Definition mixcolumns (state_316 : int128)
  : both (fset.fset0) [interface] (int128) :=
  ((letb c0_317 : int32 :=
        mixcolumn (lift_to_both0 (usize 0)) (lift_to_both0 state_316) in
      letb c1_318 : int32 :=
        mixcolumn (lift_to_both0 (usize 1)) (lift_to_both0 state_316) in
      letb c2_319 : int32 :=
        mixcolumn (lift_to_both0 (usize 2)) (lift_to_both0 state_316) in
      letb c3_320 : int32 :=
        mixcolumn (lift_to_both0 (usize 3)) (lift_to_both0 state_316) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (rebuild_u128 (
          lift_to_both0 c0_317) (lift_to_both0 c1_318) (lift_to_both0 c2_319) (
          lift_to_both0 c3_320))
      ) : both (fset.fset0) [interface] (int128)).
Fail Next Obligation.


Notation "'aesenc_inp'" :=(
  int128 '× int128 : choice_type) (in custom pack_type at level 2).
Notation "'aesenc_inp'" :=(int128 '× int128 : ChoiceEquality) (at level 2).
Notation "'aesenc_out'" :=(
  int128 : choice_type) (in custom pack_type at level 2).
Notation "'aesenc_out'" :=(int128 : ChoiceEquality) (at level 2).
Definition AESENC : nat :=
  327.
Program Definition aesenc (state_322 : int128) (rkey_326 : int128)
  : both (fset.fset0) [interface] (int128) :=
  ((letb state_323 : int128 := subbytes (lift_to_both0 state_322) in
      letb state_324 : int128 := shiftrows (lift_to_both0 state_323) in
      letb state_325 : int128 := mixcolumns (lift_to_both0 state_324) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) ((
          lift_to_both0 state_325) .^ (lift_to_both0 rkey_326))
      ) : both (fset.fset0) [interface] (int128)).
Fail Next Obligation.


Notation "'aesenclast_inp'" :=(
  int128 '× int128 : choice_type) (in custom pack_type at level 2).
Notation "'aesenclast_inp'" :=(int128 '× int128 : ChoiceEquality) (at level 2).
Notation "'aesenclast_out'" :=(
  int128 : choice_type) (in custom pack_type at level 2).
Notation "'aesenclast_out'" :=(int128 : ChoiceEquality) (at level 2).
Definition AESENCLAST : nat :=
  332.
Program Definition aesenclast (state_328 : int128) (rkey_331 : int128)
  : both (fset.fset0) [interface] (int128) :=
  ((letb state_329 : int128 := subbytes (lift_to_both0 state_328) in
      letb state_330 : int128 := shiftrows (lift_to_both0 state_329) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) ((
          lift_to_both0 state_330) .^ (lift_to_both0 rkey_331))
      ) : both (fset.fset0) [interface] (int128)).
Fail Next Obligation.

Definition state_333_loc : ChoiceEqualityLocation :=
  (int128 ; 334%nat).
Notation "'aes_rounds_inp'" :=(
  key_list_t '× int128 : choice_type) (in custom pack_type at level 2).
Notation "'aes_rounds_inp'" :=(
  key_list_t '× int128 : ChoiceEquality) (at level 2).
Notation "'aes_rounds_out'" :=(
  int128 : choice_type) (in custom pack_type at level 2).
Notation "'aes_rounds_out'" :=(int128 : ChoiceEquality) (at level 2).
Definition AES_ROUNDS : nat :=
  338.
Program Definition aes_rounds (rkeys_336 : key_list_t) (inp_335 : int128)
  : both (CEfset ([state_333_loc])) [interface] (int128) :=
  ((letbm state_333 : int128 loc( state_333_loc ) :=
        (lift_to_both0 inp_335) .^ (seq_index (rkeys_336) (lift_to_both0 (
              usize 0))) in
      letb state_333 :=
        foldi_both' (lift_to_both0 (usize 1)) (lift_to_both0 (
              usize 10)) state_333 (L := (CEfset ([state_333_loc]))) (
            I := [interface]) (fun round_337 state_333 =>
            letbm state_333 loc( state_333_loc ) :=
              aesenc (lift_to_both0 state_333) (seq_index (rkeys_336) (
                  lift_to_both0 round_337)) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 state_333)
            ) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (aesenclast (
          lift_to_both0 state_333) (seq_index (rkeys_336) (lift_to_both0 (
              usize 10))))
      ) : both (CEfset ([state_333_loc])) [interface] (int128)).
Fail Next Obligation.


Notation "'aes_inp'" :=(
  int128 '× int128 : choice_type) (in custom pack_type at level 2).
Notation "'aes_inp'" :=(int128 '× int128 : ChoiceEquality) (at level 2).
Notation "'aes_out'" :=(int128 : choice_type) (in custom pack_type at level 2).
Notation "'aes_out'" :=(int128 : ChoiceEquality) (at level 2).
Definition AES : nat :=
  342.
Program Definition aes (key_339 : int128) (inp_341 : int128)
  : both (CEfset (
      [rkeys_274_loc ; key_275_loc ; temp2_276_loc ; state_333_loc])) [interface] (
    int128) :=
  ((letb rkeys_340 : seq int128 := keys_expand (lift_to_both0 key_339) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (aes_rounds (
          lift_to_both0 rkeys_340) (lift_to_both0 inp_341))
      ) : both (CEfset (
        [rkeys_274_loc ; key_275_loc ; temp2_276_loc ; state_333_loc])) [interface] (
      int128)).
Fail Next Obligation.

