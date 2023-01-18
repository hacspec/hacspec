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


Notation "'vpshufd1_inp'" :=(
  int128 '× int8 '× uint_size : choice_type) (in custom pack_type at level 2).
Notation "'vpshufd1_inp'" :=(
  int128 '× int8 '× uint_size : ChoiceEquality) (at level 2).
Notation "'vpshufd1_out'" :=(
  int32 : choice_type) (in custom pack_type at level 2).
Notation "'vpshufd1_out'" :=(int32 : ChoiceEquality) (at level 2).
Definition VPSHUFD1 : nat :=
  212.
Program Definition vpshufd1 (s_209 : int128) (o_210 : int8) (i_211 : uint_size)
  : both (fset.fset0) [interface] (int32) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        (fun x => lift_to_both0 (repr (unsigned x)))((
            lift_to_both0 s_209) shift_right ((lift_to_both0 (usize 32)) .* (((
                  (fun x => lift_to_both0 (repr (unsigned x)))(
                    lift_to_both0 o_210)) usize_shift_right ((lift_to_both0 (
                      usize 2)) .* (lift_to_both0 i_211))) .% (lift_to_both0 (
                  usize 4))))))
      ) : both (fset.fset0) [interface] (int32)).
Fail Next Obligation.


Notation "'vpshufd_inp'" :=(
  int128 '× int8 : choice_type) (in custom pack_type at level 2).
Notation "'vpshufd_inp'" :=(int128 '× int8 : ChoiceEquality) (at level 2).
Notation "'vpshufd_out'" :=(
  int128 : choice_type) (in custom pack_type at level 2).
Notation "'vpshufd_out'" :=(int128 : ChoiceEquality) (at level 2).
Definition VPSHUFD : nat :=
  219.
Program Definition vpshufd (s_213 : int128) (o_214 : int8)
  : both (fset.fset0) [interface] (int128) :=
  ((letb d1_215 : int32 :=
        vpshufd1 (lift_to_both0 s_213) (lift_to_both0 o_214) (lift_to_both0 (
            usize 0)) in
      letb d2_216 : int32 :=
        vpshufd1 (lift_to_both0 s_213) (lift_to_both0 o_214) (lift_to_both0 (
            usize 1)) in
      letb d3_217 : int32 :=
        vpshufd1 (lift_to_both0 s_213) (lift_to_both0 o_214) (lift_to_both0 (
            usize 2)) in
      letb d4_218 : int32 :=
        vpshufd1 (lift_to_both0 s_213) (lift_to_both0 o_214) (lift_to_both0 (
            usize 3)) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) ((((
              (fun x => lift_to_both0 (repr (unsigned x)))(
                lift_to_both0 d1_215)) .| ((
                (fun x => lift_to_both0 (repr (unsigned x)))(
                  lift_to_both0 d2_216)) shift_left (lift_to_both0 (
                  usize 32)))) .| ((
              (fun x => lift_to_both0 (repr (unsigned x)))(
                lift_to_both0 d3_217)) shift_left (lift_to_both0 (
                usize 64)))) .| (((fun x => lift_to_both0 (repr (unsigned x)))(
              lift_to_both0 d4_218)) shift_left (lift_to_both0 (usize 96))))
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
  227.
Program Definition vshufps (s1_220 : int128) (s2_224 : int128) (o_221 : int8)
  : both (fset.fset0) [interface] (int128) :=
  ((letb d1_222 : int32 :=
        vpshufd1 (lift_to_both0 s1_220) (lift_to_both0 o_221) (lift_to_both0 (
            usize 0)) in
      letb d2_223 : int32 :=
        vpshufd1 (lift_to_both0 s1_220) (lift_to_both0 o_221) (lift_to_both0 (
            usize 1)) in
      letb d3_225 : int32 :=
        vpshufd1 (lift_to_both0 s2_224) (lift_to_both0 o_221) (lift_to_both0 (
            usize 2)) in
      letb d4_226 : int32 :=
        vpshufd1 (lift_to_both0 s2_224) (lift_to_both0 o_221) (lift_to_both0 (
            usize 3)) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) ((((
              (fun x => lift_to_both0 (repr (unsigned x)))(
                lift_to_both0 d1_222)) .| ((
                (fun x => lift_to_both0 (repr (unsigned x)))(
                  lift_to_both0 d2_223)) shift_left (lift_to_both0 (
                  usize 32)))) .| ((
              (fun x => lift_to_both0 (repr (unsigned x)))(
                lift_to_both0 d3_225)) shift_left (lift_to_both0 (
                usize 64)))) .| (((fun x => lift_to_both0 (repr (unsigned x)))(
              lift_to_both0 d4_226)) shift_left (lift_to_both0 (usize 96))))
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
  237.
Program Definition key_combine (rkey_231 : int128) (temp1_228 : int128) (
    temp2_230 : int128)
  : both (fset.fset0) [interface] ((int128 '× int128)) :=
  ((letb temp1_229 : int128 :=
        vpshufd (lift_to_both0 temp1_228) (lift_to_both0 (@repr U8 255)) in
      letb temp2_232 : int128 :=
        vshufps (lift_to_both0 temp2_230) (lift_to_both0 rkey_231) (
          lift_to_both0 (@repr U8 16)) in
      letb rkey_233 : int128 :=
        (lift_to_both0 rkey_231) .^ (lift_to_both0 temp2_232) in
      letb temp2_234 : int128 :=
        vshufps (lift_to_both0 temp2_232) (lift_to_both0 rkey_233) (
          lift_to_both0 (@repr U8 140)) in
      letb rkey_235 : int128 :=
        (lift_to_both0 rkey_233) .^ (lift_to_both0 temp2_234) in
      letb rkey_236 : int128 :=
        (lift_to_both0 rkey_235) .^ (lift_to_both0 temp1_229) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 rkey_236,
          lift_to_both0 temp2_234
        ))
      ) : both (fset.fset0) [interface] ((int128 '× int128))).
Fail Next Obligation.


Notation "'index_u32_inp'" :=(
  int128 '× uint_size : choice_type) (in custom pack_type at level 2).
Notation "'index_u32_inp'" :=(
  int128 '× uint_size : ChoiceEquality) (at level 2).
Notation "'index_u32_out'" :=(
  int32 : choice_type) (in custom pack_type at level 2).
Notation "'index_u32_out'" :=(int32 : ChoiceEquality) (at level 2).
Definition INDEX_U32 : nat :=
  240.
Program Definition index_u32 (s_238 : int128) (i_239 : uint_size)
  : both (fset.fset0) [interface] (int32) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        (fun x => lift_to_both0 (repr (unsigned x)))(((
              lift_to_both0 s_238) shift_right ((lift_to_both0 i_239) .* (
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
  243.
Program Definition index_u8 (s_241 : int32) (i_242 : uint_size)
  : both (fset.fset0) [interface] (int8) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        (fun x => lift_to_both0 (repr (unsigned x)))(((
              lift_to_both0 s_241) shift_right ((lift_to_both0 i_242) .* (
                lift_to_both0 (usize 8)))) .% ((lift_to_both0 (
                @repr U32 1)) shift_left (lift_to_both0 (usize 8)))))
      ) : both (fset.fset0) [interface] (int8)).
Fail Next Obligation.


Notation "'index_u8_u128_inp'" :=(
  int128 '× uint_size : choice_type) (in custom pack_type at level 2).
Notation "'index_u8_u128_inp'" :=(
  int128 '× uint_size : ChoiceEquality) (at level 2).
Notation "'index_u8_u128_out'" :=(
  int8 : choice_type) (in custom pack_type at level 2).
Notation "'index_u8_u128_out'" :=(int8 : ChoiceEquality) (at level 2).
Definition INDEX_U8_U128 : nat :=
  246.
Program Definition index_u8_u128 (s_244 : int128) (i_245 : uint_size)
  : both (fset.fset0) [interface] (int8) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        (fun x => lift_to_both0 (repr (unsigned x)))(((
              lift_to_both0 s_244) shift_right ((lift_to_both0 i_245) .* (
                lift_to_both0 (usize 8)))) .% ((lift_to_both0 (
                @repr U128 1)) shift_left (lift_to_both0 (usize 8)))))
      ) : both (fset.fset0) [interface] (int8)).
Fail Next Obligation.


Notation "'set_index_u128_inp'" :=(
  int128 '× uint_size '× int8 : choice_type) (in custom pack_type at level 2).
Notation "'set_index_u128_inp'" :=(
  int128 '× uint_size '× int8 : ChoiceEquality) (at level 2).
Notation "'set_index_u128_out'" :=(
  int128 : choice_type) (in custom pack_type at level 2).
Notation "'set_index_u128_out'" :=(int128 : ChoiceEquality) (at level 2).
Definition SET_INDEX_U128 : nat :=
  250.
Program Definition set_index_u128 (s_247 : int128) (c_248 : uint_size) (
    v_249 : int8)
  : both (fset.fset0) [interface] (int128) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (((
            lift_to_both0 s_247) .- ((
              (fun x => lift_to_both0 (repr (unsigned x)))(index_u8_u128 (
                  lift_to_both0 s_247) (lift_to_both0 c_248))) shift_left ((
                lift_to_both0 c_248) .* (lift_to_both0 (usize 8))))) .+ ((
            (fun x => lift_to_both0 (repr (unsigned x)))(
              lift_to_both0 v_249)) shift_left ((lift_to_both0 c_248) .* (
              lift_to_both0 (usize 8)))))
      ) : both (fset.fset0) [interface] (int128)).
Fail Next Obligation.


Notation "'rebuild_u32_inp'" :=(
  int8 '× int8 '× int8 '× int8 : choice_type) (in custom pack_type at level 2).
Notation "'rebuild_u32_inp'" :=(
  int8 '× int8 '× int8 '× int8 : ChoiceEquality) (at level 2).
Notation "'rebuild_u32_out'" :=(
  int32 : choice_type) (in custom pack_type at level 2).
Notation "'rebuild_u32_out'" :=(int32 : ChoiceEquality) (at level 2).
Definition REBUILD_U32 : nat :=
  255.
Program Definition rebuild_u32 (s0_251 : int8) (s1_252 : int8) (s2_253 : int8) (
    s3_254 : int8)
  : both (fset.fset0) [interface] (int32) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) ((((
              (fun x => lift_to_both0 (repr (unsigned x)))(
                lift_to_both0 s0_251)) .| ((
                (fun x => lift_to_both0 (repr (unsigned x)))(
                  lift_to_both0 s1_252)) shift_left (lift_to_both0 (
                  usize 8)))) .| (((fun x => lift_to_both0 (repr (unsigned x)))(
                lift_to_both0 s2_253)) shift_left (lift_to_both0 (
                usize 16)))) .| (((fun x => lift_to_both0 (repr (unsigned x)))(
              lift_to_both0 s3_254)) shift_left (lift_to_both0 (usize 24))))
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
  260.
Program Definition rebuild_u128 (s0_256 : int32) (s1_257 : int32) (
    s2_258 : int32) (s3_259 : int32)
  : both (fset.fset0) [interface] (int128) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) ((((
              (fun x => lift_to_both0 (repr (unsigned x)))(
                lift_to_both0 s0_256)) .| ((
                (fun x => lift_to_both0 (repr (unsigned x)))(
                  lift_to_both0 s1_257)) shift_left (lift_to_both0 (
                  usize 32)))) .| ((
              (fun x => lift_to_both0 (repr (unsigned x)))(
                lift_to_both0 s2_258)) shift_left (lift_to_both0 (
                usize 64)))) .| (((fun x => lift_to_both0 (repr (unsigned x)))(
              lift_to_both0 s3_259)) shift_left (lift_to_both0 (usize 96))))
      ) : both (fset.fset0) [interface] (int128)).
Fail Next Obligation.

Definition res_261_loc : ChoiceEqualityLocation :=
  (u32_word_t ; 262%nat).
Notation "'subword_inp'" :=(
  int32 : choice_type) (in custom pack_type at level 2).
Notation "'subword_inp'" :=(int32 : ChoiceEquality) (at level 2).
Notation "'subword_out'" :=(
  int32 : choice_type) (in custom pack_type at level 2).
Notation "'subword_out'" :=(int32 : ChoiceEquality) (at level 2).
Definition SUBWORD : nat :=
  266.
Program Definition subword (v_263 : int32)
  : both (CEfset ([res_261_loc])) [interface] (int32) :=
  ((letb vs_264 : u32_word_t := u32_to_be_bytes (lift_to_both0 v_263) in
      letbm res_261 : u32_word_t loc( res_261_loc ) :=
        array_new_ (default : int8) (4) in
      letb res_261 :=
        foldi_both' (lift_to_both0 (usize 0)) (lift_to_both0 (
              usize 4)) res_261 (L := (CEfset ([res_261_loc]))) (
            I := [interface]) (fun i_265 res_261 =>
            letb res_261 : u32_word_t :=
              array_upd res_261 (lift_to_both0 i_265) (is_pure (array_index (
                    sbox_v) (array_index (vs_264) ((lift_to_both0 (
                          usize 3)) .- (lift_to_both0 i_265))))) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 res_261)
            ) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (u32_from_be_bytes (
          lift_to_both0 res_261))
      ) : both (CEfset ([res_261_loc])) [interface] (int32)).
Fail Next Obligation.


Notation "'ror_inp'" :=(
  int32 '× uint_size : choice_type) (in custom pack_type at level 2).
Notation "'ror_inp'" :=(int32 '× uint_size : ChoiceEquality) (at level 2).
Notation "'ror_out'" :=(int32 : choice_type) (in custom pack_type at level 2).
Notation "'ror_out'" :=(int32 : ChoiceEquality) (at level 2).
Definition ROR : nat :=
  269.
Program Definition ror (v_267 : int32) (i_268 : uint_size)
  : both (fset.fset0) [interface] (int32) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (((
            lift_to_both0 v_267) shift_right (lift_to_both0 i_268)) .| ((
            lift_to_both0 v_267) shift_left ((lift_to_both0 (usize 32)) .- (
              lift_to_both0 i_268))))
      ) : both (fset.fset0) [interface] (int32)).
Fail Next Obligation.


Notation "'aeskeygenassist_inp'" :=(
  int128 '× int8 : choice_type) (in custom pack_type at level 2).
Notation "'aeskeygenassist_inp'" :=(
  int128 '× int8 : ChoiceEquality) (at level 2).
Notation "'aeskeygenassist_out'" :=(
  int128 : choice_type) (in custom pack_type at level 2).
Notation "'aeskeygenassist_out'" :=(int128 : ChoiceEquality) (at level 2).
Definition AESKEYGENASSIST : nat :=
  278.
Program Definition aeskeygenassist (v1_270 : int128) (v2_274 : int8)
  : both (CEfset ([res_261_loc])) [interface] (int128) :=
  ((letb x1_271 : int32 :=
        index_u32 (lift_to_both0 v1_270) (lift_to_both0 (usize 1)) in
      letb x3_272 : int32 :=
        index_u32 (lift_to_both0 v1_270) (lift_to_both0 (usize 3)) in
      letb y0_273 : int32 :=
        subword ((fun x => lift_to_both0 (repr (unsigned x)))(
            lift_to_both0 x1_271)) in
      letb y1_275 : int32 :=
        (ror (lift_to_both0 y0_273) (lift_to_both0 (usize 1))) .^ (
          (fun x => lift_to_both0 (repr (unsigned x)))(lift_to_both0 v2_274)) in
      letb y2_276 : int32 :=
        subword ((fun x => lift_to_both0 (repr (unsigned x)))(
            lift_to_both0 x3_272)) in
      letb y3_277 : int32 :=
        (ror (lift_to_both0 y2_276) (lift_to_both0 (usize 1))) .^ (
          (fun x => lift_to_both0 (repr (unsigned x)))(lift_to_both0 v2_274)) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (rebuild_u128 (
          lift_to_both0 y0_273) (lift_to_both0 y1_275) (lift_to_both0 y2_276) (
          lift_to_both0 y3_277))
      ) : both (CEfset ([res_261_loc])) [interface] (int128)).
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
  283.
Program Definition key_expand (rcon_280 : int8) (rkey_279 : int128) (
    temp2_282 : int128)
  : both (CEfset ([res_261_loc])) [interface] ((int128 '× int128)) :=
  ((letb temp1_281 : int128 :=
        aeskeygenassist (lift_to_both0 rkey_279) (lift_to_both0 rcon_280) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (key_combine (
          lift_to_both0 rkey_279) (lift_to_both0 temp1_281) (
          lift_to_both0 temp2_282))
      ) : both (CEfset ([res_261_loc])) [interface] ((int128 '× int128))).
Fail Next Obligation.


Notation "'aes_subword_inp'" :=(
  int32 : choice_type) (in custom pack_type at level 2).
Notation "'aes_subword_inp'" :=(int32 : ChoiceEquality) (at level 2).
Notation "'aes_subword_out'" :=(
  int32 : choice_type) (in custom pack_type at level 2).
Notation "'aes_subword_out'" :=(int32 : ChoiceEquality) (at level 2).
Definition AES_SUBWORD : nat :=
  285.
Program Definition aes_subword (v_284 : int32)
  : both (fset.fset0) [interface] (int32) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (rebuild_u32 (array_index (
            sbox_v) (index_u8 (lift_to_both0 v_284) (lift_to_both0 (
                usize 0)))) (array_index (sbox_v) (index_u8 (
              lift_to_both0 v_284) (lift_to_both0 (usize 1)))) (array_index (
            sbox_v) (index_u8 (lift_to_both0 v_284) (lift_to_both0 (
                usize 2)))) (array_index (sbox_v) (index_u8 (
              lift_to_both0 v_284) (lift_to_both0 (usize 3)))))
      ) : both (fset.fset0) [interface] (int32)).
Fail Next Obligation.


Notation "'key_expand_alt_inp'" :=(
  int8 '× int128 : choice_type) (in custom pack_type at level 2).
Notation "'key_expand_alt_inp'" :=(
  int8 '× int128 : ChoiceEquality) (at level 2).
Notation "'key_expand_alt_out'" :=(
  int128 : choice_type) (in custom pack_type at level 2).
Notation "'key_expand_alt_out'" :=(int128 : ChoiceEquality) (at level 2).
Definition KEY_EXPAND_ALT : nat :=
  295.
Program Definition key_expand_alt (rcon_289 : int8) (rkey_286 : int128)
  : both (fset.fset0) [interface] (int128) :=
  ((letb r0_287 : int32 :=
        ror (index_u32 (lift_to_both0 rkey_286) (lift_to_both0 (usize 0))) (
          lift_to_both0 (usize 24)) in
      letb s0_288 : int32 := aes_subword (lift_to_both0 r0_287) in
      letb temp0_290 : int32 :=
        (lift_to_both0 s0_288) .^ ((
            (fun x => lift_to_both0 (repr (unsigned x)))(
              lift_to_both0 rcon_289)) shift_left (lift_to_both0 (usize 24))) in
      letb v0_291 : int32 :=
        (lift_to_both0 temp0_290) .^ (index_u32 (lift_to_both0 rkey_286) (
            lift_to_both0 (usize 3))) in
      letb v1_292 : int32 :=
        (lift_to_both0 v0_291) .^ (index_u32 (lift_to_both0 rkey_286) (
            lift_to_both0 (usize 2))) in
      letb v2_293 : int32 :=
        (lift_to_both0 v1_292) .^ (index_u32 (lift_to_both0 rkey_286) (
            lift_to_both0 (usize 1))) in
      letb v3_294 : int32 :=
        (lift_to_both0 v2_293) .^ (index_u32 (lift_to_both0 rkey_286) (
            lift_to_both0 (usize 0))) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (rebuild_u128 (
          lift_to_both0 v3_294) (lift_to_both0 v2_293) (lift_to_both0 v1_292) (
          lift_to_both0 v0_291))
      ) : both (fset.fset0) [interface] (int128)).
Fail Next Obligation.

Notation "'key_list_t'" := (seq int128) : hacspec_scope.

Definition key_298_loc : ChoiceEqualityLocation :=
  (int128 ; 299%nat).
Definition temp2_297_loc : ChoiceEqualityLocation :=
  (int128 ; 300%nat).
Definition rkeys_296_loc : ChoiceEqualityLocation :=
  (key_list_t ; 301%nat).
Notation "'keys_expand_inp'" :=(
  int128 : choice_type) (in custom pack_type at level 2).
Notation "'keys_expand_inp'" :=(int128 : ChoiceEquality) (at level 2).
Notation "'keys_expand_out'" :=(
  key_list_t : choice_type) (in custom pack_type at level 2).
Notation "'keys_expand_out'" :=(key_list_t : ChoiceEquality) (at level 2).
Definition KEYS_EXPAND : nat :=
  305.
Program Definition keys_expand (key_302 : int128)
  : both (CEfset ([rkeys_296_loc ; temp2_297_loc ; key_298_loc])) [interface] (
    key_list_t) :=
  ((letbm rkeys_296 : key_list_t loc( rkeys_296_loc ) :=
        seq_new_ (default : int128) (lift_to_both0 (usize 0)) in
      letbm rkeys_296 loc( rkeys_296_loc ) :=
        seq_push (lift_to_both0 rkeys_296) (lift_to_both0 key_302) in
      letbm temp2_297 : int128 loc( temp2_297_loc ) :=
        lift_to_both0 (@repr U128 0) in
      letbm key_298 : int128 loc( key_298_loc ) := lift_to_both0 key_302 in
      letb '(rkeys_296, key_298) :=
        foldi_both' (lift_to_both0 (usize 1)) (lift_to_both0 (
              usize 12)) prod_ce(rkeys_296, key_298) (L := (CEfset (
                [rkeys_296_loc ; temp2_297_loc ; key_298_loc]))) (
            I := [interface]) (fun round_303 '(rkeys_296, key_298) =>
            letb rcon_304 : int8 :=
              array_index (rcon_v) (lift_to_both0 round_303) in
            letbm key_298 loc( key_298_loc ) :=
              key_expand_alt (lift_to_both0 rcon_304) (lift_to_both0 key_298) in
            letbm rkeys_296 loc( rkeys_296_loc ) :=
              seq_push (lift_to_both0 rkeys_296) (lift_to_both0 key_298) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                lift_to_both0 rkeys_296,
                lift_to_both0 key_298
              ))
            ) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 rkeys_296)
      ) : both (CEfset (
        [rkeys_296_loc ; temp2_297_loc ; key_298_loc])) [interface] (
      key_list_t)).
Fail Next Obligation.


Notation "'sub_bytes_inp'" :=(
  int128 : choice_type) (in custom pack_type at level 2).
Notation "'sub_bytes_inp'" :=(int128 : ChoiceEquality) (at level 2).
Notation "'sub_bytes_out'" :=(
  int128 : choice_type) (in custom pack_type at level 2).
Notation "'sub_bytes_out'" :=(int128 : ChoiceEquality) (at level 2).
Definition SUBBYTES : nat :=
  307.
Program Definition sub_bytes (s_306 : int128)
  : both (fset.fset0) [interface] (int128) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (rebuild_u128 (
          aes_subword (index_u32 (lift_to_both0 s_306) (lift_to_both0 (
                usize 0)))) (aes_subword (index_u32 (lift_to_both0 s_306) (
              lift_to_both0 (usize 1)))) (aes_subword (index_u32 (
              lift_to_both0 s_306) (lift_to_both0 (usize 2)))) (aes_subword (
            index_u32 (lift_to_both0 s_306) (lift_to_both0 (usize 3)))))
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
  311.
Program Definition matrix_index (s_308 : int128) (i_310 : uint_size) (
    j_309 : uint_size)
  : both (fset.fset0) [interface] (int8) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (index_u8 (index_u32 (
            lift_to_both0 s_308) (lift_to_both0 j_309)) (lift_to_both0 i_310))
      ) : both (fset.fset0) [interface] (int8)).
Fail Next Obligation.


Notation "'shift_rows_inp'" :=(
  int128 : choice_type) (in custom pack_type at level 2).
Notation "'shift_rows_inp'" :=(int128 : ChoiceEquality) (at level 2).
Notation "'shift_rows_out'" :=(
  int128 : choice_type) (in custom pack_type at level 2).
Notation "'shift_rows_out'" :=(int128 : ChoiceEquality) (at level 2).
Definition SHIFTROWS : nat :=
  317.
Program Definition shift_rows (s_312 : int128)
  : both (fset.fset0) [interface] (int128) :=
  ((letb r0_313 : int32 :=
        rebuild_u32 (matrix_index (lift_to_both0 s_312) (lift_to_both0 (
              usize 0)) (lift_to_both0 (usize 1))) (matrix_index (
            lift_to_both0 s_312) (lift_to_both0 (usize 1)) (lift_to_both0 (
              usize 2))) (matrix_index (lift_to_both0 s_312) (lift_to_both0 (
              usize 2)) (lift_to_both0 (usize 3))) (matrix_index (
            lift_to_both0 s_312) (lift_to_both0 (usize 3)) (lift_to_both0 (
              usize 0))) in
      letb r1_314 : int32 :=
        rebuild_u32 (matrix_index (lift_to_both0 s_312) (lift_to_both0 (
              usize 0)) (lift_to_both0 (usize 2))) (matrix_index (
            lift_to_both0 s_312) (lift_to_both0 (usize 1)) (lift_to_both0 (
              usize 3))) (matrix_index (lift_to_both0 s_312) (lift_to_both0 (
              usize 2)) (lift_to_both0 (usize 0))) (matrix_index (
            lift_to_both0 s_312) (lift_to_both0 (usize 3)) (lift_to_both0 (
              usize 1))) in
      letb r2_315 : int32 :=
        rebuild_u32 (matrix_index (lift_to_both0 s_312) (lift_to_both0 (
              usize 0)) (lift_to_both0 (usize 3))) (matrix_index (
            lift_to_both0 s_312) (lift_to_both0 (usize 1)) (lift_to_both0 (
              usize 0))) (matrix_index (lift_to_both0 s_312) (lift_to_both0 (
              usize 2)) (lift_to_both0 (usize 1))) (matrix_index (
            lift_to_both0 s_312) (lift_to_both0 (usize 3)) (lift_to_both0 (
              usize 2))) in
      letb r3_316 : int32 :=
        rebuild_u32 (matrix_index (lift_to_both0 s_312) (lift_to_both0 (
              usize 0)) (lift_to_both0 (usize 0))) (matrix_index (
            lift_to_both0 s_312) (lift_to_both0 (usize 1)) (lift_to_both0 (
              usize 1))) (matrix_index (lift_to_both0 s_312) (lift_to_both0 (
              usize 2)) (lift_to_both0 (usize 2))) (matrix_index (
            lift_to_both0 s_312) (lift_to_both0 (usize 3)) (lift_to_both0 (
              usize 3))) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (rebuild_u128 (
          lift_to_both0 r0_313) (lift_to_both0 r1_314) (lift_to_both0 r2_315) (
          lift_to_both0 r3_316))
      ) : both (fset.fset0) [interface] (int128)).
Fail Next Obligation.


Notation "'xtime_inp'" :=(int8 : choice_type) (in custom pack_type at level 2).
Notation "'xtime_inp'" :=(int8 : ChoiceEquality) (at level 2).
Notation "'xtime_out'" :=(int8 : choice_type) (in custom pack_type at level 2).
Notation "'xtime_out'" :=(int8 : ChoiceEquality) (at level 2).
Definition XTIME : nat :=
  323.
Program Definition xtime (x_318 : int8)
  : both (fset.fset0) [interface] (int8) :=
  ((letb x1_319 : int8 :=
        (lift_to_both0 x_318) shift_left (lift_to_both0 (usize 1)) in
      letb x7_320 : int8 :=
        (lift_to_both0 x_318) shift_right (lift_to_both0 (usize 7)) in
      letb x71_321 : int8 :=
        (lift_to_both0 x7_320) .& (lift_to_both0 (@repr U8 1)) in
      letb x711b_322 : int8 :=
        (lift_to_both0 x71_321) .* (lift_to_both0 (@repr U8 27)) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) ((
          lift_to_both0 x1_319) .^ (lift_to_both0 x711b_322))
      ) : both (fset.fset0) [interface] (int8)).
Fail Next Obligation.


Notation "'mix_column_simpl_inp'" :=(
  int8 '× int8 '× int8 '× int8 : choice_type) (in custom pack_type at level 2).
Notation "'mix_column_simpl_inp'" :=(
  int8 '× int8 '× int8 '× int8 : ChoiceEquality) (at level 2).
Notation "'mix_column_simpl_out'" :=((int8 '× int8 '× int8 '× int8
  ) : choice_type) (in custom pack_type at level 2).
Notation "'mix_column_simpl_out'" :=((int8 '× int8 '× int8 '× int8
  ) : ChoiceEquality) (at level 2).
Definition MIX_COLUMN_SIMPL : nat :=
  329.
Program Definition mix_column_simpl (s0_324 : int8) (s1_325 : int8) (
    s2_326 : int8) (s3_327 : int8)
  : both (fset.fset0) [interface] ((int8 '× int8 '× int8 '× int8)) :=
  ((letb tmp_328 : int8 :=
        (((lift_to_both0 s0_324) .^ (lift_to_both0 s1_325)) .^ (
            lift_to_both0 s2_326)) .^ (lift_to_both0 s3_327) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          ((lift_to_both0 s0_324) .^ (lift_to_both0 tmp_328)) .^ (xtime ((
                lift_to_both0 s0_324) .^ (lift_to_both0 s1_325))),
          ((lift_to_both0 s1_325) .^ (lift_to_both0 tmp_328)) .^ (xtime ((
                lift_to_both0 s1_325) .^ (lift_to_both0 s2_326))),
          ((lift_to_both0 s2_326) .^ (lift_to_both0 tmp_328)) .^ (xtime ((
                lift_to_both0 s2_326) .^ (lift_to_both0 s3_327))),
          ((lift_to_both0 s3_327) .^ (lift_to_both0 tmp_328)) .^ (xtime ((
                lift_to_both0 s3_327) .^ (lift_to_both0 s0_324)))
        ))
      ) : both (fset.fset0) [interface] ((int8 '× int8 '× int8 '× int8))).
Fail Next Obligation.


Notation "'mix_column_inp'" :=(
  uint_size '× int128 : choice_type) (in custom pack_type at level 2).
Notation "'mix_column_inp'" :=(
  uint_size '× int128 : ChoiceEquality) (at level 2).
Notation "'mix_column_out'" :=(
  int128 : choice_type) (in custom pack_type at level 2).
Notation "'mix_column_out'" :=(int128 : ChoiceEquality) (at level 2).
Definition MIX_COLUMN : nat :=
  343.
Program Definition mix_column (c_330 : uint_size) (state_332 : int128)
  : both (fset.fset0) [interface] (int128) :=
  ((letb i0_331 : uint_size :=
        (lift_to_both0 c_330) .* (lift_to_both0 (usize 4)) in
      letb s0_333 : int8 :=
        matrix_index (lift_to_both0 state_332) (lift_to_both0 (usize 3)) (
          lift_to_both0 c_330) in
      letb s1_334 : int8 :=
        matrix_index (lift_to_both0 state_332) (lift_to_both0 (usize 2)) (
          lift_to_both0 c_330) in
      letb s2_335 : int8 :=
        matrix_index (lift_to_both0 state_332) (lift_to_both0 (usize 1)) (
          lift_to_both0 c_330) in
      letb s3_336 : int8 :=
        matrix_index (lift_to_both0 state_332) (lift_to_both0 (usize 0)) (
          lift_to_both0 c_330) in
      letb tmp_337 : int8 :=
        (((lift_to_both0 s0_333) .^ (lift_to_both0 s1_334)) .^ (
            lift_to_both0 s2_335)) .^ (lift_to_both0 s3_336) in
      letb st_338 : int128 := lift_to_both0 state_332 in
      letb st_339 : int128 :=
        set_index_u128 (lift_to_both0 st_338) ((lift_to_both0 (usize 3)) .+ ((
              lift_to_both0 c_330) .* (lift_to_both0 (usize 4)))) (((
              lift_to_both0 s0_333) .^ (lift_to_both0 tmp_337)) .^ (xtime ((
                lift_to_both0 s0_333) .^ (lift_to_both0 s1_334)))) in
      letb st_340 : int128 :=
        set_index_u128 (lift_to_both0 st_339) ((lift_to_both0 (usize 2)) .+ ((
              lift_to_both0 c_330) .* (lift_to_both0 (usize 4)))) (((
              lift_to_both0 s1_334) .^ (lift_to_both0 tmp_337)) .^ (xtime ((
                lift_to_both0 s1_334) .^ (lift_to_both0 s2_335)))) in
      letb st_341 : int128 :=
        set_index_u128 (lift_to_both0 st_340) ((lift_to_both0 (usize 1)) .+ ((
              lift_to_both0 c_330) .* (lift_to_both0 (usize 4)))) (((
              lift_to_both0 s2_335) .^ (lift_to_both0 tmp_337)) .^ (xtime ((
                lift_to_both0 s2_335) .^ (lift_to_both0 s3_336)))) in
      letb st_342 : int128 :=
        set_index_u128 (lift_to_both0 st_341) ((lift_to_both0 (usize 0)) .+ ((
              lift_to_both0 c_330) .* (lift_to_both0 (usize 4)))) (((
              lift_to_both0 s3_336) .^ (lift_to_both0 tmp_337)) .^ (xtime ((
                lift_to_both0 s3_336) .^ (lift_to_both0 s0_333)))) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 st_342)
      ) : both (fset.fset0) [interface] (int128)).
Fail Next Obligation.


Notation "'mix_columns_inp'" :=(
  int128 : choice_type) (in custom pack_type at level 2).
Notation "'mix_columns_inp'" :=(int128 : ChoiceEquality) (at level 2).
Notation "'mix_columns_out'" :=(
  int128 : choice_type) (in custom pack_type at level 2).
Notation "'mix_columns_out'" :=(int128 : ChoiceEquality) (at level 2).
Definition MIX_COLUMNS : nat :=
  348.
Program Definition mix_columns (state_344 : int128)
  : both (fset.fset0) [interface] (int128) :=
  ((letb state_345 : int128 :=
        mix_column (lift_to_both0 (usize 0)) (lift_to_both0 state_344) in
      letb state_346 : int128 :=
        mix_column (lift_to_both0 (usize 1)) (lift_to_both0 state_345) in
      letb state_347 : int128 :=
        mix_column (lift_to_both0 (usize 2)) (lift_to_both0 state_346) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (mix_column (
          lift_to_both0 (usize 3)) (lift_to_both0 state_347))
      ) : both (fset.fset0) [interface] (int128)).
Fail Next Obligation.


Notation "'aes_enc_inp'" :=(
  int128 '× int128 : choice_type) (in custom pack_type at level 2).
Notation "'aes_enc_inp'" :=(int128 '× int128 : ChoiceEquality) (at level 2).
Notation "'aes_enc_out'" :=(
  int128 : choice_type) (in custom pack_type at level 2).
Notation "'aes_enc_out'" :=(int128 : ChoiceEquality) (at level 2).
Definition AES_ENC : nat :=
  354.
Program Definition aes_enc (state_349 : int128) (rkey_353 : int128)
  : both (fset.fset0) [interface] (int128) :=
  ((letb state_350 : int128 := sub_bytes (lift_to_both0 state_349) in
      letb state_351 : int128 := shift_rows (lift_to_both0 state_350) in
      letb state_352 : int128 := mix_columns (lift_to_both0 state_351) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) ((
          lift_to_both0 state_352) .^ (lift_to_both0 rkey_353))
      ) : both (fset.fset0) [interface] (int128)).
Fail Next Obligation.


Notation "'aes_enc_last_inp'" :=(
  int128 '× int128 : choice_type) (in custom pack_type at level 2).
Notation "'aes_enc_last_inp'" :=(
  int128 '× int128 : ChoiceEquality) (at level 2).
Notation "'aes_enc_last_out'" :=(
  int128 : choice_type) (in custom pack_type at level 2).
Notation "'aes_enc_last_out'" :=(int128 : ChoiceEquality) (at level 2).
Definition AES_ENC_LAST : nat :=
  359.
Program Definition aes_enc_last (state_355 : int128) (rkey_358 : int128)
  : both (fset.fset0) [interface] (int128) :=
  ((letb state_356 : int128 := sub_bytes (lift_to_both0 state_355) in
      letb state_357 : int128 := shift_rows (lift_to_both0 state_356) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) ((
          lift_to_both0 state_357) .^ (lift_to_both0 rkey_358))
      ) : both (fset.fset0) [interface] (int128)).
Fail Next Obligation.

Definition state_360_loc : ChoiceEqualityLocation :=
  (int128 ; 361%nat).
Notation "'aes_rounds_inp'" :=(
  key_list_t '× int128 : choice_type) (in custom pack_type at level 2).
Notation "'aes_rounds_inp'" :=(
  key_list_t '× int128 : ChoiceEquality) (at level 2).
Notation "'aes_rounds_out'" :=(
  int128 : choice_type) (in custom pack_type at level 2).
Notation "'aes_rounds_out'" :=(int128 : ChoiceEquality) (at level 2).
Definition AES_ROUNDS : nat :=
  365.
Program Definition aes_rounds (rkeys_363 : key_list_t) (inp_362 : int128)
  : both (CEfset ([state_360_loc])) [interface] (int128) :=
  ((letbm state_360 : int128 loc( state_360_loc ) :=
        (lift_to_both0 inp_362) .^ (seq_index (rkeys_363) (lift_to_both0 (
              usize 0))) in
      letb state_360 :=
        foldi_both' (lift_to_both0 (usize 1)) (lift_to_both0 (
              usize 10)) state_360 (L := (CEfset ([state_360_loc]))) (
            I := [interface]) (fun round_364 state_360 =>
            letbm state_360 loc( state_360_loc ) :=
              aes_enc (lift_to_both0 state_360) (seq_index (rkeys_363) (
                  lift_to_both0 round_364)) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 state_360)
            ) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (aes_enc_last (
          lift_to_both0 state_360) (seq_index (rkeys_363) (lift_to_both0 (
              usize 10))))
      ) : both (CEfset ([state_360_loc])) [interface] (int128)).
Fail Next Obligation.


Notation "'aes_inp'" :=(
  int128 '× int128 : choice_type) (in custom pack_type at level 2).
Notation "'aes_inp'" :=(int128 '× int128 : ChoiceEquality) (at level 2).
Notation "'aes_out'" :=(int128 : choice_type) (in custom pack_type at level 2).
Notation "'aes_out'" :=(int128 : ChoiceEquality) (at level 2).
Definition AES : nat :=
  369.
Program Definition aes (key_366 : int128) (inp_368 : int128)
  : both (CEfset (
      [rkeys_296_loc ; temp2_297_loc ; key_298_loc ; state_360_loc])) [interface] (
    int128) :=
  ((letb rkeys_367 : seq int128 := keys_expand (lift_to_both0 key_366) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (aes_rounds (
          lift_to_both0 rkeys_367) (lift_to_both0 inp_368))
      ) : both (CEfset (
        [rkeys_296_loc ; temp2_297_loc ; key_298_loc ; state_360_loc])) [interface] (
      int128)).
Fail Next Obligation.

