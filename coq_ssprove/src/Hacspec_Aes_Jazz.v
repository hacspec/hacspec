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
              lift_to_both0 s_209) shift_right (((lift_to_both0 (usize 3)) .- (
                  lift_to_both0 i_210)) .* (lift_to_both0 (usize 32)))) .% ((
              lift_to_both0 (@repr U128 1)) shift_left (lift_to_both0 (
                usize 32)))))
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
              lift_to_both0 s_212) shift_right (((lift_to_both0 (usize 3)) .- (
                  lift_to_both0 i_213)) .* (lift_to_both0 (usize 8)))) .% ((
              lift_to_both0 (@repr U32 1)) shift_left (lift_to_both0 (
                usize 8)))))
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
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (((((
                (fun x => lift_to_both0 (repr (unsigned x)))(
                  lift_to_both0 s0_215)) shift_left (lift_to_both0 (
                  usize 24))) .| (((fun x => lift_to_both0 (repr (unsigned x)))(
                  lift_to_both0 s1_216)) shift_left (lift_to_both0 (
                  usize 16)))) .| ((
              (fun x => lift_to_both0 (repr (unsigned x)))(
                lift_to_both0 s2_217)) shift_left (lift_to_both0 (
                usize 8)))) .| ((fun x => lift_to_both0 (repr (unsigned x)))(
            lift_to_both0 s3_218)))
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
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (((((
                (fun x => lift_to_both0 (repr (unsigned x)))(
                  lift_to_both0 s0_220)) shift_left (lift_to_both0 (
                  usize 96))) .| (((fun x => lift_to_both0 (repr (unsigned x)))(
                  lift_to_both0 s1_221)) shift_left (lift_to_both0 (
                  usize 64)))) .| ((
              (fun x => lift_to_both0 (repr (unsigned x)))(
                lift_to_both0 s2_222)) shift_left (lift_to_both0 (
                usize 32)))) .| ((fun x => lift_to_both0 (repr (unsigned x)))(
            lift_to_both0 s3_223)))
      ) : both (fset.fset0) [interface] (int128)).
Fail Next Obligation.


Notation "'vpshufd1_inp'" :=(
  int128 '× int8 '× uint_size : choice_type) (in custom pack_type at level 2).
Notation "'vpshufd1_inp'" :=(
  int128 '× int8 '× uint_size : ChoiceEquality) (at level 2).
Notation "'vpshufd1_out'" :=(
  int32 : choice_type) (in custom pack_type at level 2).
Notation "'vpshufd1_out'" :=(int32 : ChoiceEquality) (at level 2).
Definition VPSHUFD1_ : nat :=
  228.
Program Definition vpshufd1 (s_225 : int128) (o_226 : int8) (i_227 : uint_size)
  : both (fset.fset0) [interface] (int32) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        (fun x => lift_to_both0 (repr (unsigned x)))((
            lift_to_both0 s_225) shift_right ((lift_to_both0 (usize 32)) .* ((
                lift_to_both0 (usize 3)) .- (((
                    (fun x => lift_to_both0 (repr (unsigned x)))(
                      lift_to_both0 o_226)) usize_shift_right ((lift_to_both0 (
                        usize 2)) .* (lift_to_both0 i_227))) .% (lift_to_both0 (
                    usize 4)))))))
      ) : both (fset.fset0) [interface] (int32)).
Fail Next Obligation.


Notation "'vpshufd_inp'" :=(
  int128 '× int8 : choice_type) (in custom pack_type at level 2).
Notation "'vpshufd_inp'" :=(int128 '× int8 : ChoiceEquality) (at level 2).
Notation "'vpshufd_out'" :=(
  int128 : choice_type) (in custom pack_type at level 2).
Notation "'vpshufd_out'" :=(int128 : ChoiceEquality) (at level 2).
Definition VPSHUFD : nat :=
  235.
Program Definition vpshufd (s_229 : int128) (o_230 : int8)
  : both (fset.fset0) [interface] (int128) :=
  ((letb d1_231 : int32 :=
        vpshufd1 (lift_to_both0 s_229) (lift_to_both0 o_230) ((lift_to_both0 (
              usize 3)) .- (lift_to_both0 (usize 0))) in
      letb d2_232 : int32 :=
        vpshufd1 (lift_to_both0 s_229) (lift_to_both0 o_230) ((lift_to_both0 (
              usize 3)) .- (lift_to_both0 (usize 1))) in
      letb d3_233 : int32 :=
        vpshufd1 (lift_to_both0 s_229) (lift_to_both0 o_230) ((lift_to_both0 (
              usize 3)) .- (lift_to_both0 (usize 2))) in
      letb d4_234 : int32 :=
        vpshufd1 (lift_to_both0 s_229) (lift_to_both0 o_230) ((lift_to_both0 (
              usize 3)) .- (lift_to_both0 (usize 3))) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (rebuild_u128 (
          lift_to_both0 d4_234) (lift_to_both0 d3_233) (lift_to_both0 d2_232) (
          lift_to_both0 d1_231))
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
  243.
Program Definition vshufps (s1_236 : int128) (s2_240 : int128) (o_237 : int8)
  : both (fset.fset0) [interface] (int128) :=
  ((letb d1_238 : int32 :=
        vpshufd1 (lift_to_both0 s1_236) (lift_to_both0 o_237) (lift_to_both0 (
            usize 0)) in
      letb d2_239 : int32 :=
        vpshufd1 (lift_to_both0 s1_236) (lift_to_both0 o_237) (lift_to_both0 (
            usize 1)) in
      letb d3_241 : int32 :=
        vpshufd1 (lift_to_both0 s2_240) (lift_to_both0 o_237) (lift_to_both0 (
            usize 2)) in
      letb d4_242 : int32 :=
        vpshufd1 (lift_to_both0 s2_240) (lift_to_both0 o_237) (lift_to_both0 (
            usize 3)) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (rebuild_u128 (
          lift_to_both0 d1_238) (lift_to_both0 d2_239) (lift_to_both0 d3_241) (
          lift_to_both0 d4_242))
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
  253.
Program Definition key_combine (rkey_247 : int128) (temp1_244 : int128) (
    temp2_246 : int128)
  : both (fset.fset0) [interface] ((int128 '× int128)) :=
  ((letb temp1_245 : int128 :=
        vpshufd (lift_to_both0 temp1_244) (lift_to_both0 (@repr U8 255)) in
      letb temp2_248 : int128 :=
        vshufps (lift_to_both0 temp2_246) (lift_to_both0 rkey_247) (
          lift_to_both0 (@repr U8 16)) in
      letb rkey_249 : int128 :=
        (lift_to_both0 rkey_247) .^ (lift_to_both0 temp2_248) in
      letb temp2_250 : int128 :=
        vshufps (lift_to_both0 temp2_248) (lift_to_both0 rkey_249) (
          lift_to_both0 (@repr U8 140)) in
      letb rkey_251 : int128 :=
        (lift_to_both0 rkey_249) .^ (lift_to_both0 temp2_250) in
      letb rkey_252 : int128 :=
        (lift_to_both0 rkey_251) .^ (lift_to_both0 temp1_245) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 rkey_252,
          lift_to_both0 temp2_250
        ))
      ) : both (fset.fset0) [interface] ((int128 '× int128))).
Fail Next Obligation.


Notation "'aes_subword_inp'" :=(
  int32 : choice_type) (in custom pack_type at level 2).
Notation "'aes_subword_inp'" :=(int32 : ChoiceEquality) (at level 2).
Notation "'aes_subword_out'" :=(
  int32 : choice_type) (in custom pack_type at level 2).
Notation "'aes_subword_out'" :=(int32 : ChoiceEquality) (at level 2).
Definition AES_SUBWORD : nat :=
  255.
Program Definition aes_subword (v_254 : int32)
  : both (fset.fset0) [interface] (int32) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (rebuild_u32 (array_index (
            sbox_v) (index_u8 (lift_to_both0 v_254) (lift_to_both0 (
                usize 0)))) (array_index (sbox_v) (index_u8 (
              lift_to_both0 v_254) (lift_to_both0 (usize 1)))) (array_index (
            sbox_v) (index_u8 (lift_to_both0 v_254) (lift_to_both0 (
                usize 2)))) (array_index (sbox_v) (index_u8 (
              lift_to_both0 v_254) (lift_to_both0 (usize 3)))))
      ) : both (fset.fset0) [interface] (int32)).
Fail Next Obligation.


Notation "'rotword_inp'" :=(
  int32 : choice_type) (in custom pack_type at level 2).
Notation "'rotword_inp'" :=(int32 : ChoiceEquality) (at level 2).
Notation "'rotword_out'" :=(
  int32 : choice_type) (in custom pack_type at level 2).
Notation "'rotword_out'" :=(int32 : ChoiceEquality) (at level 2).
Definition ROTWORD : nat :=
  257.
Program Definition rotword (v_256 : int32)
  : both (fset.fset0) [interface] (int32) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (rebuild_u32 (index_u8 (
            lift_to_both0 v_256) (lift_to_both0 (usize 1))) (index_u8 (
            lift_to_both0 v_256) (lift_to_both0 (usize 2))) (index_u8 (
            lift_to_both0 v_256) (lift_to_both0 (usize 3))) (index_u8 (
            lift_to_both0 v_256) (lift_to_both0 (usize 0))))
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
  266.
Program Definition aeskeygenassist (v1_258 : int128) (v2_262 : int8)
  : both (fset.fset0) [interface] (int128) :=
  ((letb x1_259 : int32 :=
        index_u32 (lift_to_both0 v1_258) (lift_to_both0 (usize 1)) in
      letb x3_260 : int32 :=
        index_u32 (lift_to_both0 v1_258) (lift_to_both0 (usize 3)) in
      letb y0_261 : int32 := aes_subword (lift_to_both0 x1_259) in
      letb y1_263 : int32 :=
        (rotword (lift_to_both0 y0_261)) .^ ((
            (fun x => lift_to_both0 (repr (unsigned x)))(
              lift_to_both0 v2_262)) shift_left (lift_to_both0 (usize 24))) in
      letb y2_264 : int32 := aes_subword (lift_to_both0 x3_260) in
      letb y3_265 : int32 :=
        (rotword (lift_to_both0 y2_264)) .^ ((
            (fun x => lift_to_both0 (repr (unsigned x)))(
              lift_to_both0 v2_262)) shift_left (lift_to_both0 (usize 24))) in
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
  271.
Program Definition key_expand (rcon_268 : int8) (rkey_267 : int128) (
    temp2_270 : int128)
  : both (fset.fset0) [interface] ((int128 '× int128)) :=
  ((letb temp1_269 : int128 :=
        aeskeygenassist (lift_to_both0 rkey_267) (lift_to_both0 rcon_268) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (key_combine (
          lift_to_both0 rkey_267) (lift_to_both0 temp1_269) (
          lift_to_both0 temp2_270))
      ) : both (fset.fset0) [interface] ((int128 '× int128))).
Fail Next Obligation.

Notation "'key_list_t'" := (seq int128) : hacspec_scope.

Definition temp2_273_loc : ChoiceEqualityLocation :=
  (int128 ; 275%nat).
Definition rkeys_272_loc : ChoiceEqualityLocation :=
  (key_list_t ; 276%nat).
Definition key_274_loc : ChoiceEqualityLocation :=
  (int128 ; 277%nat).
Notation "'keys_expand_inp'" :=(
  int128 : choice_type) (in custom pack_type at level 2).
Notation "'keys_expand_inp'" :=(int128 : ChoiceEquality) (at level 2).
Notation "'keys_expand_out'" :=(
  key_list_t : choice_type) (in custom pack_type at level 2).
Notation "'keys_expand_out'" :=(key_list_t : ChoiceEquality) (at level 2).
Definition KEYS_EXPAND : nat :=
  283.
Program Definition keys_expand (key_278 : int128)
  : both (CEfset ([rkeys_272_loc ; temp2_273_loc ; key_274_loc])) [interface] (
    key_list_t) :=
  ((letbm rkeys_272 : key_list_t loc( rkeys_272_loc ) :=
        seq_new_ (default : int128) (lift_to_both0 (usize 0)) in
      letbm rkeys_272 loc( rkeys_272_loc ) :=
        seq_push (lift_to_both0 rkeys_272) (lift_to_both0 key_278) in
      letbm temp2_273 : int128 loc( temp2_273_loc ) :=
        lift_to_both0 (@repr U128 0) in
      letbm key_274 : int128 loc( key_274_loc ) := lift_to_both0 key_278 in
      letb '(rkeys_272, temp2_273, key_274) :=
        foldi_both' (lift_to_both0 (usize 1)) (lift_to_both0 (
              usize 12)) prod_ce(rkeys_272, temp2_273, key_274) (L := (CEfset (
                [rkeys_272_loc ; temp2_273_loc ; key_274_loc]))) (
            I := [interface]) (fun round_279 '(rkeys_272, temp2_273, key_274) =>
            letb rcon_280 : int8 :=
              array_index (rcon_v) (lift_to_both0 round_279) in
            letb '(nkey_281, ntemp2_282) : (int128 '× int128) :=
              key_expand (lift_to_both0 rcon_280) (lift_to_both0 key_274) (
                lift_to_both0 temp2_273) in
            letbm key_274 loc( key_274_loc ) := lift_to_both0 nkey_281 in
            letbm temp2_273 loc( temp2_273_loc ) := lift_to_both0 ntemp2_282 in
            letbm rkeys_272 loc( rkeys_272_loc ) :=
              seq_push (lift_to_both0 rkeys_272) (lift_to_both0 key_274) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                lift_to_both0 rkeys_272,
                lift_to_both0 temp2_273,
                lift_to_both0 key_274
              ))
            ) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 rkeys_272)
      ) : both (CEfset (
        [rkeys_272_loc ; temp2_273_loc ; key_274_loc])) [interface] (
      key_list_t)).
Fail Next Obligation.


Notation "'sub_bytes_inp'" :=(
  int128 : choice_type) (in custom pack_type at level 2).
Notation "'sub_bytes_inp'" :=(int128 : ChoiceEquality) (at level 2).
Notation "'sub_bytes_out'" :=(
  int128 : choice_type) (in custom pack_type at level 2).
Notation "'sub_bytes_out'" :=(int128 : ChoiceEquality) (at level 2).
Definition SUBBYTES : nat :=
  285.
Program Definition sub_bytes (s_284 : int128)
  : both (fset.fset0) [interface] (int128) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (rebuild_u128 (
          aes_subword (index_u32 (lift_to_both0 s_284) (lift_to_both0 (
                usize 0)))) (aes_subword (index_u32 (lift_to_both0 s_284) (
              lift_to_both0 (usize 1)))) (aes_subword (index_u32 (
              lift_to_both0 s_284) (lift_to_both0 (usize 2)))) (aes_subword (
            index_u32 (lift_to_both0 s_284) (lift_to_both0 (usize 3)))))
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
  289.
Program Definition matrix_index (s_286 : int128) (i_288 : uint_size) (
    j_287 : uint_size)
  : both (fset.fset0) [interface] (int8) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (index_u8 (index_u32 (
            lift_to_both0 s_286) (lift_to_both0 j_287)) (lift_to_both0 i_288))
      ) : both (fset.fset0) [interface] (int8)).
Fail Next Obligation.


Notation "'shift_rows_inp'" :=(
  int128 : choice_type) (in custom pack_type at level 2).
Notation "'shift_rows_inp'" :=(int128 : ChoiceEquality) (at level 2).
Notation "'shift_rows_out'" :=(
  int128 : choice_type) (in custom pack_type at level 2).
Notation "'shift_rows_out'" :=(int128 : ChoiceEquality) (at level 2).
Definition SHIFTROWS : nat :=
  295.
Program Definition shift_rows (s_290 : int128)
  : both (fset.fset0) [interface] (int128) :=
  ((letb c0_291 : int32 :=
        rebuild_u32 (matrix_index (lift_to_both0 s_290) (lift_to_both0 (
              usize 0)) (lift_to_both0 (usize 0))) (matrix_index (
            lift_to_both0 s_290) (lift_to_both0 (usize 1)) (lift_to_both0 (
              usize 1))) (matrix_index (lift_to_both0 s_290) (lift_to_both0 (
              usize 2)) (lift_to_both0 (usize 2))) (matrix_index (
            lift_to_both0 s_290) (lift_to_both0 (usize 3)) (lift_to_both0 (
              usize 3))) in
      letb c1_292 : int32 :=
        rebuild_u32 (matrix_index (lift_to_both0 s_290) (lift_to_both0 (
              usize 0)) (lift_to_both0 (usize 1))) (matrix_index (
            lift_to_both0 s_290) (lift_to_both0 (usize 1)) (lift_to_both0 (
              usize 2))) (matrix_index (lift_to_both0 s_290) (lift_to_both0 (
              usize 2)) (lift_to_both0 (usize 3))) (matrix_index (
            lift_to_both0 s_290) (lift_to_both0 (usize 3)) (lift_to_both0 (
              usize 0))) in
      letb c2_293 : int32 :=
        rebuild_u32 (matrix_index (lift_to_both0 s_290) (lift_to_both0 (
              usize 0)) (lift_to_both0 (usize 2))) (matrix_index (
            lift_to_both0 s_290) (lift_to_both0 (usize 1)) (lift_to_both0 (
              usize 3))) (matrix_index (lift_to_both0 s_290) (lift_to_both0 (
              usize 2)) (lift_to_both0 (usize 0))) (matrix_index (
            lift_to_both0 s_290) (lift_to_both0 (usize 3)) (lift_to_both0 (
              usize 1))) in
      letb c3_294 : int32 :=
        rebuild_u32 (matrix_index (lift_to_both0 s_290) (lift_to_both0 (
              usize 0)) (lift_to_both0 (usize 3))) (matrix_index (
            lift_to_both0 s_290) (lift_to_both0 (usize 1)) (lift_to_both0 (
              usize 0))) (matrix_index (lift_to_both0 s_290) (lift_to_both0 (
              usize 2)) (lift_to_both0 (usize 1))) (matrix_index (
            lift_to_both0 s_290) (lift_to_both0 (usize 3)) (lift_to_both0 (
              usize 2))) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (rebuild_u128 (
          lift_to_both0 c0_291) (lift_to_both0 c1_292) (lift_to_both0 c2_293) (
          lift_to_both0 c3_294))
      ) : both (fset.fset0) [interface] (int128)).
Fail Next Obligation.


Notation "'xtime_inp'" :=(int8 : choice_type) (in custom pack_type at level 2).
Notation "'xtime_inp'" :=(int8 : ChoiceEquality) (at level 2).
Notation "'xtime_out'" :=(int8 : choice_type) (in custom pack_type at level 2).
Notation "'xtime_out'" :=(int8 : ChoiceEquality) (at level 2).
Definition XTIME : nat :=
  301.
Program Definition xtime (x_296 : int8)
  : both (fset.fset0) [interface] (int8) :=
  ((letb x1_297 : int8 :=
        (lift_to_both0 x_296) shift_left (lift_to_both0 (usize 1)) in
      letb x7_298 : int8 :=
        (lift_to_both0 x_296) shift_right (lift_to_both0 (usize 7)) in
      letb x71_299 : int8 :=
        (lift_to_both0 x7_298) .& (lift_to_both0 (@repr U8 1)) in
      letb x711b_300 : int8 :=
        (lift_to_both0 x71_299) .* (lift_to_both0 (@repr U8 27)) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) ((
          lift_to_both0 x1_297) .^ (lift_to_both0 x711b_300))
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
  307.
Program Definition mix_column_simpl (s0_302 : int8) (s1_303 : int8) (
    s2_304 : int8) (s3_305 : int8)
  : both (fset.fset0) [interface] ((int8 '× int8 '× int8 '× int8)) :=
  ((letb tmp_306 : int8 :=
        (((lift_to_both0 s0_302) .^ (lift_to_both0 s1_303)) .^ (
            lift_to_both0 s2_304)) .^ (lift_to_both0 s3_305) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          ((lift_to_both0 s0_302) .^ (lift_to_both0 tmp_306)) .^ (xtime ((
                lift_to_both0 s0_302) .^ (lift_to_both0 s1_303))),
          ((lift_to_both0 s1_303) .^ (lift_to_both0 tmp_306)) .^ (xtime ((
                lift_to_both0 s1_303) .^ (lift_to_both0 s2_304))),
          ((lift_to_both0 s2_304) .^ (lift_to_both0 tmp_306)) .^ (xtime ((
                lift_to_both0 s2_304) .^ (lift_to_both0 s3_305))),
          ((lift_to_both0 s3_305) .^ (lift_to_both0 tmp_306)) .^ (xtime ((
                lift_to_both0 s3_305) .^ (lift_to_both0 s0_302)))
        ))
      ) : both (fset.fset0) [interface] ((int8 '× int8 '× int8 '× int8))).
Fail Next Obligation.


Notation "'mix_column_inp'" :=(
  uint_size '× int128 : choice_type) (in custom pack_type at level 2).
Notation "'mix_column_inp'" :=(
  uint_size '× int128 : ChoiceEquality) (at level 2).
Notation "'mix_column_out'" :=(
  int32 : choice_type) (in custom pack_type at level 2).
Notation "'mix_column_out'" :=(int32 : ChoiceEquality) (at level 2).
Definition MIX_COLUMN : nat :=
  320.
Program Definition mix_column (c_308 : uint_size) (state_310 : int128)
  : both (fset.fset0) [interface] (int32) :=
  ((letb i0_309 : uint_size :=
        (lift_to_both0 c_308) .* (lift_to_both0 (usize 4)) in
      letb s0_311 : int8 :=
        matrix_index (lift_to_both0 state_310) (lift_to_both0 (usize 0)) (
          lift_to_both0 c_308) in
      letb s1_312 : int8 :=
        matrix_index (lift_to_both0 state_310) (lift_to_both0 (usize 1)) (
          lift_to_both0 c_308) in
      letb s2_313 : int8 :=
        matrix_index (lift_to_both0 state_310) (lift_to_both0 (usize 2)) (
          lift_to_both0 c_308) in
      letb s3_314 : int8 :=
        matrix_index (lift_to_both0 state_310) (lift_to_both0 (usize 3)) (
          lift_to_both0 c_308) in
      letb tmp_315 : int8 :=
        (((lift_to_both0 s0_311) .^ (lift_to_both0 s1_312)) .^ (
            lift_to_both0 s2_313)) .^ (lift_to_both0 s3_314) in
      letb r0_316 : int8 :=
        ((lift_to_both0 s0_311) .^ (lift_to_both0 tmp_315)) .^ (xtime ((
              lift_to_both0 s0_311) .^ (lift_to_both0 s1_312))) in
      letb r1_317 : int8 :=
        ((lift_to_both0 s1_312) .^ (lift_to_both0 tmp_315)) .^ (xtime ((
              lift_to_both0 s1_312) .^ (lift_to_both0 s2_313))) in
      letb r2_318 : int8 :=
        ((lift_to_both0 s2_313) .^ (lift_to_both0 tmp_315)) .^ (xtime ((
              lift_to_both0 s2_313) .^ (lift_to_both0 s3_314))) in
      letb r3_319 : int8 :=
        ((lift_to_both0 s3_314) .^ (lift_to_both0 tmp_315)) .^ (xtime ((
              lift_to_both0 s3_314) .^ (lift_to_both0 s0_311))) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (rebuild_u32 (
          lift_to_both0 r0_316) (lift_to_both0 r1_317) (lift_to_both0 r2_318) (
          lift_to_both0 r3_319))
      ) : both (fset.fset0) [interface] (int32)).
Fail Next Obligation.


Notation "'mix_columns_inp'" :=(
  int128 : choice_type) (in custom pack_type at level 2).
Notation "'mix_columns_inp'" :=(int128 : ChoiceEquality) (at level 2).
Notation "'mix_columns_out'" :=(
  int128 : choice_type) (in custom pack_type at level 2).
Notation "'mix_columns_out'" :=(int128 : ChoiceEquality) (at level 2).
Definition MIX_COLUMNS : nat :=
  326.
Program Definition mix_columns (state_321 : int128)
  : both (fset.fset0) [interface] (int128) :=
  ((letb c0_322 : int32 :=
        mix_column (lift_to_both0 (usize 0)) (lift_to_both0 state_321) in
      letb c1_323 : int32 :=
        mix_column (lift_to_both0 (usize 1)) (lift_to_both0 state_321) in
      letb c2_324 : int32 :=
        mix_column (lift_to_both0 (usize 2)) (lift_to_both0 state_321) in
      letb c3_325 : int32 :=
        mix_column (lift_to_both0 (usize 3)) (lift_to_both0 state_321) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (rebuild_u128 (
          lift_to_both0 c0_322) (lift_to_both0 c1_323) (lift_to_both0 c2_324) (
          lift_to_both0 c3_325))
      ) : both (fset.fset0) [interface] (int128)).
Fail Next Obligation.


Notation "'aes_enc_inp'" :=(
  int128 '× int128 : choice_type) (in custom pack_type at level 2).
Notation "'aes_enc_inp'" :=(int128 '× int128 : ChoiceEquality) (at level 2).
Notation "'aes_enc_out'" :=(
  int128 : choice_type) (in custom pack_type at level 2).
Notation "'aes_enc_out'" :=(int128 : ChoiceEquality) (at level 2).
Definition AES_ENC : nat :=
  332.
Program Definition aes_enc (state_327 : int128) (rkey_331 : int128)
  : both (fset.fset0) [interface] (int128) :=
  ((letb state_328 : int128 := sub_bytes (lift_to_both0 state_327) in
      letb state_329 : int128 := shift_rows (lift_to_both0 state_328) in
      letb state_330 : int128 := mix_columns (lift_to_both0 state_329) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) ((
          lift_to_both0 state_330) .^ (lift_to_both0 rkey_331))
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
  337.
Program Definition aes_enc_last (state_333 : int128) (rkey_336 : int128)
  : both (fset.fset0) [interface] (int128) :=
  ((letb state_334 : int128 := sub_bytes (lift_to_both0 state_333) in
      letb state_335 : int128 := shift_rows (lift_to_both0 state_334) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) ((
          lift_to_both0 state_335) .^ (lift_to_both0 rkey_336))
      ) : both (fset.fset0) [interface] (int128)).
Fail Next Obligation.

Definition state_338_loc : ChoiceEqualityLocation :=
  (int128 ; 339%nat).
Notation "'aes_rounds_inp'" :=(
  key_list_t '× int128 : choice_type) (in custom pack_type at level 2).
Notation "'aes_rounds_inp'" :=(
  key_list_t '× int128 : ChoiceEquality) (at level 2).
Notation "'aes_rounds_out'" :=(
  int128 : choice_type) (in custom pack_type at level 2).
Notation "'aes_rounds_out'" :=(int128 : ChoiceEquality) (at level 2).
Definition AES_ROUNDS : nat :=
  343.
Program Definition aes_rounds (rkeys_341 : key_list_t) (inp_340 : int128)
  : both (CEfset ([state_338_loc])) [interface] (int128) :=
  ((letbm state_338 : int128 loc( state_338_loc ) :=
        (lift_to_both0 inp_340) .^ (seq_index (rkeys_341) (lift_to_both0 (
              usize 0))) in
      letb state_338 :=
        foldi_both' (lift_to_both0 (usize 1)) (lift_to_both0 (
              usize 10)) state_338 (L := (CEfset ([state_338_loc]))) (
            I := [interface]) (fun round_342 state_338 =>
            letbm state_338 loc( state_338_loc ) :=
              aes_enc (lift_to_both0 state_338) (seq_index (rkeys_341) (
                  lift_to_both0 round_342)) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 state_338)
            ) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (aes_enc_last (
          lift_to_both0 state_338) (seq_index (rkeys_341) (lift_to_both0 (
              usize 10))))
      ) : both (CEfset ([state_338_loc])) [interface] (int128)).
Fail Next Obligation.


Notation "'aes_inp'" :=(
  int128 '× int128 : choice_type) (in custom pack_type at level 2).
Notation "'aes_inp'" :=(int128 '× int128 : ChoiceEquality) (at level 2).
Notation "'aes_out'" :=(int128 : choice_type) (in custom pack_type at level 2).
Notation "'aes_out'" :=(int128 : ChoiceEquality) (at level 2).
Definition AES : nat :=
  347.
Program Definition aes (key_344 : int128) (inp_346 : int128)
  : both (CEfset (
      [rkeys_272_loc ; temp2_273_loc ; key_274_loc ; state_338_loc])) [interface] (
    int128) :=
  ((letb rkeys_345 : seq int128 := keys_expand (lift_to_both0 key_344) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (aes_rounds (
          lift_to_both0 rkeys_345) (lift_to_both0 inp_346))
      ) : both (CEfset (
        [rkeys_272_loc ; temp2_273_loc ; key_274_loc ; state_338_loc])) [interface] (
      int128)).
Fail Next Obligation.


Notation "'temp_inp'" :=(
  unit_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'temp_inp'" :=(unit_ChoiceEquality : ChoiceEquality) (at level 2).
Notation "'temp_out'" :=(
  unit_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'temp_out'" :=(unit_ChoiceEquality : ChoiceEquality) (at level 2).
Definition TEMP : nat :=
  351.
Program Definition temp 
  : both (fset.fset0) [interface] (unit_ChoiceEquality) :=
  ((letb msg_348 : int128 :=
        lift_to_both0 (@repr U128 66814286504060421741230023322616923956) in
      letb key_349 : int128 :=
        lift_to_both0 (@repr U128 57811460909138771071931939740208549692) in
      letb ctx_350 : int128 :=
        lift_to_both0 (@repr U128 75960790320075369159181001580855561010) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 (
          (tt : unit_ChoiceEquality)))
      ) : both (fset.fset0) [interface] (unit_ChoiceEquality)).
Fail Next Obligation.

