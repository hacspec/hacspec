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
  2203.
Program Definition index_u32 (s_2201 : int128) (i_2202 : uint_size)
  : both (fset.fset0) [interface] (int32) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        (fun x => lift_to_both0 (repr (unsigned x)))(((
              lift_to_both0 s_2201) shift_right ((lift_to_both0 i_2202) .* (
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
  2206.
Program Definition index_u8 (s_2204 : int32) (i_2205 : uint_size)
  : both (fset.fset0) [interface] (int8) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        (fun x => lift_to_both0 (repr (unsigned x)))(((
              lift_to_both0 s_2204) shift_right ((lift_to_both0 i_2205) .* (
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
  2211.
Program Definition rebuild_u32 (s0_2207 : int8) (s1_2208 : int8) (
    s2_2209 : int8) (s3_2210 : int8)
  : both (fset.fset0) [interface] (int32) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) ((
          (fun x => lift_to_both0 (repr (unsigned x)))(
            lift_to_both0 s0_2207)) .| (((
              (fun x => lift_to_both0 (repr (unsigned x)))(
                lift_to_both0 s1_2208)) shift_left (lift_to_both0 (
                usize 8))) .| ((((fun x => lift_to_both0 (repr (unsigned x)))(
                  lift_to_both0 s2_2209)) shift_left (lift_to_both0 (
                  usize 16))) .| (((fun x => lift_to_both0 (repr (unsigned x)))(
                  lift_to_both0 s3_2210)) shift_left (lift_to_both0 (
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
  2216.
Program Definition rebuild_u128 (s0_2212 : int32) (s1_2213 : int32) (
    s2_2214 : int32) (s3_2215 : int32)
  : both (fset.fset0) [interface] (int128) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) ((
          (fun x => lift_to_both0 (repr (unsigned x)))(
            lift_to_both0 s0_2212)) .| (((
              (fun x => lift_to_both0 (repr (unsigned x)))(
                lift_to_both0 s1_2213)) shift_left (lift_to_both0 (
                usize 32))) .| ((((fun x => lift_to_both0 (repr (unsigned x)))(
                  lift_to_both0 s2_2214)) shift_left (lift_to_both0 (
                  usize 64))) .| (((fun x => lift_to_both0 (repr (unsigned x)))(
                  lift_to_both0 s3_2215)) shift_left (lift_to_both0 (
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
  2218.
Program Definition subword (v_2217 : int32)
  : both (fset.fset0) [interface] (int32) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (rebuild_u32 (array_index (
            sbox_v) (index_u8 (lift_to_both0 v_2217) (lift_to_both0 (
                usize 0)))) (array_index (sbox_v) (index_u8 (
              lift_to_both0 v_2217) (lift_to_both0 (usize 1)))) (array_index (
            sbox_v) (index_u8 (lift_to_both0 v_2217) (lift_to_both0 (
                usize 2)))) (array_index (sbox_v) (index_u8 (
              lift_to_both0 v_2217) (lift_to_both0 (usize 3)))))
      ) : both (fset.fset0) [interface] (int32)).
Fail Next Obligation.


Notation "'rotword_inp'" :=(
  int32 : choice_type) (in custom pack_type at level 2).
Notation "'rotword_inp'" :=(int32 : ChoiceEquality) (at level 2).
Notation "'rotword_out'" :=(
  int32 : choice_type) (in custom pack_type at level 2).
Notation "'rotword_out'" :=(int32 : ChoiceEquality) (at level 2).
Definition ROTWORD : nat :=
  2220.
Program Definition rotword (v_2219 : int32)
  : both (fset.fset0) [interface] (int32) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (rebuild_u32 (index_u8 (
            lift_to_both0 v_2219) (lift_to_both0 (usize 1))) (index_u8 (
            lift_to_both0 v_2219) (lift_to_both0 (usize 2))) (index_u8 (
            lift_to_both0 v_2219) (lift_to_both0 (usize 3))) (index_u8 (
            lift_to_both0 v_2219) (lift_to_both0 (usize 0))))
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
  2224.
Program Definition vpshufd1 (s_2221 : int128) (o_2222 : int8) (
    i_2223 : uint_size)
  : both (fset.fset0) [interface] (int32) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (index_u32 ((
            lift_to_both0 s_2221) shift_right ((lift_to_both0 (usize 32)) .* (
              (fun x => lift_to_both0 (repr (unsigned x)))(((
                    lift_to_both0 o_2222) shift_right ((lift_to_both0 (
                        usize 2)) .* (lift_to_both0 i_2223))) .% (
                  lift_to_both0 (@repr U8 4)))))) (lift_to_both0 (usize 0)))
      ) : both (fset.fset0) [interface] (int32)).
Fail Next Obligation.


Notation "'vpshufd_inp'" :=(
  int128 '× int8 : choice_type) (in custom pack_type at level 2).
Notation "'vpshufd_inp'" :=(int128 '× int8 : ChoiceEquality) (at level 2).
Notation "'vpshufd_out'" :=(
  int128 : choice_type) (in custom pack_type at level 2).
Notation "'vpshufd_out'" :=(int128 : ChoiceEquality) (at level 2).
Definition VPSHUFD : nat :=
  2231.
Program Definition vpshufd (s_2225 : int128) (o_2226 : int8)
  : both (fset.fset0) [interface] (int128) :=
  ((letb d1_2227 : int32 :=
        vpshufd1 (lift_to_both0 s_2225) (lift_to_both0 o_2226) (lift_to_both0 (
            usize 0)) in
      letb d2_2228 : int32 :=
        vpshufd1 (lift_to_both0 s_2225) (lift_to_both0 o_2226) (lift_to_both0 (
            usize 1)) in
      letb d3_2229 : int32 :=
        vpshufd1 (lift_to_both0 s_2225) (lift_to_both0 o_2226) (lift_to_both0 (
            usize 2)) in
      letb d4_2230 : int32 :=
        vpshufd1 (lift_to_both0 s_2225) (lift_to_both0 o_2226) (lift_to_both0 (
            usize 3)) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (rebuild_u128 (
          lift_to_both0 d1_2227) (lift_to_both0 d2_2228) (
          lift_to_both0 d3_2229) (lift_to_both0 d4_2230))
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
  2239.
Program Definition vshufps (s1_2232 : int128) (s2_2236 : int128) (o_2233 : int8)
  : both (fset.fset0) [interface] (int128) :=
  ((letb d1_2234 : int32 :=
        vpshufd1 (lift_to_both0 s1_2232) (lift_to_both0 o_2233) (lift_to_both0 (
            usize 0)) in
      letb d2_2235 : int32 :=
        vpshufd1 (lift_to_both0 s1_2232) (lift_to_both0 o_2233) (lift_to_both0 (
            usize 1)) in
      letb d3_2237 : int32 :=
        vpshufd1 (lift_to_both0 s2_2236) (lift_to_both0 o_2233) (lift_to_both0 (
            usize 2)) in
      letb d4_2238 : int32 :=
        vpshufd1 (lift_to_both0 s2_2236) (lift_to_both0 o_2233) (lift_to_both0 (
            usize 3)) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (rebuild_u128 (
          lift_to_both0 d1_2234) (lift_to_both0 d2_2235) (
          lift_to_both0 d3_2237) (lift_to_both0 d4_2238))
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
  2249.
Program Definition key_combine (rkey_2243 : int128) (temp1_2240 : int128) (
    temp2_2242 : int128)
  : both (fset.fset0) [interface] ((int128 '× int128)) :=
  ((letb temp1_2241 : int128 :=
        vpshufd (lift_to_both0 temp1_2240) (lift_to_both0 (@repr U8 255)) in
      letb temp2_2244 : int128 :=
        vshufps (lift_to_both0 temp2_2242) (lift_to_both0 rkey_2243) (
          lift_to_both0 (@repr U8 16)) in
      letb rkey_2245 : int128 :=
        (lift_to_both0 rkey_2243) .^ (lift_to_both0 temp2_2244) in
      letb temp2_2246 : int128 :=
        vshufps (lift_to_both0 temp2_2244) (lift_to_both0 rkey_2245) (
          lift_to_both0 (@repr U8 140)) in
      letb rkey_2247 : int128 :=
        (lift_to_both0 rkey_2245) .^ (lift_to_both0 temp2_2246) in
      letb rkey_2248 : int128 :=
        (lift_to_both0 rkey_2247) .^ (lift_to_both0 temp1_2241) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 rkey_2248,
          lift_to_both0 temp2_2246
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
  2258.
Program Definition aeskeygenassist (v1_2250 : int128) (v2_2254 : int8)
  : both (fset.fset0) [interface] (int128) :=
  ((letb x1_2251 : int32 :=
        index_u32 (lift_to_both0 v1_2250) (lift_to_both0 (usize 1)) in
      letb x3_2252 : int32 :=
        index_u32 (lift_to_both0 v1_2250) (lift_to_both0 (usize 3)) in
      letb y0_2253 : int32 := subword (lift_to_both0 x1_2251) in
      letb y1_2255 : int32 :=
        (rotword (lift_to_both0 y0_2253)) .^ (
          (fun x => lift_to_both0 (repr (unsigned x)))(
            lift_to_both0 v2_2254)) in
      letb y2_2256 : int32 := subword (lift_to_both0 x3_2252) in
      letb y3_2257 : int32 :=
        (rotword (lift_to_both0 y2_2256)) .^ (
          (fun x => lift_to_both0 (repr (unsigned x)))(
            lift_to_both0 v2_2254)) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (rebuild_u128 (
          lift_to_both0 y0_2253) (lift_to_both0 y1_2255) (
          lift_to_both0 y2_2256) (lift_to_both0 y3_2257))
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
  2265.
Program Definition key_expand (rcon_2260 : int8) (rkey_2259 : int128) (
    temp2_2262 : int128)
  : both (fset.fset0) [interface] ((int128 '× int128)) :=
  ((letb temp1_2261 : int128 :=
        aeskeygenassist (lift_to_both0 rkey_2259) (lift_to_both0 rcon_2260) in
      letb '(rkey_2263, temp2_2264) : (int128 '× int128) :=
        key_combine (lift_to_both0 rkey_2259) (lift_to_both0 temp1_2261) (
          lift_to_both0 temp2_2262) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 rkey_2263,
          lift_to_both0 temp2_2264
        ))
      ) : both (fset.fset0) [interface] ((int128 '× int128))).
Fail Next Obligation.

Notation "'key_list_t'" := (seq int128) : hacspec_scope.

Definition temp2_2268_loc : ChoiceEqualityLocation :=
  (int128 ; 2269%nat).
Definition rkeys_2266_loc : ChoiceEqualityLocation :=
  (key_list_t ; 2270%nat).
Definition key_2267_loc : ChoiceEqualityLocation :=
  (int128 ; 2271%nat).
Notation "'keys_expand_inp'" :=(
  int128 : choice_type) (in custom pack_type at level 2).
Notation "'keys_expand_inp'" :=(int128 : ChoiceEquality) (at level 2).
Notation "'keys_expand_out'" :=(
  key_list_t : choice_type) (in custom pack_type at level 2).
Notation "'keys_expand_out'" :=(key_list_t : ChoiceEquality) (at level 2).
Definition KEYS_EXPAND : nat :=
  2277.
Program Definition keys_expand (key_2272 : int128)
  : both (CEfset (
      [rkeys_2266_loc ; key_2267_loc ; temp2_2268_loc])) [interface] (
    key_list_t) :=
  ((letbm rkeys_2266 : key_list_t loc( rkeys_2266_loc ) :=
        seq_new_ (default : int128) (lift_to_both0 (usize 0)) in
      letbm key_2267 : int128 loc( key_2267_loc ) := lift_to_both0 key_2272 in
      letbm rkeys_2266 loc( rkeys_2266_loc ) :=
        seq_push (lift_to_both0 rkeys_2266) (lift_to_both0 key_2267) in
      letbm temp2_2268 : int128 loc( temp2_2268_loc ) :=
        lift_to_both0 (@repr U128 0) in
      letb '(rkeys_2266, key_2267, temp2_2268) :=
        foldi_both' (lift_to_both0 (usize 1)) (lift_to_both0 (
              usize 11)) prod_ce(rkeys_2266, key_2267, temp2_2268) (L := (
              CEfset ([rkeys_2266_loc ; key_2267_loc ; temp2_2268_loc]))) (
            I := [interface]) (fun round_2273 '(rkeys_2266, key_2267, temp2_2268
            ) =>
            letb rcon_2274 : int8 :=
              array_index (rcon_v) (lift_to_both0 round_2273) in
            letb '(key_temp_2275, temp2_temp_2276) : (int128 '× int128) :=
              key_expand (lift_to_both0 rcon_2274) (lift_to_both0 key_2267) (
                lift_to_both0 temp2_2268) in
            letbm key_2267 loc( key_2267_loc ) := lift_to_both0 key_temp_2275 in
            letbm temp2_2268 loc( temp2_2268_loc ) :=
              lift_to_both0 temp2_temp_2276 in
            letbm rkeys_2266 loc( rkeys_2266_loc ) :=
              seq_push (lift_to_both0 rkeys_2266) (lift_to_both0 key_2267) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                lift_to_both0 rkeys_2266,
                lift_to_both0 key_2267,
                lift_to_both0 temp2_2268
              ))
            ) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        lift_to_both0 rkeys_2266)
      ) : both (CEfset (
        [rkeys_2266_loc ; key_2267_loc ; temp2_2268_loc])) [interface] (
      key_list_t)).
Fail Next Obligation.


Notation "'subbytes_inp'" :=(
  int128 : choice_type) (in custom pack_type at level 2).
Notation "'subbytes_inp'" :=(int128 : ChoiceEquality) (at level 2).
Notation "'subbytes_out'" :=(
  int128 : choice_type) (in custom pack_type at level 2).
Notation "'subbytes_out'" :=(int128 : ChoiceEquality) (at level 2).
Definition SUBBYTES : nat :=
  2279.
Program Definition subbytes (s_2278 : int128)
  : both (fset.fset0) [interface] (int128) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (rebuild_u128 (subword (
            index_u32 (lift_to_both0 s_2278) (lift_to_both0 (usize 0)))) (
          subword (index_u32 (lift_to_both0 s_2278) (lift_to_both0 (
                usize 1)))) (subword (index_u32 (lift_to_both0 s_2278) (
              lift_to_both0 (usize 2)))) (subword (index_u32 (
              lift_to_both0 s_2278) (lift_to_both0 (usize 3)))))
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
  2283.
Program Definition matrix_index (s_2280 : int128) (i_2282 : uint_size) (
    j_2281 : uint_size)
  : both (fset.fset0) [interface] (int8) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (index_u8 (index_u32 (
            lift_to_both0 s_2280) (lift_to_both0 j_2281)) (
          lift_to_both0 i_2282))
      ) : both (fset.fset0) [interface] (int8)).
Fail Next Obligation.


Notation "'shiftrows_inp'" :=(
  int128 : choice_type) (in custom pack_type at level 2).
Notation "'shiftrows_inp'" :=(int128 : ChoiceEquality) (at level 2).
Notation "'shiftrows_out'" :=(
  int128 : choice_type) (in custom pack_type at level 2).
Notation "'shiftrows_out'" :=(int128 : ChoiceEquality) (at level 2).
Definition SHIFTROWS : nat :=
  2285.
Program Definition shiftrows (s_2284 : int128)
  : both (fset.fset0) [interface] (int128) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (rebuild_u128 (
          rebuild_u32 (matrix_index (lift_to_both0 s_2284) (lift_to_both0 (
                usize 0)) (lift_to_both0 (usize 0))) (matrix_index (
              lift_to_both0 s_2284) (lift_to_both0 (usize 1)) (lift_to_both0 (
                usize 1))) (matrix_index (lift_to_both0 s_2284) (lift_to_both0 (
                usize 2)) (lift_to_both0 (usize 2))) (matrix_index (
              lift_to_both0 s_2284) (lift_to_both0 (usize 3)) (lift_to_both0 (
                usize 3)))) (rebuild_u32 (matrix_index (lift_to_both0 s_2284) (
              lift_to_both0 (usize 0)) (lift_to_both0 (usize 1))) (
            matrix_index (lift_to_both0 s_2284) (lift_to_both0 (usize 1)) (
              lift_to_both0 (usize 2))) (matrix_index (lift_to_both0 s_2284) (
              lift_to_both0 (usize 2)) (lift_to_both0 (usize 3))) (
            matrix_index (lift_to_both0 s_2284) (lift_to_both0 (usize 3)) (
              lift_to_both0 (usize 0)))) (rebuild_u32 (matrix_index (
              lift_to_both0 s_2284) (lift_to_both0 (usize 0)) (lift_to_both0 (
                usize 2))) (matrix_index (lift_to_both0 s_2284) (lift_to_both0 (
                usize 1)) (lift_to_both0 (usize 3))) (matrix_index (
              lift_to_both0 s_2284) (lift_to_both0 (usize 2)) (lift_to_both0 (
                usize 0))) (matrix_index (lift_to_both0 s_2284) (lift_to_both0 (
                usize 3)) (lift_to_both0 (usize 1)))) (rebuild_u32 (
            matrix_index (lift_to_both0 s_2284) (lift_to_both0 (usize 0)) (
              lift_to_both0 (usize 3))) (matrix_index (lift_to_both0 s_2284) (
              lift_to_both0 (usize 1)) (lift_to_both0 (usize 0))) (
            matrix_index (lift_to_both0 s_2284) (lift_to_both0 (usize 2)) (
              lift_to_both0 (usize 1))) (matrix_index (lift_to_both0 s_2284) (
              lift_to_both0 (usize 3)) (lift_to_both0 (usize 2)))))
      ) : both (fset.fset0) [interface] (int128)).
Fail Next Obligation.


Notation "'xtime_inp'" :=(int8 : choice_type) (in custom pack_type at level 2).
Notation "'xtime_inp'" :=(int8 : ChoiceEquality) (at level 2).
Notation "'xtime_out'" :=(int8 : choice_type) (in custom pack_type at level 2).
Notation "'xtime_out'" :=(int8 : ChoiceEquality) (at level 2).
Definition XTIME : nat :=
  2291.
Program Definition xtime (x_2286 : int8)
  : both (fset.fset0) [interface] (int8) :=
  ((letb x1_2287 : int8 :=
        (lift_to_both0 x_2286) shift_left (lift_to_both0 (usize 1)) in
      letb x7_2288 : int8 :=
        (lift_to_both0 x_2286) shift_right (lift_to_both0 (usize 7)) in
      letb x71_2289 : int8 :=
        (lift_to_both0 x7_2288) .& (lift_to_both0 (@repr U8 1)) in
      letb x711b_2290 : int8 :=
        (lift_to_both0 x71_2289) .* (lift_to_both0 (@repr U8 27)) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) ((
          lift_to_both0 x1_2287) .^ (lift_to_both0 x711b_2290))
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
  2303.
Program Definition mixcolumn (c_2293 : uint_size) (state_2292 : int128)
  : both (fset.fset0) [interface] (int32) :=
  ((letb s0_2294 : int8 :=
        matrix_index (lift_to_both0 state_2292) (lift_to_both0 (usize 0)) (
          lift_to_both0 c_2293) in
      letb s1_2295 : int8 :=
        matrix_index (lift_to_both0 state_2292) (lift_to_both0 (usize 1)) (
          lift_to_both0 c_2293) in
      letb s2_2296 : int8 :=
        matrix_index (lift_to_both0 state_2292) (lift_to_both0 (usize 2)) (
          lift_to_both0 c_2293) in
      letb s3_2297 : int8 :=
        matrix_index (lift_to_both0 state_2292) (lift_to_both0 (usize 3)) (
          lift_to_both0 c_2293) in
      letb tmp_2298 : int8 :=
        (((lift_to_both0 s0_2294) .^ (lift_to_both0 s1_2295)) .^ (
            lift_to_both0 s2_2296)) .^ (lift_to_both0 s3_2297) in
      letb r0_2299 : int8 :=
        ((lift_to_both0 s0_2294) .^ (lift_to_both0 tmp_2298)) .^ (xtime ((
              lift_to_both0 s0_2294) .^ (lift_to_both0 s1_2295))) in
      letb r1_2300 : int8 :=
        ((lift_to_both0 s1_2295) .^ (lift_to_both0 tmp_2298)) .^ (xtime ((
              lift_to_both0 s1_2295) .^ (lift_to_both0 s2_2296))) in
      letb r2_2301 : int8 :=
        ((lift_to_both0 s2_2296) .^ (lift_to_both0 tmp_2298)) .^ (xtime ((
              lift_to_both0 s2_2296) .^ (lift_to_both0 s3_2297))) in
      letb r3_2302 : int8 :=
        ((lift_to_both0 s3_2297) .^ (lift_to_both0 tmp_2298)) .^ (xtime ((
              lift_to_both0 s3_2297) .^ (lift_to_both0 s0_2294))) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (rebuild_u32 (
          lift_to_both0 r0_2299) (lift_to_both0 r1_2300) (
          lift_to_both0 r2_2301) (lift_to_both0 r3_2302))
      ) : both (fset.fset0) [interface] (int32)).
Fail Next Obligation.


Notation "'mixcolumns_inp'" :=(
  int128 : choice_type) (in custom pack_type at level 2).
Notation "'mixcolumns_inp'" :=(int128 : ChoiceEquality) (at level 2).
Notation "'mixcolumns_out'" :=(
  int128 : choice_type) (in custom pack_type at level 2).
Notation "'mixcolumns_out'" :=(int128 : ChoiceEquality) (at level 2).
Definition MIXCOLUMNS : nat :=
  2309.
Program Definition mixcolumns (state_2304 : int128)
  : both (fset.fset0) [interface] (int128) :=
  ((letb c0_2305 : int32 :=
        mixcolumn (lift_to_both0 (usize 0)) (lift_to_both0 state_2304) in
      letb c1_2306 : int32 :=
        mixcolumn (lift_to_both0 (usize 1)) (lift_to_both0 state_2304) in
      letb c2_2307 : int32 :=
        mixcolumn (lift_to_both0 (usize 2)) (lift_to_both0 state_2304) in
      letb c3_2308 : int32 :=
        mixcolumn (lift_to_both0 (usize 3)) (lift_to_both0 state_2304) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (rebuild_u128 (
          lift_to_both0 c0_2305) (lift_to_both0 c1_2306) (
          lift_to_both0 c2_2307) (lift_to_both0 c3_2308))
      ) : both (fset.fset0) [interface] (int128)).
Fail Next Obligation.


Notation "'aesenc_inp'" :=(
  int128 '× int128 : choice_type) (in custom pack_type at level 2).
Notation "'aesenc_inp'" :=(int128 '× int128 : ChoiceEquality) (at level 2).
Notation "'aesenc_out'" :=(
  int128 : choice_type) (in custom pack_type at level 2).
Notation "'aesenc_out'" :=(int128 : ChoiceEquality) (at level 2).
Definition AESENC : nat :=
  2315.
Program Definition aesenc (state_2310 : int128) (rkey_2314 : int128)
  : both (fset.fset0) [interface] (int128) :=
  ((letb state_2311 : int128 := shiftrows (lift_to_both0 state_2310) in
      letb state_2312 : int128 := subbytes (lift_to_both0 state_2311) in
      letb state_2313 : int128 := mixcolumns (lift_to_both0 state_2312) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) ((
          lift_to_both0 state_2313) .^ (lift_to_both0 rkey_2314))
      ) : both (fset.fset0) [interface] (int128)).
Fail Next Obligation.


Notation "'aesenclast_inp'" :=(
  int128 '× int128 : choice_type) (in custom pack_type at level 2).
Notation "'aesenclast_inp'" :=(int128 '× int128 : ChoiceEquality) (at level 2).
Notation "'aesenclast_out'" :=(
  int128 : choice_type) (in custom pack_type at level 2).
Notation "'aesenclast_out'" :=(int128 : ChoiceEquality) (at level 2).
Definition AESENCLAST : nat :=
  2320.
Program Definition aesenclast (state_2316 : int128) (rkey_2319 : int128)
  : both (fset.fset0) [interface] (int128) :=
  ((letb state_2317 : int128 := shiftrows (lift_to_both0 state_2316) in
      letb state_2318 : int128 := subbytes (lift_to_both0 state_2317) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) ((
          lift_to_both0 state_2318) .^ (lift_to_both0 rkey_2319))
      ) : both (fset.fset0) [interface] (int128)).
Fail Next Obligation.

Definition state_2321_loc : ChoiceEqualityLocation :=
  (int128 ; 2322%nat).
Notation "'aes_rounds_inp'" :=(
  key_list_t '× int128 : choice_type) (in custom pack_type at level 2).
Notation "'aes_rounds_inp'" :=(
  key_list_t '× int128 : ChoiceEquality) (at level 2).
Notation "'aes_rounds_out'" :=(
  int128 : choice_type) (in custom pack_type at level 2).
Notation "'aes_rounds_out'" :=(int128 : ChoiceEquality) (at level 2).
Definition AES_ROUNDS : nat :=
  2326.
Program Definition aes_rounds (rkeys_2324 : key_list_t) (inp_2323 : int128)
  : both (CEfset ([state_2321_loc])) [interface] (int128) :=
  ((letbm state_2321 : int128 loc( state_2321_loc ) :=
        (lift_to_both0 inp_2323) .^ (seq_index (rkeys_2324) (lift_to_both0 (
              usize 0))) in
      letb state_2321 :=
        foldi_both' (lift_to_both0 (usize 1)) (lift_to_both0 (
              usize 10)) state_2321 (L := (CEfset ([state_2321_loc]))) (
            I := [interface]) (fun round_2325 state_2321 =>
            letbm state_2321 loc( state_2321_loc ) :=
              aesenc (lift_to_both0 state_2321) (seq_index (rkeys_2324) (
                  lift_to_both0 round_2325)) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 state_2321)
            ) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (aesenclast (
          lift_to_both0 state_2321) (seq_index (rkeys_2324) (lift_to_both0 (
              usize 10))))
      ) : both (CEfset ([state_2321_loc])) [interface] (int128)).
Fail Next Obligation.


Notation "'aes_inp'" :=(
  int128 '× int128 : choice_type) (in custom pack_type at level 2).
Notation "'aes_inp'" :=(int128 '× int128 : ChoiceEquality) (at level 2).
Notation "'aes_out'" :=(int128 : choice_type) (in custom pack_type at level 2).
Notation "'aes_out'" :=(int128 : ChoiceEquality) (at level 2).
Definition AES : nat :=
  2330.
Program Definition aes (key_2327 : int128) (inp_2329 : int128)
  : both (CEfset (
      [rkeys_2266_loc ; key_2267_loc ; temp2_2268_loc ; state_2321_loc])) [interface] (
    int128) :=
  ((letb rkeys_2328 : seq int128 := keys_expand (lift_to_both0 key_2327) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (aes_rounds (
          lift_to_both0 rkeys_2328) (lift_to_both0 inp_2329))
      ) : both (CEfset (
        [rkeys_2266_loc ; key_2267_loc ; temp2_2268_loc ; state_2321_loc])) [interface] (
      int128)).
Fail Next Obligation.

