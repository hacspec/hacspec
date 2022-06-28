(** This file was automatically generated using Hacspec **)
Set Warnings "-notation-overridden,-ambiguous-paths".
From Crypt Require Import choice_type Package Prelude.
Import PackageNotation.
From extructures Require Import ord fset.
From CoqWord Require Import ssrZ word.
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

Definition blocksize_v : (uint_size) :=
  ((usize 16)).

Definition ivsize_v : (uint_size) :=
  ((usize 12)).

Definition key_length_v : (uint_size) :=
  ((usize 4)).

Definition rounds_v : (uint_size) :=
  ((usize 10)).

Definition key_schedule_length_v : (uint_size) :=
  ((usize 176)).

Definition iterations_v : (uint_size) :=
  ((usize 40)).

Definition invalid_key_expansion_index_v : (int8) :=
  ((@repr U8 1)).

Definition block_t  :=
  ( nseq (uint8) (blocksize_v)).

Definition word_t  :=
  ( nseq (uint8) (key_length_v)).

Definition round_key_t  :=
  ( nseq (uint8) (blocksize_v)).

Definition aes_nonce_t  :=
  ( nseq (uint8) (ivsize_v)).

Definition s_box_t  :=
  ( nseq (uint8) (usize 256)).

Definition r_con_t  :=
  ( nseq (uint8) (usize 15)).

Definition bytes144_t  :=
  ( nseq (uint8) (usize 144)).

Definition bytes176_t  :=
  ( nseq (uint8) (key_schedule_length_v)).

Definition key128_t  :=
  ( nseq (uint8) (blocksize_v)).

Notation "'byte_seq_result_t'" := ((result int8 byte_seq)) : hacspec_scope.

Notation "'block_result_t'" := ((result int8 block_t)) : hacspec_scope.

Notation "'word_result_t'" := ((result int8 word_t)) : hacspec_scope.

Definition sbox_v : (s_box_t) :=
  (let temp_1 : int8 :=
      (secret (@repr U8 99)) in
    let temp_3 : int8 :=
      (secret (@repr U8 124)) in
    let temp_5 : int8 :=
      (secret (@repr U8 119)) in
    let temp_7 : int8 :=
      (secret (@repr U8 123)) in
    let temp_9 : int8 :=
      (secret (@repr U8 242)) in
    let temp_11 : int8 :=
      (secret (@repr U8 107)) in
    let temp_13 : int8 :=
      (secret (@repr U8 111)) in
    let temp_15 : int8 :=
      (secret (@repr U8 197)) in
    let temp_17 : int8 :=
      (secret (@repr U8 48)) in
    let temp_19 : int8 :=
      (secret (@repr U8 1)) in
    let temp_21 : int8 :=
      (secret (@repr U8 103)) in
    let temp_23 : int8 :=
      (secret (@repr U8 43)) in
    let temp_25 : int8 :=
      (secret (@repr U8 254)) in
    let temp_27 : int8 :=
      (secret (@repr U8 215)) in
    let temp_29 : int8 :=
      (secret (@repr U8 171)) in
    let temp_31 : int8 :=
      (secret (@repr U8 118)) in
    let temp_33 : int8 :=
      (secret (@repr U8 202)) in
    let temp_35 : int8 :=
      (secret (@repr U8 130)) in
    let temp_37 : int8 :=
      (secret (@repr U8 201)) in
    let temp_39 : int8 :=
      (secret (@repr U8 125)) in
    let temp_41 : int8 :=
      (secret (@repr U8 250)) in
    let temp_43 : int8 :=
      (secret (@repr U8 89)) in
    let temp_45 : int8 :=
      (secret (@repr U8 71)) in
    let temp_47 : int8 :=
      (secret (@repr U8 240)) in
    let temp_49 : int8 :=
      (secret (@repr U8 173)) in
    let temp_51 : int8 :=
      (secret (@repr U8 212)) in
    let temp_53 : int8 :=
      (secret (@repr U8 162)) in
    let temp_55 : int8 :=
      (secret (@repr U8 175)) in
    let temp_57 : int8 :=
      (secret (@repr U8 156)) in
    let temp_59 : int8 :=
      (secret (@repr U8 164)) in
    let temp_61 : int8 :=
      (secret (@repr U8 114)) in
    let temp_63 : int8 :=
      (secret (@repr U8 192)) in
    let temp_65 : int8 :=
      (secret (@repr U8 183)) in
    let temp_67 : int8 :=
      (secret (@repr U8 253)) in
    let temp_69 : int8 :=
      (secret (@repr U8 147)) in
    let temp_71 : int8 :=
      (secret (@repr U8 38)) in
    let temp_73 : int8 :=
      (secret (@repr U8 54)) in
    let temp_75 : int8 :=
      (secret (@repr U8 63)) in
    let temp_77 : int8 :=
      (secret (@repr U8 247)) in
    let temp_79 : int8 :=
      (secret (@repr U8 204)) in
    let temp_81 : int8 :=
      (secret (@repr U8 52)) in
    let temp_83 : int8 :=
      (secret (@repr U8 165)) in
    let temp_85 : int8 :=
      (secret (@repr U8 229)) in
    let temp_87 : int8 :=
      (secret (@repr U8 241)) in
    let temp_89 : int8 :=
      (secret (@repr U8 113)) in
    let temp_91 : int8 :=
      (secret (@repr U8 216)) in
    let temp_93 : int8 :=
      (secret (@repr U8 49)) in
    let temp_95 : int8 :=
      (secret (@repr U8 21)) in
    let temp_97 : int8 :=
      (secret (@repr U8 4)) in
    let temp_99 : int8 :=
      (secret (@repr U8 199)) in
    let temp_101 : int8 :=
      (secret (@repr U8 35)) in
    let temp_103 : int8 :=
      (secret (@repr U8 195)) in
    let temp_105 : int8 :=
      (secret (@repr U8 24)) in
    let temp_107 : int8 :=
      (secret (@repr U8 150)) in
    let temp_109 : int8 :=
      (secret (@repr U8 5)) in
    let temp_111 : int8 :=
      (secret (@repr U8 154)) in
    let temp_113 : int8 :=
      (secret (@repr U8 7)) in
    let temp_115 : int8 :=
      (secret (@repr U8 18)) in
    let temp_117 : int8 :=
      (secret (@repr U8 128)) in
    let temp_119 : int8 :=
      (secret (@repr U8 226)) in
    let temp_121 : int8 :=
      (secret (@repr U8 235)) in
    let temp_123 : int8 :=
      (secret (@repr U8 39)) in
    let temp_125 : int8 :=
      (secret (@repr U8 178)) in
    let temp_127 : int8 :=
      (secret (@repr U8 117)) in
    let temp_129 : int8 :=
      (secret (@repr U8 9)) in
    let temp_131 : int8 :=
      (secret (@repr U8 131)) in
    let temp_133 : int8 :=
      (secret (@repr U8 44)) in
    let temp_135 : int8 :=
      (secret (@repr U8 26)) in
    let temp_137 : int8 :=
      (secret (@repr U8 27)) in
    let temp_139 : int8 :=
      (secret (@repr U8 110)) in
    let temp_141 : int8 :=
      (secret (@repr U8 90)) in
    let temp_143 : int8 :=
      (secret (@repr U8 160)) in
    let temp_145 : int8 :=
      (secret (@repr U8 82)) in
    let temp_147 : int8 :=
      (secret (@repr U8 59)) in
    let temp_149 : int8 :=
      (secret (@repr U8 214)) in
    let temp_151 : int8 :=
      (secret (@repr U8 179)) in
    let temp_153 : int8 :=
      (secret (@repr U8 41)) in
    let temp_155 : int8 :=
      (secret (@repr U8 227)) in
    let temp_157 : int8 :=
      (secret (@repr U8 47)) in
    let temp_159 : int8 :=
      (secret (@repr U8 132)) in
    let temp_161 : int8 :=
      (secret (@repr U8 83)) in
    let temp_163 : int8 :=
      (secret (@repr U8 209)) in
    let temp_165 : int8 :=
      (secret (@repr U8 0)) in
    let temp_167 : int8 :=
      (secret (@repr U8 237)) in
    let temp_169 : int8 :=
      (secret (@repr U8 32)) in
    let temp_171 : int8 :=
      (secret (@repr U8 252)) in
    let temp_173 : int8 :=
      (secret (@repr U8 177)) in
    let temp_175 : int8 :=
      (secret (@repr U8 91)) in
    let temp_177 : int8 :=
      (secret (@repr U8 106)) in
    let temp_179 : int8 :=
      (secret (@repr U8 203)) in
    let temp_181 : int8 :=
      (secret (@repr U8 190)) in
    let temp_183 : int8 :=
      (secret (@repr U8 57)) in
    let temp_185 : int8 :=
      (secret (@repr U8 74)) in
    let temp_187 : int8 :=
      (secret (@repr U8 76)) in
    let temp_189 : int8 :=
      (secret (@repr U8 88)) in
    let temp_191 : int8 :=
      (secret (@repr U8 207)) in
    let temp_193 : int8 :=
      (secret (@repr U8 208)) in
    let temp_195 : int8 :=
      (secret (@repr U8 239)) in
    let temp_197 : int8 :=
      (secret (@repr U8 170)) in
    let temp_199 : int8 :=
      (secret (@repr U8 251)) in
    let temp_201 : int8 :=
      (secret (@repr U8 67)) in
    let temp_203 : int8 :=
      (secret (@repr U8 77)) in
    let temp_205 : int8 :=
      (secret (@repr U8 51)) in
    let temp_207 : int8 :=
      (secret (@repr U8 133)) in
    let temp_209 : int8 :=
      (secret (@repr U8 69)) in
    let temp_211 : int8 :=
      (secret (@repr U8 249)) in
    let temp_213 : int8 :=
      (secret (@repr U8 2)) in
    let temp_215 : int8 :=
      (secret (@repr U8 127)) in
    let temp_217 : int8 :=
      (secret (@repr U8 80)) in
    let temp_219 : int8 :=
      (secret (@repr U8 60)) in
    let temp_221 : int8 :=
      (secret (@repr U8 159)) in
    let temp_223 : int8 :=
      (secret (@repr U8 168)) in
    let temp_225 : int8 :=
      (secret (@repr U8 81)) in
    let temp_227 : int8 :=
      (secret (@repr U8 163)) in
    let temp_229 : int8 :=
      (secret (@repr U8 64)) in
    let temp_231 : int8 :=
      (secret (@repr U8 143)) in
    let temp_233 : int8 :=
      (secret (@repr U8 146)) in
    let temp_235 : int8 :=
      (secret (@repr U8 157)) in
    let temp_237 : int8 :=
      (secret (@repr U8 56)) in
    let temp_239 : int8 :=
      (secret (@repr U8 245)) in
    let temp_241 : int8 :=
      (secret (@repr U8 188)) in
    let temp_243 : int8 :=
      (secret (@repr U8 182)) in
    let temp_245 : int8 :=
      (secret (@repr U8 218)) in
    let temp_247 : int8 :=
      (secret (@repr U8 33)) in
    let temp_249 : int8 :=
      (secret (@repr U8 16)) in
    let temp_251 : int8 :=
      (secret (@repr U8 255)) in
    let temp_253 : int8 :=
      (secret (@repr U8 243)) in
    let temp_255 : int8 :=
      (secret (@repr U8 210)) in
    let temp_257 : int8 :=
      (secret (@repr U8 205)) in
    let temp_259 : int8 :=
      (secret (@repr U8 12)) in
    let temp_261 : int8 :=
      (secret (@repr U8 19)) in
    let temp_263 : int8 :=
      (secret (@repr U8 236)) in
    let temp_265 : int8 :=
      (secret (@repr U8 95)) in
    let temp_267 : int8 :=
      (secret (@repr U8 151)) in
    let temp_269 : int8 :=
      (secret (@repr U8 68)) in
    let temp_271 : int8 :=
      (secret (@repr U8 23)) in
    let temp_273 : int8 :=
      (secret (@repr U8 196)) in
    let temp_275 : int8 :=
      (secret (@repr U8 167)) in
    let temp_277 : int8 :=
      (secret (@repr U8 126)) in
    let temp_279 : int8 :=
      (secret (@repr U8 61)) in
    let temp_281 : int8 :=
      (secret (@repr U8 100)) in
    let temp_283 : int8 :=
      (secret (@repr U8 93)) in
    let temp_285 : int8 :=
      (secret (@repr U8 25)) in
    let temp_287 : int8 :=
      (secret (@repr U8 115)) in
    let temp_289 : int8 :=
      (secret (@repr U8 96)) in
    let temp_291 : int8 :=
      (secret (@repr U8 129)) in
    let temp_293 : int8 :=
      (secret (@repr U8 79)) in
    let temp_295 : int8 :=
      (secret (@repr U8 220)) in
    let temp_297 : int8 :=
      (secret (@repr U8 34)) in
    let temp_299 : int8 :=
      (secret (@repr U8 42)) in
    let temp_301 : int8 :=
      (secret (@repr U8 144)) in
    let temp_303 : int8 :=
      (secret (@repr U8 136)) in
    let temp_305 : int8 :=
      (secret (@repr U8 70)) in
    let temp_307 : int8 :=
      (secret (@repr U8 238)) in
    let temp_309 : int8 :=
      (secret (@repr U8 184)) in
    let temp_311 : int8 :=
      (secret (@repr U8 20)) in
    let temp_313 : int8 :=
      (secret (@repr U8 222)) in
    let temp_315 : int8 :=
      (secret (@repr U8 94)) in
    let temp_317 : int8 :=
      (secret (@repr U8 11)) in
    let temp_319 : int8 :=
      (secret (@repr U8 219)) in
    let temp_321 : int8 :=
      (secret (@repr U8 224)) in
    let temp_323 : int8 :=
      (secret (@repr U8 50)) in
    let temp_325 : int8 :=
      (secret (@repr U8 58)) in
    let temp_327 : int8 :=
      (secret (@repr U8 10)) in
    let temp_329 : int8 :=
      (secret (@repr U8 73)) in
    let temp_331 : int8 :=
      (secret (@repr U8 6)) in
    let temp_333 : int8 :=
      (secret (@repr U8 36)) in
    let temp_335 : int8 :=
      (secret (@repr U8 92)) in
    let temp_337 : int8 :=
      (secret (@repr U8 194)) in
    let temp_339 : int8 :=
      (secret (@repr U8 211)) in
    let temp_341 : int8 :=
      (secret (@repr U8 172)) in
    let temp_343 : int8 :=
      (secret (@repr U8 98)) in
    let temp_345 : int8 :=
      (secret (@repr U8 145)) in
    let temp_347 : int8 :=
      (secret (@repr U8 149)) in
    let temp_349 : int8 :=
      (secret (@repr U8 228)) in
    let temp_351 : int8 :=
      (secret (@repr U8 121)) in
    let temp_353 : int8 :=
      (secret (@repr U8 231)) in
    let temp_355 : int8 :=
      (secret (@repr U8 200)) in
    let temp_357 : int8 :=
      (secret (@repr U8 55)) in
    let temp_359 : int8 :=
      (secret (@repr U8 109)) in
    let temp_361 : int8 :=
      (secret (@repr U8 141)) in
    let temp_363 : int8 :=
      (secret (@repr U8 213)) in
    let temp_365 : int8 :=
      (secret (@repr U8 78)) in
    let temp_367 : int8 :=
      (secret (@repr U8 169)) in
    let temp_369 : int8 :=
      (secret (@repr U8 108)) in
    let temp_371 : int8 :=
      (secret (@repr U8 86)) in
    let temp_373 : int8 :=
      (secret (@repr U8 244)) in
    let temp_375 : int8 :=
      (secret (@repr U8 234)) in
    let temp_377 : int8 :=
      (secret (@repr U8 101)) in
    let temp_379 : int8 :=
      (secret (@repr U8 122)) in
    let temp_381 : int8 :=
      (secret (@repr U8 174)) in
    let temp_383 : int8 :=
      (secret (@repr U8 8)) in
    let temp_385 : int8 :=
      (secret (@repr U8 186)) in
    let temp_387 : int8 :=
      (secret (@repr U8 120)) in
    let temp_389 : int8 :=
      (secret (@repr U8 37)) in
    let temp_391 : int8 :=
      (secret (@repr U8 46)) in
    let temp_393 : int8 :=
      (secret (@repr U8 28)) in
    let temp_395 : int8 :=
      (secret (@repr U8 166)) in
    let temp_397 : int8 :=
      (secret (@repr U8 180)) in
    let temp_399 : int8 :=
      (secret (@repr U8 198)) in
    let temp_401 : int8 :=
      (secret (@repr U8 232)) in
    let temp_403 : int8 :=
      (secret (@repr U8 221)) in
    let temp_405 : int8 :=
      (secret (@repr U8 116)) in
    let temp_407 : int8 :=
      (secret (@repr U8 31)) in
    let temp_409 : int8 :=
      (secret (@repr U8 75)) in
    let temp_411 : int8 :=
      (secret (@repr U8 189)) in
    let temp_413 : int8 :=
      (secret (@repr U8 139)) in
    let temp_415 : int8 :=
      (secret (@repr U8 138)) in
    let temp_417 : int8 :=
      (secret (@repr U8 112)) in
    let temp_419 : int8 :=
      (secret (@repr U8 62)) in
    let temp_421 : int8 :=
      (secret (@repr U8 181)) in
    let temp_423 : int8 :=
      (secret (@repr U8 102)) in
    let temp_425 : int8 :=
      (secret (@repr U8 72)) in
    let temp_427 : int8 :=
      (secret (@repr U8 3)) in
    let temp_429 : int8 :=
      (secret (@repr U8 246)) in
    let temp_431 : int8 :=
      (secret (@repr U8 14)) in
    let temp_433 : int8 :=
      (secret (@repr U8 97)) in
    let temp_435 : int8 :=
      (secret (@repr U8 53)) in
    let temp_437 : int8 :=
      (secret (@repr U8 87)) in
    let temp_439 : int8 :=
      (secret (@repr U8 185)) in
    let temp_441 : int8 :=
      (secret (@repr U8 134)) in
    let temp_443 : int8 :=
      (secret (@repr U8 193)) in
    let temp_445 : int8 :=
      (secret (@repr U8 29)) in
    let temp_447 : int8 :=
      (secret (@repr U8 158)) in
    let temp_449 : int8 :=
      (secret (@repr U8 225)) in
    let temp_451 : int8 :=
      (secret (@repr U8 248)) in
    let temp_453 : int8 :=
      (secret (@repr U8 152)) in
    let temp_455 : int8 :=
      (secret (@repr U8 17)) in
    let temp_457 : int8 :=
      (secret (@repr U8 105)) in
    let temp_459 : int8 :=
      (secret (@repr U8 217)) in
    let temp_461 : int8 :=
      (secret (@repr U8 142)) in
    let temp_463 : int8 :=
      (secret (@repr U8 148)) in
    let temp_465 : int8 :=
      (secret (@repr U8 155)) in
    let temp_467 : int8 :=
      (secret (@repr U8 30)) in
    let temp_469 : int8 :=
      (secret (@repr U8 135)) in
    let temp_471 : int8 :=
      (secret (@repr U8 233)) in
    let temp_473 : int8 :=
      (secret (@repr U8 206)) in
    let temp_475 : int8 :=
      (secret (@repr U8 85)) in
    let temp_477 : int8 :=
      (secret (@repr U8 40)) in
    let temp_479 : int8 :=
      (secret (@repr U8 223)) in
    let temp_481 : int8 :=
      (secret (@repr U8 140)) in
    let temp_483 : int8 :=
      (secret (@repr U8 161)) in
    let temp_485 : int8 :=
      (secret (@repr U8 137)) in
    let temp_487 : int8 :=
      (secret (@repr U8 13)) in
    let temp_489 : int8 :=
      (secret (@repr U8 191)) in
    let temp_491 : int8 :=
      (secret (@repr U8 230)) in
    let temp_493 : int8 :=
      (secret (@repr U8 66)) in
    let temp_495 : int8 :=
      (secret (@repr U8 104)) in
    let temp_497 : int8 :=
      (secret (@repr U8 65)) in
    let temp_499 : int8 :=
      (secret (@repr U8 153)) in
    let temp_501 : int8 :=
      (secret (@repr U8 45)) in
    let temp_503 : int8 :=
      (secret (@repr U8 15)) in
    let temp_505 : int8 :=
      (secret (@repr U8 176)) in
    let temp_507 : int8 :=
      (secret (@repr U8 84)) in
    let temp_509 : int8 :=
      (secret (@repr U8 187)) in
    let temp_511 : int8 :=
      (secret (@repr U8 22)) in
    let temp_513 : nseq uint8 256 :=
      (array_from_list uint8 [
          temp_1;
          temp_3;
          temp_5;
          temp_7;
          temp_9;
          temp_11;
          temp_13;
          temp_15;
          temp_17;
          temp_19;
          temp_21;
          temp_23;
          temp_25;
          temp_27;
          temp_29;
          temp_31;
          temp_33;
          temp_35;
          temp_37;
          temp_39;
          temp_41;
          temp_43;
          temp_45;
          temp_47;
          temp_49;
          temp_51;
          temp_53;
          temp_55;
          temp_57;
          temp_59;
          temp_61;
          temp_63;
          temp_65;
          temp_67;
          temp_69;
          temp_71;
          temp_73;
          temp_75;
          temp_77;
          temp_79;
          temp_81;
          temp_83;
          temp_85;
          temp_87;
          temp_89;
          temp_91;
          temp_93;
          temp_95;
          temp_97;
          temp_99;
          temp_101;
          temp_103;
          temp_105;
          temp_107;
          temp_109;
          temp_111;
          temp_113;
          temp_115;
          temp_117;
          temp_119;
          temp_121;
          temp_123;
          temp_125;
          temp_127;
          temp_129;
          temp_131;
          temp_133;
          temp_135;
          temp_137;
          temp_139;
          temp_141;
          temp_143;
          temp_145;
          temp_147;
          temp_149;
          temp_151;
          temp_153;
          temp_155;
          temp_157;
          temp_159;
          temp_161;
          temp_163;
          temp_165;
          temp_167;
          temp_169;
          temp_171;
          temp_173;
          temp_175;
          temp_177;
          temp_179;
          temp_181;
          temp_183;
          temp_185;
          temp_187;
          temp_189;
          temp_191;
          temp_193;
          temp_195;
          temp_197;
          temp_199;
          temp_201;
          temp_203;
          temp_205;
          temp_207;
          temp_209;
          temp_211;
          temp_213;
          temp_215;
          temp_217;
          temp_219;
          temp_221;
          temp_223;
          temp_225;
          temp_227;
          temp_229;
          temp_231;
          temp_233;
          temp_235;
          temp_237;
          temp_239;
          temp_241;
          temp_243;
          temp_245;
          temp_247;
          temp_249;
          temp_251;
          temp_253;
          temp_255;
          temp_257;
          temp_259;
          temp_261;
          temp_263;
          temp_265;
          temp_267;
          temp_269;
          temp_271;
          temp_273;
          temp_275;
          temp_277;
          temp_279;
          temp_281;
          temp_283;
          temp_285;
          temp_287;
          temp_289;
          temp_291;
          temp_293;
          temp_295;
          temp_297;
          temp_299;
          temp_301;
          temp_303;
          temp_305;
          temp_307;
          temp_309;
          temp_311;
          temp_313;
          temp_315;
          temp_317;
          temp_319;
          temp_321;
          temp_323;
          temp_325;
          temp_327;
          temp_329;
          temp_331;
          temp_333;
          temp_335;
          temp_337;
          temp_339;
          temp_341;
          temp_343;
          temp_345;
          temp_347;
          temp_349;
          temp_351;
          temp_353;
          temp_355;
          temp_357;
          temp_359;
          temp_361;
          temp_363;
          temp_365;
          temp_367;
          temp_369;
          temp_371;
          temp_373;
          temp_375;
          temp_377;
          temp_379;
          temp_381;
          temp_383;
          temp_385;
          temp_387;
          temp_389;
          temp_391;
          temp_393;
          temp_395;
          temp_397;
          temp_399;
          temp_401;
          temp_403;
          temp_405;
          temp_407;
          temp_409;
          temp_411;
          temp_413;
          temp_415;
          temp_417;
          temp_419;
          temp_421;
          temp_423;
          temp_425;
          temp_427;
          temp_429;
          temp_431;
          temp_433;
          temp_435;
          temp_437;
          temp_439;
          temp_441;
          temp_443;
          temp_445;
          temp_447;
          temp_449;
          temp_451;
          temp_453;
          temp_455;
          temp_457;
          temp_459;
          temp_461;
          temp_463;
          temp_465;
          temp_467;
          temp_469;
          temp_471;
          temp_473;
          temp_475;
          temp_477;
          temp_479;
          temp_481;
          temp_483;
          temp_485;
          temp_487;
          temp_489;
          temp_491;
          temp_493;
          temp_495;
          temp_497;
          temp_499;
          temp_501;
          temp_503;
          temp_505;
          temp_507;
          temp_509;
          temp_511
        ]) in
    (temp_513)).

Definition rcon_v : (r_con_t) :=
  (let temp_515 : int8 :=
      (secret (@repr U8 141)) in
    let temp_517 : int8 :=
      (secret (@repr U8 1)) in
    let temp_519 : int8 :=
      (secret (@repr U8 2)) in
    let temp_521 : int8 :=
      (secret (@repr U8 4)) in
    let temp_523 : int8 :=
      (secret (@repr U8 8)) in
    let temp_525 : int8 :=
      (secret (@repr U8 16)) in
    let temp_527 : int8 :=
      (secret (@repr U8 32)) in
    let temp_529 : int8 :=
      (secret (@repr U8 64)) in
    let temp_531 : int8 :=
      (secret (@repr U8 128)) in
    let temp_533 : int8 :=
      (secret (@repr U8 27)) in
    let temp_535 : int8 :=
      (secret (@repr U8 54)) in
    let temp_537 : int8 :=
      (secret (@repr U8 108)) in
    let temp_539 : int8 :=
      (secret (@repr U8 216)) in
    let temp_541 : int8 :=
      (secret (@repr U8 171)) in
    let temp_543 : int8 :=
      (secret (@repr U8 77)) in
    let temp_545 : nseq uint8 15 :=
      (array_from_list uint8 [
          temp_515;
          temp_517;
          temp_519;
          temp_521;
          temp_523;
          temp_525;
          temp_527;
          temp_529;
          temp_531;
          temp_533;
          temp_535;
          temp_537;
          temp_539;
          temp_541;
          temp_543
        ]) in
    (temp_545)).

Definition st_554_loc : ChoiceEqualityLocation :=
  ((block_t ; 555%nat)).
Notation "'sub_bytes_inp'" :=(
  block_t : choice_type) (in custom pack_type at level 2).
Notation "'sub_bytes_out'" :=(
  block_t : choice_type) (in custom pack_type at level 2).
Definition SUB_BYTES : nat :=
  (556).
Program Definition sub_bytes
   : package (CEfset ([st_554_loc])) [interface  ] [interface
  #val #[ SUB_BYTES ] : sub_bytes_inp → sub_bytes_out ] :=
  ([package #def #[ SUB_BYTES ] (temp_inp : sub_bytes_inp) : sub_bytes_out { 
    let '(state_546) := temp_inp : block_t in
    ({ code  '(st_554 : block_t) ←
          (ret (state_546)) ;;
        #put st_554_loc := st_554 ;;
       '(st_554 : (block_t)) ←
        (foldi' (usize 0) (blocksize_v) st_554 (L2 := CEfset ([st_554_loc])) (
              I2 := [interface 
              ]) (H_loc_incl := _) (H_opsig_incl := _) (fun i_547 st_554 =>
            ({ code  '(st_554 : block_t) ←
                ( temp_549 ←
                    (array_index (state_546) (i_547)) ;;
                   temp_551 ←
                    (uint8_declassify (temp_549)) ;;
                   temp_553 ←
                    (array_index (sbox_v) (temp_551)) ;;
                  ret (array_upd st_554 (i_547) (temp_553))) ;;
              
              @ret ((block_t)) (st_554) } : code (CEfset (
                  [st_554_loc])) [interface  ] _))) ;;
      
      @ret (block_t) (st_554) } : code (CEfset ([st_554_loc])) [interface  ] _)
    }]).
Fail Next Obligation.
Program Definition package_sub_bytes : package _ _ _ :=
  (sub_bytes).
Fail Next Obligation.

Definition out_604_loc : ChoiceEqualityLocation :=
  ((block_t ; 605%nat)).
Notation "'shift_row_inp'" :=(
  uint_size '× uint_size '× block_t : choice_type) (in custom pack_type at level 2).
Notation "'shift_row_out'" :=(
  block_t : choice_type) (in custom pack_type at level 2).
Definition SHIFT_ROW : nat :=
  (606).
Program Definition shift_row
   : package (CEfset ([out_604_loc])) [interface  ] [interface
  #val #[ SHIFT_ROW ] : shift_row_inp → shift_row_out ] :=
  ([package #def #[ SHIFT_ROW ] (temp_inp : shift_row_inp) : shift_row_out { 
    let '(
      i_558 , shift_559 , state_557) := temp_inp : uint_size '× uint_size '× block_t in
    ({ code  '(out_604 : block_t) ←
          (ret (state_557)) ;;
        #put out_604_loc := out_604 ;;
       '(out_604 : block_t) ←
        ( '(temp_561 : uint_size) ←
            ((shift_559) %% (usize 4)) ;;
           '(temp_563 : uint_size) ←
            ((usize 4) .* (temp_561)) ;;
           '(temp_565 : uint_size) ←
            ((i_558) .+ (temp_563)) ;;
           temp_567 ←
            (array_index (state_557) (temp_565)) ;;
          ret (array_upd out_604 (i_558) (temp_567))) ;;
      
       '(out_604 : block_t) ←
        ( '(temp_569 : uint_size) ←
            ((i_558) .+ (usize 4)) ;;
           '(temp_571 : uint_size) ←
            ((shift_559) .+ (usize 1)) ;;
           '(temp_573 : uint_size) ←
            ((temp_571) %% (usize 4)) ;;
           '(temp_575 : uint_size) ←
            ((usize 4) .* (temp_573)) ;;
           '(temp_577 : uint_size) ←
            ((i_558) .+ (temp_575)) ;;
           temp_579 ←
            (array_index (state_557) (temp_577)) ;;
          ret (array_upd out_604 (temp_569) (temp_579))) ;;
      
       '(out_604 : block_t) ←
        ( '(temp_581 : uint_size) ←
            ((i_558) .+ (usize 8)) ;;
           '(temp_583 : uint_size) ←
            ((shift_559) .+ (usize 2)) ;;
           '(temp_585 : uint_size) ←
            ((temp_583) %% (usize 4)) ;;
           '(temp_587 : uint_size) ←
            ((usize 4) .* (temp_585)) ;;
           '(temp_589 : uint_size) ←
            ((i_558) .+ (temp_587)) ;;
           temp_591 ←
            (array_index (state_557) (temp_589)) ;;
          ret (array_upd out_604 (temp_581) (temp_591))) ;;
      
       '(out_604 : block_t) ←
        ( '(temp_593 : uint_size) ←
            ((i_558) .+ (usize 12)) ;;
           '(temp_595 : uint_size) ←
            ((shift_559) .+ (usize 3)) ;;
           '(temp_597 : uint_size) ←
            ((temp_595) %% (usize 4)) ;;
           '(temp_599 : uint_size) ←
            ((usize 4) .* (temp_597)) ;;
           '(temp_601 : uint_size) ←
            ((i_558) .+ (temp_599)) ;;
           temp_603 ←
            (array_index (state_557) (temp_601)) ;;
          ret (array_upd out_604 (temp_593) (temp_603))) ;;
      
      @ret (block_t) (out_604) } : code (CEfset ([out_604_loc])) [interface 
      ] _)
    }]).
Fail Next Obligation.
Program Definition package_shift_row : package _ _ _ :=
  (shift_row).
Fail Next Obligation.


Notation "'shift_rows_inp'" :=(
  block_t : choice_type) (in custom pack_type at level 2).
Notation "'shift_rows_out'" :=(
  block_t : choice_type) (in custom pack_type at level 2).
Definition SHIFT_ROWS : nat :=
  (616).
Program Definition shift_rows
   : package (CEfset ([])) [interface
  #val #[ SHIFT_ROW ] : shift_row_inp → shift_row_out ] [interface
  #val #[ SHIFT_ROWS ] : shift_rows_inp → shift_rows_out ] :=
  ([package #def #[ SHIFT_ROWS ] (temp_inp : shift_rows_inp) : shift_rows_out { 
    let '(state_607) := temp_inp : block_t in
    #import {sig #[ SHIFT_ROW ] : shift_row_inp → shift_row_out } as  shift_row ;;
    let shift_row := fun x_0 x_1 x_2 => shift_row (x_0,x_1,x_2) in
    ({ code  '(state_610 : block_t) ←
        ( '(temp_609 : block_t) ←
            (shift_row (usize 1) (usize 1) (state_607)) ;;
          ret (temp_609)) ;;
       '(state_613 : block_t) ←
        ( '(temp_612 : block_t) ←
            (shift_row (usize 2) (usize 2) (state_610)) ;;
          ret (temp_612)) ;;
       '(temp_615 : block_t) ←
        (shift_row (usize 3) (usize 3) (state_613)) ;;
      @ret (block_t) (temp_615) } : code (CEfset ([])) [interface
      #val #[ SHIFT_ROW ] : shift_row_inp → shift_row_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_shift_rows : package _ _ _ :=
  (seq_link shift_rows link_rest(package_shift_row)).
Fail Next Obligation.


Notation "'xtime_inp'" :=(uint8 : choice_type) (in custom pack_type at level 2).
Notation "'xtime_out'" :=(uint8 : choice_type) (in custom pack_type at level 2).
Definition XTIME : nat :=
  (636).
Program Definition xtime
   : package (fset.fset0) [interface  ] [interface
  #val #[ XTIME ] : xtime_inp → xtime_out ] :=
  ([package #def #[ XTIME ] (temp_inp : xtime_inp) : xtime_out { 
    let '(x_617) := temp_inp : uint8 in
    ({ code  '(x1_632 : uint8) ←
        ( temp_619 ←
            ((x_617) shift_left (usize 1)) ;;
          ret (temp_619)) ;;
       '(x7_622 : uint8) ←
        ( temp_621 ←
            ((x_617) shift_right (usize 7)) ;;
          ret (temp_621)) ;;
       '(x71_627 : uint8) ←
        ( '(temp_624 : int8) ←
            (secret (@repr U8 1)) ;;
           temp_626 ←
            ((x7_622) .& (temp_624)) ;;
          ret (temp_626)) ;;
       '(x711b_633 : uint8) ←
        ( '(temp_629 : int8) ←
            (secret (@repr U8 27)) ;;
           '(temp_631 : uint8) ←
            ((x71_627) .* (temp_629)) ;;
          ret (temp_631)) ;;
       temp_635 ←
        ((x1_632) .^ (x711b_633)) ;;
      @ret (uint8) (temp_635) } : code (fset.fset0) [interface  ] _)
    }]).
Fail Next Obligation.
Program Definition package_xtime : package _ _ _ :=
  (xtime).
Fail Next Obligation.

Definition st_705_loc : ChoiceEqualityLocation :=
  ((block_t ; 706%nat)).
Notation "'mix_column_inp'" :=(
  uint_size '× block_t : choice_type) (in custom pack_type at level 2).
Notation "'mix_column_out'" :=(
  block_t : choice_type) (in custom pack_type at level 2).
Definition MIX_COLUMN : nat :=
  (707).
Program Definition mix_column
   : package (CEfset ([st_705_loc])) [interface
  #val #[ XTIME ] : xtime_inp → xtime_out ] [interface
  #val #[ MIX_COLUMN ] : mix_column_inp → mix_column_out ] :=
  ([package #def #[ MIX_COLUMN ] (temp_inp : mix_column_inp) : mix_column_out { 
    let '(c_637 , state_642) := temp_inp : uint_size '× block_t in
    #import {sig #[ XTIME ] : xtime_inp → xtime_out } as  xtime ;;
    let xtime := fun x_0 => xtime (x_0) in
    ({ code  '(i0_640 : uint_size) ←
        ( '(temp_639 : uint_size) ←
            ((usize 4) .* (c_637)) ;;
          ret (temp_639)) ;;
       '(s0_656 : uint8) ←
        ( temp_643 ←
            (array_index (state_642) (i0_640)) ;;
          ret (temp_643)) ;;
       '(s1_657 : uint8) ←
        ( '(temp_645 : uint_size) ←
            ((i0_640) .+ (usize 1)) ;;
           temp_647 ←
            (array_index (state_642) (temp_645)) ;;
          ret (temp_647)) ;;
       '(s2_660 : uint8) ←
        ( '(temp_649 : uint_size) ←
            ((i0_640) .+ (usize 2)) ;;
           temp_651 ←
            (array_index (state_642) (temp_649)) ;;
          ret (temp_651)) ;;
       '(s3_663 : uint8) ←
        ( '(temp_653 : uint_size) ←
            ((i0_640) .+ (usize 3)) ;;
           temp_655 ←
            (array_index (state_642) (temp_653)) ;;
          ret (temp_655)) ;;
       '(st_705 : block_t) ←
          (ret (state_642)) ;;
        #put st_705_loc := st_705 ;;
       '(tmp_666 : uint8) ←
        ( temp_659 ←
            ((s0_656) .^ (s1_657)) ;;
           temp_662 ←
            ((temp_659) .^ (s2_660)) ;;
           temp_665 ←
            ((temp_662) .^ (s3_663)) ;;
          ret (temp_665)) ;;
       '(st_705 : block_t) ←
        ( temp_668 ←
            ((s0_656) .^ (tmp_666)) ;;
           temp_670 ←
            ((s0_656) .^ (s1_657)) ;;
           '(temp_672 : uint8) ←
            (xtime (temp_670)) ;;
           temp_674 ←
            ((temp_668) .^ (temp_672)) ;;
          ret (array_upd st_705 (i0_640) (temp_674))) ;;
      
       '(st_705 : block_t) ←
        ( '(temp_676 : uint_size) ←
            ((i0_640) .+ (usize 1)) ;;
           temp_678 ←
            ((s1_657) .^ (tmp_666)) ;;
           temp_680 ←
            ((s1_657) .^ (s2_660)) ;;
           '(temp_682 : uint8) ←
            (xtime (temp_680)) ;;
           temp_684 ←
            ((temp_678) .^ (temp_682)) ;;
          ret (array_upd st_705 (temp_676) (temp_684))) ;;
      
       '(st_705 : block_t) ←
        ( '(temp_686 : uint_size) ←
            ((i0_640) .+ (usize 2)) ;;
           temp_688 ←
            ((s2_660) .^ (tmp_666)) ;;
           temp_690 ←
            ((s2_660) .^ (s3_663)) ;;
           '(temp_692 : uint8) ←
            (xtime (temp_690)) ;;
           temp_694 ←
            ((temp_688) .^ (temp_692)) ;;
          ret (array_upd st_705 (temp_686) (temp_694))) ;;
      
       '(st_705 : block_t) ←
        ( '(temp_696 : uint_size) ←
            ((i0_640) .+ (usize 3)) ;;
           temp_698 ←
            ((s3_663) .^ (tmp_666)) ;;
           temp_700 ←
            ((s3_663) .^ (s0_656)) ;;
           '(temp_702 : uint8) ←
            (xtime (temp_700)) ;;
           temp_704 ←
            ((temp_698) .^ (temp_702)) ;;
          ret (array_upd st_705 (temp_696) (temp_704))) ;;
      
      @ret (block_t) (st_705) } : code (CEfset ([st_705_loc])) [interface
      #val #[ XTIME ] : xtime_inp → xtime_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_mix_column : package _ _ _ :=
  (seq_link mix_column link_rest(package_xtime)).
Fail Next Obligation.


Notation "'mix_columns_inp'" :=(
  block_t : choice_type) (in custom pack_type at level 2).
Notation "'mix_columns_out'" :=(
  block_t : choice_type) (in custom pack_type at level 2).
Definition MIX_COLUMNS : nat :=
  (720).
Program Definition mix_columns
   : package (CEfset ([])) [interface
  #val #[ MIX_COLUMN ] : mix_column_inp → mix_column_out ] [interface
  #val #[ MIX_COLUMNS ] : mix_columns_inp → mix_columns_out ] :=
  (
    [package #def #[ MIX_COLUMNS ] (temp_inp : mix_columns_inp) : mix_columns_out { 
    let '(state_708) := temp_inp : block_t in
    #import {sig #[ MIX_COLUMN ] : mix_column_inp → mix_column_out } as  mix_column ;;
    let mix_column := fun x_0 x_1 => mix_column (x_0,x_1) in
    ({ code  '(state_711 : block_t) ←
        ( '(temp_710 : block_t) ←
            (mix_column (usize 0) (state_708)) ;;
          ret (temp_710)) ;;
       '(state_714 : block_t) ←
        ( '(temp_713 : block_t) ←
            (mix_column (usize 1) (state_711)) ;;
          ret (temp_713)) ;;
       '(state_717 : block_t) ←
        ( '(temp_716 : block_t) ←
            (mix_column (usize 2) (state_714)) ;;
          ret (temp_716)) ;;
       '(temp_719 : block_t) ←
        (mix_column (usize 3) (state_717)) ;;
      @ret (block_t) (temp_719) } : code (CEfset ([])) [interface
      #val #[ MIX_COLUMN ] : mix_column_inp → mix_column_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_mix_columns : package _ _ _ :=
  (seq_link mix_columns link_rest(package_mix_column)).
Fail Next Obligation.

Definition out_724_loc : ChoiceEqualityLocation :=
  ((block_t ; 731%nat)).
Notation "'add_round_key_inp'" :=(
  block_t '× round_key_t : choice_type) (in custom pack_type at level 2).
Notation "'add_round_key_out'" :=(
  block_t : choice_type) (in custom pack_type at level 2).
Definition ADD_ROUND_KEY : nat :=
  (732).
Program Definition add_round_key
   : package (CEfset ([out_724_loc])) [interface  ] [interface
  #val #[ ADD_ROUND_KEY ] : add_round_key_inp → add_round_key_out ] :=
  (
    [package #def #[ ADD_ROUND_KEY ] (temp_inp : add_round_key_inp) : add_round_key_out { 
    let '(state_721 , key_727) := temp_inp : block_t '× round_key_t in
    ({ code  '(out_724 : block_t) ←
          (ret (state_721)) ;;
        #put out_724_loc := out_724 ;;
       '(out_724 : (block_t)) ←
        (foldi' (usize 0) (blocksize_v) out_724 (L2 := CEfset ([out_724_loc])) (
              I2 := [interface 
              ]) (H_loc_incl := _) (H_opsig_incl := _) (fun i_722 out_724 =>
            ({ code  '(out_724 : block_t) ←
                ( temp_725 ←
                    (array_index (out_724) (i_722)) ;;
                   temp_728 ←
                    (array_index (key_727) (i_722)) ;;
                   temp_730 ←
                    ((temp_725) .^ (temp_728)) ;;
                  ret (array_upd out_724 (i_722) (temp_730))) ;;
              
              @ret ((block_t)) (out_724) } : code (CEfset (
                  [out_724_loc])) [interface  ] _))) ;;
      
      @ret (block_t) (out_724) } : code (CEfset ([out_724_loc])) [interface 
      ] _)
    }]).
Fail Next Obligation.
Program Definition package_add_round_key : package _ _ _ :=
  (add_round_key).
Fail Next Obligation.


Notation "'aes_enc_inp'" :=(
  block_t '× round_key_t : choice_type) (in custom pack_type at level 2).
Notation "'aes_enc_out'" :=(
  block_t : choice_type) (in custom pack_type at level 2).
Definition AES_ENC : nat :=
  (746).
Program Definition aes_enc
   : package (CEfset ([])) [interface
  #val #[ ADD_ROUND_KEY ] : add_round_key_inp → add_round_key_out ;
  #val #[ MIX_COLUMNS ] : mix_columns_inp → mix_columns_out ;
  #val #[ SHIFT_ROWS ] : shift_rows_inp → shift_rows_out ;
  #val #[ SUB_BYTES ] : sub_bytes_inp → sub_bytes_out ] [interface
  #val #[ AES_ENC ] : aes_enc_inp → aes_enc_out ] :=
  ([package #def #[ AES_ENC ] (temp_inp : aes_enc_inp) : aes_enc_out { 
    let '(state_733 , round_key_743) := temp_inp : block_t '× round_key_t in
    #import {sig #[ ADD_ROUND_KEY ] : add_round_key_inp → add_round_key_out } as  add_round_key ;;
    let add_round_key := fun x_0 x_1 => add_round_key (x_0,x_1) in
    #import {sig #[ MIX_COLUMNS ] : mix_columns_inp → mix_columns_out } as  mix_columns ;;
    let mix_columns := fun x_0 => mix_columns (x_0) in
    #import {sig #[ SHIFT_ROWS ] : shift_rows_inp → shift_rows_out } as  shift_rows ;;
    let shift_rows := fun x_0 => shift_rows (x_0) in
    #import {sig #[ SUB_BYTES ] : sub_bytes_inp → sub_bytes_out } as  sub_bytes ;;
    let sub_bytes := fun x_0 => sub_bytes (x_0) in
    ({ code  '(state_736 : block_t) ←
        ( '(temp_735 : block_t) ←
            (sub_bytes (state_733)) ;;
          ret (temp_735)) ;;
       '(state_739 : block_t) ←
        ( '(temp_738 : block_t) ←
            (shift_rows (state_736)) ;;
          ret (temp_738)) ;;
       '(state_742 : block_t) ←
        ( '(temp_741 : block_t) ←
            (mix_columns (state_739)) ;;
          ret (temp_741)) ;;
       '(temp_745 : block_t) ←
        (add_round_key (state_742) (round_key_743)) ;;
      @ret (block_t) (temp_745) } : code (CEfset ([])) [interface
      #val #[ ADD_ROUND_KEY ] : add_round_key_inp → add_round_key_out ;
      #val #[ MIX_COLUMNS ] : mix_columns_inp → mix_columns_out ;
      #val #[ SHIFT_ROWS ] : shift_rows_inp → shift_rows_out ;
      #val #[ SUB_BYTES ] : sub_bytes_inp → sub_bytes_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_aes_enc : package _ _ _ :=
  (seq_link aes_enc link_rest(
      package_add_round_key,package_mix_columns,package_shift_rows,package_sub_bytes)).
Fail Next Obligation.


Notation "'aes_enc_last_inp'" :=(
  block_t '× round_key_t : choice_type) (in custom pack_type at level 2).
Notation "'aes_enc_last_out'" :=(
  block_t : choice_type) (in custom pack_type at level 2).
Definition AES_ENC_LAST : nat :=
  (757).
Program Definition aes_enc_last
   : package (CEfset ([])) [interface
  #val #[ ADD_ROUND_KEY ] : add_round_key_inp → add_round_key_out ;
  #val #[ SHIFT_ROWS ] : shift_rows_inp → shift_rows_out ;
  #val #[ SUB_BYTES ] : sub_bytes_inp → sub_bytes_out ] [interface
  #val #[ AES_ENC_LAST ] : aes_enc_last_inp → aes_enc_last_out ] :=
  (
    [package #def #[ AES_ENC_LAST ] (temp_inp : aes_enc_last_inp) : aes_enc_last_out { 
    let '(state_747 , round_key_754) := temp_inp : block_t '× round_key_t in
    #import {sig #[ ADD_ROUND_KEY ] : add_round_key_inp → add_round_key_out } as  add_round_key ;;
    let add_round_key := fun x_0 x_1 => add_round_key (x_0,x_1) in
    #import {sig #[ SHIFT_ROWS ] : shift_rows_inp → shift_rows_out } as  shift_rows ;;
    let shift_rows := fun x_0 => shift_rows (x_0) in
    #import {sig #[ SUB_BYTES ] : sub_bytes_inp → sub_bytes_out } as  sub_bytes ;;
    let sub_bytes := fun x_0 => sub_bytes (x_0) in
    ({ code  '(state_750 : block_t) ←
        ( '(temp_749 : block_t) ←
            (sub_bytes (state_747)) ;;
          ret (temp_749)) ;;
       '(state_753 : block_t) ←
        ( '(temp_752 : block_t) ←
            (shift_rows (state_750)) ;;
          ret (temp_752)) ;;
       '(temp_756 : block_t) ←
        (add_round_key (state_753) (round_key_754)) ;;
      @ret (block_t) (temp_756) } : code (CEfset ([])) [interface
      #val #[ ADD_ROUND_KEY ] : add_round_key_inp → add_round_key_out ;
      #val #[ SHIFT_ROWS ] : shift_rows_inp → shift_rows_out ;
      #val #[ SUB_BYTES ] : sub_bytes_inp → sub_bytes_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_aes_enc_last : package _ _ _ :=
  (seq_link aes_enc_last link_rest(
      package_add_round_key,package_shift_rows,package_sub_bytes)).
Fail Next Obligation.

Definition out_765_loc : ChoiceEqualityLocation :=
  ((block_t ; 773%nat)).
Notation "'rounds_aes_inp'" :=(
  block_t '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'rounds_aes_out'" :=(
  block_t : choice_type) (in custom pack_type at level 2).
Definition ROUNDS_AES : nat :=
  (774).
Program Definition rounds_aes
   : package (CEfset ([out_765_loc])) [interface
  #val #[ AES_ENC ] : aes_enc_inp → aes_enc_out ] [interface
  #val #[ ROUNDS_AES ] : rounds_aes_inp → rounds_aes_out ] :=
  ([package #def #[ ROUNDS_AES ] (temp_inp : rounds_aes_inp) : rounds_aes_out { 
    let '(state_758 , key_759) := temp_inp : block_t '× byte_seq in
    #import {sig #[ AES_ENC ] : aes_enc_inp → aes_enc_out } as  aes_enc ;;
    let aes_enc := fun x_0 x_1 => aes_enc (x_0,x_1) in
    ({ code  '(out_765 : block_t) ←
          (ret (state_758)) ;;
        #put out_765_loc := out_765 ;;
       '(temp_761 : uint_size) ←
        (seq_num_chunks (key_759) (blocksize_v)) ;;
       '(out_765 : (block_t)) ←
        (foldi' (usize 0) (temp_761) out_765 (L2 := CEfset ([out_765_loc])) (
              I2 := [interface #val #[ AES_ENC ] : aes_enc_inp → aes_enc_out
              ]) (H_loc_incl := _) (H_opsig_incl := _) (fun i_762 out_765 =>
            ({ code  temp_772 ←
                ( '(temp_764 : (uint_size '× seq uint8)) ←
                    (seq_get_chunk (key_759) (blocksize_v) (i_762)) ;;
                  ret (temp_764)) ;;
              let '(_, key_block_766) :=
                (temp_772) : (uint_size '× seq uint8) in
               '(out_765 : block_t) ←
                  (( '(temp_768 : round_key_t) ←
                        (array_from_seq (blocksize_v) (key_block_766)) ;;
                       '(temp_770 : block_t) ←
                        (aes_enc (out_765) (temp_768)) ;;
                      ret (temp_770))) ;;
                #put out_765_loc := out_765 ;;
              
              @ret ((block_t)) (out_765) } : code (CEfset (
                  [out_765_loc])) [interface
              #val #[ AES_ENC ] : aes_enc_inp → aes_enc_out ] _))) ;;
      
      @ret (block_t) (out_765) } : code (CEfset ([out_765_loc])) [interface
      #val #[ AES_ENC ] : aes_enc_inp → aes_enc_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_rounds_aes : package _ _ _ :=
  (seq_link rounds_aes link_rest(package_aes_enc)).
Fail Next Obligation.


Notation "'block_cipher_aes_inp'" :=(
  block_t '× byte_seq '× uint_size : choice_type) (in custom pack_type at level 2).
Notation "'block_cipher_aes_out'" :=(
  block_t : choice_type) (in custom pack_type at level 2).
Definition BLOCK_CIPHER_AES : nat :=
  (799).
Program Definition block_cipher_aes
   : package (CEfset ([])) [interface
  #val #[ ADD_ROUND_KEY ] : add_round_key_inp → add_round_key_out ;
  #val #[ AES_ENC_LAST ] : aes_enc_last_inp → aes_enc_last_out ;
  #val #[ ROUNDS_AES ] : rounds_aes_inp → rounds_aes_out ] [interface
  #val #[ BLOCK_CIPHER_AES ] : block_cipher_aes_inp → block_cipher_aes_out
  ] :=
  (
    [package #def #[ BLOCK_CIPHER_AES ] (temp_inp : block_cipher_aes_inp) : block_cipher_aes_out { 
    let '(
      input_787 , key_775 , nr_778) := temp_inp : block_t '× byte_seq '× uint_size in
    #import {sig #[ ADD_ROUND_KEY ] : add_round_key_inp → add_round_key_out } as  add_round_key ;;
    let add_round_key := fun x_0 x_1 => add_round_key (x_0,x_1) in
    #import {sig #[ AES_ENC_LAST ] : aes_enc_last_inp → aes_enc_last_out } as  aes_enc_last ;;
    let aes_enc_last := fun x_0 x_1 => aes_enc_last (x_0,x_1) in
    #import {sig #[ ROUNDS_AES ] : rounds_aes_inp → rounds_aes_out } as  rounds_aes ;;
    let rounds_aes := fun x_0 x_1 => rounds_aes (x_0,x_1) in
    ({ code  '(k0_788 : round_key_t) ←
        ( '(temp_777 : round_key_t) ←
            (array_from_slice_range (default : uint8) (blocksize_v) (key_775) (
                prod_ce(usize 0, usize 16))) ;;
          ret (temp_777)) ;;
       '(k_792 : seq uint8) ←
        ( '(temp_780 : uint_size) ←
            ((nr_778) .* (usize 16)) ;;
           '(temp_782 : byte_seq) ←
            (seq_from_slice_range (key_775) (prod_ce(usize 16, temp_780))) ;;
          ret (temp_782)) ;;
       '(kn_796 : round_key_t) ←
        ( '(temp_784 : uint_size) ←
            ((nr_778) .* (usize 16)) ;;
           '(temp_786 : round_key_t) ←
            (array_from_slice (default : uint8) (blocksize_v) (key_775) (
                temp_784) (usize 16)) ;;
          ret (temp_786)) ;;
       '(state_791 : block_t) ←
        ( '(temp_790 : block_t) ←
            (add_round_key (input_787) (k0_788)) ;;
          ret (temp_790)) ;;
       '(state_795 : block_t) ←
        ( '(temp_794 : block_t) ←
            (rounds_aes (state_791) (k_792)) ;;
          ret (temp_794)) ;;
       '(temp_798 : block_t) ←
        (aes_enc_last (state_795) (kn_796)) ;;
      @ret (block_t) (temp_798) } : code (CEfset ([])) [interface
      #val #[ ADD_ROUND_KEY ] : add_round_key_inp → add_round_key_out ;
      #val #[ AES_ENC_LAST ] : aes_enc_last_inp → aes_enc_last_out ;
      #val #[ ROUNDS_AES ] : rounds_aes_inp → rounds_aes_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_block_cipher_aes : package _ _ _ :=
  (seq_link block_cipher_aes link_rest(
      package_add_round_key,package_aes_enc_last,package_rounds_aes)).
Fail Next Obligation.


Notation "'rotate_word_inp'" :=(
  word_t : choice_type) (in custom pack_type at level 2).
Notation "'rotate_word_out'" :=(
  word_t : choice_type) (in custom pack_type at level 2).
Definition ROTATE_WORD : nat :=
  (811).
Program Definition rotate_word
   : package (fset.fset0) [interface  ] [interface
  #val #[ ROTATE_WORD ] : rotate_word_inp → rotate_word_out ] :=
  (
    [package #def #[ ROTATE_WORD ] (temp_inp : rotate_word_inp) : rotate_word_out { 
    let '(w_801) := temp_inp : word_t in
    ({ code  temp_802 ←
        (array_index (w_801) (usize 1)) ;;
       temp_804 ←
        (array_index (w_801) (usize 2)) ;;
       temp_806 ←
        (array_index (w_801) (usize 3)) ;;
       temp_808 ←
        (array_index (w_801) (usize 0)) ;;
       '(temp_810 : nseq uint8 4) ←
        (array_from_list uint8 [temp_802; temp_804; temp_806; temp_808]) ;;
      @ret (word_t) (temp_810) } : code (fset.fset0) [interface  ] _)
    }]).
Fail Next Obligation.
Program Definition package_rotate_word : package _ _ _ :=
  (rotate_word).
Fail Next Obligation.


Notation "'slice_word_inp'" :=(
  word_t : choice_type) (in custom pack_type at level 2).
Notation "'slice_word_out'" :=(
  word_t : choice_type) (in custom pack_type at level 2).
Definition SLICE_WORD : nat :=
  (839).
Program Definition slice_word
   : package (fset.fset0) [interface  ] [interface
  #val #[ SLICE_WORD ] : slice_word_inp → slice_word_out ] :=
  ([package #def #[ SLICE_WORD ] (temp_inp : slice_word_inp) : slice_word_out { 
    let '(w_813) := temp_inp : word_t in
    ({ code  temp_814 ←
        (array_index (w_813) (usize 0)) ;;
       temp_816 ←
        (declassify_usize_from_uint8 (temp_814)) ;;
       temp_818 ←
        (array_index (sbox_v) (temp_816)) ;;
       temp_820 ←
        (array_index (w_813) (usize 1)) ;;
       temp_822 ←
        (declassify_usize_from_uint8 (temp_820)) ;;
       temp_824 ←
        (array_index (sbox_v) (temp_822)) ;;
       temp_826 ←
        (array_index (w_813) (usize 2)) ;;
       temp_828 ←
        (declassify_usize_from_uint8 (temp_826)) ;;
       temp_830 ←
        (array_index (sbox_v) (temp_828)) ;;
       temp_832 ←
        (array_index (w_813) (usize 3)) ;;
       temp_834 ←
        (declassify_usize_from_uint8 (temp_832)) ;;
       temp_836 ←
        (array_index (sbox_v) (temp_834)) ;;
       '(temp_838 : nseq uint8 4) ←
        (array_from_list uint8 [temp_818; temp_824; temp_830; temp_836]) ;;
      @ret (word_t) (temp_838) } : code (fset.fset0) [interface  ] _)
    }]).
Fail Next Obligation.
Program Definition package_slice_word : package _ _ _ :=
  (slice_word).
Fail Next Obligation.

Definition k_843_loc : ChoiceEqualityLocation :=
  ((word_t ; 851%nat)).
Notation "'aes_keygen_assist_inp'" :=(
  word_t '× uint8 : choice_type) (in custom pack_type at level 2).
Notation "'aes_keygen_assist_out'" :=(
  word_t : choice_type) (in custom pack_type at level 2).
Definition AES_KEYGEN_ASSIST : nat :=
  (852).
Program Definition aes_keygen_assist
   : package (CEfset ([k_843_loc])) [interface
  #val #[ ROTATE_WORD ] : rotate_word_inp → rotate_word_out ;
  #val #[ SLICE_WORD ] : slice_word_inp → slice_word_out ] [interface
  #val #[ AES_KEYGEN_ASSIST ] : aes_keygen_assist_inp → aes_keygen_assist_out
  ] :=
  (
    [package #def #[ AES_KEYGEN_ASSIST ] (temp_inp : aes_keygen_assist_inp) : aes_keygen_assist_out { 
    let '(w_840 , rcon_848) := temp_inp : word_t '× uint8 in
    #import {sig #[ ROTATE_WORD ] : rotate_word_inp → rotate_word_out } as  rotate_word ;;
    let rotate_word := fun x_0 => rotate_word (x_0) in
    #import {sig #[ SLICE_WORD ] : slice_word_inp → slice_word_out } as  slice_word ;;
    let slice_word := fun x_0 => slice_word (x_0) in
    ({ code  '(k_843 : word_t) ←
          ( '(temp_842 : word_t) ←
              (rotate_word (w_840)) ;;
            ret (temp_842)) ;;
        #put k_843_loc := k_843 ;;
       '(k_843 : word_t) ←
          (( '(temp_845 : word_t) ←
                (slice_word (k_843)) ;;
              ret (temp_845))) ;;
        #put k_843_loc := k_843 ;;
      
       '(k_843 : word_t) ←
        ( temp_847 ←
            (array_index (k_843) (usize 0)) ;;
           temp_850 ←
            ((temp_847) .^ (rcon_848)) ;;
          ret (array_upd k_843 (usize 0) (temp_850))) ;;
      
      @ret (word_t) (k_843) } : code (CEfset ([k_843_loc])) [interface
      #val #[ ROTATE_WORD ] : rotate_word_inp → rotate_word_out ;
      #val #[ SLICE_WORD ] : slice_word_inp → slice_word_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_aes_keygen_assist : package _ _ _ :=
  (seq_link aes_keygen_assist link_rest(
      package_rotate_word,package_slice_word)).
Fail Next Obligation.

Definition result_874_loc : ChoiceEqualityLocation :=
  (((result int8 word_t) ; 895%nat)).
Definition k_867_loc : ChoiceEqualityLocation :=
  ((word_t ; 896%nat)).
Notation "'key_expansion_word_inp'" :=(
  word_t '× word_t '× uint_size '× uint_size '× uint_size : choice_type) (in custom pack_type at level 2).
Notation "'key_expansion_word_out'" :=(
  word_result_t : choice_type) (in custom pack_type at level 2).
Definition KEY_EXPANSION_WORD : nat :=
  (897).
Program Definition key_expansion_word
   : package (CEfset ([k_867_loc ; result_874_loc])) [interface
  #val #[ AES_KEYGEN_ASSIST ] : aes_keygen_assist_inp → aes_keygen_assist_out ;
  #val #[ SLICE_WORD ] : slice_word_inp → slice_word_out ] [interface
  #val #[ KEY_EXPANSION_WORD ] : key_expansion_word_inp → key_expansion_word_out
  ] :=
  (
    [package #def #[ KEY_EXPANSION_WORD ] (temp_inp : key_expansion_word_inp) : key_expansion_word_out { 
    let '(
      w0_889 , w1_853 , i_854 , nk_862 , nr_855) := temp_inp : word_t '× word_t '× uint_size '× uint_size '× uint_size in
    #import {sig #[ AES_KEYGEN_ASSIST ] : aes_keygen_assist_inp → aes_keygen_assist_out } as  aes_keygen_assist ;;
    let aes_keygen_assist := fun x_0 x_1 => aes_keygen_assist (x_0,x_1) in
    #import {sig #[ SLICE_WORD ] : slice_word_inp → slice_word_out } as  slice_word ;;
    let slice_word := fun x_0 => slice_word (x_0) in
    ({ code  '(k_867 : word_t) ←
          (ret (w1_853)) ;;
        #put k_867_loc := k_867 ;;
       '(result_874 : (result int8 word_t)) ←
          (ret (@Err word_t int8 (invalid_key_expansion_index_v))) ;;
        #put result_874_loc := result_874 ;;
       '(temp_857 : uint_size) ←
        ((nr_855) .+ (usize 1)) ;;
       '(temp_859 : uint_size) ←
        ((usize 4) .* (temp_857)) ;;
       '(temp_861 : bool_ChoiceEquality) ←
        ((i_854) <.? (temp_859)) ;;
       temp_894 ←
        (if temp_861:bool_ChoiceEquality
          then (({ code  '(temp_864 : uint_size) ←
                ((i_854) %% (nk_862)) ;;
               '(temp_866 : bool_ChoiceEquality) ←
                ((temp_864) =.? (usize 0)) ;;
               '(k_867 : (word_t)) ←
                (if temp_866:bool_ChoiceEquality
                  then (({ code  '(k_867 : word_t) ←
                          (( '(temp_869 : uint_size) ←
                                ((i_854) ./ (nk_862)) ;;
                               temp_871 ←
                                (array_index (rcon_v) (temp_869)) ;;
                               '(temp_873 : word_t) ←
                                (aes_keygen_assist (k_867) (temp_871)) ;;
                              ret (temp_873))) ;;
                        #put k_867_loc := k_867 ;;
                      
                      @ret ((word_t)) (k_867) } : code (CEfset (
                          [k_867_loc ; result_874_loc])) [interface
                      #val #[ AES_KEYGEN_ASSIST ] : aes_keygen_assist_inp → aes_keygen_assist_out
                      ] _))
                  else  (({ code  '(temp_876 : bool_ChoiceEquality) ←
                        ((nk_862) >.? (usize 6)) ;;
                       '(temp_878 : uint_size) ←
                        ((i_854) %% (nk_862)) ;;
                       '(temp_880 : bool_ChoiceEquality) ←
                        ((temp_878) =.? (usize 4)) ;;
                       '(temp_882 : bool_ChoiceEquality) ←
                        ((temp_876) && (temp_880)) ;;
                       '(k_867 : (word_t)) ←
                        (if temp_882:bool_ChoiceEquality
                          then (({ code  '(k_867 : word_t) ←
                                  (( '(temp_884 : word_t) ←
                                        (slice_word (k_867)) ;;
                                      ret (temp_884))) ;;
                                #put k_867_loc := k_867 ;;
                              
                              @ret ((word_t)) (k_867) } : code (CEfset (
                                  [k_867_loc ; result_874_loc])) [interface
                              #val #[ SLICE_WORD ] : slice_word_inp → slice_word_out
                              ] _))
                          else @ret ((word_t)) (k_867)) ;;
                      
                      @ret ((word_t)) (k_867) } : code (CEfset (
                          [k_867_loc ; result_874_loc])) [interface
                      #val #[ SLICE_WORD ] : slice_word_inp → slice_word_out
                      ] _))) ;;
              
               '(k_867 : (word_t)) ←
                (foldi' (usize 0) (usize 4) k_867 (L2 := CEfset (
                        [k_867_loc ; result_874_loc])) (I2 := [interface
                      #val #[ AES_KEYGEN_ASSIST ] : aes_keygen_assist_inp → aes_keygen_assist_out ;
                      #val #[ SLICE_WORD ] : slice_word_inp → slice_word_out
                      ]) (H_loc_incl := _) (H_opsig_incl := _) (fun i_885 k_867 =>
                    ({ code  '(k_867 : word_t) ←
                        ( temp_887 ←
                            (array_index (k_867) (i_885)) ;;
                           temp_890 ←
                            (array_index (w0_889) (i_885)) ;;
                           temp_892 ←
                            ((temp_887) .^ (temp_890)) ;;
                          ret (array_upd k_867 (i_885) (temp_892))) ;;
                      
                      @ret ((word_t)) (k_867) } : code (CEfset (
                          [k_867_loc ; result_874_loc])) [interface  ] _))) ;;
              
               '(result_874 : (result int8 word_t)) ←
                  ((ret (@Ok word_t int8 (k_867)))) ;;
                #put result_874_loc := result_874 ;;
              
              @ret ((word_t '× (result int8 word_t))) (prod_ce(
                  k_867,
                  result_874
                )) } : code (CEfset ([k_867_loc ; result_874_loc])) [interface
              #val #[ AES_KEYGEN_ASSIST ] : aes_keygen_assist_inp → aes_keygen_assist_out ;
              #val #[ SLICE_WORD ] : slice_word_inp → slice_word_out ] _))
          else @ret ((word_t '× (result int8 word_t))) (prod_ce(
              k_867,
              result_874
            ))) ;;
      let '(k_867, result_874) :=
        (temp_894) : (word_t '× (result int8 word_t)) in
      
      @ret ((result int8 word_t)) (result_874) } : code (CEfset (
          [k_867_loc ; result_874_loc])) [interface
      #val #[ AES_KEYGEN_ASSIST ] : aes_keygen_assist_inp → aes_keygen_assist_out ;
      #val #[ SLICE_WORD ] : slice_word_inp → slice_word_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_key_expansion_word : package _ _ _ :=
  (seq_link key_expansion_word link_rest(
      package_aes_keygen_assist,package_slice_word)).
Fail Next Obligation.

Definition key_ex_901_loc : ChoiceEqualityLocation :=
  ((seq uint8 ; 935%nat)).
Notation "'key_expansion_aes_inp'" :=(
  byte_seq '× uint_size '× uint_size '× uint_size '× uint_size '× uint_size : choice_type) (in custom pack_type at level 2).
Notation "'key_expansion_aes_out'" :=(
  byte_seq_result_t : choice_type) (in custom pack_type at level 2).
Definition KEY_EXPANSION_AES : nat :=
  (936).
Program Definition key_expansion_aes
   : package (CEfset ([key_ex_901_loc])) [interface
  #val #[ KEY_EXPANSION_WORD ] : key_expansion_word_inp → key_expansion_word_out
  ] [interface
  #val #[ KEY_EXPANSION_AES ] : key_expansion_aes_inp → key_expansion_aes_out
  ] :=
  (
    [package #def #[ KEY_EXPANSION_AES ] (temp_inp : key_expansion_aes_inp) : key_expansion_aes_out { 
    let '(
      key_902 , nk_924 , nr_925 , key_schedule_length_898 , key_length_905 , iterations_906) := temp_inp : byte_seq '× uint_size '× uint_size '× uint_size '× uint_size '× uint_size in
    #import {sig #[ KEY_EXPANSION_WORD ] : key_expansion_word_inp → key_expansion_word_out } as  key_expansion_word ;;
    let key_expansion_word := fun x_0 x_1 x_2 x_3 x_4 => key_expansion_word (
      x_0,x_1,x_2,x_3,x_4) in
    ({ code  '(key_ex_901 : seq uint8) ←
          ( temp_900 ←
              (seq_new_ (default : uint8) (key_schedule_length_898)) ;;
            ret (temp_900)) ;;
        #put key_ex_901_loc := key_ex_901 ;;
       '(key_ex_901 : seq uint8) ←
          (( '(temp_904 : seq uint8) ←
                (seq_update_start (key_ex_901) (key_902)) ;;
              ret (temp_904))) ;;
        #put key_ex_901_loc := key_ex_901 ;;
      
       '(word_size_908 : uint_size) ←
        (ret (key_length_905)) ;;
      bnd(ChoiceEqualityMonad.result_bind_code int8 , (seq uint8) , _ , CEfset (
          [key_ex_901_loc])) key_ex_901 ⇠
      (foldi_bind_code' (usize 0) (iterations_906) (
          key_ex_901) (fun j_907 key_ex_901 =>
        ({ code  '(i_911 : uint_size) ←
            ( '(temp_910 : uint_size) ←
                ((j_907) .+ (word_size_908)) ;;
              ret (temp_910)) ;;
           '(key_ex_901 : seq uint8) ←
              ((ret (key_ex_901))) ;;
            #put key_ex_901_loc := key_ex_901 ;;
          
          bnd(ChoiceEqualityMonad.result_bind_code int8 , word_t , _ , CEfset (
              [key_ex_901_loc])) word_930 ⇠
          (({ code  '(temp_913 : uint_size) ←
                ((i_911) .- (word_size_908)) ;;
               '(temp_915 : uint_size) ←
                ((usize 4) .* (temp_913)) ;;
               '(temp_917 : word_t) ←
                (array_from_slice (default : uint8) (key_length_v) (
                    key_ex_901) (temp_915) (usize 4)) ;;
               '(temp_919 : uint_size) ←
                ((usize 4) .* (i_911)) ;;
               '(temp_921 : uint_size) ←
                ((temp_919) .- (usize 4)) ;;
               '(temp_923 : word_t) ←
                (array_from_slice (default : uint8) (key_length_v) (
                    key_ex_901) (temp_921) (usize 4)) ;;
               '(temp_927 : word_result_t) ←
                (key_expansion_word (temp_917) (temp_923) (i_911) (nk_924) (
                    nr_925)) ;;
              @ret _ (temp_927) } : code (CEfset ([key_ex_901_loc])) [interface
              #val #[ KEY_EXPANSION_WORD ] : key_expansion_word_inp → key_expansion_word_out
              ] _)) in
          ({ code  '(key_ex_901 : seq uint8) ←
                (( '(temp_929 : uint_size) ←
                      ((usize 4) .* (i_911)) ;;
                     '(temp_932 : seq uint8) ←
                      (array_to_seq (word_930)) ;;
                     '(temp_934 : seq uint8) ←
                      (seq_update (key_ex_901) (temp_929) (temp_932)) ;;
                    ret (temp_934))) ;;
              #put key_ex_901_loc := key_ex_901 ;;
            
            @ret ((result int8 (seq uint8))) (@Ok (seq uint8) int8 (
                key_ex_901)) } : code (CEfset ([key_ex_901_loc])) [interface
            #val #[ KEY_EXPANSION_WORD ] : key_expansion_word_inp → key_expansion_word_out
            ] _) } : code (CEfset ([key_ex_901_loc])) [interface
          #val #[ KEY_EXPANSION_WORD ] : key_expansion_word_inp → key_expansion_word_out
          ] _))) in
      ({ code @ret ((result int8 byte_seq)) (@Ok byte_seq int8 (
            key_ex_901)) } : code (CEfset ([key_ex_901_loc])) [interface
        #val #[ KEY_EXPANSION_WORD ] : key_expansion_word_inp → key_expansion_word_out
        ] _) } : code (CEfset ([key_ex_901_loc])) [interface
      #val #[ KEY_EXPANSION_WORD ] : key_expansion_word_inp → key_expansion_word_out
      ] _)
    }]).
Fail Next Obligation.
Program Definition package_key_expansion_aes : package _ _ _ :=
  (seq_link key_expansion_aes link_rest(package_key_expansion_word)).
Fail Next Obligation.


Notation "'aes_encrypt_block_inp'" :=(
  byte_seq '× block_t '× uint_size '× uint_size '× uint_size '× uint_size '× uint_size : choice_type) (in custom pack_type at level 2).
Notation "'aes_encrypt_block_out'" :=(
  block_result_t : choice_type) (in custom pack_type at level 2).
Definition AES_ENCRYPT_BLOCK : nat :=
  (949).
Program Definition aes_encrypt_block
   : package (CEfset ([])) [interface
  #val #[ BLOCK_CIPHER_AES ] : block_cipher_aes_inp → block_cipher_aes_out ;
  #val #[ KEY_EXPANSION_AES ] : key_expansion_aes_inp → key_expansion_aes_out
  ] [interface
  #val #[ AES_ENCRYPT_BLOCK ] : aes_encrypt_block_inp → aes_encrypt_block_out
  ] :=
  (
    [package #def #[ AES_ENCRYPT_BLOCK ] (temp_inp : aes_encrypt_block_inp) : aes_encrypt_block_out { 
    let '(
      k_937 , input_945 , nk_938 , nr_939 , key_schedule_length_940 , key_length_941 , iterations_942) := temp_inp : byte_seq '× block_t '× uint_size '× uint_size '× uint_size '× uint_size '× uint_size in
    #import {sig #[ BLOCK_CIPHER_AES ] : block_cipher_aes_inp → block_cipher_aes_out } as  block_cipher_aes ;;
    let block_cipher_aes := fun x_0 x_1 x_2 => block_cipher_aes (x_0,x_1,x_2) in
    #import {sig #[ KEY_EXPANSION_AES ] : key_expansion_aes_inp → key_expansion_aes_out } as  key_expansion_aes ;;
    let key_expansion_aes := fun x_0 x_1 x_2 x_3 x_4 x_5 => key_expansion_aes (
      x_0,x_1,x_2,x_3,x_4,x_5) in
    ({ code bnd(
        ChoiceEqualityMonad.result_bind_code int8 , byte_seq , _ , CEfset (
          [])) key_ex_946 ⇠
      (({ code  '(temp_944 : byte_seq_result_t) ←
            (key_expansion_aes (k_937) (nk_938) (nr_939) (
                key_schedule_length_940) (key_length_941) (iterations_942)) ;;
          @ret _ (temp_944) } : code (CEfset ([])) [interface
          #val #[ KEY_EXPANSION_AES ] : key_expansion_aes_inp → key_expansion_aes_out
          ] _)) in
      ({ code  '(temp_948 : block_t) ←
          (block_cipher_aes (input_945) (key_ex_946) (nr_939)) ;;
        @ret ((result int8 block_t)) (@Ok block_t int8 (temp_948)) } : code (
          CEfset ([])) [interface
        #val #[ BLOCK_CIPHER_AES ] : block_cipher_aes_inp → block_cipher_aes_out ;
        #val #[ KEY_EXPANSION_AES ] : key_expansion_aes_inp → key_expansion_aes_out
        ] _) } : code (CEfset ([])) [interface
      #val #[ BLOCK_CIPHER_AES ] : block_cipher_aes_inp → block_cipher_aes_out ;
      #val #[ KEY_EXPANSION_AES ] : key_expansion_aes_inp → key_expansion_aes_out
      ] _)
    }]).
Fail Next Obligation.
Program Definition package_aes_encrypt_block : package _ _ _ :=
  (seq_link aes_encrypt_block link_rest(
      package_block_cipher_aes,package_key_expansion_aes)).
Fail Next Obligation.


Notation "'aes128_encrypt_block_inp'" :=(
  key128_t '× block_t : choice_type) (in custom pack_type at level 2).
Notation "'aes128_encrypt_block_out'" :=(
  block_t : choice_type) (in custom pack_type at level 2).
Definition AES128_ENCRYPT_BLOCK : nat :=
  (960).
Program Definition aes128_encrypt_block
   : package (CEfset ([])) [interface
  #val #[ AES_ENCRYPT_BLOCK ] : aes_encrypt_block_inp → aes_encrypt_block_out
  ] [interface
  #val #[ AES128_ENCRYPT_BLOCK ] : aes128_encrypt_block_inp → aes128_encrypt_block_out
  ] :=
  (
    [package #def #[ AES128_ENCRYPT_BLOCK ] (temp_inp : aes128_encrypt_block_inp) : aes128_encrypt_block_out { 
    let '(k_950 , input_955) := temp_inp : key128_t '× block_t in
    #import {sig #[ AES_ENCRYPT_BLOCK ] : aes_encrypt_block_inp → aes_encrypt_block_out } as  aes_encrypt_block ;;
    let aes_encrypt_block := fun x_0 x_1 x_2 x_3 x_4 x_5 x_6 => aes_encrypt_block (
      x_0,x_1,x_2,x_3,x_4,x_5,x_6) in
    ({ code  '(temp_952 : seq uint8) ←
        (array_to_seq (k_950)) ;;
       '(temp_954 : byte_seq) ←
        (seq_from_seq (temp_952)) ;;
       '(temp_957 : block_result_t) ←
        (aes_encrypt_block (temp_954) (input_955) (key_length_v) (rounds_v) (
            key_schedule_length_v) (key_length_v) (iterations_v)) ;;
       temp_959 ←
        (result_unwrap (temp_957)) ;;
      @ret (block_t) (temp_959) } : code (CEfset ([])) [interface
      #val #[ AES_ENCRYPT_BLOCK ] : aes_encrypt_block_inp → aes_encrypt_block_out
      ] _)
    }]).
Fail Next Obligation.
Program Definition package_aes128_encrypt_block : package _ _ _ :=
  (seq_link aes128_encrypt_block link_rest(package_aes_encrypt_block)).
Fail Next Obligation.

Definition input_963_loc : ChoiceEqualityLocation :=
  ((block_t ; 984%nat)).
Notation "'aes_ctr_key_block_inp'" :=(
  byte_seq '× aes_nonce_t '× uint32 '× uint_size '× uint_size '× uint_size '× uint_size '× uint_size : choice_type) (in custom pack_type at level 2).
Notation "'aes_ctr_key_block_out'" :=(
  block_result_t : choice_type) (in custom pack_type at level 2).
Definition AES_CTR_KEY_BLOCK : nat :=
  (985).
Program Definition aes_ctr_key_block
   : package (CEfset ([input_963_loc])) [interface
  #val #[ AES_ENCRYPT_BLOCK ] : aes_encrypt_block_inp → aes_encrypt_block_out
  ] [interface
  #val #[ AES_CTR_KEY_BLOCK ] : aes_ctr_key_block_inp → aes_ctr_key_block_out
  ] :=
  (
    [package #def #[ AES_CTR_KEY_BLOCK ] (temp_inp : aes_ctr_key_block_inp) : aes_ctr_key_block_out { 
    let '(
      k_976 , n_964 , c_969 , nk_977 , nr_978 , key_schedule_length_979 , key_length_980 , iterations_981) := temp_inp : byte_seq '× aes_nonce_t '× uint32 '× uint_size '× uint_size '× uint_size '× uint_size '× uint_size in
    #import {sig #[ AES_ENCRYPT_BLOCK ] : aes_encrypt_block_inp → aes_encrypt_block_out } as  aes_encrypt_block ;;
    let aes_encrypt_block := fun x_0 x_1 x_2 x_3 x_4 x_5 x_6 => aes_encrypt_block (
      x_0,x_1,x_2,x_3,x_4,x_5,x_6) in
    ({ code  '(input_963 : block_t) ←
          ( '(temp_962 : block_t) ←
              (array_new_ (default : uint8) (blocksize_v)) ;;
            ret (temp_962)) ;;
        #put input_963_loc := input_963 ;;
       '(input_963 : block_t) ←
          (( '(temp_966 : seq uint8) ←
                (array_to_seq (n_964)) ;;
               '(temp_968 : block_t) ←
                (array_update (input_963) (usize 0) (temp_966)) ;;
              ret (temp_968))) ;;
        #put input_963_loc := input_963 ;;
      
       '(input_963 : block_t) ←
          (( '(temp_971 : uint32_word_t) ←
                (uint32_to_be_bytes (c_969)) ;;
               '(temp_973 : seq uint8) ←
                (array_to_seq (temp_971)) ;;
               '(temp_975 : block_t) ←
                (array_update (input_963) (usize 12) (temp_973)) ;;
              ret (temp_975))) ;;
        #put input_963_loc := input_963 ;;
      
       '(temp_983 : block_result_t) ←
        (aes_encrypt_block (k_976) (input_963) (nk_977) (nr_978) (
            key_schedule_length_979) (key_length_980) (iterations_981)) ;;
      @ret (block_result_t) (temp_983) } : code (CEfset (
          [input_963_loc])) [interface
      #val #[ AES_ENCRYPT_BLOCK ] : aes_encrypt_block_inp → aes_encrypt_block_out
      ] _)
    }]).
Fail Next Obligation.
Program Definition package_aes_ctr_key_block : package _ _ _ :=
  (seq_link aes_ctr_key_block link_rest(package_aes_encrypt_block)).
Fail Next Obligation.

Definition out_989_loc : ChoiceEqualityLocation :=
  ((block_t ; 996%nat)).
Notation "'xor_block_inp'" :=(
  block_t '× block_t : choice_type) (in custom pack_type at level 2).
Notation "'xor_block_out'" :=(
  block_t : choice_type) (in custom pack_type at level 2).
Definition XOR_BLOCK : nat :=
  (997).
Program Definition xor_block
   : package (CEfset ([out_989_loc])) [interface  ] [interface
  #val #[ XOR_BLOCK ] : xor_block_inp → xor_block_out ] :=
  ([package #def #[ XOR_BLOCK ] (temp_inp : xor_block_inp) : xor_block_out { 
    let '(block_986 , key_block_992) := temp_inp : block_t '× block_t in
    ({ code  '(out_989 : block_t) ←
          (ret (block_986)) ;;
        #put out_989_loc := out_989 ;;
       '(out_989 : (block_t)) ←
        (foldi' (usize 0) (blocksize_v) out_989 (L2 := CEfset ([out_989_loc])) (
              I2 := [interface 
              ]) (H_loc_incl := _) (H_opsig_incl := _) (fun i_987 out_989 =>
            ({ code  '(out_989 : block_t) ←
                ( temp_990 ←
                    (array_index (out_989) (i_987)) ;;
                   temp_993 ←
                    (array_index (key_block_992) (i_987)) ;;
                   temp_995 ←
                    ((temp_990) .^ (temp_993)) ;;
                  ret (array_upd out_989 (i_987) (temp_995))) ;;
              
              @ret ((block_t)) (out_989) } : code (CEfset (
                  [out_989_loc])) [interface  ] _))) ;;
      
      @ret (block_t) (out_989) } : code (CEfset ([out_989_loc])) [interface 
      ] _)
    }]).
Fail Next Obligation.
Program Definition package_xor_block : package _ _ _ :=
  (xor_block).
Fail Next Obligation.

Definition ctr_1012_loc : ChoiceEqualityLocation :=
  ((uint32 ; 1057%nat)).
Definition blocks_out_1020_loc : ChoiceEqualityLocation :=
  ((seq uint8 ; 1058%nat)).
Notation "'aes_counter_mode_inp'" :=(
  byte_seq '× aes_nonce_t '× uint32 '× byte_seq '× uint_size '× uint_size '× uint_size '× uint_size '× uint_size : choice_type) (in custom pack_type at level 2).
Notation "'aes_counter_mode_out'" :=(
  byte_seq_result_t : choice_type) (in custom pack_type at level 2).
Definition AES_COUNTER_MODE : nat :=
  (1059).
Program Definition aes_counter_mode
   : package (CEfset ([ctr_1012_loc ; blocks_out_1020_loc])) [interface
  #val #[ AES_CTR_KEY_BLOCK ] : aes_ctr_key_block_inp → aes_ctr_key_block_out ;
  #val #[ XOR_BLOCK ] : xor_block_inp → xor_block_out ] [interface
  #val #[ AES_COUNTER_MODE ] : aes_counter_mode_inp → aes_counter_mode_out
  ] :=
  (
    [package #def #[ AES_COUNTER_MODE ] (temp_inp : aes_counter_mode_inp) : aes_counter_mode_out { 
    let '(
      key_1010 , nonce_1011 , counter_998 , msg_999 , nk_1013 , nr_1014 , key_schedule_length_1015 , key_length_1016 , iterations_1017) := temp_inp : byte_seq '× aes_nonce_t '× uint32 '× byte_seq '× uint_size '× uint_size '× uint_size '× uint_size '× uint_size in
    #import {sig #[ AES_CTR_KEY_BLOCK ] : aes_ctr_key_block_inp → aes_ctr_key_block_out } as  aes_ctr_key_block ;;
    let aes_ctr_key_block := fun x_0 x_1 x_2 x_3 x_4 x_5 x_6 x_7 => aes_ctr_key_block (
      x_0,x_1,x_2,x_3,x_4,x_5,x_6,x_7) in
    #import {sig #[ XOR_BLOCK ] : xor_block_inp → xor_block_out } as  xor_block ;;
    let xor_block := fun x_0 x_1 => xor_block (x_0,x_1) in
    ({ code  '(ctr_1012 : uint32) ←
          (ret (counter_998)) ;;
        #put ctr_1012_loc := ctr_1012 ;;
       '(blocks_out_1020 : seq uint8) ←
          ( '(temp_1001 : uint_size) ←
              (seq_len (msg_999)) ;;
             temp_1003 ←
              (seq_new_ (default : uint8) (temp_1001)) ;;
            ret (temp_1003)) ;;
        #put blocks_out_1020_loc := blocks_out_1020 ;;
       '(n_blocks_1006 : uint_size) ←
        ( '(temp_1005 : uint_size) ←
            (seq_num_exact_chunks (msg_999) (blocksize_v)) ;;
          ret (temp_1005)) ;;
      bnd(ChoiceEqualityMonad.result_bind_code int8 , (uint32 '× seq uint8
        ) , _ , CEfset ([ctr_1012_loc ; blocks_out_1020_loc])) '(
        ctr_1012,
        blocks_out_1020
      ) ⇠
      (foldi_bind_code' (usize 0) (n_blocks_1006) (prod_ce(
            ctr_1012,
            blocks_out_1020
          )) (fun i_1007 '(ctr_1012, blocks_out_1020) =>
        ({ code  '(msg_block_1021 : seq uint8) ←
            ( '(temp_1009 : byte_seq) ←
                (seq_get_exact_chunk (msg_999) (blocksize_v) (i_1007)) ;;
              ret (temp_1009)) ;;
          bnd(ChoiceEqualityMonad.result_bind_code int8 , block_t , _ , CEfset (
              [ctr_1012_loc ; blocks_out_1020_loc])) key_block_1024 ⇠
          (({ code  '(temp_1019 : block_result_t) ←
                (aes_ctr_key_block (key_1010) (nonce_1011) (ctr_1012) (
                    nk_1013) (nr_1014) (key_schedule_length_1015) (
                    key_length_1016) (iterations_1017)) ;;
              @ret _ (temp_1019) } : code (CEfset (
                  [ctr_1012_loc ; blocks_out_1020_loc])) [interface
              #val #[ AES_CTR_KEY_BLOCK ] : aes_ctr_key_block_inp → aes_ctr_key_block_out
              ] _)) in
          ({ code  '(blocks_out_1020 : seq uint8) ←
                (( '(temp_1023 : block_t) ←
                      (array_from_seq (blocksize_v) (msg_block_1021)) ;;
                     '(temp_1026 : block_t) ←
                      (xor_block (temp_1023) (key_block_1024)) ;;
                     '(temp_1028 : seq uint8) ←
                      (array_to_seq (temp_1026)) ;;
                     '(temp_1030 : seq uint8) ←
                      (seq_set_chunk (blocks_out_1020) (blocksize_v) (i_1007) (
                          temp_1028)) ;;
                    ret (temp_1030))) ;;
              #put blocks_out_1020_loc := blocks_out_1020 ;;
            
             '(ctr_1012 : uint32) ←
                (( '(temp_1032 : int32) ←
                      (secret (@repr U32 1)) ;;
                     '(temp_1034 : uint32) ←
                      ((ctr_1012) .+ (temp_1032)) ;;
                    ret (temp_1034))) ;;
              #put ctr_1012_loc := ctr_1012 ;;
            
            @ret ((result int8 (uint32 '× seq uint8))) (@Ok (
                uint32 '×
                seq uint8
              ) int8 (prod_ce(ctr_1012, blocks_out_1020))) } : code (CEfset (
                [ctr_1012_loc ; blocks_out_1020_loc])) [interface
            #val #[ AES_CTR_KEY_BLOCK ] : aes_ctr_key_block_inp → aes_ctr_key_block_out ;
            #val #[ XOR_BLOCK ] : xor_block_inp → xor_block_out
            ] _) } : code (CEfset (
              [ctr_1012_loc ; blocks_out_1020_loc])) [interface
          #val #[ AES_CTR_KEY_BLOCK ] : aes_ctr_key_block_inp → aes_ctr_key_block_out ;
          #val #[ XOR_BLOCK ] : xor_block_inp → xor_block_out ] _))) in
      ({ code  '(last_block_1037 : seq uint8) ←
          ( '(temp_1036 : byte_seq) ←
              (seq_get_remainder_chunk (msg_999) (blocksize_v)) ;;
            ret (temp_1036)) ;;
         '(last_block_len_1040 : uint_size) ←
          ( '(temp_1039 : uint_size) ←
              (seq_len (last_block_1037)) ;;
            ret (temp_1039)) ;;
         '(temp_1042 : bool_ChoiceEquality) ←
          ((last_block_len_1040) !=.? (usize 0)) ;;
        bnd(ChoiceEqualityMonad.result_bind_code int8 , (seq uint8
          ) , _ , CEfset (
            [ctr_1012_loc ; blocks_out_1020_loc])) 'blocks_out_1020 ⇠
        (if temp_1042 : bool_ChoiceEquality
          then ({ code ({ code  '(last_block_1049 : block_t) ←
                ( '(temp_1044 : block_t) ←
                    (array_new_ (default : uint8) (blocksize_v)) ;;
                   '(temp_1046 : block_t) ←
                    (array_update_start (temp_1044) (last_block_1037)) ;;
                  ret (temp_1046)) ;;
              bnd(
                ChoiceEqualityMonad.result_bind_code int8 , block_t , _ , CEfset (
                  [ctr_1012_loc ; blocks_out_1020_loc])) key_block_1050 ⇠
              (({ code  '(temp_1048 : block_result_t) ←
                    (aes_ctr_key_block (key_1010) (nonce_1011) (ctr_1012) (
                        nk_1013) (nr_1014) (key_schedule_length_1015) (
                        key_length_1016) (iterations_1017)) ;;
                  @ret _ (temp_1048) } : code (CEfset (
                      [ctr_1012_loc ; blocks_out_1020_loc])) [interface
                  #val #[ AES_CTR_KEY_BLOCK ] : aes_ctr_key_block_inp → aes_ctr_key_block_out
                  ] _)) in
              ({ code  '(blocks_out_1020 : seq uint8) ←
                    (( '(temp_1052 : block_t) ←
                          (xor_block (last_block_1049) (key_block_1050)) ;;
                         '(temp_1054 : seq uint8) ←
                          (array_slice_range (temp_1052) (prod_ce(
                                usize 0,
                                last_block_len_1040
                              ))) ;;
                         '(temp_1056 : seq uint8) ←
                          (seq_set_chunk (blocks_out_1020) (blocksize_v) (
                              n_blocks_1006) (temp_1054)) ;;
                        ret (temp_1056))) ;;
                  #put blocks_out_1020_loc := blocks_out_1020 ;;
                
                @ret ((result int8 (seq uint8))) (@Ok (seq uint8) int8 (
                    blocks_out_1020)) } : code (CEfset (
                    [ctr_1012_loc ; blocks_out_1020_loc])) [interface
                #val #[ AES_CTR_KEY_BLOCK ] : aes_ctr_key_block_inp → aes_ctr_key_block_out ;
                #val #[ XOR_BLOCK ] : xor_block_inp → xor_block_out
                ] _) } : code (CEfset (
                  [ctr_1012_loc ; blocks_out_1020_loc])) [interface
              #val #[ AES_CTR_KEY_BLOCK ] : aes_ctr_key_block_inp → aes_ctr_key_block_out ;
              #val #[ XOR_BLOCK ] : xor_block_inp → xor_block_out
              ] _) } : code (CEfset (
                [ctr_1012_loc ; blocks_out_1020_loc])) [interface
            #val #[ AES_CTR_KEY_BLOCK ] : aes_ctr_key_block_inp → aes_ctr_key_block_out ;
            #val #[ XOR_BLOCK ] : xor_block_inp → xor_block_out ] _)
          else ({ code @ret ((result int8 (seq uint8))) (@Ok (seq uint8) int8 (
                blocks_out_1020)) } : code _ _ _) ) in
        ({ code @ret ((result int8 byte_seq)) (@Ok byte_seq int8 (
              blocks_out_1020)) } : code (CEfset (
              [ctr_1012_loc ; blocks_out_1020_loc])) [interface
          #val #[ AES_CTR_KEY_BLOCK ] : aes_ctr_key_block_inp → aes_ctr_key_block_out ;
          #val #[ XOR_BLOCK ] : xor_block_inp → xor_block_out ] _) } : code (
          CEfset ([ctr_1012_loc ; blocks_out_1020_loc])) [interface
        #val #[ AES_CTR_KEY_BLOCK ] : aes_ctr_key_block_inp → aes_ctr_key_block_out ;
        #val #[ XOR_BLOCK ] : xor_block_inp → xor_block_out ] _) } : code (
        CEfset ([ctr_1012_loc ; blocks_out_1020_loc])) [interface
      #val #[ AES_CTR_KEY_BLOCK ] : aes_ctr_key_block_inp → aes_ctr_key_block_out ;
      #val #[ XOR_BLOCK ] : xor_block_inp → xor_block_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_aes_counter_mode : package _ _ _ :=
  (seq_link aes_counter_mode link_rest(
      package_aes_ctr_key_block,package_xor_block)).
Fail Next Obligation.


Notation "'aes128_encrypt_inp'" :=(
  key128_t '× aes_nonce_t '× uint32 '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'aes128_encrypt_out'" :=(
  byte_seq : choice_type) (in custom pack_type at level 2).
Definition AES128_ENCRYPT : nat :=
  (1072).
Program Definition aes128_encrypt
   : package (CEfset ([])) [interface
  #val #[ AES_COUNTER_MODE ] : aes_counter_mode_inp → aes_counter_mode_out
  ] [interface
  #val #[ AES128_ENCRYPT ] : aes128_encrypt_inp → aes128_encrypt_out ] :=
  (
    [package #def #[ AES128_ENCRYPT ] (temp_inp : aes128_encrypt_inp) : aes128_encrypt_out { 
    let '(
      key_1060 , nonce_1065 , counter_1066 , msg_1067) := temp_inp : key128_t '× aes_nonce_t '× uint32 '× byte_seq in
    #import {sig #[ AES_COUNTER_MODE ] : aes_counter_mode_inp → aes_counter_mode_out } as  aes_counter_mode ;;
    let aes_counter_mode := fun x_0 x_1 x_2 x_3 x_4 x_5 x_6 x_7 x_8 => aes_counter_mode (
      x_0,x_1,x_2,x_3,x_4,x_5,x_6,x_7,x_8) in
    ({ code  '(temp_1062 : seq uint8) ←
        (array_to_seq (key_1060)) ;;
       '(temp_1064 : byte_seq) ←
        (seq_from_seq (temp_1062)) ;;
       '(temp_1069 : byte_seq_result_t) ←
        (aes_counter_mode (temp_1064) (nonce_1065) (counter_1066) (msg_1067) (
            key_length_v) (rounds_v) (key_schedule_length_v) (key_length_v) (
            iterations_v)) ;;
       temp_1071 ←
        (result_unwrap (temp_1069)) ;;
      @ret (seq uint8) (temp_1071) } : code (CEfset ([])) [interface
      #val #[ AES_COUNTER_MODE ] : aes_counter_mode_inp → aes_counter_mode_out
      ] _)
    }]).
Fail Next Obligation.
Program Definition package_aes128_encrypt : package _ _ _ :=
  (seq_link aes128_encrypt link_rest(package_aes_counter_mode)).
Fail Next Obligation.


Notation "'aes128_decrypt_inp'" :=(
  key128_t '× aes_nonce_t '× uint32 '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'aes128_decrypt_out'" :=(
  byte_seq : choice_type) (in custom pack_type at level 2).
Definition AES128_DECRYPT : nat :=
  (1085).
Program Definition aes128_decrypt
   : package (CEfset ([])) [interface
  #val #[ AES_COUNTER_MODE ] : aes_counter_mode_inp → aes_counter_mode_out
  ] [interface
  #val #[ AES128_DECRYPT ] : aes128_decrypt_inp → aes128_decrypt_out ] :=
  (
    [package #def #[ AES128_DECRYPT ] (temp_inp : aes128_decrypt_inp) : aes128_decrypt_out { 
    let '(
      key_1073 , nonce_1078 , counter_1079 , ctxt_1080) := temp_inp : key128_t '× aes_nonce_t '× uint32 '× byte_seq in
    #import {sig #[ AES_COUNTER_MODE ] : aes_counter_mode_inp → aes_counter_mode_out } as  aes_counter_mode ;;
    let aes_counter_mode := fun x_0 x_1 x_2 x_3 x_4 x_5 x_6 x_7 x_8 => aes_counter_mode (
      x_0,x_1,x_2,x_3,x_4,x_5,x_6,x_7,x_8) in
    ({ code  '(temp_1075 : seq uint8) ←
        (array_to_seq (key_1073)) ;;
       '(temp_1077 : byte_seq) ←
        (seq_from_seq (temp_1075)) ;;
       '(temp_1082 : byte_seq_result_t) ←
        (aes_counter_mode (temp_1077) (nonce_1078) (counter_1079) (ctxt_1080) (
            key_length_v) (rounds_v) (key_schedule_length_v) (key_length_v) (
            iterations_v)) ;;
       temp_1084 ←
        (result_unwrap (temp_1082)) ;;
      @ret (seq uint8) (temp_1084) } : code (CEfset ([])) [interface
      #val #[ AES_COUNTER_MODE ] : aes_counter_mode_inp → aes_counter_mode_out
      ] _)
    }]).
Fail Next Obligation.
Program Definition package_aes128_decrypt : package _ _ _ :=
  (seq_link aes128_decrypt link_rest(package_aes_counter_mode)).
Fail Next Obligation.

