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

Require Import Hacspec_Sha512.

Definition field_canvas_t  :=
  (nseq (int8) (32)).
Definition ed25519_field_element_t  :=
  (nat_mod 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed).

Definition scalar_canvas_t  :=
  (nseq (int8) (32)).
Definition scalar_t  :=
  (nat_mod 0x1000000000000000000000000000000014def9dea2f79cd65812631a5cf5d3ed).

Definition big_scalar_canvas_t  :=
  (nseq (int8) (64)).
Definition big_scalar_t  :=
  (nat_mod 0x1000000000000000000000000000000014def9dea2f79cd65812631a5cf5d3ed).

Definition big_integer_canvas_t  :=
  (nseq (int8) (32)).
Definition big_integer_t  :=
  (nat_mod 0x8000000000000000000000000000000080000000000000000000000000000000).

Notation "'ed_point_t'" := ((
  ed25519_field_element_t '×
  ed25519_field_element_t '×
  ed25519_field_element_t '×
  ed25519_field_element_t
)) : hacspec_scope.

Definition compressed_ed_point_t  :=
  ( nseq (uint8) (usize 32)).

Definition serialized_scalar_t  :=
  ( nseq (uint8) (usize 32)).

Definition signature_t  :=
  ( nseq (uint8) (usize 64)).

Notation "'public_key_t'" := (compressed_ed_point_t) : hacspec_scope.

Notation "'secret_key_t'" := (serialized_scalar_t) : hacspec_scope.

Definition error_t : ChoiceEquality :=
  (
    unit_ChoiceEquality '+ unit_ChoiceEquality '+ unit_ChoiceEquality '+ unit_ChoiceEquality '+ unit_ChoiceEquality '+ unit_ChoiceEquality).
Definition InvalidPublickey : error_t :=
  (inl (inl (inl (inl (inl tt))))).
Definition InvalidSignature : error_t :=
  (inl (inl (inl (inl (inr tt))))).
Definition InvalidS : error_t :=
  (inl (inl (inl (inr tt)))).
Definition InvalidR : error_t :=
  (inl (inl (inr tt))).
Definition SmallOrderPoint : error_t :=
  (inl (inr tt)).
Definition NotEnoughRandomness : error_t :=
  (inr tt).

Notation "'verify_result_t'" := ((
  result error_t unit_ChoiceEquality)) : hacspec_scope.

Definition base_v : (compressed_ed_point_t) :=
  (let temp_12269 : int8 :=
      (secret (@repr U8 88)) in
    let temp_12271 : int8 :=
      (secret (@repr U8 102)) in
    let temp_12273 : int8 :=
      (secret (@repr U8 102)) in
    let temp_12275 : int8 :=
      (secret (@repr U8 102)) in
    let temp_12277 : int8 :=
      (secret (@repr U8 102)) in
    let temp_12279 : int8 :=
      (secret (@repr U8 102)) in
    let temp_12281 : int8 :=
      (secret (@repr U8 102)) in
    let temp_12283 : int8 :=
      (secret (@repr U8 102)) in
    let temp_12285 : int8 :=
      (secret (@repr U8 102)) in
    let temp_12287 : int8 :=
      (secret (@repr U8 102)) in
    let temp_12289 : int8 :=
      (secret (@repr U8 102)) in
    let temp_12291 : int8 :=
      (secret (@repr U8 102)) in
    let temp_12293 : int8 :=
      (secret (@repr U8 102)) in
    let temp_12295 : int8 :=
      (secret (@repr U8 102)) in
    let temp_12297 : int8 :=
      (secret (@repr U8 102)) in
    let temp_12299 : int8 :=
      (secret (@repr U8 102)) in
    let temp_12301 : int8 :=
      (secret (@repr U8 102)) in
    let temp_12303 : int8 :=
      (secret (@repr U8 102)) in
    let temp_12305 : int8 :=
      (secret (@repr U8 102)) in
    let temp_12307 : int8 :=
      (secret (@repr U8 102)) in
    let temp_12309 : int8 :=
      (secret (@repr U8 102)) in
    let temp_12311 : int8 :=
      (secret (@repr U8 102)) in
    let temp_12313 : int8 :=
      (secret (@repr U8 102)) in
    let temp_12315 : int8 :=
      (secret (@repr U8 102)) in
    let temp_12317 : int8 :=
      (secret (@repr U8 102)) in
    let temp_12319 : int8 :=
      (secret (@repr U8 102)) in
    let temp_12321 : int8 :=
      (secret (@repr U8 102)) in
    let temp_12323 : int8 :=
      (secret (@repr U8 102)) in
    let temp_12325 : int8 :=
      (secret (@repr U8 102)) in
    let temp_12327 : int8 :=
      (secret (@repr U8 102)) in
    let temp_12329 : int8 :=
      (secret (@repr U8 102)) in
    let temp_12331 : int8 :=
      (secret (@repr U8 102)) in
    let temp_12333 : nseq uint8 32 :=
      (array_from_list uint8 [
          temp_12269;
          temp_12271;
          temp_12273;
          temp_12275;
          temp_12277;
          temp_12279;
          temp_12281;
          temp_12283;
          temp_12285;
          temp_12287;
          temp_12289;
          temp_12291;
          temp_12293;
          temp_12295;
          temp_12297;
          temp_12299;
          temp_12301;
          temp_12303;
          temp_12305;
          temp_12307;
          temp_12309;
          temp_12311;
          temp_12313;
          temp_12315;
          temp_12317;
          temp_12319;
          temp_12321;
          temp_12323;
          temp_12325;
          temp_12327;
          temp_12329;
          temp_12331
        ]) in
    (temp_12333)).

Definition constant_p_v : (serialized_scalar_t) :=
  (let temp_12335 : int8 :=
      (secret (@repr U8 237)) in
    let temp_12337 : int8 :=
      (secret (@repr U8 255)) in
    let temp_12339 : int8 :=
      (secret (@repr U8 255)) in
    let temp_12341 : int8 :=
      (secret (@repr U8 255)) in
    let temp_12343 : int8 :=
      (secret (@repr U8 255)) in
    let temp_12345 : int8 :=
      (secret (@repr U8 255)) in
    let temp_12347 : int8 :=
      (secret (@repr U8 255)) in
    let temp_12349 : int8 :=
      (secret (@repr U8 255)) in
    let temp_12351 : int8 :=
      (secret (@repr U8 255)) in
    let temp_12353 : int8 :=
      (secret (@repr U8 255)) in
    let temp_12355 : int8 :=
      (secret (@repr U8 255)) in
    let temp_12357 : int8 :=
      (secret (@repr U8 255)) in
    let temp_12359 : int8 :=
      (secret (@repr U8 255)) in
    let temp_12361 : int8 :=
      (secret (@repr U8 255)) in
    let temp_12363 : int8 :=
      (secret (@repr U8 255)) in
    let temp_12365 : int8 :=
      (secret (@repr U8 255)) in
    let temp_12367 : int8 :=
      (secret (@repr U8 255)) in
    let temp_12369 : int8 :=
      (secret (@repr U8 255)) in
    let temp_12371 : int8 :=
      (secret (@repr U8 255)) in
    let temp_12373 : int8 :=
      (secret (@repr U8 255)) in
    let temp_12375 : int8 :=
      (secret (@repr U8 255)) in
    let temp_12377 : int8 :=
      (secret (@repr U8 255)) in
    let temp_12379 : int8 :=
      (secret (@repr U8 255)) in
    let temp_12381 : int8 :=
      (secret (@repr U8 255)) in
    let temp_12383 : int8 :=
      (secret (@repr U8 255)) in
    let temp_12385 : int8 :=
      (secret (@repr U8 255)) in
    let temp_12387 : int8 :=
      (secret (@repr U8 255)) in
    let temp_12389 : int8 :=
      (secret (@repr U8 255)) in
    let temp_12391 : int8 :=
      (secret (@repr U8 255)) in
    let temp_12393 : int8 :=
      (secret (@repr U8 255)) in
    let temp_12395 : int8 :=
      (secret (@repr U8 255)) in
    let temp_12397 : int8 :=
      (secret (@repr U8 127)) in
    let temp_12399 : nseq uint8 32 :=
      (array_from_list uint8 [
          temp_12335;
          temp_12337;
          temp_12339;
          temp_12341;
          temp_12343;
          temp_12345;
          temp_12347;
          temp_12349;
          temp_12351;
          temp_12353;
          temp_12355;
          temp_12357;
          temp_12359;
          temp_12361;
          temp_12363;
          temp_12365;
          temp_12367;
          temp_12369;
          temp_12371;
          temp_12373;
          temp_12375;
          temp_12377;
          temp_12379;
          temp_12381;
          temp_12383;
          temp_12385;
          temp_12387;
          temp_12389;
          temp_12391;
          temp_12393;
          temp_12395;
          temp_12397
        ]) in
    (temp_12399)).

Definition constant_l_v : (serialized_scalar_t) :=
  (let temp_12401 : int8 :=
      (secret (@repr U8 237)) in
    let temp_12403 : int8 :=
      (secret (@repr U8 211)) in
    let temp_12405 : int8 :=
      (secret (@repr U8 245)) in
    let temp_12407 : int8 :=
      (secret (@repr U8 92)) in
    let temp_12409 : int8 :=
      (secret (@repr U8 26)) in
    let temp_12411 : int8 :=
      (secret (@repr U8 99)) in
    let temp_12413 : int8 :=
      (secret (@repr U8 18)) in
    let temp_12415 : int8 :=
      (secret (@repr U8 88)) in
    let temp_12417 : int8 :=
      (secret (@repr U8 214)) in
    let temp_12419 : int8 :=
      (secret (@repr U8 156)) in
    let temp_12421 : int8 :=
      (secret (@repr U8 247)) in
    let temp_12423 : int8 :=
      (secret (@repr U8 162)) in
    let temp_12425 : int8 :=
      (secret (@repr U8 222)) in
    let temp_12427 : int8 :=
      (secret (@repr U8 249)) in
    let temp_12429 : int8 :=
      (secret (@repr U8 222)) in
    let temp_12431 : int8 :=
      (secret (@repr U8 20)) in
    let temp_12433 : int8 :=
      (secret (@repr U8 0)) in
    let temp_12435 : int8 :=
      (secret (@repr U8 0)) in
    let temp_12437 : int8 :=
      (secret (@repr U8 0)) in
    let temp_12439 : int8 :=
      (secret (@repr U8 0)) in
    let temp_12441 : int8 :=
      (secret (@repr U8 0)) in
    let temp_12443 : int8 :=
      (secret (@repr U8 0)) in
    let temp_12445 : int8 :=
      (secret (@repr U8 0)) in
    let temp_12447 : int8 :=
      (secret (@repr U8 0)) in
    let temp_12449 : int8 :=
      (secret (@repr U8 0)) in
    let temp_12451 : int8 :=
      (secret (@repr U8 0)) in
    let temp_12453 : int8 :=
      (secret (@repr U8 0)) in
    let temp_12455 : int8 :=
      (secret (@repr U8 0)) in
    let temp_12457 : int8 :=
      (secret (@repr U8 0)) in
    let temp_12459 : int8 :=
      (secret (@repr U8 0)) in
    let temp_12461 : int8 :=
      (secret (@repr U8 0)) in
    let temp_12463 : int8 :=
      (secret (@repr U8 16)) in
    let temp_12465 : nseq uint8 32 :=
      (array_from_list uint8 [
          temp_12401;
          temp_12403;
          temp_12405;
          temp_12407;
          temp_12409;
          temp_12411;
          temp_12413;
          temp_12415;
          temp_12417;
          temp_12419;
          temp_12421;
          temp_12423;
          temp_12425;
          temp_12427;
          temp_12429;
          temp_12431;
          temp_12433;
          temp_12435;
          temp_12437;
          temp_12439;
          temp_12441;
          temp_12443;
          temp_12445;
          temp_12447;
          temp_12449;
          temp_12451;
          temp_12453;
          temp_12455;
          temp_12457;
          temp_12459;
          temp_12461;
          temp_12463
        ]) in
    (temp_12465)).

Definition constant_p3_8_v : (serialized_scalar_t) :=
  (let temp_12467 : int8 :=
      (secret (@repr U8 254)) in
    let temp_12469 : int8 :=
      (secret (@repr U8 255)) in
    let temp_12471 : int8 :=
      (secret (@repr U8 255)) in
    let temp_12473 : int8 :=
      (secret (@repr U8 255)) in
    let temp_12475 : int8 :=
      (secret (@repr U8 255)) in
    let temp_12477 : int8 :=
      (secret (@repr U8 255)) in
    let temp_12479 : int8 :=
      (secret (@repr U8 255)) in
    let temp_12481 : int8 :=
      (secret (@repr U8 255)) in
    let temp_12483 : int8 :=
      (secret (@repr U8 255)) in
    let temp_12485 : int8 :=
      (secret (@repr U8 255)) in
    let temp_12487 : int8 :=
      (secret (@repr U8 255)) in
    let temp_12489 : int8 :=
      (secret (@repr U8 255)) in
    let temp_12491 : int8 :=
      (secret (@repr U8 255)) in
    let temp_12493 : int8 :=
      (secret (@repr U8 255)) in
    let temp_12495 : int8 :=
      (secret (@repr U8 255)) in
    let temp_12497 : int8 :=
      (secret (@repr U8 255)) in
    let temp_12499 : int8 :=
      (secret (@repr U8 255)) in
    let temp_12501 : int8 :=
      (secret (@repr U8 255)) in
    let temp_12503 : int8 :=
      (secret (@repr U8 255)) in
    let temp_12505 : int8 :=
      (secret (@repr U8 255)) in
    let temp_12507 : int8 :=
      (secret (@repr U8 255)) in
    let temp_12509 : int8 :=
      (secret (@repr U8 255)) in
    let temp_12511 : int8 :=
      (secret (@repr U8 255)) in
    let temp_12513 : int8 :=
      (secret (@repr U8 255)) in
    let temp_12515 : int8 :=
      (secret (@repr U8 255)) in
    let temp_12517 : int8 :=
      (secret (@repr U8 255)) in
    let temp_12519 : int8 :=
      (secret (@repr U8 255)) in
    let temp_12521 : int8 :=
      (secret (@repr U8 255)) in
    let temp_12523 : int8 :=
      (secret (@repr U8 255)) in
    let temp_12525 : int8 :=
      (secret (@repr U8 255)) in
    let temp_12527 : int8 :=
      (secret (@repr U8 255)) in
    let temp_12529 : int8 :=
      (secret (@repr U8 15)) in
    let temp_12531 : nseq uint8 32 :=
      (array_from_list uint8 [
          temp_12467;
          temp_12469;
          temp_12471;
          temp_12473;
          temp_12475;
          temp_12477;
          temp_12479;
          temp_12481;
          temp_12483;
          temp_12485;
          temp_12487;
          temp_12489;
          temp_12491;
          temp_12493;
          temp_12495;
          temp_12497;
          temp_12499;
          temp_12501;
          temp_12503;
          temp_12505;
          temp_12507;
          temp_12509;
          temp_12511;
          temp_12513;
          temp_12515;
          temp_12517;
          temp_12519;
          temp_12521;
          temp_12523;
          temp_12525;
          temp_12527;
          temp_12529
        ]) in
    (temp_12531)).

Definition constant_p1_4_v : (serialized_scalar_t) :=
  (let temp_12533 : int8 :=
      (secret (@repr U8 251)) in
    let temp_12535 : int8 :=
      (secret (@repr U8 255)) in
    let temp_12537 : int8 :=
      (secret (@repr U8 255)) in
    let temp_12539 : int8 :=
      (secret (@repr U8 255)) in
    let temp_12541 : int8 :=
      (secret (@repr U8 255)) in
    let temp_12543 : int8 :=
      (secret (@repr U8 255)) in
    let temp_12545 : int8 :=
      (secret (@repr U8 255)) in
    let temp_12547 : int8 :=
      (secret (@repr U8 255)) in
    let temp_12549 : int8 :=
      (secret (@repr U8 255)) in
    let temp_12551 : int8 :=
      (secret (@repr U8 255)) in
    let temp_12553 : int8 :=
      (secret (@repr U8 255)) in
    let temp_12555 : int8 :=
      (secret (@repr U8 255)) in
    let temp_12557 : int8 :=
      (secret (@repr U8 255)) in
    let temp_12559 : int8 :=
      (secret (@repr U8 255)) in
    let temp_12561 : int8 :=
      (secret (@repr U8 255)) in
    let temp_12563 : int8 :=
      (secret (@repr U8 255)) in
    let temp_12565 : int8 :=
      (secret (@repr U8 255)) in
    let temp_12567 : int8 :=
      (secret (@repr U8 255)) in
    let temp_12569 : int8 :=
      (secret (@repr U8 255)) in
    let temp_12571 : int8 :=
      (secret (@repr U8 255)) in
    let temp_12573 : int8 :=
      (secret (@repr U8 255)) in
    let temp_12575 : int8 :=
      (secret (@repr U8 255)) in
    let temp_12577 : int8 :=
      (secret (@repr U8 255)) in
    let temp_12579 : int8 :=
      (secret (@repr U8 255)) in
    let temp_12581 : int8 :=
      (secret (@repr U8 255)) in
    let temp_12583 : int8 :=
      (secret (@repr U8 255)) in
    let temp_12585 : int8 :=
      (secret (@repr U8 255)) in
    let temp_12587 : int8 :=
      (secret (@repr U8 255)) in
    let temp_12589 : int8 :=
      (secret (@repr U8 255)) in
    let temp_12591 : int8 :=
      (secret (@repr U8 255)) in
    let temp_12593 : int8 :=
      (secret (@repr U8 255)) in
    let temp_12595 : int8 :=
      (secret (@repr U8 31)) in
    let temp_12597 : nseq uint8 32 :=
      (array_from_list uint8 [
          temp_12533;
          temp_12535;
          temp_12537;
          temp_12539;
          temp_12541;
          temp_12543;
          temp_12545;
          temp_12547;
          temp_12549;
          temp_12551;
          temp_12553;
          temp_12555;
          temp_12557;
          temp_12559;
          temp_12561;
          temp_12563;
          temp_12565;
          temp_12567;
          temp_12569;
          temp_12571;
          temp_12573;
          temp_12575;
          temp_12577;
          temp_12579;
          temp_12581;
          temp_12583;
          temp_12585;
          temp_12587;
          temp_12589;
          temp_12591;
          temp_12593;
          temp_12595
        ]) in
    (temp_12597)).

Definition constant_d_v : (serialized_scalar_t) :=
  (let temp_12599 : int8 :=
      (secret (@repr U8 163)) in
    let temp_12601 : int8 :=
      (secret (@repr U8 120)) in
    let temp_12603 : int8 :=
      (secret (@repr U8 89)) in
    let temp_12605 : int8 :=
      (secret (@repr U8 19)) in
    let temp_12607 : int8 :=
      (secret (@repr U8 202)) in
    let temp_12609 : int8 :=
      (secret (@repr U8 77)) in
    let temp_12611 : int8 :=
      (secret (@repr U8 235)) in
    let temp_12613 : int8 :=
      (secret (@repr U8 117)) in
    let temp_12615 : int8 :=
      (secret (@repr U8 171)) in
    let temp_12617 : int8 :=
      (secret (@repr U8 216)) in
    let temp_12619 : int8 :=
      (secret (@repr U8 65)) in
    let temp_12621 : int8 :=
      (secret (@repr U8 65)) in
    let temp_12623 : int8 :=
      (secret (@repr U8 77)) in
    let temp_12625 : int8 :=
      (secret (@repr U8 10)) in
    let temp_12627 : int8 :=
      (secret (@repr U8 112)) in
    let temp_12629 : int8 :=
      (secret (@repr U8 0)) in
    let temp_12631 : int8 :=
      (secret (@repr U8 152)) in
    let temp_12633 : int8 :=
      (secret (@repr U8 232)) in
    let temp_12635 : int8 :=
      (secret (@repr U8 121)) in
    let temp_12637 : int8 :=
      (secret (@repr U8 119)) in
    let temp_12639 : int8 :=
      (secret (@repr U8 121)) in
    let temp_12641 : int8 :=
      (secret (@repr U8 64)) in
    let temp_12643 : int8 :=
      (secret (@repr U8 199)) in
    let temp_12645 : int8 :=
      (secret (@repr U8 140)) in
    let temp_12647 : int8 :=
      (secret (@repr U8 115)) in
    let temp_12649 : int8 :=
      (secret (@repr U8 254)) in
    let temp_12651 : int8 :=
      (secret (@repr U8 111)) in
    let temp_12653 : int8 :=
      (secret (@repr U8 43)) in
    let temp_12655 : int8 :=
      (secret (@repr U8 238)) in
    let temp_12657 : int8 :=
      (secret (@repr U8 108)) in
    let temp_12659 : int8 :=
      (secret (@repr U8 3)) in
    let temp_12661 : int8 :=
      (secret (@repr U8 82)) in
    let temp_12663 : nseq uint8 32 :=
      (array_from_list uint8 [
          temp_12599;
          temp_12601;
          temp_12603;
          temp_12605;
          temp_12607;
          temp_12609;
          temp_12611;
          temp_12613;
          temp_12615;
          temp_12617;
          temp_12619;
          temp_12621;
          temp_12623;
          temp_12625;
          temp_12627;
          temp_12629;
          temp_12631;
          temp_12633;
          temp_12635;
          temp_12637;
          temp_12639;
          temp_12641;
          temp_12643;
          temp_12645;
          temp_12647;
          temp_12649;
          temp_12651;
          temp_12653;
          temp_12655;
          temp_12657;
          temp_12659;
          temp_12661
        ]) in
    (temp_12663)).


Notation "'is_negative_inp'" := (
  ed25519_field_element_t : choice_type) (in custom pack_type at level 2).
Notation "'is_negative_out'" := (
  uint8 : choice_type) (in custom pack_type at level 2).
Definition IS_NEGATIVE : nat :=
  (12671).
Program Definition is_negative
   : package (fset.fset0) [interface] [interface
  #val #[ IS_NEGATIVE ] : is_negative_inp → is_negative_out ] :=
  (
    [package #def #[ IS_NEGATIVE ] (temp_inp : is_negative_inp) : is_negative_out { 
    let '(x_12664) := temp_inp : ed25519_field_element_t in
    ({ code  temp_12666 ←
        (nat_mod_bit (x_12664) (usize 0)) ;;
       '(temp_12668 : int8) ←
        (secret (@repr U8 1)) ;;
       '(temp_12670 : int8) ←
        (secret (@repr U8 0)) ;;
      @ret (uint8) ((if (temp_12666):bool_ChoiceEquality then (*inline*) (
            temp_12668) else (temp_12670))) } : code (fset.fset0) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_is_negative : package _ _ _ :=
  (is_negative).
Fail Next Obligation.

Definition s_12687_loc : ChoiceEqualityLocation :=
  ((byte_seq ; 12700%nat)).
Notation "'compress_inp'" := (
  ed_point_t : choice_type) (in custom pack_type at level 2).
Notation "'compress_out'" := (
  compressed_ed_point_t : choice_type) (in custom pack_type at level 2).
Definition COMPRESS : nat :=
  (12701).
Program Definition compress
   : package (CEfset ([s_12687_loc])) [interface
  #val #[ IS_NEGATIVE ] : is_negative_inp → is_negative_out ] [interface
  #val #[ COMPRESS ] : compress_inp → compress_out ] :=
  ([package #def #[ COMPRESS ] (temp_inp : compress_inp) : compress_out { 
    let '(p_12672) := temp_inp : ed_point_t in
    #import {sig #[ IS_NEGATIVE ] : is_negative_inp → is_negative_out } as is_negative ;;
    let is_negative := fun x_0 => is_negative (x_0) in
    ({ code  temp_12699 ←
        (ret (p_12672)) ;;
      let '(x_12676, y_12680, z_12673, _) :=
        (temp_12699) : (
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t
      ) in
       '(z_inv_12677 : ed25519_field_element_t) ←
        ( temp_12675 ←
            (nat_mod_inv (z_12673)) ;;
          ret (temp_12675)) ;;
       '(x_12689 : ed25519_field_element_t) ←
        ( '(temp_12679 : ed25519_field_element_t) ←
            ((x_12676) *% (z_inv_12677)) ;;
          ret (temp_12679)) ;;
       '(y_12683 : ed25519_field_element_t) ←
        ( '(temp_12682 : ed25519_field_element_t) ←
            ((y_12680) *% (z_inv_12677)) ;;
          ret (temp_12682)) ;;
       '(s_12687 : byte_seq) ←
          ( temp_12685 ←
              (nat_mod_to_byte_seq_le (y_12683)) ;;
            ret (temp_12685)) ;;
        #put s_12687_loc := s_12687 ;;
       '(s_12687 : seq uint8) ←
        ( '(temp_12688 : uint8) ←
            (seq_index (s_12687) (usize 31)) ;;
           '(temp_12691 : uint8) ←
            (is_negative (x_12689)) ;;
           temp_12693 ←
            ((temp_12691) shift_left (usize 7)) ;;
           temp_12695 ←
            ((temp_12688) .^ (temp_12693)) ;;
          ret (seq_upd s_12687 (usize 31) (temp_12695))) ;;
      
       '(temp_12697 : compressed_ed_point_t) ←
        (array_from_slice (default : uint8) (32) (s_12687) (usize 0) (
            usize 32)) ;;
      @ret (compressed_ed_point_t) (temp_12697) } : code (CEfset (
          [s_12687_loc])) [interface
      #val #[ IS_NEGATIVE ] : is_negative_inp → is_negative_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_compress : package _ _ _ :=
  (seq_link compress link_rest(package_is_negative)).
Fail Next Obligation.

Definition result_12721_loc : ChoiceEqualityLocation :=
  (((option ed25519_field_element_t) ; 12740%nat)).
Notation "'sqrt_inp'" := (
  ed25519_field_element_t : choice_type) (in custom pack_type at level 2).
Notation "'sqrt_out'" := ((
    option ed25519_field_element_t) : choice_type) (in custom pack_type at level 2).
Definition SQRT : nat :=
  (12741).
Program Definition sqrt
   : package (CEfset ([result_12721_loc])) [interface
  #val #[ SOME ] : some_inp → some_out ] [interface
  #val #[ SQRT ] : sqrt_inp → sqrt_out ] :=
  ([package #def #[ SQRT ] (temp_inp : sqrt_inp) : sqrt_out { 
    let '(a_12710) := temp_inp : ed25519_field_element_t in
    #import {sig #[ SOME ] : some_inp → some_out } as some ;;
    let some := fun x_0 => some (x_0) in
    ({ code  '(p3_8_12711 : ed25519_field_element_t) ←
        ( '(temp_12703 : seq uint8) ←
            (array_to_seq (constant_p3_8_v)) ;;
           '(temp_12705 : ed25519_field_element_t) ←
            (nat_mod_from_byte_seq_le (temp_12703)) ;;
          ret (temp_12705)) ;;
       '(p1_4_12732 : ed25519_field_element_t) ←
        ( '(temp_12707 : seq uint8) ←
            (array_to_seq (constant_p1_4_v)) ;;
           '(temp_12709 : ed25519_field_element_t) ←
            (nat_mod_from_byte_seq_le (temp_12707)) ;;
          ret (temp_12709)) ;;
       '(x_c_12714 : ed25519_field_element_t) ←
        ( temp_12713 ←
            (nat_mod_pow_self (a_12710) (p3_8_12711)) ;;
          ret (temp_12713)) ;;
       '(result_12721 : (option ed25519_field_element_t)) ←
          (ret (@None ed25519_field_element_t)) ;;
        #put result_12721_loc := result_12721 ;;
       '(temp_12716 : ed25519_field_element_t) ←
        ((x_c_12714) *% (x_c_12714)) ;;
       '(temp_12718 : bool_ChoiceEquality) ←
        ((temp_12716) =.? (a_12710)) ;;
       '(result_12721 : ((option ed25519_field_element_t))) ←
        (if temp_12718:bool_ChoiceEquality
          then (*not state*) (let temp_then :=  '(result_12721 : (
                    option ed25519_field_element_t)) ←
                (( temp_12720 ←
                      (some (x_c_12714)) ;;
                    ret (temp_12720))) ;;
              #put result_12721_loc := result_12721 ;;
            
            @ret (((option ed25519_field_element_t))) (result_12721) in
            ({ code temp_then } : code (CEfset ([result_12721_loc])) [interface
              #val #[ SOME ] : some_inp → some_out ] _))
          else @ret (((option ed25519_field_element_t))) (result_12721)) ;;
      
       '(temp_12723 : ed25519_field_element_t) ←
        ((x_c_12714) *% (x_c_12714)) ;;
       '(temp_12725 : ed25519_field_element_t) ←
        (nat_mod_zero ) ;;
       '(temp_12727 : ed25519_field_element_t) ←
        ((temp_12725) -% (a_12710)) ;;
       '(temp_12729 : bool_ChoiceEquality) ←
        ((temp_12723) =.? (temp_12727)) ;;
       '(result_12721 : ((option ed25519_field_element_t))) ←
        (if temp_12729:bool_ChoiceEquality
          then (*not state*) (let temp_then :=  '(
                x_12737 : ed25519_field_element_t) ←
              ( '(temp_12731 : ed25519_field_element_t) ←
                  (nat_mod_two ) ;;
                 temp_12734 ←
                  (nat_mod_pow_self (temp_12731) (p1_4_12732)) ;;
                 '(temp_12736 : ed25519_field_element_t) ←
                  ((temp_12734) *% (x_c_12714)) ;;
                ret (temp_12736)) ;;
             '(result_12721 : (option ed25519_field_element_t)) ←
                (( temp_12739 ←
                      (some (x_12737)) ;;
                    ret (temp_12739))) ;;
              #put result_12721_loc := result_12721 ;;
            
            @ret (((option ed25519_field_element_t))) (result_12721) in
            ({ code temp_then } : code (CEfset ([result_12721_loc])) [interface
              #val #[ SOME ] : some_inp → some_out ] _))
          else @ret (((option ed25519_field_element_t))) (result_12721)) ;;
      
      @ret ((option ed25519_field_element_t)) (result_12721) } : code (CEfset (
          [result_12721_loc])) [interface #val #[ SOME ] : some_inp → some_out
      ] _)
    }]).
Fail Next Obligation.
Program Definition package_sqrt : package _ _ _ :=
  (seq_link sqrt link_rest(package_some)).
Fail Next Obligation.


Notation "'check_canonical_point_inp'" := (
  compressed_ed_point_t : choice_type) (in custom pack_type at level 2).
Notation "'check_canonical_point_out'" := (
  bool_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Definition CHECK_CANONICAL_POINT : nat :=
  (12760).
Program Definition check_canonical_point
   : package (fset.fset0) [interface] [interface
  #val #[ CHECK_CANONICAL_POINT ] : check_canonical_point_inp → check_canonical_point_out
  ] :=
  (
    [package #def #[ CHECK_CANONICAL_POINT ] (temp_inp : check_canonical_point_inp) : check_canonical_point_out { 
    let '(x_12743) := temp_inp : compressed_ed_point_t in
    ({ code  '(x_12743 : compressed_ed_point_t) ←
        ( temp_12744 ←
            (array_index (x_12743) (usize 31)) ;;
           '(temp_12746 : int8) ←
            (secret (@repr U8 127)) ;;
           temp_12748 ←
            ((temp_12744) .& (temp_12746)) ;;
          ret (array_upd x_12743 (usize 31) (temp_12748))) ;;
      
       '(x_12753 : big_integer_t) ←
        ( '(temp_12750 : seq uint8) ←
            (array_to_seq (x_12743)) ;;
           '(temp_12752 : big_integer_t) ←
            (nat_mod_from_byte_seq_le (temp_12750)) ;;
          ret (temp_12752)) ;;
       '(temp_12755 : seq uint8) ←
        (array_to_seq (constant_p_v)) ;;
       '(temp_12757 : big_integer_t) ←
        (nat_mod_from_byte_seq_le (temp_12755)) ;;
       '(temp_12759 : bool_ChoiceEquality) ←
        ((x_12753) <.? (temp_12757)) ;;
      @ret (bool_ChoiceEquality) (temp_12759) } : code (
        fset.fset0) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_check_canonical_point : package _ _ _ :=
  (check_canonical_point).
Fail Next Obligation.

Definition y_s_12775_loc : ChoiceEqualityLocation :=
  ((compressed_ed_point_t ; 12839%nat)).
Definition x_12810_loc : ChoiceEqualityLocation :=
  ((ed25519_field_element_t ; 12840%nat)).
Notation "'decompress_inp'" := (
  compressed_ed_point_t : choice_type) (in custom pack_type at level 2).
Notation "'decompress_out'" := ((
    option ed_point_t) : choice_type) (in custom pack_type at level 2).
Definition DECOMPRESS : nat :=
  (12841).
Program Definition decompress
   : package (CEfset ([y_s_12775_loc ; x_12810_loc])) [interface
  #val #[ SOME ] : some_inp → some_out ;
  #val #[ CHECK_CANONICAL_POINT ] : check_canonical_point_inp → check_canonical_point_out ;
  #val #[ IS_NEGATIVE ] : is_negative_inp → is_negative_out ;
  #val #[ SQRT ] : sqrt_inp → sqrt_out ] [interface
  #val #[ DECOMPRESS ] : decompress_inp → decompress_out ] :=
  ([package #def #[ DECOMPRESS ] (temp_inp : decompress_inp) : decompress_out { 
    let '(q_12766) := temp_inp : compressed_ed_point_t in
    #import {sig #[ SOME ] : some_inp → some_out } as some ;;
    let some := fun x_0 => some (x_0) in
    #import {sig #[ CHECK_CANONICAL_POINT ] : check_canonical_point_inp → check_canonical_point_out } as check_canonical_point ;;
    let check_canonical_point := fun x_0 => check_canonical_point (x_0) in
    #import {sig #[ IS_NEGATIVE ] : is_negative_inp → is_negative_out } as is_negative ;;
    let is_negative := fun x_0 => is_negative (x_0) in
    #import {sig #[ SQRT ] : sqrt_inp → sqrt_out } as sqrt ;;
    let sqrt := fun x_0 => sqrt (x_0) in
    ({ code  '(d_12796 : ed25519_field_element_t) ←
        ( '(temp_12762 : seq uint8) ←
            (array_to_seq (constant_d_v)) ;;
           '(temp_12764 : ed25519_field_element_t) ←
            (nat_mod_from_byte_seq_le (temp_12762)) ;;
          ret (temp_12764)) ;;
       '(x_s_12817 : uint8) ←
        ( temp_12767 ←
            (array_index (q_12766) (usize 31)) ;;
           '(temp_12769 : int8) ←
            (secret (@repr U8 128)) ;;
           temp_12771 ←
            ((temp_12767) .& (temp_12769)) ;;
           temp_12773 ←
            ((temp_12771) shift_right (usize 7)) ;;
          ret (temp_12773)) ;;
       '(y_s_12775 : compressed_ed_point_t) ←
          (ret (q_12766)) ;;
        #put y_s_12775_loc := y_s_12775 ;;
       '(y_s_12775 : compressed_ed_point_t) ←
        ( temp_12776 ←
            (array_index (y_s_12775) (usize 31)) ;;
           '(temp_12778 : int8) ←
            (secret (@repr U8 127)) ;;
           temp_12780 ←
            ((temp_12776) .& (temp_12778)) ;;
          ret (array_upd y_s_12775 (usize 31) (temp_12780))) ;;
      
       '(temp_12782 : bool_ChoiceEquality) ←
        (check_canonical_point (y_s_12775)) ;;
      bnd(
        ChoiceEqualityMonad.option_bind_code , unit_ChoiceEquality , _ , CEfset (
          [y_s_12775_loc ; x_12810_loc])) 'tt ⇠
      (if negb (temp_12782) : bool_ChoiceEquality
        then (*state*) (({ code bnd(
              ChoiceEqualityMonad.option_bind_code , ed_point_t , _ , CEfset (
                [y_s_12775_loc])) _ ⇠
            (({ code @ret _ (@None ed_point_t) } : code (CEfset (
                    [y_s_12775_loc])) [interface] _)) in
            ({ code @ret ((option unit_ChoiceEquality)) (
                @Some unit_ChoiceEquality (
                  (tt : unit_ChoiceEquality))) } : code (CEfset (
                  [y_s_12775_loc])) [interface] _) } : code (CEfset (
                [y_s_12775_loc])) [interface] _))
        else ({ code @ret ((option unit_ChoiceEquality)) (
            @Some unit_ChoiceEquality (
              (tt : unit_ChoiceEquality))) } : code _ _ _) ) in
      ({ code  '(y_12789 : ed25519_field_element_t) ←
          ( '(temp_12784 : seq uint8) ←
              (array_to_seq (y_s_12775)) ;;
             '(temp_12786 : ed25519_field_element_t) ←
              (nat_mod_from_byte_seq_le (temp_12784)) ;;
            ret (temp_12786)) ;;
         '(z_12793 : ed25519_field_element_t) ←
          ( '(temp_12788 : ed25519_field_element_t) ←
              (nat_mod_one ) ;;
            ret (temp_12788)) ;;
         '(yy_12792 : ed25519_field_element_t) ←
          ( '(temp_12791 : ed25519_field_element_t) ←
              ((y_12789) *% (y_12789)) ;;
            ret (temp_12791)) ;;
         '(u_12801 : ed25519_field_element_t) ←
          ( '(temp_12795 : ed25519_field_element_t) ←
              ((yy_12792) -% (z_12793)) ;;
            ret (temp_12795)) ;;
         '(v_12802 : ed25519_field_element_t) ←
          ( '(temp_12798 : ed25519_field_element_t) ←
              ((d_12796) *% (yy_12792)) ;;
             '(temp_12800 : ed25519_field_element_t) ←
              ((temp_12798) +% (z_12793)) ;;
            ret (temp_12800)) ;;
         '(xx_12807 : ed25519_field_element_t) ←
          ( temp_12804 ←
              (nat_mod_inv (v_12802)) ;;
             '(temp_12806 : ed25519_field_element_t) ←
              ((u_12801) *% (temp_12804)) ;;
            ret (temp_12806)) ;;
        bndm(
          ChoiceEqualityMonad.option_bind_code , ed25519_field_element_t , _ , CEfset (
            [y_s_12775_loc ; x_12810_loc])) x_12810 ⇠
        (({ code  '(temp_12809 : (option ed25519_field_element_t)) ←
              (sqrt (xx_12807)) ;;
            @ret _ (temp_12809) } : code (CEfset (
                [y_s_12775_loc ; x_12810_loc])) [interface
            #val #[ SQRT ] : sqrt_inp → sqrt_out ] _)) in
        ({ code  '(x_r_12824 : uint8) ←
            ( '(temp_12812 : uint8) ←
                (is_negative (x_12810)) ;;
              ret (temp_12812)) ;;
           '(temp_12814 : ed25519_field_element_t) ←
            (nat_mod_zero ) ;;
           '(temp_12816 : bool_ChoiceEquality) ←
            ((x_12810) =.? (temp_12814)) ;;
           temp_12819 ←
            (uint8_declassify (x_s_12817)) ;;
           '(temp_12821 : bool_ChoiceEquality) ←
            ((temp_12819) =.? (@repr U8 1)) ;;
           '(temp_12823 : bool_ChoiceEquality) ←
            ((temp_12816) && (temp_12821)) ;;
          bnd(
            ChoiceEqualityMonad.option_bind_code , unit_ChoiceEquality , _ , CEfset (
              [y_s_12775_loc ; x_12810_loc])) 'tt ⇠
          (if temp_12823 : bool_ChoiceEquality
            then (*state*) (({ code bnd(
                  ChoiceEqualityMonad.option_bind_code , ed_point_t , _ , CEfset (
                    [y_s_12775_loc ; x_12810_loc])) _ ⇠
                (({ code @ret _ (@None ed_point_t) } : code (CEfset (
                        [y_s_12775_loc ; x_12810_loc])) [interface] _)) in
                ({ code @ret ((option unit_ChoiceEquality)) (
                    @Some unit_ChoiceEquality (
                      (tt : unit_ChoiceEquality))) } : code (CEfset (
                      [y_s_12775_loc ; x_12810_loc])) [interface] _) } : code (
                  CEfset ([y_s_12775_loc ; x_12810_loc])) [interface] _))
            else ({ code @ret ((option unit_ChoiceEquality)) (
                @Some unit_ChoiceEquality (
                  (tt : unit_ChoiceEquality))) } : code _ _ _) ) in
          ({ code  temp_12826 ←
              (uint8_declassify (x_r_12824)) ;;
             temp_12828 ←
              (uint8_declassify (x_s_12817)) ;;
             '(temp_12830 : bool_ChoiceEquality) ←
              ((temp_12826) !=.? (temp_12828)) ;;
             '(x_12810 : (ed25519_field_element_t)) ←
              (if temp_12830:bool_ChoiceEquality
                then (*not state*) (let temp_then :=  '(
                        x_12810 : ed25519_field_element_t) ←
                      (( '(temp_12832 : ed25519_field_element_t) ←
                            (nat_mod_zero ) ;;
                           '(temp_12834 : ed25519_field_element_t) ←
                            ((temp_12832) -% (x_12810)) ;;
                          ret (temp_12834))) ;;
                    #put x_12810_loc := x_12810 ;;
                  
                  @ret ((ed25519_field_element_t)) (x_12810) in
                  ({ code temp_then } : code (CEfset (
                        [y_s_12775_loc ; x_12810_loc])) [interface] _))
                else @ret ((ed25519_field_element_t)) (x_12810)) ;;
            
             '(temp_12836 : ed25519_field_element_t) ←
              ((x_12810) *% (y_12789)) ;;
             temp_12838 ←
              (some (prod_ce(x_12810, y_12789, z_12793, temp_12836))) ;;
            @ret ((option (
                  ed25519_field_element_t '×
                  ed25519_field_element_t '×
                  ed25519_field_element_t '×
                  ed25519_field_element_t
                ))) (temp_12838) } : code (CEfset (
                [y_s_12775_loc ; x_12810_loc])) [interface
            #val #[ SOME ] : some_inp → some_out ;
            #val #[ CHECK_CANONICAL_POINT ] : check_canonical_point_inp → check_canonical_point_out ;
            #val #[ IS_NEGATIVE ] : is_negative_inp → is_negative_out ;
            #val #[ SQRT ] : sqrt_inp → sqrt_out ] _) } : code (CEfset (
              [y_s_12775_loc ; x_12810_loc])) [interface
          #val #[ SOME ] : some_inp → some_out ;
          #val #[ CHECK_CANONICAL_POINT ] : check_canonical_point_inp → check_canonical_point_out ;
          #val #[ IS_NEGATIVE ] : is_negative_inp → is_negative_out ;
          #val #[ SQRT ] : sqrt_inp → sqrt_out ] _) } : code (CEfset (
            [y_s_12775_loc ; x_12810_loc])) [interface
        #val #[ SOME ] : some_inp → some_out ;
        #val #[ CHECK_CANONICAL_POINT ] : check_canonical_point_inp → check_canonical_point_out ;
        #val #[ IS_NEGATIVE ] : is_negative_inp → is_negative_out ;
        #val #[ SQRT ] : sqrt_inp → sqrt_out ] _) } : code (CEfset (
          [y_s_12775_loc ; x_12810_loc])) [interface
      #val #[ SOME ] : some_inp → some_out ;
      #val #[ CHECK_CANONICAL_POINT ] : check_canonical_point_inp → check_canonical_point_out ;
      #val #[ IS_NEGATIVE ] : is_negative_inp → is_negative_out ;
      #val #[ SQRT ] : sqrt_inp → sqrt_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_decompress : package _ _ _ :=
  (seq_link decompress link_rest(
      package_some,package_check_canonical_point,package_is_negative,package_sqrt)).
Fail Next Obligation.

Definition y_s_12856_loc : ChoiceEqualityLocation :=
  ((compressed_ed_point_t ; 12908%nat)).
Definition x_12889_loc : ChoiceEqualityLocation :=
  ((ed25519_field_element_t ; 12909%nat)).
Notation "'decompress_non_canonical_inp'" := (
  compressed_ed_point_t : choice_type) (in custom pack_type at level 2).
Notation "'decompress_non_canonical_out'" := ((
    option ed_point_t) : choice_type) (in custom pack_type at level 2).
Definition DECOMPRESS_NON_CANONICAL : nat :=
  (12910).
Program Definition decompress_non_canonical
   : package (CEfset ([y_s_12856_loc ; x_12889_loc])) [interface
  #val #[ SOME ] : some_inp → some_out ;
  #val #[ IS_NEGATIVE ] : is_negative_inp → is_negative_out ;
  #val #[ SQRT ] : sqrt_inp → sqrt_out ] [interface
  #val #[ DECOMPRESS_NON_CANONICAL ] : decompress_non_canonical_inp → decompress_non_canonical_out
  ] :=
  (
    [package #def #[ DECOMPRESS_NON_CANONICAL ] (temp_inp : decompress_non_canonical_inp) : decompress_non_canonical_out { 
    let '(p_12847) := temp_inp : compressed_ed_point_t in
    #import {sig #[ SOME ] : some_inp → some_out } as some ;;
    let some := fun x_0 => some (x_0) in
    #import {sig #[ IS_NEGATIVE ] : is_negative_inp → is_negative_out } as is_negative ;;
    let is_negative := fun x_0 => is_negative (x_0) in
    #import {sig #[ SQRT ] : sqrt_inp → sqrt_out } as sqrt ;;
    let sqrt := fun x_0 => sqrt (x_0) in
    ({ code  '(d_12875 : ed25519_field_element_t) ←
        ( '(temp_12843 : seq uint8) ←
            (array_to_seq (constant_d_v)) ;;
           '(temp_12845 : ed25519_field_element_t) ←
            (nat_mod_from_byte_seq_le (temp_12843)) ;;
          ret (temp_12845)) ;;
       '(x_s_12895 : uint8) ←
        ( temp_12848 ←
            (array_index (p_12847) (usize 31)) ;;
           '(temp_12850 : int8) ←
            (secret (@repr U8 128)) ;;
           temp_12852 ←
            ((temp_12848) .& (temp_12850)) ;;
           temp_12854 ←
            ((temp_12852) shift_right (usize 7)) ;;
          ret (temp_12854)) ;;
       '(y_s_12856 : compressed_ed_point_t) ←
          (ret (p_12847)) ;;
        #put y_s_12856_loc := y_s_12856 ;;
       '(y_s_12856 : compressed_ed_point_t) ←
        ( temp_12857 ←
            (array_index (y_s_12856) (usize 31)) ;;
           '(temp_12859 : int8) ←
            (secret (@repr U8 127)) ;;
           temp_12861 ←
            ((temp_12857) .& (temp_12859)) ;;
          ret (array_upd y_s_12856 (usize 31) (temp_12861))) ;;
      
       '(y_12868 : ed25519_field_element_t) ←
        ( '(temp_12863 : seq uint8) ←
            (array_to_seq (y_s_12856)) ;;
           '(temp_12865 : ed25519_field_element_t) ←
            (nat_mod_from_byte_seq_le (temp_12863)) ;;
          ret (temp_12865)) ;;
       '(z_12872 : ed25519_field_element_t) ←
        ( '(temp_12867 : ed25519_field_element_t) ←
            (nat_mod_one ) ;;
          ret (temp_12867)) ;;
       '(yy_12871 : ed25519_field_element_t) ←
        ( '(temp_12870 : ed25519_field_element_t) ←
            ((y_12868) *% (y_12868)) ;;
          ret (temp_12870)) ;;
       '(u_12880 : ed25519_field_element_t) ←
        ( '(temp_12874 : ed25519_field_element_t) ←
            ((yy_12871) -% (z_12872)) ;;
          ret (temp_12874)) ;;
       '(v_12881 : ed25519_field_element_t) ←
        ( '(temp_12877 : ed25519_field_element_t) ←
            ((d_12875) *% (yy_12871)) ;;
           '(temp_12879 : ed25519_field_element_t) ←
            ((temp_12877) +% (z_12872)) ;;
          ret (temp_12879)) ;;
       '(xx_12886 : ed25519_field_element_t) ←
        ( temp_12883 ←
            (nat_mod_inv (v_12881)) ;;
           '(temp_12885 : ed25519_field_element_t) ←
            ((u_12880) *% (temp_12883)) ;;
          ret (temp_12885)) ;;
      bndm(
        ChoiceEqualityMonad.option_bind_code , ed25519_field_element_t , _ , CEfset (
          [y_s_12856_loc ; x_12889_loc])) x_12889 ⇠
      (({ code  '(temp_12888 : (option ed25519_field_element_t)) ←
            (sqrt (xx_12886)) ;;
          @ret _ (temp_12888) } : code (CEfset (
              [y_s_12856_loc ; x_12889_loc])) [interface
          #val #[ SQRT ] : sqrt_inp → sqrt_out ] _)) in
      ({ code  '(x_r_12892 : uint8) ←
          ( '(temp_12891 : uint8) ←
              (is_negative (x_12889)) ;;
            ret (temp_12891)) ;;
         temp_12894 ←
          (uint8_declassify (x_r_12892)) ;;
         temp_12897 ←
          (uint8_declassify (x_s_12895)) ;;
         '(temp_12899 : bool_ChoiceEquality) ←
          ((temp_12894) !=.? (temp_12897)) ;;
         '(x_12889 : (ed25519_field_element_t)) ←
          (if temp_12899:bool_ChoiceEquality
            then (*not state*) (let temp_then :=  '(
                    x_12889 : ed25519_field_element_t) ←
                  (( '(temp_12901 : ed25519_field_element_t) ←
                        (nat_mod_zero ) ;;
                       '(temp_12903 : ed25519_field_element_t) ←
                        ((temp_12901) -% (x_12889)) ;;
                      ret (temp_12903))) ;;
                #put x_12889_loc := x_12889 ;;
              
              @ret ((ed25519_field_element_t)) (x_12889) in
              ({ code temp_then } : code (CEfset (
                    [y_s_12856_loc ; x_12889_loc])) [interface] _))
            else @ret ((ed25519_field_element_t)) (x_12889)) ;;
        
         '(temp_12905 : ed25519_field_element_t) ←
          ((x_12889) *% (y_12868)) ;;
         temp_12907 ←
          (some (prod_ce(x_12889, y_12868, z_12872, temp_12905))) ;;
        @ret ((option (
              ed25519_field_element_t '×
              ed25519_field_element_t '×
              ed25519_field_element_t '×
              ed25519_field_element_t
            ))) (temp_12907) } : code (CEfset (
            [y_s_12856_loc ; x_12889_loc])) [interface
        #val #[ SOME ] : some_inp → some_out ;
        #val #[ IS_NEGATIVE ] : is_negative_inp → is_negative_out ;
        #val #[ SQRT ] : sqrt_inp → sqrt_out ] _) } : code (CEfset (
          [y_s_12856_loc ; x_12889_loc])) [interface
      #val #[ SOME ] : some_inp → some_out ;
      #val #[ IS_NEGATIVE ] : is_negative_inp → is_negative_out ;
      #val #[ SQRT ] : sqrt_inp → sqrt_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_decompress_non_canonical : package _ _ _ :=
  (seq_link decompress_non_canonical link_rest(
      package_some,package_is_negative,package_sqrt)).
Fail Next Obligation.

Definition s_12926_loc : ChoiceEqualityLocation :=
  ((byte_seq ; 12937%nat)).
Notation "'encode_inp'" := (
  ed_point_t : choice_type) (in custom pack_type at level 2).
Notation "'encode_out'" := (
  byte_seq : choice_type) (in custom pack_type at level 2).
Definition ENCODE : nat :=
  (12938).
Program Definition encode
   : package (CEfset ([s_12926_loc])) [interface
  #val #[ IS_NEGATIVE ] : is_negative_inp → is_negative_out ] [interface
  #val #[ ENCODE ] : encode_inp → encode_out ] :=
  ([package #def #[ ENCODE ] (temp_inp : encode_inp) : encode_out { 
    let '(p_12911) := temp_inp : ed_point_t in
    #import {sig #[ IS_NEGATIVE ] : is_negative_inp → is_negative_out } as is_negative ;;
    let is_negative := fun x_0 => is_negative (x_0) in
    ({ code  temp_12936 ←
        (ret (p_12911)) ;;
      let '(x_12915, y_12919, z_12912, _) :=
        (temp_12936) : (
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t
      ) in
       '(z_inv_12916 : ed25519_field_element_t) ←
        ( temp_12914 ←
            (nat_mod_inv (z_12912)) ;;
          ret (temp_12914)) ;;
       '(x_12928 : ed25519_field_element_t) ←
        ( '(temp_12918 : ed25519_field_element_t) ←
            ((x_12915) *% (z_inv_12916)) ;;
          ret (temp_12918)) ;;
       '(y_12922 : ed25519_field_element_t) ←
        ( '(temp_12921 : ed25519_field_element_t) ←
            ((y_12919) *% (z_inv_12916)) ;;
          ret (temp_12921)) ;;
       '(s_12926 : byte_seq) ←
          ( temp_12924 ←
              (nat_mod_to_byte_seq_le (y_12922)) ;;
            ret (temp_12924)) ;;
        #put s_12926_loc := s_12926 ;;
       '(s_12926 : seq uint8) ←
        ( '(temp_12927 : uint8) ←
            (seq_index (s_12926) (usize 31)) ;;
           '(temp_12930 : uint8) ←
            (is_negative (x_12928)) ;;
           temp_12932 ←
            ((temp_12930) shift_left (usize 7)) ;;
           temp_12934 ←
            ((temp_12927) .^ (temp_12932)) ;;
          ret (seq_upd s_12926 (usize 31) (temp_12934))) ;;
      
      @ret (seq uint8) (s_12926) } : code (CEfset ([s_12926_loc])) [interface
      #val #[ IS_NEGATIVE ] : is_negative_inp → is_negative_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_encode : package _ _ _ :=
  (seq_link encode link_rest(package_is_negative)).
Fail Next Obligation.


Notation "'decode_inp'" := (
  byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'decode_out'" := ((
    option ed_point_t) : choice_type) (in custom pack_type at level 2).
Definition DECODE : nat :=
  (12945).
Program Definition decode
   : package (CEfset ([])) [interface
  #val #[ DECOMPRESS ] : decompress_inp → decompress_out ] [interface
  #val #[ DECODE ] : decode_inp → decode_out ] :=
  ([package #def #[ DECODE ] (temp_inp : decode_inp) : decode_out { 
    let '(q_s_12939) := temp_inp : byte_seq in
    #import {sig #[ DECOMPRESS ] : decompress_inp → decompress_out } as decompress ;;
    let decompress := fun x_0 => decompress (x_0) in
    ({ code  '(q_12942 : compressed_ed_point_t) ←
        ( '(temp_12941 : compressed_ed_point_t) ←
            (array_from_slice (default : uint8) (32) (q_s_12939) (usize 0) (
                usize 32)) ;;
          ret (temp_12941)) ;;
       '(temp_12944 : (option ed_point_t)) ←
        (decompress (q_12942)) ;;
      @ret ((option ed_point_t)) (temp_12944) } : code (CEfset ([])) [interface
      #val #[ DECOMPRESS ] : decompress_inp → decompress_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_decode : package _ _ _ :=
  (seq_link decode link_rest(package_decompress)).
Fail Next Obligation.


Notation "'point_add_inp'" := (
  ed_point_t '× ed_point_t : choice_type) (in custom pack_type at level 2).
Notation "'point_add_out'" := (
  ed_point_t : choice_type) (in custom pack_type at level 2).
Definition POINT_ADD : nat :=
  (13018).
Program Definition point_add
   : package (fset.fset0) [interface] [interface
  #val #[ POINT_ADD ] : point_add_inp → point_add_out ] :=
  ([package #def #[ POINT_ADD ] (temp_inp : point_add_inp) : point_add_out { 
    let '(p_12952 , q_12953) := temp_inp : ed_point_t '× ed_point_t in
    ({ code  '(d_c_12974 : ed25519_field_element_t) ←
        ( '(temp_12947 : seq uint8) ←
            (array_to_seq (constant_d_v)) ;;
           '(temp_12949 : ed25519_field_element_t) ←
            (nat_mod_from_byte_seq_le (temp_12947)) ;;
          ret (temp_12949)) ;;
       '(two_12971 : ed25519_field_element_t) ←
        ( '(temp_12951 : ed25519_field_element_t) ←
            (nat_mod_two ) ;;
          ret (temp_12951)) ;;
       temp_13017 ←
        (ret (p_12952)) ;;
      let '(x1_12955, y1_12954, z1_12980, t1_12970) :=
        (temp_13017) : (
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t
      ) in
       temp_13015 ←
        (ret (q_12953)) ;;
      let '(x2_12959, y2_12958, z2_12983, t2_12977) :=
        (temp_13015) : (
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t
      ) in
       '(a_12987 : ed25519_field_element_t) ←
        ( '(temp_12957 : ed25519_field_element_t) ←
            ((y1_12954) -% (x1_12955)) ;;
           '(temp_12961 : ed25519_field_element_t) ←
            ((y2_12958) -% (x2_12959)) ;;
           '(temp_12963 : ed25519_field_element_t) ←
            ((temp_12957) *% (temp_12961)) ;;
          ret (temp_12963)) ;;
       '(b_12986 : ed25519_field_element_t) ←
        ( '(temp_12965 : ed25519_field_element_t) ←
            ((y1_12954) +% (x1_12955)) ;;
           '(temp_12967 : ed25519_field_element_t) ←
            ((y2_12958) +% (x2_12959)) ;;
           '(temp_12969 : ed25519_field_element_t) ←
            ((temp_12965) *% (temp_12967)) ;;
          ret (temp_12969)) ;;
       '(c_12991 : ed25519_field_element_t) ←
        ( '(temp_12973 : ed25519_field_element_t) ←
            ((t1_12970) *% (two_12971)) ;;
           '(temp_12976 : ed25519_field_element_t) ←
            ((temp_12973) *% (d_c_12974)) ;;
           '(temp_12979 : ed25519_field_element_t) ←
            ((temp_12976) *% (t2_12977)) ;;
          ret (temp_12979)) ;;
       '(d_12990 : ed25519_field_element_t) ←
        ( '(temp_12982 : ed25519_field_element_t) ←
            ((z1_12980) *% (two_12971)) ;;
           '(temp_12985 : ed25519_field_element_t) ←
            ((temp_12982) *% (z2_12983)) ;;
          ret (temp_12985)) ;;
       '(e_12998 : ed25519_field_element_t) ←
        ( '(temp_12989 : ed25519_field_element_t) ←
            ((b_12986) -% (a_12987)) ;;
          ret (temp_12989)) ;;
       '(f_12999 : ed25519_field_element_t) ←
        ( '(temp_12993 : ed25519_field_element_t) ←
            ((d_12990) -% (c_12991)) ;;
          ret (temp_12993)) ;;
       '(g_13002 : ed25519_field_element_t) ←
        ( '(temp_12995 : ed25519_field_element_t) ←
            ((d_12990) +% (c_12991)) ;;
          ret (temp_12995)) ;;
       '(h_13003 : ed25519_field_element_t) ←
        ( '(temp_12997 : ed25519_field_element_t) ←
            ((b_12986) +% (a_12987)) ;;
          ret (temp_12997)) ;;
       '(x3_13010 : ed25519_field_element_t) ←
        ( '(temp_13001 : ed25519_field_element_t) ←
            ((e_12998) *% (f_12999)) ;;
          ret (temp_13001)) ;;
       '(y3_13011 : ed25519_field_element_t) ←
        ( '(temp_13005 : ed25519_field_element_t) ←
            ((g_13002) *% (h_13003)) ;;
          ret (temp_13005)) ;;
       '(t3_13013 : ed25519_field_element_t) ←
        ( '(temp_13007 : ed25519_field_element_t) ←
            ((e_12998) *% (h_13003)) ;;
          ret (temp_13007)) ;;
       '(z3_13012 : ed25519_field_element_t) ←
        ( '(temp_13009 : ed25519_field_element_t) ←
            ((f_12999) *% (g_13002)) ;;
          ret (temp_13009)) ;;
      @ret ((
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        )) (prod_ce(x3_13010, y3_13011, z3_13012, t3_13013)) } : code (
        fset.fset0) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_point_add : package _ _ _ :=
  (point_add).
Fail Next Obligation.


Notation "'point_identity_inp'" := (
  unit_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'point_identity_out'" := (
  ed_point_t : choice_type) (in custom pack_type at level 2).
Definition POINT_IDENTITY : nat :=
  (13027).
Program Definition point_identity
   : package (fset.fset0) [interface] [interface
  #val #[ POINT_IDENTITY ] : point_identity_inp → point_identity_out ] :=
  (
    [package #def #[ POINT_IDENTITY ] (temp_inp : point_identity_inp) : point_identity_out { 
    ({ code  '(temp_13020 : ed25519_field_element_t) ←
        (nat_mod_zero ) ;;
       '(temp_13022 : ed25519_field_element_t) ←
        (nat_mod_one ) ;;
       '(temp_13024 : ed25519_field_element_t) ←
        (nat_mod_one ) ;;
       '(temp_13026 : ed25519_field_element_t) ←
        (nat_mod_zero ) ;;
      @ret ((
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        )) (prod_ce(temp_13020, temp_13022, temp_13024, temp_13026)) } : code (
        fset.fset0) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_point_identity : package _ _ _ :=
  (point_identity).
Fail Next Obligation.

Definition q_13035_loc : ChoiceEqualityLocation :=
  (((
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t
      ) ; 13043%nat)).
Definition p_13036_loc : ChoiceEqualityLocation :=
  (((
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t
      ) ; 13044%nat)).
Notation "'point_mul_inp'" := (
  scalar_t '× ed_point_t : choice_type) (in custom pack_type at level 2).
Notation "'point_mul_out'" := (
  ed_point_t : choice_type) (in custom pack_type at level 2).
Definition POINT_MUL : nat :=
  (13045).
Program Definition point_mul
   : package (CEfset ([p_13036_loc ; q_13035_loc])) [interface
  #val #[ POINT_ADD ] : point_add_inp → point_add_out ;
  #val #[ POINT_IDENTITY ] : point_identity_inp → point_identity_out
  ] [interface #val #[ POINT_MUL ] : point_mul_inp → point_mul_out ] :=
  ([package #def #[ POINT_MUL ] (temp_inp : point_mul_inp) : point_mul_out { 
    let '(s_13031 , p_13028) := temp_inp : scalar_t '× ed_point_t in
    #import {sig #[ POINT_ADD ] : point_add_inp → point_add_out } as point_add ;;
    let point_add := fun x_0 x_1 => point_add (x_0,x_1) in
    #import {sig #[ POINT_IDENTITY ] : point_identity_inp → point_identity_out } as point_identity ;;
    let point_identity := point_identity tt in
    ({ code  '(p_13036 : (
              ed25519_field_element_t '×
              ed25519_field_element_t '×
              ed25519_field_element_t '×
              ed25519_field_element_t
            )) ←
          (ret (p_13028)) ;;
        #put p_13036_loc := p_13036 ;;
       '(q_13035 : (
              ed25519_field_element_t '×
              ed25519_field_element_t '×
              ed25519_field_element_t '×
              ed25519_field_element_t
            )) ←
          ( '(temp_13030 : ed_point_t) ←
              (point_identity ) ;;
            ret (temp_13030)) ;;
        #put q_13035_loc := q_13035 ;;
       temp_13042 ←
        (foldi' (usize 0) (usize 256) prod_ce(p_13036, q_13035) (L2 := CEfset (
                [p_13036_loc ; q_13035_loc])) (I2 := [interface
              #val #[ POINT_ADD ] : point_add_inp → point_add_out ;
              #val #[ POINT_IDENTITY ] : point_identity_inp → point_identity_out
              ]) (H_loc_incl := _) (H_opsig_incl := _) (fun i_13032 '(
              p_13036,
              q_13035
            ) =>
            ({ code  temp_13034 ←
                (nat_mod_bit (s_13031) (i_13032)) ;;
               '(q_13035 : (
                    (
                      ed25519_field_element_t '×
                      ed25519_field_element_t '×
                      ed25519_field_element_t '×
                      ed25519_field_element_t
                    )
                  )) ←
                (if temp_13034:bool_ChoiceEquality
                  then (*not state*) (let temp_then :=  '(q_13035 : (
                            ed25519_field_element_t '×
                            ed25519_field_element_t '×
                            ed25519_field_element_t '×
                            ed25519_field_element_t
                          )) ←
                        (( '(temp_13038 : ed_point_t) ←
                              (point_add (q_13035) (p_13036)) ;;
                            ret (temp_13038))) ;;
                      #put q_13035_loc := q_13035 ;;
                    
                    @ret ((
                        (
                          ed25519_field_element_t '×
                          ed25519_field_element_t '×
                          ed25519_field_element_t '×
                          ed25519_field_element_t
                        )
                      )) (q_13035) in
                    ({ code temp_then } : code (CEfset (
                          [p_13036_loc ; q_13035_loc])) [interface
                      #val #[ POINT_ADD ] : point_add_inp → point_add_out
                      ] _))
                  else @ret ((
                      (
                        ed25519_field_element_t '×
                        ed25519_field_element_t '×
                        ed25519_field_element_t '×
                        ed25519_field_element_t
                      )
                    )) (q_13035)) ;;
              
               '(p_13036 : (
                      ed25519_field_element_t '×
                      ed25519_field_element_t '×
                      ed25519_field_element_t '×
                      ed25519_field_element_t
                    )) ←
                  (( '(temp_13040 : ed_point_t) ←
                        (point_add (p_13036) (p_13036)) ;;
                      ret (temp_13040))) ;;
                #put p_13036_loc := p_13036 ;;
              
              @ret ((
                  (
                    ed25519_field_element_t '×
                    ed25519_field_element_t '×
                    ed25519_field_element_t '×
                    ed25519_field_element_t
                  ) '×
                  (
                    ed25519_field_element_t '×
                    ed25519_field_element_t '×
                    ed25519_field_element_t '×
                    ed25519_field_element_t
                  )
                )) (prod_ce(p_13036, q_13035)) } : code (CEfset (
                  [p_13036_loc ; q_13035_loc])) [interface
              #val #[ POINT_ADD ] : point_add_inp → point_add_out ] _))) ;;
      let '(p_13036, q_13035) :=
        (temp_13042) : (
        (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) '×
        (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        )
      ) in
      
      @ret ((
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        )) (q_13035) } : code (CEfset ([p_13036_loc ; q_13035_loc])) [interface
      #val #[ POINT_ADD ] : point_add_inp → point_add_out ;
      #val #[ POINT_IDENTITY ] : point_identity_inp → point_identity_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_point_mul : package _ _ _ :=
  (seq_link point_mul link_rest(package_point_add,package_point_identity)).
Fail Next Obligation.


Notation "'point_mul_by_cofactor_inp'" := (
  ed_point_t : choice_type) (in custom pack_type at level 2).
Notation "'point_mul_by_cofactor_out'" := (
  ed_point_t : choice_type) (in custom pack_type at level 2).
Definition POINT_MUL_BY_COFACTOR : nat :=
  (13056).
Program Definition point_mul_by_cofactor
   : package (fset.fset0) [interface
  #val #[ POINT_ADD ] : point_add_inp → point_add_out ] [interface
  #val #[ POINT_MUL_BY_COFACTOR ] : point_mul_by_cofactor_inp → point_mul_by_cofactor_out
  ] :=
  (
    [package #def #[ POINT_MUL_BY_COFACTOR ] (temp_inp : point_mul_by_cofactor_inp) : point_mul_by_cofactor_out { 
    let '(p_13046) := temp_inp : ed_point_t in
    #import {sig #[ POINT_ADD ] : point_add_inp → point_add_out } as point_add ;;
    let point_add := fun x_0 x_1 => point_add (x_0,x_1) in
    ({ code  '(p2_13049 : (
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t
          )) ←
        ( '(temp_13048 : ed_point_t) ←
            (point_add (p_13046) (p_13046)) ;;
          ret (temp_13048)) ;;
       '(p4_13052 : (
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t
          )) ←
        ( '(temp_13051 : ed_point_t) ←
            (point_add (p2_13049) (p2_13049)) ;;
          ret (temp_13051)) ;;
       '(p8_13055 : (
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t
          )) ←
        ( '(temp_13054 : ed_point_t) ←
            (point_add (p4_13052) (p4_13052)) ;;
          ret (temp_13054)) ;;
      @ret ((
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        )) (p8_13055) } : code (fset.fset0) [interface
      #val #[ POINT_ADD ] : point_add_inp → point_add_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_point_mul_by_cofactor : package _ _ _ :=
  (seq_link point_mul_by_cofactor link_rest(package_point_add)).
Fail Next Obligation.


Notation "'point_neg_inp'" := (
  ed_point_t : choice_type) (in custom pack_type at level 2).
Notation "'point_neg_out'" := (
  ed_point_t : choice_type) (in custom pack_type at level 2).
Definition POINT_NEG : nat :=
  (13072).
Program Definition point_neg
   : package (fset.fset0) [interface] [interface
  #val #[ POINT_NEG ] : point_neg_inp → point_neg_out ] :=
  ([package #def #[ POINT_NEG ] (temp_inp : point_neg_inp) : point_neg_out { 
    let '(p_13057) := temp_inp : ed_point_t in
    ({ code  temp_13071 ←
        (ret (p_13057)) ;;
      let '(x_13060, y_13063, z_13064, t_13067) :=
        (temp_13071) : (
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t
      ) in
       '(temp_13059 : ed25519_field_element_t) ←
        (nat_mod_zero ) ;;
       '(temp_13062 : ed25519_field_element_t) ←
        ((temp_13059) -% (x_13060)) ;;
       '(temp_13066 : ed25519_field_element_t) ←
        (nat_mod_zero ) ;;
       '(temp_13069 : ed25519_field_element_t) ←
        ((temp_13066) -% (t_13067)) ;;
      @ret ((
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        )) (prod_ce(temp_13062, y_13063, z_13064, temp_13069)) } : code (
        fset.fset0) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_point_neg : package _ _ _ :=
  (point_neg).
Fail Next Obligation.


Notation "'point_eq_inp'" := (
  ed_point_t '× ed_point_t : choice_type) (in custom pack_type at level 2).
Notation "'point_eq_out'" := (
  bool_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Definition POINT_EQ : nat :=
  (13099).
Program Definition point_eq
   : package (fset.fset0) [interface] [interface
  #val #[ POINT_EQ ] : point_eq_inp → point_eq_out ] :=
  ([package #def #[ POINT_EQ ] (temp_inp : point_eq_inp) : point_eq_out { 
    let '(p_13073 , q_13074) := temp_inp : ed_point_t '× ed_point_t in
    ({ code  temp_13098 ←
        (ret (p_13073)) ;;
      let '(x1_13075, y1_13085, z1_13080, _) :=
        (temp_13098) : (
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t
      ) in
       temp_13096 ←
        (ret (q_13074)) ;;
      let '(x2_13079, y2_13088, z2_13076, _) :=
        (temp_13096) : (
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t
      ) in
       '(temp_13078 : ed25519_field_element_t) ←
        ((x1_13075) *% (z2_13076)) ;;
       '(temp_13082 : ed25519_field_element_t) ←
        ((x2_13079) *% (z1_13080)) ;;
       '(temp_13084 : bool_ChoiceEquality) ←
        ((temp_13078) =.? (temp_13082)) ;;
       '(temp_13087 : ed25519_field_element_t) ←
        ((y1_13085) *% (z2_13076)) ;;
       '(temp_13090 : ed25519_field_element_t) ←
        ((y2_13088) *% (z1_13080)) ;;
       '(temp_13092 : bool_ChoiceEquality) ←
        ((temp_13087) =.? (temp_13090)) ;;
       '(temp_13094 : bool_ChoiceEquality) ←
        ((temp_13084) && (temp_13092)) ;;
      @ret (bool_ChoiceEquality) (temp_13094) } : code (
        fset.fset0) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_point_eq : package _ _ _ :=
  (point_eq).
Fail Next Obligation.


Notation "'point_normalize_inp'" := (
  ed_point_t : choice_type) (in custom pack_type at level 2).
Notation "'point_normalize_out'" := (
  ed_point_t : choice_type) (in custom pack_type at level 2).
Definition POINT_NORMALIZE : nat :=
  (13122).
Program Definition point_normalize
   : package (fset.fset0) [interface] [interface
  #val #[ POINT_NORMALIZE ] : point_normalize_inp → point_normalize_out ] :=
  (
    [package #def #[ POINT_NORMALIZE ] (temp_inp : point_normalize_inp) : point_normalize_out { 
    let '(q_13100) := temp_inp : ed_point_t in
    ({ code  temp_13121 ←
        (ret (q_13100)) ;;
      let '(qx_13101, qy_13107, qz_13102, _) :=
        (temp_13121) : (
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t
      ) in
       '(px_13114 : ed25519_field_element_t) ←
        ( temp_13104 ←
            (nat_mod_inv (qz_13102)) ;;
           '(temp_13106 : ed25519_field_element_t) ←
            ((qx_13101) *% (temp_13104)) ;;
          ret (temp_13106)) ;;
       '(py_13115 : ed25519_field_element_t) ←
        ( temp_13109 ←
            (nat_mod_inv (qz_13102)) ;;
           '(temp_13111 : ed25519_field_element_t) ←
            ((qy_13107) *% (temp_13109)) ;;
          ret (temp_13111)) ;;
       '(pz_13118 : ed25519_field_element_t) ←
        ( '(temp_13113 : ed25519_field_element_t) ←
            (nat_mod_one ) ;;
          ret (temp_13113)) ;;
       '(pt_13119 : ed25519_field_element_t) ←
        ( '(temp_13117 : ed25519_field_element_t) ←
            ((px_13114) *% (py_13115)) ;;
          ret (temp_13117)) ;;
      @ret ((
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        )) (prod_ce(px_13114, py_13115, pz_13118, pt_13119)) } : code (
        fset.fset0) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_point_normalize : package _ _ _ :=
  (point_normalize).
Fail Next Obligation.

Definition s_13138_loc : ChoiceEqualityLocation :=
  ((serialized_scalar_t ; 13157%nat)).
Notation "'secret_expand_inp'" := (
  secret_key_t : choice_type) (in custom pack_type at level 2).
Notation "'secret_expand_out'" := ((serialized_scalar_t '× serialized_scalar_t
  ) : choice_type) (in custom pack_type at level 2).
Definition SECRET_EXPAND : nat :=
  (13158).
Program Definition secret_expand
   : package (CEfset ([s_13138_loc])) [interface
  #val #[ SHA512 ] : sha512_inp → sha512_out ] [interface
  #val #[ SECRET_EXPAND ] : secret_expand_inp → secret_expand_out ] :=
  (
    [package #def #[ SECRET_EXPAND ] (temp_inp : secret_expand_inp) : secret_expand_out { 
    let '(sk_13123) := temp_inp : secret_key_t in
    #import {sig #[ SHA512 ] : sha512_inp → sha512_out } as sha512 ;;
    let sha512 := fun x_0 => sha512 (x_0) in
    ({ code  '(h_13128 : sha512_digest_t) ←
        ( '(temp_13125 : byte_seq) ←
            (seq_from_slice (sk_13123) (usize 0) (usize 32)) ;;
           temp_13127 ←
            (sha512 (temp_13125)) ;;
          ret (temp_13127)) ;;
       '(h_d_13156 : serialized_scalar_t) ←
        ( '(temp_13130 : seq uint8) ←
            (array_to_seq (h_13128)) ;;
           '(temp_13132 : serialized_scalar_t) ←
            (array_from_slice (default : uint8) (32) (temp_13130) (usize 32) (
                usize 32)) ;;
          ret (temp_13132)) ;;
       '(s_13138 : serialized_scalar_t) ←
          ( '(temp_13134 : seq uint8) ←
              (array_to_seq (h_13128)) ;;
             '(temp_13136 : serialized_scalar_t) ←
              (array_from_slice (default : uint8) (32) (temp_13134) (usize 0) (
                  usize 32)) ;;
            ret (temp_13136)) ;;
        #put s_13138_loc := s_13138 ;;
       '(s_13138 : serialized_scalar_t) ←
        ( temp_13139 ←
            (array_index (s_13138) (usize 0)) ;;
           '(temp_13141 : int8) ←
            (secret (@repr U8 248)) ;;
           temp_13143 ←
            ((temp_13139) .& (temp_13141)) ;;
          ret (array_upd s_13138 (usize 0) (temp_13143))) ;;
      
       '(s_13138 : serialized_scalar_t) ←
        ( temp_13145 ←
            (array_index (s_13138) (usize 31)) ;;
           '(temp_13147 : int8) ←
            (secret (@repr U8 127)) ;;
           temp_13149 ←
            ((temp_13145) .& (temp_13147)) ;;
          ret (array_upd s_13138 (usize 31) (temp_13149))) ;;
      
       '(s_13138 : serialized_scalar_t) ←
        ( temp_13151 ←
            (array_index (s_13138) (usize 31)) ;;
           '(temp_13153 : int8) ←
            (secret (@repr U8 64)) ;;
           temp_13155 ←
            ((temp_13151) .| (temp_13153)) ;;
          ret (array_upd s_13138 (usize 31) (temp_13155))) ;;
      
      @ret ((serialized_scalar_t '× serialized_scalar_t)) (prod_ce(
          s_13138,
          h_d_13156
        )) } : code (CEfset ([s_13138_loc])) [interface
      #val #[ SHA512 ] : sha512_inp → sha512_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_secret_expand : package _ _ _ :=
  (seq_link secret_expand link_rest(package_sha512)).
Fail Next Obligation.


Notation "'secret_to_public_inp'" := (
  secret_key_t : choice_type) (in custom pack_type at level 2).
Notation "'secret_to_public_out'" := (
  public_key_t : choice_type) (in custom pack_type at level 2).
Definition SECRET_TO_PUBLIC : nat :=
  (13180).
Program Definition secret_to_public
   : package (CEfset ([])) [interface
  #val #[ COMPRESS ] : compress_inp → compress_out ;
  #val #[ DECOMPRESS ] : decompress_inp → decompress_out ;
  #val #[ POINT_MUL ] : point_mul_inp → point_mul_out ;
  #val #[ SECRET_EXPAND ] : secret_expand_inp → secret_expand_out ] [interface
  #val #[ SECRET_TO_PUBLIC ] : secret_to_public_inp → secret_to_public_out
  ] :=
  (
    [package #def #[ SECRET_TO_PUBLIC ] (temp_inp : secret_to_public_inp) : secret_to_public_out { 
    let '(sk_13159) := temp_inp : secret_key_t in
    #import {sig #[ COMPRESS ] : compress_inp → compress_out } as compress ;;
    let compress := fun x_0 => compress (x_0) in
    #import {sig #[ DECOMPRESS ] : decompress_inp → decompress_out } as decompress ;;
    let decompress := fun x_0 => decompress (x_0) in
    #import {sig #[ POINT_MUL ] : point_mul_inp → point_mul_out } as point_mul ;;
    let point_mul := fun x_0 x_1 => point_mul (x_0,x_1) in
    #import {sig #[ SECRET_EXPAND ] : secret_expand_inp → secret_expand_out } as secret_expand ;;
    let secret_expand := fun x_0 => secret_expand (x_0) in
    ({ code  temp_13179 ←
        ( '(temp_13161 : (serialized_scalar_t '× serialized_scalar_t)) ←
            (secret_expand (sk_13159)) ;;
          ret (temp_13161)) ;;
      let '(s_13166, _) :=
        (temp_13179) : (serialized_scalar_t '× serialized_scalar_t) in
       '(base_13172 : (
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t
          )) ←
        ( '(temp_13163 : (option ed_point_t)) ←
            (decompress (base_v)) ;;
           temp_13165 ←
            (option_unwrap (temp_13163)) ;;
          ret (temp_13165)) ;;
       '(ss_13171 : scalar_t) ←
        ( '(temp_13168 : seq uint8) ←
            (array_to_seq (s_13166)) ;;
           '(temp_13170 : scalar_t) ←
            (nat_mod_from_byte_seq_le (temp_13168)) ;;
          ret (temp_13170)) ;;
       '(a_13175 : (
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t
          )) ←
        ( '(temp_13174 : ed_point_t) ←
            (point_mul (ss_13171) (base_13172)) ;;
          ret (temp_13174)) ;;
       '(temp_13177 : compressed_ed_point_t) ←
        (compress (a_13175)) ;;
      @ret (compressed_ed_point_t) (temp_13177) } : code (CEfset (
          [])) [interface #val #[ COMPRESS ] : compress_inp → compress_out ;
      #val #[ DECOMPRESS ] : decompress_inp → decompress_out ;
      #val #[ POINT_MUL ] : point_mul_inp → point_mul_out ;
      #val #[ SECRET_EXPAND ] : secret_expand_inp → secret_expand_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_secret_to_public : package _ _ _ :=
  (seq_link secret_to_public link_rest(
      package_compress,package_decompress,package_point_mul,package_secret_expand)).
Fail Next Obligation.


Notation "'check_canonical_scalar_inp'" := (
  serialized_scalar_t : choice_type) (in custom pack_type at level 2).
Notation "'check_canonical_scalar_out'" := (
  bool_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Definition CHECK_CANONICAL_SCALAR : nat :=
  (13202).
Program Definition check_canonical_scalar
   : package (fset.fset0) [interface] [interface
  #val #[ CHECK_CANONICAL_SCALAR ] : check_canonical_scalar_inp → check_canonical_scalar_out
  ] :=
  (
    [package #def #[ CHECK_CANONICAL_SCALAR ] (temp_inp : check_canonical_scalar_inp) : check_canonical_scalar_out { 
    let '(s_13182) := temp_inp : serialized_scalar_t in
    ({ code  temp_13183 ←
        (array_index (s_13182) (usize 31)) ;;
       '(temp_13185 : int8) ←
        (secret (@repr U8 224)) ;;
       temp_13187 ←
        ((temp_13183) .& (temp_13185)) ;;
       temp_13189 ←
        (uint8_declassify (temp_13187)) ;;
       '(temp_13191 : bool_ChoiceEquality) ←
        ((temp_13189) !=.? (@repr U8 0)) ;;
       '(temp_13193 : seq uint8) ←
        (array_to_seq (s_13182)) ;;
       '(temp_13195 : big_integer_t) ←
        (nat_mod_from_byte_seq_le (temp_13193)) ;;
       '(temp_13197 : seq uint8) ←
        (array_to_seq (constant_l_v)) ;;
       '(temp_13199 : big_integer_t) ←
        (nat_mod_from_byte_seq_le (temp_13197)) ;;
       '(temp_13201 : bool_ChoiceEquality) ←
        ((temp_13195) <.? (temp_13199)) ;;
      @ret (bool_ChoiceEquality) ((if (
            temp_13191):bool_ChoiceEquality then (*inline*) (
            (false : bool_ChoiceEquality)) else (temp_13201))) } : code (
        fset.fset0) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_check_canonical_scalar : package _ _ _ :=
  (check_canonical_scalar).
Fail Next Obligation.

