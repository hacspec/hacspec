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

Notation "'ristretto_point_t'" := ((
  field_element_t '×
  field_element_t '×
  field_element_t '×
  field_element_t
)) : hacspec_scope.

Notation "'decode_result_t'" := ((
  result int8 ristretto_point_t)) : hacspec_scope.

Definition ristretto_point_encoded_t  :=
  ( nseq (uint8) (usize 32)).

Definition byte_string_t  :=
  ( nseq (uint8) (usize 64)).

Definition field_canvas_t  :=
  (nseq (int8) (32)).
Definition field_element_t  :=
  (nat_mod 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed).

Definition scalar_canvas_t  :=
  (nseq (int8) (32)).
Definition scalar_t  :=
  (nat_mod 0x1000000000000000000000000000000014def9dea2f79cd65812631a5cf5d3ed).

Definition decoding_error_v : (int8) :=
  ((@repr U8 20)).


Notation "'p_inp'" := (
  unit_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'p_out'" := (
  field_element_t : choice_type) (in custom pack_type at level 2).
Definition P : nat :=
  (4553).
Program Definition p
   : package (fset.fset0) [interface] [interface #val #[ P ] : p_inp → p_out
  ] :=
  ([package #def #[ P ] (temp_inp : p_inp) : p_out { 
    ({ code  '(temp_4488 : int8) ←
        (secret (@repr U8 127)) ;;
       '(temp_4490 : int8) ←
        (secret (@repr U8 255)) ;;
       '(temp_4492 : int8) ←
        (secret (@repr U8 255)) ;;
       '(temp_4494 : int8) ←
        (secret (@repr U8 255)) ;;
       '(temp_4496 : int8) ←
        (secret (@repr U8 255)) ;;
       '(temp_4498 : int8) ←
        (secret (@repr U8 255)) ;;
       '(temp_4500 : int8) ←
        (secret (@repr U8 255)) ;;
       '(temp_4502 : int8) ←
        (secret (@repr U8 255)) ;;
       '(temp_4504 : int8) ←
        (secret (@repr U8 255)) ;;
       '(temp_4506 : int8) ←
        (secret (@repr U8 255)) ;;
       '(temp_4508 : int8) ←
        (secret (@repr U8 255)) ;;
       '(temp_4510 : int8) ←
        (secret (@repr U8 255)) ;;
       '(temp_4512 : int8) ←
        (secret (@repr U8 255)) ;;
       '(temp_4514 : int8) ←
        (secret (@repr U8 255)) ;;
       '(temp_4516 : int8) ←
        (secret (@repr U8 255)) ;;
       '(temp_4518 : int8) ←
        (secret (@repr U8 255)) ;;
       '(temp_4520 : int8) ←
        (secret (@repr U8 255)) ;;
       '(temp_4522 : int8) ←
        (secret (@repr U8 255)) ;;
       '(temp_4524 : int8) ←
        (secret (@repr U8 255)) ;;
       '(temp_4526 : int8) ←
        (secret (@repr U8 255)) ;;
       '(temp_4528 : int8) ←
        (secret (@repr U8 255)) ;;
       '(temp_4530 : int8) ←
        (secret (@repr U8 255)) ;;
       '(temp_4532 : int8) ←
        (secret (@repr U8 255)) ;;
       '(temp_4534 : int8) ←
        (secret (@repr U8 255)) ;;
       '(temp_4536 : int8) ←
        (secret (@repr U8 255)) ;;
       '(temp_4538 : int8) ←
        (secret (@repr U8 255)) ;;
       '(temp_4540 : int8) ←
        (secret (@repr U8 255)) ;;
       '(temp_4542 : int8) ←
        (secret (@repr U8 255)) ;;
       '(temp_4544 : int8) ←
        (secret (@repr U8 255)) ;;
       '(temp_4546 : int8) ←
        (secret (@repr U8 255)) ;;
       '(temp_4548 : int8) ←
        (secret (@repr U8 255)) ;;
       '(temp_4550 : int8) ←
        (secret (@repr U8 237)) ;;
       '(temp_4552 : field_element_t) ←
        (nat_mod_from_byte_seq_be (seq_from_list _ [
              temp_4488;
              temp_4490;
              temp_4492;
              temp_4494;
              temp_4496;
              temp_4498;
              temp_4500;
              temp_4502;
              temp_4504;
              temp_4506;
              temp_4508;
              temp_4510;
              temp_4512;
              temp_4514;
              temp_4516;
              temp_4518;
              temp_4520;
              temp_4522;
              temp_4524;
              temp_4526;
              temp_4528;
              temp_4530;
              temp_4532;
              temp_4534;
              temp_4536;
              temp_4538;
              temp_4540;
              temp_4542;
              temp_4544;
              temp_4546;
              temp_4548;
              temp_4550
            ])) ;;
      @ret (field_element_t) (temp_4552) } : code (fset.fset0) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_p : package _ _ _ :=
  (p).
Fail Next Obligation.


Notation "'d_inp'" := (
  unit_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'d_out'" := (
  field_element_t : choice_type) (in custom pack_type at level 2).
Definition D : nat :=
  (4620).
Program Definition d
   : package (fset.fset0) [interface] [interface #val #[ D ] : d_inp → d_out
  ] :=
  ([package #def #[ D ] (temp_inp : d_inp) : d_out { 
    ({ code  '(temp_4555 : int8) ←
        (secret (@repr U8 82)) ;;
       '(temp_4557 : int8) ←
        (secret (@repr U8 3)) ;;
       '(temp_4559 : int8) ←
        (secret (@repr U8 108)) ;;
       '(temp_4561 : int8) ←
        (secret (@repr U8 238)) ;;
       '(temp_4563 : int8) ←
        (secret (@repr U8 43)) ;;
       '(temp_4565 : int8) ←
        (secret (@repr U8 111)) ;;
       '(temp_4567 : int8) ←
        (secret (@repr U8 254)) ;;
       '(temp_4569 : int8) ←
        (secret (@repr U8 115)) ;;
       '(temp_4571 : int8) ←
        (secret (@repr U8 140)) ;;
       '(temp_4573 : int8) ←
        (secret (@repr U8 199)) ;;
       '(temp_4575 : int8) ←
        (secret (@repr U8 64)) ;;
       '(temp_4577 : int8) ←
        (secret (@repr U8 121)) ;;
       '(temp_4579 : int8) ←
        (secret (@repr U8 119)) ;;
       '(temp_4581 : int8) ←
        (secret (@repr U8 121)) ;;
       '(temp_4583 : int8) ←
        (secret (@repr U8 232)) ;;
       '(temp_4585 : int8) ←
        (secret (@repr U8 152)) ;;
       '(temp_4587 : int8) ←
        (secret (@repr U8 0)) ;;
       '(temp_4589 : int8) ←
        (secret (@repr U8 112)) ;;
       '(temp_4591 : int8) ←
        (secret (@repr U8 10)) ;;
       '(temp_4593 : int8) ←
        (secret (@repr U8 77)) ;;
       '(temp_4595 : int8) ←
        (secret (@repr U8 65)) ;;
       '(temp_4597 : int8) ←
        (secret (@repr U8 65)) ;;
       '(temp_4599 : int8) ←
        (secret (@repr U8 216)) ;;
       '(temp_4601 : int8) ←
        (secret (@repr U8 171)) ;;
       '(temp_4603 : int8) ←
        (secret (@repr U8 117)) ;;
       '(temp_4605 : int8) ←
        (secret (@repr U8 235)) ;;
       '(temp_4607 : int8) ←
        (secret (@repr U8 77)) ;;
       '(temp_4609 : int8) ←
        (secret (@repr U8 202)) ;;
       '(temp_4611 : int8) ←
        (secret (@repr U8 19)) ;;
       '(temp_4613 : int8) ←
        (secret (@repr U8 89)) ;;
       '(temp_4615 : int8) ←
        (secret (@repr U8 120)) ;;
       '(temp_4617 : int8) ←
        (secret (@repr U8 163)) ;;
       '(temp_4619 : field_element_t) ←
        (nat_mod_from_byte_seq_be (seq_from_list _ [
              temp_4555;
              temp_4557;
              temp_4559;
              temp_4561;
              temp_4563;
              temp_4565;
              temp_4567;
              temp_4569;
              temp_4571;
              temp_4573;
              temp_4575;
              temp_4577;
              temp_4579;
              temp_4581;
              temp_4583;
              temp_4585;
              temp_4587;
              temp_4589;
              temp_4591;
              temp_4593;
              temp_4595;
              temp_4597;
              temp_4599;
              temp_4601;
              temp_4603;
              temp_4605;
              temp_4607;
              temp_4609;
              temp_4611;
              temp_4613;
              temp_4615;
              temp_4617
            ])) ;;
      @ret (field_element_t) (temp_4619) } : code (fset.fset0) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_d : package _ _ _ :=
  (d).
Fail Next Obligation.


Notation "'sqrt_m1_inp'" := (
  unit_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'sqrt_m1_out'" := (
  field_element_t : choice_type) (in custom pack_type at level 2).
Definition SQRT_M1 : nat :=
  (4687).
Program Definition sqrt_m1
   : package (fset.fset0) [interface] [interface
  #val #[ SQRT_M1 ] : sqrt_m1_inp → sqrt_m1_out ] :=
  ([package #def #[ SQRT_M1 ] (temp_inp : sqrt_m1_inp) : sqrt_m1_out { 
    ({ code  '(temp_4622 : int8) ←
        (secret (@repr U8 43)) ;;
       '(temp_4624 : int8) ←
        (secret (@repr U8 131)) ;;
       '(temp_4626 : int8) ←
        (secret (@repr U8 36)) ;;
       '(temp_4628 : int8) ←
        (secret (@repr U8 128)) ;;
       '(temp_4630 : int8) ←
        (secret (@repr U8 79)) ;;
       '(temp_4632 : int8) ←
        (secret (@repr U8 193)) ;;
       '(temp_4634 : int8) ←
        (secret (@repr U8 223)) ;;
       '(temp_4636 : int8) ←
        (secret (@repr U8 11)) ;;
       '(temp_4638 : int8) ←
        (secret (@repr U8 43)) ;;
       '(temp_4640 : int8) ←
        (secret (@repr U8 77)) ;;
       '(temp_4642 : int8) ←
        (secret (@repr U8 0)) ;;
       '(temp_4644 : int8) ←
        (secret (@repr U8 153)) ;;
       '(temp_4646 : int8) ←
        (secret (@repr U8 61)) ;;
       '(temp_4648 : int8) ←
        (secret (@repr U8 251)) ;;
       '(temp_4650 : int8) ←
        (secret (@repr U8 215)) ;;
       '(temp_4652 : int8) ←
        (secret (@repr U8 167)) ;;
       '(temp_4654 : int8) ←
        (secret (@repr U8 47)) ;;
       '(temp_4656 : int8) ←
        (secret (@repr U8 67)) ;;
       '(temp_4658 : int8) ←
        (secret (@repr U8 24)) ;;
       '(temp_4660 : int8) ←
        (secret (@repr U8 6)) ;;
       '(temp_4662 : int8) ←
        (secret (@repr U8 173)) ;;
       '(temp_4664 : int8) ←
        (secret (@repr U8 47)) ;;
       '(temp_4666 : int8) ←
        (secret (@repr U8 228)) ;;
       '(temp_4668 : int8) ←
        (secret (@repr U8 120)) ;;
       '(temp_4670 : int8) ←
        (secret (@repr U8 196)) ;;
       '(temp_4672 : int8) ←
        (secret (@repr U8 238)) ;;
       '(temp_4674 : int8) ←
        (secret (@repr U8 27)) ;;
       '(temp_4676 : int8) ←
        (secret (@repr U8 39)) ;;
       '(temp_4678 : int8) ←
        (secret (@repr U8 74)) ;;
       '(temp_4680 : int8) ←
        (secret (@repr U8 14)) ;;
       '(temp_4682 : int8) ←
        (secret (@repr U8 160)) ;;
       '(temp_4684 : int8) ←
        (secret (@repr U8 176)) ;;
       '(temp_4686 : field_element_t) ←
        (nat_mod_from_byte_seq_be (seq_from_list _ [
              temp_4622;
              temp_4624;
              temp_4626;
              temp_4628;
              temp_4630;
              temp_4632;
              temp_4634;
              temp_4636;
              temp_4638;
              temp_4640;
              temp_4642;
              temp_4644;
              temp_4646;
              temp_4648;
              temp_4650;
              temp_4652;
              temp_4654;
              temp_4656;
              temp_4658;
              temp_4660;
              temp_4662;
              temp_4664;
              temp_4666;
              temp_4668;
              temp_4670;
              temp_4672;
              temp_4674;
              temp_4676;
              temp_4678;
              temp_4680;
              temp_4682;
              temp_4684
            ])) ;;
      @ret (field_element_t) (temp_4686) } : code (fset.fset0) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_sqrt_m1 : package _ _ _ :=
  (sqrt_m1).
Fail Next Obligation.


Notation "'invsqrt_a_minus_d_inp'" := (
  unit_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'invsqrt_a_minus_d_out'" := (
  field_element_t : choice_type) (in custom pack_type at level 2).
Definition INVSQRT_A_MINUS_D : nat :=
  (4754).
Program Definition invsqrt_a_minus_d
   : package (fset.fset0) [interface] [interface
  #val #[ INVSQRT_A_MINUS_D ] : invsqrt_a_minus_d_inp → invsqrt_a_minus_d_out
  ] :=
  (
    [package #def #[ INVSQRT_A_MINUS_D ] (temp_inp : invsqrt_a_minus_d_inp) : invsqrt_a_minus_d_out { 
    ({ code  '(temp_4689 : int8) ←
        (secret (@repr U8 120)) ;;
       '(temp_4691 : int8) ←
        (secret (@repr U8 108)) ;;
       '(temp_4693 : int8) ←
        (secret (@repr U8 137)) ;;
       '(temp_4695 : int8) ←
        (secret (@repr U8 5)) ;;
       '(temp_4697 : int8) ←
        (secret (@repr U8 207)) ;;
       '(temp_4699 : int8) ←
        (secret (@repr U8 175)) ;;
       '(temp_4701 : int8) ←
        (secret (@repr U8 252)) ;;
       '(temp_4703 : int8) ←
        (secret (@repr U8 162)) ;;
       '(temp_4705 : int8) ←
        (secret (@repr U8 22)) ;;
       '(temp_4707 : int8) ←
        (secret (@repr U8 194)) ;;
       '(temp_4709 : int8) ←
        (secret (@repr U8 123)) ;;
       '(temp_4711 : int8) ←
        (secret (@repr U8 145)) ;;
       '(temp_4713 : int8) ←
        (secret (@repr U8 254)) ;;
       '(temp_4715 : int8) ←
        (secret (@repr U8 1)) ;;
       '(temp_4717 : int8) ←
        (secret (@repr U8 216)) ;;
       '(temp_4719 : int8) ←
        (secret (@repr U8 64)) ;;
       '(temp_4721 : int8) ←
        (secret (@repr U8 157)) ;;
       '(temp_4723 : int8) ←
        (secret (@repr U8 47)) ;;
       '(temp_4725 : int8) ←
        (secret (@repr U8 22)) ;;
       '(temp_4727 : int8) ←
        (secret (@repr U8 23)) ;;
       '(temp_4729 : int8) ←
        (secret (@repr U8 90)) ;;
       '(temp_4731 : int8) ←
        (secret (@repr U8 65)) ;;
       '(temp_4733 : int8) ←
        (secret (@repr U8 114)) ;;
       '(temp_4735 : int8) ←
        (secret (@repr U8 190)) ;;
       '(temp_4737 : int8) ←
        (secret (@repr U8 153)) ;;
       '(temp_4739 : int8) ←
        (secret (@repr U8 200)) ;;
       '(temp_4741 : int8) ←
        (secret (@repr U8 253)) ;;
       '(temp_4743 : int8) ←
        (secret (@repr U8 170)) ;;
       '(temp_4745 : int8) ←
        (secret (@repr U8 128)) ;;
       '(temp_4747 : int8) ←
        (secret (@repr U8 93)) ;;
       '(temp_4749 : int8) ←
        (secret (@repr U8 64)) ;;
       '(temp_4751 : int8) ←
        (secret (@repr U8 234)) ;;
       '(temp_4753 : field_element_t) ←
        (nat_mod_from_byte_seq_be (seq_from_list _ [
              temp_4689;
              temp_4691;
              temp_4693;
              temp_4695;
              temp_4697;
              temp_4699;
              temp_4701;
              temp_4703;
              temp_4705;
              temp_4707;
              temp_4709;
              temp_4711;
              temp_4713;
              temp_4715;
              temp_4717;
              temp_4719;
              temp_4721;
              temp_4723;
              temp_4725;
              temp_4727;
              temp_4729;
              temp_4731;
              temp_4733;
              temp_4735;
              temp_4737;
              temp_4739;
              temp_4741;
              temp_4743;
              temp_4745;
              temp_4747;
              temp_4749;
              temp_4751
            ])) ;;
      @ret (field_element_t) (temp_4753) } : code (fset.fset0) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_invsqrt_a_minus_d : package _ _ _ :=
  (invsqrt_a_minus_d).
Fail Next Obligation.


Notation "'sqrt_ad_minus_one_inp'" := (
  unit_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'sqrt_ad_minus_one_out'" := (
  field_element_t : choice_type) (in custom pack_type at level 2).
Definition SQRT_AD_MINUS_ONE : nat :=
  (4821).
Program Definition sqrt_ad_minus_one
   : package (fset.fset0) [interface] [interface
  #val #[ SQRT_AD_MINUS_ONE ] : sqrt_ad_minus_one_inp → sqrt_ad_minus_one_out
  ] :=
  (
    [package #def #[ SQRT_AD_MINUS_ONE ] (temp_inp : sqrt_ad_minus_one_inp) : sqrt_ad_minus_one_out { 
    ({ code  '(temp_4756 : int8) ←
        (secret (@repr U8 55)) ;;
       '(temp_4758 : int8) ←
        (secret (@repr U8 105)) ;;
       '(temp_4760 : int8) ←
        (secret (@repr U8 49)) ;;
       '(temp_4762 : int8) ←
        (secret (@repr U8 191)) ;;
       '(temp_4764 : int8) ←
        (secret (@repr U8 43)) ;;
       '(temp_4766 : int8) ←
        (secret (@repr U8 131)) ;;
       '(temp_4768 : int8) ←
        (secret (@repr U8 72)) ;;
       '(temp_4770 : int8) ←
        (secret (@repr U8 172)) ;;
       '(temp_4772 : int8) ←
        (secret (@repr U8 15)) ;;
       '(temp_4774 : int8) ←
        (secret (@repr U8 60)) ;;
       '(temp_4776 : int8) ←
        (secret (@repr U8 252)) ;;
       '(temp_4778 : int8) ←
        (secret (@repr U8 201)) ;;
       '(temp_4780 : int8) ←
        (secret (@repr U8 49)) ;;
       '(temp_4782 : int8) ←
        (secret (@repr U8 245)) ;;
       '(temp_4784 : int8) ←
        (secret (@repr U8 209)) ;;
       '(temp_4786 : int8) ←
        (secret (@repr U8 253)) ;;
       '(temp_4788 : int8) ←
        (secret (@repr U8 175)) ;;
       '(temp_4790 : int8) ←
        (secret (@repr U8 157)) ;;
       '(temp_4792 : int8) ←
        (secret (@repr U8 142)) ;;
       '(temp_4794 : int8) ←
        (secret (@repr U8 12)) ;;
       '(temp_4796 : int8) ←
        (secret (@repr U8 27)) ;;
       '(temp_4798 : int8) ←
        (secret (@repr U8 120)) ;;
       '(temp_4800 : int8) ←
        (secret (@repr U8 84)) ;;
       '(temp_4802 : int8) ←
        (secret (@repr U8 189)) ;;
       '(temp_4804 : int8) ←
        (secret (@repr U8 126)) ;;
       '(temp_4806 : int8) ←
        (secret (@repr U8 151)) ;;
       '(temp_4808 : int8) ←
        (secret (@repr U8 246)) ;;
       '(temp_4810 : int8) ←
        (secret (@repr U8 160)) ;;
       '(temp_4812 : int8) ←
        (secret (@repr U8 73)) ;;
       '(temp_4814 : int8) ←
        (secret (@repr U8 123)) ;;
       '(temp_4816 : int8) ←
        (secret (@repr U8 46)) ;;
       '(temp_4818 : int8) ←
        (secret (@repr U8 27)) ;;
       '(temp_4820 : field_element_t) ←
        (nat_mod_from_byte_seq_be (seq_from_list _ [
              temp_4756;
              temp_4758;
              temp_4760;
              temp_4762;
              temp_4764;
              temp_4766;
              temp_4768;
              temp_4770;
              temp_4772;
              temp_4774;
              temp_4776;
              temp_4778;
              temp_4780;
              temp_4782;
              temp_4784;
              temp_4786;
              temp_4788;
              temp_4790;
              temp_4792;
              temp_4794;
              temp_4796;
              temp_4798;
              temp_4800;
              temp_4802;
              temp_4804;
              temp_4806;
              temp_4808;
              temp_4810;
              temp_4812;
              temp_4814;
              temp_4816;
              temp_4818
            ])) ;;
      @ret (field_element_t) (temp_4820) } : code (fset.fset0) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_sqrt_ad_minus_one : package _ _ _ :=
  (sqrt_ad_minus_one).
Fail Next Obligation.


Notation "'one_minus_d_sq_inp'" := (
  unit_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'one_minus_d_sq_out'" := (
  field_element_t : choice_type) (in custom pack_type at level 2).
Definition ONE_MINUS_D_SQ : nat :=
  (4888).
Program Definition one_minus_d_sq
   : package (fset.fset0) [interface] [interface
  #val #[ ONE_MINUS_D_SQ ] : one_minus_d_sq_inp → one_minus_d_sq_out ] :=
  (
    [package #def #[ ONE_MINUS_D_SQ ] (temp_inp : one_minus_d_sq_inp) : one_minus_d_sq_out { 
    ({ code  '(temp_4823 : int8) ←
        (secret (@repr U8 2)) ;;
       '(temp_4825 : int8) ←
        (secret (@repr U8 144)) ;;
       '(temp_4827 : int8) ←
        (secret (@repr U8 114)) ;;
       '(temp_4829 : int8) ←
        (secret (@repr U8 168)) ;;
       '(temp_4831 : int8) ←
        (secret (@repr U8 178)) ;;
       '(temp_4833 : int8) ←
        (secret (@repr U8 179)) ;;
       '(temp_4835 : int8) ←
        (secret (@repr U8 224)) ;;
       '(temp_4837 : int8) ←
        (secret (@repr U8 215)) ;;
       '(temp_4839 : int8) ←
        (secret (@repr U8 153)) ;;
       '(temp_4841 : int8) ←
        (secret (@repr U8 148)) ;;
       '(temp_4843 : int8) ←
        (secret (@repr U8 171)) ;;
       '(temp_4845 : int8) ←
        (secret (@repr U8 221)) ;;
       '(temp_4847 : int8) ←
        (secret (@repr U8 190)) ;;
       '(temp_4849 : int8) ←
        (secret (@repr U8 112)) ;;
       '(temp_4851 : int8) ←
        (secret (@repr U8 223)) ;;
       '(temp_4853 : int8) ←
        (secret (@repr U8 228)) ;;
       '(temp_4855 : int8) ←
        (secret (@repr U8 44)) ;;
       '(temp_4857 : int8) ←
        (secret (@repr U8 129)) ;;
       '(temp_4859 : int8) ←
        (secret (@repr U8 161)) ;;
       '(temp_4861 : int8) ←
        (secret (@repr U8 56)) ;;
       '(temp_4863 : int8) ←
        (secret (@repr U8 205)) ;;
       '(temp_4865 : int8) ←
        (secret (@repr U8 94)) ;;
       '(temp_4867 : int8) ←
        (secret (@repr U8 53)) ;;
       '(temp_4869 : int8) ←
        (secret (@repr U8 15)) ;;
       '(temp_4871 : int8) ←
        (secret (@repr U8 226)) ;;
       '(temp_4873 : int8) ←
        (secret (@repr U8 124)) ;;
       '(temp_4875 : int8) ←
        (secret (@repr U8 9)) ;;
       '(temp_4877 : int8) ←
        (secret (@repr U8 193)) ;;
       '(temp_4879 : int8) ←
        (secret (@repr U8 148)) ;;
       '(temp_4881 : int8) ←
        (secret (@repr U8 95)) ;;
       '(temp_4883 : int8) ←
        (secret (@repr U8 193)) ;;
       '(temp_4885 : int8) ←
        (secret (@repr U8 118)) ;;
       '(temp_4887 : field_element_t) ←
        (nat_mod_from_byte_seq_be (seq_from_list _ [
              temp_4823;
              temp_4825;
              temp_4827;
              temp_4829;
              temp_4831;
              temp_4833;
              temp_4835;
              temp_4837;
              temp_4839;
              temp_4841;
              temp_4843;
              temp_4845;
              temp_4847;
              temp_4849;
              temp_4851;
              temp_4853;
              temp_4855;
              temp_4857;
              temp_4859;
              temp_4861;
              temp_4863;
              temp_4865;
              temp_4867;
              temp_4869;
              temp_4871;
              temp_4873;
              temp_4875;
              temp_4877;
              temp_4879;
              temp_4881;
              temp_4883;
              temp_4885
            ])) ;;
      @ret (field_element_t) (temp_4887) } : code (fset.fset0) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_one_minus_d_sq : package _ _ _ :=
  (one_minus_d_sq).
Fail Next Obligation.


Notation "'d_minus_one_sq_inp'" := (
  unit_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'d_minus_one_sq_out'" := (
  field_element_t : choice_type) (in custom pack_type at level 2).
Definition D_MINUS_ONE_SQ : nat :=
  (4955).
Program Definition d_minus_one_sq
   : package (fset.fset0) [interface] [interface
  #val #[ D_MINUS_ONE_SQ ] : d_minus_one_sq_inp → d_minus_one_sq_out ] :=
  (
    [package #def #[ D_MINUS_ONE_SQ ] (temp_inp : d_minus_one_sq_inp) : d_minus_one_sq_out { 
    ({ code  '(temp_4890 : int8) ←
        (secret (@repr U8 89)) ;;
       '(temp_4892 : int8) ←
        (secret (@repr U8 104)) ;;
       '(temp_4894 : int8) ←
        (secret (@repr U8 179)) ;;
       '(temp_4896 : int8) ←
        (secret (@repr U8 122)) ;;
       '(temp_4898 : int8) ←
        (secret (@repr U8 246)) ;;
       '(temp_4900 : int8) ←
        (secret (@repr U8 108)) ;;
       '(temp_4902 : int8) ←
        (secret (@repr U8 34)) ;;
       '(temp_4904 : int8) ←
        (secret (@repr U8 65)) ;;
       '(temp_4906 : int8) ←
        (secret (@repr U8 76)) ;;
       '(temp_4908 : int8) ←
        (secret (@repr U8 220)) ;;
       '(temp_4910 : int8) ←
        (secret (@repr U8 211)) ;;
       '(temp_4912 : int8) ←
        (secret (@repr U8 47)) ;;
       '(temp_4914 : int8) ←
        (secret (@repr U8 82)) ;;
       '(temp_4916 : int8) ←
        (secret (@repr U8 155)) ;;
       '(temp_4918 : int8) ←
        (secret (@repr U8 78)) ;;
       '(temp_4920 : int8) ←
        (secret (@repr U8 235)) ;;
       '(temp_4922 : int8) ←
        (secret (@repr U8 210)) ;;
       '(temp_4924 : int8) ←
        (secret (@repr U8 158)) ;;
       '(temp_4926 : int8) ←
        (secret (@repr U8 74)) ;;
       '(temp_4928 : int8) ←
        (secret (@repr U8 44)) ;;
       '(temp_4930 : int8) ←
        (secret (@repr U8 176)) ;;
       '(temp_4932 : int8) ←
        (secret (@repr U8 30)) ;;
       '(temp_4934 : int8) ←
        (secret (@repr U8 25)) ;;
       '(temp_4936 : int8) ←
        (secret (@repr U8 153)) ;;
       '(temp_4938 : int8) ←
        (secret (@repr U8 49)) ;;
       '(temp_4940 : int8) ←
        (secret (@repr U8 173)) ;;
       '(temp_4942 : int8) ←
        (secret (@repr U8 90)) ;;
       '(temp_4944 : int8) ←
        (secret (@repr U8 170)) ;;
       '(temp_4946 : int8) ←
        (secret (@repr U8 68)) ;;
       '(temp_4948 : int8) ←
        (secret (@repr U8 237)) ;;
       '(temp_4950 : int8) ←
        (secret (@repr U8 77)) ;;
       '(temp_4952 : int8) ←
        (secret (@repr U8 32)) ;;
       '(temp_4954 : field_element_t) ←
        (nat_mod_from_byte_seq_be (seq_from_list _ [
              temp_4890;
              temp_4892;
              temp_4894;
              temp_4896;
              temp_4898;
              temp_4900;
              temp_4902;
              temp_4904;
              temp_4906;
              temp_4908;
              temp_4910;
              temp_4912;
              temp_4914;
              temp_4916;
              temp_4918;
              temp_4920;
              temp_4922;
              temp_4924;
              temp_4926;
              temp_4928;
              temp_4930;
              temp_4932;
              temp_4934;
              temp_4936;
              temp_4938;
              temp_4940;
              temp_4942;
              temp_4944;
              temp_4946;
              temp_4948;
              temp_4950;
              temp_4952
            ])) ;;
      @ret (field_element_t) (temp_4954) } : code (fset.fset0) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_d_minus_one_sq : package _ _ _ :=
  (d_minus_one_sq).
Fail Next Obligation.


Notation "'base_point_encoded_inp'" := (
  unit_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'base_point_encoded_out'" := (
  ristretto_point_encoded_t : choice_type) (in custom pack_type at level 2).
Definition BASE_POINT_ENCODED : nat :=
  (5022).
Program Definition base_point_encoded
   : package (fset.fset0) [interface] [interface
  #val #[ BASE_POINT_ENCODED ] : base_point_encoded_inp → base_point_encoded_out
  ] :=
  (
    [package #def #[ BASE_POINT_ENCODED ] (temp_inp : base_point_encoded_inp) : base_point_encoded_out { 
    ({ code  '(temp_4957 : int8) ←
        (secret (@repr U8 226)) ;;
       '(temp_4959 : int8) ←
        (secret (@repr U8 242)) ;;
       '(temp_4961 : int8) ←
        (secret (@repr U8 174)) ;;
       '(temp_4963 : int8) ←
        (secret (@repr U8 10)) ;;
       '(temp_4965 : int8) ←
        (secret (@repr U8 106)) ;;
       '(temp_4967 : int8) ←
        (secret (@repr U8 188)) ;;
       '(temp_4969 : int8) ←
        (secret (@repr U8 78)) ;;
       '(temp_4971 : int8) ←
        (secret (@repr U8 113)) ;;
       '(temp_4973 : int8) ←
        (secret (@repr U8 168)) ;;
       '(temp_4975 : int8) ←
        (secret (@repr U8 132)) ;;
       '(temp_4977 : int8) ←
        (secret (@repr U8 169)) ;;
       '(temp_4979 : int8) ←
        (secret (@repr U8 97)) ;;
       '(temp_4981 : int8) ←
        (secret (@repr U8 197)) ;;
       '(temp_4983 : int8) ←
        (secret (@repr U8 0)) ;;
       '(temp_4985 : int8) ←
        (secret (@repr U8 81)) ;;
       '(temp_4987 : int8) ←
        (secret (@repr U8 95)) ;;
       '(temp_4989 : int8) ←
        (secret (@repr U8 88)) ;;
       '(temp_4991 : int8) ←
        (secret (@repr U8 227)) ;;
       '(temp_4993 : int8) ←
        (secret (@repr U8 11)) ;;
       '(temp_4995 : int8) ←
        (secret (@repr U8 106)) ;;
       '(temp_4997 : int8) ←
        (secret (@repr U8 165)) ;;
       '(temp_4999 : int8) ←
        (secret (@repr U8 130)) ;;
       '(temp_5001 : int8) ←
        (secret (@repr U8 221)) ;;
       '(temp_5003 : int8) ←
        (secret (@repr U8 141)) ;;
       '(temp_5005 : int8) ←
        (secret (@repr U8 182)) ;;
       '(temp_5007 : int8) ←
        (secret (@repr U8 166)) ;;
       '(temp_5009 : int8) ←
        (secret (@repr U8 89)) ;;
       '(temp_5011 : int8) ←
        (secret (@repr U8 69)) ;;
       '(temp_5013 : int8) ←
        (secret (@repr U8 224)) ;;
       '(temp_5015 : int8) ←
        (secret (@repr U8 141)) ;;
       '(temp_5017 : int8) ←
        (secret (@repr U8 45)) ;;
       '(temp_5019 : int8) ←
        (secret (@repr U8 118)) ;;
       '(temp_5021 : ristretto_point_encoded_t) ←
        (array_from_seq (32) (seq_from_list _ [
              temp_4957;
              temp_4959;
              temp_4961;
              temp_4963;
              temp_4965;
              temp_4967;
              temp_4969;
              temp_4971;
              temp_4973;
              temp_4975;
              temp_4977;
              temp_4979;
              temp_4981;
              temp_4983;
              temp_4985;
              temp_4987;
              temp_4989;
              temp_4991;
              temp_4993;
              temp_4995;
              temp_4997;
              temp_4999;
              temp_5001;
              temp_5003;
              temp_5005;
              temp_5007;
              temp_5009;
              temp_5011;
              temp_5013;
              temp_5015;
              temp_5017;
              temp_5019
            ])) ;;
      @ret (ristretto_point_encoded_t) (temp_5021) } : code (
        fset.fset0) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_base_point_encoded : package _ _ _ :=
  (base_point_encoded).
Fail Next Obligation.


Notation "'base_point_inp'" := (
  unit_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'base_point_out'" := (
  ristretto_point_t : choice_type) (in custom pack_type at level 2).
Definition BASE_POINT : nat :=
  (5029).
Program Definition base_point
   : package (fset.fset0) [interface
  #val #[ BASE_POINT_ENCODED ] : base_point_encoded_inp → base_point_encoded_out ;
  #val #[ DECODE ] : decode_inp → decode_out ] [interface
  #val #[ BASE_POINT ] : base_point_inp → base_point_out ] :=
  ([package #def #[ BASE_POINT ] (temp_inp : base_point_inp) : base_point_out { 
    #import {sig #[ BASE_POINT_ENCODED ] : base_point_encoded_inp → base_point_encoded_out } as base_point_encoded ;;
    let base_point_encoded := base_point_encoded tt in
    #import {sig #[ DECODE ] : decode_inp → decode_out } as decode ;;
    let decode := fun x_0 => decode (x_0) in
    ({ code  '(temp_5024 : ristretto_point_encoded_t) ←
        (base_point_encoded ) ;;
       '(temp_5026 : decode_result_t) ←
        (decode (temp_5024)) ;;
       temp_5028 ←
        (result_unwrap (temp_5026)) ;;
      @ret ((
          field_element_t '×
          field_element_t '×
          field_element_t '×
          field_element_t
        )) (temp_5028) } : code (fset.fset0) [interface
      #val #[ BASE_POINT_ENCODED ] : base_point_encoded_inp → base_point_encoded_out ;
      #val #[ DECODE ] : decode_inp → decode_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_base_point : package _ _ _ :=
  (seq_link base_point link_rest(package_base_point_encoded,package_decode)).
Fail Next Obligation.


Notation "'identity_point_inp'" := (
  unit_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'identity_point_out'" := (
  ristretto_point_t : choice_type) (in custom pack_type at level 2).
Definition IDENTITY_POINT : nat :=
  (5038).
Program Definition identity_point
   : package (fset.fset0) [interface #val #[ FE ] : fe_inp → fe_out
  ] [interface
  #val #[ IDENTITY_POINT ] : identity_point_inp → identity_point_out ] :=
  (
    [package #def #[ IDENTITY_POINT ] (temp_inp : identity_point_inp) : identity_point_out { 
    #import {sig #[ FE ] : fe_inp → fe_out } as fe ;;
    let fe := fun x_0 => fe (x_0) in
    ({ code  '(temp_5031 : field_element_t) ←
        (fe (usize 0)) ;;
       '(temp_5033 : field_element_t) ←
        (fe (usize 1)) ;;
       '(temp_5035 : field_element_t) ←
        (fe (usize 1)) ;;
       '(temp_5037 : field_element_t) ←
        (fe (usize 0)) ;;
      @ret ((
          field_element_t '×
          field_element_t '×
          field_element_t '×
          field_element_t
        )) (prod_ce(temp_5031, temp_5033, temp_5035, temp_5037)) } : code (
        fset.fset0) [interface #val #[ FE ] : fe_inp → fe_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_identity_point : package _ _ _ :=
  (seq_link identity_point link_rest(package_fe)).
Fail Next Obligation.


Notation "'fe_inp'" := (
  uint_size : choice_type) (in custom pack_type at level 2).
Notation "'fe_out'" := (
  field_element_t : choice_type) (in custom pack_type at level 2).
Definition FE : nat :=
  (5042).
Program Definition fe
   : package (fset.fset0) [interface] [interface
  #val #[ FE ] : fe_inp → fe_out ] :=
  ([package #def #[ FE ] (temp_inp : fe_inp) : fe_out { 
    let '(x_5039) := temp_inp : uint_size in
    ({ code  '(temp_5041 : field_element_t) ←
        (nat_mod_from_literal (
            0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed) (
            pub_u128 (x_5039))) ;;
      @ret (field_element_t) (temp_5041) } : code (fset.fset0) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_fe : package _ _ _ :=
  (fe).
Fail Next Obligation.

Definition res_5126_loc : ChoiceEqualityLocation :=
  ((bool_ChoiceEquality ; 5127%nat)).
Notation "'geq_p_inp'" := (
  seq uint8 : choice_type) (in custom pack_type at level 2).
Notation "'geq_p_out'" := (
  bool_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Definition GEQ_P : nat :=
  (5128).
Program Definition geq_p
   : package (CEfset ([res_5126_loc])) [interface] [interface
  #val #[ GEQ_P ] : geq_p_inp → geq_p_out ] :=
  ([package #def #[ GEQ_P ] (temp_inp : geq_p_inp) : geq_p_out { 
    let '(x_5112) := temp_inp : seq uint8 in
    ({ code  '(p_seq_5107 : seq uint8) ←
        ( '(temp_5044 : int8) ←
            (secret (@repr U8 237)) ;;
           '(temp_5046 : int8) ←
            (secret (@repr U8 255)) ;;
           '(temp_5048 : int8) ←
            (secret (@repr U8 255)) ;;
           '(temp_5050 : int8) ←
            (secret (@repr U8 255)) ;;
           '(temp_5052 : int8) ←
            (secret (@repr U8 255)) ;;
           '(temp_5054 : int8) ←
            (secret (@repr U8 255)) ;;
           '(temp_5056 : int8) ←
            (secret (@repr U8 255)) ;;
           '(temp_5058 : int8) ←
            (secret (@repr U8 255)) ;;
           '(temp_5060 : int8) ←
            (secret (@repr U8 255)) ;;
           '(temp_5062 : int8) ←
            (secret (@repr U8 255)) ;;
           '(temp_5064 : int8) ←
            (secret (@repr U8 255)) ;;
           '(temp_5066 : int8) ←
            (secret (@repr U8 255)) ;;
           '(temp_5068 : int8) ←
            (secret (@repr U8 255)) ;;
           '(temp_5070 : int8) ←
            (secret (@repr U8 255)) ;;
           '(temp_5072 : int8) ←
            (secret (@repr U8 255)) ;;
           '(temp_5074 : int8) ←
            (secret (@repr U8 255)) ;;
           '(temp_5076 : int8) ←
            (secret (@repr U8 255)) ;;
           '(temp_5078 : int8) ←
            (secret (@repr U8 255)) ;;
           '(temp_5080 : int8) ←
            (secret (@repr U8 255)) ;;
           '(temp_5082 : int8) ←
            (secret (@repr U8 255)) ;;
           '(temp_5084 : int8) ←
            (secret (@repr U8 255)) ;;
           '(temp_5086 : int8) ←
            (secret (@repr U8 255)) ;;
           '(temp_5088 : int8) ←
            (secret (@repr U8 255)) ;;
           '(temp_5090 : int8) ←
            (secret (@repr U8 255)) ;;
           '(temp_5092 : int8) ←
            (secret (@repr U8 255)) ;;
           '(temp_5094 : int8) ←
            (secret (@repr U8 255)) ;;
           '(temp_5096 : int8) ←
            (secret (@repr U8 255)) ;;
           '(temp_5098 : int8) ←
            (secret (@repr U8 255)) ;;
           '(temp_5100 : int8) ←
            (secret (@repr U8 255)) ;;
           '(temp_5102 : int8) ←
            (secret (@repr U8 255)) ;;
           '(temp_5104 : int8) ←
            (secret (@repr U8 255)) ;;
           '(temp_5106 : int8) ←
            (secret (@repr U8 127)) ;;
          ret (seq_from_list _ [
              temp_5044;
              temp_5046;
              temp_5048;
              temp_5050;
              temp_5052;
              temp_5054;
              temp_5056;
              temp_5058;
              temp_5060;
              temp_5062;
              temp_5064;
              temp_5066;
              temp_5068;
              temp_5070;
              temp_5072;
              temp_5074;
              temp_5076;
              temp_5078;
              temp_5080;
              temp_5082;
              temp_5084;
              temp_5086;
              temp_5088;
              temp_5090;
              temp_5092;
              temp_5094;
              temp_5096;
              temp_5098;
              temp_5100;
              temp_5102;
              temp_5104;
              temp_5106
            ])) ;;
       '(res_5126 : bool_ChoiceEquality) ←
          (ret ((true : bool_ChoiceEquality))) ;;
        #put res_5126_loc := res_5126 ;;
       '(temp_5109 : uint_size) ←
        (seq_len (p_seq_5107)) ;;
       '(res_5126 : (bool_ChoiceEquality)) ←
        (foldi' (usize 0) (temp_5109) res_5126 (L2 := CEfset ([res_5126_loc])) (
              I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (fun index_5110 res_5126 =>
            ({ code  '(x_index_5120 : int8) ←
                ( '(temp_5113 : uint8) ←
                    (seq_index (x_5112) (index_5110)) ;;
                   temp_5115 ←
                    (uint8_declassify (temp_5113)) ;;
                  ret (temp_5115)) ;;
               '(p_index_5121 : int8) ←
                ( '(temp_5117 : uint8) ←
                    (seq_index (p_seq_5107) (index_5110)) ;;
                   temp_5119 ←
                    (uint8_declassify (temp_5117)) ;;
                  ret (temp_5119)) ;;
               '(temp_5123 : bool_ChoiceEquality) ←
                ((x_index_5120) !=.? (p_index_5121)) ;;
               '(res_5126 : (bool_ChoiceEquality)) ←
                (if temp_5123:bool_ChoiceEquality
                  then (*not state*) (let temp_then :=  '(
                          res_5126 : bool_ChoiceEquality) ←
                        (( '(temp_5125 : bool_ChoiceEquality) ←
                              ((x_index_5120) >.? (p_index_5121)) ;;
                            ret (temp_5125))) ;;
                      #put res_5126_loc := res_5126 ;;
                    
                    @ret ((bool_ChoiceEquality)) (res_5126) in
                    ({ code temp_then } : code (CEfset (
                          [res_5126_loc])) [interface] _))
                  else @ret ((bool_ChoiceEquality)) (res_5126)) ;;
              
              @ret ((bool_ChoiceEquality)) (res_5126) } : code (CEfset (
                  [res_5126_loc])) [interface] _))) ;;
      
      @ret (bool_ChoiceEquality) (res_5126) } : code (CEfset (
          [res_5126_loc])) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_geq_p : package _ _ _ :=
  (geq_p).
Fail Next Obligation.


Notation "'is_negative_inp'" := (
  field_element_t : choice_type) (in custom pack_type at level 2).
Notation "'is_negative_out'" := (
  bool_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Definition IS_NEGATIVE : nat :=
  (5138).
Program Definition is_negative
   : package (fset.fset0) [interface #val #[ FE ] : fe_inp → fe_out
  ] [interface #val #[ IS_NEGATIVE ] : is_negative_inp → is_negative_out ] :=
  (
    [package #def #[ IS_NEGATIVE ] (temp_inp : is_negative_inp) : is_negative_out { 
    let '(e_5129) := temp_inp : field_element_t in
    #import {sig #[ FE ] : fe_inp → fe_out } as fe ;;
    let fe := fun x_0 => fe (x_0) in
    ({ code  '(temp_5131 : field_element_t) ←
        (fe (usize 2)) ;;
       '(temp_5133 : field_element_t) ←
        ((e_5129) rem (temp_5131)) ;;
       '(temp_5135 : field_element_t) ←
        (fe (usize 1)) ;;
       '(temp_5137 : bool_ChoiceEquality) ←
        ((temp_5133) =.? (temp_5135)) ;;
      @ret (bool_ChoiceEquality) (temp_5137) } : code (fset.fset0) [interface
      #val #[ FE ] : fe_inp → fe_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_is_negative : package _ _ _ :=
  (seq_link is_negative link_rest(package_fe)).
Fail Next Obligation.


Notation "'eq_inp'" := (
  field_element_t '× field_element_t : choice_type) (in custom pack_type at level 2).
Notation "'eq_out'" := (
  bool_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Definition EQ : nat :=
  (5143).
Program Definition eq
   : package (fset.fset0) [interface] [interface
  #val #[ EQ ] : eq_inp → eq_out ] :=
  ([package #def #[ EQ ] (temp_inp : eq_inp) : eq_out { 
    let '(u_5139 , v_5140) := temp_inp : field_element_t '× field_element_t in
    ({ code  '(temp_5142 : bool_ChoiceEquality) ←
        ((u_5139) =.? (v_5140)) ;;
      @ret (bool_ChoiceEquality) (temp_5142) } : code (
        fset.fset0) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_eq : package _ _ _ :=
  (eq).
Fail Next Obligation.


Notation "'select_inp'" := (
  field_element_t '× bool_ChoiceEquality '× field_element_t : choice_type) (in custom pack_type at level 2).
Notation "'select_out'" := (
  field_element_t : choice_type) (in custom pack_type at level 2).
Definition SELECT : nat :=
  (5147).
Program Definition select
   : package (fset.fset0) [interface] [interface
  #val #[ SELECT ] : select_inp → select_out ] :=
  ([package #def #[ SELECT ] (temp_inp : select_inp) : select_out { 
    let '(
      u_5145 , cond_5144 , v_5146) := temp_inp : field_element_t '× bool_ChoiceEquality '× field_element_t in
    ({ code @ret (field_element_t) ((if (
            cond_5144):bool_ChoiceEquality then (*inline*) (u_5145) else (
            v_5146))) } : code (fset.fset0) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_select : package _ _ _ :=
  (select).
Fail Next Obligation.


Notation "'neg_fe_inp'" := (
  field_element_t : choice_type) (in custom pack_type at level 2).
Notation "'neg_fe_out'" := (
  field_element_t : choice_type) (in custom pack_type at level 2).
Definition NEG_FE : nat :=
  (5153).
Program Definition neg_fe
   : package (fset.fset0) [interface #val #[ FE ] : fe_inp → fe_out
  ] [interface #val #[ NEG_FE ] : neg_fe_inp → neg_fe_out ] :=
  ([package #def #[ NEG_FE ] (temp_inp : neg_fe_inp) : neg_fe_out { 
    let '(u_5150) := temp_inp : field_element_t in
    #import {sig #[ FE ] : fe_inp → fe_out } as fe ;;
    let fe := fun x_0 => fe (x_0) in
    ({ code  '(temp_5149 : field_element_t) ←
        (fe (usize 0)) ;;
       '(temp_5152 : field_element_t) ←
        ((temp_5149) -% (u_5150)) ;;
      @ret (field_element_t) (temp_5152) } : code (fset.fset0) [interface
      #val #[ FE ] : fe_inp → fe_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_neg_fe : package _ _ _ :=
  (seq_link neg_fe link_rest(package_fe)).
Fail Next Obligation.


Notation "'abs_inp'" := (
  field_element_t : choice_type) (in custom pack_type at level 2).
Notation "'abs_out'" := (
  field_element_t : choice_type) (in custom pack_type at level 2).
Definition ABS : nat :=
  (5161).
Program Definition abs
   : package (fset.fset0) [interface
  #val #[ IS_NEGATIVE ] : is_negative_inp → is_negative_out ;
  #val #[ NEG_FE ] : neg_fe_inp → neg_fe_out ;
  #val #[ SELECT ] : select_inp → select_out ] [interface
  #val #[ ABS ] : abs_inp → abs_out ] :=
  ([package #def #[ ABS ] (temp_inp : abs_inp) : abs_out { 
    let '(u_5154) := temp_inp : field_element_t in
    #import {sig #[ IS_NEGATIVE ] : is_negative_inp → is_negative_out } as is_negative ;;
    let is_negative := fun x_0 => is_negative (x_0) in
    #import {sig #[ NEG_FE ] : neg_fe_inp → neg_fe_out } as neg_fe ;;
    let neg_fe := fun x_0 => neg_fe (x_0) in
    #import {sig #[ SELECT ] : select_inp → select_out } as select ;;
    let select := fun x_0 x_1 x_2 => select (x_0,x_1,x_2) in
    ({ code  '(temp_5156 : field_element_t) ←
        (neg_fe (u_5154)) ;;
       '(temp_5158 : bool_ChoiceEquality) ←
        (is_negative (u_5154)) ;;
       '(temp_5160 : field_element_t) ←
        (select (temp_5156) (temp_5158) (u_5154)) ;;
      @ret (field_element_t) (temp_5160) } : code (fset.fset0) [interface
      #val #[ IS_NEGATIVE ] : is_negative_inp → is_negative_out ;
      #val #[ NEG_FE ] : neg_fe_inp → neg_fe_out ;
      #val #[ SELECT ] : select_inp → select_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_abs : package _ _ _ :=
  (seq_link abs link_rest(package_is_negative,package_neg_fe,package_select)).
Fail Next Obligation.

Definition r_5192_loc : ChoiceEqualityLocation :=
  ((field_element_t ; 5229%nat)).
Notation "'sqrt_ratio_m1_inp'" := (
  field_element_t '× field_element_t : choice_type) (in custom pack_type at level 2).
Notation "'sqrt_ratio_m1_out'" := ((bool_ChoiceEquality '× field_element_t
  ) : choice_type) (in custom pack_type at level 2).
Definition SQRT_RATIO_M1 : nat :=
  (5230).
Program Definition sqrt_ratio_m1
   : package (CEfset ([r_5192_loc])) [interface #val #[ P ] : p_inp → p_out ;
  #val #[ SQRT_M1 ] : sqrt_m1_inp → sqrt_m1_out ;
  #val #[ ABS ] : abs_inp → abs_out ; #val #[ EQ ] : eq_inp → eq_out ;
  #val #[ FE ] : fe_inp → fe_out ;
  #val #[ NEG_FE ] : neg_fe_inp → neg_fe_out ;
  #val #[ SELECT ] : select_inp → select_out ] [interface
  #val #[ SQRT_RATIO_M1 ] : sqrt_ratio_m1_inp → sqrt_ratio_m1_out ] :=
  (
    [package #def #[ SQRT_RATIO_M1 ] (temp_inp : sqrt_ratio_m1_inp) : sqrt_ratio_m1_out { 
    let '(u_5172 , v_5162) := temp_inp : field_element_t '× field_element_t in
    #import {sig #[ P ] : p_inp → p_out } as p ;;
    let p := p tt in
    #import {sig #[ SQRT_M1 ] : sqrt_m1_inp → sqrt_m1_out } as sqrt_m1 ;;
    let sqrt_m1 := sqrt_m1 tt in
    #import {sig #[ ABS ] : abs_inp → abs_out } as abs ;;
    let abs := fun x_0 => abs (x_0) in
    #import {sig #[ EQ ] : eq_inp → eq_out } as eq ;;
    let eq := fun x_0 x_1 => eq (x_0,x_1) in
    #import {sig #[ FE ] : fe_inp → fe_out } as fe ;;
    let fe := fun x_0 => fe (x_0) in
    #import {sig #[ NEG_FE ] : neg_fe_inp → neg_fe_out } as neg_fe ;;
    let neg_fe := fun x_0 => neg_fe (x_0) in
    #import {sig #[ SELECT ] : select_inp → select_out } as select ;;
    let select := fun x_0 x_1 x_2 => select (x_0,x_1,x_2) in
    ({ code  '(v3_5167 : field_element_t) ←
        ( '(temp_5164 : field_element_t) ←
            (nat_mod_pow (v_5162) (@repr U128 2)) ;;
           '(temp_5166 : field_element_t) ←
            ((temp_5164) *% (v_5162)) ;;
          ret (temp_5166)) ;;
       '(v7_5175 : field_element_t) ←
        ( '(temp_5169 : field_element_t) ←
            (nat_mod_pow (v3_5167) (@repr U128 2)) ;;
           '(temp_5171 : field_element_t) ←
            ((temp_5169) *% (v_5162)) ;;
          ret (temp_5171)) ;;
       '(r_5192 : field_element_t) ←
          ( '(temp_5174 : field_element_t) ←
              ((u_5172) *% (v3_5167)) ;;
             '(temp_5177 : field_element_t) ←
              ((u_5172) *% (v7_5175)) ;;
             '(temp_5179 : field_element_t) ←
              (p ) ;;
             '(temp_5181 : field_element_t) ←
              (fe (usize 5)) ;;
             '(temp_5183 : field_element_t) ←
              ((temp_5179) -% (temp_5181)) ;;
             '(temp_5185 : field_element_t) ←
              (fe (usize 8)) ;;
             '(temp_5187 : field_element_t) ←
              ((temp_5183) /% (temp_5185)) ;;
             temp_5189 ←
              (nat_mod_pow_felem (temp_5177) (temp_5187)) ;;
             '(temp_5191 : field_element_t) ←
              ((temp_5174) *% (temp_5189)) ;;
            ret (temp_5191)) ;;
        #put r_5192_loc := r_5192 ;;
       '(check_5197 : field_element_t) ←
        ( '(temp_5194 : field_element_t) ←
            (nat_mod_pow (r_5192) (@repr U128 2)) ;;
           '(temp_5196 : field_element_t) ←
            ((v_5162) *% (temp_5194)) ;;
          ret (temp_5196)) ;;
       '(correct_sign_sqrt_5225 : bool_ChoiceEquality) ←
        ( '(temp_5199 : bool_ChoiceEquality) ←
            (eq (check_5197) (u_5172)) ;;
          ret (temp_5199)) ;;
       '(flipped_sign_sqrt_5217 : bool_ChoiceEquality) ←
        ( '(temp_5201 : field_element_t) ←
            (neg_fe (u_5172)) ;;
           '(temp_5203 : bool_ChoiceEquality) ←
            (eq (check_5197) (temp_5201)) ;;
          ret (temp_5203)) ;;
       '(flipped_sign_sqrt_i_5218 : bool_ChoiceEquality) ←
        ( '(temp_5205 : field_element_t) ←
            (neg_fe (u_5172)) ;;
           '(temp_5207 : field_element_t) ←
            (sqrt_m1 ) ;;
           '(temp_5209 : field_element_t) ←
            ((temp_5205) *% (temp_5207)) ;;
           '(temp_5211 : bool_ChoiceEquality) ←
            (eq (check_5197) (temp_5209)) ;;
          ret (temp_5211)) ;;
       '(r_prime_5216 : field_element_t) ←
        ( '(temp_5213 : field_element_t) ←
            (sqrt_m1 ) ;;
           '(temp_5215 : field_element_t) ←
            ((temp_5213) *% (r_5192)) ;;
          ret (temp_5215)) ;;
       '(r_5192 : field_element_t) ←
          (( '(temp_5220 : bool_ChoiceEquality) ←
                ((flipped_sign_sqrt_5217) || (flipped_sign_sqrt_i_5218)) ;;
               '(temp_5222 : field_element_t) ←
                (select (r_prime_5216) (temp_5220) (r_5192)) ;;
              ret (temp_5222))) ;;
        #put r_5192_loc := r_5192 ;;
      
       '(r_5192 : field_element_t) ←
          (( '(temp_5224 : field_element_t) ←
                (abs (r_5192)) ;;
              ret (temp_5224))) ;;
        #put r_5192_loc := r_5192 ;;
      
       '(was_square_5228 : bool_ChoiceEquality) ←
        ( '(temp_5227 : bool_ChoiceEquality) ←
            ((correct_sign_sqrt_5225) || (flipped_sign_sqrt_5217)) ;;
          ret (temp_5227)) ;;
      @ret ((bool_ChoiceEquality '× field_element_t)) (prod_ce(
          was_square_5228,
          r_5192
        )) } : code (CEfset ([r_5192_loc])) [interface
      #val #[ P ] : p_inp → p_out ;
      #val #[ SQRT_M1 ] : sqrt_m1_inp → sqrt_m1_out ;
      #val #[ ABS ] : abs_inp → abs_out ; #val #[ EQ ] : eq_inp → eq_out ;
      #val #[ FE ] : fe_inp → fe_out ;
      #val #[ NEG_FE ] : neg_fe_inp → neg_fe_out ;
      #val #[ SELECT ] : select_inp → select_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_sqrt_ratio_m1 : package _ _ _ :=
  (seq_link sqrt_ratio_m1 link_rest(
      package_p,package_sqrt_m1,package_abs,package_eq,package_fe,package_neg_fe,package_select)).
Fail Next Obligation.

Definition s_5267_loc : ChoiceEqualityLocation :=
  ((field_element_t ; 5324%nat)).
Notation "'map_inp'" := (
  field_element_t : choice_type) (in custom pack_type at level 2).
Notation "'map_out'" := (
  ristretto_point_t : choice_type) (in custom pack_type at level 2).
Definition MAP : nat :=
  (5325).
Program Definition map
   : package (CEfset ([s_5267_loc])) [interface #val #[ D ] : d_inp → d_out ;
  #val #[ D_MINUS_ONE_SQ ] : d_minus_one_sq_inp → d_minus_one_sq_out ;
  #val #[ ONE_MINUS_D_SQ ] : one_minus_d_sq_inp → one_minus_d_sq_out ;
  #val #[ SQRT_AD_MINUS_ONE ] : sqrt_ad_minus_one_inp → sqrt_ad_minus_one_out ;
  #val #[ SQRT_M1 ] : sqrt_m1_inp → sqrt_m1_out ;
  #val #[ ABS ] : abs_inp → abs_out ; #val #[ FE ] : fe_inp → fe_out ;
  #val #[ NEG_FE ] : neg_fe_inp → neg_fe_out ;
  #val #[ SELECT ] : select_inp → select_out ;
  #val #[ SQRT_RATIO_M1 ] : sqrt_ratio_m1_inp → sqrt_ratio_m1_out ] [interface
  #val #[ MAP ] : map_inp → map_out ] :=
  ([package #def #[ MAP ] (temp_inp : map_inp) : map_out { 
    let '(t_5238) := temp_inp : field_element_t in
    #import {sig #[ D ] : d_inp → d_out } as d ;;
    let d := d tt in
    #import {sig #[ D_MINUS_ONE_SQ ] : d_minus_one_sq_inp → d_minus_one_sq_out } as d_minus_one_sq ;;
    let d_minus_one_sq := d_minus_one_sq tt in
    #import {sig #[ ONE_MINUS_D_SQ ] : one_minus_d_sq_inp → one_minus_d_sq_out } as one_minus_d_sq ;;
    let one_minus_d_sq := one_minus_d_sq tt in
    #import {sig #[ SQRT_AD_MINUS_ONE ] : sqrt_ad_minus_one_inp → sqrt_ad_minus_one_out } as sqrt_ad_minus_one ;;
    let sqrt_ad_minus_one := sqrt_ad_minus_one tt in
    #import {sig #[ SQRT_M1 ] : sqrt_m1_inp → sqrt_m1_out } as sqrt_m1 ;;
    let sqrt_m1 := sqrt_m1 tt in
    #import {sig #[ ABS ] : abs_inp → abs_out } as abs ;;
    let abs := fun x_0 => abs (x_0) in
    #import {sig #[ FE ] : fe_inp → fe_out } as fe ;;
    let fe := fun x_0 => fe (x_0) in
    #import {sig #[ NEG_FE ] : neg_fe_inp → neg_fe_out } as neg_fe ;;
    let neg_fe := fun x_0 => neg_fe (x_0) in
    #import {sig #[ SELECT ] : select_inp → select_out } as select ;;
    let select := fun x_0 x_1 x_2 => select (x_0,x_1,x_2) in
    #import {sig #[ SQRT_RATIO_M1 ] : sqrt_ratio_m1_inp → sqrt_ratio_m1_out } as sqrt_ratio_m1 ;;
    let sqrt_ratio_m1 := fun x_0 x_1 => sqrt_ratio_m1 (x_0,x_1) in
    ({ code  '(one_5233 : field_element_t) ←
        ( '(temp_5232 : field_element_t) ←
            (fe (usize 1)) ;;
          ret (temp_5232)) ;;
       '(minus_one_5250 : field_element_t) ←
        ( '(temp_5235 : field_element_t) ←
            (neg_fe (one_5233)) ;;
          ret (temp_5235)) ;;
       '(r_5243 : field_element_t) ←
        ( '(temp_5237 : field_element_t) ←
            (sqrt_m1 ) ;;
           '(temp_5240 : field_element_t) ←
            (nat_mod_pow (t_5238) (@repr U128 2)) ;;
           '(temp_5242 : field_element_t) ←
            ((temp_5237) *% (temp_5240)) ;;
          ret (temp_5242)) ;;
       '(u_5263 : field_element_t) ←
        ( '(temp_5245 : field_element_t) ←
            ((r_5243) +% (one_5233)) ;;
           '(temp_5247 : field_element_t) ←
            (one_minus_d_sq ) ;;
           '(temp_5249 : field_element_t) ←
            ((temp_5245) *% (temp_5247)) ;;
          ret (temp_5249)) ;;
       '(v_5264 : field_element_t) ←
        ( '(temp_5252 : field_element_t) ←
            (d ) ;;
           '(temp_5254 : field_element_t) ←
            ((r_5243) *% (temp_5252)) ;;
           '(temp_5256 : field_element_t) ←
            ((minus_one_5250) -% (temp_5254)) ;;
           '(temp_5258 : field_element_t) ←
            (d ) ;;
           '(temp_5260 : field_element_t) ←
            ((r_5243) +% (temp_5258)) ;;
           '(temp_5262 : field_element_t) ←
            ((temp_5256) *% (temp_5260)) ;;
          ret (temp_5262)) ;;
       temp_5323 ←
        ( '(temp_5266 : (bool_ChoiceEquality '× field_element_t)) ←
            (sqrt_ratio_m1 (u_5263) (v_5264)) ;;
          ret (temp_5266)) ;;
      let '(was_square_5274, s_5267) :=
        (temp_5323) : (bool_ChoiceEquality '× field_element_t) in
       '(s_prime_5275 : field_element_t) ←
        ( '(temp_5269 : field_element_t) ←
            ((s_5267) *% (t_5238)) ;;
           '(temp_5271 : field_element_t) ←
            (abs (temp_5269)) ;;
           '(temp_5273 : field_element_t) ←
            (neg_fe (temp_5271)) ;;
          ret (temp_5273)) ;;
       '(s_5267 : field_element_t) ←
          (( '(temp_5277 : field_element_t) ←
                (select (s_5267) (was_square_5274) (s_prime_5275)) ;;
              ret (temp_5277))) ;;
        #put s_5267_loc := s_5267 ;;
      
       '(c_5280 : field_element_t) ←
        ( '(temp_5279 : field_element_t) ←
            (select (minus_one_5250) (was_square_5274) (r_5243)) ;;
          ret (temp_5279)) ;;
       '(n_5297 : field_element_t) ←
        ( '(temp_5282 : field_element_t) ←
            ((r_5243) -% (one_5233)) ;;
           '(temp_5284 : field_element_t) ←
            ((c_5280) *% (temp_5282)) ;;
           '(temp_5286 : field_element_t) ←
            (d_minus_one_sq ) ;;
           '(temp_5288 : field_element_t) ←
            ((temp_5284) *% (temp_5286)) ;;
           '(temp_5290 : field_element_t) ←
            ((temp_5288) -% (v_5264)) ;;
          ret (temp_5290)) ;;
       '(w0_5310 : field_element_t) ←
        ( '(temp_5292 : field_element_t) ←
            (fe (usize 2)) ;;
           '(temp_5294 : field_element_t) ←
            ((temp_5292) *% (s_5267)) ;;
           '(temp_5296 : field_element_t) ←
            ((temp_5294) *% (v_5264)) ;;
          ret (temp_5296)) ;;
       '(w1_5315 : field_element_t) ←
        ( '(temp_5299 : field_element_t) ←
            (sqrt_ad_minus_one ) ;;
           '(temp_5301 : field_element_t) ←
            ((n_5297) *% (temp_5299)) ;;
          ret (temp_5301)) ;;
       '(w2_5314 : field_element_t) ←
        ( '(temp_5303 : field_element_t) ←
            (nat_mod_pow (s_5267) (@repr U128 2)) ;;
           '(temp_5305 : field_element_t) ←
            ((one_5233) -% (temp_5303)) ;;
          ret (temp_5305)) ;;
       '(w3_5311 : field_element_t) ←
        ( '(temp_5307 : field_element_t) ←
            (nat_mod_pow (s_5267) (@repr U128 2)) ;;
           '(temp_5309 : field_element_t) ←
            ((one_5233) +% (temp_5307)) ;;
          ret (temp_5309)) ;;
       '(temp_5313 : field_element_t) ←
        ((w0_5310) *% (w3_5311)) ;;
       '(temp_5317 : field_element_t) ←
        ((w2_5314) *% (w1_5315)) ;;
       '(temp_5319 : field_element_t) ←
        ((w1_5315) *% (w3_5311)) ;;
       '(temp_5321 : field_element_t) ←
        ((w0_5310) *% (w2_5314)) ;;
      @ret ((
          field_element_t '×
          field_element_t '×
          field_element_t '×
          field_element_t
        )) (prod_ce(temp_5313, temp_5317, temp_5319, temp_5321)) } : code (
        CEfset ([s_5267_loc])) [interface #val #[ D ] : d_inp → d_out ;
      #val #[ D_MINUS_ONE_SQ ] : d_minus_one_sq_inp → d_minus_one_sq_out ;
      #val #[ ONE_MINUS_D_SQ ] : one_minus_d_sq_inp → one_minus_d_sq_out ;
      #val #[ SQRT_AD_MINUS_ONE ] : sqrt_ad_minus_one_inp → sqrt_ad_minus_one_out ;
      #val #[ SQRT_M1 ] : sqrt_m1_inp → sqrt_m1_out ;
      #val #[ ABS ] : abs_inp → abs_out ; #val #[ FE ] : fe_inp → fe_out ;
      #val #[ NEG_FE ] : neg_fe_inp → neg_fe_out ;
      #val #[ SELECT ] : select_inp → select_out ;
      #val #[ SQRT_RATIO_M1 ] : sqrt_ratio_m1_inp → sqrt_ratio_m1_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_map : package _ _ _ :=
  (seq_link map link_rest(
      package_d,package_d_minus_one_sq,package_one_minus_d_sq,package_sqrt_ad_minus_one,package_sqrt_m1,package_abs,package_fe,package_neg_fe,package_select,package_sqrt_ratio_m1)).
Fail Next Obligation.

Definition r0_bytes_5338_loc : ChoiceEqualityLocation :=
  ((seq int8 ; 5361%nat)).
Definition r1_bytes_5343_loc : ChoiceEqualityLocation :=
  ((seq int8 ; 5362%nat)).
Notation "'one_way_map_inp'" := (
  byte_string_t : choice_type) (in custom pack_type at level 2).
Notation "'one_way_map_out'" := (
  ristretto_point_t : choice_type) (in custom pack_type at level 2).
Definition ONE_WAY_MAP : nat :=
  (5363).
Program Definition one_way_map
   : package (CEfset ([r0_bytes_5338_loc ; r1_bytes_5343_loc])) [interface
  #val #[ ADD ] : add_inp → add_out ; #val #[ MAP ] : map_inp → map_out
  ] [interface #val #[ ONE_WAY_MAP ] : one_way_map_inp → one_way_map_out ] :=
  (
    [package #def #[ ONE_WAY_MAP ] (temp_inp : one_way_map_inp) : one_way_map_out { 
    let '(b_5326) := temp_inp : byte_string_t in
    #import {sig #[ ADD ] : add_inp → add_out } as add ;;
    let add := fun x_0 x_1 => add (x_0,x_1) in
    #import {sig #[ MAP ] : map_inp → map_out } as map ;;
    let map := fun x_0 => map (x_0) in
    ({ code  '(r0_bytes_5331 : seq uint8) ←
        ( '(temp_5328 : seq uint8) ←
            (array_slice (b_5326) (usize 0) (usize 32)) ;;
          ret (temp_5328)) ;;
       '(r1_bytes_5334 : seq uint8) ←
        ( '(temp_5330 : seq uint8) ←
            (array_slice (b_5326) (usize 32) (usize 32)) ;;
          ret (temp_5330)) ;;
       '(r0_bytes_5338 : seq int8) ←
          ( '(temp_5333 : seq uint8) ←
              (seq_declassify (r0_bytes_5331)) ;;
            ret (temp_5333)) ;;
        #put r0_bytes_5338_loc := r0_bytes_5338 ;;
       '(r1_bytes_5343 : seq int8) ←
          ( '(temp_5336 : seq uint8) ←
              (seq_declassify (r1_bytes_5334)) ;;
            ret (temp_5336)) ;;
        #put r1_bytes_5343_loc := r1_bytes_5343 ;;
       '(r0_bytes_5338 : seq int8) ←
        ( '(temp_5339 : int8) ←
            (seq_index (r0_bytes_5338) (usize 31)) ;;
           '(temp_5341 : int8) ←
            ((temp_5339) .% (@repr U8 128)) ;;
          ret (seq_upd r0_bytes_5338 (usize 31) (temp_5341))) ;;
      
       '(r1_bytes_5343 : seq int8) ←
        ( '(temp_5344 : int8) ←
            (seq_index (r1_bytes_5343) (usize 31)) ;;
           '(temp_5346 : int8) ←
            ((temp_5344) .% (@repr U8 128)) ;;
          ret (seq_upd r1_bytes_5343 (usize 31) (temp_5346))) ;;
      
       '(r0_5351 : field_element_t) ←
        ( temp_5348 ←
            (nat_mod_from_public_byte_seq_le (r0_bytes_5338)) ;;
          ret (temp_5348)) ;;
       '(r1_5354 : field_element_t) ←
        ( temp_5350 ←
            (nat_mod_from_public_byte_seq_le (r1_bytes_5343)) ;;
          ret (temp_5350)) ;;
       '(p1_5357 : (
            field_element_t '×
            field_element_t '×
            field_element_t '×
            field_element_t
          )) ←
        ( '(temp_5353 : ristretto_point_t) ←
            (map (r0_5351)) ;;
          ret (temp_5353)) ;;
       '(p2_5358 : (
            field_element_t '×
            field_element_t '×
            field_element_t '×
            field_element_t
          )) ←
        ( '(temp_5356 : ristretto_point_t) ←
            (map (r1_5354)) ;;
          ret (temp_5356)) ;;
       '(temp_5360 : ristretto_point_t) ←
        (add (p1_5357) (p2_5358)) ;;
      @ret (ristretto_point_t) (temp_5360) } : code (CEfset (
          [r0_bytes_5338_loc ; r1_bytes_5343_loc])) [interface
      #val #[ ADD ] : add_inp → add_out ; #val #[ MAP ] : map_inp → map_out
      ] _)
    }]).
Fail Next Obligation.
Program Definition package_one_way_map : package _ _ _ :=
  (seq_link one_way_map link_rest(package_add,package_map)).
Fail Next Obligation.

Definition y_5425_loc : ChoiceEqualityLocation :=
  ((field_element_t ; 5454%nat)).
Notation "'encode_inp'" := (
  ristretto_point_t : choice_type) (in custom pack_type at level 2).
Notation "'encode_out'" := (
  ristretto_point_encoded_t : choice_type) (in custom pack_type at level 2).
Definition ENCODE : nat :=
  (5455).
Program Definition encode
   : package (CEfset ([y_5425_loc])) [interface
  #val #[ INVSQRT_A_MINUS_D ] : invsqrt_a_minus_d_inp → invsqrt_a_minus_d_out ;
  #val #[ SQRT_M1 ] : sqrt_m1_inp → sqrt_m1_out ;
  #val #[ ABS ] : abs_inp → abs_out ; #val #[ FE ] : fe_inp → fe_out ;
  #val #[ IS_NEGATIVE ] : is_negative_inp → is_negative_out ;
  #val #[ NEG_FE ] : neg_fe_inp → neg_fe_out ;
  #val #[ SELECT ] : select_inp → select_out ;
  #val #[ SQRT_RATIO_M1 ] : sqrt_ratio_m1_inp → sqrt_ratio_m1_out ] [interface
  #val #[ ENCODE ] : encode_inp → encode_out ] :=
  ([package #def #[ ENCODE ] (temp_inp : encode_inp) : encode_out { 
    let '(u_5364) := temp_inp : ristretto_point_t in
    #import {sig #[ INVSQRT_A_MINUS_D ] : invsqrt_a_minus_d_inp → invsqrt_a_minus_d_out } as invsqrt_a_minus_d ;;
    let invsqrt_a_minus_d := invsqrt_a_minus_d tt in
    #import {sig #[ SQRT_M1 ] : sqrt_m1_inp → sqrt_m1_out } as sqrt_m1 ;;
    let sqrt_m1 := sqrt_m1 tt in
    #import {sig #[ ABS ] : abs_inp → abs_out } as abs ;;
    let abs := fun x_0 => abs (x_0) in
    #import {sig #[ FE ] : fe_inp → fe_out } as fe ;;
    let fe := fun x_0 => fe (x_0) in
    #import {sig #[ IS_NEGATIVE ] : is_negative_inp → is_negative_out } as is_negative ;;
    let is_negative := fun x_0 => is_negative (x_0) in
    #import {sig #[ NEG_FE ] : neg_fe_inp → neg_fe_out } as neg_fe ;;
    let neg_fe := fun x_0 => neg_fe (x_0) in
    #import {sig #[ SELECT ] : select_inp → select_out } as select ;;
    let select := fun x_0 x_1 x_2 => select (x_0,x_1,x_2) in
    #import {sig #[ SQRT_RATIO_M1 ] : sqrt_ratio_m1_inp → sqrt_ratio_m1_out } as sqrt_ratio_m1 ;;
    let sqrt_ratio_m1 := fun x_0 x_1 => sqrt_ratio_m1 (x_0,x_1) in
    ({ code  temp_5453 ←
        (ret (u_5364)) ;;
      let '(x0_5373, y0_5366, z0_5365, t0_5395) :=
        (temp_5453) : (
        field_element_t '×
        field_element_t '×
        field_element_t '×
        field_element_t
      ) in
       '(u1_5378 : field_element_t) ←
        ( '(temp_5368 : field_element_t) ←
            ((z0_5365) +% (y0_5366)) ;;
           '(temp_5370 : field_element_t) ←
            ((z0_5365) -% (y0_5366)) ;;
           '(temp_5372 : field_element_t) ←
            ((temp_5368) *% (temp_5370)) ;;
          ret (temp_5372)) ;;
       '(u2_5379 : field_element_t) ←
        ( '(temp_5375 : field_element_t) ←
            ((x0_5373) *% (y0_5366)) ;;
          ret (temp_5375)) ;;
       temp_5451 ←
        ( '(temp_5377 : field_element_t) ←
            (fe (usize 1)) ;;
           '(temp_5381 : field_element_t) ←
            (nat_mod_pow (u2_5379) (@repr U128 2)) ;;
           '(temp_5383 : field_element_t) ←
            ((u1_5378) *% (temp_5381)) ;;
           '(temp_5385 : (bool_ChoiceEquality '× field_element_t)) ←
            (sqrt_ratio_m1 (temp_5377) (temp_5383)) ;;
          ret (temp_5385)) ;;
      let '(_, invsqrt_5386) :=
        (temp_5451) : (bool_ChoiceEquality '× field_element_t) in
       '(den1_5391 : field_element_t) ←
        ( '(temp_5388 : field_element_t) ←
            ((invsqrt_5386) *% (u1_5378)) ;;
          ret (temp_5388)) ;;
       '(den2_5392 : field_element_t) ←
        ( '(temp_5390 : field_element_t) ←
            ((invsqrt_5386) *% (u2_5379)) ;;
          ret (temp_5390)) ;;
       '(z_inv_5410 : field_element_t) ←
        ( '(temp_5394 : field_element_t) ←
            ((den1_5391) *% (den2_5392)) ;;
           '(temp_5397 : field_element_t) ←
            ((temp_5394) *% (t0_5395)) ;;
          ret (temp_5397)) ;;
       '(ix0_5419 : field_element_t) ←
        ( '(temp_5399 : field_element_t) ←
            (sqrt_m1 ) ;;
           '(temp_5401 : field_element_t) ←
            ((x0_5373) *% (temp_5399)) ;;
          ret (temp_5401)) ;;
       '(iy0_5415 : field_element_t) ←
        ( '(temp_5403 : field_element_t) ←
            (sqrt_m1 ) ;;
           '(temp_5405 : field_element_t) ←
            ((y0_5366) *% (temp_5403)) ;;
          ret (temp_5405)) ;;
       '(enchanted_denominator_5422 : field_element_t) ←
        ( '(temp_5407 : field_element_t) ←
            (invsqrt_a_minus_d ) ;;
           '(temp_5409 : field_element_t) ←
            ((den1_5391) *% (temp_5407)) ;;
          ret (temp_5409)) ;;
       '(rotate_5416 : bool_ChoiceEquality) ←
        ( '(temp_5412 : field_element_t) ←
            ((t0_5395) *% (z_inv_5410)) ;;
           '(temp_5414 : bool_ChoiceEquality) ←
            (is_negative (temp_5412)) ;;
          ret (temp_5414)) ;;
       '(x_5428 : field_element_t) ←
        ( '(temp_5418 : field_element_t) ←
            (select (iy0_5415) (rotate_5416) (x0_5373)) ;;
          ret (temp_5418)) ;;
       '(y_5425 : field_element_t) ←
          ( '(temp_5421 : field_element_t) ←
              (select (ix0_5419) (rotate_5416) (y0_5366)) ;;
            ret (temp_5421)) ;;
        #put y_5425_loc := y_5425 ;;
       '(z_5436 : field_element_t) ←
        (ret (z0_5365)) ;;
       '(den_inv_5435 : field_element_t) ←
        ( '(temp_5424 : field_element_t) ←
            (select (enchanted_denominator_5422) (rotate_5416) (den2_5392)) ;;
          ret (temp_5424)) ;;
       '(y_5425 : field_element_t) ←
          (( '(temp_5427 : field_element_t) ←
                (neg_fe (y_5425)) ;;
               '(temp_5430 : field_element_t) ←
                ((x_5428) *% (z_inv_5410)) ;;
               '(temp_5432 : bool_ChoiceEquality) ←
                (is_negative (temp_5430)) ;;
               '(temp_5434 : field_element_t) ←
                (select (temp_5427) (temp_5432) (y_5425)) ;;
              ret (temp_5434))) ;;
        #put y_5425_loc := y_5425 ;;
      
       '(s_5445 : field_element_t) ←
        ( '(temp_5438 : field_element_t) ←
            ((z_5436) -% (y_5425)) ;;
           '(temp_5440 : field_element_t) ←
            ((den_inv_5435) *% (temp_5438)) ;;
           '(temp_5442 : field_element_t) ←
            (abs (temp_5440)) ;;
          ret (temp_5442)) ;;
       '(temp_5444 : ristretto_point_encoded_t) ←
        (array_new_ (default : uint8) (32)) ;;
       temp_5447 ←
        (nat_mod_to_byte_seq_le (s_5445)) ;;
       '(temp_5449 : ristretto_point_encoded_t) ←
        (array_update_start (temp_5444) (temp_5447)) ;;
      @ret (ristretto_point_encoded_t) (temp_5449) } : code (CEfset (
          [y_5425_loc])) [interface
      #val #[ INVSQRT_A_MINUS_D ] : invsqrt_a_minus_d_inp → invsqrt_a_minus_d_out ;
      #val #[ SQRT_M1 ] : sqrt_m1_inp → sqrt_m1_out ;
      #val #[ ABS ] : abs_inp → abs_out ; #val #[ FE ] : fe_inp → fe_out ;
      #val #[ IS_NEGATIVE ] : is_negative_inp → is_negative_out ;
      #val #[ NEG_FE ] : neg_fe_inp → neg_fe_out ;
      #val #[ SELECT ] : select_inp → select_out ;
      #val #[ SQRT_RATIO_M1 ] : sqrt_ratio_m1_inp → sqrt_ratio_m1_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_encode : package _ _ _ :=
  (seq_link encode link_rest(
      package_invsqrt_a_minus_d,package_sqrt_m1,package_abs,package_fe,package_is_negative,package_neg_fe,package_select,package_sqrt_ratio_m1)).
Fail Next Obligation.

Definition ret_5533_loc : ChoiceEqualityLocation :=
  (((result int8 ristretto_point_t) ; 5536%nat)).
Notation "'decode_inp'" := (
  ristretto_point_encoded_t : choice_type) (in custom pack_type at level 2).
Notation "'decode_out'" := (
  decode_result_t : choice_type) (in custom pack_type at level 2).
Definition DECODE : nat :=
  (5537).
Program Definition decode
   : package (CEfset ([ret_5533_loc])) [interface
  #val #[ D ] : d_inp → d_out ; #val #[ ABS ] : abs_inp → abs_out ;
  #val #[ FE ] : fe_inp → fe_out ; #val #[ GEQ_P ] : geq_p_inp → geq_p_out ;
  #val #[ IS_NEGATIVE ] : is_negative_inp → is_negative_out ;
  #val #[ NEG_FE ] : neg_fe_inp → neg_fe_out ;
  #val #[ SQRT_RATIO_M1 ] : sqrt_ratio_m1_inp → sqrt_ratio_m1_out ] [interface
  #val #[ DECODE ] : decode_inp → decode_out ] :=
  ([package #def #[ DECODE ] (temp_inp : decode_inp) : decode_out { 
    let '(u_5456) := temp_inp : ristretto_point_encoded_t in
    #import {sig #[ D ] : d_inp → d_out } as d ;;
    let d := d tt in
    #import {sig #[ ABS ] : abs_inp → abs_out } as abs ;;
    let abs := fun x_0 => abs (x_0) in
    #import {sig #[ FE ] : fe_inp → fe_out } as fe ;;
    let fe := fun x_0 => fe (x_0) in
    #import {sig #[ GEQ_P ] : geq_p_inp → geq_p_out } as geq_p ;;
    let geq_p := fun x_0 => geq_p (x_0) in
    #import {sig #[ IS_NEGATIVE ] : is_negative_inp → is_negative_out } as is_negative ;;
    let is_negative := fun x_0 => is_negative (x_0) in
    #import {sig #[ NEG_FE ] : neg_fe_inp → neg_fe_out } as neg_fe ;;
    let neg_fe := fun x_0 => neg_fe (x_0) in
    #import {sig #[ SQRT_RATIO_M1 ] : sqrt_ratio_m1_inp → sqrt_ratio_m1_out } as sqrt_ratio_m1 ;;
    let sqrt_ratio_m1 := fun x_0 x_1 => sqrt_ratio_m1 (x_0,x_1) in
    ({ code  '(ret_5533 : (result int8 ristretto_point_t)) ←
          (ret (@inr ristretto_point_t int8 (decoding_error_v))) ;;
        #put ret_5533_loc := ret_5533 ;;
       '(s_5465 : field_element_t) ←
        ( '(temp_5458 : seq uint8) ←
            (array_to_seq (u_5456)) ;;
           '(temp_5460 : field_element_t) ←
            (nat_mod_from_byte_seq_le (temp_5458)) ;;
          ret (temp_5460)) ;;
       temp_5462 ←
        (array_to_le_bytes (u_5456)) ;;
       '(temp_5464 : bool_ChoiceEquality) ←
        (geq_p (temp_5462)) ;;
       '(temp_5467 : bool_ChoiceEquality) ←
        (is_negative (s_5465)) ;;
       '(temp_5469 : bool_ChoiceEquality) ←
        ((negb (temp_5464)) && (negb (temp_5467))) ;;
       '(ret_5533 : ((result int8 ristretto_point_t))) ←
        (if temp_5469:bool_ChoiceEquality
          then (*not state*) (let temp_then :=  '(
                one_5474 : field_element_t) ←
              ( '(temp_5471 : field_element_t) ←
                  (fe (usize 1)) ;;
                ret (temp_5471)) ;;
             '(ss_5475 : field_element_t) ←
              ( '(temp_5473 : field_element_t) ←
                  (nat_mod_pow (s_5465) (@repr U128 2)) ;;
                ret (temp_5473)) ;;
             '(u1_5485 : field_element_t) ←
              ( '(temp_5477 : field_element_t) ←
                  ((one_5474) -% (ss_5475)) ;;
                ret (temp_5477)) ;;
             '(u2_5480 : field_element_t) ←
              ( '(temp_5479 : field_element_t) ←
                  ((one_5474) +% (ss_5475)) ;;
                ret (temp_5479)) ;;
             '(u2_sqr_5492 : field_element_t) ←
              ( '(temp_5482 : field_element_t) ←
                  (nat_mod_pow (u2_5480) (@repr U128 2)) ;;
                ret (temp_5482)) ;;
             '(v_5495 : field_element_t) ←
              ( '(temp_5484 : field_element_t) ←
                  (d ) ;;
                 '(temp_5487 : field_element_t) ←
                  (nat_mod_pow (u1_5485) (@repr U128 2)) ;;
                 '(temp_5489 : field_element_t) ←
                  ((temp_5484) *% (temp_5487)) ;;
                 '(temp_5491 : field_element_t) ←
                  (neg_fe (temp_5489)) ;;
                 '(temp_5494 : field_element_t) ←
                  ((temp_5491) -% (u2_sqr_5492)) ;;
                ret (temp_5494)) ;;
             temp_5535 ←
              ( '(temp_5497 : field_element_t) ←
                  ((v_5495) *% (u2_sqr_5492)) ;;
                 '(temp_5499 : (bool_ChoiceEquality '× field_element_t)) ←
                  (sqrt_ratio_m1 (one_5474) (temp_5497)) ;;
                ret (temp_5499)) ;;
            let '(was_square_5521, invsqrt_5500) :=
              (temp_5535) : (bool_ChoiceEquality '× field_element_t) in
             '(den_x_5503 : field_element_t) ←
              ( '(temp_5502 : field_element_t) ←
                  ((invsqrt_5500) *% (u2_5480)) ;;
                ret (temp_5502)) ;;
             '(den_y_5514 : field_element_t) ←
              ( '(temp_5505 : field_element_t) ←
                  ((invsqrt_5500) *% (den_x_5503)) ;;
                 '(temp_5507 : field_element_t) ←
                  ((temp_5505) *% (v_5495)) ;;
                ret (temp_5507)) ;;
             '(x_5517 : field_element_t) ←
              ( '(temp_5509 : field_element_t) ←
                  ((s_5465) +% (s_5465)) ;;
                 '(temp_5511 : field_element_t) ←
                  ((temp_5509) *% (den_x_5503)) ;;
                 '(temp_5513 : field_element_t) ←
                  (abs (temp_5511)) ;;
                ret (temp_5513)) ;;
             '(y_5518 : field_element_t) ←
              ( '(temp_5516 : field_element_t) ←
                  ((u1_5485) *% (den_y_5514)) ;;
                ret (temp_5516)) ;;
             '(t_5522 : field_element_t) ←
              ( '(temp_5520 : field_element_t) ←
                  ((x_5517) *% (y_5518)) ;;
                ret (temp_5520)) ;;
             '(temp_5524 : bool_ChoiceEquality) ←
              (is_negative (t_5522)) ;;
             '(temp_5526 : bool_ChoiceEquality) ←
              ((negb (was_square_5521)) || (temp_5524)) ;;
             '(temp_5528 : field_element_t) ←
              (fe (usize 0)) ;;
             '(temp_5530 : bool_ChoiceEquality) ←
              ((y_5518) =.? (temp_5528)) ;;
             '(temp_5532 : bool_ChoiceEquality) ←
              ((temp_5526) || (temp_5530)) ;;
             '(ret_5533 : ((result int8 ristretto_point_t))) ←
              (if negb (temp_5532):bool_ChoiceEquality
                then (*not state*) (let temp_then :=  '(ret_5533 : (
                          result int8 ristretto_point_t)) ←
                      ((ret (@inl ristretto_point_t int8 (prod_ce(
                                x_5517,
                                y_5518,
                                one_5474,
                                t_5522
                              ))))) ;;
                    #put ret_5533_loc := ret_5533 ;;
                  
                  @ret (((result int8 ristretto_point_t))) (ret_5533) in
                  ({ code temp_then } : code (CEfset (
                        [ret_5533_loc])) [interface] _))
                else @ret (((result int8 ristretto_point_t))) (ret_5533)) ;;
            
            @ret (((result int8 ristretto_point_t))) (ret_5533) in
            ({ code temp_then } : code (CEfset ([ret_5533_loc])) [interface
              #val #[ D ] : d_inp → d_out ;
              #val #[ ABS ] : abs_inp → abs_out ;
              #val #[ FE ] : fe_inp → fe_out ;
              #val #[ IS_NEGATIVE ] : is_negative_inp → is_negative_out ;
              #val #[ NEG_FE ] : neg_fe_inp → neg_fe_out ;
              #val #[ SQRT_RATIO_M1 ] : sqrt_ratio_m1_inp → sqrt_ratio_m1_out
              ] _))
          else @ret (((result int8 ristretto_point_t))) (ret_5533)) ;;
      
      @ret ((result int8 ristretto_point_t)) (ret_5533) } : code (CEfset (
          [ret_5533_loc])) [interface #val #[ D ] : d_inp → d_out ;
      #val #[ ABS ] : abs_inp → abs_out ; #val #[ FE ] : fe_inp → fe_out ;
      #val #[ GEQ_P ] : geq_p_inp → geq_p_out ;
      #val #[ IS_NEGATIVE ] : is_negative_inp → is_negative_out ;
      #val #[ NEG_FE ] : neg_fe_inp → neg_fe_out ;
      #val #[ SQRT_RATIO_M1 ] : sqrt_ratio_m1_inp → sqrt_ratio_m1_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_decode : package _ _ _ :=
  (seq_link decode link_rest(
      package_d,package_abs,package_fe,package_geq_p,package_is_negative,package_neg_fe,package_sqrt_ratio_m1)).
Fail Next Obligation.


Notation "'equals_inp'" := (
  ristretto_point_t '× ristretto_point_t : choice_type) (in custom pack_type at level 2).
Notation "'equals_out'" := (
  bool_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Definition EQUALS : nat :=
  (5562).
Program Definition equals
   : package (fset.fset0) [interface] [interface
  #val #[ EQUALS ] : equals_inp → equals_out ] :=
  ([package #def #[ EQUALS ] (temp_inp : equals_inp) : equals_out { 
    let '(
      u_5538 , v_5539) := temp_inp : ristretto_point_t '× ristretto_point_t in
    ({ code  temp_5561 ←
        (ret (u_5538)) ;;
      let '(x1_5540, y1_5545, _, _) :=
        (temp_5561) : (
        field_element_t '×
        field_element_t '×
        field_element_t '×
        field_element_t
      ) in
       temp_5559 ←
        (ret (v_5539)) ;;
      let '(x2_5544, y2_5541, _, _) :=
        (temp_5559) : (
        field_element_t '×
        field_element_t '×
        field_element_t '×
        field_element_t
      ) in
       '(temp_5543 : field_element_t) ←
        ((x1_5540) *% (y2_5541)) ;;
       '(temp_5547 : field_element_t) ←
        ((x2_5544) *% (y1_5545)) ;;
       '(temp_5549 : bool_ChoiceEquality) ←
        ((temp_5543) =.? (temp_5547)) ;;
       '(temp_5551 : field_element_t) ←
        ((y1_5545) *% (y2_5541)) ;;
       '(temp_5553 : field_element_t) ←
        ((x1_5540) *% (x2_5544)) ;;
       '(temp_5555 : bool_ChoiceEquality) ←
        ((temp_5551) =.? (temp_5553)) ;;
       '(temp_5557 : bool_ChoiceEquality) ←
        ((temp_5549) || (temp_5555)) ;;
      @ret (bool_ChoiceEquality) (temp_5557) } : code (
        fset.fset0) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_equals : package _ _ _ :=
  (equals).
Fail Next Obligation.


Notation "'add_inp'" := (
  ristretto_point_t '× ristretto_point_t : choice_type) (in custom pack_type at level 2).
Notation "'add_out'" := (
  ristretto_point_t : choice_type) (in custom pack_type at level 2).
Definition ADD : nat :=
  (5629).
Program Definition add
   : package (fset.fset0) [interface #val #[ FE ] : fe_inp → fe_out
  ] [interface #val #[ ADD ] : add_inp → add_out ] :=
  ([package #def #[ ADD ] (temp_inp : add_inp) : add_out { 
    let '(
      u_5563 , v_5564) := temp_inp : ristretto_point_t '× ristretto_point_t in
    #import {sig #[ FE ] : fe_inp → fe_out } as fe ;;
    let fe := fun x_0 => fe (x_0) in
    ({ code  temp_5628 ←
        (ret (u_5563)) ;;
      let '(x1_5566, y1_5565, z1_5583, t1_5591) :=
        (temp_5628) : (
        field_element_t '×
        field_element_t '×
        field_element_t '×
        field_element_t
      ) in
       temp_5626 ←
        (ret (v_5564)) ;;
      let '(x2_5570, y2_5569, z2_5594, t2_5586) :=
        (temp_5626) : (
        field_element_t '×
        field_element_t '×
        field_element_t '×
        field_element_t
      ) in
       '(a_5602 : field_element_t) ←
        ( '(temp_5568 : field_element_t) ←
            ((y1_5565) -% (x1_5566)) ;;
           '(temp_5572 : field_element_t) ←
            ((y2_5569) +% (x2_5570)) ;;
           '(temp_5574 : field_element_t) ←
            ((temp_5568) *% (temp_5572)) ;;
          ret (temp_5574)) ;;
       '(b_5601 : field_element_t) ←
        ( '(temp_5576 : field_element_t) ←
            ((y1_5565) +% (x1_5566)) ;;
           '(temp_5578 : field_element_t) ←
            ((y2_5569) -% (x2_5570)) ;;
           '(temp_5580 : field_element_t) ←
            ((temp_5576) *% (temp_5578)) ;;
          ret (temp_5580)) ;;
       '(c_5598 : field_element_t) ←
        ( '(temp_5582 : field_element_t) ←
            (fe (usize 2)) ;;
           '(temp_5585 : field_element_t) ←
            ((temp_5582) *% (z1_5583)) ;;
           '(temp_5588 : field_element_t) ←
            ((temp_5585) *% (t2_5586)) ;;
          ret (temp_5588)) ;;
       '(d_5597 : field_element_t) ←
        ( '(temp_5590 : field_element_t) ←
            (fe (usize 2)) ;;
           '(temp_5593 : field_element_t) ←
            ((temp_5590) *% (t1_5591)) ;;
           '(temp_5596 : field_element_t) ←
            ((temp_5593) *% (z2_5594)) ;;
          ret (temp_5596)) ;;
       '(e_5609 : field_element_t) ←
        ( '(temp_5600 : field_element_t) ←
            ((d_5597) +% (c_5598)) ;;
          ret (temp_5600)) ;;
       '(f_5610 : field_element_t) ←
        ( '(temp_5604 : field_element_t) ←
            ((b_5601) -% (a_5602)) ;;
          ret (temp_5604)) ;;
       '(g_5613 : field_element_t) ←
        ( '(temp_5606 : field_element_t) ←
            ((b_5601) +% (a_5602)) ;;
          ret (temp_5606)) ;;
       '(h_5614 : field_element_t) ←
        ( '(temp_5608 : field_element_t) ←
            ((d_5597) -% (c_5598)) ;;
          ret (temp_5608)) ;;
       '(x3_5621 : field_element_t) ←
        ( '(temp_5612 : field_element_t) ←
            ((e_5609) *% (f_5610)) ;;
          ret (temp_5612)) ;;
       '(y3_5622 : field_element_t) ←
        ( '(temp_5616 : field_element_t) ←
            ((g_5613) *% (h_5614)) ;;
          ret (temp_5616)) ;;
       '(t3_5624 : field_element_t) ←
        ( '(temp_5618 : field_element_t) ←
            ((e_5609) *% (h_5614)) ;;
          ret (temp_5618)) ;;
       '(z3_5623 : field_element_t) ←
        ( '(temp_5620 : field_element_t) ←
            ((f_5610) *% (g_5613)) ;;
          ret (temp_5620)) ;;
      @ret ((
          field_element_t '×
          field_element_t '×
          field_element_t '×
          field_element_t
        )) (prod_ce(x3_5621, y3_5622, z3_5623, t3_5624)) } : code (
        fset.fset0) [interface #val #[ FE ] : fe_inp → fe_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_add : package _ _ _ :=
  (seq_link add link_rest(package_fe)).
Fail Next Obligation.


Notation "'neg_inp'" := (
  ristretto_point_t : choice_type) (in custom pack_type at level 2).
Notation "'neg_out'" := (
  ristretto_point_t : choice_type) (in custom pack_type at level 2).
Definition NEG : nat :=
  (5641).
Program Definition neg
   : package (fset.fset0) [interface
  #val #[ NEG_FE ] : neg_fe_inp → neg_fe_out ] [interface
  #val #[ NEG ] : neg_inp → neg_out ] :=
  ([package #def #[ NEG ] (temp_inp : neg_inp) : neg_out { 
    let '(u_5630) := temp_inp : ristretto_point_t in
    #import {sig #[ NEG_FE ] : neg_fe_inp → neg_fe_out } as neg_fe ;;
    let neg_fe := fun x_0 => neg_fe (x_0) in
    ({ code  temp_5640 ←
        (ret (u_5630)) ;;
      let '(x1_5631, y1_5634, z1_5635, t1_5638) :=
        (temp_5640) : (
        field_element_t '×
        field_element_t '×
        field_element_t '×
        field_element_t
      ) in
       '(temp_5633 : field_element_t) ←
        (neg_fe (x1_5631)) ;;
       '(temp_5637 : field_element_t) ←
        (neg_fe (z1_5635)) ;;
      @ret ((
          field_element_t '×
          field_element_t '×
          field_element_t '×
          field_element_t
        )) (prod_ce(temp_5633, y1_5634, temp_5637, t1_5638)) } : code (
        fset.fset0) [interface #val #[ NEG_FE ] : neg_fe_inp → neg_fe_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_neg : package _ _ _ :=
  (seq_link neg link_rest(package_neg_fe)).
Fail Next Obligation.


Notation "'sub_inp'" := (
  ristretto_point_t '× ristretto_point_t : choice_type) (in custom pack_type at level 2).
Notation "'sub_out'" := (
  ristretto_point_t : choice_type) (in custom pack_type at level 2).
Definition SUB : nat :=
  (5648).
Program Definition sub
   : package (fset.fset0) [interface #val #[ ADD ] : add_inp → add_out ;
  #val #[ NEG ] : neg_inp → neg_out ] [interface
  #val #[ SUB ] : sub_inp → sub_out ] :=
  ([package #def #[ SUB ] (temp_inp : sub_inp) : sub_out { 
    let '(
      u_5642 , v_5643) := temp_inp : ristretto_point_t '× ristretto_point_t in
    #import {sig #[ ADD ] : add_inp → add_out } as add ;;
    let add := fun x_0 x_1 => add (x_0,x_1) in
    #import {sig #[ NEG ] : neg_inp → neg_out } as neg ;;
    let neg := fun x_0 => neg (x_0) in
    ({ code  '(temp_5645 : ristretto_point_t) ←
        (neg (v_5643)) ;;
       '(temp_5647 : ristretto_point_t) ←
        (add (u_5642) (temp_5645)) ;;
      @ret (ristretto_point_t) (temp_5647) } : code (fset.fset0) [interface
      #val #[ ADD ] : add_inp → add_out ; #val #[ NEG ] : neg_inp → neg_out
      ] _)
    }]).
Fail Next Obligation.
Program Definition package_sub : package _ _ _ :=
  (seq_link sub link_rest(package_add,package_neg)).
Fail Next Obligation.


Notation "'double_inp'" := (
  ristretto_point_t : choice_type) (in custom pack_type at level 2).
Notation "'double_out'" := (
  ristretto_point_t : choice_type) (in custom pack_type at level 2).
Definition DOUBLE : nat :=
  (5696).
Program Definition double
   : package (fset.fset0) [interface #val #[ FE ] : fe_inp → fe_out
  ] [interface #val #[ DOUBLE ] : double_inp → double_out ] :=
  ([package #def #[ DOUBLE ] (temp_inp : double_inp) : double_out { 
    let '(u_5649) := temp_inp : ristretto_point_t in
    #import {sig #[ FE ] : fe_inp → fe_out } as fe ;;
    let fe := fun x_0 => fe (x_0) in
    ({ code  temp_5695 ←
        (ret (u_5649)) ;;
      let '(x1_5650, y1_5653, z1_5658, _) :=
        (temp_5695) : (
        field_element_t '×
        field_element_t '×
        field_element_t '×
        field_element_t
      ) in
       '(a_5663 : field_element_t) ←
        ( '(temp_5652 : field_element_t) ←
            (nat_mod_pow (x1_5650) (@repr U128 2)) ;;
          ret (temp_5652)) ;;
       '(b_5664 : field_element_t) ←
        ( '(temp_5655 : field_element_t) ←
            (nat_mod_pow (y1_5653) (@repr U128 2)) ;;
          ret (temp_5655)) ;;
       '(c_5676 : field_element_t) ←
        ( '(temp_5657 : field_element_t) ←
            (fe (usize 2)) ;;
           '(temp_5660 : field_element_t) ←
            (nat_mod_pow (z1_5658) (@repr U128 2)) ;;
           '(temp_5662 : field_element_t) ←
            ((temp_5657) *% (temp_5660)) ;;
          ret (temp_5662)) ;;
       '(h_5667 : field_element_t) ←
        ( '(temp_5666 : field_element_t) ←
            ((a_5663) +% (b_5664)) ;;
          ret (temp_5666)) ;;
       '(e_5680 : field_element_t) ←
        ( '(temp_5669 : field_element_t) ←
            ((x1_5650) +% (y1_5653)) ;;
           '(temp_5671 : field_element_t) ←
            (nat_mod_pow (temp_5669) (@repr U128 2)) ;;
           '(temp_5673 : field_element_t) ←
            ((h_5667) -% (temp_5671)) ;;
          ret (temp_5673)) ;;
       '(g_5677 : field_element_t) ←
        ( '(temp_5675 : field_element_t) ←
            ((a_5663) -% (b_5664)) ;;
          ret (temp_5675)) ;;
       '(f_5681 : field_element_t) ←
        ( '(temp_5679 : field_element_t) ←
            ((c_5676) +% (g_5677)) ;;
          ret (temp_5679)) ;;
       '(x2_5690 : field_element_t) ←
        ( '(temp_5683 : field_element_t) ←
            ((e_5680) *% (f_5681)) ;;
          ret (temp_5683)) ;;
       '(y2_5691 : field_element_t) ←
        ( '(temp_5685 : field_element_t) ←
            ((g_5677) *% (h_5667)) ;;
          ret (temp_5685)) ;;
       '(t2_5693 : field_element_t) ←
        ( '(temp_5687 : field_element_t) ←
            ((e_5680) *% (h_5667)) ;;
          ret (temp_5687)) ;;
       '(z2_5692 : field_element_t) ←
        ( '(temp_5689 : field_element_t) ←
            ((f_5681) *% (g_5677)) ;;
          ret (temp_5689)) ;;
      @ret ((
          field_element_t '×
          field_element_t '×
          field_element_t '×
          field_element_t
        )) (prod_ce(x2_5690, y2_5691, z2_5692, t2_5693)) } : code (
        fset.fset0) [interface #val #[ FE ] : fe_inp → fe_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_double : package _ _ _ :=
  (seq_link double link_rest(package_fe)).
Fail Next Obligation.

Definition temp_5709_loc : ChoiceEqualityLocation :=
  (((field_element_t '× field_element_t '× field_element_t '× field_element_t
      ) ; 5716%nat)).
Definition res_5708_loc : ChoiceEqualityLocation :=
  (((field_element_t '× field_element_t '× field_element_t '× field_element_t
      ) ; 5717%nat)).
Notation "'mul_inp'" := (
  scalar_t '× ristretto_point_t : choice_type) (in custom pack_type at level 2).
Notation "'mul_out'" := (
  ristretto_point_t : choice_type) (in custom pack_type at level 2).
Definition MUL : nat :=
  (5718).
Program Definition mul
   : package (CEfset ([res_5708_loc ; temp_5709_loc])) [interface
  #val #[ IDENTITY_POINT ] : identity_point_inp → identity_point_out ;
  #val #[ ADD ] : add_inp → add_out ;
  #val #[ DOUBLE ] : double_inp → double_out ] [interface
  #val #[ MUL ] : mul_inp → mul_out ] :=
  ([package #def #[ MUL ] (temp_inp : mul_inp) : mul_out { 
    let '(k_5700 , p_5699) := temp_inp : scalar_t '× ristretto_point_t in
    #import {sig #[ IDENTITY_POINT ] : identity_point_inp → identity_point_out } as identity_point ;;
    let identity_point := identity_point tt in
    #import {sig #[ ADD ] : add_inp → add_out } as add ;;
    let add := fun x_0 x_1 => add (x_0,x_1) in
    #import {sig #[ DOUBLE ] : double_inp → double_out } as double ;;
    let double := fun x_0 => double (x_0) in
    ({ code  '(res_5708 : (
              field_element_t '×
              field_element_t '×
              field_element_t '×
              field_element_t
            )) ←
          ( '(temp_5698 : ristretto_point_t) ←
              (identity_point ) ;;
            ret (temp_5698)) ;;
        #put res_5708_loc := res_5708 ;;
       '(temp_5709 : (
              field_element_t '×
              field_element_t '×
              field_element_t '×
              field_element_t
            )) ←
          (ret (p_5699)) ;;
        #put temp_5709_loc := temp_5709 ;;
       temp_5715 ←
        (foldi' (usize 0) (usize 256) prod_ce(res_5708, temp_5709) (
              L2 := CEfset ([res_5708_loc ; temp_5709_loc])) (I2 := [interface
              #val #[ IDENTITY_POINT ] : identity_point_inp → identity_point_out ;
              #val #[ ADD ] : add_inp → add_out ;
              #val #[ DOUBLE ] : double_inp → double_out
              ]) (H_loc_incl := _) (H_opsig_incl := _) (fun i_5701 '(
              res_5708,
              temp_5709
            ) =>
            ({ code  temp_5703 ←
                (nat_mod_get_bit (k_5700) (i_5701)) ;;
               '(temp_5705 : scalar_t) ←
                (nat_mod_from_literal (
                    0x1000000000000000000000000000000014def9dea2f79cd65812631a5cf5d3ed) (
                    @repr U128 1)) ;;
               '(temp_5707 : bool_ChoiceEquality) ←
                ((temp_5703) =.? (temp_5705)) ;;
               '(res_5708 : (
                    (
                      field_element_t '×
                      field_element_t '×
                      field_element_t '×
                      field_element_t
                    )
                  )) ←
                (if temp_5707:bool_ChoiceEquality
                  then (*not state*) (let temp_then :=  '(res_5708 : (
                            field_element_t '×
                            field_element_t '×
                            field_element_t '×
                            field_element_t
                          )) ←
                        (( '(temp_5711 : ristretto_point_t) ←
                              (add (res_5708) (temp_5709)) ;;
                            ret (temp_5711))) ;;
                      #put res_5708_loc := res_5708 ;;
                    
                    @ret ((
                        (
                          field_element_t '×
                          field_element_t '×
                          field_element_t '×
                          field_element_t
                        )
                      )) (res_5708) in
                    ({ code temp_then } : code (CEfset (
                          [res_5708_loc ; temp_5709_loc])) [interface
                      #val #[ ADD ] : add_inp → add_out ] _))
                  else @ret ((
                      (
                        field_element_t '×
                        field_element_t '×
                        field_element_t '×
                        field_element_t
                      )
                    )) (res_5708)) ;;
              
               '(temp_5709 : (
                      field_element_t '×
                      field_element_t '×
                      field_element_t '×
                      field_element_t
                    )) ←
                  (( '(temp_5713 : ristretto_point_t) ←
                        (double (temp_5709)) ;;
                      ret (temp_5713))) ;;
                #put temp_5709_loc := temp_5709 ;;
              
              @ret ((
                  (
                    field_element_t '×
                    field_element_t '×
                    field_element_t '×
                    field_element_t
                  ) '×
                  (
                    field_element_t '×
                    field_element_t '×
                    field_element_t '×
                    field_element_t
                  )
                )) (prod_ce(res_5708, temp_5709)) } : code (CEfset (
                  [res_5708_loc ; temp_5709_loc])) [interface
              #val #[ ADD ] : add_inp → add_out ;
              #val #[ DOUBLE ] : double_inp → double_out ] _))) ;;
      let '(res_5708, temp_5709) :=
        (temp_5715) : (
        (
          field_element_t '×
          field_element_t '×
          field_element_t '×
          field_element_t
        ) '×
        (
          field_element_t '×
          field_element_t '×
          field_element_t '×
          field_element_t
        )
      ) in
      
      @ret ((
          field_element_t '×
          field_element_t '×
          field_element_t '×
          field_element_t
        )) (res_5708) } : code (CEfset (
          [res_5708_loc ; temp_5709_loc])) [interface
      #val #[ IDENTITY_POINT ] : identity_point_inp → identity_point_out ;
      #val #[ ADD ] : add_inp → add_out ;
      #val #[ DOUBLE ] : double_inp → double_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_mul : package _ _ _ :=
  (seq_link mul link_rest(package_identity_point,package_add,package_double)).
Fail Next Obligation.

