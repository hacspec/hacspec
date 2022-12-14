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


Definition block_size_v : uint_size :=
  usize 128.

Definition len_size_v : uint_size :=
  usize 16.

Definition k_size_v : uint_size :=
  usize 80.

Definition hash_size_v : uint_size :=
  ((usize 512) ./ (usize 8)).

Definition block_t := nseq (uint8) (block_size_v).

Definition op_table_type_t := nseq (uint_size) (usize 12).

Definition sha512_digest_t := nseq (uint8) (hash_size_v).

Definition round_constants_table_t := nseq (uint64) (k_size_v).

Definition hash_t := nseq (uint64) (usize 8).


Notation "'ch_inp'" :=(
  uint64 '× uint64 '× uint64 : choice_type) (in custom pack_type at level 2).
Notation "'ch_inp'" :=(
  uint64 '× uint64 '× uint64 : ChoiceEquality) (at level 2).
Notation "'ch_out'" :=(uint64 : choice_type) (in custom pack_type at level 2).
Notation "'ch_out'" :=(uint64 : ChoiceEquality) (at level 2).
Definition CH : nat :=
  2884.
Program Definition ch (x_2881 : uint64) (y_2882 : uint64) (z_2883 : uint64)
  : both (fset.fset0) [interface] (uint64) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (((
            lift_to_both0 x_2881) .& (lift_to_both0 y_2882)) .^ ((not (
              lift_to_both0 x_2881)) .& (lift_to_both0 z_2883)))
      ) : both (fset.fset0) [interface] (uint64)).
Fail Next Obligation.


Notation "'maj_inp'" :=(
  uint64 '× uint64 '× uint64 : choice_type) (in custom pack_type at level 2).
Notation "'maj_inp'" :=(
  uint64 '× uint64 '× uint64 : ChoiceEquality) (at level 2).
Notation "'maj_out'" :=(uint64 : choice_type) (in custom pack_type at level 2).
Notation "'maj_out'" :=(uint64 : ChoiceEquality) (at level 2).
Definition MAJ : nat :=
  2888.
Program Definition maj (x_2885 : uint64) (y_2886 : uint64) (z_2887 : uint64)
  : both (fset.fset0) [interface] (uint64) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (((
            lift_to_both0 x_2885) .& (lift_to_both0 y_2886)) .^ (((
              lift_to_both0 x_2885) .& (lift_to_both0 z_2887)) .^ ((
              lift_to_both0 y_2886) .& (lift_to_both0 z_2887))))
      ) : both (fset.fset0) [interface] (uint64)).
Fail Next Obligation.

Definition op_table_v : op_table_type_t :=
  array_from_list uint_size [
    (usize 28) : uint_size;
    (usize 34) : uint_size;
    (usize 39) : uint_size;
    (usize 14) : uint_size;
    (usize 18) : uint_size;
    (usize 41) : uint_size;
    (usize 1) : uint_size;
    (usize 8) : uint_size;
    (usize 7) : uint_size;
    (usize 19) : uint_size;
    (usize 61) : uint_size;
    (usize 6) : uint_size
  ].

Definition k_table_v : round_constants_table_t :=
  array_from_list uint64 [
    (secret (@repr U64 4794697086780616226)) : uint64;
    (secret (@repr U64 8158064640168781261)) : uint64;
    (secret (@repr U64 13096744586834688815)) : uint64;
    (secret (@repr U64 16840607885511220156)) : uint64;
    (secret (@repr U64 4131703408338449720)) : uint64;
    (secret (@repr U64 6480981068601479193)) : uint64;
    (secret (@repr U64 10538285296894168987)) : uint64;
    (secret (@repr U64 12329834152419229976)) : uint64;
    (secret (@repr U64 15566598209576043074)) : uint64;
    (secret (@repr U64 1334009975649890238)) : uint64;
    (secret (@repr U64 2608012711638119052)) : uint64;
    (secret (@repr U64 6128411473006802146)) : uint64;
    (secret (@repr U64 8268148722764581231)) : uint64;
    (secret (@repr U64 9286055187155687089)) : uint64;
    (secret (@repr U64 11230858885718282805)) : uint64;
    (secret (@repr U64 13951009754708518548)) : uint64;
    (secret (@repr U64 16472876342353939154)) : uint64;
    (secret (@repr U64 17275323862435702243)) : uint64;
    (secret (@repr U64 1135362057144423861)) : uint64;
    (secret (@repr U64 2597628984639134821)) : uint64;
    (secret (@repr U64 3308224258029322869)) : uint64;
    (secret (@repr U64 5365058923640841347)) : uint64;
    (secret (@repr U64 6679025012923562964)) : uint64;
    (secret (@repr U64 8573033837759648693)) : uint64;
    (secret (@repr U64 10970295158949994411)) : uint64;
    (secret (@repr U64 12119686244451234320)) : uint64;
    (secret (@repr U64 12683024718118986047)) : uint64;
    (secret (@repr U64 13788192230050041572)) : uint64;
    (secret (@repr U64 14330467153632333762)) : uint64;
    (secret (@repr U64 15395433587784984357)) : uint64;
    (secret (@repr U64 489312712824947311)) : uint64;
    (secret (@repr U64 1452737877330783856)) : uint64;
    (secret (@repr U64 2861767655752347644)) : uint64;
    (secret (@repr U64 3322285676063803686)) : uint64;
    (secret (@repr U64 5560940570517711597)) : uint64;
    (secret (@repr U64 5996557281743188959)) : uint64;
    (secret (@repr U64 7280758554555802590)) : uint64;
    (secret (@repr U64 8532644243296465576)) : uint64;
    (secret (@repr U64 9350256976987008742)) : uint64;
    (secret (@repr U64 10552545826968843579)) : uint64;
    (secret (@repr U64 11727347734174303076)) : uint64;
    (secret (@repr U64 12113106623233404929)) : uint64;
    (secret (@repr U64 14000437183269869457)) : uint64;
    (secret (@repr U64 14369950271660146224)) : uint64;
    (secret (@repr U64 15101387698204529176)) : uint64;
    (secret (@repr U64 15463397548674623760)) : uint64;
    (secret (@repr U64 17586052441742319658)) : uint64;
    (secret (@repr U64 1182934255886127544)) : uint64;
    (secret (@repr U64 1847814050463011016)) : uint64;
    (secret (@repr U64 2177327727835720531)) : uint64;
    (secret (@repr U64 2830643537854262169)) : uint64;
    (secret (@repr U64 3796741975233480872)) : uint64;
    (secret (@repr U64 4115178125766777443)) : uint64;
    (secret (@repr U64 5681478168544905931)) : uint64;
    (secret (@repr U64 6601373596472566643)) : uint64;
    (secret (@repr U64 7507060721942968483)) : uint64;
    (secret (@repr U64 8399075790359081724)) : uint64;
    (secret (@repr U64 8693463985226723168)) : uint64;
    (secret (@repr U64 9568029438360202098)) : uint64;
    (secret (@repr U64 10144078919501101548)) : uint64;
    (secret (@repr U64 10430055236837252648)) : uint64;
    (secret (@repr U64 11840083180663258601)) : uint64;
    (secret (@repr U64 13761210420658862357)) : uint64;
    (secret (@repr U64 14299343276471374635)) : uint64;
    (secret (@repr U64 14566680578165727644)) : uint64;
    (secret (@repr U64 15097957966210449927)) : uint64;
    (secret (@repr U64 16922976911328602910)) : uint64;
    (secret (@repr U64 17689382322260857208)) : uint64;
    (secret (@repr U64 500013540394364858)) : uint64;
    (secret (@repr U64 748580250866718886)) : uint64;
    (secret (@repr U64 1242879168328830382)) : uint64;
    (secret (@repr U64 1977374033974150939)) : uint64;
    (secret (@repr U64 2944078676154940804)) : uint64;
    (secret (@repr U64 3659926193048069267)) : uint64;
    (secret (@repr U64 4368137639120453308)) : uint64;
    (secret (@repr U64 4836135668995329356)) : uint64;
    (secret (@repr U64 5532061633213252278)) : uint64;
    (secret (@repr U64 6448918945643986474)) : uint64;
    (secret (@repr U64 6902733635092675308)) : uint64;
    (secret (@repr U64 7801388544844847127)) : uint64
  ].

Definition hash_init_v : hash_t :=
  array_from_list uint64 [
    (secret (@repr U64 7640891576956012808)) : uint64;
    (secret (@repr U64 13503953896175478587)) : uint64;
    (secret (@repr U64 4354685564936845355)) : uint64;
    (secret (@repr U64 11912009170470909681)) : uint64;
    (secret (@repr U64 5840696475078001361)) : uint64;
    (secret (@repr U64 11170449401992604703)) : uint64;
    (secret (@repr U64 2270897969802886507)) : uint64;
    (secret (@repr U64 6620516959819538809)) : uint64
  ].

Definition tmp_2889_loc : ChoiceEqualityLocation :=
  (uint64 ; 2890%nat).
Notation "'sigma_inp'" :=(
  uint64 '× uint_size '× uint_size : choice_type) (in custom pack_type at level 2).
Notation "'sigma_inp'" :=(
  uint64 '× uint_size '× uint_size : ChoiceEquality) (at level 2).
Notation "'sigma_out'" :=(
  uint64 : choice_type) (in custom pack_type at level 2).
Notation "'sigma_out'" :=(uint64 : ChoiceEquality) (at level 2).
Definition SIGMA : nat :=
  2894.
Program Definition sigma (x_2891 : uint64) (i_2892 : uint_size) (
    op_2893 : uint_size)
  : both (CEfset ([tmp_2889_loc])) [interface] (uint64) :=
  ((letbm tmp_2889 : uint64 loc( tmp_2889_loc ) :=
        uint64_rotate_right (lift_to_both0 x_2891) (array_index (op_table_v) (((
                lift_to_both0 (usize 3)) .* (lift_to_both0 i_2892)) .+ (
              lift_to_both0 (usize 2)))) in
      letb '(tmp_2889) :=
        if (lift_to_both0 op_2893) =.? (lift_to_both0 (
            usize 0)) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset ([tmp_2889_loc])) (L2 := CEfset (
            [tmp_2889_loc])) (I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
          letbm tmp_2889 loc( tmp_2889_loc ) :=
            (lift_to_both0 x_2891) shift_right (array_index (op_table_v) (((
                    lift_to_both0 (usize 3)) .* (lift_to_both0 i_2892)) .+ (
                  lift_to_both0 (usize 2)))) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 tmp_2889)
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          lift_to_both0 tmp_2889)
         in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (((uint64_rotate_right (
              lift_to_both0 x_2891) (array_index (op_table_v) ((lift_to_both0 (
                    usize 3)) .* (lift_to_both0 i_2892)))) .^ (
            uint64_rotate_right (lift_to_both0 x_2891) (array_index (
                op_table_v) (((lift_to_both0 (usize 3)) .* (
                    lift_to_both0 i_2892)) .+ (lift_to_both0 (usize 1)))))) .^ (
          lift_to_both0 tmp_2889))
      ) : both (CEfset ([tmp_2889_loc])) [interface] (uint64)).
Fail Next Obligation.

Definition s_2895_loc : ChoiceEqualityLocation :=
  (round_constants_table_t ; 2896%nat).
Notation "'schedule_inp'" :=(
  block_t : choice_type) (in custom pack_type at level 2).
Notation "'schedule_inp'" :=(block_t : ChoiceEquality) (at level 2).
Notation "'schedule_out'" :=(
  round_constants_table_t : choice_type) (in custom pack_type at level 2).
Notation "'schedule_out'" :=(
  round_constants_table_t : ChoiceEquality) (at level 2).
Definition SCHEDULE : nat :=
  2906.
Program Definition schedule (block_2897 : block_t)
  : both (CEfset ([tmp_2889_loc ; s_2895_loc])) [interface] (
    round_constants_table_t) :=
  ((letb b_2898 : seq uint64 :=
        array_to_be_uint64s (lift_to_both0 block_2897) in
      letbm s_2895 : round_constants_table_t loc( s_2895_loc ) :=
        array_new_ (default : uint64) (k_size_v) in
      letb s_2895 :=
        foldi_both' (lift_to_both0 (usize 0)) (lift_to_both0 k_size_v) s_2895 (
            L := (CEfset ([tmp_2889_loc ; s_2895_loc]))) (I := [interface]) (
            fun i_2899 s_2895 =>
            letb '(s_2895) :=
              if (lift_to_both0 i_2899) <.? (lift_to_both0 (
                  usize 16)) :bool_ChoiceEquality
              then lift_scope (L1 := CEfset ([s_2895_loc])) (L2 := CEfset (
                  [tmp_2889_loc ; s_2895_loc])) (I1 := [interface]) (
                I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
                letb s_2895 : round_constants_table_t :=
                  array_upd s_2895 (lift_to_both0 i_2899) (is_pure (seq_index (
                        b_2898) (lift_to_both0 i_2899))) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                  lift_to_both0 s_2895)
                )
              else  lift_scope (L1 := CEfset ([tmp_2889_loc ; s_2895_loc])) (
                L2 := CEfset ([tmp_2889_loc ; s_2895_loc])) (
                I1 := [interface]) (
                I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
                letb t16_2900 : uint64 :=
                  array_index (s_2895) ((lift_to_both0 i_2899) .- (
                      lift_to_both0 (usize 16))) in
                letb t15_2901 : uint64 :=
                  array_index (s_2895) ((lift_to_both0 i_2899) .- (
                      lift_to_both0 (usize 15))) in
                letb t7_2902 : uint64 :=
                  array_index (s_2895) ((lift_to_both0 i_2899) .- (
                      lift_to_both0 (usize 7))) in
                letb t2_2903 : uint64 :=
                  array_index (s_2895) ((lift_to_both0 i_2899) .- (
                      lift_to_both0 (usize 2))) in
                letb s1_2904 : uint64 :=
                  sigma (lift_to_both0 t2_2903) (lift_to_both0 (usize 3)) (
                    lift_to_both0 (usize 0)) in
                letb s0_2905 : uint64 :=
                  sigma (lift_to_both0 t15_2901) (lift_to_both0 (usize 2)) (
                    lift_to_both0 (usize 0)) in
                letb s_2895 : round_constants_table_t :=
                  array_upd s_2895 (lift_to_both0 i_2899) (is_pure ((((
                            lift_to_both0 s1_2904) .+ (
                            lift_to_both0 t7_2902)) .+ (
                          lift_to_both0 s0_2905)) .+ (
                        lift_to_both0 t16_2900))) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                  lift_to_both0 s_2895)
                ) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 s_2895)
            ) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 s_2895)
      ) : both (CEfset ([tmp_2889_loc ; s_2895_loc])) [interface] (
      round_constants_table_t)).
Fail Next Obligation.

Definition h_2907_loc : ChoiceEqualityLocation :=
  (hash_t ; 2908%nat).
Notation "'shuffle_inp'" :=(
  round_constants_table_t '× hash_t : choice_type) (in custom pack_type at level 2).
Notation "'shuffle_inp'" :=(
  round_constants_table_t '× hash_t : ChoiceEquality) (at level 2).
Notation "'shuffle_out'" :=(
  hash_t : choice_type) (in custom pack_type at level 2).
Notation "'shuffle_out'" :=(hash_t : ChoiceEquality) (at level 2).
Definition SHUFFLE : nat :=
  2922.
Program Definition shuffle (ws_2919 : round_constants_table_t) (
    hashi_2909 : hash_t)
  : both (CEfset ([tmp_2889_loc ; h_2907_loc])) [interface] (hash_t) :=
  ((letbm h_2907 : hash_t loc( h_2907_loc ) := lift_to_both0 hashi_2909 in
      letb h_2907 :=
        foldi_both' (lift_to_both0 (usize 0)) (lift_to_both0 k_size_v) h_2907 (
            L := (CEfset ([tmp_2889_loc ; h_2907_loc]))) (I := [interface]) (
            fun i_2910 h_2907 =>
            letb a0_2911 : uint64 :=
              array_index (h_2907) (lift_to_both0 (usize 0)) in
            letb b0_2912 : uint64 :=
              array_index (h_2907) (lift_to_both0 (usize 1)) in
            letb c0_2913 : uint64 :=
              array_index (h_2907) (lift_to_both0 (usize 2)) in
            letb d0_2914 : uint64 :=
              array_index (h_2907) (lift_to_both0 (usize 3)) in
            letb e0_2915 : uint64 :=
              array_index (h_2907) (lift_to_both0 (usize 4)) in
            letb f0_2916 : uint64 :=
              array_index (h_2907) (lift_to_both0 (usize 5)) in
            letb g0_2917 : uint64 :=
              array_index (h_2907) (lift_to_both0 (usize 6)) in
            letb h0_2918 : uint64 :=
              array_index (h_2907) (lift_to_both0 (usize 7)) in
            letb t1_2920 : uint64 :=
              ((((lift_to_both0 h0_2918) .+ (sigma (lift_to_both0 e0_2915) (
                        lift_to_both0 (usize 1)) (lift_to_both0 (
                          usize 1)))) .+ (ch (lift_to_both0 e0_2915) (
                      lift_to_both0 f0_2916) (lift_to_both0 g0_2917))) .+ (
                  array_index (k_table_v) (lift_to_both0 i_2910))) .+ (
                array_index (ws_2919) (lift_to_both0 i_2910)) in
            letb t2_2921 : uint64 :=
              (sigma (lift_to_both0 a0_2911) (lift_to_both0 (usize 0)) (
                  lift_to_both0 (usize 1))) .+ (maj (lift_to_both0 a0_2911) (
                  lift_to_both0 b0_2912) (lift_to_both0 c0_2913)) in
            letb h_2907 : hash_t :=
              array_upd h_2907 (lift_to_both0 (usize 0)) (is_pure ((
                    lift_to_both0 t1_2920) .+ (lift_to_both0 t2_2921))) in
            letb h_2907 : hash_t :=
              array_upd h_2907 (lift_to_both0 (usize 1)) (is_pure (
                  lift_to_both0 a0_2911)) in
            letb h_2907 : hash_t :=
              array_upd h_2907 (lift_to_both0 (usize 2)) (is_pure (
                  lift_to_both0 b0_2912)) in
            letb h_2907 : hash_t :=
              array_upd h_2907 (lift_to_both0 (usize 3)) (is_pure (
                  lift_to_both0 c0_2913)) in
            letb h_2907 : hash_t :=
              array_upd h_2907 (lift_to_both0 (usize 4)) (is_pure ((
                    lift_to_both0 d0_2914) .+ (lift_to_both0 t1_2920))) in
            letb h_2907 : hash_t :=
              array_upd h_2907 (lift_to_both0 (usize 5)) (is_pure (
                  lift_to_both0 e0_2915)) in
            letb h_2907 : hash_t :=
              array_upd h_2907 (lift_to_both0 (usize 6)) (is_pure (
                  lift_to_both0 f0_2916)) in
            letb h_2907 : hash_t :=
              array_upd h_2907 (lift_to_both0 (usize 7)) (is_pure (
                  lift_to_both0 g0_2917)) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 h_2907)
            ) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 h_2907)
      ) : both (CEfset ([tmp_2889_loc ; h_2907_loc])) [interface] (hash_t)).
Fail Next Obligation.

Definition h_2923_loc : ChoiceEqualityLocation :=
  (hash_t ; 2924%nat).
Notation "'compress_inp'" :=(
  block_t '× hash_t : choice_type) (in custom pack_type at level 2).
Notation "'compress_inp'" :=(block_t '× hash_t : ChoiceEquality) (at level 2).
Notation "'compress_out'" :=(
  hash_t : choice_type) (in custom pack_type at level 2).
Notation "'compress_out'" :=(hash_t : ChoiceEquality) (at level 2).
Definition COMPRESS : nat :=
  2929.
Program Definition compress (block_2925 : block_t) (h_in_2927 : hash_t)
  : both (CEfset (
      [tmp_2889_loc ; s_2895_loc ; h_2907_loc ; h_2923_loc])) [interface] (
    hash_t) :=
  ((letb s_2926 : round_constants_table_t :=
        schedule (lift_to_both0 block_2925) in
      letbm h_2923 : hash_t loc( h_2923_loc ) :=
        shuffle (lift_to_both0 s_2926) (lift_to_both0 h_in_2927) in
      letb h_2923 :=
        foldi_both' (lift_to_both0 (usize 0)) (lift_to_both0 (usize 8)) h_2923 (
            L := (CEfset (
                [tmp_2889_loc ; s_2895_loc ; h_2907_loc ; h_2923_loc]))) (
            I := [interface]) (fun i_2928 h_2923 =>
            letb h_2923 : hash_t :=
              array_upd h_2923 (lift_to_both0 i_2928) (is_pure ((array_index (
                      h_2923) (lift_to_both0 i_2928)) .+ (array_index (
                      h_in_2927) (lift_to_both0 i_2928)))) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 h_2923)
            ) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 h_2923)
      ) : both (CEfset (
        [tmp_2889_loc ; s_2895_loc ; h_2907_loc ; h_2923_loc])) [interface] (
      hash_t)).
Fail Next Obligation.

Definition pad_block_2933_loc : ChoiceEqualityLocation :=
  (block_t ; 2934%nat).
Definition last_block_2931_loc : ChoiceEqualityLocation :=
  (block_t ; 2935%nat).
Definition last_block_len_2932_loc : ChoiceEqualityLocation :=
  (uint_size ; 2936%nat).
Definition h_2930_loc : ChoiceEqualityLocation :=
  (hash_t ; 2937%nat).
Notation "'hash_inp'" :=(
  byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'hash_inp'" :=(byte_seq : ChoiceEquality) (at level 2).
Notation "'hash_out'" :=(
  sha512_digest_t : choice_type) (in custom pack_type at level 2).
Notation "'hash_out'" :=(sha512_digest_t : ChoiceEquality) (at level 2).
Definition HASH : nat :=
  2944.
Program Definition hash (msg_2938 : byte_seq)
  : both (CEfset (
      [tmp_2889_loc ; s_2895_loc ; h_2907_loc ; h_2923_loc ; h_2930_loc ; last_block_2931_loc ; last_block_len_2932_loc ; pad_block_2933_loc])) [interface] (
    sha512_digest_t) :=
  ((letbm h_2930 : hash_t loc( h_2930_loc ) := lift_to_both0 hash_init_v in
      letbm last_block_2931 : block_t loc( last_block_2931_loc ) :=
        array_new_ (default : uint8) (block_size_v) in
      letbm last_block_len_2932 : uint_size loc( last_block_len_2932_loc ) :=
        lift_to_both0 (usize 0) in
      letb '(h_2930, last_block_2931, last_block_len_2932) :=
        foldi_both' (lift_to_both0 (usize 0)) (seq_num_chunks (
              lift_to_both0 msg_2938) (lift_to_both0 block_size_v)) prod_ce(
            h_2930,
            last_block_2931,
            last_block_len_2932
          ) (L := (CEfset (
                [tmp_2889_loc ; s_2895_loc ; h_2907_loc ; h_2923_loc ; h_2930_loc ; last_block_2931_loc ; last_block_len_2932_loc ; pad_block_2933_loc]))) (
            I := [interface]) (fun i_2939 '(
              h_2930,
              last_block_2931,
              last_block_len_2932
            ) =>
            letb '(block_len_2940, block_2941) : (uint_size '× seq uint8) :=
              seq_get_chunk (lift_to_both0 msg_2938) (
                lift_to_both0 block_size_v) (lift_to_both0 i_2939) in
            letb '(h_2930, last_block_2931, last_block_len_2932) :=
              if (lift_to_both0 block_len_2940) <.? (
                lift_to_both0 block_size_v) :bool_ChoiceEquality
              then lift_scope (L1 := CEfset (
                  [h_2930_loc ; last_block_2931_loc ; last_block_len_2932_loc])) (
                L2 := CEfset (
                  [tmp_2889_loc ; s_2895_loc ; h_2907_loc ; h_2923_loc ; h_2930_loc ; last_block_2931_loc ; last_block_len_2932_loc])) (
                I1 := [interface]) (
                I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
                letbm last_block_2931 loc( last_block_2931_loc ) :=
                  array_update_start (array_new_ (default : uint8) (
                      block_size_v)) (lift_to_both0 block_2941) in
                letbm last_block_len_2932 loc( last_block_len_2932_loc ) :=
                  lift_to_both0 block_len_2940 in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                    lift_to_both0 h_2930,
                    lift_to_both0 last_block_2931,
                    lift_to_both0 last_block_len_2932
                  ))
                )
              else  lift_scope (L1 := CEfset (
                  [tmp_2889_loc ; s_2895_loc ; h_2907_loc ; h_2923_loc ; h_2930_loc ; last_block_2931_loc ; last_block_len_2932_loc])) (
                L2 := CEfset (
                  [tmp_2889_loc ; s_2895_loc ; h_2907_loc ; h_2923_loc ; h_2930_loc ; last_block_2931_loc ; last_block_len_2932_loc])) (
                I1 := [interface]) (
                I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
                letb compress_input_2942 : block_t :=
                  array_from_seq (block_size_v) (lift_to_both0 block_2941) in
                letbm h_2930 loc( h_2930_loc ) :=
                  compress (lift_to_both0 compress_input_2942) (
                    lift_to_both0 h_2930) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                    lift_to_both0 h_2930,
                    lift_to_both0 last_block_2931,
                    lift_to_both0 last_block_len_2932
                  ))
                ) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                lift_to_both0 h_2930,
                lift_to_both0 last_block_2931,
                lift_to_both0 last_block_len_2932
              ))
            ) in
      letb last_block_2931 : block_t :=
        array_upd last_block_2931 (lift_to_both0 last_block_len_2932) (is_pure (
            secret (lift_to_both0 (@repr U8 128)))) in
      letb len_bist_2943 : uint128 :=
        secret (pub_u128 (is_pure ((seq_len (lift_to_both0 msg_2938)) .* (
                lift_to_both0 (usize 8))))) in
      letb '(h_2930, last_block_2931) :=
        if (lift_to_both0 last_block_len_2932) <.? ((
            lift_to_both0 block_size_v) .- (
            lift_to_both0 len_size_v)) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset (
            [tmp_2889_loc ; s_2895_loc ; h_2907_loc ; h_2923_loc ; h_2930_loc ; last_block_2931_loc ; last_block_len_2932_loc])) (
          L2 := CEfset (
            [tmp_2889_loc ; s_2895_loc ; h_2907_loc ; h_2923_loc ; h_2930_loc ; last_block_2931_loc ; last_block_len_2932_loc ; pad_block_2933_loc])) (
          I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
          letbm last_block_2931 loc( last_block_2931_loc ) :=
            array_update (lift_to_both0 last_block_2931) ((
                lift_to_both0 block_size_v) .- (lift_to_both0 len_size_v)) (
              array_to_seq (uint128_to_be_bytes (
                lift_to_both0 len_bist_2943))) in
          letbm h_2930 loc( h_2930_loc ) :=
            compress (lift_to_both0 last_block_2931) (lift_to_both0 h_2930) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
              lift_to_both0 h_2930,
              lift_to_both0 last_block_2931
            ))
          )
        else  lift_scope (L1 := CEfset (
            [tmp_2889_loc ; s_2895_loc ; h_2907_loc ; h_2923_loc ; h_2930_loc ; last_block_2931_loc ; last_block_len_2932_loc ; pad_block_2933_loc])) (
          L2 := CEfset (
            [tmp_2889_loc ; s_2895_loc ; h_2907_loc ; h_2923_loc ; h_2930_loc ; last_block_2931_loc ; last_block_len_2932_loc ; pad_block_2933_loc])) (
          I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
          letbm pad_block_2933 : block_t loc( pad_block_2933_loc ) :=
            array_new_ (default : uint8) (block_size_v) in
          letbm pad_block_2933 loc( pad_block_2933_loc ) :=
            array_update (lift_to_both0 pad_block_2933) ((
                lift_to_both0 block_size_v) .- (lift_to_both0 len_size_v)) (
              array_to_seq (uint128_to_be_bytes (
                lift_to_both0 len_bist_2943))) in
          letbm h_2930 loc( h_2930_loc ) :=
            compress (lift_to_both0 last_block_2931) (lift_to_both0 h_2930) in
          letbm h_2930 loc( h_2930_loc ) :=
            compress (lift_to_both0 pad_block_2933) (lift_to_both0 h_2930) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
              lift_to_both0 h_2930,
              lift_to_both0 last_block_2931
            ))
          ) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (array_from_seq (
          hash_size_v) (array_to_be_bytes (lift_to_both0 h_2930)))
      ) : both (CEfset (
        [tmp_2889_loc ; s_2895_loc ; h_2907_loc ; h_2923_loc ; h_2930_loc ; last_block_2931_loc ; last_block_len_2932_loc ; pad_block_2933_loc])) [interface] (
      sha512_digest_t)).
Fail Next Obligation.


Notation "'sha512_inp'" :=(
  byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'sha512_inp'" :=(byte_seq : ChoiceEquality) (at level 2).
Notation "'sha512_out'" :=(
  sha512_digest_t : choice_type) (in custom pack_type at level 2).
Notation "'sha512_out'" :=(sha512_digest_t : ChoiceEquality) (at level 2).
Definition SHA512 : nat :=
  2946.
Program Definition sha512 (msg_2945 : byte_seq)
  : both (CEfset (
      [tmp_2889_loc ; s_2895_loc ; h_2907_loc ; h_2923_loc ; h_2930_loc ; last_block_2931_loc ; last_block_len_2932_loc ; pad_block_2933_loc])) [interface] (
    sha512_digest_t) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (hash (
          lift_to_both0 msg_2945))
      ) : both (CEfset (
        [tmp_2889_loc ; s_2895_loc ; h_2907_loc ; h_2923_loc ; h_2930_loc ; last_block_2931_loc ; last_block_len_2932_loc ; pad_block_2933_loc])) [interface] (
      sha512_digest_t)).
Fail Next Obligation.

