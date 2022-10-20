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
  2714.
Program Definition ch
  : both_package (fset.fset0) [interface] [(CH,(ch_inp,ch_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(
      x_2711 , y_2712 , z_2713) := temp_inp : uint64 '× uint64 '× uint64 in
    
    ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (((
              lift_to_both0 x_2711) .& (lift_to_both0 y_2712)) .^ ((not (
                lift_to_both0 x_2711)) .& (lift_to_both0 z_2713)))
        ) : both (fset.fset0) [interface] (uint64)))in
  both_package' _ _ (CH,(ch_inp,ch_out)) temp_package_both.
Fail Next Obligation.


Notation "'maj_inp'" :=(
  uint64 '× uint64 '× uint64 : choice_type) (in custom pack_type at level 2).
Notation "'maj_inp'" :=(
  uint64 '× uint64 '× uint64 : ChoiceEquality) (at level 2).
Notation "'maj_out'" :=(uint64 : choice_type) (in custom pack_type at level 2).
Notation "'maj_out'" :=(uint64 : ChoiceEquality) (at level 2).
Definition MAJ : nat :=
  2718.
Program Definition maj
  : both_package (fset.fset0) [interface] [(MAJ,(maj_inp,maj_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(
      x_2715 , y_2716 , z_2717) := temp_inp : uint64 '× uint64 '× uint64 in
    
    ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (((
              lift_to_both0 x_2715) .& (lift_to_both0 y_2716)) .^ (((
                lift_to_both0 x_2715) .& (lift_to_both0 z_2717)) .^ ((
                lift_to_both0 y_2716) .& (lift_to_both0 z_2717))))
        ) : both (fset.fset0) [interface] (uint64)))in
  both_package' _ _ (MAJ,(maj_inp,maj_out)) temp_package_both.
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

Definition tmp_2719_loc : ChoiceEqualityLocation :=
  (uint64 ; 2720%nat).
Notation "'sigma_inp'" :=(
  uint64 '× uint_size '× uint_size : choice_type) (in custom pack_type at level 2).
Notation "'sigma_inp'" :=(
  uint64 '× uint_size '× uint_size : ChoiceEquality) (at level 2).
Notation "'sigma_out'" :=(
  uint64 : choice_type) (in custom pack_type at level 2).
Notation "'sigma_out'" :=(uint64 : ChoiceEquality) (at level 2).
Definition SIGMA : nat :=
  2724.
Program Definition sigma
  : both_package (CEfset ([tmp_2719_loc])) [interface] [(SIGMA,(
      sigma_inp,sigma_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(
      x_2721 , i_2722 , op_2723) := temp_inp : uint64 '× uint_size '× uint_size in
    
    ((letbm tmp_2719 : uint64 loc( tmp_2719_loc ) :=
          uint64_rotate_right (lift_to_both0 x_2721) (array_index (op_table_v) (
              ((lift_to_both0 (usize 3)) .* (lift_to_both0 i_2722)) .+ (
                lift_to_both0 (usize 2)))) in
        letb 'tmp_2719 :=
          if (lift_to_both0 op_2723) =.? (lift_to_both0 (
              usize 0)) :bool_ChoiceEquality
          then lift_scope (L1 := CEfset ([tmp_2719_loc])) (L2 := CEfset (
            [tmp_2719_loc])) (I1 := [interface]) (I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
            letbm tmp_2719 loc( tmp_2719_loc ) :=
              (lift_to_both0 x_2721) shift_right (array_index (op_table_v) (((
                      lift_to_both0 (usize 3)) .* (lift_to_both0 i_2722)) .+ (
                    lift_to_both0 (usize 2)))) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 tmp_2719)
            )
          else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 tmp_2719)
           in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (((
              uint64_rotate_right (lift_to_both0 x_2721) (array_index (
                  op_table_v) ((lift_to_both0 (usize 3)) .* (
                    lift_to_both0 i_2722)))) .^ (uint64_rotate_right (
                lift_to_both0 x_2721) (array_index (op_table_v) (((
                      lift_to_both0 (usize 3)) .* (lift_to_both0 i_2722)) .+ (
                    lift_to_both0 (usize 1)))))) .^ (lift_to_both0 tmp_2719))
        ) : both (CEfset ([tmp_2719_loc])) [interface] (uint64)))in
  both_package' _ _ (SIGMA,(sigma_inp,sigma_out)) temp_package_both.
Fail Next Obligation.

Definition s_2725_loc : ChoiceEqualityLocation :=
  (round_constants_table_t ; 2726%nat).
Notation "'schedule_inp'" :=(
  block_t : choice_type) (in custom pack_type at level 2).
Notation "'schedule_inp'" :=(block_t : ChoiceEquality) (at level 2).
Notation "'schedule_out'" :=(
  round_constants_table_t : choice_type) (in custom pack_type at level 2).
Notation "'schedule_out'" :=(
  round_constants_table_t : ChoiceEquality) (at level 2).
Definition SCHEDULE : nat :=
  2736.
Program Definition schedule
  : both_package (CEfset ([s_2725_loc])) [interface
  #val #[ SIGMA ] : sigma_inp → sigma_out ] [(SCHEDULE,(
      schedule_inp,schedule_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(block_2727) := temp_inp : block_t in
    
    let sigma := fun x_0 x_1 x_2 => package_both sigma (x_0,x_1,x_2) in
    ((letb b_2728 : seq uint64 :=
          array_to_be_uint64s (lift_to_both0 block_2727) in
        letbm s_2725 : round_constants_table_t loc( s_2725_loc ) :=
          array_new_ (default : uint64) (k_size_v) in
        letb s_2725 :=
          foldi_both' (lift_to_both0 (usize 0)) (
              lift_to_both0 k_size_v) s_2725 (L := (CEfset (
                [s_2725_loc]))) (I := ([interface
              #val #[ SIGMA ] : sigma_inp → sigma_out
              ])) (fun i_2729 s_2725 =>
            letb 's_2725 :=
              if (lift_to_both0 i_2729) <.? (lift_to_both0 (
                  usize 16)) :bool_ChoiceEquality
              then lift_scope (L1 := CEfset ([s_2725_loc])) (L2 := CEfset (
                [s_2725_loc])) (I1 := [interface]) (I2 := [interface
              #val #[ SIGMA ] : sigma_inp → sigma_out
              ]) (H_loc_incl := _) (H_opsig_incl := _) (
                letb s_2725 : round_constants_table_t :=
                  array_upd s_2725 (lift_to_both0 i_2729) (is_pure (seq_index (
                        b_2728) (lift_to_both0 i_2729))) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                  lift_to_both0 s_2725)
                )
              else  lift_scope (L1 := CEfset ([s_2725_loc])) (L2 := CEfset (
                [s_2725_loc])) (I1 := [interface
              #val #[ SIGMA ] : sigma_inp → sigma_out ]) (I2 := [interface
              #val #[ SIGMA ] : sigma_inp → sigma_out
              ]) (H_loc_incl := _) (H_opsig_incl := _) (
                letb t16_2730 : uint64 :=
                  array_index (s_2725) ((lift_to_both0 i_2729) .- (
                      lift_to_both0 (usize 16))) in
                letb t15_2731 : uint64 :=
                  array_index (s_2725) ((lift_to_both0 i_2729) .- (
                      lift_to_both0 (usize 15))) in
                letb t7_2732 : uint64 :=
                  array_index (s_2725) ((lift_to_both0 i_2729) .- (
                      lift_to_both0 (usize 7))) in
                letb t2_2733 : uint64 :=
                  array_index (s_2725) ((lift_to_both0 i_2729) .- (
                      lift_to_both0 (usize 2))) in
                letb s1_2734 : uint64 :=
                  sigma (lift_to_both0 t2_2733) (lift_to_both0 (usize 3)) (
                    lift_to_both0 (usize 0)) in
                letb s0_2735 : uint64 :=
                  sigma (lift_to_both0 t15_2731) (lift_to_both0 (usize 2)) (
                    lift_to_both0 (usize 0)) in
                letb s_2725 : round_constants_table_t :=
                  array_upd s_2725 (lift_to_both0 i_2729) (is_pure ((((
                            lift_to_both0 s1_2734) .+ (
                            lift_to_both0 t7_2732)) .+ (
                          lift_to_both0 s0_2735)) .+ (
                        lift_to_both0 t16_2730))) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                  lift_to_both0 s_2725)
                ) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 s_2725)
            ) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 s_2725)
        ) : both (CEfset ([s_2725_loc])) [interface
      #val #[ SIGMA ] : sigma_inp → sigma_out ] (round_constants_table_t)))in
  both_package' _ _ (SCHEDULE,(schedule_inp,schedule_out)) temp_package_both.
Fail Next Obligation.

Definition h_2737_loc : ChoiceEqualityLocation :=
  (hash_t ; 2738%nat).
Notation "'shuffle_inp'" :=(
  round_constants_table_t '× hash_t : choice_type) (in custom pack_type at level 2).
Notation "'shuffle_inp'" :=(
  round_constants_table_t '× hash_t : ChoiceEquality) (at level 2).
Notation "'shuffle_out'" :=(
  hash_t : choice_type) (in custom pack_type at level 2).
Notation "'shuffle_out'" :=(hash_t : ChoiceEquality) (at level 2).
Definition SHUFFLE : nat :=
  2752.
Program Definition shuffle
  : both_package (CEfset ([h_2737_loc])) [interface
  #val #[ CH ] : ch_inp → ch_out ; #val #[ MAJ ] : maj_inp → maj_out ;
  #val #[ SIGMA ] : sigma_inp → sigma_out ] [(SHUFFLE,(
      shuffle_inp,shuffle_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(
      ws_2749 , hashi_2739) := temp_inp : round_constants_table_t '× hash_t in
    
    let ch := fun x_0 x_1 x_2 => package_both ch (x_0,x_1,x_2) in
    let maj := fun x_0 x_1 x_2 => package_both maj (x_0,x_1,x_2) in
    let sigma := fun x_0 x_1 x_2 => package_both sigma (x_0,x_1,x_2) in
    ((letbm h_2737 : hash_t loc( h_2737_loc ) := lift_to_both0 hashi_2739 in
        letb h_2737 :=
          foldi_both' (lift_to_both0 (usize 0)) (
              lift_to_both0 k_size_v) h_2737 (L := (CEfset (
                [h_2737_loc]))) (I := ([interface
              #val #[ CH ] : ch_inp → ch_out ;
              #val #[ MAJ ] : maj_inp → maj_out ;
              #val #[ SIGMA ] : sigma_inp → sigma_out
              ])) (fun i_2740 h_2737 =>
            letb a0_2741 : uint64 :=
              array_index (h_2737) (lift_to_both0 (usize 0)) in
            letb b0_2742 : uint64 :=
              array_index (h_2737) (lift_to_both0 (usize 1)) in
            letb c0_2743 : uint64 :=
              array_index (h_2737) (lift_to_both0 (usize 2)) in
            letb d0_2744 : uint64 :=
              array_index (h_2737) (lift_to_both0 (usize 3)) in
            letb e0_2745 : uint64 :=
              array_index (h_2737) (lift_to_both0 (usize 4)) in
            letb f0_2746 : uint64 :=
              array_index (h_2737) (lift_to_both0 (usize 5)) in
            letb g0_2747 : uint64 :=
              array_index (h_2737) (lift_to_both0 (usize 6)) in
            letb h0_2748 : uint64 :=
              array_index (h_2737) (lift_to_both0 (usize 7)) in
            letb t1_2750 : uint64 :=
              ((((lift_to_both0 h0_2748) .+ (sigma (lift_to_both0 e0_2745) (
                        lift_to_both0 (usize 1)) (lift_to_both0 (
                          usize 1)))) .+ (ch (lift_to_both0 e0_2745) (
                      lift_to_both0 f0_2746) (lift_to_both0 g0_2747))) .+ (
                  array_index (k_table_v) (lift_to_both0 i_2740))) .+ (
                array_index (ws_2749) (lift_to_both0 i_2740)) in
            letb t2_2751 : uint64 :=
              (sigma (lift_to_both0 a0_2741) (lift_to_both0 (usize 0)) (
                  lift_to_both0 (usize 1))) .+ (maj (lift_to_both0 a0_2741) (
                  lift_to_both0 b0_2742) (lift_to_both0 c0_2743)) in
            letb h_2737 : hash_t :=
              array_upd h_2737 (lift_to_both0 (usize 0)) (is_pure ((
                    lift_to_both0 t1_2750) .+ (lift_to_both0 t2_2751))) in
            letb h_2737 : hash_t :=
              array_upd h_2737 (lift_to_both0 (usize 1)) (is_pure (
                  lift_to_both0 a0_2741)) in
            letb h_2737 : hash_t :=
              array_upd h_2737 (lift_to_both0 (usize 2)) (is_pure (
                  lift_to_both0 b0_2742)) in
            letb h_2737 : hash_t :=
              array_upd h_2737 (lift_to_both0 (usize 3)) (is_pure (
                  lift_to_both0 c0_2743)) in
            letb h_2737 : hash_t :=
              array_upd h_2737 (lift_to_both0 (usize 4)) (is_pure ((
                    lift_to_both0 d0_2744) .+ (lift_to_both0 t1_2750))) in
            letb h_2737 : hash_t :=
              array_upd h_2737 (lift_to_both0 (usize 5)) (is_pure (
                  lift_to_both0 e0_2745)) in
            letb h_2737 : hash_t :=
              array_upd h_2737 (lift_to_both0 (usize 6)) (is_pure (
                  lift_to_both0 f0_2746)) in
            letb h_2737 : hash_t :=
              array_upd h_2737 (lift_to_both0 (usize 7)) (is_pure (
                  lift_to_both0 g0_2747)) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 h_2737)
            ) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 h_2737)
        ) : both (CEfset ([h_2737_loc])) [interface
      #val #[ CH ] : ch_inp → ch_out ; #val #[ MAJ ] : maj_inp → maj_out ;
      #val #[ SIGMA ] : sigma_inp → sigma_out ] (hash_t)))in
  both_package' _ _ (SHUFFLE,(shuffle_inp,shuffle_out)) temp_package_both.
Fail Next Obligation.

Definition h_2753_loc : ChoiceEqualityLocation :=
  (hash_t ; 2754%nat).
Notation "'compress_inp'" :=(
  block_t '× hash_t : choice_type) (in custom pack_type at level 2).
Notation "'compress_inp'" :=(block_t '× hash_t : ChoiceEquality) (at level 2).
Notation "'compress_out'" :=(
  hash_t : choice_type) (in custom pack_type at level 2).
Notation "'compress_out'" :=(hash_t : ChoiceEquality) (at level 2).
Definition COMPRESS : nat :=
  2759.
Program Definition compress
  : both_package (CEfset ([h_2753_loc])) [interface
  #val #[ SCHEDULE ] : schedule_inp → schedule_out ;
  #val #[ SHUFFLE ] : shuffle_inp → shuffle_out ] [(COMPRESS,(
      compress_inp,compress_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(block_2755 , h_in_2757) := temp_inp : block_t '× hash_t in
    
    let schedule := fun x_0 => package_both schedule (x_0) in
    let shuffle := fun x_0 x_1 => package_both shuffle (x_0,x_1) in
    ((letb s_2756 : round_constants_table_t :=
          schedule (lift_to_both0 block_2755) in
        letbm h_2753 : hash_t loc( h_2753_loc ) :=
          shuffle (lift_to_both0 s_2756) (lift_to_both0 h_in_2757) in
        letb h_2753 :=
          foldi_both' (lift_to_both0 (usize 0)) (lift_to_both0 (
                usize 8)) h_2753 (L := (CEfset ([h_2753_loc]))) (I := (
              [interface #val #[ SCHEDULE ] : schedule_inp → schedule_out ;
              #val #[ SHUFFLE ] : shuffle_inp → shuffle_out
              ])) (fun i_2758 h_2753 =>
            letb h_2753 : hash_t :=
              array_upd h_2753 (lift_to_both0 i_2758) (is_pure ((array_index (
                      h_2753) (lift_to_both0 i_2758)) .+ (array_index (
                      h_in_2757) (lift_to_both0 i_2758)))) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 h_2753)
            ) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 h_2753)
        ) : both (CEfset ([h_2753_loc])) [interface
      #val #[ SCHEDULE ] : schedule_inp → schedule_out ;
      #val #[ SHUFFLE ] : shuffle_inp → shuffle_out ] (hash_t)))in
  both_package' _ _ (COMPRESS,(compress_inp,compress_out)) temp_package_both.
Fail Next Obligation.

Definition last_block_2761_loc : ChoiceEqualityLocation :=
  (block_t ; 2764%nat).
Definition pad_block_2763_loc : ChoiceEqualityLocation :=
  (block_t ; 2765%nat).
Definition last_block_len_2762_loc : ChoiceEqualityLocation :=
  (uint_size ; 2766%nat).
Definition h_2760_loc : ChoiceEqualityLocation :=
  (hash_t ; 2767%nat).
Notation "'hash_inp'" :=(
  byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'hash_inp'" :=(byte_seq : ChoiceEquality) (at level 2).
Notation "'hash_out'" :=(
  sha512_digest_t : choice_type) (in custom pack_type at level 2).
Notation "'hash_out'" :=(sha512_digest_t : ChoiceEquality) (at level 2).
Definition HASH : nat :=
  2774.
Program Definition hash
  : both_package (CEfset (
      [h_2760_loc ; last_block_2761_loc ; last_block_len_2762_loc ; pad_block_2763_loc])) [interface
  #val #[ COMPRESS ] : compress_inp → compress_out ] [(HASH,(
      hash_inp,hash_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(msg_2768) := temp_inp : byte_seq in
    
    let compress := fun x_0 x_1 => package_both compress (x_0,x_1) in
    ((letbm h_2760 : hash_t loc( h_2760_loc ) := lift_to_both0 hash_init_v in
        letbm last_block_2761 : block_t loc( last_block_2761_loc ) :=
          array_new_ (default : uint8) (block_size_v) in
        letbm last_block_len_2762 : uint_size loc( last_block_len_2762_loc ) :=
          lift_to_both0 (usize 0) in
        letb '(h_2760, last_block_2761, last_block_len_2762) :=
          foldi_both' (lift_to_both0 (usize 0)) (seq_num_chunks (
                lift_to_both0 msg_2768) (lift_to_both0 block_size_v)) prod_ce(
              h_2760,
              last_block_2761,
              last_block_len_2762
            ) (L := (CEfset (
                [h_2760_loc ; last_block_2761_loc ; last_block_len_2762_loc ; pad_block_2763_loc]))) (I := (
              [interface #val #[ COMPRESS ] : compress_inp → compress_out
              ])) (fun i_2769 '(h_2760, last_block_2761, last_block_len_2762) =>
            letb '(block_len_2770, block_2771) : (uint_size '× seq uint8) :=
              seq_get_chunk (lift_to_both0 msg_2768) (
                lift_to_both0 block_size_v) (lift_to_both0 i_2769) in
            letb '(h_2760, last_block_2761, last_block_len_2762) :=
              if (lift_to_both0 block_len_2770) <.? (
                lift_to_both0 block_size_v) :bool_ChoiceEquality
              then lift_scope (L1 := CEfset (
                [h_2760_loc ; last_block_2761_loc ; last_block_len_2762_loc])) (L2 := CEfset (
                [h_2760_loc ; last_block_2761_loc ; last_block_len_2762_loc])) (I1 := [interface]) (I2 := [interface
              #val #[ COMPRESS ] : compress_inp → compress_out
              ]) (H_loc_incl := _) (H_opsig_incl := _) (
                letbm last_block_2761 loc( last_block_2761_loc ) :=
                  array_update_start (array_new_ (default : uint8) (
                      block_size_v)) (lift_to_both0 block_2771) in
                letbm last_block_len_2762 loc( last_block_len_2762_loc ) :=
                  lift_to_both0 block_len_2770 in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                    lift_to_both0 h_2760,
                    lift_to_both0 last_block_2761,
                    lift_to_both0 last_block_len_2762
                  ))
                )
              else  lift_scope (L1 := CEfset (
                [h_2760_loc ; last_block_2761_loc ; last_block_len_2762_loc])) (L2 := CEfset (
                [h_2760_loc ; last_block_2761_loc ; last_block_len_2762_loc])) (I1 := [interface
              #val #[ COMPRESS ] : compress_inp → compress_out
              ]) (I2 := [interface
              #val #[ COMPRESS ] : compress_inp → compress_out
              ]) (H_loc_incl := _) (H_opsig_incl := _) (
                letb compress_input_2772 : block_t :=
                  array_from_seq (block_size_v) (lift_to_both0 block_2771) in
                letbm h_2760 loc( h_2760_loc ) :=
                  compress (lift_to_both0 compress_input_2772) (
                    lift_to_both0 h_2760) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                    lift_to_both0 h_2760,
                    lift_to_both0 last_block_2761,
                    lift_to_both0 last_block_len_2762
                  ))
                ) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                lift_to_both0 h_2760,
                lift_to_both0 last_block_2761,
                lift_to_both0 last_block_len_2762
              ))
            ) in
        letb last_block_2761 : block_t :=
          array_upd last_block_2761 (lift_to_both0 last_block_len_2762) (
            is_pure (secret (lift_to_both0 (@repr U8 128)))) in
        letb len_bist_2773 : uint128 :=
          secret (pub_u128 (is_pure ((seq_len (lift_to_both0 msg_2768)) .* (
                  lift_to_both0 (usize 8))))) in
        letb '(h_2760, last_block_2761) :=
          if (lift_to_both0 last_block_len_2762) <.? ((
              lift_to_both0 block_size_v) .- (
              lift_to_both0 len_size_v)) :bool_ChoiceEquality
          then lift_scope (L1 := CEfset (
            [h_2760_loc ; last_block_2761_loc ; last_block_len_2762_loc])) (L2 := CEfset (
            [h_2760_loc ; last_block_2761_loc ; last_block_len_2762_loc ; pad_block_2763_loc])) (I1 := [interface
          #val #[ COMPRESS ] : compress_inp → compress_out
          ]) (I2 := [interface
          #val #[ COMPRESS ] : compress_inp → compress_out
          ]) (H_loc_incl := _) (H_opsig_incl := _) (
            letbm last_block_2761 loc( last_block_2761_loc ) :=
              array_update (lift_to_both0 last_block_2761) ((
                  lift_to_both0 block_size_v) .- (lift_to_both0 len_size_v)) (
                array_to_seq (uint128_to_be_bytes (
                  lift_to_both0 len_bist_2773))) in
            letbm h_2760 loc( h_2760_loc ) :=
              compress (lift_to_both0 last_block_2761) (lift_to_both0 h_2760) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                lift_to_both0 h_2760,
                lift_to_both0 last_block_2761
              ))
            )
          else  lift_scope (L1 := CEfset (
            [h_2760_loc ; last_block_2761_loc ; last_block_len_2762_loc ; pad_block_2763_loc])) (L2 := CEfset (
            [h_2760_loc ; last_block_2761_loc ; last_block_len_2762_loc ; pad_block_2763_loc])) (I1 := [interface
          #val #[ COMPRESS ] : compress_inp → compress_out
          ]) (I2 := [interface
          #val #[ COMPRESS ] : compress_inp → compress_out
          ]) (H_loc_incl := _) (H_opsig_incl := _) (
            letbm pad_block_2763 : block_t loc( pad_block_2763_loc ) :=
              array_new_ (default : uint8) (block_size_v) in
            letbm pad_block_2763 loc( pad_block_2763_loc ) :=
              array_update (lift_to_both0 pad_block_2763) ((
                  lift_to_both0 block_size_v) .- (lift_to_both0 len_size_v)) (
                array_to_seq (uint128_to_be_bytes (
                  lift_to_both0 len_bist_2773))) in
            letbm h_2760 loc( h_2760_loc ) :=
              compress (lift_to_both0 last_block_2761) (lift_to_both0 h_2760) in
            letbm h_2760 loc( h_2760_loc ) :=
              compress (lift_to_both0 pad_block_2763) (lift_to_both0 h_2760) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                lift_to_both0 h_2760,
                lift_to_both0 last_block_2761
              ))
            ) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (array_from_seq (
            hash_size_v) (array_to_be_bytes (lift_to_both0 h_2760)))
        ) : both (CEfset (
          [h_2760_loc ; last_block_2761_loc ; last_block_len_2762_loc ; pad_block_2763_loc])) [interface
      #val #[ COMPRESS ] : compress_inp → compress_out ] (sha512_digest_t)))in
  both_package' _ _ (HASH,(hash_inp,hash_out)) temp_package_both.
Fail Next Obligation.


Notation "'sha512_inp'" :=(
  byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'sha512_inp'" :=(byte_seq : ChoiceEquality) (at level 2).
Notation "'sha512_out'" :=(
  sha512_digest_t : choice_type) (in custom pack_type at level 2).
Notation "'sha512_out'" :=(sha512_digest_t : ChoiceEquality) (at level 2).
Definition SHA512 : nat :=
  2776.
Program Definition sha512
  : both_package (CEfset ([])) [interface #val #[ HASH ] : hash_inp → hash_out
  ] [(SHA512,(sha512_inp,sha512_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(msg_2775) := temp_inp : byte_seq in
    
    let hash := fun x_0 => package_both hash (x_0) in
    ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (hash (
            lift_to_both0 msg_2775))
        ) : both (CEfset ([])) [interface #val #[ HASH ] : hash_inp → hash_out
      ] (sha512_digest_t)))in
  both_package' _ _ (SHA512,(sha512_inp,sha512_out)) temp_package_both.
Fail Next Obligation.

