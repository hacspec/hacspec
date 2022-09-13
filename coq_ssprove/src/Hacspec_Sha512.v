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

Definition block_size_v : (uint_size) :=
  ((usize 128)).

Definition len_size_v : (uint_size) :=
  ((usize 16)).

Definition k_size_v : (uint_size) :=
  ((usize 80)).

Definition hash_size_v : (uint_size) :=
  (let temp_13204 : uint_size :=
      ((usize 512) ./ (usize 8)) in
    (temp_13204)).

Definition block_t  :=
  ( nseq (uint8) (block_size_v)).

Definition op_table_type_t  :=
  ( nseq (uint_size) (usize 12)).

Definition sha512_digest_t  :=
  ( nseq (uint8) (hash_size_v)).

Definition round_constants_table_t  :=
  ( nseq (uint64) (k_size_v)).

Definition hash_t  :=
  ( nseq (uint64) (usize 8)).


Notation "'ch_inp'" := (
  uint64 '× uint64 '× uint64 : choice_type) (in custom pack_type at level 2).
Notation "'ch_out'" := (uint64 : choice_type) (in custom pack_type at level 2).
Definition CH : nat :=
  (13214).
Program Definition ch
   : package (fset.fset0) [interface] [interface
  #val #[ CH ] : ch_inp → ch_out ] :=
  ([package #def #[ CH ] (temp_inp : ch_inp) : ch_out { 
    let '(
      x_13205 , y_13206 , z_13209) := temp_inp : uint64 '× uint64 '× uint64 in
    ({ code  temp_13208 ←
        ((x_13205) .& (y_13206)) ;;
       temp_13211 ←
        ((not (x_13205)) .& (z_13209)) ;;
       temp_13213 ←
        ((temp_13208) .^ (temp_13211)) ;;
      @ret (uint64) (temp_13213) } : code (fset.fset0) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_ch : package _ _ _ :=
  (ch).
Fail Next Obligation.


Notation "'maj_inp'" := (
  uint64 '× uint64 '× uint64 : choice_type) (in custom pack_type at level 2).
Notation "'maj_out'" := (uint64 : choice_type) (in custom pack_type at level 2).
Definition MAJ : nat :=
  (13228).
Program Definition maj
   : package (fset.fset0) [interface] [interface
  #val #[ MAJ ] : maj_inp → maj_out ] :=
  ([package #def #[ MAJ ] (temp_inp : maj_inp) : maj_out { 
    let '(
      x_13215 , y_13216 , z_13219) := temp_inp : uint64 '× uint64 '× uint64 in
    ({ code  temp_13218 ←
        ((x_13215) .& (y_13216)) ;;
       temp_13221 ←
        ((x_13215) .& (z_13219)) ;;
       temp_13223 ←
        ((y_13216) .& (z_13219)) ;;
       temp_13225 ←
        ((temp_13221) .^ (temp_13223)) ;;
       temp_13227 ←
        ((temp_13218) .^ (temp_13225)) ;;
      @ret (uint64) (temp_13227) } : code (fset.fset0) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_maj : package _ _ _ :=
  (maj).
Fail Next Obligation.

Definition op_table_v : (op_table_type_t) :=
  (let temp_13230 : nseq uint_size 12 :=
      (array_from_list uint_size [
          usize 28;
          usize 34;
          usize 39;
          usize 14;
          usize 18;
          usize 41;
          usize 1;
          usize 8;
          usize 7;
          usize 19;
          usize 61;
          usize 6
        ]) in
    (temp_13230)).

Definition k_table_v : (round_constants_table_t) :=
  (let temp_13232 : int64 :=
      (secret (@repr U64 4794697086780616226)) in
    let temp_13234 : int64 :=
      (secret (@repr U64 8158064640168781261)) in
    let temp_13236 : int64 :=
      (secret (@repr U64 13096744586834688815)) in
    let temp_13238 : int64 :=
      (secret (@repr U64 16840607885511220156)) in
    let temp_13240 : int64 :=
      (secret (@repr U64 4131703408338449720)) in
    let temp_13242 : int64 :=
      (secret (@repr U64 6480981068601479193)) in
    let temp_13244 : int64 :=
      (secret (@repr U64 10538285296894168987)) in
    let temp_13246 : int64 :=
      (secret (@repr U64 12329834152419229976)) in
    let temp_13248 : int64 :=
      (secret (@repr U64 15566598209576043074)) in
    let temp_13250 : int64 :=
      (secret (@repr U64 1334009975649890238)) in
    let temp_13252 : int64 :=
      (secret (@repr U64 2608012711638119052)) in
    let temp_13254 : int64 :=
      (secret (@repr U64 6128411473006802146)) in
    let temp_13256 : int64 :=
      (secret (@repr U64 8268148722764581231)) in
    let temp_13258 : int64 :=
      (secret (@repr U64 9286055187155687089)) in
    let temp_13260 : int64 :=
      (secret (@repr U64 11230858885718282805)) in
    let temp_13262 : int64 :=
      (secret (@repr U64 13951009754708518548)) in
    let temp_13264 : int64 :=
      (secret (@repr U64 16472876342353939154)) in
    let temp_13266 : int64 :=
      (secret (@repr U64 17275323862435702243)) in
    let temp_13268 : int64 :=
      (secret (@repr U64 1135362057144423861)) in
    let temp_13270 : int64 :=
      (secret (@repr U64 2597628984639134821)) in
    let temp_13272 : int64 :=
      (secret (@repr U64 3308224258029322869)) in
    let temp_13274 : int64 :=
      (secret (@repr U64 5365058923640841347)) in
    let temp_13276 : int64 :=
      (secret (@repr U64 6679025012923562964)) in
    let temp_13278 : int64 :=
      (secret (@repr U64 8573033837759648693)) in
    let temp_13280 : int64 :=
      (secret (@repr U64 10970295158949994411)) in
    let temp_13282 : int64 :=
      (secret (@repr U64 12119686244451234320)) in
    let temp_13284 : int64 :=
      (secret (@repr U64 12683024718118986047)) in
    let temp_13286 : int64 :=
      (secret (@repr U64 13788192230050041572)) in
    let temp_13288 : int64 :=
      (secret (@repr U64 14330467153632333762)) in
    let temp_13290 : int64 :=
      (secret (@repr U64 15395433587784984357)) in
    let temp_13292 : int64 :=
      (secret (@repr U64 489312712824947311)) in
    let temp_13294 : int64 :=
      (secret (@repr U64 1452737877330783856)) in
    let temp_13296 : int64 :=
      (secret (@repr U64 2861767655752347644)) in
    let temp_13298 : int64 :=
      (secret (@repr U64 3322285676063803686)) in
    let temp_13300 : int64 :=
      (secret (@repr U64 5560940570517711597)) in
    let temp_13302 : int64 :=
      (secret (@repr U64 5996557281743188959)) in
    let temp_13304 : int64 :=
      (secret (@repr U64 7280758554555802590)) in
    let temp_13306 : int64 :=
      (secret (@repr U64 8532644243296465576)) in
    let temp_13308 : int64 :=
      (secret (@repr U64 9350256976987008742)) in
    let temp_13310 : int64 :=
      (secret (@repr U64 10552545826968843579)) in
    let temp_13312 : int64 :=
      (secret (@repr U64 11727347734174303076)) in
    let temp_13314 : int64 :=
      (secret (@repr U64 12113106623233404929)) in
    let temp_13316 : int64 :=
      (secret (@repr U64 14000437183269869457)) in
    let temp_13318 : int64 :=
      (secret (@repr U64 14369950271660146224)) in
    let temp_13320 : int64 :=
      (secret (@repr U64 15101387698204529176)) in
    let temp_13322 : int64 :=
      (secret (@repr U64 15463397548674623760)) in
    let temp_13324 : int64 :=
      (secret (@repr U64 17586052441742319658)) in
    let temp_13326 : int64 :=
      (secret (@repr U64 1182934255886127544)) in
    let temp_13328 : int64 :=
      (secret (@repr U64 1847814050463011016)) in
    let temp_13330 : int64 :=
      (secret (@repr U64 2177327727835720531)) in
    let temp_13332 : int64 :=
      (secret (@repr U64 2830643537854262169)) in
    let temp_13334 : int64 :=
      (secret (@repr U64 3796741975233480872)) in
    let temp_13336 : int64 :=
      (secret (@repr U64 4115178125766777443)) in
    let temp_13338 : int64 :=
      (secret (@repr U64 5681478168544905931)) in
    let temp_13340 : int64 :=
      (secret (@repr U64 6601373596472566643)) in
    let temp_13342 : int64 :=
      (secret (@repr U64 7507060721942968483)) in
    let temp_13344 : int64 :=
      (secret (@repr U64 8399075790359081724)) in
    let temp_13346 : int64 :=
      (secret (@repr U64 8693463985226723168)) in
    let temp_13348 : int64 :=
      (secret (@repr U64 9568029438360202098)) in
    let temp_13350 : int64 :=
      (secret (@repr U64 10144078919501101548)) in
    let temp_13352 : int64 :=
      (secret (@repr U64 10430055236837252648)) in
    let temp_13354 : int64 :=
      (secret (@repr U64 11840083180663258601)) in
    let temp_13356 : int64 :=
      (secret (@repr U64 13761210420658862357)) in
    let temp_13358 : int64 :=
      (secret (@repr U64 14299343276471374635)) in
    let temp_13360 : int64 :=
      (secret (@repr U64 14566680578165727644)) in
    let temp_13362 : int64 :=
      (secret (@repr U64 15097957966210449927)) in
    let temp_13364 : int64 :=
      (secret (@repr U64 16922976911328602910)) in
    let temp_13366 : int64 :=
      (secret (@repr U64 17689382322260857208)) in
    let temp_13368 : int64 :=
      (secret (@repr U64 500013540394364858)) in
    let temp_13370 : int64 :=
      (secret (@repr U64 748580250866718886)) in
    let temp_13372 : int64 :=
      (secret (@repr U64 1242879168328830382)) in
    let temp_13374 : int64 :=
      (secret (@repr U64 1977374033974150939)) in
    let temp_13376 : int64 :=
      (secret (@repr U64 2944078676154940804)) in
    let temp_13378 : int64 :=
      (secret (@repr U64 3659926193048069267)) in
    let temp_13380 : int64 :=
      (secret (@repr U64 4368137639120453308)) in
    let temp_13382 : int64 :=
      (secret (@repr U64 4836135668995329356)) in
    let temp_13384 : int64 :=
      (secret (@repr U64 5532061633213252278)) in
    let temp_13386 : int64 :=
      (secret (@repr U64 6448918945643986474)) in
    let temp_13388 : int64 :=
      (secret (@repr U64 6902733635092675308)) in
    let temp_13390 : int64 :=
      (secret (@repr U64 7801388544844847127)) in
    let temp_13392 : nseq uint64 80 :=
      (array_from_list uint64 [
          temp_13232;
          temp_13234;
          temp_13236;
          temp_13238;
          temp_13240;
          temp_13242;
          temp_13244;
          temp_13246;
          temp_13248;
          temp_13250;
          temp_13252;
          temp_13254;
          temp_13256;
          temp_13258;
          temp_13260;
          temp_13262;
          temp_13264;
          temp_13266;
          temp_13268;
          temp_13270;
          temp_13272;
          temp_13274;
          temp_13276;
          temp_13278;
          temp_13280;
          temp_13282;
          temp_13284;
          temp_13286;
          temp_13288;
          temp_13290;
          temp_13292;
          temp_13294;
          temp_13296;
          temp_13298;
          temp_13300;
          temp_13302;
          temp_13304;
          temp_13306;
          temp_13308;
          temp_13310;
          temp_13312;
          temp_13314;
          temp_13316;
          temp_13318;
          temp_13320;
          temp_13322;
          temp_13324;
          temp_13326;
          temp_13328;
          temp_13330;
          temp_13332;
          temp_13334;
          temp_13336;
          temp_13338;
          temp_13340;
          temp_13342;
          temp_13344;
          temp_13346;
          temp_13348;
          temp_13350;
          temp_13352;
          temp_13354;
          temp_13356;
          temp_13358;
          temp_13360;
          temp_13362;
          temp_13364;
          temp_13366;
          temp_13368;
          temp_13370;
          temp_13372;
          temp_13374;
          temp_13376;
          temp_13378;
          temp_13380;
          temp_13382;
          temp_13384;
          temp_13386;
          temp_13388;
          temp_13390
        ]) in
    (temp_13392)).

Definition hash_init_v : (hash_t) :=
  (let temp_13394 : int64 :=
      (secret (@repr U64 7640891576956012808)) in
    let temp_13396 : int64 :=
      (secret (@repr U64 13503953896175478587)) in
    let temp_13398 : int64 :=
      (secret (@repr U64 4354685564936845355)) in
    let temp_13400 : int64 :=
      (secret (@repr U64 11912009170470909681)) in
    let temp_13402 : int64 :=
      (secret (@repr U64 5840696475078001361)) in
    let temp_13404 : int64 :=
      (secret (@repr U64 11170449401992604703)) in
    let temp_13406 : int64 :=
      (secret (@repr U64 2270897969802886507)) in
    let temp_13408 : int64 :=
      (secret (@repr U64 6620516959819538809)) in
    let temp_13410 : nseq uint64 8 :=
      (array_from_list uint64 [
          temp_13394;
          temp_13396;
          temp_13398;
          temp_13400;
          temp_13402;
          temp_13404;
          temp_13406;
          temp_13408
        ]) in
    (temp_13410)).

Definition tmp_13432_loc : ChoiceEqualityLocation :=
  ((uint64 ; 13451%nat)).
Notation "'sigma_inp'" := (
  uint64 '× uint_size '× uint_size : choice_type) (in custom pack_type at level 2).
Notation "'sigma_out'" := (
  uint64 : choice_type) (in custom pack_type at level 2).
Definition SIGMA : nat :=
  (13452).
Program Definition sigma
   : package (CEfset ([tmp_13432_loc])) [interface] [interface
  #val #[ SIGMA ] : sigma_inp → sigma_out ] :=
  ([package #def #[ SIGMA ] (temp_inp : sigma_inp) : sigma_out { 
    let '(
      x_13411 , i_13412 , op_13421) := temp_inp : uint64 '× uint_size '× uint_size in
    ({ code  '(tmp_13432 : uint64) ←
          ( '(temp_13414 : uint_size) ←
              ((usize 3) .* (i_13412)) ;;
             '(temp_13416 : uint_size) ←
              ((temp_13414) .+ (usize 2)) ;;
             temp_13418 ←
              (array_index (op_table_v) (temp_13416)) ;;
             temp_13420 ←
              (uint64_rotate_right (x_13411) (temp_13418)) ;;
            ret (temp_13420)) ;;
        #put tmp_13432_loc := tmp_13432 ;;
       '(temp_13423 : bool_ChoiceEquality) ←
        ((op_13421) =.? (usize 0)) ;;
       '(tmp_13432 : (uint64)) ←
        (if temp_13423:bool_ChoiceEquality
          then (*not state*) (let temp_then :=  '(tmp_13432 : uint64) ←
                (( '(temp_13425 : uint_size) ←
                      ((usize 3) .* (i_13412)) ;;
                     '(temp_13427 : uint_size) ←
                      ((temp_13425) .+ (usize 2)) ;;
                     temp_13429 ←
                      (array_index (op_table_v) (temp_13427)) ;;
                     temp_13431 ←
                      ((x_13411) shift_right (temp_13429)) ;;
                    ret (temp_13431))) ;;
              #put tmp_13432_loc := tmp_13432 ;;
            
            @ret ((uint64)) (tmp_13432) in
            ({ code temp_then } : code (CEfset (
                  [tmp_13432_loc])) [interface] _))
          else @ret ((uint64)) (tmp_13432)) ;;
      
       '(temp_13434 : uint_size) ←
        ((usize 3) .* (i_13412)) ;;
       temp_13436 ←
        (array_index (op_table_v) (temp_13434)) ;;
       temp_13438 ←
        (uint64_rotate_right (x_13411) (temp_13436)) ;;
       '(temp_13440 : uint_size) ←
        ((usize 3) .* (i_13412)) ;;
       '(temp_13442 : uint_size) ←
        ((temp_13440) .+ (usize 1)) ;;
       temp_13444 ←
        (array_index (op_table_v) (temp_13442)) ;;
       temp_13446 ←
        (uint64_rotate_right (x_13411) (temp_13444)) ;;
       temp_13448 ←
        ((temp_13438) .^ (temp_13446)) ;;
       temp_13450 ←
        ((temp_13448) .^ (tmp_13432)) ;;
      @ret (uint64) (temp_13450) } : code (CEfset (
          [tmp_13432_loc])) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_sigma : package _ _ _ :=
  (sigma).
Fail Next Obligation.

Definition s_13464_loc : ChoiceEqualityLocation :=
  ((round_constants_table_t ; 13497%nat)).
Notation "'schedule_inp'" := (
  block_t : choice_type) (in custom pack_type at level 2).
Notation "'schedule_out'" := (
  round_constants_table_t : choice_type) (in custom pack_type at level 2).
Definition SCHEDULE : nat :=
  (13498).
Program Definition schedule
   : package (CEfset ([s_13464_loc])) [interface
  #val #[ SIGMA ] : sigma_inp → sigma_out ] [interface
  #val #[ SCHEDULE ] : schedule_inp → schedule_out ] :=
  ([package #def #[ SCHEDULE ] (temp_inp : schedule_inp) : schedule_out { 
    let '(block_13453) := temp_inp : block_t in
    #import {sig #[ SIGMA ] : sigma_inp → sigma_out } as sigma ;;
    let sigma := fun x_0 x_1 x_2 => sigma (x_0,x_1,x_2) in
    ({ code  '(b_13462 : seq uint64) ←
        ( temp_13455 ←
            (array_to_be_uint64s (block_13453)) ;;
          ret (temp_13455)) ;;
       '(s_13464 : round_constants_table_t) ←
          ( '(temp_13457 : round_constants_table_t) ←
              (array_new_ (default : uint64) (k_size_v)) ;;
            ret (temp_13457)) ;;
        #put s_13464_loc := s_13464 ;;
       '(s_13464 : (round_constants_table_t)) ←
        (foldi' (usize 0) (k_size_v) s_13464 (L2 := CEfset ([s_13464_loc])) (
              I2 := [interface #val #[ SIGMA ] : sigma_inp → sigma_out
              ]) (H_loc_incl := _) (H_opsig_incl := _) (fun i_13458 s_13464 =>
            ({ code  '(temp_13460 : bool_ChoiceEquality) ←
                ((i_13458) <.? (usize 16)) ;;
               '(s_13464 : (round_constants_table_t)) ←
                (if temp_13460:bool_ChoiceEquality
                  then (*not state*) (let temp_then :=  '(
                        s_13464 : round_constants_table_t) ←
                      ( '(temp_13463 : uint64) ←
                          (seq_index (b_13462) (i_13458)) ;;
                        ret (array_upd s_13464 (i_13458) (temp_13463))) ;;
                    
                    @ret ((round_constants_table_t)) (s_13464) in
                    ({ code temp_then } : code (CEfset (
                          [s_13464_loc])) [interface] _))
                  else  (({ code  '(t16_13494 : uint64) ←
                        ( '(temp_13466 : uint_size) ←
                            ((i_13458) .- (usize 16)) ;;
                           temp_13468 ←
                            (array_index (s_13464) (temp_13466)) ;;
                          ret (temp_13468)) ;;
                       '(t15_13484 : uint64) ←
                        ( '(temp_13470 : uint_size) ←
                            ((i_13458) .- (usize 15)) ;;
                           temp_13472 ←
                            (array_index (s_13464) (temp_13470)) ;;
                          ret (temp_13472)) ;;
                       '(t7_13488 : uint64) ←
                        ( '(temp_13474 : uint_size) ←
                            ((i_13458) .- (usize 7)) ;;
                           temp_13476 ←
                            (array_index (s_13464) (temp_13474)) ;;
                          ret (temp_13476)) ;;
                       '(t2_13481 : uint64) ←
                        ( '(temp_13478 : uint_size) ←
                            ((i_13458) .- (usize 2)) ;;
                           temp_13480 ←
                            (array_index (s_13464) (temp_13478)) ;;
                          ret (temp_13480)) ;;
                       '(s1_13487 : uint64) ←
                        ( '(temp_13483 : uint64) ←
                            (sigma (t2_13481) (usize 3) (usize 0)) ;;
                          ret (temp_13483)) ;;
                       '(s0_13491 : uint64) ←
                        ( '(temp_13486 : uint64) ←
                            (sigma (t15_13484) (usize 2) (usize 0)) ;;
                          ret (temp_13486)) ;;
                       '(s_13464 : round_constants_table_t) ←
                        ( '(temp_13490 : uint64) ←
                            ((s1_13487) .+ (t7_13488)) ;;
                           '(temp_13493 : uint64) ←
                            ((temp_13490) .+ (s0_13491)) ;;
                           '(temp_13496 : uint64) ←
                            ((temp_13493) .+ (t16_13494)) ;;
                          ret (array_upd s_13464 (i_13458) (temp_13496))) ;;
                      
                      @ret ((round_constants_table_t)) (s_13464) } : code (
                        CEfset ([s_13464_loc])) [interface
                      #val #[ SIGMA ] : sigma_inp → sigma_out ] _))) ;;
              
              @ret ((round_constants_table_t)) (s_13464) } : code (CEfset (
                  [s_13464_loc])) [interface
              #val #[ SIGMA ] : sigma_inp → sigma_out ] _))) ;;
      
      @ret (round_constants_table_t) (s_13464) } : code (CEfset (
          [s_13464_loc])) [interface #val #[ SIGMA ] : sigma_inp → sigma_out
      ] _)
    }]).
Fail Next Obligation.
Program Definition package_schedule : package _ _ _ :=
  (seq_link schedule link_rest(package_sigma)).
Fail Next Obligation.

Definition h_13501_loc : ChoiceEqualityLocation :=
  ((hash_t ; 13555%nat)).
Notation "'shuffle_inp'" := (
  round_constants_table_t '× hash_t : choice_type) (in custom pack_type at level 2).
Notation "'shuffle_out'" := (
  hash_t : choice_type) (in custom pack_type at level 2).
Definition SHUFFLE : nat :=
  (13556).
Program Definition shuffle
   : package (CEfset ([h_13501_loc])) [interface
  #val #[ CH ] : ch_inp → ch_out ; #val #[ MAJ ] : maj_inp → maj_out ;
  #val #[ SIGMA ] : sigma_inp → sigma_out ] [interface
  #val #[ SHUFFLE ] : shuffle_inp → shuffle_out ] :=
  ([package #def #[ SHUFFLE ] (temp_inp : shuffle_inp) : shuffle_out { 
    let '(
      ws_13535 , hashi_13499) := temp_inp : round_constants_table_t '× hash_t in
    #import {sig #[ CH ] : ch_inp → ch_out } as ch ;;
    let ch := fun x_0 x_1 x_2 => ch (x_0,x_1,x_2) in
    #import {sig #[ MAJ ] : maj_inp → maj_out } as maj ;;
    let maj := fun x_0 x_1 x_2 => maj (x_0,x_1,x_2) in
    #import {sig #[ SIGMA ] : sigma_inp → sigma_out } as sigma ;;
    let sigma := fun x_0 x_1 x_2 => sigma (x_0,x_1,x_2) in
    ({ code  '(h_13501 : hash_t) ←
          (ret (hashi_13499)) ;;
        #put h_13501_loc := h_13501 ;;
       '(h_13501 : (hash_t)) ←
        (foldi' (usize 0) (k_size_v) h_13501 (L2 := CEfset ([h_13501_loc])) (
              I2 := [interface #val #[ CH ] : ch_inp → ch_out ;
              #val #[ MAJ ] : maj_inp → maj_out ;
              #val #[ SIGMA ] : sigma_inp → sigma_out
              ]) (H_loc_incl := _) (H_opsig_incl := _) (fun i_13529 h_13501 =>
            ({ code  '(a0_13539 : uint64) ←
                ( temp_13502 ←
                    (array_index (h_13501) (usize 0)) ;;
                  ret (temp_13502)) ;;
               '(b0_13542 : uint64) ←
                ( temp_13504 ←
                    (array_index (h_13501) (usize 1)) ;;
                  ret (temp_13504)) ;;
               '(c0_13543 : uint64) ←
                ( temp_13506 ←
                    (array_index (h_13501) (usize 2)) ;;
                  ret (temp_13506)) ;;
               '(d0_13552 : uint64) ←
                ( temp_13508 ←
                    (array_index (h_13501) (usize 3)) ;;
                  ret (temp_13508)) ;;
               '(e0_13518 : uint64) ←
                ( temp_13510 ←
                    (array_index (h_13501) (usize 4)) ;;
                  ret (temp_13510)) ;;
               '(f0_13523 : uint64) ←
                ( temp_13512 ←
                    (array_index (h_13501) (usize 5)) ;;
                  ret (temp_13512)) ;;
               '(g0_13524 : uint64) ←
                ( temp_13514 ←
                    (array_index (h_13501) (usize 6)) ;;
                  ret (temp_13514)) ;;
               '(h0_13517 : uint64) ←
                ( temp_13516 ←
                    (array_index (h_13501) (usize 7)) ;;
                  ret (temp_13516)) ;;
               '(t1_13548 : uint64) ←
                ( '(temp_13520 : uint64) ←
                    (sigma (e0_13518) (usize 1) (usize 1)) ;;
                   '(temp_13522 : uint64) ←
                    ((h0_13517) .+ (temp_13520)) ;;
                   '(temp_13526 : uint64) ←
                    (ch (e0_13518) (f0_13523) (g0_13524)) ;;
                   '(temp_13528 : uint64) ←
                    ((temp_13522) .+ (temp_13526)) ;;
                   temp_13531 ←
                    (array_index (k_table_v) (i_13529)) ;;
                   '(temp_13533 : uint64) ←
                    ((temp_13528) .+ (temp_13531)) ;;
                   temp_13536 ←
                    (array_index (ws_13535) (i_13529)) ;;
                   '(temp_13538 : uint64) ←
                    ((temp_13533) .+ (temp_13536)) ;;
                  ret (temp_13538)) ;;
               '(t2_13549 : uint64) ←
                ( '(temp_13541 : uint64) ←
                    (sigma (a0_13539) (usize 0) (usize 1)) ;;
                   '(temp_13545 : uint64) ←
                    (maj (a0_13539) (b0_13542) (c0_13543)) ;;
                   '(temp_13547 : uint64) ←
                    ((temp_13541) .+ (temp_13545)) ;;
                  ret (temp_13547)) ;;
               '(h_13501 : hash_t) ←
                ( '(temp_13551 : uint64) ←
                    ((t1_13548) .+ (t2_13549)) ;;
                  ret (array_upd h_13501 (usize 0) (temp_13551))) ;;
              
               '(h_13501 : hash_t) ←
                (ret (array_upd h_13501 (usize 1) (a0_13539))) ;;
              
               '(h_13501 : hash_t) ←
                (ret (array_upd h_13501 (usize 2) (b0_13542))) ;;
              
               '(h_13501 : hash_t) ←
                (ret (array_upd h_13501 (usize 3) (c0_13543))) ;;
              
               '(h_13501 : hash_t) ←
                ( '(temp_13554 : uint64) ←
                    ((d0_13552) .+ (t1_13548)) ;;
                  ret (array_upd h_13501 (usize 4) (temp_13554))) ;;
              
               '(h_13501 : hash_t) ←
                (ret (array_upd h_13501 (usize 5) (e0_13518))) ;;
              
               '(h_13501 : hash_t) ←
                (ret (array_upd h_13501 (usize 6) (f0_13523))) ;;
              
               '(h_13501 : hash_t) ←
                (ret (array_upd h_13501 (usize 7) (g0_13524))) ;;
              
              @ret ((hash_t)) (h_13501) } : code (CEfset (
                  [h_13501_loc])) [interface #val #[ CH ] : ch_inp → ch_out ;
              #val #[ MAJ ] : maj_inp → maj_out ;
              #val #[ SIGMA ] : sigma_inp → sigma_out ] _))) ;;
      
      @ret (hash_t) (h_13501) } : code (CEfset ([h_13501_loc])) [interface
      #val #[ CH ] : ch_inp → ch_out ; #val #[ MAJ ] : maj_inp → maj_out ;
      #val #[ SIGMA ] : sigma_inp → sigma_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_shuffle : package _ _ _ :=
  (seq_link shuffle link_rest(package_ch,package_maj,package_sigma)).
Fail Next Obligation.

Definition h_13566_loc : ChoiceEqualityLocation :=
  ((hash_t ; 13572%nat)).
Notation "'compress_inp'" := (
  block_t '× hash_t : choice_type) (in custom pack_type at level 2).
Notation "'compress_out'" := (
  hash_t : choice_type) (in custom pack_type at level 2).
Definition COMPRESS : nat :=
  (13573).
Program Definition compress
   : package (CEfset ([h_13566_loc])) [interface
  #val #[ SCHEDULE ] : schedule_inp → schedule_out ;
  #val #[ SHUFFLE ] : shuffle_inp → shuffle_out ] [interface
  #val #[ COMPRESS ] : compress_inp → compress_out ] :=
  ([package #def #[ COMPRESS ] (temp_inp : compress_inp) : compress_out { 
    let '(block_13557 , h_in_13561) := temp_inp : block_t '× hash_t in
    #import {sig #[ SCHEDULE ] : schedule_inp → schedule_out } as schedule ;;
    let schedule := fun x_0 => schedule (x_0) in
    #import {sig #[ SHUFFLE ] : shuffle_inp → shuffle_out } as shuffle ;;
    let shuffle := fun x_0 x_1 => shuffle (x_0,x_1) in
    ({ code  '(s_13560 : round_constants_table_t) ←
        ( '(temp_13559 : round_constants_table_t) ←
            (schedule (block_13557)) ;;
          ret (temp_13559)) ;;
       '(h_13566 : hash_t) ←
          ( '(temp_13563 : hash_t) ←
              (shuffle (s_13560) (h_in_13561)) ;;
            ret (temp_13563)) ;;
        #put h_13566_loc := h_13566 ;;
       '(h_13566 : (hash_t)) ←
        (foldi' (usize 0) (usize 8) h_13566 (L2 := CEfset ([h_13566_loc])) (
              I2 := [interface
              #val #[ SCHEDULE ] : schedule_inp → schedule_out ;
              #val #[ SHUFFLE ] : shuffle_inp → shuffle_out
              ]) (H_loc_incl := _) (H_opsig_incl := _) (fun i_13564 h_13566 =>
            ({ code  '(h_13566 : hash_t) ←
                ( temp_13567 ←
                    (array_index (h_13566) (i_13564)) ;;
                   temp_13569 ←
                    (array_index (h_in_13561) (i_13564)) ;;
                   '(temp_13571 : uint64) ←
                    ((temp_13567) .+ (temp_13569)) ;;
                  ret (array_upd h_13566 (i_13564) (temp_13571))) ;;
              
              @ret ((hash_t)) (h_13566) } : code (CEfset (
                  [h_13566_loc])) [interface] _))) ;;
      
      @ret (hash_t) (h_13566) } : code (CEfset ([h_13566_loc])) [interface
      #val #[ SCHEDULE ] : schedule_inp → schedule_out ;
      #val #[ SHUFFLE ] : shuffle_inp → shuffle_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_compress : package _ _ _ :=
  (seq_link compress link_rest(package_schedule,package_shuffle)).
Fail Next Obligation.

Definition h_13590_loc : ChoiceEqualityLocation :=
  ((hash_t ; 13648%nat)).
Definition last_block_13591_loc : ChoiceEqualityLocation :=
  ((block_t ; 13649%nat)).
Definition last_block_len_13592_loc : ChoiceEqualityLocation :=
  ((uint_size ; 13650%nat)).
Definition pad_block_13627_loc : ChoiceEqualityLocation :=
  ((block_t ; 13651%nat)).
Notation "'hash_inp'" := (
  byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'hash_out'" := (
  sha512_digest_t : choice_type) (in custom pack_type at level 2).
Definition HASH : nat :=
  (13652).
Program Definition hash
   : package (CEfset (
      [h_13590_loc ; last_block_13591_loc ; last_block_len_13592_loc ; pad_block_13627_loc])) [interface
  #val #[ COMPRESS ] : compress_inp → compress_out ] [interface
  #val #[ HASH ] : hash_inp → hash_out ] :=
  ([package #def #[ HASH ] (temp_inp : hash_inp) : hash_out { 
    let '(msg_13576) := temp_inp : byte_seq in
    #import {sig #[ COMPRESS ] : compress_inp → compress_out } as compress ;;
    let compress := fun x_0 x_1 => compress (x_0,x_1) in
    ({ code  '(h_13590 : hash_t) ←
          (ret (hash_init_v)) ;;
        #put h_13590_loc := h_13590 ;;
       '(last_block_13591 : block_t) ←
          ( '(temp_13575 : block_t) ←
              (array_new_ (default : uint8) (block_size_v)) ;;
            ret (temp_13575)) ;;
        #put last_block_13591_loc := last_block_13591 ;;
       '(last_block_len_13592 : uint_size) ←
          (ret (usize 0)) ;;
        #put last_block_len_13592_loc := last_block_len_13592 ;;
       '(temp_13578 : uint_size) ←
        (seq_num_chunks (msg_13576) (block_size_v)) ;;
       temp_13647 ←
        (foldi' (usize 0) (temp_13578) prod_ce(
              h_13590,
              last_block_13591,
              last_block_len_13592
            ) (L2 := CEfset (
                [h_13590_loc ; last_block_13591_loc ; last_block_len_13592_loc ; pad_block_13627_loc])) (
              I2 := [interface
              #val #[ COMPRESS ] : compress_inp → compress_out
              ]) (H_loc_incl := _) (H_opsig_incl := _) (fun i_13579 '(
              h_13590,
              last_block_13591,
              last_block_len_13592
            ) =>
            ({ code  temp_13601 ←
                ( '(temp_13581 : (uint_size '× seq uint8)) ←
                    (seq_get_chunk (msg_13576) (block_size_v) (i_13579)) ;;
                  ret (temp_13581)) ;;
              let '(block_len_13582, block_13587) :=
                (temp_13601) : (uint_size '× seq uint8) in
               '(temp_13584 : bool_ChoiceEquality) ←
                ((block_len_13582) <.? (block_size_v)) ;;
               temp_13599 ←
                (if temp_13584:bool_ChoiceEquality
                  then (*not state*) (let temp_then :=  '(
                          last_block_13591 : block_t) ←
                        (( '(temp_13586 : block_t) ←
                              (array_new_ (default : uint8) (block_size_v)) ;;
                             '(temp_13589 : block_t) ←
                              (array_update_start (temp_13586) (block_13587)) ;;
                            ret (temp_13589))) ;;
                      #put last_block_13591_loc := last_block_13591 ;;
                    
                     '(last_block_len_13592 : uint_size) ←
                        ((ret (block_len_13582))) ;;
                      #put last_block_len_13592_loc := last_block_len_13592 ;;
                    
                    @ret ((hash_t '× block_t '× uint_size)) (prod_ce(
                        h_13590,
                        last_block_13591,
                        last_block_len_13592
                      )) in
                    ({ code temp_then } : code (CEfset (
                          [h_13590_loc ; last_block_13591_loc ; last_block_len_13592_loc])) [interface] _))
                  else  (({ code  '(compress_input_13595 : block_t) ←
                        ( '(temp_13594 : block_t) ←
                            (array_from_seq (block_size_v) (block_13587)) ;;
                          ret (temp_13594)) ;;
                       '(h_13590 : hash_t) ←
                          (( '(temp_13597 : hash_t) ←
                                (compress (compress_input_13595) (h_13590)) ;;
                              ret (temp_13597))) ;;
                        #put h_13590_loc := h_13590 ;;
                      
                      @ret ((hash_t '× block_t '× uint_size)) (prod_ce(
                          h_13590,
                          last_block_13591,
                          last_block_len_13592
                        )) } : code (CEfset (
                          [h_13590_loc ; last_block_13591_loc ; last_block_len_13592_loc])) [interface
                      #val #[ COMPRESS ] : compress_inp → compress_out
                      ] _))) ;;
              let '(h_13590, last_block_13591, last_block_len_13592) :=
                (temp_13599) : (hash_t '× block_t '× uint_size) in
              
              @ret ((hash_t '× block_t '× uint_size)) (prod_ce(
                  h_13590,
                  last_block_13591,
                  last_block_len_13592
                )) } : code (CEfset (
                  [h_13590_loc ; last_block_13591_loc ; last_block_len_13592_loc])) [interface
              #val #[ COMPRESS ] : compress_inp → compress_out ] _))) ;;
      let '(h_13590, last_block_13591, last_block_len_13592) :=
        (temp_13647) : (hash_t '× block_t '× uint_size) in
      
       '(last_block_13591 : block_t) ←
        ( '(temp_13603 : int8) ←
            (secret (@repr U8 128)) ;;
          ret (array_upd last_block_13591 (last_block_len_13592) (
              temp_13603))) ;;
      
       '(len_bist_13616 : uint128) ←
        ( '(temp_13605 : uint_size) ←
            (seq_len (msg_13576)) ;;
           '(temp_13607 : uint_size) ←
            ((temp_13605) .* (usize 8)) ;;
           '(temp_13609 : int128) ←
            (secret (pub_u128 (temp_13607))) ;;
          ret (temp_13609)) ;;
       '(temp_13611 : uint_size) ←
        ((block_size_v) .- (len_size_v)) ;;
       '(temp_13613 : bool_ChoiceEquality) ←
        ((last_block_len_13592) <.? (temp_13611)) ;;
       temp_13645 ←
        (if temp_13613:bool_ChoiceEquality
          then (*not state*) (let temp_then :=  '(
                  last_block_13591 : block_t) ←
                (( '(temp_13615 : uint_size) ←
                      ((block_size_v) .- (len_size_v)) ;;
                     '(temp_13618 : uint128_word_t) ←
                      (uint128_to_be_bytes (len_bist_13616)) ;;
                     '(temp_13620 : seq uint8) ←
                      (array_to_seq (temp_13618)) ;;
                     '(temp_13622 : block_t) ←
                      (array_update (last_block_13591) (temp_13615) (
                          temp_13620)) ;;
                    ret (temp_13622))) ;;
              #put last_block_13591_loc := last_block_13591 ;;
            
             '(h_13590 : hash_t) ←
                (( '(temp_13624 : hash_t) ←
                      (compress (last_block_13591) (h_13590)) ;;
                    ret (temp_13624))) ;;
              #put h_13590_loc := h_13590 ;;
            
            @ret ((hash_t '× block_t)) (prod_ce(h_13590, last_block_13591)) in
            ({ code temp_then } : code (CEfset (
                  [h_13590_loc ; last_block_13591_loc ; last_block_len_13592_loc])) [interface
              #val #[ COMPRESS ] : compress_inp → compress_out ] _))
          else  (({ code  '(pad_block_13627 : block_t) ←
                  ( '(temp_13626 : block_t) ←
                      (array_new_ (default : uint8) (block_size_v)) ;;
                    ret (temp_13626)) ;;
                #put pad_block_13627_loc := pad_block_13627 ;;
               '(pad_block_13627 : block_t) ←
                  (( '(temp_13629 : uint_size) ←
                        ((block_size_v) .- (len_size_v)) ;;
                       '(temp_13631 : uint128_word_t) ←
                        (uint128_to_be_bytes (len_bist_13616)) ;;
                       '(temp_13633 : seq uint8) ←
                        (array_to_seq (temp_13631)) ;;
                       '(temp_13635 : block_t) ←
                        (array_update (pad_block_13627) (temp_13629) (
                            temp_13633)) ;;
                      ret (temp_13635))) ;;
                #put pad_block_13627_loc := pad_block_13627 ;;
              
               '(h_13590 : hash_t) ←
                  (( '(temp_13637 : hash_t) ←
                        (compress (last_block_13591) (h_13590)) ;;
                      ret (temp_13637))) ;;
                #put h_13590_loc := h_13590 ;;
              
               '(h_13590 : hash_t) ←
                  (( '(temp_13639 : hash_t) ←
                        (compress (pad_block_13627) (h_13590)) ;;
                      ret (temp_13639))) ;;
                #put h_13590_loc := h_13590 ;;
              
              @ret ((hash_t '× block_t)) (prod_ce(h_13590, last_block_13591
                )) } : code (CEfset (
                  [h_13590_loc ; last_block_13591_loc ; last_block_len_13592_loc ; pad_block_13627_loc])) [interface
              #val #[ COMPRESS ] : compress_inp → compress_out ] _))) ;;
      let '(h_13590, last_block_13591) :=
        (temp_13645) : (hash_t '× block_t) in
      
       '(temp_13641 : seq int8) ←
        (array_to_be_bytes (h_13590)) ;;
       '(temp_13643 : sha512_digest_t) ←
        (array_from_seq (hash_size_v) (temp_13641)) ;;
      @ret (sha512_digest_t) (temp_13643) } : code (CEfset (
          [h_13590_loc ; last_block_13591_loc ; last_block_len_13592_loc ; pad_block_13627_loc])) [interface
      #val #[ COMPRESS ] : compress_inp → compress_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_hash : package _ _ _ :=
  (seq_link hash link_rest(package_compress)).
Fail Next Obligation.


Notation "'sha512_inp'" := (
  byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'sha512_out'" := (
  sha512_digest_t : choice_type) (in custom pack_type at level 2).
Definition SHA512 : nat :=
  (13656).
Program Definition sha512
   : package (CEfset ([])) [interface #val #[ HASH ] : hash_inp → hash_out
  ] [interface #val #[ SHA512 ] : sha512_inp → sha512_out ] :=
  ([package #def #[ SHA512 ] (temp_inp : sha512_inp) : sha512_out { 
    let '(msg_13653) := temp_inp : byte_seq in
    #import {sig #[ HASH ] : hash_inp → hash_out } as hash ;;
    let hash := fun x_0 => hash (x_0) in
    ({ code  '(temp_13655 : sha512_digest_t) ←
        (hash (msg_13653)) ;;
      @ret (sha512_digest_t) (temp_13655) } : code (CEfset ([])) [interface
      #val #[ HASH ] : hash_inp → hash_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_sha512 : package _ _ _ :=
  (seq_link sha512 link_rest(package_hash)).
Fail Next Obligation.

