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
  ((usize 64)).

Definition len_size_v : (uint_size) :=
  ((usize 8)).

Definition k_size_v : (uint_size) :=
  ((usize 64)).

Definition hash_size_v : (uint_size) :=
  (let temp_3629 : uint_size :=
      ((usize 256) ./ (usize 8)) in
    (temp_3629)).

Definition block_t  :=
  ( nseq (uint8) (block_size_v)).

Definition op_table_type_t  :=
  ( nseq (uint_size) (usize 12)).

Definition sha256_digest_t  :=
  ( nseq (uint8) (hash_size_v)).

Definition round_constants_table_t  :=
  ( nseq (uint32) (k_size_v)).

Definition hash_t  :=
  ( nseq (uint32) (usize 8)).


Notation "'ch_inp'" := (
  uint32 '× uint32 '× uint32 : choice_type) (in custom pack_type at level 2).
Notation "'ch_out'" := (uint32 : choice_type) (in custom pack_type at level 2).
Definition CH : nat :=
  (3639).
Program Definition ch
   : package (fset.fset0) [interface] [interface
  #val #[ CH ] : ch_inp → ch_out ] :=
  ([package #def #[ CH ] (temp_inp : ch_inp) : ch_out { 
    let '(
      x_3630 , y_3631 , z_3634) := temp_inp : uint32 '× uint32 '× uint32 in
    ({ code  temp_3633 ←
        ((x_3630) .& (y_3631)) ;;
       temp_3636 ←
        ((not (x_3630)) .& (z_3634)) ;;
       temp_3638 ←
        ((temp_3633) .^ (temp_3636)) ;;
      @ret (uint32) (temp_3638) } : code (fset.fset0) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_ch : package _ _ _ :=
  (ch).
Fail Next Obligation.


Notation "'maj_inp'" := (
  uint32 '× uint32 '× uint32 : choice_type) (in custom pack_type at level 2).
Notation "'maj_out'" := (uint32 : choice_type) (in custom pack_type at level 2).
Definition MAJ : nat :=
  (3653).
Program Definition maj
   : package (fset.fset0) [interface] [interface
  #val #[ MAJ ] : maj_inp → maj_out ] :=
  ([package #def #[ MAJ ] (temp_inp : maj_inp) : maj_out { 
    let '(
      x_3640 , y_3641 , z_3644) := temp_inp : uint32 '× uint32 '× uint32 in
    ({ code  temp_3643 ←
        ((x_3640) .& (y_3641)) ;;
       temp_3646 ←
        ((x_3640) .& (z_3644)) ;;
       temp_3648 ←
        ((y_3641) .& (z_3644)) ;;
       temp_3650 ←
        ((temp_3646) .^ (temp_3648)) ;;
       temp_3652 ←
        ((temp_3643) .^ (temp_3650)) ;;
      @ret (uint32) (temp_3652) } : code (fset.fset0) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_maj : package _ _ _ :=
  (maj).
Fail Next Obligation.

Definition op_table_v : (op_table_type_t) :=
  (let temp_3655 : nseq uint_size 12 :=
      (array_from_list uint_size [
          usize 2;
          usize 13;
          usize 22;
          usize 6;
          usize 11;
          usize 25;
          usize 7;
          usize 18;
          usize 3;
          usize 17;
          usize 19;
          usize 10
        ]) in
    (temp_3655)).

Definition k_table_v : (round_constants_table_t) :=
  (let temp_3657 : int32 :=
      (secret (@repr U32 1116352408)) in
    let temp_3659 : int32 :=
      (secret (@repr U32 1899447441)) in
    let temp_3661 : int32 :=
      (secret (@repr U32 3049323471)) in
    let temp_3663 : int32 :=
      (secret (@repr U32 3921009573)) in
    let temp_3665 : int32 :=
      (secret (@repr U32 961987163)) in
    let temp_3667 : int32 :=
      (secret (@repr U32 1508970993)) in
    let temp_3669 : int32 :=
      (secret (@repr U32 2453635748)) in
    let temp_3671 : int32 :=
      (secret (@repr U32 2870763221)) in
    let temp_3673 : int32 :=
      (secret (@repr U32 3624381080)) in
    let temp_3675 : int32 :=
      (secret (@repr U32 310598401)) in
    let temp_3677 : int32 :=
      (secret (@repr U32 607225278)) in
    let temp_3679 : int32 :=
      (secret (@repr U32 1426881987)) in
    let temp_3681 : int32 :=
      (secret (@repr U32 1925078388)) in
    let temp_3683 : int32 :=
      (secret (@repr U32 2162078206)) in
    let temp_3685 : int32 :=
      (secret (@repr U32 2614888103)) in
    let temp_3687 : int32 :=
      (secret (@repr U32 3248222580)) in
    let temp_3689 : int32 :=
      (secret (@repr U32 3835390401)) in
    let temp_3691 : int32 :=
      (secret (@repr U32 4022224774)) in
    let temp_3693 : int32 :=
      (secret (@repr U32 264347078)) in
    let temp_3695 : int32 :=
      (secret (@repr U32 604807628)) in
    let temp_3697 : int32 :=
      (secret (@repr U32 770255983)) in
    let temp_3699 : int32 :=
      (secret (@repr U32 1249150122)) in
    let temp_3701 : int32 :=
      (secret (@repr U32 1555081692)) in
    let temp_3703 : int32 :=
      (secret (@repr U32 1996064986)) in
    let temp_3705 : int32 :=
      (secret (@repr U32 2554220882)) in
    let temp_3707 : int32 :=
      (secret (@repr U32 2821834349)) in
    let temp_3709 : int32 :=
      (secret (@repr U32 2952996808)) in
    let temp_3711 : int32 :=
      (secret (@repr U32 3210313671)) in
    let temp_3713 : int32 :=
      (secret (@repr U32 3336571891)) in
    let temp_3715 : int32 :=
      (secret (@repr U32 3584528711)) in
    let temp_3717 : int32 :=
      (secret (@repr U32 113926993)) in
    let temp_3719 : int32 :=
      (secret (@repr U32 338241895)) in
    let temp_3721 : int32 :=
      (secret (@repr U32 666307205)) in
    let temp_3723 : int32 :=
      (secret (@repr U32 773529912)) in
    let temp_3725 : int32 :=
      (secret (@repr U32 1294757372)) in
    let temp_3727 : int32 :=
      (secret (@repr U32 1396182291)) in
    let temp_3729 : int32 :=
      (secret (@repr U32 1695183700)) in
    let temp_3731 : int32 :=
      (secret (@repr U32 1986661051)) in
    let temp_3733 : int32 :=
      (secret (@repr U32 2177026350)) in
    let temp_3735 : int32 :=
      (secret (@repr U32 2456956037)) in
    let temp_3737 : int32 :=
      (secret (@repr U32 2730485921)) in
    let temp_3739 : int32 :=
      (secret (@repr U32 2820302411)) in
    let temp_3741 : int32 :=
      (secret (@repr U32 3259730800)) in
    let temp_3743 : int32 :=
      (secret (@repr U32 3345764771)) in
    let temp_3745 : int32 :=
      (secret (@repr U32 3516065817)) in
    let temp_3747 : int32 :=
      (secret (@repr U32 3600352804)) in
    let temp_3749 : int32 :=
      (secret (@repr U32 4094571909)) in
    let temp_3751 : int32 :=
      (secret (@repr U32 275423344)) in
    let temp_3753 : int32 :=
      (secret (@repr U32 430227734)) in
    let temp_3755 : int32 :=
      (secret (@repr U32 506948616)) in
    let temp_3757 : int32 :=
      (secret (@repr U32 659060556)) in
    let temp_3759 : int32 :=
      (secret (@repr U32 883997877)) in
    let temp_3761 : int32 :=
      (secret (@repr U32 958139571)) in
    let temp_3763 : int32 :=
      (secret (@repr U32 1322822218)) in
    let temp_3765 : int32 :=
      (secret (@repr U32 1537002063)) in
    let temp_3767 : int32 :=
      (secret (@repr U32 1747873779)) in
    let temp_3769 : int32 :=
      (secret (@repr U32 1955562222)) in
    let temp_3771 : int32 :=
      (secret (@repr U32 2024104815)) in
    let temp_3773 : int32 :=
      (secret (@repr U32 2227730452)) in
    let temp_3775 : int32 :=
      (secret (@repr U32 2361852424)) in
    let temp_3777 : int32 :=
      (secret (@repr U32 2428436474)) in
    let temp_3779 : int32 :=
      (secret (@repr U32 2756734187)) in
    let temp_3781 : int32 :=
      (secret (@repr U32 3204031479)) in
    let temp_3783 : int32 :=
      (secret (@repr U32 3329325298)) in
    let temp_3785 : nseq uint32 64 :=
      (array_from_list uint32 [
          temp_3657;
          temp_3659;
          temp_3661;
          temp_3663;
          temp_3665;
          temp_3667;
          temp_3669;
          temp_3671;
          temp_3673;
          temp_3675;
          temp_3677;
          temp_3679;
          temp_3681;
          temp_3683;
          temp_3685;
          temp_3687;
          temp_3689;
          temp_3691;
          temp_3693;
          temp_3695;
          temp_3697;
          temp_3699;
          temp_3701;
          temp_3703;
          temp_3705;
          temp_3707;
          temp_3709;
          temp_3711;
          temp_3713;
          temp_3715;
          temp_3717;
          temp_3719;
          temp_3721;
          temp_3723;
          temp_3725;
          temp_3727;
          temp_3729;
          temp_3731;
          temp_3733;
          temp_3735;
          temp_3737;
          temp_3739;
          temp_3741;
          temp_3743;
          temp_3745;
          temp_3747;
          temp_3749;
          temp_3751;
          temp_3753;
          temp_3755;
          temp_3757;
          temp_3759;
          temp_3761;
          temp_3763;
          temp_3765;
          temp_3767;
          temp_3769;
          temp_3771;
          temp_3773;
          temp_3775;
          temp_3777;
          temp_3779;
          temp_3781;
          temp_3783
        ]) in
    (temp_3785)).

Definition hash_init_v : (hash_t) :=
  (let temp_3787 : int32 :=
      (secret (@repr U32 1779033703)) in
    let temp_3789 : int32 :=
      (secret (@repr U32 3144134277)) in
    let temp_3791 : int32 :=
      (secret (@repr U32 1013904242)) in
    let temp_3793 : int32 :=
      (secret (@repr U32 2773480762)) in
    let temp_3795 : int32 :=
      (secret (@repr U32 1359893119)) in
    let temp_3797 : int32 :=
      (secret (@repr U32 2600822924)) in
    let temp_3799 : int32 :=
      (secret (@repr U32 528734635)) in
    let temp_3801 : int32 :=
      (secret (@repr U32 1541459225)) in
    let temp_3803 : nseq uint32 8 :=
      (array_from_list uint32 [
          temp_3787;
          temp_3789;
          temp_3791;
          temp_3793;
          temp_3795;
          temp_3797;
          temp_3799;
          temp_3801
        ]) in
    (temp_3803)).

Definition tmp_3825_loc : ChoiceEqualityLocation :=
  ((uint32 ; 3844%nat)).
Notation "'sigma_inp'" := (
  uint32 '× uint_size '× uint_size : choice_type) (in custom pack_type at level 2).
Notation "'sigma_out'" := (
  uint32 : choice_type) (in custom pack_type at level 2).
Definition SIGMA : nat :=
  (3845).
Program Definition sigma
   : package (CEfset ([tmp_3825_loc])) [interface] [interface
  #val #[ SIGMA ] : sigma_inp → sigma_out ] :=
  ([package #def #[ SIGMA ] (temp_inp : sigma_inp) : sigma_out { 
    let '(
      x_3804 , i_3805 , op_3814) := temp_inp : uint32 '× uint_size '× uint_size in
    ({ code  '(tmp_3825 : uint32) ←
          ( '(temp_3807 : uint_size) ←
              ((usize 3) .* (i_3805)) ;;
             '(temp_3809 : uint_size) ←
              ((temp_3807) .+ (usize 2)) ;;
             temp_3811 ←
              (array_index (op_table_v) (temp_3809)) ;;
             temp_3813 ←
              (uint32_rotate_right (x_3804) (temp_3811)) ;;
            ret (temp_3813)) ;;
        #put tmp_3825_loc := tmp_3825 ;;
       '(temp_3816 : bool_ChoiceEquality) ←
        ((op_3814) =.? (usize 0)) ;;
       '(tmp_3825 : (uint32)) ←
        (if temp_3816:bool_ChoiceEquality
          then (*not state*) (let temp_then :=  '(tmp_3825 : uint32) ←
                (( '(temp_3818 : uint_size) ←
                      ((usize 3) .* (i_3805)) ;;
                     '(temp_3820 : uint_size) ←
                      ((temp_3818) .+ (usize 2)) ;;
                     temp_3822 ←
                      (array_index (op_table_v) (temp_3820)) ;;
                     temp_3824 ←
                      ((x_3804) shift_right (temp_3822)) ;;
                    ret (temp_3824))) ;;
              #put tmp_3825_loc := tmp_3825 ;;
            
            @ret ((uint32)) (tmp_3825) in
            ({ code temp_then } : code (CEfset ([tmp_3825_loc])) [interface] _))
          else @ret ((uint32)) (tmp_3825)) ;;
      
       '(temp_3827 : uint_size) ←
        ((usize 3) .* (i_3805)) ;;
       temp_3829 ←
        (array_index (op_table_v) (temp_3827)) ;;
       temp_3831 ←
        (uint32_rotate_right (x_3804) (temp_3829)) ;;
       '(temp_3833 : uint_size) ←
        ((usize 3) .* (i_3805)) ;;
       '(temp_3835 : uint_size) ←
        ((temp_3833) .+ (usize 1)) ;;
       temp_3837 ←
        (array_index (op_table_v) (temp_3835)) ;;
       temp_3839 ←
        (uint32_rotate_right (x_3804) (temp_3837)) ;;
       temp_3841 ←
        ((temp_3831) .^ (temp_3839)) ;;
       temp_3843 ←
        ((temp_3841) .^ (tmp_3825)) ;;
      @ret (uint32) (temp_3843) } : code (CEfset (
          [tmp_3825_loc])) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_sigma : package _ _ _ :=
  (sigma).
Fail Next Obligation.

Definition s_3857_loc : ChoiceEqualityLocation :=
  ((round_constants_table_t ; 3890%nat)).
Notation "'schedule_inp'" := (
  block_t : choice_type) (in custom pack_type at level 2).
Notation "'schedule_out'" := (
  round_constants_table_t : choice_type) (in custom pack_type at level 2).
Definition SCHEDULE : nat :=
  (3891).
Program Definition schedule
   : package (CEfset ([s_3857_loc])) [interface
  #val #[ SIGMA ] : sigma_inp → sigma_out ] [interface
  #val #[ SCHEDULE ] : schedule_inp → schedule_out ] :=
  ([package #def #[ SCHEDULE ] (temp_inp : schedule_inp) : schedule_out { 
    let '(block_3846) := temp_inp : block_t in
    #import {sig #[ SIGMA ] : sigma_inp → sigma_out } as sigma ;;
    let sigma := fun x_0 x_1 x_2 => sigma (x_0,x_1,x_2) in
    ({ code  '(b_3855 : seq uint32) ←
        ( temp_3848 ←
            (array_to_be_uint32s (block_3846)) ;;
          ret (temp_3848)) ;;
       '(s_3857 : round_constants_table_t) ←
          ( '(temp_3850 : round_constants_table_t) ←
              (array_new_ (default : uint32) (k_size_v)) ;;
            ret (temp_3850)) ;;
        #put s_3857_loc := s_3857 ;;
       '(s_3857 : (round_constants_table_t)) ←
        (foldi' (usize 0) (k_size_v) s_3857 (L2 := CEfset ([s_3857_loc])) (
              I2 := [interface #val #[ SIGMA ] : sigma_inp → sigma_out
              ]) (H_loc_incl := _) (H_opsig_incl := _) (fun i_3851 s_3857 =>
            ({ code  '(temp_3853 : bool_ChoiceEquality) ←
                ((i_3851) <.? (usize 16)) ;;
               '(s_3857 : (round_constants_table_t)) ←
                (if temp_3853:bool_ChoiceEquality
                  then (*not state*) (let temp_then :=  '(
                        s_3857 : round_constants_table_t) ←
                      ( '(temp_3856 : uint32) ←
                          (seq_index (b_3855) (i_3851)) ;;
                        ret (array_upd s_3857 (i_3851) (temp_3856))) ;;
                    
                    @ret ((round_constants_table_t)) (s_3857) in
                    ({ code temp_then } : code (CEfset (
                          [s_3857_loc])) [interface] _))
                  else  (({ code  '(t16_3887 : uint32) ←
                        ( '(temp_3859 : uint_size) ←
                            ((i_3851) .- (usize 16)) ;;
                           temp_3861 ←
                            (array_index (s_3857) (temp_3859)) ;;
                          ret (temp_3861)) ;;
                       '(t15_3877 : uint32) ←
                        ( '(temp_3863 : uint_size) ←
                            ((i_3851) .- (usize 15)) ;;
                           temp_3865 ←
                            (array_index (s_3857) (temp_3863)) ;;
                          ret (temp_3865)) ;;
                       '(t7_3881 : uint32) ←
                        ( '(temp_3867 : uint_size) ←
                            ((i_3851) .- (usize 7)) ;;
                           temp_3869 ←
                            (array_index (s_3857) (temp_3867)) ;;
                          ret (temp_3869)) ;;
                       '(t2_3874 : uint32) ←
                        ( '(temp_3871 : uint_size) ←
                            ((i_3851) .- (usize 2)) ;;
                           temp_3873 ←
                            (array_index (s_3857) (temp_3871)) ;;
                          ret (temp_3873)) ;;
                       '(s1_3880 : uint32) ←
                        ( '(temp_3876 : uint32) ←
                            (sigma (t2_3874) (usize 3) (usize 0)) ;;
                          ret (temp_3876)) ;;
                       '(s0_3884 : uint32) ←
                        ( '(temp_3879 : uint32) ←
                            (sigma (t15_3877) (usize 2) (usize 0)) ;;
                          ret (temp_3879)) ;;
                       '(s_3857 : round_constants_table_t) ←
                        ( '(temp_3883 : uint32) ←
                            ((s1_3880) .+ (t7_3881)) ;;
                           '(temp_3886 : uint32) ←
                            ((temp_3883) .+ (s0_3884)) ;;
                           '(temp_3889 : uint32) ←
                            ((temp_3886) .+ (t16_3887)) ;;
                          ret (array_upd s_3857 (i_3851) (temp_3889))) ;;
                      
                      @ret ((round_constants_table_t)) (s_3857) } : code (
                        CEfset ([s_3857_loc])) [interface
                      #val #[ SIGMA ] : sigma_inp → sigma_out ] _))) ;;
              
              @ret ((round_constants_table_t)) (s_3857) } : code (CEfset (
                  [s_3857_loc])) [interface
              #val #[ SIGMA ] : sigma_inp → sigma_out ] _))) ;;
      
      @ret (round_constants_table_t) (s_3857) } : code (CEfset (
          [s_3857_loc])) [interface #val #[ SIGMA ] : sigma_inp → sigma_out
      ] _)
    }]).
Fail Next Obligation.
Program Definition package_schedule : package _ _ _ :=
  (seq_link schedule link_rest(package_sigma)).
Fail Next Obligation.

Definition h_3894_loc : ChoiceEqualityLocation :=
  ((hash_t ; 3948%nat)).
Notation "'shuffle_inp'" := (
  round_constants_table_t '× hash_t : choice_type) (in custom pack_type at level 2).
Notation "'shuffle_out'" := (
  hash_t : choice_type) (in custom pack_type at level 2).
Definition SHUFFLE : nat :=
  (3949).
Program Definition shuffle
   : package (CEfset ([h_3894_loc])) [interface
  #val #[ CH ] : ch_inp → ch_out ; #val #[ MAJ ] : maj_inp → maj_out ;
  #val #[ SIGMA ] : sigma_inp → sigma_out ] [interface
  #val #[ SHUFFLE ] : shuffle_inp → shuffle_out ] :=
  ([package #def #[ SHUFFLE ] (temp_inp : shuffle_inp) : shuffle_out { 
    let '(
      ws_3928 , hashi_3892) := temp_inp : round_constants_table_t '× hash_t in
    #import {sig #[ CH ] : ch_inp → ch_out } as ch ;;
    let ch := fun x_0 x_1 x_2 => ch (x_0,x_1,x_2) in
    #import {sig #[ MAJ ] : maj_inp → maj_out } as maj ;;
    let maj := fun x_0 x_1 x_2 => maj (x_0,x_1,x_2) in
    #import {sig #[ SIGMA ] : sigma_inp → sigma_out } as sigma ;;
    let sigma := fun x_0 x_1 x_2 => sigma (x_0,x_1,x_2) in
    ({ code  '(h_3894 : hash_t) ←
          (ret (hashi_3892)) ;;
        #put h_3894_loc := h_3894 ;;
       '(h_3894 : (hash_t)) ←
        (foldi' (usize 0) (k_size_v) h_3894 (L2 := CEfset ([h_3894_loc])) (
              I2 := [interface #val #[ CH ] : ch_inp → ch_out ;
              #val #[ MAJ ] : maj_inp → maj_out ;
              #val #[ SIGMA ] : sigma_inp → sigma_out
              ]) (H_loc_incl := _) (H_opsig_incl := _) (fun i_3922 h_3894 =>
            ({ code  '(a0_3932 : uint32) ←
                ( temp_3895 ←
                    (array_index (h_3894) (usize 0)) ;;
                  ret (temp_3895)) ;;
               '(b0_3935 : uint32) ←
                ( temp_3897 ←
                    (array_index (h_3894) (usize 1)) ;;
                  ret (temp_3897)) ;;
               '(c0_3936 : uint32) ←
                ( temp_3899 ←
                    (array_index (h_3894) (usize 2)) ;;
                  ret (temp_3899)) ;;
               '(d0_3945 : uint32) ←
                ( temp_3901 ←
                    (array_index (h_3894) (usize 3)) ;;
                  ret (temp_3901)) ;;
               '(e0_3911 : uint32) ←
                ( temp_3903 ←
                    (array_index (h_3894) (usize 4)) ;;
                  ret (temp_3903)) ;;
               '(f0_3916 : uint32) ←
                ( temp_3905 ←
                    (array_index (h_3894) (usize 5)) ;;
                  ret (temp_3905)) ;;
               '(g0_3917 : uint32) ←
                ( temp_3907 ←
                    (array_index (h_3894) (usize 6)) ;;
                  ret (temp_3907)) ;;
               '(h0_3910 : uint32) ←
                ( temp_3909 ←
                    (array_index (h_3894) (usize 7)) ;;
                  ret (temp_3909)) ;;
               '(t1_3941 : uint32) ←
                ( '(temp_3913 : uint32) ←
                    (sigma (e0_3911) (usize 1) (usize 1)) ;;
                   '(temp_3915 : uint32) ←
                    ((h0_3910) .+ (temp_3913)) ;;
                   '(temp_3919 : uint32) ←
                    (ch (e0_3911) (f0_3916) (g0_3917)) ;;
                   '(temp_3921 : uint32) ←
                    ((temp_3915) .+ (temp_3919)) ;;
                   temp_3924 ←
                    (array_index (k_table_v) (i_3922)) ;;
                   '(temp_3926 : uint32) ←
                    ((temp_3921) .+ (temp_3924)) ;;
                   temp_3929 ←
                    (array_index (ws_3928) (i_3922)) ;;
                   '(temp_3931 : uint32) ←
                    ((temp_3926) .+ (temp_3929)) ;;
                  ret (temp_3931)) ;;
               '(t2_3942 : uint32) ←
                ( '(temp_3934 : uint32) ←
                    (sigma (a0_3932) (usize 0) (usize 1)) ;;
                   '(temp_3938 : uint32) ←
                    (maj (a0_3932) (b0_3935) (c0_3936)) ;;
                   '(temp_3940 : uint32) ←
                    ((temp_3934) .+ (temp_3938)) ;;
                  ret (temp_3940)) ;;
               '(h_3894 : hash_t) ←
                ( '(temp_3944 : uint32) ←
                    ((t1_3941) .+ (t2_3942)) ;;
                  ret (array_upd h_3894 (usize 0) (temp_3944))) ;;
              
               '(h_3894 : hash_t) ←
                (ret (array_upd h_3894 (usize 1) (a0_3932))) ;;
              
               '(h_3894 : hash_t) ←
                (ret (array_upd h_3894 (usize 2) (b0_3935))) ;;
              
               '(h_3894 : hash_t) ←
                (ret (array_upd h_3894 (usize 3) (c0_3936))) ;;
              
               '(h_3894 : hash_t) ←
                ( '(temp_3947 : uint32) ←
                    ((d0_3945) .+ (t1_3941)) ;;
                  ret (array_upd h_3894 (usize 4) (temp_3947))) ;;
              
               '(h_3894 : hash_t) ←
                (ret (array_upd h_3894 (usize 5) (e0_3911))) ;;
              
               '(h_3894 : hash_t) ←
                (ret (array_upd h_3894 (usize 6) (f0_3916))) ;;
              
               '(h_3894 : hash_t) ←
                (ret (array_upd h_3894 (usize 7) (g0_3917))) ;;
              
              @ret ((hash_t)) (h_3894) } : code (CEfset (
                  [h_3894_loc])) [interface #val #[ CH ] : ch_inp → ch_out ;
              #val #[ MAJ ] : maj_inp → maj_out ;
              #val #[ SIGMA ] : sigma_inp → sigma_out ] _))) ;;
      
      @ret (hash_t) (h_3894) } : code (CEfset ([h_3894_loc])) [interface
      #val #[ CH ] : ch_inp → ch_out ; #val #[ MAJ ] : maj_inp → maj_out ;
      #val #[ SIGMA ] : sigma_inp → sigma_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_shuffle : package _ _ _ :=
  (seq_link shuffle link_rest(package_ch,package_maj,package_sigma)).
Fail Next Obligation.

Definition h_3959_loc : ChoiceEqualityLocation :=
  ((hash_t ; 3965%nat)).
Notation "'compress_inp'" := (
  block_t '× hash_t : choice_type) (in custom pack_type at level 2).
Notation "'compress_out'" := (
  hash_t : choice_type) (in custom pack_type at level 2).
Definition COMPRESS : nat :=
  (3966).
Program Definition compress
   : package (CEfset ([h_3959_loc])) [interface
  #val #[ SCHEDULE ] : schedule_inp → schedule_out ;
  #val #[ SHUFFLE ] : shuffle_inp → shuffle_out ] [interface
  #val #[ COMPRESS ] : compress_inp → compress_out ] :=
  ([package #def #[ COMPRESS ] (temp_inp : compress_inp) : compress_out { 
    let '(block_3950 , h_in_3954) := temp_inp : block_t '× hash_t in
    #import {sig #[ SCHEDULE ] : schedule_inp → schedule_out } as schedule ;;
    let schedule := fun x_0 => schedule (x_0) in
    #import {sig #[ SHUFFLE ] : shuffle_inp → shuffle_out } as shuffle ;;
    let shuffle := fun x_0 x_1 => shuffle (x_0,x_1) in
    ({ code  '(s_3953 : round_constants_table_t) ←
        ( '(temp_3952 : round_constants_table_t) ←
            (schedule (block_3950)) ;;
          ret (temp_3952)) ;;
       '(h_3959 : hash_t) ←
          ( '(temp_3956 : hash_t) ←
              (shuffle (s_3953) (h_in_3954)) ;;
            ret (temp_3956)) ;;
        #put h_3959_loc := h_3959 ;;
       '(h_3959 : (hash_t)) ←
        (foldi' (usize 0) (usize 8) h_3959 (L2 := CEfset ([h_3959_loc])) (
              I2 := [interface
              #val #[ SCHEDULE ] : schedule_inp → schedule_out ;
              #val #[ SHUFFLE ] : shuffle_inp → shuffle_out
              ]) (H_loc_incl := _) (H_opsig_incl := _) (fun i_3957 h_3959 =>
            ({ code  '(h_3959 : hash_t) ←
                ( temp_3960 ←
                    (array_index (h_3959) (i_3957)) ;;
                   temp_3962 ←
                    (array_index (h_in_3954) (i_3957)) ;;
                   '(temp_3964 : uint32) ←
                    ((temp_3960) .+ (temp_3962)) ;;
                  ret (array_upd h_3959 (i_3957) (temp_3964))) ;;
              
              @ret ((hash_t)) (h_3959) } : code (CEfset (
                  [h_3959_loc])) [interface] _))) ;;
      
      @ret (hash_t) (h_3959) } : code (CEfset ([h_3959_loc])) [interface
      #val #[ SCHEDULE ] : schedule_inp → schedule_out ;
      #val #[ SHUFFLE ] : shuffle_inp → shuffle_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_compress : package _ _ _ :=
  (seq_link compress link_rest(package_schedule,package_shuffle)).
Fail Next Obligation.

Definition h_3983_loc : ChoiceEqualityLocation :=
  ((hash_t ; 4041%nat)).
Definition last_block_len_3985_loc : ChoiceEqualityLocation :=
  ((uint_size ; 4042%nat)).
Definition pad_block_4020_loc : ChoiceEqualityLocation :=
  ((block_t ; 4043%nat)).
Definition last_block_3984_loc : ChoiceEqualityLocation :=
  ((block_t ; 4044%nat)).
Notation "'hash_inp'" := (
  byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'hash_out'" := (
  sha256_digest_t : choice_type) (in custom pack_type at level 2).
Definition HASH : nat :=
  (4045).
Program Definition hash
   : package (CEfset (
      [h_3983_loc ; last_block_3984_loc ; last_block_len_3985_loc ; pad_block_4020_loc])) [interface
  #val #[ COMPRESS ] : compress_inp → compress_out ] [interface
  #val #[ HASH ] : hash_inp → hash_out ] :=
  ([package #def #[ HASH ] (temp_inp : hash_inp) : hash_out { 
    let '(msg_3969) := temp_inp : byte_seq in
    #import {sig #[ COMPRESS ] : compress_inp → compress_out } as compress ;;
    let compress := fun x_0 x_1 => compress (x_0,x_1) in
    ({ code  '(h_3983 : hash_t) ←
          (ret (hash_init_v)) ;;
        #put h_3983_loc := h_3983 ;;
       '(last_block_3984 : block_t) ←
          ( '(temp_3968 : block_t) ←
              (array_new_ (default : uint8) (block_size_v)) ;;
            ret (temp_3968)) ;;
        #put last_block_3984_loc := last_block_3984 ;;
       '(last_block_len_3985 : uint_size) ←
          (ret (usize 0)) ;;
        #put last_block_len_3985_loc := last_block_len_3985 ;;
       '(temp_3971 : uint_size) ←
        (seq_num_chunks (msg_3969) (block_size_v)) ;;
       temp_4040 ←
        (foldi' (usize 0) (temp_3971) prod_ce(
              h_3983,
              last_block_3984,
              last_block_len_3985
            ) (L2 := CEfset (
                [h_3983_loc ; last_block_3984_loc ; last_block_len_3985_loc ; pad_block_4020_loc])) (
              I2 := [interface
              #val #[ COMPRESS ] : compress_inp → compress_out
              ]) (H_loc_incl := _) (H_opsig_incl := _) (fun i_3972 '(
              h_3983,
              last_block_3984,
              last_block_len_3985
            ) =>
            ({ code  temp_3994 ←
                ( '(temp_3974 : (uint_size '× seq uint8)) ←
                    (seq_get_chunk (msg_3969) (block_size_v) (i_3972)) ;;
                  ret (temp_3974)) ;;
              let '(block_len_3975, block_3980) :=
                (temp_3994) : (uint_size '× seq uint8) in
               '(temp_3977 : bool_ChoiceEquality) ←
                ((block_len_3975) <.? (block_size_v)) ;;
               temp_3992 ←
                (if temp_3977:bool_ChoiceEquality
                  then (*not state*) (let temp_then :=  '(
                          last_block_3984 : block_t) ←
                        (( '(temp_3979 : block_t) ←
                              (array_new_ (default : uint8) (block_size_v)) ;;
                             '(temp_3982 : block_t) ←
                              (array_update_start (temp_3979) (block_3980)) ;;
                            ret (temp_3982))) ;;
                      #put last_block_3984_loc := last_block_3984 ;;
                    
                     '(last_block_len_3985 : uint_size) ←
                        ((ret (block_len_3975))) ;;
                      #put last_block_len_3985_loc := last_block_len_3985 ;;
                    
                    @ret ((hash_t '× block_t '× uint_size)) (prod_ce(
                        h_3983,
                        last_block_3984,
                        last_block_len_3985
                      )) in
                    ({ code temp_then } : code (CEfset (
                          [h_3983_loc ; last_block_3984_loc ; last_block_len_3985_loc])) [interface] _))
                  else  (({ code  '(compress_input_3988 : block_t) ←
                        ( '(temp_3987 : block_t) ←
                            (array_from_seq (block_size_v) (block_3980)) ;;
                          ret (temp_3987)) ;;
                       '(h_3983 : hash_t) ←
                          (( '(temp_3990 : hash_t) ←
                                (compress (compress_input_3988) (h_3983)) ;;
                              ret (temp_3990))) ;;
                        #put h_3983_loc := h_3983 ;;
                      
                      @ret ((hash_t '× block_t '× uint_size)) (prod_ce(
                          h_3983,
                          last_block_3984,
                          last_block_len_3985
                        )) } : code (CEfset (
                          [h_3983_loc ; last_block_3984_loc ; last_block_len_3985_loc])) [interface
                      #val #[ COMPRESS ] : compress_inp → compress_out
                      ] _))) ;;
              let '(h_3983, last_block_3984, last_block_len_3985) :=
                (temp_3992) : (hash_t '× block_t '× uint_size) in
              
              @ret ((hash_t '× block_t '× uint_size)) (prod_ce(
                  h_3983,
                  last_block_3984,
                  last_block_len_3985
                )) } : code (CEfset (
                  [h_3983_loc ; last_block_3984_loc ; last_block_len_3985_loc])) [interface
              #val #[ COMPRESS ] : compress_inp → compress_out ] _))) ;;
      let '(h_3983, last_block_3984, last_block_len_3985) :=
        (temp_4040) : (hash_t '× block_t '× uint_size) in
      
       '(last_block_3984 : block_t) ←
        ( '(temp_3996 : int8) ←
            (secret (@repr U8 128)) ;;
          ret (array_upd last_block_3984 (last_block_len_3985) (temp_3996))) ;;
      
       '(len_bist_4009 : uint64) ←
        ( '(temp_3998 : uint_size) ←
            (seq_len (msg_3969)) ;;
           '(temp_4000 : uint_size) ←
            ((temp_3998) .* (usize 8)) ;;
           '(temp_4002 : int64) ←
            (secret (pub_u64 (temp_4000))) ;;
          ret (temp_4002)) ;;
       '(temp_4004 : uint_size) ←
        ((block_size_v) .- (len_size_v)) ;;
       '(temp_4006 : bool_ChoiceEquality) ←
        ((last_block_len_3985) <.? (temp_4004)) ;;
       temp_4038 ←
        (if temp_4006:bool_ChoiceEquality
          then (*not state*) (let temp_then :=  '(last_block_3984 : block_t) ←
                (( '(temp_4008 : uint_size) ←
                      ((block_size_v) .- (len_size_v)) ;;
                     '(temp_4011 : uint64_word_t) ←
                      (uint64_to_be_bytes (len_bist_4009)) ;;
                     '(temp_4013 : seq uint8) ←
                      (array_to_seq (temp_4011)) ;;
                     '(temp_4015 : block_t) ←
                      (array_update (last_block_3984) (temp_4008) (
                          temp_4013)) ;;
                    ret (temp_4015))) ;;
              #put last_block_3984_loc := last_block_3984 ;;
            
             '(h_3983 : hash_t) ←
                (( '(temp_4017 : hash_t) ←
                      (compress (last_block_3984) (h_3983)) ;;
                    ret (temp_4017))) ;;
              #put h_3983_loc := h_3983 ;;
            
            @ret ((hash_t '× block_t)) (prod_ce(h_3983, last_block_3984)) in
            ({ code temp_then } : code (CEfset (
                  [h_3983_loc ; last_block_3984_loc ; last_block_len_3985_loc])) [interface
              #val #[ COMPRESS ] : compress_inp → compress_out ] _))
          else  (({ code  '(pad_block_4020 : block_t) ←
                  ( '(temp_4019 : block_t) ←
                      (array_new_ (default : uint8) (block_size_v)) ;;
                    ret (temp_4019)) ;;
                #put pad_block_4020_loc := pad_block_4020 ;;
               '(pad_block_4020 : block_t) ←
                  (( '(temp_4022 : uint_size) ←
                        ((block_size_v) .- (len_size_v)) ;;
                       '(temp_4024 : uint64_word_t) ←
                        (uint64_to_be_bytes (len_bist_4009)) ;;
                       '(temp_4026 : seq uint8) ←
                        (array_to_seq (temp_4024)) ;;
                       '(temp_4028 : block_t) ←
                        (array_update (pad_block_4020) (temp_4022) (
                            temp_4026)) ;;
                      ret (temp_4028))) ;;
                #put pad_block_4020_loc := pad_block_4020 ;;
              
               '(h_3983 : hash_t) ←
                  (( '(temp_4030 : hash_t) ←
                        (compress (last_block_3984) (h_3983)) ;;
                      ret (temp_4030))) ;;
                #put h_3983_loc := h_3983 ;;
              
               '(h_3983 : hash_t) ←
                  (( '(temp_4032 : hash_t) ←
                        (compress (pad_block_4020) (h_3983)) ;;
                      ret (temp_4032))) ;;
                #put h_3983_loc := h_3983 ;;
              
              @ret ((hash_t '× block_t)) (prod_ce(h_3983, last_block_3984
                )) } : code (CEfset (
                  [h_3983_loc ; last_block_3984_loc ; last_block_len_3985_loc ; pad_block_4020_loc])) [interface
              #val #[ COMPRESS ] : compress_inp → compress_out ] _))) ;;
      let '(h_3983, last_block_3984) :=
        (temp_4038) : (hash_t '× block_t) in
      
       '(temp_4034 : seq int8) ←
        (array_to_be_bytes (h_3983)) ;;
       '(temp_4036 : sha256_digest_t) ←
        (array_from_seq (hash_size_v) (temp_4034)) ;;
      @ret (sha256_digest_t) (temp_4036) } : code (CEfset (
          [h_3983_loc ; last_block_3984_loc ; last_block_len_3985_loc ; pad_block_4020_loc])) [interface
      #val #[ COMPRESS ] : compress_inp → compress_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_hash : package _ _ _ :=
  (seq_link hash link_rest(package_compress)).
Fail Next Obligation.


Notation "'sha256_inp'" := (
  byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'sha256_out'" := (
  sha256_digest_t : choice_type) (in custom pack_type at level 2).
Definition SHA256 : nat :=
  (4049).
Program Definition sha256
   : package (CEfset ([])) [interface #val #[ HASH ] : hash_inp → hash_out
  ] [interface #val #[ SHA256 ] : sha256_inp → sha256_out ] :=
  ([package #def #[ SHA256 ] (temp_inp : sha256_inp) : sha256_out { 
    let '(msg_4046) := temp_inp : byte_seq in
    #import {sig #[ HASH ] : hash_inp → hash_out } as hash ;;
    let hash := fun x_0 => hash (x_0) in
    ({ code  '(temp_4048 : sha256_digest_t) ←
        (hash (msg_4046)) ;;
      @ret (sha256_digest_t) (temp_4048) } : code (CEfset ([])) [interface
      #val #[ HASH ] : hash_inp → hash_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_sha256 : package _ _ _ :=
  (seq_link sha256 link_rest(package_hash)).
Fail Next Obligation.

