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
  usize 64.

Definition len_size_v : uint_size :=
  usize 8.

Definition k_size_v : uint_size :=
  usize 64.

Definition hash_size_v : uint_size :=
  ((usize 256) ./ (usize 8)).

Definition block_t := nseq (uint8) (block_size_v).

Definition op_table_type_t := nseq (uint_size) (usize 12).

Definition sha256_digest_t := nseq (uint8) (hash_size_v).

Definition round_constants_table_t := nseq (uint32) (k_size_v).

Definition hash_t := nseq (uint32) (usize 8).


Notation "'ch_inp'" :=(
  uint32 '× uint32 '× uint32 : choice_type) (in custom pack_type at level 2).
Notation "'ch_inp'" :=(
  uint32 '× uint32 '× uint32 : ChoiceEquality) (at level 2).
Notation "'ch_out'" :=(uint32 : choice_type) (in custom pack_type at level 2).
Notation "'ch_out'" :=(uint32 : ChoiceEquality) (at level 2).
Definition CH : nat :=
  835.
Program Definition ch (x_832 : uint32) (y_833 : uint32) (z_834 : uint32)
  : both (fset.fset0) [interface] (uint32) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (((
            lift_to_both0 x_832) .& (lift_to_both0 y_833)) .^ ((not (
              lift_to_both0 x_832)) .& (lift_to_both0 z_834)))
      ) : both (fset.fset0) [interface] (uint32)).
Fail Next Obligation.


Notation "'maj_inp'" :=(
  uint32 '× uint32 '× uint32 : choice_type) (in custom pack_type at level 2).
Notation "'maj_inp'" :=(
  uint32 '× uint32 '× uint32 : ChoiceEquality) (at level 2).
Notation "'maj_out'" :=(uint32 : choice_type) (in custom pack_type at level 2).
Notation "'maj_out'" :=(uint32 : ChoiceEquality) (at level 2).
Definition MAJ : nat :=
  839.
Program Definition maj (x_836 : uint32) (y_837 : uint32) (z_838 : uint32)
  : both (fset.fset0) [interface] (uint32) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (((
            lift_to_both0 x_836) .& (lift_to_both0 y_837)) .^ (((
              lift_to_both0 x_836) .& (lift_to_both0 z_838)) .^ ((
              lift_to_both0 y_837) .& (lift_to_both0 z_838))))
      ) : both (fset.fset0) [interface] (uint32)).
Fail Next Obligation.

Definition op_table_v : op_table_type_t :=
  array_from_list uint_size [
    (usize 2) : uint_size;
    (usize 13) : uint_size;
    (usize 22) : uint_size;
    (usize 6) : uint_size;
    (usize 11) : uint_size;
    (usize 25) : uint_size;
    (usize 7) : uint_size;
    (usize 18) : uint_size;
    (usize 3) : uint_size;
    (usize 17) : uint_size;
    (usize 19) : uint_size;
    (usize 10) : uint_size
  ].

Definition k_table_v : round_constants_table_t :=
  array_from_list uint32 [
    (secret (@repr U32 1116352408)) : uint32;
    (secret (@repr U32 1899447441)) : uint32;
    (secret (@repr U32 3049323471)) : uint32;
    (secret (@repr U32 3921009573)) : uint32;
    (secret (@repr U32 961987163)) : uint32;
    (secret (@repr U32 1508970993)) : uint32;
    (secret (@repr U32 2453635748)) : uint32;
    (secret (@repr U32 2870763221)) : uint32;
    (secret (@repr U32 3624381080)) : uint32;
    (secret (@repr U32 310598401)) : uint32;
    (secret (@repr U32 607225278)) : uint32;
    (secret (@repr U32 1426881987)) : uint32;
    (secret (@repr U32 1925078388)) : uint32;
    (secret (@repr U32 2162078206)) : uint32;
    (secret (@repr U32 2614888103)) : uint32;
    (secret (@repr U32 3248222580)) : uint32;
    (secret (@repr U32 3835390401)) : uint32;
    (secret (@repr U32 4022224774)) : uint32;
    (secret (@repr U32 264347078)) : uint32;
    (secret (@repr U32 604807628)) : uint32;
    (secret (@repr U32 770255983)) : uint32;
    (secret (@repr U32 1249150122)) : uint32;
    (secret (@repr U32 1555081692)) : uint32;
    (secret (@repr U32 1996064986)) : uint32;
    (secret (@repr U32 2554220882)) : uint32;
    (secret (@repr U32 2821834349)) : uint32;
    (secret (@repr U32 2952996808)) : uint32;
    (secret (@repr U32 3210313671)) : uint32;
    (secret (@repr U32 3336571891)) : uint32;
    (secret (@repr U32 3584528711)) : uint32;
    (secret (@repr U32 113926993)) : uint32;
    (secret (@repr U32 338241895)) : uint32;
    (secret (@repr U32 666307205)) : uint32;
    (secret (@repr U32 773529912)) : uint32;
    (secret (@repr U32 1294757372)) : uint32;
    (secret (@repr U32 1396182291)) : uint32;
    (secret (@repr U32 1695183700)) : uint32;
    (secret (@repr U32 1986661051)) : uint32;
    (secret (@repr U32 2177026350)) : uint32;
    (secret (@repr U32 2456956037)) : uint32;
    (secret (@repr U32 2730485921)) : uint32;
    (secret (@repr U32 2820302411)) : uint32;
    (secret (@repr U32 3259730800)) : uint32;
    (secret (@repr U32 3345764771)) : uint32;
    (secret (@repr U32 3516065817)) : uint32;
    (secret (@repr U32 3600352804)) : uint32;
    (secret (@repr U32 4094571909)) : uint32;
    (secret (@repr U32 275423344)) : uint32;
    (secret (@repr U32 430227734)) : uint32;
    (secret (@repr U32 506948616)) : uint32;
    (secret (@repr U32 659060556)) : uint32;
    (secret (@repr U32 883997877)) : uint32;
    (secret (@repr U32 958139571)) : uint32;
    (secret (@repr U32 1322822218)) : uint32;
    (secret (@repr U32 1537002063)) : uint32;
    (secret (@repr U32 1747873779)) : uint32;
    (secret (@repr U32 1955562222)) : uint32;
    (secret (@repr U32 2024104815)) : uint32;
    (secret (@repr U32 2227730452)) : uint32;
    (secret (@repr U32 2361852424)) : uint32;
    (secret (@repr U32 2428436474)) : uint32;
    (secret (@repr U32 2756734187)) : uint32;
    (secret (@repr U32 3204031479)) : uint32;
    (secret (@repr U32 3329325298)) : uint32
  ].

Definition hash_init_v : hash_t :=
  array_from_list uint32 [
    (secret (@repr U32 1779033703)) : uint32;
    (secret (@repr U32 3144134277)) : uint32;
    (secret (@repr U32 1013904242)) : uint32;
    (secret (@repr U32 2773480762)) : uint32;
    (secret (@repr U32 1359893119)) : uint32;
    (secret (@repr U32 2600822924)) : uint32;
    (secret (@repr U32 528734635)) : uint32;
    (secret (@repr U32 1541459225)) : uint32
  ].

Definition tmp_840_loc : ChoiceEqualityLocation :=
  (uint32 ; 841%nat).
Notation "'sigma_inp'" :=(
  uint32 '× uint_size '× uint_size : choice_type) (in custom pack_type at level 2).
Notation "'sigma_inp'" :=(
  uint32 '× uint_size '× uint_size : ChoiceEquality) (at level 2).
Notation "'sigma_out'" :=(
  uint32 : choice_type) (in custom pack_type at level 2).
Notation "'sigma_out'" :=(uint32 : ChoiceEquality) (at level 2).
Definition SIGMA : nat :=
  845.
Program Definition sigma (x_842 : uint32) (i_843 : uint_size) (
    op_844 : uint_size)
  : both (CEfset ([tmp_840_loc])) [interface] (uint32) :=
  ((letbm tmp_840 : uint32 loc( tmp_840_loc ) :=
        uint32_rotate_right (lift_to_both0 x_842) (array_index (op_table_v) (((
                lift_to_both0 (usize 3)) .* (lift_to_both0 i_843)) .+ (
              lift_to_both0 (usize 2)))) in
      letb '(tmp_840) :=
        if (lift_to_both0 op_844) =.? (lift_to_both0 (
            usize 0)) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset ([tmp_840_loc])) (L2 := CEfset (
            [tmp_840_loc])) (I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
          letbm tmp_840 loc( tmp_840_loc ) :=
            (lift_to_both0 x_842) shift_right (array_index (op_table_v) (((
                    lift_to_both0 (usize 3)) .* (lift_to_both0 i_843)) .+ (
                  lift_to_both0 (usize 2)))) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 tmp_840)
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          lift_to_both0 tmp_840)
         in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (((uint32_rotate_right (
              lift_to_both0 x_842) (array_index (op_table_v) ((lift_to_both0 (
                    usize 3)) .* (lift_to_both0 i_843)))) .^ (
            uint32_rotate_right (lift_to_both0 x_842) (array_index (
                op_table_v) (((lift_to_both0 (usize 3)) .* (
                    lift_to_both0 i_843)) .+ (lift_to_both0 (usize 1)))))) .^ (
          lift_to_both0 tmp_840))
      ) : both (CEfset ([tmp_840_loc])) [interface] (uint32)).
Fail Next Obligation.

Definition s_846_loc : ChoiceEqualityLocation :=
  (round_constants_table_t ; 847%nat).
Notation "'schedule_inp'" :=(
  block_t : choice_type) (in custom pack_type at level 2).
Notation "'schedule_inp'" :=(block_t : ChoiceEquality) (at level 2).
Notation "'schedule_out'" :=(
  round_constants_table_t : choice_type) (in custom pack_type at level 2).
Notation "'schedule_out'" :=(
  round_constants_table_t : ChoiceEquality) (at level 2).
Definition SCHEDULE : nat :=
  857.
Program Definition schedule (block_848 : block_t)
  : both (CEfset ([tmp_840_loc ; s_846_loc])) [interface] (
    round_constants_table_t) :=
  ((letb b_849 : seq uint32 := array_to_be_uint32s (lift_to_both0 block_848) in
      letbm s_846 : round_constants_table_t loc( s_846_loc ) :=
        array_new_ (default : uint32) (k_size_v) in
      letb s_846 :=
        foldi_both' (lift_to_both0 (usize 0)) (lift_to_both0 k_size_v) s_846 (
            L := (CEfset ([tmp_840_loc ; s_846_loc]))) (I := [interface]) (
            fun i_850 s_846 =>
            letb '(s_846) :=
              if (lift_to_both0 i_850) <.? (lift_to_both0 (
                  usize 16)) :bool_ChoiceEquality
              then lift_scope (L1 := CEfset ([s_846_loc])) (L2 := CEfset (
                  [tmp_840_loc ; s_846_loc])) (I1 := [interface]) (
                I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
                letb s_846 : round_constants_table_t :=
                  array_upd s_846 (lift_to_both0 i_850) (is_pure (seq_index (
                        b_849) (lift_to_both0 i_850))) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                  lift_to_both0 s_846)
                )
              else  lift_scope (L1 := CEfset ([tmp_840_loc ; s_846_loc])) (
                L2 := CEfset ([tmp_840_loc ; s_846_loc])) (I1 := [interface]) (
                I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
                letb t16_851 : uint32 :=
                  array_index (s_846) ((lift_to_both0 i_850) .- (lift_to_both0 (
                        usize 16))) in
                letb t15_852 : uint32 :=
                  array_index (s_846) ((lift_to_both0 i_850) .- (lift_to_both0 (
                        usize 15))) in
                letb t7_853 : uint32 :=
                  array_index (s_846) ((lift_to_both0 i_850) .- (lift_to_both0 (
                        usize 7))) in
                letb t2_854 : uint32 :=
                  array_index (s_846) ((lift_to_both0 i_850) .- (lift_to_both0 (
                        usize 2))) in
                letb s1_855 : uint32 :=
                  sigma (lift_to_both0 t2_854) (lift_to_both0 (usize 3)) (
                    lift_to_both0 (usize 0)) in
                letb s0_856 : uint32 :=
                  sigma (lift_to_both0 t15_852) (lift_to_both0 (usize 2)) (
                    lift_to_both0 (usize 0)) in
                letb s_846 : round_constants_table_t :=
                  array_upd s_846 (lift_to_both0 i_850) (is_pure ((((
                            lift_to_both0 s1_855) .+ (
                            lift_to_both0 t7_853)) .+ (
                          lift_to_both0 s0_856)) .+ (lift_to_both0 t16_851))) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                  lift_to_both0 s_846)
                ) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 s_846)
            ) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 s_846)
      ) : both (CEfset ([tmp_840_loc ; s_846_loc])) [interface] (
      round_constants_table_t)).
Fail Next Obligation.

Definition h_858_loc : ChoiceEqualityLocation :=
  (hash_t ; 859%nat).
Notation "'shuffle_inp'" :=(
  round_constants_table_t '× hash_t : choice_type) (in custom pack_type at level 2).
Notation "'shuffle_inp'" :=(
  round_constants_table_t '× hash_t : ChoiceEquality) (at level 2).
Notation "'shuffle_out'" :=(
  hash_t : choice_type) (in custom pack_type at level 2).
Notation "'shuffle_out'" :=(hash_t : ChoiceEquality) (at level 2).
Definition SHUFFLE : nat :=
  873.
Program Definition shuffle (ws_870 : round_constants_table_t) (
    hashi_860 : hash_t)
  : both (CEfset ([tmp_840_loc ; h_858_loc])) [interface] (hash_t) :=
  ((letbm h_858 : hash_t loc( h_858_loc ) := lift_to_both0 hashi_860 in
      letb h_858 :=
        foldi_both' (lift_to_both0 (usize 0)) (lift_to_both0 k_size_v) h_858 (
            L := (CEfset ([tmp_840_loc ; h_858_loc]))) (I := [interface]) (
            fun i_861 h_858 =>
            letb a0_862 : uint32 :=
              array_index (h_858) (lift_to_both0 (usize 0)) in
            letb b0_863 : uint32 :=
              array_index (h_858) (lift_to_both0 (usize 1)) in
            letb c0_864 : uint32 :=
              array_index (h_858) (lift_to_both0 (usize 2)) in
            letb d0_865 : uint32 :=
              array_index (h_858) (lift_to_both0 (usize 3)) in
            letb e0_866 : uint32 :=
              array_index (h_858) (lift_to_both0 (usize 4)) in
            letb f0_867 : uint32 :=
              array_index (h_858) (lift_to_both0 (usize 5)) in
            letb g0_868 : uint32 :=
              array_index (h_858) (lift_to_both0 (usize 6)) in
            letb h0_869 : uint32 :=
              array_index (h_858) (lift_to_both0 (usize 7)) in
            letb t1_871 : uint32 :=
              ((((lift_to_both0 h0_869) .+ (sigma (lift_to_both0 e0_866) (
                        lift_to_both0 (usize 1)) (lift_to_both0 (
                          usize 1)))) .+ (ch (lift_to_both0 e0_866) (
                      lift_to_both0 f0_867) (lift_to_both0 g0_868))) .+ (
                  array_index (k_table_v) (lift_to_both0 i_861))) .+ (
                array_index (ws_870) (lift_to_both0 i_861)) in
            letb t2_872 : uint32 :=
              (sigma (lift_to_both0 a0_862) (lift_to_both0 (usize 0)) (
                  lift_to_both0 (usize 1))) .+ (maj (lift_to_both0 a0_862) (
                  lift_to_both0 b0_863) (lift_to_both0 c0_864)) in
            letb h_858 : hash_t :=
              array_upd h_858 (lift_to_both0 (usize 0)) (is_pure ((
                    lift_to_both0 t1_871) .+ (lift_to_both0 t2_872))) in
            letb h_858 : hash_t :=
              array_upd h_858 (lift_to_both0 (usize 1)) (is_pure (
                  lift_to_both0 a0_862)) in
            letb h_858 : hash_t :=
              array_upd h_858 (lift_to_both0 (usize 2)) (is_pure (
                  lift_to_both0 b0_863)) in
            letb h_858 : hash_t :=
              array_upd h_858 (lift_to_both0 (usize 3)) (is_pure (
                  lift_to_both0 c0_864)) in
            letb h_858 : hash_t :=
              array_upd h_858 (lift_to_both0 (usize 4)) (is_pure ((
                    lift_to_both0 d0_865) .+ (lift_to_both0 t1_871))) in
            letb h_858 : hash_t :=
              array_upd h_858 (lift_to_both0 (usize 5)) (is_pure (
                  lift_to_both0 e0_866)) in
            letb h_858 : hash_t :=
              array_upd h_858 (lift_to_both0 (usize 6)) (is_pure (
                  lift_to_both0 f0_867)) in
            letb h_858 : hash_t :=
              array_upd h_858 (lift_to_both0 (usize 7)) (is_pure (
                  lift_to_both0 g0_868)) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 h_858)
            ) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 h_858)
      ) : both (CEfset ([tmp_840_loc ; h_858_loc])) [interface] (hash_t)).
Fail Next Obligation.

Definition h_874_loc : ChoiceEqualityLocation :=
  (hash_t ; 875%nat).
Notation "'compress_inp'" :=(
  block_t '× hash_t : choice_type) (in custom pack_type at level 2).
Notation "'compress_inp'" :=(block_t '× hash_t : ChoiceEquality) (at level 2).
Notation "'compress_out'" :=(
  hash_t : choice_type) (in custom pack_type at level 2).
Notation "'compress_out'" :=(hash_t : ChoiceEquality) (at level 2).
Definition COMPRESS : nat :=
  880.
Program Definition compress (block_876 : block_t) (h_in_878 : hash_t)
  : both (CEfset (
      [tmp_840_loc ; s_846_loc ; h_858_loc ; h_874_loc])) [interface] (
    hash_t) :=
  ((letb s_877 : round_constants_table_t :=
        schedule (lift_to_both0 block_876) in
      letbm h_874 : hash_t loc( h_874_loc ) :=
        shuffle (lift_to_both0 s_877) (lift_to_both0 h_in_878) in
      letb h_874 :=
        foldi_both' (lift_to_both0 (usize 0)) (lift_to_both0 (usize 8)) h_874 (
            L := (CEfset ([tmp_840_loc ; s_846_loc ; h_858_loc ; h_874_loc]))) (
            I := [interface]) (fun i_879 h_874 =>
            letb h_874 : hash_t :=
              array_upd h_874 (lift_to_both0 i_879) (is_pure ((array_index (
                      h_874) (lift_to_both0 i_879)) .+ (array_index (h_in_878) (
                      lift_to_both0 i_879)))) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 h_874)
            ) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 h_874)
      ) : both (CEfset (
        [tmp_840_loc ; s_846_loc ; h_858_loc ; h_874_loc])) [interface] (
      hash_t)).
Fail Next Obligation.

Definition last_block_882_loc : ChoiceEqualityLocation :=
  (block_t ; 885%nat).
Definition last_block_len_883_loc : ChoiceEqualityLocation :=
  (uint_size ; 886%nat).
Definition h_881_loc : ChoiceEqualityLocation :=
  (hash_t ; 887%nat).
Definition pad_block_884_loc : ChoiceEqualityLocation :=
  (block_t ; 888%nat).
Notation "'hash_inp'" :=(
  byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'hash_inp'" :=(byte_seq : ChoiceEquality) (at level 2).
Notation "'hash_out'" :=(
  sha256_digest_t : choice_type) (in custom pack_type at level 2).
Notation "'hash_out'" :=(sha256_digest_t : ChoiceEquality) (at level 2).
Definition HASH : nat :=
  895.
Program Definition hash (msg_889 : byte_seq)
  : both (CEfset (
      [tmp_840_loc ; s_846_loc ; h_858_loc ; h_874_loc ; h_881_loc ; last_block_882_loc ; last_block_len_883_loc ; pad_block_884_loc])) [interface] (
    sha256_digest_t) :=
  ((letbm h_881 : hash_t loc( h_881_loc ) := lift_to_both0 hash_init_v in
      letbm last_block_882 : block_t loc( last_block_882_loc ) :=
        array_new_ (default : uint8) (block_size_v) in
      letbm last_block_len_883 : uint_size loc( last_block_len_883_loc ) :=
        lift_to_both0 (usize 0) in
      letb '(h_881, last_block_882, last_block_len_883) :=
        foldi_both' (lift_to_both0 (usize 0)) (seq_num_chunks (
              lift_to_both0 msg_889) (lift_to_both0 block_size_v)) prod_ce(
            h_881,
            last_block_882,
            last_block_len_883
          ) (L := (CEfset (
                [tmp_840_loc ; s_846_loc ; h_858_loc ; h_874_loc ; h_881_loc ; last_block_882_loc ; last_block_len_883_loc ; pad_block_884_loc]))) (
            I := [interface]) (fun i_890 '(
              h_881,
              last_block_882,
              last_block_len_883
            ) =>
            letb '(block_len_891, block_892) : (uint_size '× seq uint8) :=
              seq_get_chunk (lift_to_both0 msg_889) (
                lift_to_both0 block_size_v) (lift_to_both0 i_890) in
            letb '(h_881, last_block_882, last_block_len_883) :=
              if (lift_to_both0 block_len_891) <.? (
                lift_to_both0 block_size_v) :bool_ChoiceEquality
              then lift_scope (L1 := CEfset (
                  [h_881_loc ; last_block_882_loc ; last_block_len_883_loc])) (
                L2 := CEfset (
                  [tmp_840_loc ; s_846_loc ; h_858_loc ; h_874_loc ; h_881_loc ; last_block_882_loc ; last_block_len_883_loc])) (
                I1 := [interface]) (
                I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
                letbm last_block_882 loc( last_block_882_loc ) :=
                  array_update_start (array_new_ (default : uint8) (
                      block_size_v)) (lift_to_both0 block_892) in
                letbm last_block_len_883 loc( last_block_len_883_loc ) :=
                  lift_to_both0 block_len_891 in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                    lift_to_both0 h_881,
                    lift_to_both0 last_block_882,
                    lift_to_both0 last_block_len_883
                  ))
                )
              else  lift_scope (L1 := CEfset (
                  [tmp_840_loc ; s_846_loc ; h_858_loc ; h_874_loc ; h_881_loc ; last_block_882_loc ; last_block_len_883_loc])) (
                L2 := CEfset (
                  [tmp_840_loc ; s_846_loc ; h_858_loc ; h_874_loc ; h_881_loc ; last_block_882_loc ; last_block_len_883_loc])) (
                I1 := [interface]) (
                I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
                letb compress_input_893 : block_t :=
                  array_from_seq (block_size_v) (lift_to_both0 block_892) in
                letbm h_881 loc( h_881_loc ) :=
                  compress (lift_to_both0 compress_input_893) (
                    lift_to_both0 h_881) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                    lift_to_both0 h_881,
                    lift_to_both0 last_block_882,
                    lift_to_both0 last_block_len_883
                  ))
                ) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                lift_to_both0 h_881,
                lift_to_both0 last_block_882,
                lift_to_both0 last_block_len_883
              ))
            ) in
      letb last_block_882 : block_t :=
        array_upd last_block_882 (lift_to_both0 last_block_len_883) (is_pure (
            secret (lift_to_both0 (@repr U8 128)))) in
      letb len_bist_894 : uint64 :=
        secret (pub_u64 (is_pure ((seq_len (lift_to_both0 msg_889)) .* (
                lift_to_both0 (usize 8))))) in
      letb '(h_881, last_block_882) :=
        if (lift_to_both0 last_block_len_883) <.? ((
            lift_to_both0 block_size_v) .- (
            lift_to_both0 len_size_v)) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset (
            [tmp_840_loc ; s_846_loc ; h_858_loc ; h_874_loc ; h_881_loc ; last_block_882_loc ; last_block_len_883_loc])) (
          L2 := CEfset (
            [tmp_840_loc ; s_846_loc ; h_858_loc ; h_874_loc ; h_881_loc ; last_block_882_loc ; last_block_len_883_loc ; pad_block_884_loc])) (
          I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
          letbm last_block_882 loc( last_block_882_loc ) :=
            array_update (lift_to_both0 last_block_882) ((
                lift_to_both0 block_size_v) .- (lift_to_both0 len_size_v)) (
              array_to_seq (uint64_to_be_bytes (lift_to_both0 len_bist_894))) in
          letbm h_881 loc( h_881_loc ) :=
            compress (lift_to_both0 last_block_882) (lift_to_both0 h_881) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
              lift_to_both0 h_881,
              lift_to_both0 last_block_882
            ))
          )
        else  lift_scope (L1 := CEfset (
            [tmp_840_loc ; s_846_loc ; h_858_loc ; h_874_loc ; h_881_loc ; last_block_882_loc ; last_block_len_883_loc ; pad_block_884_loc])) (
          L2 := CEfset (
            [tmp_840_loc ; s_846_loc ; h_858_loc ; h_874_loc ; h_881_loc ; last_block_882_loc ; last_block_len_883_loc ; pad_block_884_loc])) (
          I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
          letbm pad_block_884 : block_t loc( pad_block_884_loc ) :=
            array_new_ (default : uint8) (block_size_v) in
          letbm pad_block_884 loc( pad_block_884_loc ) :=
            array_update (lift_to_both0 pad_block_884) ((
                lift_to_both0 block_size_v) .- (lift_to_both0 len_size_v)) (
              array_to_seq (uint64_to_be_bytes (lift_to_both0 len_bist_894))) in
          letbm h_881 loc( h_881_loc ) :=
            compress (lift_to_both0 last_block_882) (lift_to_both0 h_881) in
          letbm h_881 loc( h_881_loc ) :=
            compress (lift_to_both0 pad_block_884) (lift_to_both0 h_881) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
              lift_to_both0 h_881,
              lift_to_both0 last_block_882
            ))
          ) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (array_from_seq (
          hash_size_v) (array_to_be_bytes (lift_to_both0 h_881)))
      ) : both (CEfset (
        [tmp_840_loc ; s_846_loc ; h_858_loc ; h_874_loc ; h_881_loc ; last_block_882_loc ; last_block_len_883_loc ; pad_block_884_loc])) [interface] (
      sha256_digest_t)).
Fail Next Obligation.


Notation "'sha256_inp'" :=(
  byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'sha256_inp'" :=(byte_seq : ChoiceEquality) (at level 2).
Notation "'sha256_out'" :=(
  sha256_digest_t : choice_type) (in custom pack_type at level 2).
Notation "'sha256_out'" :=(sha256_digest_t : ChoiceEquality) (at level 2).
Definition SHA256 : nat :=
  897.
Program Definition sha256 (msg_896 : byte_seq)
  : both (CEfset (
      [tmp_840_loc ; s_846_loc ; h_858_loc ; h_874_loc ; h_881_loc ; last_block_882_loc ; last_block_len_883_loc ; pad_block_884_loc])) [interface] (
    sha256_digest_t) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (hash (
          lift_to_both0 msg_896))
      ) : both (CEfset (
        [tmp_840_loc ; s_846_loc ; h_858_loc ; h_874_loc ; h_881_loc ; last_block_882_loc ; last_block_len_883_loc ; pad_block_884_loc])) [interface] (
      sha256_digest_t)).
Fail Next Obligation.

