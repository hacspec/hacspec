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

Require Import Hacspec_Edwards25519.

Require Import Hacspec_Sha512.

Definition b_in_bytes_v : (uint_size) :=
  ((usize 64)).

Definition s_in_bytes_v : (uint_size) :=
  ((usize 128)).

Definition l_v : (uint_size) :=
  ((usize 48)).

Definition j_v : (int128) :=
  ((@repr U128 486662)).

Definition z_v : (int128) :=
  ((@repr U128 2)).

Definition arr_ed25519_field_element_t  :=
  ( nseq (uint64) (usize 4)).

Definition ed_field_hash_canvas_t  :=
  (nseq (int8) (64)).
Definition ed_field_hash_t  :=
  (nat_mod 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed).

Definition error_t : ChoiceEquality :=
  (unit_ChoiceEquality).
Definition ExpandMessageAbort : error_t :=
  ( tt).

Definition eqb_error_t (x y : error_t) : bool_ChoiceEquality :=
  (match x with
       | ExpandMessageAbort => match y with | ExpandMessageAbort=> true end
       end.).

Definition eqb_leibniz_error_t (x y : error_t) : eqb_error_t x y = true <-> x = y.
Proof. split. intros; destruct x ; destruct y ; try (f_equal ; apply eqb_leibniz) ; easy. intros ; subst ; destruct y ; try reflexivity ; try (apply eqb_refl). Qed.

Instance eq_dec_error_t : EqDec (error_t) :=
Build_EqDec (error_t) (eqb_error_t) (eqb_leibniz_error_t).


Notation "'byte_seq_result_t'" := ((result error_t byte_seq)) : hacspec_scope.

Notation "'seq_ed_result_t'" := ((
  result error_t seq ed25519_field_element_t)) : hacspec_scope.

Notation "'ed_point_result_t'" := ((result error_t ed_point_t)) : hacspec_scope.

Definition p_1_2_v : (arr_ed25519_field_element_t) :=
  (let temp_13658 : int64 :=
      (secret (@repr U64 4611686018427387903)) in
    let temp_13660 : int64 :=
      (secret (@repr U64 18446744073709551615)) in
    let temp_13662 : int64 :=
      (secret (@repr U64 18446744073709551615)) in
    let temp_13664 : int64 :=
      (secret (@repr U64 18446744073709551606)) in
    let temp_13666 : nseq uint64 4 :=
      (array_from_list uint64 [temp_13658; temp_13660; temp_13662; temp_13664
        ]) in
    (temp_13666)).

Definition p_3_8_v : (arr_ed25519_field_element_t) :=
  (let temp_13668 : int64 :=
      (secret (@repr U64 1152921504606846975)) in
    let temp_13670 : int64 :=
      (secret (@repr U64 18446744073709551615)) in
    let temp_13672 : int64 :=
      (secret (@repr U64 18446744073709551615)) in
    let temp_13674 : int64 :=
      (secret (@repr U64 18446744073709551614)) in
    let temp_13676 : nseq uint64 4 :=
      (array_from_list uint64 [temp_13668; temp_13670; temp_13672; temp_13674
        ]) in
    (temp_13676)).

Definition p_5_8_v : (arr_ed25519_field_element_t) :=
  (let temp_13678 : int64 :=
      (secret (@repr U64 1152921504606846975)) in
    let temp_13680 : int64 :=
      (secret (@repr U64 18446744073709551615)) in
    let temp_13682 : int64 :=
      (secret (@repr U64 18446744073709551615)) in
    let temp_13684 : int64 :=
      (secret (@repr U64 18446744073709551613)) in
    let temp_13686 : nseq uint64 4 :=
      (array_from_list uint64 [temp_13678; temp_13680; temp_13682; temp_13684
        ]) in
    (temp_13686)).

Definition uniform_bytes_13781_loc : ChoiceEqualityLocation :=
  ((seq uint8 ; 13789%nat)).
Definition b_i_13758_loc : ChoiceEqualityLocation :=
  ((seq uint8 ; 13790%nat)).
Definition result_13784_loc : ChoiceEqualityLocation :=
  (((result error_t byte_seq) ; 13791%nat)).
Definition l_i_b_str_13728_loc : ChoiceEqualityLocation :=
  ((seq uint8 ; 13792%nat)).
Notation "'expand_message_xmd_inp'" := (
  byte_seq '× byte_seq '× uint_size : choice_type) (in custom pack_type at level 2).
Notation "'expand_message_xmd_out'" := (
  byte_seq_result_t : choice_type) (in custom pack_type at level 2).
Definition EXPAND_MESSAGE_XMD : nat :=
  (13793).
Program Definition expand_message_xmd
   : package (CEfset (
      [result_13784_loc ; l_i_b_str_13728_loc ; b_i_13758_loc ; uniform_bytes_13781_loc])) [interface
  #val #[ HASH ] : hash_inp → hash_out ] [interface
  #val #[ EXPAND_MESSAGE_XMD ] : expand_message_xmd_inp → expand_message_xmd_out
  ] :=
  (
    [package #def #[ EXPAND_MESSAGE_XMD ] (temp_inp : expand_message_xmd_inp) : expand_message_xmd_out { 
    let '(
      msg_13725 , dst_13701 , len_in_bytes_13687) := temp_inp : byte_seq '× byte_seq '× uint_size in
    #import {sig #[ HASH ] : hash_inp → hash_out } as hash ;;
    let hash := fun x_0 => hash (x_0) in
    ({ code  '(ell_13694 : uint_size) ←
        ( '(temp_13689 : uint_size) ←
            ((len_in_bytes_13687) .+ (b_in_bytes_v)) ;;
           '(temp_13691 : uint_size) ←
            ((temp_13689) .- (usize 1)) ;;
           '(temp_13693 : uint_size) ←
            ((temp_13691) ./ (b_in_bytes_v)) ;;
          ret (temp_13693)) ;;
       '(result_13784 : (result error_t byte_seq)) ←
          (ret (@inr byte_seq error_t (ExpandMessageAbort))) ;;
        #put result_13784_loc := result_13784 ;;
       '(temp_13696 : bool_ChoiceEquality) ←
        ((ell_13694) >.? (usize 255)) ;;
       '(temp_13698 : bool_ChoiceEquality) ←
        ((len_in_bytes_13687) >.? (usize 65535)) ;;
       '(temp_13700 : bool_ChoiceEquality) ←
        ((temp_13696) || (temp_13698)) ;;
       '(temp_13703 : uint_size) ←
        (seq_len (dst_13701)) ;;
       '(temp_13705 : bool_ChoiceEquality) ←
        ((temp_13703) >.? (usize 255)) ;;
       '(temp_13707 : bool_ChoiceEquality) ←
        ((temp_13700) || (temp_13705)) ;;
       '(result_13784 : ((result error_t byte_seq))) ←
        (if negb (temp_13707):bool_ChoiceEquality
          then (*not state*) (let temp_then :=  '(
                dst_prime_13735 : seq uint8) ←
              ( '(temp_13709 : uint_size) ←
                  (seq_len (dst_13701)) ;;
                 temp_13711 ←
                  (uint8_from_usize (temp_13709)) ;;
                 '(temp_13713 : byte_seq) ←
                  (seq_push (dst_13701) (temp_13711)) ;;
                ret (temp_13713)) ;;
             '(z_pad_13724 : seq uint8) ←
              ( temp_13715 ←
                  (seq_new_ (default : uint8) (s_in_bytes_v)) ;;
                ret (temp_13715)) ;;
             '(l_i_b_str_13728 : seq uint8) ←
                ( temp_13717 ←
                    (seq_new_ (default : uint8) (usize 2)) ;;
                  ret (temp_13717)) ;;
              #put l_i_b_str_13728_loc := l_i_b_str_13728 ;;
             '(l_i_b_str_13728 : seq uint8) ←
              ( '(temp_13719 : uint_size) ←
                  ((len_in_bytes_13687) ./ (usize 256)) ;;
                 temp_13721 ←
                  (uint8_from_usize (temp_13719)) ;;
                ret (seq_upd l_i_b_str_13728 (usize 0) (temp_13721))) ;;
            
             '(l_i_b_str_13728 : seq uint8) ←
              ( temp_13723 ←
                  (uint8_from_usize (len_in_bytes_13687)) ;;
                ret (seq_upd l_i_b_str_13728 (usize 1) (temp_13723))) ;;
            
             '(msg_prime_13738 : seq uint8) ←
              ( '(temp_13727 : seq uint8) ←
                  (seq_concat (z_pad_13724) (msg_13725)) ;;
                 '(temp_13730 : seq uint8) ←
                  (seq_concat (temp_13727) (l_i_b_str_13728)) ;;
                 temp_13732 ←
                  (seq_new_ (default : uint8) (usize 1)) ;;
                 '(temp_13734 : seq uint8) ←
                  (seq_concat (temp_13730) (temp_13732)) ;;
                 '(temp_13737 : seq uint8) ←
                  (seq_concat (temp_13734) (dst_prime_13735)) ;;
                ret (temp_13737)) ;;
             '(b_0_13745 : seq uint8) ←
              ( temp_13740 ←
                  (hash (msg_prime_13738)) ;;
                 '(temp_13742 : seq uint8) ←
                  (array_to_seq (temp_13740)) ;;
                 '(temp_13744 : byte_seq) ←
                  (seq_from_seq (temp_13742)) ;;
                ret (temp_13744)) ;;
             '(b_i_13758 : seq uint8) ←
                ( '(temp_13747 : int8) ←
                    (secret (@repr U8 1)) ;;
                   '(temp_13749 : seq uint8) ←
                    (seq_push (b_0_13745) (temp_13747)) ;;
                   '(temp_13751 : seq uint8) ←
                    (seq_concat (temp_13749) (dst_prime_13735)) ;;
                   temp_13753 ←
                    (hash (temp_13751)) ;;
                   '(temp_13755 : seq uint8) ←
                    (array_to_seq (temp_13753)) ;;
                   '(temp_13757 : byte_seq) ←
                    (seq_from_seq (temp_13755)) ;;
                  ret (temp_13757)) ;;
              #put b_i_13758_loc := b_i_13758 ;;
             '(uniform_bytes_13781 : seq uint8) ←
                ( '(temp_13760 : byte_seq) ←
                    (seq_from_seq (b_i_13758)) ;;
                  ret (temp_13760)) ;;
              #put uniform_bytes_13781_loc := uniform_bytes_13781 ;;
             '(temp_13762 : uint_size) ←
              ((ell_13694) .+ (usize 1)) ;;
             temp_13788 ←
              (foldi' (usize 2) (temp_13762) prod_ce(
                    b_i_13758,
                    uniform_bytes_13781
                  ) (L2 := CEfset (
                      [result_13784_loc ; l_i_b_str_13728_loc ; b_i_13758_loc ; uniform_bytes_13781_loc])) (
                    I2 := [interface #val #[ HASH ] : hash_inp → hash_out
                    ]) (H_loc_incl := _) (H_opsig_incl := _) (fun i_13768 '(
                    b_i_13758,
                    uniform_bytes_13781
                  ) =>
                  ({ code  '(t_13765 : seq uint8) ←
                      ( '(temp_13764 : byte_seq) ←
                          (seq_from_seq (b_0_13745)) ;;
                        ret (temp_13764)) ;;
                     '(b_i_13758 : seq uint8) ←
                        (( temp_13767 ←
                              ((t_13765) seq_xor (b_i_13758)) ;;
                             temp_13770 ←
                              (uint8_from_usize (i_13768)) ;;
                             '(temp_13772 : seq uint8) ←
                              (seq_push (temp_13767) (temp_13770)) ;;
                             '(temp_13774 : seq uint8) ←
                              (seq_concat (temp_13772) (dst_prime_13735)) ;;
                             temp_13776 ←
                              (hash (temp_13774)) ;;
                             '(temp_13778 : seq uint8) ←
                              (array_to_seq (temp_13776)) ;;
                             '(temp_13780 : byte_seq) ←
                              (seq_from_seq (temp_13778)) ;;
                            ret (temp_13780))) ;;
                      #put b_i_13758_loc := b_i_13758 ;;
                    
                     '(uniform_bytes_13781 : seq uint8) ←
                        (( '(temp_13783 : seq uint8) ←
                              (seq_concat (uniform_bytes_13781) (b_i_13758)) ;;
                            ret (temp_13783))) ;;
                      #put uniform_bytes_13781_loc := uniform_bytes_13781 ;;
                    
                    @ret ((seq uint8 '× seq uint8)) (prod_ce(
                        b_i_13758,
                        uniform_bytes_13781
                      )) } : code (CEfset (
                        [result_13784_loc ; l_i_b_str_13728_loc ; b_i_13758_loc ; uniform_bytes_13781_loc])) [interface
                    #val #[ HASH ] : hash_inp → hash_out ] _))) ;;
            let '(b_i_13758, uniform_bytes_13781) :=
              (temp_13788) : (seq uint8 '× seq uint8) in
            
             '(result_13784 : (result error_t byte_seq)) ←
                (( temp_13786 ←
                      (seq_truncate (uniform_bytes_13781) (
                          len_in_bytes_13687)) ;;
                    ret (@inl byte_seq error_t (temp_13786)))) ;;
              #put result_13784_loc := result_13784 ;;
            
            @ret (((result error_t byte_seq))) (result_13784) in
            ({ code temp_then } : code (CEfset (
                  [result_13784_loc ; l_i_b_str_13728_loc ; b_i_13758_loc ; uniform_bytes_13781_loc])) [interface
              #val #[ HASH ] : hash_inp → hash_out ] _))
          else @ret (((result error_t byte_seq))) (result_13784)) ;;
      
      @ret ((result error_t byte_seq)) (result_13784) } : code (CEfset (
          [result_13784_loc ; l_i_b_str_13728_loc ; b_i_13758_loc ; uniform_bytes_13781_loc])) [interface
      #val #[ HASH ] : hash_inp → hash_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_expand_message_xmd : package _ _ _ :=
  (seq_link expand_message_xmd link_rest(package_hash)).
Fail Next Obligation.

Definition output_13821_loc : ChoiceEqualityLocation :=
  ((seq ed25519_field_element_t ; 13822%nat)).
Notation "'ed_hash_to_field_inp'" := (
  byte_seq '× byte_seq '× uint_size : choice_type) (in custom pack_type at level 2).
Notation "'ed_hash_to_field_out'" := (
  seq_ed_result_t : choice_type) (in custom pack_type at level 2).
Definition ED_HASH_TO_FIELD : nat :=
  (13823).
Program Definition ed_hash_to_field
   : package (CEfset ([output_13821_loc])) [interface
  #val #[ EXPAND_MESSAGE_XMD ] : expand_message_xmd_inp → expand_message_xmd_out
  ] [interface
  #val #[ ED_HASH_TO_FIELD ] : ed_hash_to_field_inp → ed_hash_to_field_out
  ] :=
  (
    [package #def #[ ED_HASH_TO_FIELD ] (temp_inp : ed_hash_to_field_inp) : ed_hash_to_field_out { 
    let '(
      msg_13797 , dst_13798 , count_13794) := temp_inp : byte_seq '× byte_seq '× uint_size in
    #import {sig #[ EXPAND_MESSAGE_XMD ] : expand_message_xmd_inp → expand_message_xmd_out } as expand_message_xmd ;;
    let expand_message_xmd := fun x_0 x_1 x_2 => expand_message_xmd (
      x_0,x_1,x_2) in
    ({ code  '(len_in_bytes_13799 : uint_size) ←
        ( '(temp_13796 : uint_size) ←
            ((count_13794) .* (l_v)) ;;
          ret (temp_13796)) ;;
      bnd(ChoiceEqualityMonad.result_bind_code error_t , byte_seq , _ , CEfset (
          [output_13821_loc])) uniform_bytes_13807 ⇠
      (({ code  '(temp_13801 : byte_seq_result_t) ←
            (expand_message_xmd (msg_13797) (dst_13798) (len_in_bytes_13799)) ;;
          @ret _ (temp_13801) } : code (CEfset ([])) [interface
          #val #[ EXPAND_MESSAGE_XMD ] : expand_message_xmd_inp → expand_message_xmd_out
          ] _)) in
      ({ code  '(output_13821 : seq ed25519_field_element_t) ←
            ( temp_13803 ←
                (seq_new_ (default : ed25519_field_element_t) (count_13794)) ;;
              ret (temp_13803)) ;;
          #put output_13821_loc := output_13821 ;;
         '(output_13821 : (seq ed25519_field_element_t)) ←
          (foldi' (usize 0) (count_13794) output_13821 (L2 := CEfset (
                  [output_13821_loc])) (I2 := [interface
                #val #[ EXPAND_MESSAGE_XMD ] : expand_message_xmd_inp → expand_message_xmd_out
                ]) (H_loc_incl := _) (H_opsig_incl := _) (fun i_13804 output_13821 =>
              ({ code  '(elm_offset_13808 : uint_size) ←
                  ( '(temp_13806 : uint_size) ←
                      ((l_v) .* (i_13804)) ;;
                    ret (temp_13806)) ;;
                 '(tv_13811 : seq uint8) ←
                  ( '(temp_13810 : seq uint8) ←
                      (seq_slice (uniform_bytes_13807) (elm_offset_13808) (
                          l_v)) ;;
                    ret (temp_13810)) ;;
                 '(u_i_13820 : ed25519_field_element_t) ←
                  ( '(temp_13813 : ed_field_hash_t) ←
                      (nat_mod_from_byte_seq_be (tv_13811)) ;;
                     temp_13815 ←
                      (nat_mod_to_byte_seq_be (temp_13813)) ;;
                     '(temp_13817 : seq uint8) ←
                      (seq_slice (temp_13815) (usize 32) (usize 32)) ;;
                     '(temp_13819 : ed25519_field_element_t) ←
                      (nat_mod_from_byte_seq_be (temp_13817)) ;;
                    ret (temp_13819)) ;;
                 '(output_13821 : seq ed25519_field_element_t) ←
                  (ret (seq_upd output_13821 (i_13804) (u_i_13820))) ;;
                
                @ret ((seq ed25519_field_element_t)) (output_13821) } : code (
                  CEfset ([output_13821_loc])) [interface] _))) ;;
        
        @ret ((result error_t seq ed25519_field_element_t)) (
          @inl seq ed25519_field_element_t error_t (output_13821)) } : code (
          CEfset ([output_13821_loc])) [interface
        #val #[ EXPAND_MESSAGE_XMD ] : expand_message_xmd_inp → expand_message_xmd_out
        ] _) } : code (CEfset ([output_13821_loc])) [interface
      #val #[ EXPAND_MESSAGE_XMD ] : expand_message_xmd_inp → expand_message_xmd_out
      ] _)
    }]).
Fail Next Obligation.
Program Definition package_ed_hash_to_field : package _ _ _ :=
  (seq_link ed_hash_to_field link_rest(package_expand_message_xmd)).
Fail Next Obligation.


Notation "'ed_is_square_inp'" := (
  ed25519_field_element_t : choice_type) (in custom pack_type at level 2).
Notation "'ed_is_square_out'" := (
  bool_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Definition ED_IS_SQUARE : nat :=
  (13843).
Program Definition ed_is_square
   : package (fset.fset0) [interface] [interface
  #val #[ ED_IS_SQUARE ] : ed_is_square_inp → ed_is_square_out ] :=
  (
    [package #def #[ ED_IS_SQUARE ] (temp_inp : ed_is_square_inp) : ed_is_square_out { 
    let '(x_13828) := temp_inp : ed25519_field_element_t in
    ({ code  '(c1_13829 : ed25519_field_element_t) ←
        ( '(temp_13825 : seq int8) ←
            (array_to_be_bytes (p_1_2_v)) ;;
           '(temp_13827 : ed25519_field_element_t) ←
            (nat_mod_from_byte_seq_be (temp_13825)) ;;
          ret (temp_13827)) ;;
       '(tv_13832 : ed25519_field_element_t) ←
        ( temp_13831 ←
            (nat_mod_pow_self (x_13828) (c1_13829)) ;;
          ret (temp_13831)) ;;
       '(temp_13834 : ed25519_field_element_t) ←
        (nat_mod_zero ) ;;
       '(temp_13836 : bool_ChoiceEquality) ←
        ((tv_13832) =.? (temp_13834)) ;;
       '(temp_13838 : ed25519_field_element_t) ←
        (nat_mod_one ) ;;
       '(temp_13840 : bool_ChoiceEquality) ←
        ((tv_13832) =.? (temp_13838)) ;;
       '(temp_13842 : bool_ChoiceEquality) ←
        ((temp_13836) || (temp_13840)) ;;
      @ret (bool_ChoiceEquality) (temp_13842) } : code (
        fset.fset0) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_ed_is_square : package _ _ _ :=
  (ed_is_square).
Fail Next Obligation.


Notation "'sgn0_m_eq_1_inp'" := (
  ed25519_field_element_t : choice_type) (in custom pack_type at level 2).
Notation "'sgn0_m_eq_1_out'" := (
  bool_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Definition SGN0_M_EQ_1 : nat :=
  (13853).
Program Definition sgn0_m_eq_1
   : package (fset.fset0) [interface] [interface
  #val #[ SGN0_M_EQ_1 ] : sgn0_m_eq_1_inp → sgn0_m_eq_1_out ] :=
  (
    [package #def #[ SGN0_M_EQ_1 ] (temp_inp : sgn0_m_eq_1_inp) : sgn0_m_eq_1_out { 
    let '(x_13844) := temp_inp : ed25519_field_element_t in
    ({ code  '(temp_13846 : ed25519_field_element_t) ←
        (nat_mod_two ) ;;
       '(temp_13848 : ed25519_field_element_t) ←
        ((x_13844) rem (temp_13846)) ;;
       '(temp_13850 : ed25519_field_element_t) ←
        (nat_mod_one ) ;;
       '(temp_13852 : bool_ChoiceEquality) ←
        ((temp_13848) =.? (temp_13850)) ;;
      @ret (bool_ChoiceEquality) (temp_13852) } : code (
        fset.fset0) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_sgn0_m_eq_1 : package _ _ _ :=
  (sgn0_m_eq_1).
Fail Next Obligation.


Notation "'ed_clear_cofactor_inp'" := (
  ed_point_t : choice_type) (in custom pack_type at level 2).
Notation "'ed_clear_cofactor_out'" := (
  ed_point_t : choice_type) (in custom pack_type at level 2).
Definition ED_CLEAR_COFACTOR : nat :=
  (13857).
Program Definition ed_clear_cofactor
   : package (fset.fset0) [interface
  #val #[ POINT_MUL_BY_COFACTOR ] : point_mul_by_cofactor_inp → point_mul_by_cofactor_out
  ] [interface
  #val #[ ED_CLEAR_COFACTOR ] : ed_clear_cofactor_inp → ed_clear_cofactor_out
  ] :=
  (
    [package #def #[ ED_CLEAR_COFACTOR ] (temp_inp : ed_clear_cofactor_inp) : ed_clear_cofactor_out { 
    let '(x_13854) := temp_inp : ed_point_t in
    #import {sig #[ POINT_MUL_BY_COFACTOR ] : point_mul_by_cofactor_inp → point_mul_by_cofactor_out } as point_mul_by_cofactor ;;
    let point_mul_by_cofactor := fun x_0 => point_mul_by_cofactor (x_0) in
    ({ code  temp_13856 ←
        (point_mul_by_cofactor (x_13854)) ;;
      @ret ((
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        )) (temp_13856) } : code (fset.fset0) [interface
      #val #[ POINT_MUL_BY_COFACTOR ] : point_mul_by_cofactor_inp → point_mul_by_cofactor_out
      ] _)
    }]).
Fail Next Obligation.
Program Definition package_ed_clear_cofactor : package _ _ _ :=
  (seq_link ed_clear_cofactor link_rest(package_point_mul_by_cofactor)).
Fail Next Obligation.


Notation "'cmov_inp'" := (
  ed25519_field_element_t '× ed25519_field_element_t '× bool_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'cmov_out'" := (
  ed25519_field_element_t : choice_type) (in custom pack_type at level 2).
Definition CMOV : nat :=
  (13861).
Program Definition cmov
   : package (fset.fset0) [interface] [interface
  #val #[ CMOV ] : cmov_inp → cmov_out ] :=
  ([package #def #[ CMOV ] (temp_inp : cmov_inp) : cmov_out { 
    let '(
      a_13860 , b_13859 , c_13858) := temp_inp : ed25519_field_element_t '× ed25519_field_element_t '× bool_ChoiceEquality in
    ({ code @ret (ed25519_field_element_t) ((if (
            c_13858):bool_ChoiceEquality then (*inline*) (b_13859) else (
            a_13860))) } : code (fset.fset0) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_cmov : package _ _ _ :=
  (cmov).
Fail Next Obligation.


Notation "'xor_inp'" := (
  bool_ChoiceEquality '× bool_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'xor_out'" := (
  bool_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Definition XOR : nat :=
  (13864).
Program Definition xor
   : package (fset.fset0) [interface] [interface
  #val #[ XOR ] : xor_inp → xor_out ] :=
  ([package #def #[ XOR ] (temp_inp : xor_inp) : xor_out { 
    let '(
      a_13862 , b_13863) := temp_inp : bool_ChoiceEquality '× bool_ChoiceEquality in
    ({ code @ret (bool_ChoiceEquality) ((if (
            a_13862):bool_ChoiceEquality then (*inline*) ((if (
                b_13863):bool_ChoiceEquality then (*inline*) (
                (false : bool_ChoiceEquality)) else (
                (true : bool_ChoiceEquality)))) else ((if (
                b_13863):bool_ChoiceEquality then (*inline*) (
                (true : bool_ChoiceEquality)) else (
                (false : bool_ChoiceEquality)))))) } : code (
        fset.fset0) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_xor : package _ _ _ :=
  (xor).
Fail Next Obligation.


Notation "'curve25519_to_edwards25519_inp'" := (
  ed_point_t : choice_type) (in custom pack_type at level 2).
Notation "'curve25519_to_edwards25519_out'" := (
  ed_point_t : choice_type) (in custom pack_type at level 2).
Definition CURVE25519_TO_EDWARDS25519 : nat :=
  (13925).
Program Definition curve25519_to_edwards25519
   : package (fset.fset0) [interface #val #[ CMOV ] : cmov_inp → cmov_out ;
  #val #[ POINT_NORMALIZE ] : point_normalize_inp → point_normalize_out ;
  #val #[ SQRT ] : sqrt_inp → sqrt_out ] [interface
  #val #[ CURVE25519_TO_EDWARDS25519 ] : curve25519_to_edwards25519_inp → curve25519_to_edwards25519_out
  ] :=
  (
    [package #def #[ CURVE25519_TO_EDWARDS25519 ] (temp_inp : curve25519_to_edwards25519_inp) : curve25519_to_edwards25519_out { 
    let '(p_13865) := temp_inp : ed_point_t in
    #import {sig #[ CMOV ] : cmov_inp → cmov_out } as cmov ;;
    let cmov := fun x_0 x_1 x_2 => cmov (x_0,x_1,x_2) in
    #import {sig #[ POINT_NORMALIZE ] : point_normalize_inp → point_normalize_out } as point_normalize ;;
    let point_normalize := fun x_0 => point_normalize (x_0) in
    #import {sig #[ SQRT ] : sqrt_inp → sqrt_out } as sqrt ;;
    let sqrt := fun x_0 => sqrt (x_0) in
    ({ code  temp_13924 ←
        ( temp_13867 ←
            (point_normalize (p_13865)) ;;
          ret (temp_13867)) ;;
      let '(s_13872, t_13877, _, _) :=
        (temp_13924) : (
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t
      ) in
       '(one_13873 : ed25519_field_element_t) ←
        ( '(temp_13869 : ed25519_field_element_t) ←
            (nat_mod_one ) ;;
          ret (temp_13869)) ;;
       '(zero_13897 : ed25519_field_element_t) ←
        ( '(temp_13871 : ed25519_field_element_t) ←
            (nat_mod_zero ) ;;
          ret (temp_13871)) ;;
       '(tv1_13876 : ed25519_field_element_t) ←
        ( '(temp_13875 : ed25519_field_element_t) ←
            ((s_13872) +% (one_13873)) ;;
          ret (temp_13875)) ;;
       '(tv2_13880 : ed25519_field_element_t) ←
        ( '(temp_13879 : ed25519_field_element_t) ←
            ((tv1_13876) *% (t_13877)) ;;
          ret (temp_13879)) ;;
       '(tv2_13883 : ed25519_field_element_t) ←
        ( temp_13882 ←
            (nat_mod_inv (tv2_13880)) ;;
          ret (temp_13882)) ;;
       '(v_13886 : ed25519_field_element_t) ←
        ( '(temp_13885 : ed25519_field_element_t) ←
            ((tv2_13883) *% (tv1_13876)) ;;
          ret (temp_13885)) ;;
       '(v_13913 : ed25519_field_element_t) ←
        ( '(temp_13888 : ed25519_field_element_t) ←
            ((v_13886) *% (s_13872)) ;;
          ret (temp_13888)) ;;
       '(w_13893 : ed25519_field_element_t) ←
        ( '(temp_13890 : ed25519_field_element_t) ←
            ((tv2_13883) *% (t_13877)) ;;
          ret (temp_13890)) ;;
       '(tv1_13894 : ed25519_field_element_t) ←
        ( '(temp_13892 : ed25519_field_element_t) ←
            ((s_13872) -% (one_13873)) ;;
          ret (temp_13892)) ;;
       '(w_13900 : ed25519_field_element_t) ←
        ( '(temp_13896 : ed25519_field_element_t) ←
            ((w_13893) *% (tv1_13894)) ;;
          ret (temp_13896)) ;;
       '(e_13901 : bool_ChoiceEquality) ←
        ( '(temp_13899 : bool_ChoiceEquality) ←
            ((tv2_13883) =.? (zero_13897)) ;;
          ret (temp_13899)) ;;
       '(w_13920 : ed25519_field_element_t) ←
        ( '(temp_13903 : ed25519_field_element_t) ←
            (cmov (w_13900) (one_13873) (e_13901)) ;;
          ret (temp_13903)) ;;
       '(c_13910 : ed25519_field_element_t) ←
        ( '(temp_13905 : ed25519_field_element_t) ←
            (nat_mod_zero ) ;;
           '(temp_13907 : ed25519_field_element_t) ←
            (nat_mod_from_literal (_) (@repr U128 486664)) ;;
           '(temp_13909 : ed25519_field_element_t) ←
            ((temp_13905) -% (temp_13907)) ;;
          ret (temp_13909)) ;;
       '(sq_13914 : (option ed25519_field_element_t)) ←
        ( temp_13912 ←
            (sqrt (c_13910)) ;;
          ret (temp_13912)) ;;
       '(v_13919 : ed25519_field_element_t) ←
        ( temp_13916 ←
            (option_unwrap (sq_13914)) ;;
           '(temp_13918 : ed25519_field_element_t) ←
            ((v_13913) *% (temp_13916)) ;;
          ret (temp_13918)) ;;
       '(temp_13922 : ed25519_field_element_t) ←
        ((v_13919) *% (w_13920)) ;;
      @ret ((
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        )) (prod_ce(v_13919, w_13920, one_13873, temp_13922)) } : code (
        fset.fset0) [interface #val #[ CMOV ] : cmov_inp → cmov_out ;
      #val #[ POINT_NORMALIZE ] : point_normalize_inp → point_normalize_out ;
      #val #[ SQRT ] : sqrt_inp → sqrt_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_curve25519_to_edwards25519 : package _ _ _ :=
  (seq_link curve25519_to_edwards25519 link_rest(
      package_cmov,package_point_normalize,package_sqrt)).
Fail Next Obligation.

Definition x1_13951_loc : ChoiceEqualityLocation :=
  ((ed25519_field_element_t ; 14013%nat)).
Definition x_13997_loc : ChoiceEqualityLocation :=
  ((ed25519_field_element_t ; 14014%nat)).
Definition y_13992_loc : ChoiceEqualityLocation :=
  ((ed25519_field_element_t ; 14015%nat)).
Notation "'map_to_curve_elligator2_inp'" := (
  ed25519_field_element_t : choice_type) (in custom pack_type at level 2).
Notation "'map_to_curve_elligator2_out'" := (
  ed_point_t : choice_type) (in custom pack_type at level 2).
Definition MAP_TO_CURVE_ELLIGATOR2 : nat :=
  (14016).
Program Definition map_to_curve_elligator2
   : package (CEfset ([x1_13951_loc ; x_13997_loc ; y_13992_loc])) [interface
  #val #[ ED_IS_SQUARE ] : ed_is_square_inp → ed_is_square_out ;
  #val #[ SGN0_M_EQ_1 ] : sgn0_m_eq_1_inp → sgn0_m_eq_1_out ;
  #val #[ SQRT ] : sqrt_inp → sqrt_out ] [interface
  #val #[ MAP_TO_CURVE_ELLIGATOR2 ] : map_to_curve_elligator2_inp → map_to_curve_elligator2_out
  ] :=
  (
    [package #def #[ MAP_TO_CURVE_ELLIGATOR2 ] (temp_inp : map_to_curve_elligator2_inp) : map_to_curve_elligator2_out { 
    let '(u_13940) := temp_inp : ed25519_field_element_t in
    #import {sig #[ ED_IS_SQUARE ] : ed_is_square_inp → ed_is_square_out } as ed_is_square ;;
    let ed_is_square := fun x_0 => ed_is_square (x_0) in
    #import {sig #[ SGN0_M_EQ_1 ] : sgn0_m_eq_1_inp → sgn0_m_eq_1_out } as sgn0_m_eq_1 ;;
    let sgn0_m_eq_1 := fun x_0 => sgn0_m_eq_1 (x_0) in
    #import {sig #[ SQRT ] : sqrt_inp → sqrt_out } as sqrt ;;
    let sqrt := fun x_0 => sqrt (x_0) in
    ({ code  '(j_13935 : ed25519_field_element_t) ←
        ( '(temp_13927 : ed25519_field_element_t) ←
            (nat_mod_from_literal (_) (j_v)) ;;
          ret (temp_13927)) ;;
       '(z_13939 : ed25519_field_element_t) ←
        ( '(temp_13929 : ed25519_field_element_t) ←
            (nat_mod_from_literal (_) (z_v)) ;;
          ret (temp_13929)) ;;
       '(one_13938 : ed25519_field_element_t) ←
        ( '(temp_13931 : ed25519_field_element_t) ←
            (nat_mod_one ) ;;
          ret (temp_13931)) ;;
       '(zero_13934 : ed25519_field_element_t) ←
        ( '(temp_13933 : ed25519_field_element_t) ←
            (nat_mod_zero ) ;;
          ret (temp_13933)) ;;
       '(x1_13951 : ed25519_field_element_t) ←
          ( '(temp_13937 : ed25519_field_element_t) ←
              ((zero_13934) -% (j_13935)) ;;
             '(temp_13942 : ed25519_field_element_t) ←
              ((z_13939) *% (u_13940)) ;;
             '(temp_13944 : ed25519_field_element_t) ←
              ((temp_13942) *% (u_13940)) ;;
             '(temp_13946 : ed25519_field_element_t) ←
              ((one_13938) +% (temp_13944)) ;;
             temp_13948 ←
              (nat_mod_inv (temp_13946)) ;;
             '(temp_13950 : ed25519_field_element_t) ←
              ((temp_13937) *% (temp_13948)) ;;
            ret (temp_13950)) ;;
        #put x1_13951_loc := x1_13951 ;;
       '(temp_13953 : bool_ChoiceEquality) ←
        ((x1_13951) =.? (zero_13934)) ;;
       '(x1_13951 : (ed25519_field_element_t)) ←
        (if temp_13953:bool_ChoiceEquality
          then (*not state*) (let temp_then :=  '(
                  x1_13951 : ed25519_field_element_t) ←
                (( '(temp_13955 : ed25519_field_element_t) ←
                      ((zero_13934) -% (j_13935)) ;;
                    ret (temp_13955))) ;;
              #put x1_13951_loc := x1_13951 ;;
            
            @ret ((ed25519_field_element_t)) (x1_13951) in
            ({ code temp_then } : code (CEfset ([x1_13951_loc])) [interface] _))
          else @ret ((ed25519_field_element_t)) (x1_13951)) ;;
      
       '(gx1_13985 : ed25519_field_element_t) ←
        ( '(temp_13957 : ed25519_field_element_t) ←
            ((x1_13951) *% (x1_13951)) ;;
           '(temp_13959 : ed25519_field_element_t) ←
            ((temp_13957) *% (x1_13951)) ;;
           '(temp_13961 : ed25519_field_element_t) ←
            ((j_13935) *% (x1_13951)) ;;
           '(temp_13963 : ed25519_field_element_t) ←
            ((temp_13961) *% (x1_13951)) ;;
           '(temp_13965 : ed25519_field_element_t) ←
            ((temp_13959) +% (temp_13963)) ;;
           '(temp_13967 : ed25519_field_element_t) ←
            ((temp_13965) +% (x1_13951)) ;;
          ret (temp_13967)) ;;
       '(x2_13972 : ed25519_field_element_t) ←
        ( '(temp_13969 : ed25519_field_element_t) ←
            ((zero_13934) -% (x1_13951)) ;;
           '(temp_13971 : ed25519_field_element_t) ←
            ((temp_13969) -% (j_13935)) ;;
          ret (temp_13971)) ;;
       '(gx2_13998 : ed25519_field_element_t) ←
        ( '(temp_13974 : ed25519_field_element_t) ←
            ((x2_13972) *% (x2_13972)) ;;
           '(temp_13976 : ed25519_field_element_t) ←
            ((temp_13974) *% (x2_13972)) ;;
           '(temp_13978 : ed25519_field_element_t) ←
            ((x2_13972) *% (x2_13972)) ;;
           '(temp_13980 : ed25519_field_element_t) ←
            ((j_13935) *% (temp_13978)) ;;
           '(temp_13982 : ed25519_field_element_t) ←
            ((temp_13976) +% (temp_13980)) ;;
           '(temp_13984 : ed25519_field_element_t) ←
            ((temp_13982) +% (x2_13972)) ;;
          ret (temp_13984)) ;;
       '(x_13997 : ed25519_field_element_t) ←
          (ret (zero_13934)) ;;
        #put x_13997_loc := x_13997 ;;
       '(y_13992 : ed25519_field_element_t) ←
          (ret (zero_13934)) ;;
        #put y_13992_loc := y_13992 ;;
       '(temp_13987 : bool_ChoiceEquality) ←
        (ed_is_square (gx1_13985)) ;;
       temp_14012 ←
        (if temp_13987:bool_ChoiceEquality
          then (*not state*) (let temp_then :=  '(
                  x_13997 : ed25519_field_element_t) ←
                ((ret (x1_13951))) ;;
              #put x_13997_loc := x_13997 ;;
            
             '(y_13992 : ed25519_field_element_t) ←
                (( temp_13989 ←
                      (sqrt (gx1_13985)) ;;
                     temp_13991 ←
                      (option_unwrap (temp_13989)) ;;
                    ret (temp_13991))) ;;
              #put y_13992_loc := y_13992 ;;
            
             '(temp_13994 : bool_ChoiceEquality) ←
              (sgn0_m_eq_1 (y_13992)) ;;
             '(y_13992 : (ed25519_field_element_t)) ←
              (if negb (temp_13994):bool_ChoiceEquality
                then (*not state*) (let temp_then :=  '(
                        y_13992 : ed25519_field_element_t) ←
                      (( '(temp_13996 : ed25519_field_element_t) ←
                            ((zero_13934) -% (y_13992)) ;;
                          ret (temp_13996))) ;;
                    #put y_13992_loc := y_13992 ;;
                  
                  @ret ((ed25519_field_element_t)) (y_13992) in
                  ({ code temp_then } : code (CEfset (
                        [x1_13951_loc ; x_13997_loc ; y_13992_loc])) [interface] _))
                else @ret ((ed25519_field_element_t)) (y_13992)) ;;
            
            @ret ((ed25519_field_element_t '× ed25519_field_element_t)) (
              prod_ce(x_13997, y_13992)) in
            ({ code temp_then } : code (CEfset (
                  [x1_13951_loc ; x_13997_loc ; y_13992_loc])) [interface
              #val #[ SGN0_M_EQ_1 ] : sgn0_m_eq_1_inp → sgn0_m_eq_1_out ;
              #val #[ SQRT ] : sqrt_inp → sqrt_out ] _))
          else  (({ code  '(x_13997 : ed25519_field_element_t) ←
                  ((ret (x2_13972))) ;;
                #put x_13997_loc := x_13997 ;;
              
               '(y_13992 : ed25519_field_element_t) ←
                  (( temp_14000 ←
                        (sqrt (gx2_13998)) ;;
                       temp_14002 ←
                        (option_unwrap (temp_14000)) ;;
                      ret (temp_14002))) ;;
                #put y_13992_loc := y_13992 ;;
              
               '(temp_14004 : bool_ChoiceEquality) ←
                (sgn0_m_eq_1 (y_13992)) ;;
               '(y_13992 : (ed25519_field_element_t)) ←
                (if temp_14004:bool_ChoiceEquality
                  then (*not state*) (let temp_then :=  '(
                          y_13992 : ed25519_field_element_t) ←
                        (( '(temp_14006 : ed25519_field_element_t) ←
                              ((zero_13934) -% (y_13992)) ;;
                            ret (temp_14006))) ;;
                      #put y_13992_loc := y_13992 ;;
                    
                    @ret ((ed25519_field_element_t)) (y_13992) in
                    ({ code temp_then } : code (CEfset (
                          [x1_13951_loc ; x_13997_loc ; y_13992_loc])) [interface] _))
                  else @ret ((ed25519_field_element_t)) (y_13992)) ;;
              
              @ret ((ed25519_field_element_t '× ed25519_field_element_t)) (
                prod_ce(x_13997, y_13992)) } : code (CEfset (
                  [x1_13951_loc ; x_13997_loc ; y_13992_loc])) [interface
              #val #[ SGN0_M_EQ_1 ] : sgn0_m_eq_1_inp → sgn0_m_eq_1_out ;
              #val #[ SQRT ] : sqrt_inp → sqrt_out ] _))) ;;
      let '(x_13997, y_13992) :=
        (temp_14012) : (ed25519_field_element_t '× ed25519_field_element_t) in
      
       '(s_14007 : ed25519_field_element_t) ←
        (ret (x_13997)) ;;
       '(t_14008 : ed25519_field_element_t) ←
        (ret (y_13992)) ;;
       '(temp_14010 : ed25519_field_element_t) ←
        ((s_14007) *% (t_14008)) ;;
      @ret ((
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        )) (prod_ce(s_14007, t_14008, one_13938, temp_14010)) } : code (CEfset (
          [x1_13951_loc ; x_13997_loc ; y_13992_loc])) [interface
      #val #[ ED_IS_SQUARE ] : ed_is_square_inp → ed_is_square_out ;
      #val #[ SGN0_M_EQ_1 ] : sgn0_m_eq_1_inp → sgn0_m_eq_1_out ;
      #val #[ SQRT ] : sqrt_inp → sqrt_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_map_to_curve_elligator2 : package _ _ _ :=
  (seq_link map_to_curve_elligator2 link_rest(
      package_ed_is_square,package_sgn0_m_eq_1,package_sqrt)).
Fail Next Obligation.


Notation "'map_to_curve_elligator2_straight_inp'" := (
  ed25519_field_element_t : choice_type) (in custom pack_type at level 2).
Notation "'map_to_curve_elligator2_straight_out'" := (
  ed_point_t : choice_type) (in custom pack_type at level 2).
Definition MAP_TO_CURVE_ELLIGATOR2_STRAIGHT : nat :=
  (14103).
Program Definition map_to_curve_elligator2_straight
   : package (fset.fset0) [interface #val #[ CMOV ] : cmov_inp → cmov_out ;
  #val #[ ED_IS_SQUARE ] : ed_is_square_inp → ed_is_square_out ;
  #val #[ SGN0_M_EQ_1 ] : sgn0_m_eq_1_inp → sgn0_m_eq_1_out ;
  #val #[ SQRT ] : sqrt_inp → sqrt_out ; #val #[ XOR ] : xor_inp → xor_out
  ] [interface
  #val #[ MAP_TO_CURVE_ELLIGATOR2_STRAIGHT ] : map_to_curve_elligator2_straight_inp → map_to_curve_elligator2_straight_out
  ] :=
  (
    [package #def #[ MAP_TO_CURVE_ELLIGATOR2_STRAIGHT ] (temp_inp : map_to_curve_elligator2_straight_inp) : map_to_curve_elligator2_straight_out { 
    let '(u_14025) := temp_inp : ed25519_field_element_t in
    #import {sig #[ CMOV ] : cmov_inp → cmov_out } as cmov ;;
    let cmov := fun x_0 x_1 x_2 => cmov (x_0,x_1,x_2) in
    #import {sig #[ ED_IS_SQUARE ] : ed_is_square_inp → ed_is_square_out } as ed_is_square ;;
    let ed_is_square := fun x_0 => ed_is_square (x_0) in
    #import {sig #[ SGN0_M_EQ_1 ] : sgn0_m_eq_1_inp → sgn0_m_eq_1_out } as sgn0_m_eq_1 ;;
    let sgn0_m_eq_1 := fun x_0 => sgn0_m_eq_1 (x_0) in
    #import {sig #[ SQRT ] : sqrt_inp → sqrt_out } as sqrt ;;
    let sqrt := fun x_0 => sqrt (x_0) in
    #import {sig #[ XOR ] : xor_inp → xor_out } as xor ;;
    let xor := fun x_0 x_1 => xor (x_0,x_1) in
    ({ code  '(j_14048 : ed25519_field_element_t) ←
        ( '(temp_14018 : ed25519_field_element_t) ←
            (nat_mod_from_literal (_) (j_v)) ;;
          ret (temp_14018)) ;;
       '(z_14028 : ed25519_field_element_t) ←
        ( '(temp_14020 : ed25519_field_element_t) ←
            (nat_mod_from_literal (_) (z_v)) ;;
          ret (temp_14020)) ;;
       '(one_14034 : ed25519_field_element_t) ←
        ( '(temp_14022 : ed25519_field_element_t) ←
            (nat_mod_one ) ;;
          ret (temp_14022)) ;;
       '(zero_14033 : ed25519_field_element_t) ←
        ( '(temp_14024 : ed25519_field_element_t) ←
            (nat_mod_zero ) ;;
          ret (temp_14024)) ;;
       '(tv1_14029 : ed25519_field_element_t) ←
        ( '(temp_14027 : ed25519_field_element_t) ←
            ((u_14025) *% (u_14025)) ;;
          ret (temp_14027)) ;;
       '(tv1_14032 : ed25519_field_element_t) ←
        ( '(temp_14031 : ed25519_field_element_t) ←
            ((z_14028) *% (tv1_14029)) ;;
          ret (temp_14031)) ;;
       '(e1_14039 : bool_ChoiceEquality) ←
        ( '(temp_14036 : ed25519_field_element_t) ←
            ((zero_14033) -% (one_14034)) ;;
           '(temp_14038 : bool_ChoiceEquality) ←
            ((tv1_14032) =.? (temp_14036)) ;;
          ret (temp_14038)) ;;
       '(tv1_14042 : ed25519_field_element_t) ←
        ( '(temp_14041 : ed25519_field_element_t) ←
            (cmov (tv1_14032) (zero_14033) (e1_14039)) ;;
          ret (temp_14041)) ;;
       '(x1_14045 : ed25519_field_element_t) ←
        ( '(temp_14044 : ed25519_field_element_t) ←
            ((tv1_14042) +% (one_14034)) ;;
          ret (temp_14044)) ;;
       '(x1_14051 : ed25519_field_element_t) ←
        ( temp_14047 ←
            (nat_mod_inv (x1_14045)) ;;
          ret (temp_14047)) ;;
       '(x1_14054 : ed25519_field_element_t) ←
        ( '(temp_14050 : ed25519_field_element_t) ←
            ((zero_14033) -% (j_14048)) ;;
           '(temp_14053 : ed25519_field_element_t) ←
            ((temp_14050) *% (x1_14051)) ;;
          ret (temp_14053)) ;;
       '(gx1_14057 : ed25519_field_element_t) ←
        ( '(temp_14056 : ed25519_field_element_t) ←
            ((x1_14054) +% (j_14048)) ;;
          ret (temp_14056)) ;;
       '(gx1_14060 : ed25519_field_element_t) ←
        ( '(temp_14059 : ed25519_field_element_t) ←
            ((gx1_14057) *% (x1_14054)) ;;
          ret (temp_14059)) ;;
       '(gx1_14063 : ed25519_field_element_t) ←
        ( '(temp_14062 : ed25519_field_element_t) ←
            ((gx1_14060) +% (one_14034)) ;;
          ret (temp_14062)) ;;
       '(gx1_14070 : ed25519_field_element_t) ←
        ( '(temp_14065 : ed25519_field_element_t) ←
            ((gx1_14063) *% (x1_14054)) ;;
          ret (temp_14065)) ;;
       '(x2_14075 : ed25519_field_element_t) ←
        ( '(temp_14067 : ed25519_field_element_t) ←
            ((zero_14033) -% (x1_14054)) ;;
           '(temp_14069 : ed25519_field_element_t) ←
            ((temp_14067) -% (j_14048)) ;;
          ret (temp_14069)) ;;
       '(gx2_14079 : ed25519_field_element_t) ←
        ( '(temp_14072 : ed25519_field_element_t) ←
            ((tv1_14042) *% (gx1_14070)) ;;
          ret (temp_14072)) ;;
       '(e2_14076 : bool_ChoiceEquality) ←
        ( '(temp_14074 : bool_ChoiceEquality) ←
            (ed_is_square (gx1_14070)) ;;
          ret (temp_14074)) ;;
       '(x_14097 : ed25519_field_element_t) ←
        ( '(temp_14078 : ed25519_field_element_t) ←
            (cmov (x2_14075) (x1_14054) (e2_14076)) ;;
          ret (temp_14078)) ;;
       '(y2_14082 : ed25519_field_element_t) ←
        ( '(temp_14081 : ed25519_field_element_t) ←
            (cmov (gx2_14079) (gx1_14070) (e2_14076)) ;;
          ret (temp_14081)) ;;
       '(y_14087 : ed25519_field_element_t) ←
        ( temp_14084 ←
            (sqrt (y2_14082)) ;;
           temp_14086 ←
            (option_unwrap (temp_14084)) ;;
          ret (temp_14086)) ;;
       '(e3_14092 : bool_ChoiceEquality) ←
        ( '(temp_14089 : bool_ChoiceEquality) ←
            (sgn0_m_eq_1 (y_14087)) ;;
          ret (temp_14089)) ;;
       '(y_14098 : ed25519_field_element_t) ←
        ( '(temp_14091 : ed25519_field_element_t) ←
            ((zero_14033) -% (y_14087)) ;;
           '(temp_14094 : bool_ChoiceEquality) ←
            (xor (e2_14076) (e3_14092)) ;;
           '(temp_14096 : ed25519_field_element_t) ←
            (cmov (y_14087) (temp_14091) (temp_14094)) ;;
          ret (temp_14096)) ;;
       '(s_14099 : ed25519_field_element_t) ←
        (ret (x_14097)) ;;
       '(t_14100 : ed25519_field_element_t) ←
        (ret (y_14098)) ;;
       '(temp_14102 : ed25519_field_element_t) ←
        ((s_14099) *% (t_14100)) ;;
      @ret ((
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        )) (prod_ce(s_14099, t_14100, one_14034, temp_14102)) } : code (
        fset.fset0) [interface #val #[ CMOV ] : cmov_inp → cmov_out ;
      #val #[ ED_IS_SQUARE ] : ed_is_square_inp → ed_is_square_out ;
      #val #[ SGN0_M_EQ_1 ] : sgn0_m_eq_1_inp → sgn0_m_eq_1_out ;
      #val #[ SQRT ] : sqrt_inp → sqrt_out ;
      #val #[ XOR ] : xor_inp → xor_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_map_to_curve_elligator2_straight : package _ _ _ :=
  (seq_link map_to_curve_elligator2_straight link_rest(
      package_cmov,package_ed_is_square,package_sgn0_m_eq_1,package_sqrt,package_xor)).
Fail Next Obligation.


Notation "'map_to_curve_elligator2_curve25519_inp'" := (
  ed25519_field_element_t : choice_type) (in custom pack_type at level 2).
Notation "'map_to_curve_elligator2_curve25519_out'" := (
  ed_point_t : choice_type) (in custom pack_type at level 2).
Definition MAP_TO_CURVE_ELLIGATOR2_CURVE25519 : nat :=
  (14255).
Program Definition map_to_curve_elligator2_curve25519
   : package (fset.fset0) [interface #val #[ CMOV ] : cmov_inp → cmov_out ;
  #val #[ SGN0_M_EQ_1 ] : sgn0_m_eq_1_inp → sgn0_m_eq_1_out ;
  #val #[ SQRT ] : sqrt_inp → sqrt_out ; #val #[ XOR ] : xor_inp → xor_out
  ] [interface
  #val #[ MAP_TO_CURVE_ELLIGATOR2_CURVE25519 ] : map_to_curve_elligator2_curve25519_inp → map_to_curve_elligator2_curve25519_out
  ] :=
  (
    [package #def #[ MAP_TO_CURVE_ELLIGATOR2_CURVE25519 ] (temp_inp : map_to_curve_elligator2_curve25519_inp) : map_to_curve_elligator2_curve25519_out { 
    let '(u_14132) := temp_inp : ed25519_field_element_t in
    #import {sig #[ CMOV ] : cmov_inp → cmov_out } as cmov ;;
    let cmov := fun x_0 x_1 x_2 => cmov (x_0,x_1,x_2) in
    #import {sig #[ SGN0_M_EQ_1 ] : sgn0_m_eq_1_inp → sgn0_m_eq_1_out } as sgn0_m_eq_1 ;;
    let sgn0_m_eq_1 := fun x_0 => sgn0_m_eq_1 (x_0) in
    #import {sig #[ SQRT ] : sqrt_inp → sqrt_out } as sqrt ;;
    let sqrt := fun x_0 => sqrt (x_0) in
    #import {sig #[ XOR ] : xor_inp → xor_out } as xor ;;
    let xor := fun x_0 x_1 => xor (x_0,x_1) in
    ({ code  '(j_14141 : ed25519_field_element_t) ←
        ( '(temp_14105 : ed25519_field_element_t) ←
            (nat_mod_from_literal (_) (j_v)) ;;
          ret (temp_14105)) ;;
       '(zero_14120 : ed25519_field_element_t) ←
        ( '(temp_14107 : ed25519_field_element_t) ←
            (nat_mod_zero ) ;;
          ret (temp_14107)) ;;
       '(one_14121 : ed25519_field_element_t) ←
        ( '(temp_14109 : ed25519_field_element_t) ←
            (nat_mod_one ) ;;
          ret (temp_14109)) ;;
       '(two_14116 : ed25519_field_element_t) ←
        ( '(temp_14111 : ed25519_field_element_t) ←
            (nat_mod_two ) ;;
          ret (temp_14111)) ;;
       '(c1_14117 : ed25519_field_element_t) ←
        ( '(temp_14113 : seq int8) ←
            (array_to_be_bytes (p_3_8_v)) ;;
           '(temp_14115 : ed25519_field_element_t) ←
            (nat_mod_from_byte_seq_be (temp_14113)) ;;
          ret (temp_14115)) ;;
       '(c2_14206 : ed25519_field_element_t) ←
        ( temp_14119 ←
            (nat_mod_pow_self (two_14116) (c1_14117)) ;;
          ret (temp_14119)) ;;
       '(c3_14186 : ed25519_field_element_t) ←
        ( '(temp_14123 : ed25519_field_element_t) ←
            ((zero_14120) -% (one_14121)) ;;
           temp_14125 ←
            (sqrt (temp_14123)) ;;
           temp_14127 ←
            (option_unwrap (temp_14125)) ;;
          ret (temp_14127)) ;;
       '(c4_14179 : ed25519_field_element_t) ←
        ( '(temp_14129 : seq int8) ←
            (array_to_be_bytes (p_5_8_v)) ;;
           '(temp_14131 : ed25519_field_element_t) ←
            (nat_mod_from_byte_seq_be (temp_14129)) ;;
          ret (temp_14131)) ;;
       '(tv1_14135 : ed25519_field_element_t) ←
        ( '(temp_14134 : ed25519_field_element_t) ←
            ((u_14132) *% (u_14132)) ;;
          ret (temp_14134)) ;;
       '(tv1_14138 : ed25519_field_element_t) ←
        ( '(temp_14137 : ed25519_field_element_t) ←
            ((two_14116) *% (tv1_14135)) ;;
          ret (temp_14137)) ;;
       '(xd_14144 : ed25519_field_element_t) ←
        ( '(temp_14140 : ed25519_field_element_t) ←
            ((tv1_14138) +% (one_14121)) ;;
          ret (temp_14140)) ;;
       '(x1n_14153 : ed25519_field_element_t) ←
        ( '(temp_14143 : ed25519_field_element_t) ←
            ((zero_14120) -% (j_14141)) ;;
          ret (temp_14143)) ;;
       '(tv2_14147 : ed25519_field_element_t) ←
        ( '(temp_14146 : ed25519_field_element_t) ←
            ((xd_14144) *% (xd_14144)) ;;
          ret (temp_14146)) ;;
       '(gxd_14162 : ed25519_field_element_t) ←
        ( '(temp_14149 : ed25519_field_element_t) ←
            ((tv2_14147) *% (xd_14144)) ;;
          ret (temp_14149)) ;;
       '(gx1_14152 : ed25519_field_element_t) ←
        ( '(temp_14151 : ed25519_field_element_t) ←
            ((j_14141) *% (tv1_14138)) ;;
          ret (temp_14151)) ;;
       '(gx1_14156 : ed25519_field_element_t) ←
        ( '(temp_14155 : ed25519_field_element_t) ←
            ((gx1_14152) *% (x1n_14153)) ;;
          ret (temp_14155)) ;;
       '(gx1_14159 : ed25519_field_element_t) ←
        ( '(temp_14158 : ed25519_field_element_t) ←
            ((gx1_14156) +% (tv2_14147)) ;;
          ret (temp_14158)) ;;
       '(gx1_14171 : ed25519_field_element_t) ←
        ( '(temp_14161 : ed25519_field_element_t) ←
            ((gx1_14159) *% (x1n_14153)) ;;
          ret (temp_14161)) ;;
       '(tv3_14165 : ed25519_field_element_t) ←
        ( '(temp_14164 : ed25519_field_element_t) ←
            ((gxd_14162) *% (gxd_14162)) ;;
          ret (temp_14164)) ;;
       '(tv2_14174 : ed25519_field_element_t) ←
        ( '(temp_14167 : ed25519_field_element_t) ←
            ((tv3_14165) *% (tv3_14165)) ;;
          ret (temp_14167)) ;;
       '(tv3_14170 : ed25519_field_element_t) ←
        ( '(temp_14169 : ed25519_field_element_t) ←
            ((tv3_14165) *% (gxd_14162)) ;;
          ret (temp_14169)) ;;
       '(tv3_14175 : ed25519_field_element_t) ←
        ( '(temp_14173 : ed25519_field_element_t) ←
            ((tv3_14170) *% (gx1_14171)) ;;
          ret (temp_14173)) ;;
       '(tv2_14178 : ed25519_field_element_t) ←
        ( '(temp_14177 : ed25519_field_element_t) ←
            ((tv2_14174) *% (tv3_14175)) ;;
          ret (temp_14177)) ;;
       '(y11_14182 : ed25519_field_element_t) ←
        ( temp_14181 ←
            (nat_mod_pow_self (tv2_14178) (c4_14179)) ;;
          ret (temp_14181)) ;;
       '(y11_14185 : ed25519_field_element_t) ←
        ( '(temp_14184 : ed25519_field_element_t) ←
            ((y11_14182) *% (tv3_14175)) ;;
          ret (temp_14184)) ;;
       '(y12_14197 : ed25519_field_element_t) ←
        ( '(temp_14188 : ed25519_field_element_t) ←
            ((y11_14185) *% (c3_14186)) ;;
          ret (temp_14188)) ;;
       '(tv2_14191 : ed25519_field_element_t) ←
        ( '(temp_14190 : ed25519_field_element_t) ←
            ((y11_14185) *% (y11_14185)) ;;
          ret (temp_14190)) ;;
       '(tv2_14194 : ed25519_field_element_t) ←
        ( '(temp_14193 : ed25519_field_element_t) ←
            ((tv2_14191) *% (gxd_14162)) ;;
          ret (temp_14193)) ;;
       '(e1_14198 : bool_ChoiceEquality) ←
        ( '(temp_14196 : bool_ChoiceEquality) ←
            ((tv2_14194) =.? (gx1_14171)) ;;
          ret (temp_14196)) ;;
       '(y1_14227 : ed25519_field_element_t) ←
        ( '(temp_14200 : ed25519_field_element_t) ←
            (cmov (y12_14197) (y11_14185) (e1_14198)) ;;
          ret (temp_14200)) ;;
       '(x2n_14236 : ed25519_field_element_t) ←
        ( '(temp_14202 : ed25519_field_element_t) ←
            ((x1n_14153) *% (tv1_14138)) ;;
          ret (temp_14202)) ;;
       '(y21_14205 : ed25519_field_element_t) ←
        ( '(temp_14204 : ed25519_field_element_t) ←
            ((y11_14185) *% (u_14132)) ;;
          ret (temp_14204)) ;;
       '(y21_14209 : ed25519_field_element_t) ←
        ( '(temp_14208 : ed25519_field_element_t) ←
            ((y21_14205) *% (c2_14206)) ;;
          ret (temp_14208)) ;;
       '(y22_14223 : ed25519_field_element_t) ←
        ( '(temp_14211 : ed25519_field_element_t) ←
            ((y21_14209) *% (c3_14186)) ;;
          ret (temp_14211)) ;;
       '(gx2_14220 : ed25519_field_element_t) ←
        ( '(temp_14213 : ed25519_field_element_t) ←
            ((gx1_14171) *% (tv1_14138)) ;;
          ret (temp_14213)) ;;
       '(tv2_14216 : ed25519_field_element_t) ←
        ( '(temp_14215 : ed25519_field_element_t) ←
            ((y21_14209) *% (y21_14209)) ;;
          ret (temp_14215)) ;;
       '(tv2_14219 : ed25519_field_element_t) ←
        ( '(temp_14218 : ed25519_field_element_t) ←
            ((tv2_14216) *% (gxd_14162)) ;;
          ret (temp_14218)) ;;
       '(e2_14224 : bool_ChoiceEquality) ←
        ( '(temp_14222 : bool_ChoiceEquality) ←
            ((tv2_14219) =.? (gx2_14220)) ;;
          ret (temp_14222)) ;;
       '(y2_14240 : ed25519_field_element_t) ←
        ( '(temp_14226 : ed25519_field_element_t) ←
            (cmov (y22_14223) (y21_14209) (e2_14224)) ;;
          ret (temp_14226)) ;;
       '(tv2_14230 : ed25519_field_element_t) ←
        ( '(temp_14229 : ed25519_field_element_t) ←
            ((y1_14227) *% (y1_14227)) ;;
          ret (temp_14229)) ;;
       '(tv2_14233 : ed25519_field_element_t) ←
        ( '(temp_14232 : ed25519_field_element_t) ←
            ((tv2_14230) *% (gxd_14162)) ;;
          ret (temp_14232)) ;;
       '(e3_14237 : bool_ChoiceEquality) ←
        ( '(temp_14235 : bool_ChoiceEquality) ←
            ((tv2_14233) =.? (gx1_14171)) ;;
          ret (temp_14235)) ;;
       '(xn_14253 : ed25519_field_element_t) ←
        ( '(temp_14239 : ed25519_field_element_t) ←
            (cmov (x2n_14236) (x1n_14153) (e3_14237)) ;;
          ret (temp_14239)) ;;
       '(y_14243 : ed25519_field_element_t) ←
        ( '(temp_14242 : ed25519_field_element_t) ←
            (cmov (y2_14240) (y1_14227) (e3_14237)) ;;
          ret (temp_14242)) ;;
       '(e4_14248 : bool_ChoiceEquality) ←
        ( '(temp_14245 : bool_ChoiceEquality) ←
            (sgn0_m_eq_1 (y_14243)) ;;
          ret (temp_14245)) ;;
       '(y_14254 : ed25519_field_element_t) ←
        ( '(temp_14247 : ed25519_field_element_t) ←
            ((zero_14120) -% (y_14243)) ;;
           '(temp_14250 : bool_ChoiceEquality) ←
            (xor (e3_14237) (e4_14248)) ;;
           '(temp_14252 : ed25519_field_element_t) ←
            (cmov (y_14243) (temp_14247) (temp_14250)) ;;
          ret (temp_14252)) ;;
      @ret ((
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        )) (prod_ce(xn_14253, xd_14144, y_14254, one_14121)) } : code (
        fset.fset0) [interface #val #[ CMOV ] : cmov_inp → cmov_out ;
      #val #[ SGN0_M_EQ_1 ] : sgn0_m_eq_1_inp → sgn0_m_eq_1_out ;
      #val #[ SQRT ] : sqrt_inp → sqrt_out ;
      #val #[ XOR ] : xor_inp → xor_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_map_to_curve_elligator2_curve25519 : package _ _ _ :=
  (seq_link map_to_curve_elligator2_curve25519 link_rest(
      package_cmov,package_sgn0_m_eq_1,package_sqrt,package_xor)).
Fail Next Obligation.


Notation "'map_to_curve_elligator2_edwards25519_inp'" := (
  ed25519_field_element_t : choice_type) (in custom pack_type at level 2).
Notation "'map_to_curve_elligator2_edwards25519_out'" := (
  ed_point_t : choice_type) (in custom pack_type at level 2).
Definition MAP_TO_CURVE_ELLIGATOR2_EDWARDS25519 : nat :=
  (14331).
Program Definition map_to_curve_elligator2_edwards25519
   : package (fset.fset0) [interface #val #[ CMOV ] : cmov_inp → cmov_out ;
  #val #[ MAP_TO_CURVE_ELLIGATOR2_CURVE25519 ] : map_to_curve_elligator2_curve25519_inp → map_to_curve_elligator2_curve25519_out ;
  #val #[ SQRT ] : sqrt_inp → sqrt_out ] [interface
  #val #[ MAP_TO_CURVE_ELLIGATOR2_EDWARDS25519 ] : map_to_curve_elligator2_edwards25519_inp → map_to_curve_elligator2_edwards25519_out
  ] :=
  (
    [package #def #[ MAP_TO_CURVE_ELLIGATOR2_EDWARDS25519 ] (temp_inp : map_to_curve_elligator2_edwards25519_inp) : map_to_curve_elligator2_edwards25519_out { 
    let '(u_14275) := temp_inp : ed25519_field_element_t in
    #import {sig #[ CMOV ] : cmov_inp → cmov_out } as cmov ;;
    let cmov := fun x_0 x_1 x_2 => cmov (x_0,x_1,x_2) in
    #import {sig #[ MAP_TO_CURVE_ELLIGATOR2_CURVE25519 ] : map_to_curve_elligator2_curve25519_inp → map_to_curve_elligator2_curve25519_out } as map_to_curve_elligator2_curve25519 ;;
    let map_to_curve_elligator2_curve25519 := fun x_0 => map_to_curve_elligator2_curve25519 (
      x_0) in
    #import {sig #[ SQRT ] : sqrt_inp → sqrt_out } as sqrt ;;
    let sqrt := fun x_0 => sqrt (x_0) in
    ({ code  '(j_14265 : ed25519_field_element_t) ←
        ( '(temp_14257 : ed25519_field_element_t) ←
            (nat_mod_from_literal (_) (j_v)) ;;
          ret (temp_14257)) ;;
       '(zero_14264 : ed25519_field_element_t) ←
        ( '(temp_14259 : ed25519_field_element_t) ←
            (nat_mod_zero ) ;;
          ret (temp_14259)) ;;
       '(one_14305 : ed25519_field_element_t) ←
        ( '(temp_14261 : ed25519_field_element_t) ←
            (nat_mod_one ) ;;
          ret (temp_14261)) ;;
       '(two_14266 : ed25519_field_element_t) ←
        ( '(temp_14263 : ed25519_field_element_t) ←
            (nat_mod_two ) ;;
          ret (temp_14263)) ;;
       '(c1_14283 : ed25519_field_element_t) ←
        ( '(temp_14268 : ed25519_field_element_t) ←
            ((j_14265) +% (two_14266)) ;;
           '(temp_14270 : ed25519_field_element_t) ←
            ((zero_14264) -% (temp_14268)) ;;
           temp_14272 ←
            (sqrt (temp_14270)) ;;
           temp_14274 ←
            (option_unwrap (temp_14272)) ;;
          ret (temp_14274)) ;;
       temp_14330 ←
        ( '(temp_14277 : ed_point_t) ←
            (map_to_curve_elligator2_curve25519 (u_14275)) ;;
          ret (temp_14277)) ;;
      let '(xmn_14278, xmd_14286, ymn_14287, ymd_14279) :=
        (temp_14330) : (
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t
      ) in
       '(xn_14282 : ed25519_field_element_t) ←
        ( '(temp_14281 : ed25519_field_element_t) ←
            ((xmn_14278) *% (ymd_14279)) ;;
          ret (temp_14281)) ;;
       '(xn_14301 : ed25519_field_element_t) ←
        ( '(temp_14285 : ed25519_field_element_t) ←
            ((xn_14282) *% (c1_14283)) ;;
          ret (temp_14285)) ;;
       '(xd_14294 : ed25519_field_element_t) ←
        ( '(temp_14289 : ed25519_field_element_t) ←
            ((xmd_14286) *% (ymn_14287)) ;;
          ret (temp_14289)) ;;
       '(yn_14308 : ed25519_field_element_t) ←
        ( '(temp_14291 : ed25519_field_element_t) ←
            ((xmn_14278) -% (xmd_14286)) ;;
          ret (temp_14291)) ;;
       '(yd_14295 : ed25519_field_element_t) ←
        ( '(temp_14293 : ed25519_field_element_t) ←
            ((xmn_14278) +% (xmd_14286)) ;;
          ret (temp_14293)) ;;
       '(tv1_14298 : ed25519_field_element_t) ←
        ( '(temp_14297 : ed25519_field_element_t) ←
            ((xd_14294) *% (yd_14295)) ;;
          ret (temp_14297)) ;;
       '(e_14302 : bool_ChoiceEquality) ←
        ( '(temp_14300 : bool_ChoiceEquality) ←
            ((tv1_14298) =.? (zero_14264)) ;;
          ret (temp_14300)) ;;
       '(xn_14313 : ed25519_field_element_t) ←
        ( '(temp_14304 : ed25519_field_element_t) ←
            (cmov (xn_14301) (zero_14264) (e_14302)) ;;
          ret (temp_14304)) ;;
       '(xd_14314 : ed25519_field_element_t) ←
        ( '(temp_14307 : ed25519_field_element_t) ←
            (cmov (xd_14294) (one_14305) (e_14302)) ;;
          ret (temp_14307)) ;;
       '(yn_14319 : ed25519_field_element_t) ←
        ( '(temp_14310 : ed25519_field_element_t) ←
            (cmov (yn_14308) (one_14305) (e_14302)) ;;
          ret (temp_14310)) ;;
       '(yd_14320 : ed25519_field_element_t) ←
        ( '(temp_14312 : ed25519_field_element_t) ←
            (cmov (yd_14295) (one_14305) (e_14302)) ;;
          ret (temp_14312)) ;;
       '(x_14325 : ed25519_field_element_t) ←
        ( temp_14316 ←
            (nat_mod_inv (xd_14314)) ;;
           '(temp_14318 : ed25519_field_element_t) ←
            ((xn_14313) *% (temp_14316)) ;;
          ret (temp_14318)) ;;
       '(y_14326 : ed25519_field_element_t) ←
        ( temp_14322 ←
            (nat_mod_inv (yd_14320)) ;;
           '(temp_14324 : ed25519_field_element_t) ←
            ((yn_14319) *% (temp_14322)) ;;
          ret (temp_14324)) ;;
       '(temp_14328 : ed25519_field_element_t) ←
        ((x_14325) *% (y_14326)) ;;
      @ret ((
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        )) (prod_ce(x_14325, y_14326, one_14305, temp_14328)) } : code (
        fset.fset0) [interface #val #[ CMOV ] : cmov_inp → cmov_out ;
      #val #[ MAP_TO_CURVE_ELLIGATOR2_CURVE25519 ] : map_to_curve_elligator2_curve25519_inp → map_to_curve_elligator2_curve25519_out ;
      #val #[ SQRT ] : sqrt_inp → sqrt_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_map_to_curve_elligator2_edwards25519 : package _ _ _ :=
  (seq_link map_to_curve_elligator2_edwards25519 link_rest(
      package_cmov,package_map_to_curve_elligator2_curve25519,package_sqrt)).
Fail Next Obligation.


Notation "'map_to_curve_elligator2_edwards_inp'" := (
  ed25519_field_element_t : choice_type) (in custom pack_type at level 2).
Notation "'map_to_curve_elligator2_edwards_out'" := (
  ed_point_t : choice_type) (in custom pack_type at level 2).
Definition MAP_TO_CURVE_ELLIGATOR2_EDWARDS : nat :=
  (14338).
Program Definition map_to_curve_elligator2_edwards
   : package (CEfset ([])) [interface
  #val #[ CURVE25519_TO_EDWARDS25519 ] : curve25519_to_edwards25519_inp → curve25519_to_edwards25519_out ;
  #val #[ MAP_TO_CURVE_ELLIGATOR2 ] : map_to_curve_elligator2_inp → map_to_curve_elligator2_out
  ] [interface
  #val #[ MAP_TO_CURVE_ELLIGATOR2_EDWARDS ] : map_to_curve_elligator2_edwards_inp → map_to_curve_elligator2_edwards_out
  ] :=
  (
    [package #def #[ MAP_TO_CURVE_ELLIGATOR2_EDWARDS ] (temp_inp : map_to_curve_elligator2_edwards_inp) : map_to_curve_elligator2_edwards_out { 
    let '(u_14332) := temp_inp : ed25519_field_element_t in
    #import {sig #[ CURVE25519_TO_EDWARDS25519 ] : curve25519_to_edwards25519_inp → curve25519_to_edwards25519_out } as curve25519_to_edwards25519 ;;
    let curve25519_to_edwards25519 := fun x_0 => curve25519_to_edwards25519 (
      x_0) in
    #import {sig #[ MAP_TO_CURVE_ELLIGATOR2 ] : map_to_curve_elligator2_inp → map_to_curve_elligator2_out } as map_to_curve_elligator2 ;;
    let map_to_curve_elligator2 := fun x_0 => map_to_curve_elligator2 (x_0) in
    ({ code  '(st_14335 : (
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t
          )) ←
        ( '(temp_14334 : ed_point_t) ←
            (map_to_curve_elligator2 (u_14332)) ;;
          ret (temp_14334)) ;;
       '(temp_14337 : ed_point_t) ←
        (curve25519_to_edwards25519 (st_14335)) ;;
      @ret (ed_point_t) (temp_14337) } : code (CEfset ([])) [interface
      #val #[ CURVE25519_TO_EDWARDS25519 ] : curve25519_to_edwards25519_inp → curve25519_to_edwards25519_out ;
      #val #[ MAP_TO_CURVE_ELLIGATOR2 ] : map_to_curve_elligator2_inp → map_to_curve_elligator2_out
      ] _)
    }]).
Fail Next Obligation.
Program Definition package_map_to_curve_elligator2_edwards : package _ _ _ :=
  (seq_link map_to_curve_elligator2_edwards link_rest(
      package_curve25519_to_edwards25519,package_map_to_curve_elligator2)).
Fail Next Obligation.


Notation "'ed_encode_to_curve_inp'" := (
  byte_seq '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'ed_encode_to_curve_out'" := (
  ed_point_result_t : choice_type) (in custom pack_type at level 2).
Definition ED_ENCODE_TO_CURVE : nat :=
  (14351).
Program Definition ed_encode_to_curve
   : package (CEfset ([])) [interface
  #val #[ ED_CLEAR_COFACTOR ] : ed_clear_cofactor_inp → ed_clear_cofactor_out ;
  #val #[ ED_HASH_TO_FIELD ] : ed_hash_to_field_inp → ed_hash_to_field_out ;
  #val #[ MAP_TO_CURVE_ELLIGATOR2_EDWARDS ] : map_to_curve_elligator2_edwards_inp → map_to_curve_elligator2_edwards_out
  ] [interface
  #val #[ ED_ENCODE_TO_CURVE ] : ed_encode_to_curve_inp → ed_encode_to_curve_out
  ] :=
  (
    [package #def #[ ED_ENCODE_TO_CURVE ] (temp_inp : ed_encode_to_curve_inp) : ed_encode_to_curve_out { 
    let '(msg_14339 , dst_14340) := temp_inp : byte_seq '× byte_seq in
    #import {sig #[ ED_CLEAR_COFACTOR ] : ed_clear_cofactor_inp → ed_clear_cofactor_out } as ed_clear_cofactor ;;
    let ed_clear_cofactor := fun x_0 => ed_clear_cofactor (x_0) in
    #import {sig #[ ED_HASH_TO_FIELD ] : ed_hash_to_field_inp → ed_hash_to_field_out } as ed_hash_to_field ;;
    let ed_hash_to_field := fun x_0 x_1 x_2 => ed_hash_to_field (x_0,x_1,x_2) in
    #import {sig #[ MAP_TO_CURVE_ELLIGATOR2_EDWARDS ] : map_to_curve_elligator2_edwards_inp → map_to_curve_elligator2_edwards_out } as map_to_curve_elligator2_edwards ;;
    let map_to_curve_elligator2_edwards := fun x_0 => map_to_curve_elligator2_edwards (
      x_0) in
    ({ code bnd(
        ChoiceEqualityMonad.result_bind_code error_t , seq ed25519_field_element_t , _ , CEfset (
          [])) u_14344 ⇠
      (({ code  '(temp_14342 : seq_ed_result_t) ←
            (ed_hash_to_field (msg_14339) (dst_14340) (usize 1)) ;;
          @ret _ (temp_14342) } : code (CEfset ([])) [interface
          #val #[ ED_HASH_TO_FIELD ] : ed_hash_to_field_inp → ed_hash_to_field_out
          ] _)) in
      ({ code  '(q_14348 : (
              ed25519_field_element_t '×
              ed25519_field_element_t '×
              ed25519_field_element_t '×
              ed25519_field_element_t
            )) ←
          ( '(temp_14345 : ed25519_field_element_t) ←
              (seq_index (u_14344) (usize 0)) ;;
             '(temp_14347 : ed_point_t) ←
              (map_to_curve_elligator2_edwards (temp_14345)) ;;
            ret (temp_14347)) ;;
         '(temp_14350 : ed_point_t) ←
          (ed_clear_cofactor (q_14348)) ;;
        @ret ((result error_t ed_point_t)) (@inl ed_point_t error_t (
            temp_14350)) } : code (CEfset ([])) [interface
        #val #[ ED_CLEAR_COFACTOR ] : ed_clear_cofactor_inp → ed_clear_cofactor_out ;
        #val #[ ED_HASH_TO_FIELD ] : ed_hash_to_field_inp → ed_hash_to_field_out ;
        #val #[ MAP_TO_CURVE_ELLIGATOR2_EDWARDS ] : map_to_curve_elligator2_edwards_inp → map_to_curve_elligator2_edwards_out
        ] _) } : code (CEfset ([])) [interface
      #val #[ ED_CLEAR_COFACTOR ] : ed_clear_cofactor_inp → ed_clear_cofactor_out ;
      #val #[ ED_HASH_TO_FIELD ] : ed_hash_to_field_inp → ed_hash_to_field_out ;
      #val #[ MAP_TO_CURVE_ELLIGATOR2_EDWARDS ] : map_to_curve_elligator2_edwards_inp → map_to_curve_elligator2_edwards_out
      ] _)
    }]).
Fail Next Obligation.
Program Definition package_ed_encode_to_curve : package _ _ _ :=
  (seq_link ed_encode_to_curve link_rest(
      package_ed_clear_cofactor,package_ed_hash_to_field,package_map_to_curve_elligator2_edwards)).
Fail Next Obligation.

