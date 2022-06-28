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

Definition block_size_v : (uint_size) :=
  ((usize 64)).

Definition len_size_v : (uint_size) :=
  ((usize 8)).

Definition k_size_v : (uint_size) :=
  ((usize 64)).

Definition hash_size_v : (uint_size) :=
  (let temp_1 : uint_size :=
      ((usize 256) ./ (usize 8)) in
    (temp_1)).

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
  (11).
Program Definition ch
   : package (fset.fset0) [interface  ] [interface
  #val #[ CH ] : ch_inp → ch_out ] :=
  ([package #def #[ CH ] (temp_inp : ch_inp) : ch_out { 
    let '(x_2 , y_3 , z_6) := temp_inp : uint32 '× uint32 '× uint32 in
    ({ code  temp_5 ←
        ((x_2) .& (y_3)) ;;
       temp_8 ←
        ((not (x_2)) .& (z_6)) ;;
       temp_10 ←
        ((temp_5) .^ (temp_8)) ;;
      @ret (uint32) (temp_10) } : code (fset.fset0) [interface  ] _)
    }]).
Fail Next Obligation.
Program Definition package_ch : package _ _ _ :=
  (ch).
Fail Next Obligation.


Notation "'maj_inp'" := (
  uint32 '× uint32 '× uint32 : choice_type) (in custom pack_type at level 2).
Notation "'maj_out'" := (uint32 : choice_type) (in custom pack_type at level 2).
Definition MAJ : nat :=
  (25).
Program Definition maj
   : package (fset.fset0) [interface  ] [interface
  #val #[ MAJ ] : maj_inp → maj_out ] :=
  ([package #def #[ MAJ ] (temp_inp : maj_inp) : maj_out { 
    let '(x_12 , y_13 , z_16) := temp_inp : uint32 '× uint32 '× uint32 in
    ({ code  temp_15 ←
        ((x_12) .& (y_13)) ;;
       temp_18 ←
        ((x_12) .& (z_16)) ;;
       temp_20 ←
        ((y_13) .& (z_16)) ;;
       temp_22 ←
        ((temp_18) .^ (temp_20)) ;;
       temp_24 ←
        ((temp_15) .^ (temp_22)) ;;
      @ret (uint32) (temp_24) } : code (fset.fset0) [interface  ] _)
    }]).
Fail Next Obligation.
Program Definition package_maj : package _ _ _ :=
  (maj).
Fail Next Obligation.

Definition op_table_v : (op_table_type_t) :=
  (let temp_27 : nseq uint_size 12 :=
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
    (temp_27)).

Definition k_table_v : (round_constants_table_t) :=
  (let temp_29 : int32 :=
      (secret (@repr U32 1116352408)) in
    let temp_31 : int32 :=
      (secret (@repr U32 1899447441)) in
    let temp_33 : int32 :=
      (secret (@repr U32 3049323471)) in
    let temp_35 : int32 :=
      (secret (@repr U32 3921009573)) in
    let temp_37 : int32 :=
      (secret (@repr U32 961987163)) in
    let temp_39 : int32 :=
      (secret (@repr U32 1508970993)) in
    let temp_41 : int32 :=
      (secret (@repr U32 2453635748)) in
    let temp_43 : int32 :=
      (secret (@repr U32 2870763221)) in
    let temp_45 : int32 :=
      (secret (@repr U32 3624381080)) in
    let temp_47 : int32 :=
      (secret (@repr U32 310598401)) in
    let temp_49 : int32 :=
      (secret (@repr U32 607225278)) in
    let temp_51 : int32 :=
      (secret (@repr U32 1426881987)) in
    let temp_53 : int32 :=
      (secret (@repr U32 1925078388)) in
    let temp_55 : int32 :=
      (secret (@repr U32 2162078206)) in
    let temp_57 : int32 :=
      (secret (@repr U32 2614888103)) in
    let temp_59 : int32 :=
      (secret (@repr U32 3248222580)) in
    let temp_61 : int32 :=
      (secret (@repr U32 3835390401)) in
    let temp_63 : int32 :=
      (secret (@repr U32 4022224774)) in
    let temp_65 : int32 :=
      (secret (@repr U32 264347078)) in
    let temp_67 : int32 :=
      (secret (@repr U32 604807628)) in
    let temp_69 : int32 :=
      (secret (@repr U32 770255983)) in
    let temp_71 : int32 :=
      (secret (@repr U32 1249150122)) in
    let temp_73 : int32 :=
      (secret (@repr U32 1555081692)) in
    let temp_75 : int32 :=
      (secret (@repr U32 1996064986)) in
    let temp_77 : int32 :=
      (secret (@repr U32 2554220882)) in
    let temp_79 : int32 :=
      (secret (@repr U32 2821834349)) in
    let temp_81 : int32 :=
      (secret (@repr U32 2952996808)) in
    let temp_83 : int32 :=
      (secret (@repr U32 3210313671)) in
    let temp_85 : int32 :=
      (secret (@repr U32 3336571891)) in
    let temp_87 : int32 :=
      (secret (@repr U32 3584528711)) in
    let temp_89 : int32 :=
      (secret (@repr U32 113926993)) in
    let temp_91 : int32 :=
      (secret (@repr U32 338241895)) in
    let temp_93 : int32 :=
      (secret (@repr U32 666307205)) in
    let temp_95 : int32 :=
      (secret (@repr U32 773529912)) in
    let temp_97 : int32 :=
      (secret (@repr U32 1294757372)) in
    let temp_99 : int32 :=
      (secret (@repr U32 1396182291)) in
    let temp_101 : int32 :=
      (secret (@repr U32 1695183700)) in
    let temp_103 : int32 :=
      (secret (@repr U32 1986661051)) in
    let temp_105 : int32 :=
      (secret (@repr U32 2177026350)) in
    let temp_107 : int32 :=
      (secret (@repr U32 2456956037)) in
    let temp_109 : int32 :=
      (secret (@repr U32 2730485921)) in
    let temp_111 : int32 :=
      (secret (@repr U32 2820302411)) in
    let temp_113 : int32 :=
      (secret (@repr U32 3259730800)) in
    let temp_115 : int32 :=
      (secret (@repr U32 3345764771)) in
    let temp_117 : int32 :=
      (secret (@repr U32 3516065817)) in
    let temp_119 : int32 :=
      (secret (@repr U32 3600352804)) in
    let temp_121 : int32 :=
      (secret (@repr U32 4094571909)) in
    let temp_123 : int32 :=
      (secret (@repr U32 275423344)) in
    let temp_125 : int32 :=
      (secret (@repr U32 430227734)) in
    let temp_127 : int32 :=
      (secret (@repr U32 506948616)) in
    let temp_129 : int32 :=
      (secret (@repr U32 659060556)) in
    let temp_131 : int32 :=
      (secret (@repr U32 883997877)) in
    let temp_133 : int32 :=
      (secret (@repr U32 958139571)) in
    let temp_135 : int32 :=
      (secret (@repr U32 1322822218)) in
    let temp_137 : int32 :=
      (secret (@repr U32 1537002063)) in
    let temp_139 : int32 :=
      (secret (@repr U32 1747873779)) in
    let temp_141 : int32 :=
      (secret (@repr U32 1955562222)) in
    let temp_143 : int32 :=
      (secret (@repr U32 2024104815)) in
    let temp_145 : int32 :=
      (secret (@repr U32 2227730452)) in
    let temp_147 : int32 :=
      (secret (@repr U32 2361852424)) in
    let temp_149 : int32 :=
      (secret (@repr U32 2428436474)) in
    let temp_151 : int32 :=
      (secret (@repr U32 2756734187)) in
    let temp_153 : int32 :=
      (secret (@repr U32 3204031479)) in
    let temp_155 : int32 :=
      (secret (@repr U32 3329325298)) in
    let temp_157 : nseq uint32 64 :=
      (array_from_list uint32 [
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
          temp_155
        ]) in
    (temp_157)).

Definition hash_init_v : (hash_t) :=
  (let temp_159 : int32 :=
      (secret (@repr U32 1779033703)) in
    let temp_161 : int32 :=
      (secret (@repr U32 3144134277)) in
    let temp_163 : int32 :=
      (secret (@repr U32 1013904242)) in
    let temp_165 : int32 :=
      (secret (@repr U32 2773480762)) in
    let temp_167 : int32 :=
      (secret (@repr U32 1359893119)) in
    let temp_169 : int32 :=
      (secret (@repr U32 2600822924)) in
    let temp_171 : int32 :=
      (secret (@repr U32 528734635)) in
    let temp_173 : int32 :=
      (secret (@repr U32 1541459225)) in
    let temp_175 : nseq uint32 8 :=
      (array_from_list uint32 [
          temp_159;
          temp_161;
          temp_163;
          temp_165;
          temp_167;
          temp_169;
          temp_171;
          temp_173
        ]) in
    (temp_175)).

Definition tmp_197_loc : ChoiceEqualityLocation :=
  ((uint32 ; 216%nat)).
Notation "'sigma_inp'" := (
  uint32 '× uint_size '× uint_size : choice_type) (in custom pack_type at level 2).
Notation "'sigma_out'" := (
  uint32 : choice_type) (in custom pack_type at level 2).
Definition SIGMA : nat :=
  (217).
Program Definition sigma
   : package (CEfset ([tmp_197_loc])) [interface  ] [interface
  #val #[ SIGMA ] : sigma_inp → sigma_out ] :=
  ([package #def #[ SIGMA ] (temp_inp : sigma_inp) : sigma_out { 
    let '(
      x_176 , i_177 , op_186) := temp_inp : uint32 '× uint_size '× uint_size in
    ({ code  '(tmp_197 : uint32) ←
          ( '(temp_179 : uint_size) ←
              ((usize 3) .* (i_177)) ;;
             '(temp_181 : uint_size) ←
              ((temp_179) .+ (usize 2)) ;;
             temp_183 ←
              (array_index (op_table_v) (temp_181)) ;;
             temp_185 ←
              (uint32_rotate_right (x_176) (temp_183)) ;;
            ret (temp_185)) ;;
        #put tmp_197_loc := tmp_197 ;;
       '(temp_188 : bool_ChoiceEquality) ←
        ((op_186) =.? (usize 0)) ;;
       '(tmp_197 : (uint32)) ←
        (if temp_188:bool_ChoiceEquality
          then (({ code  '(tmp_197 : uint32) ←
                  (( '(temp_190 : uint_size) ←
                        ((usize 3) .* (i_177)) ;;
                       '(temp_192 : uint_size) ←
                        ((temp_190) .+ (usize 2)) ;;
                       temp_194 ←
                        (array_index (op_table_v) (temp_192)) ;;
                       temp_196 ←
                        ((x_176) shift_right (temp_194)) ;;
                      ret (temp_196))) ;;
                #put tmp_197_loc := tmp_197 ;;
              
              @ret ((uint32)) (tmp_197) } : code (CEfset (
                  [tmp_197_loc])) [interface  ] _))
          else @ret ((uint32)) (tmp_197)) ;;
      
       '(temp_199 : uint_size) ←
        ((usize 3) .* (i_177)) ;;
       temp_201 ←
        (array_index (op_table_v) (temp_199)) ;;
       temp_203 ←
        (uint32_rotate_right (x_176) (temp_201)) ;;
       '(temp_205 : uint_size) ←
        ((usize 3) .* (i_177)) ;;
       '(temp_207 : uint_size) ←
        ((temp_205) .+ (usize 1)) ;;
       temp_209 ←
        (array_index (op_table_v) (temp_207)) ;;
       temp_211 ←
        (uint32_rotate_right (x_176) (temp_209)) ;;
       temp_213 ←
        ((temp_203) .^ (temp_211)) ;;
       temp_215 ←
        ((temp_213) .^ (tmp_197)) ;;
      @ret (uint32) (temp_215) } : code (CEfset ([tmp_197_loc])) [interface 
      ] _)
    }]).
Fail Next Obligation.
Program Definition package_sigma : package _ _ _ :=
  (sigma).
Fail Next Obligation.

Definition s_229_loc : ChoiceEqualityLocation :=
  ((round_constants_table_t ; 262%nat)).
Notation "'schedule_inp'" := (
  block_t : choice_type) (in custom pack_type at level 2).
Notation "'schedule_out'" := (
  round_constants_table_t : choice_type) (in custom pack_type at level 2).
Definition SCHEDULE : nat :=
  (263).
Program Definition schedule
   : package (CEfset ([s_229_loc])) [interface
  #val #[ SIGMA ] : sigma_inp → sigma_out ] [interface
  #val #[ SCHEDULE ] : schedule_inp → schedule_out ] :=
  ([package #def #[ SCHEDULE ] (temp_inp : schedule_inp) : schedule_out { 
    let '(block_218) := temp_inp : block_t in
    #import {sig #[ SIGMA ] : sigma_inp → sigma_out } as sigma ;;
    let sigma := fun x_0 x_1 x_2 => sigma (x_0,x_1,x_2) in
    ({ code  '(b_227 : seq uint32) ←
        ( temp_220 ←
            (array_to_be_uint32s (block_218)) ;;
          ret (temp_220)) ;;
       '(s_229 : round_constants_table_t) ←
          ( '(temp_222 : round_constants_table_t) ←
              (array_new_ (default : uint32) (k_size_v)) ;;
            ret (temp_222)) ;;
        #put s_229_loc := s_229 ;;
       '(s_229 : (round_constants_table_t)) ←
        (foldi' (usize 0) (k_size_v) s_229 (L2 := CEfset ([s_229_loc])) (
              I2 := [interface #val #[ SIGMA ] : sigma_inp → sigma_out
              ]) (H_loc_incl := _) (H_opsig_incl := _) (fun i_223 s_229 =>
            ({ code  '(temp_225 : bool_ChoiceEquality) ←
                ((i_223) <.? (usize 16)) ;;
               '(s_229 : (round_constants_table_t)) ←
                (if temp_225:bool_ChoiceEquality
                  then (({ code  '(s_229 : round_constants_table_t) ←
                        ( '(temp_228 : uint32) ←
                            (seq_index (b_227) (i_223)) ;;
                          ret (array_upd s_229 (i_223) (temp_228))) ;;
                      
                      @ret ((round_constants_table_t)) (s_229) } : code (
                        CEfset ([s_229_loc])) [interface  ] _))
                  else  (({ code  '(t16_259 : uint32) ←
                        ( '(temp_231 : uint_size) ←
                            ((i_223) .- (usize 16)) ;;
                           temp_233 ←
                            (array_index (s_229) (temp_231)) ;;
                          ret (temp_233)) ;;
                       '(t15_249 : uint32) ←
                        ( '(temp_235 : uint_size) ←
                            ((i_223) .- (usize 15)) ;;
                           temp_237 ←
                            (array_index (s_229) (temp_235)) ;;
                          ret (temp_237)) ;;
                       '(t7_253 : uint32) ←
                        ( '(temp_239 : uint_size) ←
                            ((i_223) .- (usize 7)) ;;
                           temp_241 ←
                            (array_index (s_229) (temp_239)) ;;
                          ret (temp_241)) ;;
                       '(t2_246 : uint32) ←
                        ( '(temp_243 : uint_size) ←
                            ((i_223) .- (usize 2)) ;;
                           temp_245 ←
                            (array_index (s_229) (temp_243)) ;;
                          ret (temp_245)) ;;
                       '(s1_252 : uint32) ←
                        ( '(temp_248 : uint32) ←
                            (sigma (t2_246) (usize 3) (usize 0)) ;;
                          ret (temp_248)) ;;
                       '(s0_256 : uint32) ←
                        ( '(temp_251 : uint32) ←
                            (sigma (t15_249) (usize 2) (usize 0)) ;;
                          ret (temp_251)) ;;
                       '(s_229 : round_constants_table_t) ←
                        ( '(temp_255 : uint32) ←
                            ((s1_252) .+ (t7_253)) ;;
                           '(temp_258 : uint32) ←
                            ((temp_255) .+ (s0_256)) ;;
                           '(temp_261 : uint32) ←
                            ((temp_258) .+ (t16_259)) ;;
                          ret (array_upd s_229 (i_223) (temp_261))) ;;
                      
                      @ret ((round_constants_table_t)) (s_229) } : code (
                        CEfset ([s_229_loc])) [interface
                      #val #[ SIGMA ] : sigma_inp → sigma_out ] _))) ;;
              
              @ret ((round_constants_table_t)) (s_229) } : code (CEfset (
                  [s_229_loc])) [interface
              #val #[ SIGMA ] : sigma_inp → sigma_out ] _))) ;;
      
      @ret (round_constants_table_t) (s_229) } : code (CEfset (
          [s_229_loc])) [interface #val #[ SIGMA ] : sigma_inp → sigma_out
      ] _)
    }]).
Fail Next Obligation.
Program Definition package_schedule : package _ _ _ :=
  (seq_link schedule link_rest(package_sigma)).
Fail Next Obligation.

Definition h_266_loc : ChoiceEqualityLocation :=
  ((hash_t ; 320%nat)).
Notation "'shuffle_inp'" := (
  round_constants_table_t '× hash_t : choice_type) (in custom pack_type at level 2).
Notation "'shuffle_out'" := (
  hash_t : choice_type) (in custom pack_type at level 2).
Definition SHUFFLE : nat :=
  (321).
Program Definition shuffle
   : package (CEfset ([h_266_loc])) [interface
  #val #[ CH ] : ch_inp → ch_out ; #val #[ MAJ ] : maj_inp → maj_out ;
  #val #[ SIGMA ] : sigma_inp → sigma_out ] [interface
  #val #[ SHUFFLE ] : shuffle_inp → shuffle_out ] :=
  ([package #def #[ SHUFFLE ] (temp_inp : shuffle_inp) : shuffle_out { 
    let '(
      ws_300 , hashi_264) := temp_inp : round_constants_table_t '× hash_t in
    #import {sig #[ CH ] : ch_inp → ch_out } as ch ;;
    let ch := fun x_0 x_1 x_2 => ch (x_0,x_1,x_2) in
    #import {sig #[ MAJ ] : maj_inp → maj_out } as maj ;;
    let maj := fun x_0 x_1 x_2 => maj (x_0,x_1,x_2) in
    #import {sig #[ SIGMA ] : sigma_inp → sigma_out } as sigma ;;
    let sigma := fun x_0 x_1 x_2 => sigma (x_0,x_1,x_2) in
    ({ code  '(h_266 : hash_t) ←
          (ret (hashi_264)) ;;
        #put h_266_loc := h_266 ;;
       '(h_266 : (hash_t)) ←
        (foldi' (usize 0) (k_size_v) h_266 (L2 := CEfset ([h_266_loc])) (
              I2 := [interface #val #[ CH ] : ch_inp → ch_out ;
              #val #[ MAJ ] : maj_inp → maj_out ;
              #val #[ SIGMA ] : sigma_inp → sigma_out
              ]) (H_loc_incl := _) (H_opsig_incl := _) (fun i_294 h_266 =>
            ({ code  '(a0_304 : uint32) ←
                ( temp_267 ←
                    (array_index (h_266) (usize 0)) ;;
                  ret (temp_267)) ;;
               '(b0_307 : uint32) ←
                ( temp_269 ←
                    (array_index (h_266) (usize 1)) ;;
                  ret (temp_269)) ;;
               '(c0_308 : uint32) ←
                ( temp_271 ←
                    (array_index (h_266) (usize 2)) ;;
                  ret (temp_271)) ;;
               '(d0_317 : uint32) ←
                ( temp_273 ←
                    (array_index (h_266) (usize 3)) ;;
                  ret (temp_273)) ;;
               '(e0_283 : uint32) ←
                ( temp_275 ←
                    (array_index (h_266) (usize 4)) ;;
                  ret (temp_275)) ;;
               '(f0_288 : uint32) ←
                ( temp_277 ←
                    (array_index (h_266) (usize 5)) ;;
                  ret (temp_277)) ;;
               '(g0_289 : uint32) ←
                ( temp_279 ←
                    (array_index (h_266) (usize 6)) ;;
                  ret (temp_279)) ;;
               '(h0_282 : uint32) ←
                ( temp_281 ←
                    (array_index (h_266) (usize 7)) ;;
                  ret (temp_281)) ;;
               '(t1_313 : uint32) ←
                ( '(temp_285 : uint32) ←
                    (sigma (e0_283) (usize 1) (usize 1)) ;;
                   '(temp_287 : uint32) ←
                    ((h0_282) .+ (temp_285)) ;;
                   '(temp_291 : uint32) ←
                    (ch (e0_283) (f0_288) (g0_289)) ;;
                   '(temp_293 : uint32) ←
                    ((temp_287) .+ (temp_291)) ;;
                   temp_296 ←
                    (array_index (k_table_v) (i_294)) ;;
                   '(temp_298 : uint32) ←
                    ((temp_293) .+ (temp_296)) ;;
                   temp_301 ←
                    (array_index (ws_300) (i_294)) ;;
                   '(temp_303 : uint32) ←
                    ((temp_298) .+ (temp_301)) ;;
                  ret (temp_303)) ;;
               '(t2_314 : uint32) ←
                ( '(temp_306 : uint32) ←
                    (sigma (a0_304) (usize 0) (usize 1)) ;;
                   '(temp_310 : uint32) ←
                    (maj (a0_304) (b0_307) (c0_308)) ;;
                   '(temp_312 : uint32) ←
                    ((temp_306) .+ (temp_310)) ;;
                  ret (temp_312)) ;;
               '(h_266 : hash_t) ←
                ( '(temp_316 : uint32) ←
                    ((t1_313) .+ (t2_314)) ;;
                  ret (array_upd h_266 (usize 0) (temp_316))) ;;
              
               '(h_266 : hash_t) ←
                (ret (array_upd h_266 (usize 1) (a0_304))) ;;
              
               '(h_266 : hash_t) ←
                (ret (array_upd h_266 (usize 2) (b0_307))) ;;
              
               '(h_266 : hash_t) ←
                (ret (array_upd h_266 (usize 3) (c0_308))) ;;
              
               '(h_266 : hash_t) ←
                ( '(temp_319 : uint32) ←
                    ((d0_317) .+ (t1_313)) ;;
                  ret (array_upd h_266 (usize 4) (temp_319))) ;;
              
               '(h_266 : hash_t) ←
                (ret (array_upd h_266 (usize 5) (e0_283))) ;;
              
               '(h_266 : hash_t) ←
                (ret (array_upd h_266 (usize 6) (f0_288))) ;;
              
               '(h_266 : hash_t) ←
                (ret (array_upd h_266 (usize 7) (g0_289))) ;;
              
              @ret ((hash_t)) (h_266) } : code (CEfset ([h_266_loc])) [interface
              #val #[ CH ] : ch_inp → ch_out ;
              #val #[ MAJ ] : maj_inp → maj_out ;
              #val #[ SIGMA ] : sigma_inp → sigma_out ] _))) ;;
      
      @ret (hash_t) (h_266) } : code (CEfset ([h_266_loc])) [interface
      #val #[ CH ] : ch_inp → ch_out ; #val #[ MAJ ] : maj_inp → maj_out ;
      #val #[ SIGMA ] : sigma_inp → sigma_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_shuffle : package _ _ _ :=
  (seq_link shuffle link_rest(package_ch,package_maj,package_sigma)).
Fail Next Obligation.

Definition h_331_loc : ChoiceEqualityLocation :=
  ((hash_t ; 337%nat)).
Notation "'compress_inp'" := (
  block_t '× hash_t : choice_type) (in custom pack_type at level 2).
Notation "'compress_out'" := (
  hash_t : choice_type) (in custom pack_type at level 2).
Definition COMPRESS : nat :=
  (338).
Program Definition compress
   : package (CEfset ([h_331_loc])) [interface
  #val #[ SCHEDULE ] : schedule_inp → schedule_out ;
  #val #[ SHUFFLE ] : shuffle_inp → shuffle_out ] [interface
  #val #[ COMPRESS ] : compress_inp → compress_out ] :=
  ([package #def #[ COMPRESS ] (temp_inp : compress_inp) : compress_out { 
    let '(block_322 , h_in_326) := temp_inp : block_t '× hash_t in
    #import {sig #[ SCHEDULE ] : schedule_inp → schedule_out } as schedule ;;
    let schedule := fun x_0 => schedule (x_0) in
    #import {sig #[ SHUFFLE ] : shuffle_inp → shuffle_out } as shuffle ;;
    let shuffle := fun x_0 x_1 => shuffle (x_0,x_1) in
    ({ code  '(s_325 : round_constants_table_t) ←
        ( '(temp_324 : round_constants_table_t) ←
            (schedule (block_322)) ;;
          ret (temp_324)) ;;
       '(h_331 : hash_t) ←
          ( '(temp_328 : hash_t) ←
              (shuffle (s_325) (h_in_326)) ;;
            ret (temp_328)) ;;
        #put h_331_loc := h_331 ;;
       '(h_331 : (hash_t)) ←
        (foldi' (usize 0) (usize 8) h_331 (L2 := CEfset ([h_331_loc])) (
              I2 := [interface
              #val #[ SCHEDULE ] : schedule_inp → schedule_out ;
              #val #[ SHUFFLE ] : shuffle_inp → shuffle_out
              ]) (H_loc_incl := _) (H_opsig_incl := _) (fun i_329 h_331 =>
            ({ code  '(h_331 : hash_t) ←
                ( temp_332 ←
                    (array_index (h_331) (i_329)) ;;
                   temp_334 ←
                    (array_index (h_in_326) (i_329)) ;;
                   '(temp_336 : uint32) ←
                    ((temp_332) .+ (temp_334)) ;;
                  ret (array_upd h_331 (i_329) (temp_336))) ;;
              
              @ret ((hash_t)) (h_331) } : code (CEfset ([h_331_loc])) [interface
               ] _))) ;;
      
      @ret (hash_t) (h_331) } : code (CEfset ([h_331_loc])) [interface
      #val #[ SCHEDULE ] : schedule_inp → schedule_out ;
      #val #[ SHUFFLE ] : shuffle_inp → shuffle_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_compress : package _ _ _ :=
  (seq_link compress link_rest(package_schedule,package_shuffle)).
Fail Next Obligation.

Definition last_block_len_357_loc : ChoiceEqualityLocation :=
  ((uint_size ; 413%nat)).
Definition last_block_356_loc : ChoiceEqualityLocation :=
  ((block_t ; 414%nat)).
Definition pad_block_392_loc : ChoiceEqualityLocation :=
  ((block_t ; 415%nat)).
Definition h_355_loc : ChoiceEqualityLocation :=
  ((hash_t ; 416%nat)).
Notation "'hash_inp'" := (
  byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'hash_out'" := (
  sha256_digest_t : choice_type) (in custom pack_type at level 2).
Definition HASH : nat :=
  (417).
Program Definition hash
   : package (CEfset (
      [h_355_loc ; last_block_356_loc ; last_block_len_357_loc ; pad_block_392_loc])) [interface
  #val #[ COMPRESS ] : compress_inp → compress_out ] [interface
  #val #[ HASH ] : hash_inp → hash_out ] :=
  ([package #def #[ HASH ] (temp_inp : hash_inp) : hash_out { 
    let '(msg_341) := temp_inp : byte_seq in
    #import {sig #[ COMPRESS ] : compress_inp → compress_out } as compress ;;
    let compress := fun x_0 x_1 => compress (x_0,x_1) in
    ({ code  '(h_355 : hash_t) ←
          (ret (hash_init_v)) ;;
        #put h_355_loc := h_355 ;;
       '(last_block_356 : block_t) ←
          ( '(temp_340 : block_t) ←
              (array_new_ (default : uint8) (block_size_v)) ;;
            ret (temp_340)) ;;
        #put last_block_356_loc := last_block_356 ;;
       '(last_block_len_357 : uint_size) ←
          (ret (usize 0)) ;;
        #put last_block_len_357_loc := last_block_len_357 ;;
       '(temp_343 : uint_size) ←
        (seq_num_chunks (msg_341) (block_size_v)) ;;
       temp_412 ←
        (foldi' (usize 0) (temp_343) prod_ce(
              h_355,
              last_block_356,
              last_block_len_357
            ) (L2 := CEfset (
                [h_355_loc ; last_block_356_loc ; last_block_len_357_loc ; pad_block_392_loc])) (
              I2 := [interface
              #val #[ COMPRESS ] : compress_inp → compress_out
              ]) (H_loc_incl := _) (H_opsig_incl := _) (fun i_344 '(
              h_355,
              last_block_356,
              last_block_len_357
            ) =>
            ({ code  temp_366 ←
                ( '(temp_346 : (uint_size '× seq uint8)) ←
                    (seq_get_chunk (msg_341) (block_size_v) (i_344)) ;;
                  ret (temp_346)) ;;
              let '(block_len_347, block_352) :=
                (temp_366) : (uint_size '× seq uint8) in
               '(temp_349 : bool_ChoiceEquality) ←
                ((block_len_347) <.? (block_size_v)) ;;
               temp_364 ←
                (if temp_349:bool_ChoiceEquality
                  then (({ code  '(last_block_356 : block_t) ←
                          (( '(temp_351 : block_t) ←
                                (array_new_ (default : uint8) (block_size_v)) ;;
                               '(temp_354 : block_t) ←
                                (array_update_start (temp_351) (block_352)) ;;
                              ret (temp_354))) ;;
                        #put last_block_356_loc := last_block_356 ;;
                      
                       '(last_block_len_357 : uint_size) ←
                          ((ret (block_len_347))) ;;
                        #put last_block_len_357_loc := last_block_len_357 ;;
                      
                      @ret ((hash_t '× block_t '× uint_size)) (prod_ce(
                          h_355,
                          last_block_356,
                          last_block_len_357
                        )) } : code (CEfset (
                          [h_355_loc ; last_block_356_loc ; last_block_len_357_loc])) [interface
                       ] _))
                  else  (({ code  '(compress_input_360 : block_t) ←
                        ( '(temp_359 : block_t) ←
                            (array_from_seq (block_size_v) (block_352)) ;;
                          ret (temp_359)) ;;
                       '(h_355 : hash_t) ←
                          (( '(temp_362 : hash_t) ←
                                (compress (compress_input_360) (h_355)) ;;
                              ret (temp_362))) ;;
                        #put h_355_loc := h_355 ;;
                      
                      @ret ((hash_t '× block_t '× uint_size)) (prod_ce(
                          h_355,
                          last_block_356,
                          last_block_len_357
                        )) } : code (CEfset (
                          [h_355_loc ; last_block_356_loc ; last_block_len_357_loc])) [interface
                      #val #[ COMPRESS ] : compress_inp → compress_out
                      ] _))) ;;
              let '(h_355, last_block_356, last_block_len_357) :=
                (temp_364) : (hash_t '× block_t '× uint_size) in
              
              @ret ((hash_t '× block_t '× uint_size)) (prod_ce(
                  h_355,
                  last_block_356,
                  last_block_len_357
                )) } : code (CEfset (
                  [h_355_loc ; last_block_356_loc ; last_block_len_357_loc])) [interface
              #val #[ COMPRESS ] : compress_inp → compress_out ] _))) ;;
      let '(h_355, last_block_356, last_block_len_357) :=
        (temp_412) : (hash_t '× block_t '× uint_size) in
      
       '(last_block_356 : block_t) ←
        ( '(temp_368 : int8) ←
            (secret (@repr U8 128)) ;;
          ret (array_upd last_block_356 (last_block_len_357) (temp_368))) ;;
      
       '(len_bist_381 : uint64) ←
        ( '(temp_370 : uint_size) ←
            (seq_len (msg_341)) ;;
           '(temp_372 : uint_size) ←
            ((temp_370) .* (usize 8)) ;;
           '(temp_374 : int64) ←
            (secret (pub_u64 (temp_372))) ;;
          ret (temp_374)) ;;
       '(temp_376 : uint_size) ←
        ((block_size_v) .- (len_size_v)) ;;
       '(temp_378 : bool_ChoiceEquality) ←
        ((last_block_len_357) <.? (temp_376)) ;;
       temp_410 ←
        (if temp_378:bool_ChoiceEquality
          then (({ code  '(last_block_356 : block_t) ←
                  (( '(temp_380 : uint_size) ←
                        ((block_size_v) .- (len_size_v)) ;;
                       '(temp_383 : uint64_word_t) ←
                        (uint64_to_be_bytes (len_bist_381)) ;;
                       '(temp_385 : seq uint8) ←
                        (array_to_seq (temp_383)) ;;
                       '(temp_387 : block_t) ←
                        (array_update (last_block_356) (temp_380) (temp_385)) ;;
                      ret (temp_387))) ;;
                #put last_block_356_loc := last_block_356 ;;
              
               '(h_355 : hash_t) ←
                  (( '(temp_389 : hash_t) ←
                        (compress (last_block_356) (h_355)) ;;
                      ret (temp_389))) ;;
                #put h_355_loc := h_355 ;;
              
              @ret ((hash_t '× block_t)) (prod_ce(h_355, last_block_356
                )) } : code (CEfset (
                  [h_355_loc ; last_block_356_loc ; last_block_len_357_loc])) [interface
              #val #[ COMPRESS ] : compress_inp → compress_out ] _))
          else  (({ code  '(pad_block_392 : block_t) ←
                  ( '(temp_391 : block_t) ←
                      (array_new_ (default : uint8) (block_size_v)) ;;
                    ret (temp_391)) ;;
                #put pad_block_392_loc := pad_block_392 ;;
               '(pad_block_392 : block_t) ←
                  (( '(temp_394 : uint_size) ←
                        ((block_size_v) .- (len_size_v)) ;;
                       '(temp_396 : uint64_word_t) ←
                        (uint64_to_be_bytes (len_bist_381)) ;;
                       '(temp_398 : seq uint8) ←
                        (array_to_seq (temp_396)) ;;
                       '(temp_400 : block_t) ←
                        (array_update (pad_block_392) (temp_394) (temp_398)) ;;
                      ret (temp_400))) ;;
                #put pad_block_392_loc := pad_block_392 ;;
              
               '(h_355 : hash_t) ←
                  (( '(temp_402 : hash_t) ←
                        (compress (last_block_356) (h_355)) ;;
                      ret (temp_402))) ;;
                #put h_355_loc := h_355 ;;
              
               '(h_355 : hash_t) ←
                  (( '(temp_404 : hash_t) ←
                        (compress (pad_block_392) (h_355)) ;;
                      ret (temp_404))) ;;
                #put h_355_loc := h_355 ;;
              
              @ret ((hash_t '× block_t)) (prod_ce(h_355, last_block_356
                )) } : code (CEfset (
                  [h_355_loc ; last_block_356_loc ; last_block_len_357_loc ; pad_block_392_loc])) [interface
              #val #[ COMPRESS ] : compress_inp → compress_out ] _))) ;;
      let '(h_355, last_block_356) :=
        (temp_410) : (hash_t '× block_t) in
      
       '(temp_406 : seq int8) ←
        (array_to_be_bytes (h_355)) ;;
       '(temp_408 : sha256_digest_t) ←
        (array_from_seq (hash_size_v) (temp_406)) ;;
      @ret (sha256_digest_t) (temp_408) } : code (CEfset (
          [h_355_loc ; last_block_356_loc ; last_block_len_357_loc ; pad_block_392_loc])) [interface
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
  (421).
Program Definition sha256
   : package (CEfset ([])) [interface #val #[ HASH ] : hash_inp → hash_out
  ] [interface #val #[ SHA256 ] : sha256_inp → sha256_out ] :=
  ([package #def #[ SHA256 ] (temp_inp : sha256_inp) : sha256_out { 
    let '(msg_418) := temp_inp : byte_seq in
    #import {sig #[ HASH ] : hash_inp → hash_out } as hash ;;
    let hash := fun x_0 => hash (x_0) in
    ({ code  '(temp_420 : sha256_digest_t) ←
        (hash (msg_418)) ;;
      @ret (sha256_digest_t) (temp_420) } : code (CEfset ([])) [interface
      #val #[ HASH ] : hash_inp → hash_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_sha256 : package _ _ _ :=
  (seq_link sha256 link_rest(package_hash)).
Fail Next Obligation.

