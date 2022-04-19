(** This file was automatically generated using Hacspec **)
Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
From QuickChick Require Import QuickChick.
Require Import QuickChickLib.
Require Import Hacspec_Lib.

Definition fp_canvas_t := nseq (int8) (48).
Definition fp_t :=
  nat_mod 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab.
Instance show_fp_t : Show (fp_t) := Build_Show (fp_t) (fun x => show (GZnZ.val _ x)).
Definition g_fp_t : G (fp_t) := @bindGen Z (fp_t) (arbitrary) (fun x => returnGen (@Z_in_nat_mod _ x)).
Instance gen_fp_t : Gen (fp_t) := Build_Gen fp_t g_fp_t.


Definition serialized_fp_t := nseq (uint8) (usize 48).

Definition array_fp_t := nseq (uint64) (usize 6).

Definition scalar_canvas_t := nseq (int8) (32).
Definition scalar_t :=
  nat_mod 0x8000000000000000000000000000000000000000000000000000000000000000.
Instance show_scalar_t : Show (scalar_t) := Build_Show (scalar_t) (fun x => show (GZnZ.val _ x)).
Definition g_scalar_t : G (scalar_t) := @bindGen Z (scalar_t) (arbitrary) (fun x => returnGen (@Z_in_nat_mod _ x)).
Instance gen_scalar_t : Gen (scalar_t) := Build_Gen scalar_t g_scalar_t.


Notation "'g1_t'" := ((fp_t × fp_t × bool)) : hacspec_scope.
Instance show_g1_t : Show (g1_t) :=
Build_Show g1_t (fun x =>
  let (x, x0) := x in
  let (x, x1) := x in
  (
    ("(") ++ ((show x) ++ ((",") ++ ((show x0) ++ ((",") ++ ((show x1) ++ (")"))))))))%string.
Definition g_g1_t : G (g1_t) :=
bindGen arbitrary (fun x0 : fp_t =>
  bindGen arbitrary (fun x1 : fp_t =>
  bindGen arbitrary (fun x2 : bool =>
  returnGen (x0,x1,x2)))).
Instance gen_g1_t : Gen (g1_t) := Build_Gen g1_t g_g1_t.


Notation "'fp2_t'" := ((fp_t × fp_t)) : hacspec_scope.
Instance show_fp2_t : Show (fp2_t) :=
Build_Show fp2_t (fun x =>
  let (x, x0) := x in
  (("(") ++ ((show x) ++ ((",") ++ ((show x0) ++ (")"))))))%string.
Definition g_fp2_t : G (fp2_t) :=
bindGen arbitrary (fun x0 : fp_t =>
  bindGen arbitrary (fun x1 : fp_t =>
  returnGen (x0,x1))).
Instance gen_fp2_t : Gen (fp2_t) := Build_Gen fp2_t g_fp2_t.


Notation "'g2_t'" := ((fp2_t × fp2_t × bool)) : hacspec_scope.
Instance show_g2_t : Show (g2_t) :=
Build_Show g2_t (fun x =>
  let (x, x0) := x in
  let (x, x1) := x in
  (
    ("(") ++ ((show x) ++ ((",") ++ ((show x0) ++ ((",") ++ ((show x1) ++ (")"))))))))%string.
Definition g_g2_t : G (g2_t) :=
bindGen arbitrary (fun x0 : fp2_t =>
  bindGen arbitrary (fun x1 : fp2_t =>
  bindGen arbitrary (fun x2 : bool =>
  returnGen (x0,x1,x2)))).
Instance gen_g2_t : Gen (g2_t) := Build_Gen g2_t g_g2_t.


Notation "'fp6_t'" := ((fp2_t × fp2_t × fp2_t)) : hacspec_scope.
Instance show_fp6_t : Show (fp6_t) :=
Build_Show fp6_t (fun x =>
  let (x, x0) := x in
  let (x, x1) := x in
  (
    ("(") ++ ((show x) ++ ((",") ++ ((show x0) ++ ((",") ++ ((show x1) ++ (")"))))))))%string.
Definition g_fp6_t : G (fp6_t) :=
bindGen arbitrary (fun x0 : fp2_t =>
  bindGen arbitrary (fun x1 : fp2_t =>
  bindGen arbitrary (fun x2 : fp2_t =>
  returnGen (x0,x1,x2)))).
Instance gen_fp6_t : Gen (fp6_t) := Build_Gen fp6_t g_fp6_t.


Notation "'fp12_t'" := ((fp6_t × fp6_t)) : hacspec_scope.
Instance show_fp12_t : Show (fp12_t) :=
Build_Show fp12_t (fun x =>
  let (x, x0) := x in
  (("(") ++ ((show x) ++ ((",") ++ ((show x0) ++ (")"))))))%string.
Definition g_fp12_t : G (fp12_t) :=
bindGen arbitrary (fun x0 : fp6_t =>
  bindGen arbitrary (fun x1 : fp6_t =>
  returnGen (x0,x1))).
Instance gen_fp12_t : Gen (fp12_t) := Build_Gen fp12_t g_fp12_t.


Definition fp2fromfp (n_0 : fp_t) : fp2_t :=
  (n_0, nat_mod_zero ).

Definition fp2zero  : fp2_t :=
  fp2fromfp (nat_mod_zero ).

Theorem ensures_fp2zero : forall result_1 ,
 @fp2zero  = result_1 ->
 result_1 = (nat_mod_zero , nat_mod_zero ).
 Proof. Admitted.

Definition fp2neg (n_2 : fp2_t) : fp2_t :=
  let '(n1_3, n2_4) :=
    n_2 in 
  ((nat_mod_zero ) -% (n1_3), (nat_mod_zero ) -% (n2_4)).

Definition fp2add (n_5 : fp2_t) (m_6 : fp2_t) : fp2_t :=
  let '(n1_7, n2_8) :=
    n_5 in 
  let '(m1_9, m2_10) :=
    m_6 in 
  ((n1_7) +% (m1_9), (n2_8) +% (m2_10)).

Definition fp2sub (n_11 : fp2_t) (m_12 : fp2_t) : fp2_t :=
  fp2add (n_11) (fp2neg (m_12)).

Definition fp2mul (n_13 : fp2_t) (m_14 : fp2_t) : fp2_t :=
  let '(n1_15, n2_16) :=
    n_13 in 
  let '(m1_17, m2_18) :=
    m_14 in 
  let x1_19 : fp_t :=
    ((n1_15) *% (m1_17)) -% ((n2_16) *% (m2_18)) in 
  let x2_20 : fp_t :=
    ((n1_15) *% (m2_18)) +% ((n2_16) *% (m1_17)) in 
  (x1_19, x2_20).

Definition fp2inv (n_21 : fp2_t) : fp2_t :=
  let '(n1_22, n2_23) :=
    n_21 in 
  let t0_24 : fp_t :=
    ((n1_22) *% (n1_22)) +% ((n2_23) *% (n2_23)) in 
  let t1_25 : fp_t :=
    nat_mod_inv (t0_24) in 
  let x1_26 : fp_t :=
    (n1_22) *% (t1_25) in 
  let x2_27 : fp_t :=
    (nat_mod_zero ) -% ((n2_23) *% (t1_25)) in 
  (x1_26, x2_27).

Definition fp2conjugate (n_28 : fp2_t) : fp2_t :=
  let '(n1_29, n2_30) :=
    n_28 in 
  (n1_29, (nat_mod_zero ) -% (n2_30)).

Definition fp6fromfp2 (n_31 : fp2_t) : fp6_t :=
  (n_31, fp2zero , fp2zero ).

Definition fp6zero  : fp6_t :=
  fp6fromfp2 (fp2zero ).

Definition fp6neg (n_32 : fp6_t) : fp6_t :=
  let '(n1_33, n2_34, n3_35) :=
    n_32 in 
  (
    fp2sub (fp2zero ) (n1_33),
    fp2sub (fp2zero ) (n2_34),
    fp2sub (fp2zero ) (n3_35)
  ).

Definition fp6add (n_36 : fp6_t) (m_37 : fp6_t) : fp6_t :=
  let '(n1_38, n2_39, n3_40) :=
    n_36 in 
  let '(m1_41, m2_42, m3_43) :=
    m_37 in 
  (fp2add (n1_38) (m1_41), fp2add (n2_39) (m2_42), fp2add (n3_40) (m3_43)).

Definition fp6sub (n_44 : fp6_t) (m_45 : fp6_t) : fp6_t :=
  fp6add (n_44) (fp6neg (m_45)).

Definition fp6mul (n_46 : fp6_t) (m_47 : fp6_t) : fp6_t :=
  let '(n1_48, n2_49, n3_50) :=
    n_46 in 
  let '(m1_51, m2_52, m3_53) :=
    m_47 in 
  let eps_54 : (fp_t × fp_t) :=
    (nat_mod_one , nat_mod_one ) in 
  let t1_55 : (fp_t × fp_t) :=
    fp2mul (n1_48) (m1_51) in 
  let t2_56 : (fp_t × fp_t) :=
    fp2mul (n2_49) (m2_52) in 
  let t3_57 : (fp_t × fp_t) :=
    fp2mul (n3_50) (m3_53) in 
  let t4_58 : (fp_t × fp_t) :=
    fp2mul (fp2add (n2_49) (n3_50)) (fp2add (m2_52) (m3_53)) in 
  let t5_59 : (fp_t × fp_t) :=
    fp2sub (fp2sub (t4_58) (t2_56)) (t3_57) in 
  let x_60 : (fp_t × fp_t) :=
    fp2add (fp2mul (t5_59) (eps_54)) (t1_55) in 
  let t4_61 : (fp_t × fp_t) :=
    fp2mul (fp2add (n1_48) (n2_49)) (fp2add (m1_51) (m2_52)) in 
  let t5_62 : (fp_t × fp_t) :=
    fp2sub (fp2sub (t4_61) (t1_55)) (t2_56) in 
  let y_63 : (fp_t × fp_t) :=
    fp2add (t5_62) (fp2mul (eps_54) (t3_57)) in 
  let t4_64 : (fp_t × fp_t) :=
    fp2mul (fp2add (n1_48) (n3_50)) (fp2add (m1_51) (m3_53)) in 
  let t5_65 : (fp_t × fp_t) :=
    fp2sub (fp2sub (t4_64) (t1_55)) (t3_57) in 
  let z_66 : (fp_t × fp_t) :=
    fp2add (t5_65) (t2_56) in 
  (x_60, y_63, z_66).

Definition fp6inv (n_67 : fp6_t) : fp6_t :=
  let '(n1_68, n2_69, n3_70) :=
    n_67 in 
  let eps_71 : (fp_t × fp_t) :=
    (nat_mod_one , nat_mod_one ) in 
  let t1_72 : (fp_t × fp_t) :=
    fp2mul (n1_68) (n1_68) in 
  let t2_73 : (fp_t × fp_t) :=
    fp2mul (n2_69) (n2_69) in 
  let t3_74 : (fp_t × fp_t) :=
    fp2mul (n3_70) (n3_70) in 
  let t4_75 : (fp_t × fp_t) :=
    fp2mul (n1_68) (n2_69) in 
  let t5_76 : (fp_t × fp_t) :=
    fp2mul (n1_68) (n3_70) in 
  let t6_77 : (fp_t × fp_t) :=
    fp2mul (n2_69) (n3_70) in 
  let x0_78 : (fp_t × fp_t) :=
    fp2sub (t1_72) (fp2mul (eps_71) (t6_77)) in 
  let y0_79 : (fp_t × fp_t) :=
    fp2sub (fp2mul (eps_71) (t3_74)) (t4_75) in 
  let z0_80 : (fp_t × fp_t) :=
    fp2sub (t2_73) (t5_76) in 
  let t0_81 : (fp_t × fp_t) :=
    fp2mul (n1_68) (x0_78) in 
  let t0_82 : (fp_t × fp_t) :=
    fp2add (t0_81) (fp2mul (eps_71) (fp2mul (n3_70) (y0_79))) in 
  let t0_83 : (fp_t × fp_t) :=
    fp2add (t0_82) (fp2mul (eps_71) (fp2mul (n2_69) (z0_80))) in 
  let t0_84 : (fp_t × fp_t) :=
    fp2inv (t0_83) in 
  let x_85 : (fp_t × fp_t) :=
    fp2mul (x0_78) (t0_84) in 
  let y_86 : (fp_t × fp_t) :=
    fp2mul (y0_79) (t0_84) in 
  let z_87 : (fp_t × fp_t) :=
    fp2mul (z0_80) (t0_84) in 
  (x_85, y_86, z_87).

Definition fp12fromfp6 (n_88 : fp6_t) : fp12_t :=
  (n_88, fp6zero ).

Definition fp12neg (n_89 : fp12_t) : fp12_t :=
  let '(n1_90, n2_91) :=
    n_89 in 
  (fp6sub (fp6zero ) (n1_90), fp6sub (fp6zero ) (n2_91)).

Definition fp12add (n_92 : fp12_t) (m_93 : fp12_t) : fp12_t :=
  let '(n1_94, n2_95) :=
    n_92 in 
  let '(m1_96, m2_97) :=
    m_93 in 
  (fp6add (n1_94) (m1_96), fp6add (n2_95) (m2_97)).

Definition fp12sub (n_98 : fp12_t) (m_99 : fp12_t) : fp12_t :=
  fp12add (n_98) (fp12neg (m_99)).

Definition fp12mul (n_100 : fp12_t) (m_101 : fp12_t) : fp12_t :=
  let '(n1_102, n2_103) :=
    n_100 in 
  let '(m1_104, m2_105) :=
    m_101 in 
  let gamma_106 : (fp2_t × fp2_t × fp2_t) :=
    (fp2zero , fp2fromfp (nat_mod_one ), fp2zero ) in 
  let t1_107 : (fp2_t × fp2_t × fp2_t) :=
    fp6mul (n1_102) (m1_104) in 
  let t2_108 : (fp2_t × fp2_t × fp2_t) :=
    fp6mul (n2_103) (m2_105) in 
  let x_109 : (fp2_t × fp2_t × fp2_t) :=
    fp6add (t1_107) (fp6mul (t2_108) (gamma_106)) in 
  let y_110 : (fp2_t × fp2_t × fp2_t) :=
    fp6mul (fp6add (n1_102) (n2_103)) (fp6add (m1_104) (m2_105)) in 
  let y_111 : (fp2_t × fp2_t × fp2_t) :=
    fp6sub (fp6sub (y_110) (t1_107)) (t2_108) in 
  (x_109, y_111).

Definition fp12inv (n_112 : fp12_t) : fp12_t :=
  let '(n1_113, n2_114) :=
    n_112 in 
  let gamma_115 : (fp2_t × fp2_t × fp2_t) :=
    (fp2zero , fp2fromfp (nat_mod_one ), fp2zero ) in 
  let t1_116 : (fp2_t × fp2_t × fp2_t) :=
    fp6mul (n1_113) (n1_113) in 
  let t2_117 : (fp2_t × fp2_t × fp2_t) :=
    fp6mul (n2_114) (n2_114) in 
  let t1_118 : (fp2_t × fp2_t × fp2_t) :=
    fp6sub (t1_116) (fp6mul (gamma_115) (t2_117)) in 
  let t2_119 : (fp2_t × fp2_t × fp2_t) :=
    fp6inv (t1_118) in 
  let x_120 : (fp2_t × fp2_t × fp2_t) :=
    fp6mul (n1_113) (t2_119) in 
  let y_121 : (fp2_t × fp2_t × fp2_t) :=
    fp6neg (fp6mul (n2_114) (t2_119)) in 
  (x_120, y_121).

Definition fp12exp (n_122 : fp12_t) (k_123 : scalar_t) : fp12_t :=
  let c_124 : (fp6_t × fp6_t) :=
    fp12fromfp6 (fp6fromfp2 (fp2fromfp (nat_mod_one ))) in 
  let c_124 :=
    foldi (usize 0) (usize 256) (fun i_125 c_124 =>
      let c_124 :=
        fp12mul (c_124) (c_124) in 
      let '(c_124) :=
        if nat_mod_bit (k_123) ((usize 255) - (i_125)):bool then (let c_124 :=
            fp12mul (c_124) (n_122) in 
          (c_124)) else ((c_124)) in 
      (c_124))
    c_124 in 
  c_124.

Definition fp12conjugate (n_126 : fp12_t) : fp12_t :=
  let '(n1_127, n2_128) :=
    n_126 in 
  (n1_127, fp6neg (n2_128)).

Definition fp12zero  : fp12_t :=
  fp12fromfp6 (fp6zero ).

Definition g1add_a (p_129 : g1_t) (q_130 : g1_t) : g1_t :=
  let '(x1_131, y1_132, _) :=
    p_129 in 
  let '(x2_133, y2_134, _) :=
    q_130 in 
  let x_diff_135 : fp_t :=
    (x2_133) -% (x1_131) in 
  let y_diff_136 : fp_t :=
    (y2_134) -% (y1_132) in 
  let xovery_137 : fp_t :=
    (y_diff_136) *% (nat_mod_inv (x_diff_135)) in 
  let x3_138 : fp_t :=
    ((nat_mod_exp (xovery_137) (@repr WORDSIZE32 2)) -% (x1_131)) -% (
      x2_133) in 
  let y3_139 : fp_t :=
    ((xovery_137) *% ((x1_131) -% (x3_138))) -% (y1_132) in 
  (x3_138, y3_139, false).

Definition g1double_a (p_140 : g1_t) : g1_t :=
  let '(x1_141, y1_142, _) :=
    p_140 in 
  let x12_143 : fp_t :=
    nat_mod_exp (x1_141) (@repr WORDSIZE32 2) in 
  let xovery_144 : fp_t :=
    ((nat_mod_from_literal (
          0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab) (
          @repr WORDSIZE128 3) : fp_t) *% (x12_143)) *% (nat_mod_inv ((
          nat_mod_two ) *% (y1_142))) in 
  let x3_145 : fp_t :=
    (nat_mod_exp (xovery_144) (@repr WORDSIZE32 2)) -% ((nat_mod_two ) *% (
        x1_141)) in 
  let y3_146 : fp_t :=
    ((xovery_144) *% ((x1_141) -% (x3_145))) -% (y1_142) in 
  (x3_145, y3_146, false).

Definition g1double (p_147 : g1_t) : g1_t :=
  let '(x1_148, y1_149, inf1_150) :=
    p_147 in 
  (if (((y1_149) !=.? (nat_mod_zero )) && (negb (inf1_150))):bool then (
      g1double_a (p_147)) else ((nat_mod_zero , nat_mod_zero , true))).

Definition g1add (p_151 : g1_t) (q_152 : g1_t) : g1_t :=
  let '(x1_153, y1_154, inf1_155) :=
    p_151 in 
  let '(x2_156, y2_157, inf2_158) :=
    q_152 in 
  (if (inf1_155):bool then (q_152) else ((if (inf2_158):bool then (p_151) else (
          (if ((p_151) =.? (q_152)):bool then (g1double (p_151)) else ((if (
                  negb (((x1_153) =.? (x2_156)) && ((y1_154) =.? ((
                          nat_mod_zero ) -% (y2_157))))):bool then (g1add_a (
                    p_151) (q_152)) else ((nat_mod_zero , nat_mod_zero , true
                  ))))))))).

Definition g1mul (m_159 : scalar_t) (p_160 : g1_t) : g1_t :=
  let t_161 : (fp_t × fp_t × bool) :=
    (nat_mod_zero , nat_mod_zero , true) in 
  let t_161 :=
    foldi (usize 0) (usize 256) (fun i_162 t_161 =>
      let t_161 :=
        g1double (t_161) in 
      let '(t_161) :=
        if nat_mod_bit (m_159) ((usize 255) - (i_162)):bool then (let t_161 :=
            g1add (t_161) (p_160) in 
          (t_161)) else ((t_161)) in 
      (t_161))
    t_161 in 
  t_161.

Definition g1neg (p_163 : g1_t) : g1_t :=
  let '(x_164, y_165, inf_166) :=
    p_163 in 
  (x_164, (nat_mod_zero ) -% (y_165), inf_166).

Definition g2add_a (p_167 : g2_t) (q_168 : g2_t) : g2_t :=
  let '(x1_169, y1_170, _) :=
    p_167 in 
  let '(x2_171, y2_172, _) :=
    q_168 in 
  let x_diff_173 : (fp_t × fp_t) :=
    fp2sub (x2_171) (x1_169) in 
  let y_diff_174 : (fp_t × fp_t) :=
    fp2sub (y2_172) (y1_170) in 
  let xovery_175 : (fp_t × fp_t) :=
    fp2mul (y_diff_174) (fp2inv (x_diff_173)) in 
  let t1_176 : (fp_t × fp_t) :=
    fp2mul (xovery_175) (xovery_175) in 
  let t2_177 : (fp_t × fp_t) :=
    fp2sub (t1_176) (x1_169) in 
  let x3_178 : (fp_t × fp_t) :=
    fp2sub (t2_177) (x2_171) in 
  let t1_179 : (fp_t × fp_t) :=
    fp2sub (x1_169) (x3_178) in 
  let t2_180 : (fp_t × fp_t) :=
    fp2mul (xovery_175) (t1_179) in 
  let y3_181 : (fp_t × fp_t) :=
    fp2sub (t2_180) (y1_170) in 
  (x3_178, y3_181, false).

Definition g2double_a (p_182 : g2_t) : g2_t :=
  let '(x1_183, y1_184, _) :=
    p_182 in 
  let x12_185 : (fp_t × fp_t) :=
    fp2mul (x1_183) (x1_183) in 
  let t1_186 : (fp_t × fp_t) :=
    fp2mul (fp2fromfp (nat_mod_from_literal (
          0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab) (
          @repr WORDSIZE128 3) : fp_t)) (x12_185) in 
  let t2_187 : (fp_t × fp_t) :=
    fp2inv (fp2mul (fp2fromfp (nat_mod_two )) (y1_184)) in 
  let xovery_188 : (fp_t × fp_t) :=
    fp2mul (t1_186) (t2_187) in 
  let t1_189 : (fp_t × fp_t) :=
    fp2mul (xovery_188) (xovery_188) in 
  let t2_190 : (fp_t × fp_t) :=
    fp2mul (fp2fromfp (nat_mod_two )) (x1_183) in 
  let x3_191 : (fp_t × fp_t) :=
    fp2sub (t1_189) (t2_190) in 
  let t1_192 : (fp_t × fp_t) :=
    fp2sub (x1_183) (x3_191) in 
  let t2_193 : (fp_t × fp_t) :=
    fp2mul (xovery_188) (t1_192) in 
  let y3_194 : (fp_t × fp_t) :=
    fp2sub (t2_193) (y1_184) in 
  (x3_191, y3_194, false).

Definition g2double (p_195 : g2_t) : g2_t :=
  let '(x1_196, y1_197, inf1_198) :=
    p_195 in 
  (if (((y1_197) !=.? (fp2zero )) && (negb (inf1_198))):bool then (g2double_a (
        p_195)) else ((fp2zero , fp2zero , true))).

Definition g2add (p_199 : g2_t) (q_200 : g2_t) : g2_t :=
  let '(x1_201, y1_202, inf1_203) :=
    p_199 in 
  let '(x2_204, y2_205, inf2_206) :=
    q_200 in 
  (if (inf1_203):bool then (q_200) else ((if (inf2_206):bool then (p_199) else (
          (if ((p_199) =.? (q_200)):bool then (g2double (p_199)) else ((if (
                  negb (((x1_201) =.? (x2_204)) && ((y1_202) =.? (fp2neg (
                          y2_205))))):bool then (g2add_a (p_199) (q_200)) else (
                  (fp2zero , fp2zero , true))))))))).

Definition g2mul (m_207 : scalar_t) (p_208 : g2_t) : g2_t :=
  let t_209 : (fp2_t × fp2_t × bool) :=
    (fp2zero , fp2zero , true) in 
  let t_209 :=
    foldi (usize 0) (usize 256) (fun i_210 t_209 =>
      let t_209 :=
        g2double (t_209) in 
      let '(t_209) :=
        if nat_mod_bit (m_207) ((usize 255) - (i_210)):bool then (let t_209 :=
            g2add (t_209) (p_208) in 
          (t_209)) else ((t_209)) in 
      (t_209))
    t_209 in 
  t_209.

Definition g2neg (p_211 : g2_t) : g2_t :=
  let '(x_212, y_213, inf_214) :=
    p_211 in 
  (x_212, fp2neg (y_213), inf_214).

Definition twist (p_215 : g1_t) : (fp12_t × fp12_t) :=
  let '(p0_216, p1_217, _) :=
    p_215 in 
  let x_218 : ((fp2_t × fp2_t × fp2_t) × fp6_t) :=
    ((fp2zero , fp2fromfp (p0_216), fp2zero ), fp6zero ) in 
  let y_219 : (fp6_t × (fp2_t × fp2_t × fp2_t)) :=
    (fp6zero , (fp2zero , fp2fromfp (p1_217), fp2zero )) in 
  (x_218, y_219).

Definition line_double_p (r_220 : g2_t) (p_221 : g1_t) : fp12_t :=
  let '(r0_222, r1_223, _) :=
    r_220 in 
  let a_224 : (fp_t × fp_t) :=
    fp2mul (fp2fromfp (nat_mod_from_literal (
          0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab) (
          @repr WORDSIZE128 3) : fp_t)) (fp2mul (r0_222) (r0_222)) in 
  let a_225 : (fp_t × fp_t) :=
    fp2mul (a_224) (fp2inv (fp2mul (fp2fromfp (nat_mod_two )) (r1_223))) in 
  let b_226 : (fp_t × fp_t) :=
    fp2sub (r1_223) (fp2mul (a_225) (r0_222)) in 
  let a_227 : (fp6_t × fp6_t) :=
    fp12fromfp6 (fp6fromfp2 (a_225)) in 
  let b_228 : (fp6_t × fp6_t) :=
    fp12fromfp6 (fp6fromfp2 (b_226)) in 
  let '(x_229, y_230) :=
    twist (p_221) in 
  fp12neg (fp12sub (fp12sub (y_230) (fp12mul (a_227) (x_229))) (b_228)).

Definition line_add_p (r_231 : g2_t) (q_232 : g2_t) (p_233 : g1_t) : fp12_t :=
  let '(r0_234, r1_235, _) :=
    r_231 in 
  let '(q0_236, q1_237, _) :=
    q_232 in 
  let a_238 : (fp_t × fp_t) :=
    fp2mul (fp2sub (q1_237) (r1_235)) (fp2inv (fp2sub (q0_236) (r0_234))) in 
  let b_239 : (fp_t × fp_t) :=
    fp2sub (r1_235) (fp2mul (a_238) (r0_234)) in 
  let a_240 : (fp6_t × fp6_t) :=
    fp12fromfp6 (fp6fromfp2 (a_238)) in 
  let b_241 : (fp6_t × fp6_t) :=
    fp12fromfp6 (fp6fromfp2 (b_239)) in 
  let '(x_242, y_243) :=
    twist (p_233) in 
  fp12neg (fp12sub (fp12sub (y_243) (fp12mul (a_240) (x_242))) (b_241)).

Definition frobenius (f_244 : fp12_t) : fp12_t :=
  let '((g0_245, g1_246, g2_247), (h0_248, h1_249, h2_250)) :=
    f_244 in 
  let t1_251 : (fp_t × fp_t) :=
    fp2conjugate (g0_245) in 
  let t2_252 : (fp_t × fp_t) :=
    fp2conjugate (h0_248) in 
  let t3_253 : (fp_t × fp_t) :=
    fp2conjugate (g1_246) in 
  let t4_254 : (fp_t × fp_t) :=
    fp2conjugate (h1_249) in 
  let t5_255 : (fp_t × fp_t) :=
    fp2conjugate (g2_247) in 
  let t6_256 : (fp_t × fp_t) :=
    fp2conjugate (h2_250) in 
  let c1_257 : array_fp_t :=
    array_from_list uint64 (let l :=
        [
          secret (@repr WORDSIZE64 10162220747404304312) : int64;
          secret (@repr WORDSIZE64 17761815663483519293) : int64;
          secret (@repr WORDSIZE64 8873291758750579140) : int64;
          secret (@repr WORDSIZE64 1141103941765652303) : int64;
          secret (@repr WORDSIZE64 13993175198059990303) : int64;
          secret (@repr WORDSIZE64 1802798568193066599) : int64
        ] in  l) in 
  let c1_258 : seq uint8 :=
    array_to_le_bytes (c1_257) in 
  let c1_259 : fp_t :=
    nat_mod_from_byte_seq_le (c1_258) : fp_t in 
  let c2_260 : array_fp_t :=
    array_from_list uint64 (let l :=
        [
          secret (@repr WORDSIZE64 3240210268673559283) : int64;
          secret (@repr WORDSIZE64 2895069921743240898) : int64;
          secret (@repr WORDSIZE64 17009126888523054175) : int64;
          secret (@repr WORDSIZE64 6098234018649060207) : int64;
          secret (@repr WORDSIZE64 9865672654120263608) : int64;
          secret (@repr WORDSIZE64 71000049454473266) : int64
        ] in  l) in 
  let c2_261 : seq uint8 :=
    array_to_le_bytes (c2_260) in 
  let c2_262 : fp_t :=
    nat_mod_from_byte_seq_le (c2_261) : fp_t in 
  let gamma11_263 : (fp_t × fp_t) :=
    (c1_259, c2_262) in 
  let gamma12_264 : (fp_t × fp_t) :=
    fp2mul (gamma11_263) (gamma11_263) in 
  let gamma13_265 : (fp_t × fp_t) :=
    fp2mul (gamma12_264) (gamma11_263) in 
  let gamma14_266 : (fp_t × fp_t) :=
    fp2mul (gamma13_265) (gamma11_263) in 
  let gamma15_267 : (fp_t × fp_t) :=
    fp2mul (gamma14_266) (gamma11_263) in 
  let t2_268 : (fp_t × fp_t) :=
    fp2mul (t2_252) (gamma11_263) in 
  let t3_269 : (fp_t × fp_t) :=
    fp2mul (t3_253) (gamma12_264) in 
  let t4_270 : (fp_t × fp_t) :=
    fp2mul (t4_254) (gamma13_265) in 
  let t5_271 : (fp_t × fp_t) :=
    fp2mul (t5_255) (gamma14_266) in 
  let t6_272 : (fp_t × fp_t) :=
    fp2mul (t6_256) (gamma15_267) in 
  ((t1_251, t3_269, t5_271), (t2_268, t4_270, t6_272)).

Definition final_exponentiation (f_273 : fp12_t) : fp12_t :=
  let fp6_274 : (fp6_t × fp6_t) :=
    fp12conjugate (f_273) in 
  let finv_275 : (fp6_t × fp6_t) :=
    fp12inv (f_273) in 
  let fp6_1_276 : (fp6_t × fp6_t) :=
    fp12mul (fp6_274) (finv_275) in 
  let fp8_277 : (fp6_t × fp6_t) :=
    frobenius (frobenius (fp6_1_276)) in 
  let f_278 : (fp6_t × fp6_t) :=
    fp12mul (fp8_277) (fp6_1_276) in 
  let u_279 : scalar_t :=
    nat_mod_from_literal (
      0x8000000000000000000000000000000000000000000000000000000000000000) (
      @repr WORDSIZE128 15132376222941642752) : scalar_t in 
  let u_half_279 : scalar_t :=
    nat_mod_from_literal (
      0x8000000000000000000000000000000000000000000000000000000000000000) (
      @repr WORDSIZE128 7566188111470821376) : scalar_t in 
  let t0_280 : (fp6_t × fp6_t) :=
    fp12mul (f_277) (f_277) in 
  let t1_281 : (fp6_t × fp6_t) :=
    fp12exp (t0_280) (u_278) in 
  let t1_282 : (fp6_t × fp6_t) :=
    fp12conjugate (t1_281) in 
  let t2_283 : (fp6_t × fp6_t) :=
    fp12exp (t1_282) (u_half_279) in 
  let t2_284 : (fp6_t × fp6_t) :=
    fp12conjugate (t2_283) in 
  let t3_285 : (fp6_t × fp6_t) :=
    fp12conjugate (f_277) in 
  let t1_286 : (fp6_t × fp6_t) :=
    fp12mul (t3_285) (t1_282) in 
  let t1_287 : (fp6_t × fp6_t) :=
    fp12conjugate (t1_286) in 
  let t1_288 : (fp6_t × fp6_t) :=
    fp12mul (t1_287) (t2_284) in 
  let t2_289 : (fp6_t × fp6_t) :=
    fp12exp (t1_288) (u_278) in 
  let t2_290 : (fp6_t × fp6_t) :=
    fp12conjugate (t2_289) in 
  let t3_291 : (fp6_t × fp6_t) :=
    fp12exp (t2_290) (u_278) in 
  let t3_292 : (fp6_t × fp6_t) :=
    fp12conjugate (t3_291) in 
  let t1_293 : (fp6_t × fp6_t) :=
    fp12conjugate (t1_288) in 
  let t3_294 : (fp6_t × fp6_t) :=
    fp12mul (t1_293) (t3_292) in 
  let t1_295 : (fp6_t × fp6_t) :=
    fp12conjugate (t1_293) in 
  let t1_296 : (fp6_t × fp6_t) :=
    frobenius (frobenius (frobenius (t1_295))) in 
  let t2_297 : (fp6_t × fp6_t) :=
    frobenius (frobenius (t2_290)) in 
  let t1_298 : (fp6_t × fp6_t) :=
    fp12mul (t1_296) (t2_297) in 
  let t2_299 : (fp6_t × fp6_t) :=
    fp12exp (t3_294) (u_278) in 
  let t2_300 : (fp6_t × fp6_t) :=
    fp12conjugate (t2_299) in 
  let t2_301 : (fp6_t × fp6_t) :=
    fp12mul (t2_300) (t0_280) in 
  let t2_302 : (fp6_t × fp6_t) :=
    fp12mul (t2_301) (f_277) in 
  let t1_303 : (fp6_t × fp6_t) :=
    fp12mul (t1_298) (t2_302) in 
  let t2_304 : (fp6_t × fp6_t) :=
    frobenius (t3_294) in 
  let t1_305 : (fp6_t × fp6_t) :=
    fp12mul (t1_303) (t2_304) in 
  t1_305.

Definition pairing (p_306 : g1_t) (q_307 : g2_t) : fp12_t :=
  let t_308 : scalar_t :=
    nat_mod_from_literal (
      0x8000000000000000000000000000000000000000000000000000000000000000) (
      @repr WORDSIZE128 15132376222941642752) : scalar_t in 
  let r_309 : (fp2_t × fp2_t × bool) :=
    q_307 in 
  let f_310 : (fp6_t × fp6_t) :=
    fp12fromfp6 (fp6fromfp2 (fp2fromfp (nat_mod_one ))) in 
  let '(r_309, f_310) :=
    foldi (usize 1) (usize 64) (fun i_311 '(r_309, f_310) =>
      let lrr_312 : (fp6_t × fp6_t) :=
        line_double_p (r_309) (p_306) in 
      let r_309 :=
        g2double (r_309) in 
      let f_310 :=
        fp12mul (fp12mul (f_310) (f_310)) (lrr_312) in 
      let '(r_309, f_310) :=
        if nat_mod_bit (t_308) (((usize 64) - (i_311)) - (usize 1)):bool then (
          let lrq_313 : (fp6_t × fp6_t) :=
            line_add_p (r_309) (q_307) (p_306) in 
          let r_309 :=
            g2add (r_309) (q_307) in 
          let f_310 :=
            fp12mul (f_310) (lrq_313) in 
          (r_309, f_310)) else ((r_309, f_310)) in 
      (r_309, f_310))
    (r_309, f_310) in 
  final_exponentiation (fp12conjugate (f_310)).

Definition test_fp2_prop_add_neg (a_314 : fp2_t) : bool :=
  let b_315 : (fp_t × fp_t) :=
    fp2neg (a_314) in 
  (fp2fromfp (nat_mod_zero )) =.? (fp2add (a_314) (b_315)).
QuickChick (forAll g_fp2_t (fun a_314 : fp2_t =>test_fp2_prop_add_neg a_314)).


Definition test_fp2_prop_mul_inv (a_316 : fp2_t) : bool :=
  let b_317 : (fp_t × fp_t) :=
    fp2inv (a_316) in 
  (fp2fromfp (nat_mod_one )) =.? (fp2mul (a_316) (b_317)).
QuickChick (forAll g_fp2_t (fun a_316 : fp2_t =>test_fp2_prop_mul_inv a_316)).


Definition test_extraction_issue  : bool :=
  let b_318 : (fp_t × fp_t) :=
    fp2inv ((nat_mod_one , nat_mod_one )) in 
  (fp2fromfp (nat_mod_one )) =.? (fp2mul ((nat_mod_one , nat_mod_one )) (
      b_318)).
QuickChick (test_extraction_issue).


Definition test_fp6_prop_mul_inv (a_319 : fp6_t) : bool :=
  let b_320 : (fp2_t × fp2_t × fp2_t) :=
    fp6inv (a_319) in 
  (fp6fromfp2 (fp2fromfp (nat_mod_one ))) =.? (fp6mul (a_319) (b_320)).
QuickChick (forAll g_fp6_t (fun a_319 : fp6_t =>test_fp6_prop_mul_inv a_319)).


Definition test_fp6_prop_add_neg (a_321 : fp6_t) : bool :=
  let b_322 : (fp2_t × fp2_t × fp2_t) :=
    fp6neg (a_321) in 
  (fp6fromfp2 (fp2fromfp (nat_mod_zero ))) =.? (fp6add (a_321) (b_322)).
QuickChick (forAll g_fp6_t (fun a_321 : fp6_t =>test_fp6_prop_add_neg a_321)).


Definition test_fp12_prop_add_neg (a_323 : fp12_t) : bool :=
  let b_324 : (fp6_t × fp6_t) :=
    fp12neg (a_323) in 
  (fp12fromfp6 (fp6fromfp2 (fp2fromfp (nat_mod_zero )))) =.? (fp12add (a_323) (
      b_324)).
QuickChick (
  forAll g_fp12_t (fun a_323 : fp12_t =>test_fp12_prop_add_neg a_323)).


Definition test_fp12_prop_mul_inv (a_325 : fp12_t) : bool :=
  let b_326 : (fp6_t × fp6_t) :=
    fp12inv (a_325) in 
  (fp12fromfp6 (fp6fromfp2 (fp2fromfp (nat_mod_one )))) =.? (fp12mul (a_325) (
      b_326)).
QuickChick (
  forAll g_fp12_t (fun a_325 : fp12_t =>test_fp12_prop_mul_inv a_325)).


