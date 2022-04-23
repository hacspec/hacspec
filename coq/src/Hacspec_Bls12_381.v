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

Definition fp2neg (n_1 : fp2_t) : fp2_t :=
  let '(n1_2, n2_3) :=
    n_1 in 
  ((nat_mod_zero ) -% (n1_2), (nat_mod_zero ) -% (n2_3)).

Definition fp2add (n_4 : fp2_t) (m_5 : fp2_t) : fp2_t :=
  let '(n1_6, n2_7) :=
    n_4 in 
  let '(m1_8, m2_9) :=
    m_5 in 
  ((n1_6) +% (m1_8), (n2_7) +% (m2_9)).

Definition fp2sub (n_10 : fp2_t) (m_11 : fp2_t) : fp2_t :=
  fp2add (n_10) (fp2neg (m_11)).

Definition fp2mul (n_12 : fp2_t) (m_13 : fp2_t) : fp2_t :=
  let '(n1_14, n2_15) :=
    n_12 in 
  let '(m1_16, m2_17) :=
    m_13 in 
  let x1_18 : fp_t :=
    ((n1_14) *% (m1_16)) -% ((n2_15) *% (m2_17)) in 
  let x2_19 : fp_t :=
    ((n1_14) *% (m2_17)) +% ((n2_15) *% (m1_16)) in 
  (x1_18, x2_19).

Definition fp2inv (n_20 : fp2_t) : fp2_t :=
  let '(n1_21, n2_22) :=
    n_20 in 
  let t0_23 : fp_t :=
    ((n1_21) *% (n1_21)) +% ((n2_22) *% (n2_22)) in 
  let t1_24 : fp_t :=
    nat_mod_inv (t0_23) in 
  let x1_25 : fp_t :=
    (n1_21) *% (t1_24) in 
  let x2_26 : fp_t :=
    (nat_mod_zero ) -% ((n2_22) *% (t1_24)) in 
  (x1_25, x2_26).

Definition fp2conjugate (n_27 : fp2_t) : fp2_t :=
  let '(n1_28, n2_29) :=
    n_27 in 
  (n1_28, (nat_mod_zero ) -% (n2_29)).

Definition fp6fromfp2 (n_30 : fp2_t) : fp6_t :=
  (n_30, fp2zero , fp2zero ).

Definition fp6zero  : fp6_t :=
  fp6fromfp2 (fp2zero ).

Definition fp6neg (n_31 : fp6_t) : fp6_t :=
  let '(n1_32, n2_33, n3_34) :=
    n_31 in 
  (
    fp2sub (fp2zero ) (n1_32),
    fp2sub (fp2zero ) (n2_33),
    fp2sub (fp2zero ) (n3_34)
  ).

Definition fp6add (n_35 : fp6_t) (m_36 : fp6_t) : fp6_t :=
  let '(n1_37, n2_38, n3_39) :=
    n_35 in 
  let '(m1_40, m2_41, m3_42) :=
    m_36 in 
  (fp2add (n1_37) (m1_40), fp2add (n2_38) (m2_41), fp2add (n3_39) (m3_42)).

Definition fp6sub (n_43 : fp6_t) (m_44 : fp6_t) : fp6_t :=
  fp6add (n_43) (fp6neg (m_44)).

Definition fp6mul (n_45 : fp6_t) (m_46 : fp6_t) : fp6_t :=
  let '(n1_47, n2_48, n3_49) :=
    n_45 in 
  let '(m1_50, m2_51, m3_52) :=
    m_46 in 
  let eps_53 : (fp_t × fp_t) :=
    (nat_mod_one , nat_mod_one ) in 
  let t1_54 : (fp_t × fp_t) :=
    fp2mul (n1_47) (m1_50) in 
  let t2_55 : (fp_t × fp_t) :=
    fp2mul (n2_48) (m2_51) in 
  let t3_56 : (fp_t × fp_t) :=
    fp2mul (n3_49) (m3_52) in 
  let t4_57 : (fp_t × fp_t) :=
    fp2mul (fp2add (n2_48) (n3_49)) (fp2add (m2_51) (m3_52)) in 
  let t5_58 : (fp_t × fp_t) :=
    fp2sub (fp2sub (t4_57) (t2_55)) (t3_56) in 
  let x_59 : (fp_t × fp_t) :=
    fp2add (fp2mul (t5_58) (eps_53)) (t1_54) in 
  let t4_60 : (fp_t × fp_t) :=
    fp2mul (fp2add (n1_47) (n2_48)) (fp2add (m1_50) (m2_51)) in 
  let t5_61 : (fp_t × fp_t) :=
    fp2sub (fp2sub (t4_60) (t1_54)) (t2_55) in 
  let y_62 : (fp_t × fp_t) :=
    fp2add (t5_61) (fp2mul (eps_53) (t3_56)) in 
  let t4_63 : (fp_t × fp_t) :=
    fp2mul (fp2add (n1_47) (n3_49)) (fp2add (m1_50) (m3_52)) in 
  let t5_64 : (fp_t × fp_t) :=
    fp2sub (fp2sub (t4_63) (t1_54)) (t3_56) in 
  let z_65 : (fp_t × fp_t) :=
    fp2add (t5_64) (t2_55) in 
  (x_59, y_62, z_65).

Definition fp6inv (n_66 : fp6_t) : fp6_t :=
  let '(n1_67, n2_68, n3_69) :=
    n_66 in 
  let eps_70 : (fp_t × fp_t) :=
    (nat_mod_one , nat_mod_one ) in 
  let t1_71 : (fp_t × fp_t) :=
    fp2mul (n1_67) (n1_67) in 
  let t2_72 : (fp_t × fp_t) :=
    fp2mul (n2_68) (n2_68) in 
  let t3_73 : (fp_t × fp_t) :=
    fp2mul (n3_69) (n3_69) in 
  let t4_74 : (fp_t × fp_t) :=
    fp2mul (n1_67) (n2_68) in 
  let t5_75 : (fp_t × fp_t) :=
    fp2mul (n1_67) (n3_69) in 
  let t6_76 : (fp_t × fp_t) :=
    fp2mul (n2_68) (n3_69) in 
  let x0_77 : (fp_t × fp_t) :=
    fp2sub (t1_71) (fp2mul (eps_70) (t6_76)) in 
  let y0_78 : (fp_t × fp_t) :=
    fp2sub (fp2mul (eps_70) (t3_73)) (t4_74) in 
  let z0_79 : (fp_t × fp_t) :=
    fp2sub (t2_72) (t5_75) in 
  let t0_80 : (fp_t × fp_t) :=
    fp2mul (n1_67) (x0_77) in 
  let t0_81 : (fp_t × fp_t) :=
    fp2add (t0_80) (fp2mul (eps_70) (fp2mul (n3_69) (y0_78))) in 
  let t0_82 : (fp_t × fp_t) :=
    fp2add (t0_81) (fp2mul (eps_70) (fp2mul (n2_68) (z0_79))) in 
  let t0_83 : (fp_t × fp_t) :=
    fp2inv (t0_82) in 
  let x_84 : (fp_t × fp_t) :=
    fp2mul (x0_77) (t0_83) in 
  let y_85 : (fp_t × fp_t) :=
    fp2mul (y0_78) (t0_83) in 
  let z_86 : (fp_t × fp_t) :=
    fp2mul (z0_79) (t0_83) in 
  (x_84, y_85, z_86).

Definition fp12fromfp6 (n_87 : fp6_t) : fp12_t :=
  (n_87, fp6zero ).

Definition fp12neg (n_88 : fp12_t) : fp12_t :=
  let '(n1_89, n2_90) :=
    n_88 in 
  (fp6sub (fp6zero ) (n1_89), fp6sub (fp6zero ) (n2_90)).

Definition fp12add (n_91 : fp12_t) (m_92 : fp12_t) : fp12_t :=
  let '(n1_93, n2_94) :=
    n_91 in 
  let '(m1_95, m2_96) :=
    m_92 in 
  (fp6add (n1_93) (m1_95), fp6add (n2_94) (m2_96)).

Definition fp12sub (n_97 : fp12_t) (m_98 : fp12_t) : fp12_t :=
  fp12add (n_97) (fp12neg (m_98)).

Definition fp12mul (n_99 : fp12_t) (m_100 : fp12_t) : fp12_t :=
  let '(n1_101, n2_102) :=
    n_99 in 
  let '(m1_103, m2_104) :=
    m_100 in 
  let gamma_105 : (fp2_t × fp2_t × fp2_t) :=
    (fp2zero , fp2fromfp (nat_mod_one ), fp2zero ) in 
  let t1_106 : (fp2_t × fp2_t × fp2_t) :=
    fp6mul (n1_101) (m1_103) in 
  let t2_107 : (fp2_t × fp2_t × fp2_t) :=
    fp6mul (n2_102) (m2_104) in 
  let x_108 : (fp2_t × fp2_t × fp2_t) :=
    fp6add (t1_106) (fp6mul (t2_107) (gamma_105)) in 
  let y_109 : (fp2_t × fp2_t × fp2_t) :=
    fp6mul (fp6add (n1_101) (n2_102)) (fp6add (m1_103) (m2_104)) in 
  let y_110 : (fp2_t × fp2_t × fp2_t) :=
    fp6sub (fp6sub (y_109) (t1_106)) (t2_107) in 
  (x_108, y_110).

Definition fp12inv (n_111 : fp12_t) : fp12_t :=
  let '(n1_112, n2_113) :=
    n_111 in 
  let gamma_114 : (fp2_t × fp2_t × fp2_t) :=
    (fp2zero , fp2fromfp (nat_mod_one ), fp2zero ) in 
  let t1_115 : (fp2_t × fp2_t × fp2_t) :=
    fp6mul (n1_112) (n1_112) in 
  let t2_116 : (fp2_t × fp2_t × fp2_t) :=
    fp6mul (n2_113) (n2_113) in 
  let t1_117 : (fp2_t × fp2_t × fp2_t) :=
    fp6sub (t1_115) (fp6mul (gamma_114) (t2_116)) in 
  let t2_118 : (fp2_t × fp2_t × fp2_t) :=
    fp6inv (t1_117) in 
  let x_119 : (fp2_t × fp2_t × fp2_t) :=
    fp6mul (n1_112) (t2_118) in 
  let y_120 : (fp2_t × fp2_t × fp2_t) :=
    fp6neg (fp6mul (n2_113) (t2_118)) in 
  (x_119, y_120).

Definition fp12exp (n_121 : fp12_t) (k_122 : scalar_t) : fp12_t :=
  let c_123 : (fp6_t × fp6_t) :=
    fp12fromfp6 (fp6fromfp2 (fp2fromfp (nat_mod_one ))) in 
  let c_123 :=
    foldi (usize 0) (usize 256) (fun i_124 c_123 =>
      let c_123 :=
        fp12mul (c_123) (c_123) in 
      let '(c_123) :=
        if nat_mod_bit (k_122) ((usize 255) - (i_124)):bool then (let c_123 :=
            fp12mul (c_123) (n_121) in 
          (c_123)) else ((c_123)) in 
      (c_123))
    c_123 in 
  c_123.

Definition fp12conjugate (n_125 : fp12_t) : fp12_t :=
  let '(n1_126, n2_127) :=
    n_125 in 
  (n1_126, fp6neg (n2_127)).

Definition fp12zero  : fp12_t :=
  fp12fromfp6 (fp6zero ).

Definition g1add_a (p_128 : g1_t) (q_129 : g1_t) : g1_t :=
  let '(x1_130, y1_131, _) :=
    p_128 in 
  let '(x2_132, y2_133, _) :=
    q_129 in 
  let x_diff_134 : fp_t :=
    (x2_132) -% (x1_130) in 
  let y_diff_135 : fp_t :=
    (y2_133) -% (y1_131) in 
  let xovery_136 : fp_t :=
    (y_diff_135) *% (nat_mod_inv (x_diff_134)) in 
  let x3_137 : fp_t :=
    ((nat_mod_exp (xovery_136) (@repr WORDSIZE32 2)) -% (x1_130)) -% (
      x2_132) in 
  let y3_138 : fp_t :=
    ((xovery_136) *% ((x1_130) -% (x3_137))) -% (y1_131) in 
  (x3_137, y3_138, false).

Definition g1double_a (p_139 : g1_t) : g1_t :=
  let '(x1_140, y1_141, _) :=
    p_139 in 
  let x12_142 : fp_t :=
    nat_mod_exp (x1_140) (@repr WORDSIZE32 2) in 
  let xovery_143 : fp_t :=
    ((nat_mod_from_literal (
          0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab) (
          @repr WORDSIZE128 3) : fp_t) *% (x12_142)) *% (nat_mod_inv ((
          nat_mod_two ) *% (y1_141))) in 
  let x3_144 : fp_t :=
    (nat_mod_exp (xovery_143) (@repr WORDSIZE32 2)) -% ((nat_mod_two ) *% (
        x1_140)) in 
  let y3_145 : fp_t :=
    ((xovery_143) *% ((x1_140) -% (x3_144))) -% (y1_141) in 
  (x3_144, y3_145, false).

Definition g1double (p_146 : g1_t) : g1_t :=
  let '(x1_147, y1_148, inf1_149) :=
    p_146 in 
  (if (((y1_148) !=.? (nat_mod_zero )) && (negb (inf1_149))):bool then (
      g1double_a (p_146)) else ((nat_mod_zero , nat_mod_zero , true))).

Definition g1add (p_150 : g1_t) (q_151 : g1_t) : g1_t :=
  let '(x1_152, y1_153, inf1_154) :=
    p_150 in 
  let '(x2_155, y2_156, inf2_157) :=
    q_151 in 
  (if (inf1_154):bool then (q_151) else ((if (inf2_157):bool then (p_150) else (
          (if ((p_150) =.? (q_151)):bool then (g1double (p_150)) else ((if (
                  negb (((x1_152) =.? (x2_155)) && ((y1_153) =.? ((
                          nat_mod_zero ) -% (y2_156))))):bool then (g1add_a (
                    p_150) (q_151)) else ((nat_mod_zero , nat_mod_zero , true
                  ))))))))).

Definition g1mul (m_158 : scalar_t) (p_159 : g1_t) : g1_t :=
  let t_160 : (fp_t × fp_t × bool) :=
    (nat_mod_zero , nat_mod_zero , true) in 
  let t_160 :=
    foldi (usize 0) (usize 256) (fun i_161 t_160 =>
      let t_160 :=
        g1double (t_160) in 
      let '(t_160) :=
        if nat_mod_bit (m_158) ((usize 255) - (i_161)):bool then (let t_160 :=
            g1add (t_160) (p_159) in 
          (t_160)) else ((t_160)) in 
      (t_160))
    t_160 in 
  t_160.

Definition g1neg (p_162 : g1_t) : g1_t :=
  let '(x_163, y_164, inf_165) :=
    p_162 in 
  (x_163, (nat_mod_zero ) -% (y_164), inf_165).

Definition g2add_a (p_166 : g2_t) (q_167 : g2_t) : g2_t :=
  let '(x1_168, y1_169, _) :=
    p_166 in 
  let '(x2_170, y2_171, _) :=
    q_167 in 
  let x_diff_172 : (fp_t × fp_t) :=
    fp2sub (x2_170) (x1_168) in 
  let y_diff_173 : (fp_t × fp_t) :=
    fp2sub (y2_171) (y1_169) in 
  let xovery_174 : (fp_t × fp_t) :=
    fp2mul (y_diff_173) (fp2inv (x_diff_172)) in 
  let t1_175 : (fp_t × fp_t) :=
    fp2mul (xovery_174) (xovery_174) in 
  let t2_176 : (fp_t × fp_t) :=
    fp2sub (t1_175) (x1_168) in 
  let x3_177 : (fp_t × fp_t) :=
    fp2sub (t2_176) (x2_170) in 
  let t1_178 : (fp_t × fp_t) :=
    fp2sub (x1_168) (x3_177) in 
  let t2_179 : (fp_t × fp_t) :=
    fp2mul (xovery_174) (t1_178) in 
  let y3_180 : (fp_t × fp_t) :=
    fp2sub (t2_179) (y1_169) in 
  (x3_177, y3_180, false).

Definition g2double_a (p_181 : g2_t) : g2_t :=
  let '(x1_182, y1_183, _) :=
    p_181 in 
  let x12_184 : (fp_t × fp_t) :=
    fp2mul (x1_182) (x1_182) in 
  let t1_185 : (fp_t × fp_t) :=
    fp2mul (fp2fromfp (nat_mod_from_literal (
          0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab) (
          @repr WORDSIZE128 3) : fp_t)) (x12_184) in 
  let t2_186 : (fp_t × fp_t) :=
    fp2inv (fp2mul (fp2fromfp (nat_mod_two )) (y1_183)) in 
  let xovery_187 : (fp_t × fp_t) :=
    fp2mul (t1_185) (t2_186) in 
  let t1_188 : (fp_t × fp_t) :=
    fp2mul (xovery_187) (xovery_187) in 
  let t2_189 : (fp_t × fp_t) :=
    fp2mul (fp2fromfp (nat_mod_two )) (x1_182) in 
  let x3_190 : (fp_t × fp_t) :=
    fp2sub (t1_188) (t2_189) in 
  let t1_191 : (fp_t × fp_t) :=
    fp2sub (x1_182) (x3_190) in 
  let t2_192 : (fp_t × fp_t) :=
    fp2mul (xovery_187) (t1_191) in 
  let y3_193 : (fp_t × fp_t) :=
    fp2sub (t2_192) (y1_183) in 
  (x3_190, y3_193, false).

Definition g2double (p_194 : g2_t) : g2_t :=
  let '(x1_195, y1_196, inf1_197) :=
    p_194 in 
  (if (((y1_196) !=.? (fp2zero )) && (negb (inf1_197))):bool then (g2double_a (
        p_194)) else ((fp2zero , fp2zero , true))).

Definition g2add (p_198 : g2_t) (q_199 : g2_t) : g2_t :=
  let '(x1_200, y1_201, inf1_202) :=
    p_198 in 
  let '(x2_203, y2_204, inf2_205) :=
    q_199 in 
  (if (inf1_202):bool then (q_199) else ((if (inf2_205):bool then (p_198) else (
          (if ((p_198) =.? (q_199)):bool then (g2double (p_198)) else ((if (
                  negb (((x1_200) =.? (x2_203)) && ((y1_201) =.? (fp2neg (
                          y2_204))))):bool then (g2add_a (p_198) (q_199)) else (
                  (fp2zero , fp2zero , true))))))))).

Definition g2mul (m_206 : scalar_t) (p_207 : g2_t) : g2_t :=
  let t_208 : (fp2_t × fp2_t × bool) :=
    (fp2zero , fp2zero , true) in 
  let t_208 :=
    foldi (usize 0) (usize 256) (fun i_209 t_208 =>
      let t_208 :=
        g2double (t_208) in 
      let '(t_208) :=
        if nat_mod_bit (m_206) ((usize 255) - (i_209)):bool then (let t_208 :=
            g2add (t_208) (p_207) in 
          (t_208)) else ((t_208)) in 
      (t_208))
    t_208 in 
  t_208.

Definition g2neg (p_210 : g2_t) : g2_t :=
  let '(x_211, y_212, inf_213) :=
    p_210 in 
  (x_211, fp2neg (y_212), inf_213).

Definition twist (p_214 : g1_t) : (fp12_t × fp12_t) :=
  let '(p0_215, p1_216, _) :=
    p_214 in 
  let x_217 : ((fp2_t × fp2_t × fp2_t) × fp6_t) :=
    ((fp2zero , fp2fromfp (p0_215), fp2zero ), fp6zero ) in 
  let y_218 : (fp6_t × (fp2_t × fp2_t × fp2_t)) :=
    (fp6zero , (fp2zero , fp2fromfp (p1_216), fp2zero )) in 
  (x_217, y_218).

Definition line_double_p (r_219 : g2_t) (p_220 : g1_t) : fp12_t :=
  let '(r0_221, r1_222, _) :=
    r_219 in 
  let a_223 : (fp_t × fp_t) :=
    fp2mul (fp2fromfp (nat_mod_from_literal (
          0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab) (
          @repr WORDSIZE128 3) : fp_t)) (fp2mul (r0_221) (r0_221)) in 
  let a_224 : (fp_t × fp_t) :=
    fp2mul (a_223) (fp2inv (fp2mul (fp2fromfp (nat_mod_two )) (r1_222))) in 
  let b_225 : (fp_t × fp_t) :=
    fp2sub (r1_222) (fp2mul (a_224) (r0_221)) in 
  let a_226 : (fp6_t × fp6_t) :=
    fp12fromfp6 (fp6fromfp2 (a_224)) in 
  let b_227 : (fp6_t × fp6_t) :=
    fp12fromfp6 (fp6fromfp2 (b_225)) in 
  let '(x_228, y_229) :=
    twist (p_220) in 
  fp12neg (fp12sub (fp12sub (y_229) (fp12mul (a_226) (x_228))) (b_227)).

Definition line_add_p (r_230 : g2_t) (q_231 : g2_t) (p_232 : g1_t) : fp12_t :=
  let '(r0_233, r1_234, _) :=
    r_230 in 
  let '(q0_235, q1_236, _) :=
    q_231 in 
  let a_237 : (fp_t × fp_t) :=
    fp2mul (fp2sub (q1_236) (r1_234)) (fp2inv (fp2sub (q0_235) (r0_233))) in 
  let b_238 : (fp_t × fp_t) :=
    fp2sub (r1_234) (fp2mul (a_237) (r0_233)) in 
  let a_239 : (fp6_t × fp6_t) :=
    fp12fromfp6 (fp6fromfp2 (a_237)) in 
  let b_240 : (fp6_t × fp6_t) :=
    fp12fromfp6 (fp6fromfp2 (b_238)) in 
  let '(x_241, y_242) :=
    twist (p_232) in 
  fp12neg (fp12sub (fp12sub (y_242) (fp12mul (a_239) (x_241))) (b_240)).

Definition frobenius (f_243 : fp12_t) : fp12_t :=
  let '((g0_244, g1_245, g2_246), (h0_247, h1_248, h2_249)) :=
    f_243 in 
  let t1_250 : (fp_t × fp_t) :=
    fp2conjugate (g0_244) in 
  let t2_251 : (fp_t × fp_t) :=
    fp2conjugate (h0_247) in 
  let t3_252 : (fp_t × fp_t) :=
    fp2conjugate (g1_245) in 
  let t4_253 : (fp_t × fp_t) :=
    fp2conjugate (h1_248) in 
  let t5_254 : (fp_t × fp_t) :=
    fp2conjugate (g2_246) in 
  let t6_255 : (fp_t × fp_t) :=
    fp2conjugate (h2_249) in 
  let c1_256 : array_fp_t :=
    array_from_list uint64 (let l :=
        [
          secret (@repr WORDSIZE64 10162220747404304312) : int64;
          secret (@repr WORDSIZE64 17761815663483519293) : int64;
          secret (@repr WORDSIZE64 8873291758750579140) : int64;
          secret (@repr WORDSIZE64 1141103941765652303) : int64;
          secret (@repr WORDSIZE64 13993175198059990303) : int64;
          secret (@repr WORDSIZE64 1802798568193066599) : int64
        ] in  l) in 
  let c1_257 : seq uint8 :=
    array_to_le_bytes (c1_256) in 
  let c1_258 : fp_t :=
    nat_mod_from_byte_seq_le (c1_257) : fp_t in 
  let c2_259 : array_fp_t :=
    array_from_list uint64 (let l :=
        [
          secret (@repr WORDSIZE64 3240210268673559283) : int64;
          secret (@repr WORDSIZE64 2895069921743240898) : int64;
          secret (@repr WORDSIZE64 17009126888523054175) : int64;
          secret (@repr WORDSIZE64 6098234018649060207) : int64;
          secret (@repr WORDSIZE64 9865672654120263608) : int64;
          secret (@repr WORDSIZE64 71000049454473266) : int64
        ] in  l) in 
  let c2_260 : seq uint8 :=
    array_to_le_bytes (c2_259) in 
  let c2_261 : fp_t :=
    nat_mod_from_byte_seq_le (c2_260) : fp_t in 
  let gamma11_262 : (fp_t × fp_t) :=
    (c1_258, c2_261) in 
  let gamma12_263 : (fp_t × fp_t) :=
    fp2mul (gamma11_262) (gamma11_262) in 
  let gamma13_264 : (fp_t × fp_t) :=
    fp2mul (gamma12_263) (gamma11_262) in 
  let gamma14_265 : (fp_t × fp_t) :=
    fp2mul (gamma13_264) (gamma11_262) in 
  let gamma15_266 : (fp_t × fp_t) :=
    fp2mul (gamma14_265) (gamma11_262) in 
  let t2_267 : (fp_t × fp_t) :=
    fp2mul (t2_251) (gamma11_262) in 
  let t3_268 : (fp_t × fp_t) :=
    fp2mul (t3_252) (gamma12_263) in 
  let t4_269 : (fp_t × fp_t) :=
    fp2mul (t4_253) (gamma13_264) in 
  let t5_270 : (fp_t × fp_t) :=
    fp2mul (t5_254) (gamma14_265) in 
  let t6_271 : (fp_t × fp_t) :=
    fp2mul (t6_255) (gamma15_266) in 
  ((t1_250, t3_268, t5_270), (t2_267, t4_269, t6_271)).

Definition final_exponentiation (f_272 : fp12_t) : fp12_t :=
  let fp6_273 : (fp6_t × fp6_t) :=
    fp12conjugate (f_272) in 
  let finv_274 : (fp6_t × fp6_t) :=
    fp12inv (f_272) in 
  let fp6_1_275 : (fp6_t × fp6_t) :=
    fp12mul (fp6_273) (finv_274) in 
  let fp8_276 : (fp6_t × fp6_t) :=
    frobenius (frobenius (fp6_1_275)) in 
  let f_277 : (fp6_t × fp6_t) :=
    fp12mul (fp8_276) (fp6_1_275) in 
  let u_278 : scalar_t :=
    nat_mod_from_literal (
      0x8000000000000000000000000000000000000000000000000000000000000000) (
      @repr WORDSIZE128 15132376222941642752) : scalar_t in 
  let t0_279 : (fp6_t × fp6_t) :=
    fp12mul (f_277) (f_277) in 
  let t1_280 : (fp6_t × fp6_t) :=
    fp12exp (t0_279) (u_278) in 
  let t1_281 : (fp6_t × fp6_t) :=
    fp12conjugate (t1_280) in 
  let t2_282 : (fp6_t × fp6_t) :=
    fp12exp (t1_281) ((u_278) /% (nat_mod_two )) in 
  let t2_283 : (fp6_t × fp6_t) :=
    fp12conjugate (t2_282) in 
  let t3_284 : (fp6_t × fp6_t) :=
    fp12conjugate (f_277) in 
  let t1_285 : (fp6_t × fp6_t) :=
    fp12mul (t3_284) (t1_281) in 
  let t1_286 : (fp6_t × fp6_t) :=
    fp12conjugate (t1_285) in 
  let t1_287 : (fp6_t × fp6_t) :=
    fp12mul (t1_286) (t2_283) in 
  let t2_288 : (fp6_t × fp6_t) :=
    fp12exp (t1_287) (u_278) in 
  let t2_289 : (fp6_t × fp6_t) :=
    fp12conjugate (t2_288) in 
  let t3_290 : (fp6_t × fp6_t) :=
    fp12exp (t2_289) (u_278) in 
  let t3_291 : (fp6_t × fp6_t) :=
    fp12conjugate (t3_290) in 
  let t1_292 : (fp6_t × fp6_t) :=
    fp12conjugate (t1_287) in 
  let t3_293 : (fp6_t × fp6_t) :=
    fp12mul (t1_292) (t3_291) in 
  let t1_294 : (fp6_t × fp6_t) :=
    fp12conjugate (t1_292) in 
  let t1_295 : (fp6_t × fp6_t) :=
    frobenius (frobenius (frobenius (t1_294))) in 
  let t2_296 : (fp6_t × fp6_t) :=
    frobenius (frobenius (t2_289)) in 
  let t1_297 : (fp6_t × fp6_t) :=
    fp12mul (t1_295) (t2_296) in 
  let t2_298 : (fp6_t × fp6_t) :=
    fp12exp (t3_293) (u_278) in 
  let t2_299 : (fp6_t × fp6_t) :=
    fp12conjugate (t2_298) in 
  let t2_300 : (fp6_t × fp6_t) :=
    fp12mul (t2_299) (t0_279) in 
  let t2_301 : (fp6_t × fp6_t) :=
    fp12mul (t2_300) (f_277) in 
  let t1_302 : (fp6_t × fp6_t) :=
    fp12mul (t1_297) (t2_301) in 
  let t2_303 : (fp6_t × fp6_t) :=
    frobenius (t3_293) in 
  let t1_304 : (fp6_t × fp6_t) :=
    fp12mul (t1_302) (t2_303) in 
  t1_304.

Definition pairing (p_305 : g1_t) (q_306 : g2_t) : fp12_t :=
  let t_307 : scalar_t :=
    nat_mod_from_literal (
      0x8000000000000000000000000000000000000000000000000000000000000000) (
      @repr WORDSIZE128 15132376222941642752) : scalar_t in 
  let r_308 : (fp2_t × fp2_t × bool) :=
    q_306 in 
  let f_309 : (fp6_t × fp6_t) :=
    fp12fromfp6 (fp6fromfp2 (fp2fromfp (nat_mod_one ))) in 
  let '(r_308, f_309) :=
    foldi (usize 1) (usize 64) (fun i_310 '(r_308, f_309) =>
      let lrr_311 : (fp6_t × fp6_t) :=
        line_double_p (r_308) (p_305) in 
      let r_308 :=
        g2double (r_308) in 
      let f_309 :=
        fp12mul (fp12mul (f_309) (f_309)) (lrr_311) in 
      let '(r_308, f_309) :=
        if nat_mod_bit (t_307) (((usize 64) - (i_310)) - (usize 1)):bool then (
          let lrq_312 : (fp6_t × fp6_t) :=
            line_add_p (r_308) (q_306) (p_305) in 
          let r_308 :=
            g2add (r_308) (q_306) in 
          let f_309 :=
            fp12mul (f_309) (lrq_312) in 
          (r_308, f_309)) else ((r_308, f_309)) in 
      (r_308, f_309))
    (r_308, f_309) in 
  final_exponentiation (fp12conjugate (f_309)).

Definition test_fp2_prop_add_neg (a_313 : fp2_t) : bool :=
  let b_314 : (fp_t × fp_t) :=
    fp2neg (a_313) in 
  (fp2fromfp (nat_mod_zero )) =.? (fp2add (a_313) (b_314)).
QuickChick (forAll g_fp2_t (fun a_313 : fp2_t =>test_fp2_prop_add_neg a_313)).


Definition test_fp2_prop_mul_inv (a_315 : fp2_t) : bool :=
  let b_316 : (fp_t × fp_t) :=
    fp2inv (a_315) in 
  (fp2fromfp (nat_mod_one )) =.? (fp2mul (a_315) (b_316)).
QuickChick (forAll g_fp2_t (fun a_315 : fp2_t =>test_fp2_prop_mul_inv a_315)).


Definition test_extraction_issue  : bool :=
  let b_317 : (fp_t × fp_t) :=
    fp2inv ((nat_mod_one , nat_mod_one )) in 
  (fp2fromfp (nat_mod_one )) =.? (fp2mul ((nat_mod_one , nat_mod_one )) (
      b_317)).
QuickChick (test_extraction_issue).


Definition test_fp6_prop_mul_inv (a_318 : fp6_t) : bool :=
  let b_319 : (fp2_t × fp2_t × fp2_t) :=
    fp6inv (a_318) in 
  (fp6fromfp2 (fp2fromfp (nat_mod_one ))) =.? (fp6mul (a_318) (b_319)).
QuickChick (forAll g_fp6_t (fun a_318 : fp6_t =>test_fp6_prop_mul_inv a_318)).


Definition test_fp6_prop_add_neg (a_320 : fp6_t) : bool :=
  let b_321 : (fp2_t × fp2_t × fp2_t) :=
    fp6neg (a_320) in 
  (fp6fromfp2 (fp2fromfp (nat_mod_zero ))) =.? (fp6add (a_320) (b_321)).
QuickChick (forAll g_fp6_t (fun a_320 : fp6_t =>test_fp6_prop_add_neg a_320)).


Definition test_fp12_prop_add_neg (a_322 : fp12_t) : bool :=
  let b_323 : (fp6_t × fp6_t) :=
    fp12neg (a_322) in 
  (fp12fromfp6 (fp6fromfp2 (fp2fromfp (nat_mod_zero )))) =.? (fp12add (a_322) (
      b_323)).
QuickChick (
  forAll g_fp12_t (fun a_322 : fp12_t =>test_fp12_prop_add_neg a_322)).


Definition test_fp12_prop_mul_inv (a_324 : fp12_t) : bool :=
  let b_325 : (fp6_t × fp6_t) :=
    fp12inv (a_324) in 
  (fp12fromfp6 (fp6fromfp2 (fp2fromfp (nat_mod_one )))) =.? (fp12mul (a_324) (
      b_325)).
QuickChick (
  forAll g_fp12_t (fun a_324 : fp12_t =>test_fp12_prop_mul_inv a_324)).


