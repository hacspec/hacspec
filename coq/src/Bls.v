Require Import Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
From QuickChick Require Import QuickChick.
Require Import Hacspec.Lib.

Definition fp_canvas := nseq (int8) (48).
Definition fp :=
  nat_mod 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab.
Instance show_fp : Show (fp) := Build_Show (fp) (fun x => show (GZnZ.val _ x)).
Definition g_fp : G (fp) := @bindGen Z (fp) (arbitrary) (fun x => returnGen (@Z_in_nat_mod _ x)).
Instance gen_fp : Gen (fp) := Build_Gen fp g_fp.


Definition serialized_fp := nseq (uint8) (usize 48).

Definition array_fp := nseq (uint64) (usize 6).

Definition scalar_canvas := nseq (int8) (32).
Definition scalar :=
  nat_mod 0x8000000000000000000000000000000000000000000000000000000000000000.
Instance show_scalar : Show (scalar) := Build_Show (scalar) (fun x => show (GZnZ.val _ x)).
Definition g_scalar : G (scalar) := @bindGen Z (scalar) (arbitrary) (fun x => returnGen (@Z_in_nat_mod _ x)).
Instance gen_scalar : Gen (scalar) := Build_Gen scalar g_scalar.


Definition most_significant_bit (m_0 : scalar) (n_1 : uint_size) : uint_size :=
  if (((n_1) >.? (usize 0)) && (negb (nat_mod_bit (m_0) (n_1)))):bool then (
    most_significant_bit (m_0) ((n_1) - (usize 1))) else (n_1).
  
  QuickChick (
    forAll g_scalar (fun m_0 : scalar =>forAll g_uint_size (fun n_1 : uint_size =>most_significant_bit m_0) n_1)).

Notation "'g1'" := ((fp × fp × bool)) : hacspec_scope.
Instance show_g1 : Show (g1) :=
Build_Show g1 (fun x =>
  let (x, x0) := x in
  let (x, x1) := x in
  append ("("%string) (append (show x) (append (","%string) (append (show x0) (append (","%string) (append (show x1) (")"%string))))))).
Definition g_g1 : G (g1) :=
bindGen arbitrary (fun x0 : fp =>
  bindGen arbitrary (fun x1 : fp =>
  bindGen arbitrary (fun x2 : bool =>
  returnGen (x0,x1,x2)))).
Instance gen_g1 : Gen (g1) := Build_Gen g1 g_g1.


Notation "'fp2'" := ((fp × fp)) : hacspec_scope.
Instance show_fp2 : Show (fp2) :=
Build_Show fp2 (fun x =>
  let (x, x0) := x in
  append ("("%string) (append (show x) (append (","%string) (append (show x0) (")"%string))))).
Definition g_fp2 : G (fp2) :=
bindGen arbitrary (fun x0 : fp =>
  bindGen arbitrary (fun x1 : fp =>
  returnGen (x0,x1))).
Instance gen_fp2 : Gen (fp2) := Build_Gen fp2 g_fp2.


Notation "'g2'" := ((fp2 × fp2 × bool)) : hacspec_scope.
Instance show_g2 : Show (g2) :=
Build_Show g2 (fun x =>
  let (x, x0) := x in
  let (x, x1) := x in
  append ("("%string) (append (show x) (append (","%string) (append (show x0) (append (","%string) (append (show x1) (")"%string))))))).
Definition g_g2 : G (g2) :=
bindGen arbitrary (fun x0 : fp2 =>
  bindGen arbitrary (fun x1 : fp2 =>
  bindGen arbitrary (fun x2 : bool =>
  returnGen (x0,x1,x2)))).
Instance gen_g2 : Gen (g2) := Build_Gen g2 g_g2.


Notation "'fp6'" := ((fp2 × fp2 × fp2)) : hacspec_scope.
Instance show_fp6 : Show (fp6) :=
Build_Show fp6 (fun x =>
  let (x, x0) := x in
  let (x, x1) := x in
  append ("("%string) (append (show x) (append (","%string) (append (show x0) (append (","%string) (append (show x1) (")"%string))))))).
Definition g_fp6 : G (fp6) :=
bindGen arbitrary (fun x0 : fp2 =>
  bindGen arbitrary (fun x1 : fp2 =>
  bindGen arbitrary (fun x2 : fp2 =>
  returnGen (x0,x1,x2)))).
Instance gen_fp6 : Gen (fp6) := Build_Gen fp6 g_fp6.


Notation "'fp12'" := ((fp6 × fp6)) : hacspec_scope.
Instance show_fp12 : Show (fp12) :=
Build_Show fp12 (fun x =>
  let (x, x0) := x in
  append ("("%string) (append (show x) (append (","%string) (append (show x0) (")"%string))))).
Definition g_fp12 : G (fp12) :=
bindGen arbitrary (fun x0 : fp6 =>
  bindGen arbitrary (fun x1 : fp6 =>
  returnGen (x0,x1))).
Instance gen_fp12 : Gen (fp12) := Build_Gen fp12 g_fp12.


Definition fp2fromfp (n_2 : fp) : fp2 :=
  (n_2, nat_mod_zero ).
  
  QuickChick (forAll g_fp (fun n_2 : fp =>fp2fromfp n_2)).

Definition fp2zero  : fp2 :=
  fp2fromfp (nat_mod_zero ).
  
  QuickChick (fp2zero).

Definition fp2neg (n_3 : fp2) : fp2 :=
  let '(n1_4, n2_5) :=
    n_3 in 
  ((nat_mod_zero ) -% (n1_4), (nat_mod_zero ) -% (n2_5)).
  
  QuickChick (forAll g_fp2 (fun n_3 : fp2 =>fp2neg n_3)).

Definition fp2add (n_6 : fp2) (m_7 : fp2) : fp2 :=
  let '(n1_8, n2_9) :=
    n_6 in 
  let '(m1_10, m2_11) :=
    m_7 in 
  ((n1_8) +% (m1_10), (n2_9) +% (m2_11)).
  
  QuickChick (
    forAll g_fp2 (fun n_6 : fp2 =>forAll g_fp2 (fun m_7 : fp2 =>fp2add n_6) m_7)).

Definition fp2sub (n_12 : fp2) (m_13 : fp2) : fp2 :=
  fp2add (n_12) (fp2neg (m_13)).
  
  QuickChick (
    forAll g_fp2 (fun n_12 : fp2 =>forAll g_fp2 (fun m_13 : fp2 =>fp2sub n_12) m_13)).

Definition fp2mul (n_14 : fp2) (m_15 : fp2) : fp2 :=
  let '(n1_16, n2_17) :=
    n_14 in 
  let '(m1_18, m2_19) :=
    m_15 in 
  let x1_20 :=
    ((n1_16) *% (m1_18)) -% ((n2_17) *% (m2_19)) in 
  let x2_21 :=
    ((n1_16) *% (m2_19)) +% ((n2_17) *% (m1_18)) in 
  (x1_20, x2_21).
  
  QuickChick (
    forAll g_fp2 (fun n_14 : fp2 =>forAll g_fp2 (fun m_15 : fp2 =>fp2mul n_14) m_15)).

Definition fp2inv (n_22 : fp2) : fp2 :=
  let '(n1_23, n2_24) :=
    n_22 in 
  let t0_25 :=
    ((n1_23) *% (n1_23)) +% ((n2_24) *% (n2_24)) in 
  let t1_26 :=
    nat_mod_inv (t0_25) in 
  let x1_27 :=
    (n1_23) *% (t1_26) in 
  let x2_28 :=
    (nat_mod_zero ) -% ((n2_24) *% (t1_26)) in 
  (x1_27, x2_28).
  
  QuickChick (forAll g_fp2 (fun n_22 : fp2 =>fp2inv n_22)).

Definition fp2conjugate (n_29 : fp2) : fp2 :=
  let '(n1_30, n2_31) :=
    n_29 in 
  (n1_30, (nat_mod_zero ) -% (n2_31)).
  
  QuickChick (forAll g_fp2 (fun n_29 : fp2 =>fp2conjugate n_29)).

Definition fp6fromfp2 (n_32 : fp2) : fp6 :=
  (n_32, fp2zero , fp2zero ).
  
  QuickChick (forAll g_fp2 (fun n_32 : fp2 =>fp6fromfp2 n_32)).

Definition fp6zero  : fp6 :=
  fp6fromfp2 (fp2zero ).
  
  QuickChick (fp6zero).

Definition fp6neg (n_33 : fp6) : fp6 :=
  let '(n1_34, n2_35, n3_36) :=
    n_33 in 
  (
    fp2sub (fp2zero ) (n1_34),
    fp2sub (fp2zero ) (n2_35),
    fp2sub (fp2zero ) (n3_36)
  ).
  
  QuickChick (forAll g_fp6 (fun n_33 : fp6 =>fp6neg n_33)).

Definition fp6add (n_37 : fp6) (m_38 : fp6) : fp6 :=
  let '(n1_39, n2_40, n3_41) :=
    n_37 in 
  let '(m1_42, m2_43, m3_44) :=
    m_38 in 
  (fp2add (n1_39) (m1_42), fp2add (n2_40) (m2_43), fp2add (n3_41) (m3_44)).
  
  QuickChick (
    forAll g_fp6 (fun n_37 : fp6 =>forAll g_fp6 (fun m_38 : fp6 =>fp6add n_37) m_38)).

Definition fp6sub (n_45 : fp6) (m_46 : fp6) : fp6 :=
  fp6add (n_45) (fp6neg (m_46)).
  
  QuickChick (
    forAll g_fp6 (fun n_45 : fp6 =>forAll g_fp6 (fun m_46 : fp6 =>fp6sub n_45) m_46)).

Definition fp6mul (n_47 : fp6) (m_48 : fp6) : fp6 :=
  let '(n1_49, n2_50, n3_51) :=
    n_47 in 
  let '(m1_52, m2_53, m3_54) :=
    m_48 in 
  let eps_55 :=
    (nat_mod_one , nat_mod_one ) in 
  let t1_56 :=
    fp2mul (n1_49) (m1_52) in 
  let t2_57 :=
    fp2mul (n2_50) (m2_53) in 
  let t3_58 :=
    fp2mul (n3_51) (m3_54) in 
  let t4_59 :=
    fp2mul (fp2add (n2_50) (n3_51)) (fp2add (m2_53) (m3_54)) in 
  let t5_60 :=
    fp2sub (fp2sub (t4_59) (t2_57)) (t3_58) in 
  let x_61 :=
    fp2add (fp2mul (t5_60) (eps_55)) (t1_56) in 
  let t4_62 :=
    fp2mul (fp2add (n1_49) (n2_50)) (fp2add (m1_52) (m2_53)) in 
  let t5_63 :=
    fp2sub (fp2sub (t4_62) (t1_56)) (t2_57) in 
  let y_64 :=
    fp2add (t5_63) (fp2mul (eps_55) (t3_58)) in 
  let t4_65 :=
    fp2mul (fp2add (n1_49) (n3_51)) (fp2add (m1_52) (m3_54)) in 
  let t5_66 :=
    fp2sub (fp2sub (t4_65) (t1_56)) (t3_58) in 
  let z_67 :=
    fp2add (t5_66) (t2_57) in 
  (x_61, y_64, z_67).
  
  QuickChick (
    forAll g_fp6 (fun n_47 : fp6 =>forAll g_fp6 (fun m_48 : fp6 =>fp6mul n_47) m_48)).

Definition fp6inv (n_68 : fp6) : fp6 :=
  let '(n1_69, n2_70, n3_71) :=
    n_68 in 
  let eps_72 :=
    (nat_mod_one , nat_mod_one ) in 
  let t1_73 :=
    fp2mul (n1_69) (n1_69) in 
  let t2_74 :=
    fp2mul (n2_70) (n2_70) in 
  let t3_75 :=
    fp2mul (n3_71) (n3_71) in 
  let t4_76 :=
    fp2mul (n1_69) (n2_70) in 
  let t5_77 :=
    fp2mul (n1_69) (n3_71) in 
  let t6_78 :=
    fp2mul (n2_70) (n3_71) in 
  let x0_79 :=
    fp2sub (t1_73) (fp2mul (eps_72) (t6_78)) in 
  let y0_80 :=
    fp2sub (fp2mul (eps_72) (t3_75)) (t4_76) in 
  let z0_81 :=
    fp2sub (t2_74) (t5_77) in 
  let t0_82 :=
    fp2mul (n1_69) (x0_79) in 
  let t0_83 :=
    fp2add (t0_82) (fp2mul (eps_72) (fp2mul (n3_71) (y0_80))) in 
  let t0_84 :=
    fp2add (t0_83) (fp2mul (eps_72) (fp2mul (n2_70) (z0_81))) in 
  let t0_85 :=
    fp2inv (t0_84) in 
  let x_86 :=
    fp2mul (x0_79) (t0_85) in 
  let y_87 :=
    fp2mul (y0_80) (t0_85) in 
  let z_88 :=
    fp2mul (z0_81) (t0_85) in 
  (x_86, y_87, z_88).
  
  QuickChick (forAll g_fp6 (fun n_68 : fp6 =>fp6inv n_68)).

Definition fp12fromfp6 (n_89 : fp6) : fp12 :=
  (n_89, fp6zero ).
  
  QuickChick (forAll g_fp6 (fun n_89 : fp6 =>fp12fromfp6 n_89)).

Definition fp12neg (n_90 : fp12) : fp12 :=
  let '(n1_91, n2_92) :=
    n_90 in 
  (fp6sub (fp6zero ) (n1_91), fp6sub (fp6zero ) (n2_92)).
  
  QuickChick (forAll g_fp12 (fun n_90 : fp12 =>fp12neg n_90)).

Definition fp12add (n_93 : fp12) (m_94 : fp12) : fp12 :=
  let '(n1_95, n2_96) :=
    n_93 in 
  let '(m1_97, m2_98) :=
    m_94 in 
  (fp6add (n1_95) (m1_97), fp6add (n2_96) (m2_98)).
  
  QuickChick (
    forAll g_fp12 (fun n_93 : fp12 =>forAll g_fp12 (fun m_94 : fp12 =>fp12add n_93) m_94)).

Definition fp12sub (n_99 : fp12) (m_100 : fp12) : fp12 :=
  fp12add (n_99) (fp12neg (m_100)).
  
  QuickChick (
    forAll g_fp12 (fun n_99 : fp12 =>forAll g_fp12 (fun m_100 : fp12 =>fp12sub n_99) m_100)).

Definition fp12mul (n_101 : fp12) (m_102 : fp12) : fp12 :=
  let '(n1_103, n2_104) :=
    n_101 in 
  let '(m1_105, m2_106) :=
    m_102 in 
  let gamma_107 :=
    (fp2zero , fp2fromfp (nat_mod_one ), fp2zero ) in 
  let t1_108 :=
    fp6mul (n1_103) (m1_105) in 
  let t2_109 :=
    fp6mul (n2_104) (m2_106) in 
  let x_110 :=
    fp6add (t1_108) (fp6mul (t2_109) (gamma_107)) in 
  let y_111 :=
    fp6mul (fp6add (n1_103) (n2_104)) (fp6add (m1_105) (m2_106)) in 
  let y_112 :=
    fp6sub (fp6sub (y_111) (t1_108)) (t2_109) in 
  (x_110, y_112).
  
  QuickChick (
    forAll g_fp12 (fun n_101 : fp12 =>forAll g_fp12 (fun m_102 : fp12 =>fp12mul n_101) m_102)).

Definition fp12inv (n_113 : fp12) : fp12 :=
  let '(n1_114, n2_115) :=
    n_113 in 
  let gamma_116 :=
    (fp2zero , fp2fromfp (nat_mod_one ), fp2zero ) in 
  let t1_117 :=
    fp6mul (n1_114) (n1_114) in 
  let t2_118 :=
    fp6mul (n2_115) (n2_115) in 
  let t1_119 :=
    fp6sub (t1_117) (fp6mul (gamma_116) (t2_118)) in 
  let t2_120 :=
    fp6inv (t1_119) in 
  let x_121 :=
    fp6mul (n1_114) (t2_120) in 
  let y_122 :=
    fp6neg (fp6mul (n2_115) (t2_120)) in 
  (x_121, y_122).
  
  QuickChick (forAll g_fp12 (fun n_113 : fp12 =>fp12inv n_113)).

Definition fp12exp (n_123 : fp12) (k_124 : scalar) : fp12 :=
  let l_125 :=
    (usize 255) - (most_significant_bit (k_124) (usize 255)) in 
  let c_126 :=
    n_123 in 
  let c_126 :=
    foldi (l_125) (usize 255) (fun i_127 c_126 =>
      let c_126 :=
        fp12mul (c_126) (c_126) in 
      let '(c_126) :=
        if nat_mod_bit (k_124) (((usize 255) - (i_127)) - (usize 1)):bool then (
          let c_126 :=
            fp12mul (c_126) (n_123) in 
          (c_126)
        ) else ( (c_126)
        ) in 
      (c_126))
    c_126 in 
  c_126.
  
  QuickChick (
    forAll g_fp12 (fun n_123 : fp12 =>forAll g_scalar (fun k_124 : scalar =>fp12exp n_123) k_124)).

Definition fp12conjugate (n_128 : fp12) : fp12 :=
  let '(n1_129, n2_130) :=
    n_128 in 
  (n1_129, fp6neg (n2_130)).
  
  QuickChick (forAll g_fp12 (fun n_128 : fp12 =>fp12conjugate n_128)).

Definition fp12zero  : fp12 :=
  fp12fromfp6 (fp6zero ).
  
  QuickChick (fp12zero).

Definition g1add_a (p_131 : g1) (q_132 : g1) : g1 :=
  let '(x1_133, y1_134, _) :=
    p_131 in 
  let '(x2_135, y2_136, _) :=
    q_132 in 
  let x_diff_137 :=
    (x2_135) -% (x1_133) in 
  let y_diff_138 :=
    (y2_136) -% (y1_134) in 
  let xovery_139 :=
    (y_diff_138) *% (nat_mod_inv (x_diff_137)) in 
  let x3_140 :=
    ((nat_mod_exp (xovery_139) (repr 2)) -% (x1_133)) -% (x2_135) in 
  let y3_141 :=
    ((xovery_139) *% ((x1_133) -% (x3_140))) -% (y1_134) in 
  (x3_140, y3_141, false).
  
  QuickChick (
    forAll g_g1 (fun p_131 : g1 =>forAll g_g1 (fun q_132 : g1 =>g1add_a p_131) q_132)).

Definition g1double_a (p_142 : g1) : g1 :=
  let '(x1_143, y1_144, _) :=
    p_142 in 
  let x12_145 :=
    nat_mod_exp (x1_143) (repr 2) in 
  let xovery_146 :=
    (
      (
        nat_mod_from_literal (
          0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab) (
          repr 3)) *% (x12_145)) *% (
      nat_mod_inv ((nat_mod_two ) *% (y1_144))) in 
  let x3_147 :=
    (nat_mod_exp (xovery_146) (repr 2)) -% ((nat_mod_two ) *% (x1_143)) in 
  let y3_148 :=
    ((xovery_146) *% ((x1_143) -% (x3_147))) -% (y1_144) in 
  (x3_147, y3_148, false).
  
  QuickChick (forAll g_g1 (fun p_142 : g1 =>g1double_a p_142)).

Definition g1double (p_149 : g1) : g1 :=
  let '(x1_150, y1_151, inf1_152) :=
    p_149 in 
  if (((y1_151) !=.? (nat_mod_zero )) && (negb (inf1_152))):bool then (
    g1double_a (p_149)) else ((nat_mod_zero , nat_mod_zero , true)).
  
  QuickChick (forAll g_g1 (fun p_149 : g1 =>g1double p_149)).

Definition g1add (p_153 : g1) (q_154 : g1) : g1 :=
  let '(x1_155, y1_156, inf1_157) :=
    p_153 in 
  let '(x2_158, y2_159, inf2_160) :=
    q_154 in 
  if (inf1_157):bool then (q_154) else (
    if (inf2_160):bool then (p_153) else (
      if ((p_153) =.? (q_154)):bool then (g1double (p_153)) else (
        if (
          negb (
            ((x1_155) =.? (x2_158)) && (
              (y1_156) =.? ((nat_mod_zero ) -% (y2_159))))):bool then (
          g1add_a (p_153) (q_154)) else (
          (nat_mod_zero , nat_mod_zero , true))))).
  
  QuickChick (
    forAll g_g1 (fun p_153 : g1 =>forAll g_g1 (fun q_154 : g1 =>g1add p_153) q_154)).

Definition g1mul (m_161 : scalar) (p_162 : g1) : g1 :=
  let n_163 :=
    usize 255 in 
  let k_164 :=
    (n_163) - (most_significant_bit (m_161) (n_163)) in 
  let t_165 :=
    p_162 in 
  let t_165 :=
    foldi (k_164) (n_163) (fun i_166 t_165 =>
      let t_165 :=
        g1double (t_165) in 
      let '(t_165) :=
        if nat_mod_bit (m_161) (((n_163) - (i_166)) - (usize 1)):bool then (
          let t_165 :=
            g1add (t_165) (p_162) in 
          (t_165)
        ) else ( (t_165)
        ) in 
      (t_165))
    t_165 in 
  t_165.
  
  QuickChick (
    forAll g_scalar (fun m_161 : scalar =>forAll g_g1 (fun p_162 : g1 =>g1mul m_161) p_162)).

Definition g1neg (p_167 : g1) : g1 :=
  let '(x_168, y_169, inf_170) :=
    p_167 in 
  (x_168, (nat_mod_zero ) -% (y_169), inf_170).
  
  QuickChick (forAll g_g1 (fun p_167 : g1 =>g1neg p_167)).

Definition g2add_a (p_171 : g2) (q_172 : g2) : g2 :=
  let '(x1_173, y1_174, _) :=
    p_171 in 
  let '(x2_175, y2_176, _) :=
    q_172 in 
  let x_diff_177 :=
    fp2sub (x2_175) (x1_173) in 
  let y_diff_178 :=
    fp2sub (y2_176) (y1_174) in 
  let xovery_179 :=
    fp2mul (y_diff_178) (fp2inv (x_diff_177)) in 
  let t1_180 :=
    fp2mul (xovery_179) (xovery_179) in 
  let t2_181 :=
    fp2sub (t1_180) (x1_173) in 
  let x3_182 :=
    fp2sub (t2_181) (x2_175) in 
  let t1_183 :=
    fp2sub (x1_173) (x3_182) in 
  let t2_184 :=
    fp2mul (xovery_179) (t1_183) in 
  let y3_185 :=
    fp2sub (t2_184) (y1_174) in 
  (x3_182, y3_185, false).
  
  QuickChick (
    forAll g_g2 (fun p_171 : g2 =>forAll g_g2 (fun q_172 : g2 =>g2add_a p_171) q_172)).

Definition g2double_a (p_186 : g2) : g2 :=
  let '(x1_187, y1_188, _) :=
    p_186 in 
  let x12_189 :=
    fp2mul (x1_187) (x1_187) in 
  let t1_190 :=
    fp2mul (
      fp2fromfp (
        nat_mod_from_literal (
          0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab) (
          repr 3))) (x12_189) in 
  let t2_191 :=
    fp2inv (fp2mul (fp2fromfp (nat_mod_two )) (y1_188)) in 
  let xovery_192 :=
    fp2mul (t1_190) (t2_191) in 
  let t1_193 :=
    fp2mul (xovery_192) (xovery_192) in 
  let t2_194 :=
    fp2mul (fp2fromfp (nat_mod_two )) (x1_187) in 
  let x3_195 :=
    fp2sub (t1_193) (t2_194) in 
  let t1_196 :=
    fp2sub (x1_187) (x3_195) in 
  let t2_197 :=
    fp2mul (xovery_192) (t1_196) in 
  let y3_198 :=
    fp2sub (t2_197) (y1_188) in 
  (x3_195, y3_198, false).
  
  QuickChick (forAll g_g2 (fun p_186 : g2 =>g2double_a p_186)).

Definition g2double (p_199 : g2) : g2 :=
  let '(x1_200, y1_201, inf1_202) :=
    p_199 in 
  if (((y1_201) !=.? (fp2zero )) && (negb (inf1_202))):bool then (
    g2double_a (p_199)) else ((fp2zero , fp2zero , true)).
  
  QuickChick (forAll g_g2 (fun p_199 : g2 =>g2double p_199)).

Definition g2add (p_203 : g2) (q_204 : g2) : g2 :=
  let '(x1_205, y1_206, inf1_207) :=
    p_203 in 
  let '(x2_208, y2_209, inf2_210) :=
    q_204 in 
  if (inf1_207):bool then (q_204) else (
    if (inf2_210):bool then (p_203) else (
      if ((p_203) =.? (q_204)):bool then (g2double (p_203)) else (
        if (
          negb (
            ((x1_205) =.? (x2_208)) && (
              (y1_206) =.? (fp2neg (y2_209))))):bool then (
          g2add_a (p_203) (q_204)) else ((fp2zero , fp2zero , true))))).
  
  QuickChick (
    forAll g_g2 (fun p_203 : g2 =>forAll g_g2 (fun q_204 : g2 =>g2add p_203) q_204)).

Definition g2mul (m_211 : scalar) (p_212 : g2) : g2 :=
  let n_213 :=
    usize 255 in 
  let k_214 :=
    (n_213) - (most_significant_bit (m_211) (n_213)) in 
  let t_215 :=
    p_212 in 
  let t_215 :=
    foldi (k_214) (n_213) (fun i_216 t_215 =>
      let t_215 :=
        g2double (t_215) in 
      let '(t_215) :=
        if nat_mod_bit (m_211) (((n_213) - (i_216)) - (usize 1)):bool then (
          let t_215 :=
            g2add (t_215) (p_212) in 
          (t_215)
        ) else ( (t_215)
        ) in 
      (t_215))
    t_215 in 
  t_215.
  
  QuickChick (
    forAll g_scalar (fun m_211 : scalar =>forAll g_g2 (fun p_212 : g2 =>g2mul m_211) p_212)).

Definition g2neg (p_217 : g2) : g2 :=
  let '(x_218, y_219, inf_220) :=
    p_217 in 
  (x_218, fp2neg (y_219), inf_220).
  
  QuickChick (forAll g_g2 (fun p_217 : g2 =>g2neg p_217)).

Definition twist (p_221 : g1) : (fp12 × fp12) :=
  let '(p0_222, p1_223, _) :=
    p_221 in 
  let x_224 :=
    ((fp2zero , fp2fromfp (p0_222), fp2zero ), fp6zero ) in 
  let y_225 :=
    (fp6zero , (fp2zero , fp2fromfp (p1_223), fp2zero )) in 
  (x_224, y_225).
  
  QuickChick (forAll g_g1 (fun p_221 : g1 =>twist p_221)).

Definition line_double_p (r_226 : g2) (p_227 : g1) : fp12 :=
  let '(r0_228, r1_229, _) :=
    r_226 in 
  let a_230 :=
    fp2mul (
      fp2fromfp (
        nat_mod_from_literal (
          0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab) (
          repr 3))) (fp2mul (r0_228) (r0_228)) in 
  let a_231 :=
    fp2mul (a_230) (fp2inv (fp2mul (fp2fromfp (nat_mod_two )) (r1_229))) in 
  let b_232 :=
    fp2sub (r1_229) (fp2mul (a_231) (r0_228)) in 
  let a_233 :=
    fp12fromfp6 (fp6fromfp2 (a_231)) in 
  let b_234 :=
    fp12fromfp6 (fp6fromfp2 (b_232)) in 
  let '(x_235, y_236) :=
    twist (p_227) in 
  fp12neg (fp12sub (fp12sub (y_236) (fp12mul (a_233) (x_235))) (b_234)).
  
  QuickChick (
    forAll g_g2 (fun r_226 : g2 =>forAll g_g1 (fun p_227 : g1 =>line_double_p r_226) p_227)).

Definition line_add_p (r_237 : g2) (q_238 : g2) (p_239 : g1) : fp12 :=
  let '(r0_240, r1_241, _) :=
    r_237 in 
  let '(q0_242, q1_243, _) :=
    q_238 in 
  let a_244 :=
    fp2mul (fp2sub (q1_243) (r1_241)) (fp2inv (fp2sub (q0_242) (r0_240))) in 
  let b_245 :=
    fp2sub (r1_241) (fp2mul (a_244) (r0_240)) in 
  let a_246 :=
    fp12fromfp6 (fp6fromfp2 (a_244)) in 
  let b_247 :=
    fp12fromfp6 (fp6fromfp2 (b_245)) in 
  let '(x_248, y_249) :=
    twist (p_239) in 
  fp12neg (fp12sub (fp12sub (y_249) (fp12mul (a_246) (x_248))) (b_247)).
  
  QuickChick (
    forAll g_g2 (fun r_237 : g2 =>forAll g_g2 (fun q_238 : g2 =>forAll g_g1 (fun p_239 : g1 =>line_add_p r_237) q_238) p_239)).

Definition frobenius (f_250 : fp12) : fp12 :=
  let '((g0_251, g1_252, g2_253), (h0_254, h1_255, h2_256)) :=
    f_250 in 
  let t1_257 :=
    fp2conjugate (g0_251) in 
  let t2_258 :=
    fp2conjugate (h0_254) in 
  let t3_259 :=
    fp2conjugate (g1_252) in 
  let t4_260 :=
    fp2conjugate (h1_255) in 
  let t5_261 :=
    fp2conjugate (g2_253) in 
  let t6_262 :=
    fp2conjugate (h2_256) in 
  let c1_263 :=
    array_from_list uint64 (
      let l :=
        [
          secret (repr 10162220747404304312);
          secret (repr 17761815663483519293);
          secret (repr 8873291758750579140);
          secret (repr 1141103941765652303);
          secret (repr 13993175198059990303);
          secret (repr 1802798568193066599)
        ] in  l) in 
  let c1_264 :=
    array_to_le_bytes (c1_263) in 
  let c1_265 :=
    nat_mod_from_byte_seq_le (c1_264) in 
  let c2_266 :=
    array_from_list uint64 (
      let l :=
        [
          secret (repr 3240210268673559283);
          secret (repr 2895069921743240898);
          secret (repr 17009126888523054175);
          secret (repr 6098234018649060207);
          secret (repr 9865672654120263608);
          secret (repr 71000049454473266)
        ] in  l) in 
  let c2_267 :=
    array_to_le_bytes (c2_266) in 
  let c2_268 :=
    nat_mod_from_byte_seq_le (c2_267) in 
  let gamma11_269 :=
    (c1_265, c2_268) in 
  let gamma12_270 :=
    fp2mul (gamma11_269) (gamma11_269) in 
  let gamma13_271 :=
    fp2mul (gamma12_270) (gamma11_269) in 
  let gamma14_272 :=
    fp2mul (gamma13_271) (gamma11_269) in 
  let gamma15_273 :=
    fp2mul (gamma14_272) (gamma11_269) in 
  let t2_274 :=
    fp2mul (t2_258) (gamma11_269) in 
  let t3_275 :=
    fp2mul (t3_259) (gamma12_270) in 
  let t4_276 :=
    fp2mul (t4_260) (gamma13_271) in 
  let t5_277 :=
    fp2mul (t5_261) (gamma14_272) in 
  let t6_278 :=
    fp2mul (t6_262) (gamma15_273) in 
  ((t1_257, t3_275, t5_277), (t2_274, t4_276, t6_278)).
  
  QuickChick (forAll g_fp12 (fun f_250 : fp12 =>frobenius f_250)).

Definition final_exponentiation (f_279 : fp12) : fp12 :=
  let fp6_280 :=
    fp12conjugate (f_279) in 
  let finv_281 :=
    fp12inv (f_279) in 
  let fp6_1_282 :=
    fp12mul (fp6_280) (finv_281) in 
  let fp8_283 :=
    frobenius (frobenius (fp6_1_282)) in 
  let f_284 :=
    fp12mul (fp8_283) (fp6_1_282) in 
  let u_285 :=
    nat_mod_from_literal (
      0x8000000000000000000000000000000000000000000000000000000000000000) (
      repr 15132376222941642752) in 
  let t0_286 :=
    fp12mul (f_284) (f_284) in 
  let t1_287 :=
    fp12exp (t0_286) (u_285) in 
  let t1_288 :=
    fp12conjugate (t1_287) in 
  let t2_289 :=
    fp12exp (t1_288) ((u_285) /% (nat_mod_two )) in 
  let t2_290 :=
    fp12conjugate (t2_289) in 
  let t3_291 :=
    fp12conjugate (f_284) in 
  let t1_292 :=
    fp12mul (t3_291) (t1_288) in 
  let t1_293 :=
    fp12conjugate (t1_292) in 
  let t1_294 :=
    fp12mul (t1_293) (t2_290) in 
  let t2_295 :=
    fp12exp (t1_294) (u_285) in 
  let t2_296 :=
    fp12conjugate (t2_295) in 
  let t3_297 :=
    fp12exp (t2_296) (u_285) in 
  let t3_298 :=
    fp12conjugate (t3_297) in 
  let t1_299 :=
    fp12conjugate (t1_294) in 
  let t3_300 :=
    fp12mul (t1_299) (t3_298) in 
  let t1_301 :=
    fp12conjugate (t1_299) in 
  let t1_302 :=
    frobenius (frobenius (frobenius (t1_301))) in 
  let t2_303 :=
    frobenius (frobenius (t2_296)) in 
  let t1_304 :=
    fp12mul (t1_302) (t2_303) in 
  let t2_305 :=
    fp12exp (t3_300) (u_285) in 
  let t2_306 :=
    fp12conjugate (t2_305) in 
  let t2_307 :=
    fp12mul (t2_306) (t0_286) in 
  let t2_308 :=
    fp12mul (t2_307) (f_284) in 
  let t1_309 :=
    fp12mul (t1_304) (t2_308) in 
  let t2_310 :=
    frobenius (t3_300) in 
  let t1_311 :=
    fp12mul (t1_309) (t2_310) in 
  t1_311.
  
  QuickChick (forAll g_fp12 (fun f_279 : fp12 =>final_exponentiation f_279)).

Definition pairing (p_312 : g1) (q_313 : g2) : fp12 :=
  let t_314 :=
    nat_mod_from_literal (
      0x8000000000000000000000000000000000000000000000000000000000000000) (
      repr 15132376222941642752) in 
  let r_315 :=
    q_313 in 
  let f_316 :=
    fp12fromfp6 (fp6fromfp2 (fp2fromfp (nat_mod_one ))) in 
  let '(r_315, f_316) :=
    foldi (usize 1) (usize 64) (fun i_317 '(r_315, f_316) =>
      let lrr_318 :=
        line_double_p (r_315) (p_312) in 
      let r_315 :=
        g2double (r_315) in 
      let f_316 :=
        fp12mul (fp12mul (f_316) (f_316)) (lrr_318) in 
      let '(r_315, f_316) :=
        if nat_mod_bit (t_314) (((usize 64) - (i_317)) - (usize 1)):bool then (
          let lrq_319 :=
            line_add_p (r_315) (q_313) (p_312) in 
          let r_315 :=
            g2add (r_315) (q_313) in 
          let f_316 :=
            fp12mul (f_316) (lrq_319) in 
          (r_315, f_316)
        ) else ( (r_315, f_316)
        ) in 
      (r_315, f_316))
    (r_315, f_316) in 
  final_exponentiation (fp12conjugate (f_316)).
  
  QuickChick (
    forAll g_g1 (fun p_312 : g1 =>forAll g_g2 (fun q_313 : g2 =>pairing p_312) q_313)).

Definition test_fp2_prop_add_neg (a_320 : fp2) : bool :=
  let b_321 :=
    fp2neg (a_320) in 
  (fp2fromfp (nat_mod_zero )) =.? (fp2add (a_320) (b_321)).
  
  QuickChick (forAll g_fp2 (fun a_320 : fp2 =>test_fp2_prop_add_neg a_320)).

Definition test_fp2_prop_mul_inv (a_322 : fp2) : bool :=
  let b_323 :=
    fp2inv (a_322) in 
  (fp2fromfp (nat_mod_one )) =.? (fp2mul (a_322) (b_323)).
  
  QuickChick (forAll g_fp2 (fun a_322 : fp2 =>test_fp2_prop_mul_inv a_322)).

Definition test_extraction_issue  : bool :=
  let b_324 :=
    fp2inv ((nat_mod_one , nat_mod_one )) in 
  (fp2fromfp (nat_mod_one )) =.? (
    fp2mul ((nat_mod_one , nat_mod_one )) (b_324)).
  
  QuickChick (test_extraction_issue).

Definition test_fp6_prop_mul_inv (a_325 : fp6) : bool :=
  let b_326 :=
    fp6inv (a_325) in 
  (fp6fromfp2 (fp2fromfp (nat_mod_one ))) =.? (fp6mul (a_325) (b_326)).
  
  QuickChick (forAll g_fp6 (fun a_325 : fp6 =>test_fp6_prop_mul_inv a_325)).

Definition test_fp6_prop_add_neg (a_327 : fp6) : bool :=
  let b_328 :=
    fp6neg (a_327) in 
  (fp6fromfp2 (fp2fromfp (nat_mod_zero ))) =.? (fp6add (a_327) (b_328)).
  
  QuickChick (forAll g_fp6 (fun a_327 : fp6 =>test_fp6_prop_add_neg a_327)).

Definition test_fp12_prop_add_neg (a_329 : fp12) : bool :=
  let b_330 :=
    fp12neg (a_329) in 
  (fp12fromfp6 (fp6fromfp2 (fp2fromfp (nat_mod_zero )))) =.? (
    fp12add (a_329) (b_330)).
  
  QuickChick (forAll g_fp12 (fun a_329 : fp12 =>test_fp12_prop_add_neg a_329)).

Definition test_fp12_prop_mul_inv (a_331 : fp12) : bool :=
  let b_332 :=
    fp12inv (a_331) in 
  (fp12fromfp6 (fp6fromfp2 (fp2fromfp (nat_mod_one )))) =.? (
    fp12mul (a_331) (b_332)).
  
  QuickChick (forAll g_fp12 (fun a_331 : fp12 =>test_fp12_prop_mul_inv a_331)).

