Require Import Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
Require Import Hacspec.Lib.

Definition fp_canvas := nseq (int8) (48).
Definition fp :=
  nat_mod 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab.

Definition serialized_fp := nseq (uint8) (usize 48).

Definition array_fp := nseq (uint64) (usize 6).

Definition scalar_canvas := nseq (int8) (32).
Definition scalar :=
  nat_mod 0x8000000000000000000000000000000000000000000000000000000000000000.

Definition most_significant_bit (m_0 : scalar) (n_1 : uint_size) : uint_size :=
  if (((n_1) >.? (usize 0)) && (negb (nat_mod_bit (m_0) (n_1)))):bool then (
    most_significant_bit (m_0) ((n_1) - (usize 1))) else (n_1).

Notation "'g1'" := ((fp × fp × bool)) : hacspec_scope.

Notation "'fp2'" := ((fp × fp)) : hacspec_scope.

Notation "'g2'" := ((fp2 × fp2 × bool)) : hacspec_scope.

Notation "'fp6'" := ((fp2 × fp2 × fp2)) : hacspec_scope.

Notation "'fp12'" := ((fp6 × fp6)) : hacspec_scope.

Definition fp2fromfp (n_2 : fp) : fp2 :=
  (n_2, nat_mod_zero ).

Definition fp2zero  : fp2 :=
  fp2fromfp (nat_mod_zero ).

Definition fp2neg (n_3 : fp2) : fp2 :=
  let '(n1_4, n2_5) :=
    n_3 in 
  ((nat_mod_zero ) -% (n1_4), (nat_mod_zero ) -% (n2_5)).

Definition fp2add (n_6 : fp2) (m_7 : fp2) : fp2 :=
  let '(n1_8, n2_9) :=
    n_6 in 
  let '(m1_10, m2_11) :=
    m_7 in 
  ((n1_8) +% (m1_10), (n2_9) +% (m2_11)).

Definition fp2sub (n_12 : fp2) (m_13 : fp2) : fp2 :=
  fp2add (n_12) (fp2neg (m_13)).

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

Definition fp2conjugate (n_29 : fp2) : fp2 :=
  let '(n1_30, n2_31) :=
    n_29 in 
  (n1_30, (nat_mod_zero ) -% (n2_31)).

Definition fp6fromfp2 (n_32 : fp2) : fp6 :=
  (n_32, fp2zero , fp2zero ).

Definition fp6zero  : fp6 :=
  fp6fromfp2 (fp2zero ).

Definition fp6neg (n_33 : fp6) : fp6 :=
  let '(n1_34, n2_35, n3_36) :=
    n_33 in 
  (
    fp2sub (fp2zero ) (n1_34),
    fp2sub (fp2zero ) (n2_35),
    fp2sub (fp2zero ) (n3_36)
  ).

Definition fp6add (n_37 : fp6) (m_38 : fp6) : fp6 :=
  let '(n1_39, n2_40, n3_41) :=
    n_37 in 
  let '(m1_42, m2_43, m3_44) :=
    m_38 in 
  (fp2add (n1_39) (m1_42), fp2add (n2_40) (m2_43), fp2add (n3_41) (m3_44)).

Definition fp6sub (n_45 : fp6) (m_46 : fp6) : fp6 :=
  fp6add (n_45) (fp6neg (m_46)).

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

Definition fp12fromfp6 (n_89 : fp6) : fp12 :=
  (n_89, fp6zero ).

Definition fp12neg (n_90 : fp12) : fp12 :=
  let '(n1_91, n2_92) :=
    n_90 in 
  (fp6sub (fp6zero ) (n1_91), fp6sub (fp6zero ) (n2_92)).

Definition fp12add (n_93 : fp12) (m_94 : fp12) : fp12 :=
  let '(n1_95, n2_96) :=
    n_93 in 
  let '(m1_97, m2_98) :=
    m_94 in 
  (fp6add (n1_95) (m1_97), fp6add (n2_96) (m2_98)).

Definition fp12sub (n_99 : fp12) (m_100 : fp12) : fp12 :=
  fp12add (n_99) (fp12neg (m_100)).

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

Definition fp12conjugate (n_128 : fp12) : fp12 :=
  let '(n1_129, n2_130) :=
    n_128 in 
  (n1_129, fp6neg (n2_130)).

Definition fp12zero  : fp12 :=
  fp12fromfp6 (fp6zero ).

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

Definition g1add (p_149 : g1) (q_150 : g1) : g1 :=
  let '(x1_151, y1_152, inf1_153) :=
    p_149 in 
  let '(x2_154, y2_155, inf2_156) :=
    q_150 in 
  if (inf1_153):bool then (q_150) else (
    if (inf2_156):bool then (p_149) else (
      if ((p_149) =.? (q_150)):bool then (g1double_a (p_149)) else (
        if (
          negb (
            ((x1_151) =.? (x2_154)) && (
              (y1_152) =.? ((nat_mod_zero ) -% (y2_155))))):bool then (
          g1add_a (p_149) (q_150)) else (
          (nat_mod_zero , nat_mod_zero , true))))).

Definition g1double (p_157 : g1) : g1 :=
  let '(x1_158, y1_159, inf1_160) :=
    p_157 in 
  if (((y1_159) !=.? (nat_mod_zero )) && (negb (inf1_160))):bool then (
    g1double_a (p_157)) else ((nat_mod_zero , nat_mod_zero , true)).

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

Definition g1neg (p_167 : g1) : g1 :=
  let '(x_168, y_169, inf_170) :=
    p_167 in 
  (x_168, (nat_mod_zero ) -% (y_169), inf_170).

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

Definition g2add (p_199 : g2) (q_200 : g2) : g2 :=
  let '(x1_201, y1_202, inf1_203) :=
    p_199 in 
  let '(x2_204, y2_205, inf2_206) :=
    q_200 in 
  if (inf1_203):bool then (q_200) else (
    if (inf2_206):bool then (p_199) else (
      if ((p_199) =.? (q_200)):bool then (g2double_a (p_199)) else (
        if (
          negb (
            ((x1_201) =.? (x2_204)) && (
              (y1_202) =.? (fp2neg (y2_205))))):bool then (
          g2add_a (p_199) (q_200)) else ((fp2zero , fp2zero , true))))).

Definition g2double (p_207 : g2) : g2 :=
  let '(x1_208, y1_209, inf1_210) :=
    p_207 in 
  if (((y1_209) !=.? (fp2zero )) && (negb (inf1_210))):bool then (
    g2double_a (p_207)) else ((fp2zero , fp2zero , true)).

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

Definition g2neg (p_217 : g2) : g2 :=
  let '(x_218, y_219, inf_220) :=
    p_217 in 
  (x_218, fp2neg (y_219), inf_220).

Definition twist (p_221 : g1) : (fp12 × fp12) :=
  let '(p0_222, p1_223, _) :=
    p_221 in 
  let x_224 :=
    ((fp2zero , fp2fromfp (p0_222), fp2zero ), fp6zero ) in 
  let y_225 :=
    (fp6zero , (fp2zero , fp2fromfp (p1_223), fp2zero )) in 
  (x_224, y_225).

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

