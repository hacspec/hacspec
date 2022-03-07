(** This file was automatically generated using Hacspec **)
From Crypt Require Import choice_type Package Prelude.
Import PackageNotation.
From extructures Require Import ord fset.
From CoqWord Require Import ssrZ word.
From Jasmin Require Import word.
Require Import ChoiceEquality.

Require Import Hacspec_Lib.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope list_scope.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.


Obligation Tactic :=
(intros ; do 2 ssprove_valid'_2) ||
(try (Tactics.program_simpl; fail); simpl). (* Old Obligation Tactic *)

Require Import Hacspec_Lib.

Definition blocksize_v : (uint_size) :=
  ((usize 16)).

Definition ivsize_v : (uint_size) :=
  ((usize 12)).

Definition key_length_v : (uint_size) :=
  ((usize 4)).

Definition rounds_v : (uint_size) :=
  ((usize 10)).

Definition key_schedule_length_v : (uint_size) :=
  ((usize 176)).

Definition iterations_v : (uint_size) :=
  ((usize 40)).

Definition invalid_key_expansion_index_v : (int8) :=
  ((@repr U8 1)).

Definition block_t := nseq (uint8) (blocksize_v).

Definition word_t := nseq (uint8) (key_length_v).

Definition round_key_t := nseq (uint8) (blocksize_v).

Definition aes_nonce_t := nseq (uint8) (ivsize_v).

Definition s_box_t := nseq (uint8) (usize 256).

Definition r_con_t := nseq (uint8) (usize 15).

Definition bytes144_t := nseq (uint8) (usize 144).

Definition bytes176_t := nseq (uint8) (key_schedule_length_v).

Definition key128_t := nseq (uint8) (blocksize_v).

Notation "'byte_seq_result_t'" := ((result byte_seq int8)) : hacspec_scope.

Notation "'block_result_t'" := ((result block_t int8)) : hacspec_scope.

Notation "'word_result_t'" := ((result word_t int8)) : hacspec_scope.

Definition sbox_v : (s_box_t) :=
  (let temp_0 : int8 :=
      (secret_pure (@repr U8 99)) in
    let temp_1 : int8 :=
      (secret_pure (@repr U8 124)) in
    let temp_2 : int8 :=
      (secret_pure (@repr U8 119)) in
    let temp_3 : int8 :=
      (secret_pure (@repr U8 123)) in
    let temp_4 : int8 :=
      (secret_pure (@repr U8 242)) in
    let temp_5 : int8 :=
      (secret_pure (@repr U8 107)) in
    let temp_6 : int8 :=
      (secret_pure (@repr U8 111)) in
    let temp_7 : int8 :=
      (secret_pure (@repr U8 197)) in
    let temp_8 : int8 :=
      (secret_pure (@repr U8 48)) in
    let temp_9 : int8 :=
      (secret_pure (@repr U8 1)) in
    let temp_10 : int8 :=
      (secret_pure (@repr U8 103)) in
    let temp_11 : int8 :=
      (secret_pure (@repr U8 43)) in
    let temp_12 : int8 :=
      (secret_pure (@repr U8 254)) in
    let temp_13 : int8 :=
      (secret_pure (@repr U8 215)) in
    let temp_14 : int8 :=
      (secret_pure (@repr U8 171)) in
    let temp_15 : int8 :=
      (secret_pure (@repr U8 118)) in
    let temp_16 : int8 :=
      (secret_pure (@repr U8 202)) in
    let temp_17 : int8 :=
      (secret_pure (@repr U8 130)) in
    let temp_18 : int8 :=
      (secret_pure (@repr U8 201)) in
    let temp_19 : int8 :=
      (secret_pure (@repr U8 125)) in
    let temp_20 : int8 :=
      (secret_pure (@repr U8 250)) in
    let temp_21 : int8 :=
      (secret_pure (@repr U8 89)) in
    let temp_22 : int8 :=
      (secret_pure (@repr U8 71)) in
    let temp_23 : int8 :=
      (secret_pure (@repr U8 240)) in
    let temp_24 : int8 :=
      (secret_pure (@repr U8 173)) in
    let temp_25 : int8 :=
      (secret_pure (@repr U8 212)) in
    let temp_26 : int8 :=
      (secret_pure (@repr U8 162)) in
    let temp_27 : int8 :=
      (secret_pure (@repr U8 175)) in
    let temp_28 : int8 :=
      (secret_pure (@repr U8 156)) in
    let temp_29 : int8 :=
      (secret_pure (@repr U8 164)) in
    let temp_30 : int8 :=
      (secret_pure (@repr U8 114)) in
    let temp_31 : int8 :=
      (secret_pure (@repr U8 192)) in
    let temp_32 : int8 :=
      (secret_pure (@repr U8 183)) in
    let temp_33 : int8 :=
      (secret_pure (@repr U8 253)) in
    let temp_34 : int8 :=
      (secret_pure (@repr U8 147)) in
    let temp_35 : int8 :=
      (secret_pure (@repr U8 38)) in
    let temp_36 : int8 :=
      (secret_pure (@repr U8 54)) in
    let temp_37 : int8 :=
      (secret_pure (@repr U8 63)) in
    let temp_38 : int8 :=
      (secret_pure (@repr U8 247)) in
    let temp_39 : int8 :=
      (secret_pure (@repr U8 204)) in
    let temp_40 : int8 :=
      (secret_pure (@repr U8 52)) in
    let temp_41 : int8 :=
      (secret_pure (@repr U8 165)) in
    let temp_42 : int8 :=
      (secret_pure (@repr U8 229)) in
    let temp_43 : int8 :=
      (secret_pure (@repr U8 241)) in
    let temp_44 : int8 :=
      (secret_pure (@repr U8 113)) in
    let temp_45 : int8 :=
      (secret_pure (@repr U8 216)) in
    let temp_46 : int8 :=
      (secret_pure (@repr U8 49)) in
    let temp_47 : int8 :=
      (secret_pure (@repr U8 21)) in
    let temp_48 : int8 :=
      (secret_pure (@repr U8 4)) in
    let temp_49 : int8 :=
      (secret_pure (@repr U8 199)) in
    let temp_50 : int8 :=
      (secret_pure (@repr U8 35)) in
    let temp_51 : int8 :=
      (secret_pure (@repr U8 195)) in
    let temp_52 : int8 :=
      (secret_pure (@repr U8 24)) in
    let temp_53 : int8 :=
      (secret_pure (@repr U8 150)) in
    let temp_54 : int8 :=
      (secret_pure (@repr U8 5)) in
    let temp_55 : int8 :=
      (secret_pure (@repr U8 154)) in
    let temp_56 : int8 :=
      (secret_pure (@repr U8 7)) in
    let temp_57 : int8 :=
      (secret_pure (@repr U8 18)) in
    let temp_58 : int8 :=
      (secret_pure (@repr U8 128)) in
    let temp_59 : int8 :=
      (secret_pure (@repr U8 226)) in
    let temp_60 : int8 :=
      (secret_pure (@repr U8 235)) in
    let temp_61 : int8 :=
      (secret_pure (@repr U8 39)) in
    let temp_62 : int8 :=
      (secret_pure (@repr U8 178)) in
    let temp_63 : int8 :=
      (secret_pure (@repr U8 117)) in
    let temp_64 : int8 :=
      (secret_pure (@repr U8 9)) in
    let temp_65 : int8 :=
      (secret_pure (@repr U8 131)) in
    let temp_66 : int8 :=
      (secret_pure (@repr U8 44)) in
    let temp_67 : int8 :=
      (secret_pure (@repr U8 26)) in
    let temp_68 : int8 :=
      (secret_pure (@repr U8 27)) in
    let temp_69 : int8 :=
      (secret_pure (@repr U8 110)) in
    let temp_70 : int8 :=
      (secret_pure (@repr U8 90)) in
    let temp_71 : int8 :=
      (secret_pure (@repr U8 160)) in
    let temp_72 : int8 :=
      (secret_pure (@repr U8 82)) in
    let temp_73 : int8 :=
      (secret_pure (@repr U8 59)) in
    let temp_74 : int8 :=
      (secret_pure (@repr U8 214)) in
    let temp_75 : int8 :=
      (secret_pure (@repr U8 179)) in
    let temp_76 : int8 :=
      (secret_pure (@repr U8 41)) in
    let temp_77 : int8 :=
      (secret_pure (@repr U8 227)) in
    let temp_78 : int8 :=
      (secret_pure (@repr U8 47)) in
    let temp_79 : int8 :=
      (secret_pure (@repr U8 132)) in
    let temp_80 : int8 :=
      (secret_pure (@repr U8 83)) in
    let temp_81 : int8 :=
      (secret_pure (@repr U8 209)) in
    let temp_82 : int8 :=
      (secret_pure (@repr U8 0)) in
    let temp_83 : int8 :=
      (secret_pure (@repr U8 237)) in
    let temp_84 : int8 :=
      (secret_pure (@repr U8 32)) in
    let temp_85 : int8 :=
      (secret_pure (@repr U8 252)) in
    let temp_86 : int8 :=
      (secret_pure (@repr U8 177)) in
    let temp_87 : int8 :=
      (secret_pure (@repr U8 91)) in
    let temp_88 : int8 :=
      (secret_pure (@repr U8 106)) in
    let temp_89 : int8 :=
      (secret_pure (@repr U8 203)) in
    let temp_90 : int8 :=
      (secret_pure (@repr U8 190)) in
    let temp_91 : int8 :=
      (secret_pure (@repr U8 57)) in
    let temp_92 : int8 :=
      (secret_pure (@repr U8 74)) in
    let temp_93 : int8 :=
      (secret_pure (@repr U8 76)) in
    let temp_94 : int8 :=
      (secret_pure (@repr U8 88)) in
    let temp_95 : int8 :=
      (secret_pure (@repr U8 207)) in
    let temp_96 : int8 :=
      (secret_pure (@repr U8 208)) in
    let temp_97 : int8 :=
      (secret_pure (@repr U8 239)) in
    let temp_98 : int8 :=
      (secret_pure (@repr U8 170)) in
    let temp_99 : int8 :=
      (secret_pure (@repr U8 251)) in
    let temp_100 : int8 :=
      (secret_pure (@repr U8 67)) in
    let temp_101 : int8 :=
      (secret_pure (@repr U8 77)) in
    let temp_102 : int8 :=
      (secret_pure (@repr U8 51)) in
    let temp_103 : int8 :=
      (secret_pure (@repr U8 133)) in
    let temp_104 : int8 :=
      (secret_pure (@repr U8 69)) in
    let temp_105 : int8 :=
      (secret_pure (@repr U8 249)) in
    let temp_106 : int8 :=
      (secret_pure (@repr U8 2)) in
    let temp_107 : int8 :=
      (secret_pure (@repr U8 127)) in
    let temp_108 : int8 :=
      (secret_pure (@repr U8 80)) in
    let temp_109 : int8 :=
      (secret_pure (@repr U8 60)) in
    let temp_110 : int8 :=
      (secret_pure (@repr U8 159)) in
    let temp_111 : int8 :=
      (secret_pure (@repr U8 168)) in
    let temp_112 : int8 :=
      (secret_pure (@repr U8 81)) in
    let temp_113 : int8 :=
      (secret_pure (@repr U8 163)) in
    let temp_114 : int8 :=
      (secret_pure (@repr U8 64)) in
    let temp_115 : int8 :=
      (secret_pure (@repr U8 143)) in
    let temp_116 : int8 :=
      (secret_pure (@repr U8 146)) in
    let temp_117 : int8 :=
      (secret_pure (@repr U8 157)) in
    let temp_118 : int8 :=
      (secret_pure (@repr U8 56)) in
    let temp_119 : int8 :=
      (secret_pure (@repr U8 245)) in
    let temp_120 : int8 :=
      (secret_pure (@repr U8 188)) in
    let temp_121 : int8 :=
      (secret_pure (@repr U8 182)) in
    let temp_122 : int8 :=
      (secret_pure (@repr U8 218)) in
    let temp_123 : int8 :=
      (secret_pure (@repr U8 33)) in
    let temp_124 : int8 :=
      (secret_pure (@repr U8 16)) in
    let temp_125 : int8 :=
      (secret_pure (@repr U8 255)) in
    let temp_126 : int8 :=
      (secret_pure (@repr U8 243)) in
    let temp_127 : int8 :=
      (secret_pure (@repr U8 210)) in
    let temp_128 : int8 :=
      (secret_pure (@repr U8 205)) in
    let temp_129 : int8 :=
      (secret_pure (@repr U8 12)) in
    let temp_130 : int8 :=
      (secret_pure (@repr U8 19)) in
    let temp_131 : int8 :=
      (secret_pure (@repr U8 236)) in
    let temp_132 : int8 :=
      (secret_pure (@repr U8 95)) in
    let temp_133 : int8 :=
      (secret_pure (@repr U8 151)) in
    let temp_134 : int8 :=
      (secret_pure (@repr U8 68)) in
    let temp_135 : int8 :=
      (secret_pure (@repr U8 23)) in
    let temp_136 : int8 :=
      (secret_pure (@repr U8 196)) in
    let temp_137 : int8 :=
      (secret_pure (@repr U8 167)) in
    let temp_138 : int8 :=
      (secret_pure (@repr U8 126)) in
    let temp_139 : int8 :=
      (secret_pure (@repr U8 61)) in
    let temp_140 : int8 :=
      (secret_pure (@repr U8 100)) in
    let temp_141 : int8 :=
      (secret_pure (@repr U8 93)) in
    let temp_142 : int8 :=
      (secret_pure (@repr U8 25)) in
    let temp_143 : int8 :=
      (secret_pure (@repr U8 115)) in
    let temp_144 : int8 :=
      (secret_pure (@repr U8 96)) in
    let temp_145 : int8 :=
      (secret_pure (@repr U8 129)) in
    let temp_146 : int8 :=
      (secret_pure (@repr U8 79)) in
    let temp_147 : int8 :=
      (secret_pure (@repr U8 220)) in
    let temp_148 : int8 :=
      (secret_pure (@repr U8 34)) in
    let temp_149 : int8 :=
      (secret_pure (@repr U8 42)) in
    let temp_150 : int8 :=
      (secret_pure (@repr U8 144)) in
    let temp_151 : int8 :=
      (secret_pure (@repr U8 136)) in
    let temp_152 : int8 :=
      (secret_pure (@repr U8 70)) in
    let temp_153 : int8 :=
      (secret_pure (@repr U8 238)) in
    let temp_154 : int8 :=
      (secret_pure (@repr U8 184)) in
    let temp_155 : int8 :=
      (secret_pure (@repr U8 20)) in
    let temp_156 : int8 :=
      (secret_pure (@repr U8 222)) in
    let temp_157 : int8 :=
      (secret_pure (@repr U8 94)) in
    let temp_158 : int8 :=
      (secret_pure (@repr U8 11)) in
    let temp_159 : int8 :=
      (secret_pure (@repr U8 219)) in
    let temp_160 : int8 :=
      (secret_pure (@repr U8 224)) in
    let temp_161 : int8 :=
      (secret_pure (@repr U8 50)) in
    let temp_162 : int8 :=
      (secret_pure (@repr U8 58)) in
    let temp_163 : int8 :=
      (secret_pure (@repr U8 10)) in
    let temp_164 : int8 :=
      (secret_pure (@repr U8 73)) in
    let temp_165 : int8 :=
      (secret_pure (@repr U8 6)) in
    let temp_166 : int8 :=
      (secret_pure (@repr U8 36)) in
    let temp_167 : int8 :=
      (secret_pure (@repr U8 92)) in
    let temp_168 : int8 :=
      (secret_pure (@repr U8 194)) in
    let temp_169 : int8 :=
      (secret_pure (@repr U8 211)) in
    let temp_170 : int8 :=
      (secret_pure (@repr U8 172)) in
    let temp_171 : int8 :=
      (secret_pure (@repr U8 98)) in
    let temp_172 : int8 :=
      (secret_pure (@repr U8 145)) in
    let temp_173 : int8 :=
      (secret_pure (@repr U8 149)) in
    let temp_174 : int8 :=
      (secret_pure (@repr U8 228)) in
    let temp_175 : int8 :=
      (secret_pure (@repr U8 121)) in
    let temp_176 : int8 :=
      (secret_pure (@repr U8 231)) in
    let temp_177 : int8 :=
      (secret_pure (@repr U8 200)) in
    let temp_178 : int8 :=
      (secret_pure (@repr U8 55)) in
    let temp_179 : int8 :=
      (secret_pure (@repr U8 109)) in
    let temp_180 : int8 :=
      (secret_pure (@repr U8 141)) in
    let temp_181 : int8 :=
      (secret_pure (@repr U8 213)) in
    let temp_182 : int8 :=
      (secret_pure (@repr U8 78)) in
    let temp_183 : int8 :=
      (secret_pure (@repr U8 169)) in
    let temp_184 : int8 :=
      (secret_pure (@repr U8 108)) in
    let temp_185 : int8 :=
      (secret_pure (@repr U8 86)) in
    let temp_186 : int8 :=
      (secret_pure (@repr U8 244)) in
    let temp_187 : int8 :=
      (secret_pure (@repr U8 234)) in
    let temp_188 : int8 :=
      (secret_pure (@repr U8 101)) in
    let temp_189 : int8 :=
      (secret_pure (@repr U8 122)) in
    let temp_190 : int8 :=
      (secret_pure (@repr U8 174)) in
    let temp_191 : int8 :=
      (secret_pure (@repr U8 8)) in
    let temp_192 : int8 :=
      (secret_pure (@repr U8 186)) in
    let temp_193 : int8 :=
      (secret_pure (@repr U8 120)) in
    let temp_194 : int8 :=
      (secret_pure (@repr U8 37)) in
    let temp_195 : int8 :=
      (secret_pure (@repr U8 46)) in
    let temp_196 : int8 :=
      (secret_pure (@repr U8 28)) in
    let temp_197 : int8 :=
      (secret_pure (@repr U8 166)) in
    let temp_198 : int8 :=
      (secret_pure (@repr U8 180)) in
    let temp_199 : int8 :=
      (secret_pure (@repr U8 198)) in
    let temp_200 : int8 :=
      (secret_pure (@repr U8 232)) in
    let temp_201 : int8 :=
      (secret_pure (@repr U8 221)) in
    let temp_202 : int8 :=
      (secret_pure (@repr U8 116)) in
    let temp_203 : int8 :=
      (secret_pure (@repr U8 31)) in
    let temp_204 : int8 :=
      (secret_pure (@repr U8 75)) in
    let temp_205 : int8 :=
      (secret_pure (@repr U8 189)) in
    let temp_206 : int8 :=
      (secret_pure (@repr U8 139)) in
    let temp_207 : int8 :=
      (secret_pure (@repr U8 138)) in
    let temp_208 : int8 :=
      (secret_pure (@repr U8 112)) in
    let temp_209 : int8 :=
      (secret_pure (@repr U8 62)) in
    let temp_210 : int8 :=
      (secret_pure (@repr U8 181)) in
    let temp_211 : int8 :=
      (secret_pure (@repr U8 102)) in
    let temp_212 : int8 :=
      (secret_pure (@repr U8 72)) in
    let temp_213 : int8 :=
      (secret_pure (@repr U8 3)) in
    let temp_214 : int8 :=
      (secret_pure (@repr U8 246)) in
    let temp_215 : int8 :=
      (secret_pure (@repr U8 14)) in
    let temp_216 : int8 :=
      (secret_pure (@repr U8 97)) in
    let temp_217 : int8 :=
      (secret_pure (@repr U8 53)) in
    let temp_218 : int8 :=
      (secret_pure (@repr U8 87)) in
    let temp_219 : int8 :=
      (secret_pure (@repr U8 185)) in
    let temp_220 : int8 :=
      (secret_pure (@repr U8 134)) in
    let temp_221 : int8 :=
      (secret_pure (@repr U8 193)) in
    let temp_222 : int8 :=
      (secret_pure (@repr U8 29)) in
    let temp_223 : int8 :=
      (secret_pure (@repr U8 158)) in
    let temp_224 : int8 :=
      (secret_pure (@repr U8 225)) in
    let temp_225 : int8 :=
      (secret_pure (@repr U8 248)) in
    let temp_226 : int8 :=
      (secret_pure (@repr U8 152)) in
    let temp_227 : int8 :=
      (secret_pure (@repr U8 17)) in
    let temp_228 : int8 :=
      (secret_pure (@repr U8 105)) in
    let temp_229 : int8 :=
      (secret_pure (@repr U8 217)) in
    let temp_230 : int8 :=
      (secret_pure (@repr U8 142)) in
    let temp_231 : int8 :=
      (secret_pure (@repr U8 148)) in
    let temp_232 : int8 :=
      (secret_pure (@repr U8 155)) in
    let temp_233 : int8 :=
      (secret_pure (@repr U8 30)) in
    let temp_234 : int8 :=
      (secret_pure (@repr U8 135)) in
    let temp_235 : int8 :=
      (secret_pure (@repr U8 233)) in
    let temp_236 : int8 :=
      (secret_pure (@repr U8 206)) in
    let temp_237 : int8 :=
      (secret_pure (@repr U8 85)) in
    let temp_238 : int8 :=
      (secret_pure (@repr U8 40)) in
    let temp_239 : int8 :=
      (secret_pure (@repr U8 223)) in
    let temp_240 : int8 :=
      (secret_pure (@repr U8 140)) in
    let temp_241 : int8 :=
      (secret_pure (@repr U8 161)) in
    let temp_242 : int8 :=
      (secret_pure (@repr U8 137)) in
    let temp_243 : int8 :=
      (secret_pure (@repr U8 13)) in
    let temp_244 : int8 :=
      (secret_pure (@repr U8 191)) in
    let temp_245 : int8 :=
      (secret_pure (@repr U8 230)) in
    let temp_246 : int8 :=
      (secret_pure (@repr U8 66)) in
    let temp_247 : int8 :=
      (secret_pure (@repr U8 104)) in
    let temp_248 : int8 :=
      (secret_pure (@repr U8 65)) in
    let temp_249 : int8 :=
      (secret_pure (@repr U8 153)) in
    let temp_250 : int8 :=
      (secret_pure (@repr U8 45)) in
    let temp_251 : int8 :=
      (secret_pure (@repr U8 15)) in
    let temp_252 : int8 :=
      (secret_pure (@repr U8 176)) in
    let temp_253 : int8 :=
      (secret_pure (@repr U8 84)) in
    let temp_254 : int8 :=
      (secret_pure (@repr U8 187)) in
    let temp_255 : int8 :=
      (secret_pure (@repr U8 22)) in
    (array_from_list uint8 (let l :=
          ([
              temp_0;
              temp_1;
              temp_2;
              temp_3;
              temp_4;
              temp_5;
              temp_6;
              temp_7;
              temp_8;
              temp_9;
              temp_10;
              temp_11;
              temp_12;
              temp_13;
              temp_14;
              temp_15;
              temp_16;
              temp_17;
              temp_18;
              temp_19;
              temp_20;
              temp_21;
              temp_22;
              temp_23;
              temp_24;
              temp_25;
              temp_26;
              temp_27;
              temp_28;
              temp_29;
              temp_30;
              temp_31;
              temp_32;
              temp_33;
              temp_34;
              temp_35;
              temp_36;
              temp_37;
              temp_38;
              temp_39;
              temp_40;
              temp_41;
              temp_42;
              temp_43;
              temp_44;
              temp_45;
              temp_46;
              temp_47;
              temp_48;
              temp_49;
              temp_50;
              temp_51;
              temp_52;
              temp_53;
              temp_54;
              temp_55;
              temp_56;
              temp_57;
              temp_58;
              temp_59;
              temp_60;
              temp_61;
              temp_62;
              temp_63;
              temp_64;
              temp_65;
              temp_66;
              temp_67;
              temp_68;
              temp_69;
              temp_70;
              temp_71;
              temp_72;
              temp_73;
              temp_74;
              temp_75;
              temp_76;
              temp_77;
              temp_78;
              temp_79;
              temp_80;
              temp_81;
              temp_82;
              temp_83;
              temp_84;
              temp_85;
              temp_86;
              temp_87;
              temp_88;
              temp_89;
              temp_90;
              temp_91;
              temp_92;
              temp_93;
              temp_94;
              temp_95;
              temp_96;
              temp_97;
              temp_98;
              temp_99;
              temp_100;
              temp_101;
              temp_102;
              temp_103;
              temp_104;
              temp_105;
              temp_106;
              temp_107;
              temp_108;
              temp_109;
              temp_110;
              temp_111;
              temp_112;
              temp_113;
              temp_114;
              temp_115;
              temp_116;
              temp_117;
              temp_118;
              temp_119;
              temp_120;
              temp_121;
              temp_122;
              temp_123;
              temp_124;
              temp_125;
              temp_126;
              temp_127;
              temp_128;
              temp_129;
              temp_130;
              temp_131;
              temp_132;
              temp_133;
              temp_134;
              temp_135;
              temp_136;
              temp_137;
              temp_138;
              temp_139;
              temp_140;
              temp_141;
              temp_142;
              temp_143;
              temp_144;
              temp_145;
              temp_146;
              temp_147;
              temp_148;
              temp_149;
              temp_150;
              temp_151;
              temp_152;
              temp_153;
              temp_154;
              temp_155;
              temp_156;
              temp_157;
              temp_158;
              temp_159;
              temp_160;
              temp_161;
              temp_162;
              temp_163;
              temp_164;
              temp_165;
              temp_166;
              temp_167;
              temp_168;
              temp_169;
              temp_170;
              temp_171;
              temp_172;
              temp_173;
              temp_174;
              temp_175;
              temp_176;
              temp_177;
              temp_178;
              temp_179;
              temp_180;
              temp_181;
              temp_182;
              temp_183;
              temp_184;
              temp_185;
              temp_186;
              temp_187;
              temp_188;
              temp_189;
              temp_190;
              temp_191;
              temp_192;
              temp_193;
              temp_194;
              temp_195;
              temp_196;
              temp_197;
              temp_198;
              temp_199;
              temp_200;
              temp_201;
              temp_202;
              temp_203;
              temp_204;
              temp_205;
              temp_206;
              temp_207;
              temp_208;
              temp_209;
              temp_210;
              temp_211;
              temp_212;
              temp_213;
              temp_214;
              temp_215;
              temp_216;
              temp_217;
              temp_218;
              temp_219;
              temp_220;
              temp_221;
              temp_222;
              temp_223;
              temp_224;
              temp_225;
              temp_226;
              temp_227;
              temp_228;
              temp_229;
              temp_230;
              temp_231;
              temp_232;
              temp_233;
              temp_234;
              temp_235;
              temp_236;
              temp_237;
              temp_238;
              temp_239;
              temp_240;
              temp_241;
              temp_242;
              temp_243;
              temp_244;
              temp_245;
              temp_246;
              temp_247;
              temp_248;
              temp_249;
              temp_250;
              temp_251;
              temp_252;
              temp_253;
              temp_254;
              temp_255
            ]) in
         l))).

Definition rcon_v : (r_con_t) :=
  (let temp_256 : int8 :=
      (secret_pure (@repr U8 141)) in
    let temp_257 : int8 :=
      (secret_pure (@repr U8 1)) in
    let temp_258 : int8 :=
      (secret_pure (@repr U8 2)) in
    let temp_259 : int8 :=
      (secret_pure (@repr U8 4)) in
    let temp_260 : int8 :=
      (secret_pure (@repr U8 8)) in
    let temp_261 : int8 :=
      (secret_pure (@repr U8 16)) in
    let temp_262 : int8 :=
      (secret_pure (@repr U8 32)) in
    let temp_263 : int8 :=
      (secret_pure (@repr U8 64)) in
    let temp_264 : int8 :=
      (secret_pure (@repr U8 128)) in
    let temp_265 : int8 :=
      (secret_pure (@repr U8 27)) in
    let temp_266 : int8 :=
      (secret_pure (@repr U8 54)) in
    let temp_267 : int8 :=
      (secret_pure (@repr U8 108)) in
    let temp_268 : int8 :=
      (secret_pure (@repr U8 216)) in
    let temp_269 : int8 :=
      (secret_pure (@repr U8 171)) in
    let temp_270 : int8 :=
      (secret_pure (@repr U8 77)) in
    (array_from_list uint8 (let l :=
          ([
              temp_256;
              temp_257;
              temp_258;
              temp_259;
              temp_260;
              temp_261;
              temp_262;
              temp_263;
              temp_264;
              temp_265;
              temp_266;
              temp_267;
              temp_268;
              temp_269;
              temp_270
            ]) in
         l))).

Definition st_274_loc : Location :=
  (block_t : choice_type ; 275%nat).
Program Definition sub_bytes
  (state_271 : block_t)
  : code (fset (path.sort leb [ st_274_loc])) [interface] (@ct (block_t)) :=
  (({code #put st_274_loc := 
        (state_271) ;;
      st_274 ← get st_274_loc ;;
      let st_274 : block_t :=
        (st_274) in
       st_274 ←
        (foldi (usize 0) (blocksize_v) (fun i_272 (st_274 : block_t) =>
            ({code  temp_273 ←
                (uint8_declassify (array_index (state_271) (i_272))) ;;
               st_274 ←
                (array_upd st_274 (i_272) (array_index (sbox_v) (temp_273))) ;;
              let st_274 : block_t :=
                (st_274) in
              
              @pkg_core_definition.ret _ ( ((st_274))) } : code (fset (
                  path.sort leb [ st_274_loc])) [interface] _))
          st_274) ;;
      
      @pkg_core_definition.ret block_t ( (st_274)) } : code (fset (
          path.sort leb [ st_274_loc])) [interface] _)).
Fail Next Obligation.

Definition out_279_loc : Location :=
  (block_t : choice_type ; 280%nat).
Program Definition shift_row
  (i_277 : uint_size)
  (shift_278 : uint_size)
  (state_276 : block_t)
  : code (fset (path.sort leb [ out_279_loc])) [interface] (@ct (block_t)) :=
  (({code #put out_279_loc := 
        (state_276) ;;
      out_279 ← get out_279_loc ;;
      let out_279 : block_t :=
        (out_279) in
       out_279 ←
        (array_upd out_279 (i_277) (array_index (state_276) ((i_277) .+ ((
                  usize 4) .* ((shift_278) %% (usize 4)))))) ;;
      let out_279 : block_t :=
        (out_279) in
      
       out_279 ←
        (array_upd out_279 ((i_277) .+ (usize 4)) (array_index (state_276) ((
                i_277) .+ ((usize 4) .* (((shift_278) .+ (usize 1)) %% (
                    usize 4)))))) ;;
      let out_279 : block_t :=
        (out_279) in
      
       out_279 ←
        (array_upd out_279 ((i_277) .+ (usize 8)) (array_index (state_276) ((
                i_277) .+ ((usize 4) .* (((shift_278) .+ (usize 2)) %% (
                    usize 4)))))) ;;
      let out_279 : block_t :=
        (out_279) in
      
       out_279 ←
        (array_upd out_279 ((i_277) .+ (usize 12)) (array_index (state_276) ((
                i_277) .+ ((usize 4) .* (((shift_278) .+ (usize 3)) %% (
                    usize 4)))))) ;;
      let out_279 : block_t :=
        (out_279) in
      
      @pkg_core_definition.ret block_t ( (out_279)) } : code (fset (
          path.sort leb [ out_279_loc])) [interface] _)).
Fail Next Obligation.


Program Definition shift_rows
  (state_281 : block_t)
  : code (fset (path.sort leb [ out_279_loc])) [interface] (@ct (block_t)) :=
  (({code  temp_282 ←
        (shift_row (usize 1) (usize 1) (state_281)) ;;
      let state_283 : block_t :=
        (temp_282) in
       temp_284 ←
        (shift_row (usize 2) (usize 2) (state_283)) ;;
      let state_285 : block_t :=
        (temp_284) in
       temp_286 ←
        (shift_row (usize 3) (usize 3) (state_285)) ;;
      @pkg_core_definition.ret block_t ( (temp_286)) } : code (fset (
          path.sort leb [ out_279_loc])) [interface] _)).
Fail Next Obligation.


Program Definition xtime
  (x_287 : uint8)
  : code (fset.fset0) [interface] (@ct (uint8)) :=
  (({code let x1_292 : uint8 :=
        ((x_287) shift_left (usize 1)) in
      let x7_288 : uint8 :=
        ((x_287) shift_right (usize 7)) in
       temp_289 ←
        (secret (@repr U8 1)) ;;
      let temp_289 : int8 :=
        (temp_289) in
      let x71_290 : uint8 :=
        ((x7_288) .& (temp_289)) in
       temp_291 ←
        (secret (@repr U8 27)) ;;
      let temp_291 : int8 :=
        (temp_291) in
      let x711b_293 : uint8 :=
        ((x71_290) .* (temp_291)) in
      @pkg_core_definition.ret uint8 ( ((x1_292) .^ (x711b_293))) } : code (
        fset.fset0) [interface] _)).
Fail Next Obligation.

Definition st_306_loc : Location :=
  (block_t : choice_type ; 307%nat).
Program Definition mix_column
  (c_294 : uint_size)
  (state_296 : block_t)
  : code (fset (path.sort leb [ st_306_loc])) [interface] (@ct (block_t)) :=
  (({code let i0_295 : uint_size :=
        ((usize 4) .* (c_294)) in
      let s0_297 : uint8 :=
        (array_index (state_296) (i0_295)) in
      let s1_298 : uint8 :=
        (array_index (state_296) ((i0_295) .+ (usize 1))) in
      let s2_299 : uint8 :=
        (array_index (state_296) ((i0_295) .+ (usize 2))) in
      let s3_300 : uint8 :=
        (array_index (state_296) ((i0_295) .+ (usize 3))) in
      #put st_306_loc := 
        (state_296) ;;
      st_306 ← get st_306_loc ;;
      let st_306 : block_t :=
        (st_306) in
      let tmp_301 : uint8 :=
        ((((s0_297) .^ (s1_298)) .^ (s2_299)) .^ (s3_300)) in
       temp_302 ←
        (xtime ((s0_297) .^ (s1_298))) ;;
       st_306 ←
        (array_upd st_306 (i0_295) (((s0_297) .^ (tmp_301)) .^ (temp_302))) ;;
      let st_306 : block_t :=
        (st_306) in
      
       temp_303 ←
        (xtime ((s1_298) .^ (s2_299))) ;;
       st_306 ←
        (array_upd st_306 ((i0_295) .+ (usize 1)) (((s1_298) .^ (tmp_301)) .^ (
              temp_303))) ;;
      let st_306 : block_t :=
        (st_306) in
      
       temp_304 ←
        (xtime ((s2_299) .^ (s3_300))) ;;
       st_306 ←
        (array_upd st_306 ((i0_295) .+ (usize 2)) (((s2_299) .^ (tmp_301)) .^ (
              temp_304))) ;;
      let st_306 : block_t :=
        (st_306) in
      
       temp_305 ←
        (xtime ((s3_300) .^ (s0_297))) ;;
       st_306 ←
        (array_upd st_306 ((i0_295) .+ (usize 3)) (((s3_300) .^ (tmp_301)) .^ (
              temp_305))) ;;
      let st_306 : block_t :=
        (st_306) in
      
      @pkg_core_definition.ret block_t ( (st_306)) } : code (fset (
          path.sort leb [ st_306_loc])) [interface] _)).
Fail Next Obligation.


Program Definition mix_columns
  (state_308 : block_t)
  : code (fset (path.sort leb [ st_306_loc])) [interface] (@ct (block_t)) :=
  (({code  temp_309 ←
        (mix_column (usize 0) (state_308)) ;;
      let state_310 : block_t :=
        (temp_309) in
       temp_311 ←
        (mix_column (usize 1) (state_310)) ;;
      let state_312 : block_t :=
        (temp_311) in
       temp_313 ←
        (mix_column (usize 2) (state_312)) ;;
      let state_314 : block_t :=
        (temp_313) in
       temp_315 ←
        (mix_column (usize 3) (state_314)) ;;
      @pkg_core_definition.ret block_t ( (temp_315)) } : code (fset (
          path.sort leb [ st_306_loc])) [interface] _)).
Fail Next Obligation.

Definition out_318_loc : Location :=
  (block_t : choice_type ; 320%nat).
Program Definition add_round_key
  (state_316 : block_t)
  (key_319 : round_key_t)
  : code (fset (path.sort leb [ out_318_loc])) [interface] (@ct (block_t)) :=
  (({code #put out_318_loc := 
        (state_316) ;;
      out_318 ← get out_318_loc ;;
      let out_318 : block_t :=
        (out_318) in
       out_318 ←
        (foldi (usize 0) (blocksize_v) (fun i_317 (out_318 : block_t) =>
            ({code  out_318 ←
                (array_upd out_318 (i_317) ((array_index (out_318) (i_317)) .^ (
                      array_index (key_319) (i_317)))) ;;
              let out_318 : block_t :=
                (out_318) in
              
              @pkg_core_definition.ret _ ( ((out_318))) } : code (fset (
                  path.sort leb [ out_318_loc])) [interface] _))
          out_318) ;;
      
      @pkg_core_definition.ret block_t ( (out_318)) } : code (fset (
          path.sort leb [ out_318_loc])) [interface] _)).
Fail Next Obligation.


Program Definition aes_enc
  (state_321 : block_t)
  (round_key_328 : round_key_t)
  : code (fset (
      path.sort leb [ st_306_loc ; st_274_loc ; out_279_loc ; out_318_loc])) [interface] (
    @ct (block_t)) :=
  (({code  temp_322 ←
        (sub_bytes (state_321)) ;;
      let state_323 : block_t :=
        (temp_322) in
       temp_324 ←
        (shift_rows (state_323)) ;;
      let state_325 : block_t :=
        (temp_324) in
       temp_326 ←
        (mix_columns (state_325)) ;;
      let state_327 : block_t :=
        (temp_326) in
       temp_329 ←
        (add_round_key (state_327) (round_key_328)) ;;
      @pkg_core_definition.ret block_t ( (temp_329)) } : code (fset (
          path.sort leb [ st_306_loc ; st_274_loc ; out_279_loc ; out_318_loc])) [interface] _)).
Fail Next Obligation.


Program Definition aes_enc_last
  (state_330 : block_t)
  (round_key_335 : round_key_t)
  : code (fset (
      path.sort leb [ out_279_loc ; st_274_loc ; out_318_loc])) [interface] (
    @ct (block_t)) :=
  (({code  temp_331 ←
        (sub_bytes (state_330)) ;;
      let state_332 : block_t :=
        (temp_331) in
       temp_333 ←
        (shift_rows (state_332)) ;;
      let state_334 : block_t :=
        (temp_333) in
       temp_336 ←
        (add_round_key (state_334) (round_key_335)) ;;
      @pkg_core_definition.ret block_t ( (temp_336)) } : code (fset (
          path.sort leb [ out_279_loc ; st_274_loc ; out_318_loc])) [interface] _)).
Fail Next Obligation.

Definition out_342_loc : Location :=
  (block_t : choice_type ; 346%nat).
Program Definition rounds_aes
  (state_337 : block_t)
  (key_338 : byte_seq)
  : code (fset (
      path.sort leb [ out_279_loc ; st_274_loc ; out_318_loc ; out_342_loc ; st_306_loc])) [interface] (
    @ct (block_t)) :=
  (({code #put out_342_loc := 
        (state_337) ;;
      out_342 ← get out_342_loc ;;
      let out_342 : block_t :=
        (out_342) in
       temp_339 ←
        (seq_num_chunks (key_338) (blocksize_v)) ;;
       out_342 ←
        (foldi (usize 0) (temp_339) (fun i_340 (out_342 : _) =>
            ({code  temp_341 ←
                (seq_get_chunk (key_338) (blocksize_v) (i_340)) ;;
              let '(_, key_block_343) :=
                (temp_341) : (uint_size '× seq uint8) in
               temp_344 ←
                (array_from_seq (blocksize_v) (key_block_343)) ;;
               temp_345 ←
                (aes_enc (out_342) (temp_344)) ;;
              out_342 ← get out_342_loc ;;
              
              #put out_342_loc := 
                (temp_345) ;;
              out_342 ← get out_342_loc ;;
              
              @pkg_core_definition.ret _ ( ((out_342))) } : code (fset (
                  path.sort leb [ st_274_loc ; out_279_loc ; out_318_loc ; out_342_loc ; st_306_loc])) [interface] _))
          out_342) ;;
      
      @pkg_core_definition.ret block_t ( (out_342)) } : code (fset (
          path.sort leb [ out_279_loc ; st_274_loc ; out_318_loc ; out_342_loc ; st_306_loc])) [interface] _)).
Fail Next Obligation.


Program Definition block_cipher_aes
  (input_352 : block_t)
  (key_347 : byte_seq)
  (nr_349 : uint_size)
  : code (fset (
      path.sort leb [ st_274_loc ; out_318_loc ; out_342_loc ; out_279_loc ; st_306_loc])) [interface] (
    @ct (block_t)) :=
  (({code  temp_348 ←
        (array_from_slice_range (default) (blocksize_v) (key_347) ((
              usize 0,
              usize 16
            ))) ;;
      let k0_353 : round_key_t :=
        (temp_348) in
       temp_350 ←
        (seq_from_slice_range (key_347) ((usize 16, (nr_349) .* (usize 16)))) ;;
      let k_356 : seq uint8 :=
        (temp_350) in
       temp_351 ←
        (array_from_slice (default) (blocksize_v) (key_347) ((nr_349) .* (
              usize 16)) (usize 16)) ;;
      let kn_359 : round_key_t :=
        (temp_351) in
       temp_354 ←
        (add_round_key (input_352) (k0_353)) ;;
      let state_355 : block_t :=
        (temp_354) in
       temp_357 ←
        (rounds_aes (state_355) (k_356)) ;;
      let state_358 : block_t :=
        (temp_357) in
       temp_360 ←
        (aes_enc_last (state_358) (kn_359)) ;;
      @pkg_core_definition.ret block_t ( (temp_360)) } : code (fset (
          path.sort leb [ st_274_loc ; out_318_loc ; out_342_loc ; out_279_loc ; st_306_loc])) [interface] _)).
Fail Next Obligation.


Program Definition rotate_word
  (w_361 : word_t)
  : code (fset.fset0) [interface] (@ct (word_t)) :=
  (({code @pkg_core_definition.ret word_t ( (array_from_list uint8 (let l :=
            ([
                array_index (w_361) (usize 1);
                array_index (w_361) (usize 2);
                array_index (w_361) (usize 3);
                array_index (w_361) (usize 0)
              ]) in
           l))) } : code (fset.fset0) [interface] _)).
Fail Next Obligation.


Program Definition slice_word
  (w_362 : word_t)
  : code (fset.fset0) [interface] (@ct (word_t)) :=
  (({code  temp_363 ←
        (declassify_usize_from_uint8 (array_index (w_362) (usize 0))) ;;
       temp_364 ←
        (declassify_usize_from_uint8 (array_index (w_362) (usize 1))) ;;
       temp_365 ←
        (declassify_usize_from_uint8 (array_index (w_362) (usize 2))) ;;
       temp_366 ←
        (declassify_usize_from_uint8 (array_index (w_362) (usize 3))) ;;
      @pkg_core_definition.ret word_t ( (array_from_list uint8 (let l :=
            ([
                array_index (sbox_v) (temp_363);
                array_index (sbox_v) (temp_364);
                array_index (sbox_v) (temp_365);
                array_index (sbox_v) (temp_366)
              ]) in
           l))) } : code (fset.fset0) [interface] _)).
Fail Next Obligation.

Definition k_369_loc : Location :=
  (word_t : choice_type ; 372%nat).
Program Definition aes_keygen_assist
  (w_367 : word_t)
  (rcon_371 : uint8)
  : code (fset (path.sort leb [ k_369_loc])) [interface] (@ct (word_t)) :=
  (({code  temp_368 ←
        (rotate_word (w_367)) ;;
      #put k_369_loc := 
        (temp_368) ;;
      k_369 ← get k_369_loc ;;
      let k_369 : word_t :=
        (k_369) in
       temp_370 ←
        (slice_word (k_369)) ;;
      k_369 ← get k_369_loc ;;
      
      #put k_369_loc := 
        (temp_370) ;;
      k_369 ← get k_369_loc ;;
      let k_369 : word_t :=
        (k_369) in
      
       k_369 ←
        (array_upd k_369 (usize 0) ((array_index (k_369) (usize 0)) .^ (
              rcon_371))) ;;
      let k_369 : word_t :=
        (k_369) in
      
      @pkg_core_definition.ret word_t ( (k_369)) } : code (fset (
          path.sort leb [ k_369_loc])) [interface] _)).
Fail Next Obligation.

Definition result_375_loc : Location :=
  ((result word_t int8) : choice_type ; 383%nat).
Definition k_374_loc : Location :=
  (word_t : choice_type ; 384%nat).
Program Definition key_expansion_word
  (w0_382 : word_t)
  (w1_373 : word_t)
  (i_376 : uint_size)
  (nk_378 : uint_size)
  (nr_377 : uint_size)
  : code (fset (
      path.sort leb [ k_374_loc ; k_369_loc ; result_375_loc])) [interface] (
    @ct (word_result_t)) :=
  (({code #put k_374_loc := 
        (w1_373) ;;
      k_374 ← get k_374_loc ;;
      let k_374 : word_t :=
        (k_374) in
      #put result_375_loc := 
        (@Err word_t int8 (invalid_key_expansion_index_v)) ;;
      result_375 ← get result_375_loc ;;
      (* let result_375 : (result word_t int8) := *)
      (*   (result_375) in *)
       '(k_374, result_375) ←
        (if (i_376) <.? ((usize 4) .* ((nr_377) .+ (
                usize 1))):bool_ChoiceEquality then (({code  '(k_374) ←
                (if ((i_376) %% (nk_378)) =.? (
                    usize 0):bool_ChoiceEquality then (({code  temp_379 ←
                        (aes_keygen_assist (k_374) (array_index (rcon_v) ((
                                i_376) ./ (nk_378)))) ;;
                      k_374 ← get k_374_loc ;;
                      
                      #put k_374_loc := 
                        (temp_379) ;;
                      k_374 ← get k_374_loc ;;
                      
                      @pkg_core_definition.ret _ ( ((k_374))) } : code (fset (
                          path.sort leb [ result_375_loc ; k_369_loc ; k_374_loc])) [interface] _)) else (
                    ({code  '(k_374) ←
                        (if ((nk_378) >.? (usize 6)) && (((i_376) %% (
                                nk_378)) =.? (
                              usize 4)):bool_ChoiceEquality then ((
                              {code  temp_380 ←
                                (slice_word (k_374)) ;;
                              k_374 ← get k_374_loc ;;
                              
                              #put k_374_loc := 
                                (temp_380) ;;
                              k_374 ← get k_374_loc ;;
                              
                              @pkg_core_definition.ret _ ( ((k_374))) } : code (
                                fset (
                                  path.sort leb [ k_374_loc ; result_375_loc])) [interface] _)) else (
                            @pkg_core_definition.ret _ ( ((k_374))))) ;;
                      
                      @pkg_core_definition.ret _ ( ((k_374))) } : code (fset (
                          path.sort leb [ result_375_loc ; k_374_loc])) [interface] _))) ;;
              
               k_374 ←
                (foldi (usize 0) (usize 4) (fun i_381 (k_374 : word_t) =>
                    ({code  k_374 ←
                        (array_upd k_374 (i_381) ((array_index (k_374) (
                                i_381)) .^ (array_index (w0_382) (i_381)))) ;;
                      let k_374 : word_t :=
                        (k_374) in
                      
                      @pkg_core_definition.ret _ ( ((k_374))) } : code (fset (
                          path.sort leb [ k_369_loc ; k_374_loc ; result_375_loc])) [interface] _))
                  k_374) ;;
              
              result_375 ← get result_375_loc ;;
              
              #put result_375_loc := 
                (@Ok word_t int8 (k_374)) ;;
              result_375 ← get result_375_loc ;;
              
              @pkg_core_definition.ret (word_t '× word_result_t) ( ((k_374, result_375))) } : code (
                fset (
                  path.sort leb [ k_374_loc ; k_369_loc ; result_375_loc])) [interface] _)) else (
            @pkg_core_definition.ret _ ( ((k_374, result_375))))) ;;
      
      @pkg_core_definition.ret (result word_t int8) ( (result_375)) } : code (
        fset (
          path.sort leb [ k_374_loc ; k_369_loc ; result_375_loc])) [interface] _)).
Fail Next Obligation.

Definition key_ex_387_loc : Location :=
  (seq uint8 : choice_type ; 403%nat).
Program Definition key_expansion_aes
  (key_388 : byte_seq)
  (nk_397 : uint_size)
  (nr_398 : uint_size)
  (key_schedule_length_385 : uint_size)
  (key_length_390 : uint_size)
  (iterations_391 : uint_size)
  : code (fset (
      path.sort leb [ k_369_loc ; result_375_loc ; k_374_loc ; key_ex_387_loc])) [interface] (
    @ct (byte_seq_result_t)) :=
  (({code  temp_386 ←
        (seq_new_ (default) (key_schedule_length_385)) ;;
      #put key_ex_387_loc := 
        (temp_386) ;;
      key_ex_387 ← get key_ex_387_loc ;;
      let key_ex_387 : seq uint8 :=
        (key_ex_387) in
       temp_389 ←
        (seq_update_start (key_ex_387) (key_388)) ;;
      key_ex_387 ← get key_ex_387_loc ;;
      
      #put key_ex_387_loc := 
        (temp_389) ;;
      key_ex_387 ← get key_ex_387_loc ;;
      
      let key_ex_387 : seq uint8 :=
        (key_ex_387) in
      let word_size_393 : uint_size :=
        (key_length_390) in
      ChoiceEqualityMonad.bind_code (M := result2 int8) (L1 := path.sort leb [ key_ex_387_loc ; k_374_loc ; result_375_loc ; k_369_loc]) (L2 := path.sort leb [ k_369_loc ; result_375_loc ; k_374_loc ; key_ex_387_loc]) (is_true0 := _) (
        foldi_bind_code (M := result2 int8) (L1 := path.sort leb [ key_ex_387_loc ; k_374_loc ; result_375_loc ; k_369_loc]) (L2 := path.sort leb [ k_369_loc ; result_375_loc ; k_374_loc ; key_ex_387_loc]) (is_true0 := _)  (
          usize 0) (iterations_391) (Ok key_ex_387) (fun j_392 key_ex_387 =>
        ({code let i_394 : uint_size :=
            ((j_392) .+ (word_size_393)) in
           temp_395 ←
            (array_from_slice (default) (key_length_v) (key_ex_387) ((
                  usize 4) .* ((i_394) .- (word_size_393))) (usize 4) : code _ _ word_t) ;;
           temp_396 ←
            (array_from_slice (default) (key_length_v) (key_ex_387) (((
                    usize 4) .* (i_394)) .- (usize 4)) (usize 4)) ;;
           temp_399 ←
            (key_expansion_word (temp_395) (temp_396) (i_394) (nk_397) (
                nr_398)) ;;
          ChoiceEqualityMonad.bind_code (M := result2 int8) (L1 := path.sort leb [ result_375_loc ; k_374_loc ; k_369_loc ; key_ex_387_loc]) (L2 := path.sort leb [ key_ex_387_loc ; k_374_loc ; result_375_loc ; k_369_loc]) (is_true0 := _) (
            (
              {code @pkg_core_definition.ret _ temp_399 } : code _ [interface] _)) (
            fun word_400 => ({code  temp_401 ←
                (array_to_seq (word_400)) ;;
              let temp_401 : seq uint8 :=
                (temp_401) in
               temp_402 ←
                (seq_update (key_ex_387) ((usize 4) .* (i_394)) (temp_401)) ;;
              key_ex_387 ← get key_ex_387_loc ;;
              
              #put key_ex_387_loc := 
                (temp_402) ;;
              key_ex_387 ← get key_ex_387_loc ;;
              let key_ex_387 : seq uint8 :=
                (key_ex_387) in

              @pkg_core_definition.ret _ ( (Ok ((key_ex_387
                  )))) } : code _ [interface] _)) } : code (fset (
              path.sort leb [ key_ex_387_loc ; k_374_loc ; result_375_loc ; k_369_loc])) [interface] _))) (
        fun key_ex_387 => ({code @pkg_core_definition.ret (
            result byte_seq int8) ( (@Ok byte_seq int8 (
              key_ex_387))) } : code _ [interface] _)) } : code (fset (
          path.sort leb [ k_369_loc ; result_375_loc ; k_374_loc ; key_ex_387_loc])) [interface] _)).
Fail Next Obligation.


Program Definition aes_encrypt_block
  (k_404 : byte_seq)
  (input_411 : block_t)
  (nk_405 : uint_size)
  (nr_406 : uint_size)
  (key_schedule_length_407 : uint_size)
  (key_length_408 : uint_size)
  (iterations_409 : uint_size)
  : code (fset (
      path.sort leb [ out_318_loc ; k_369_loc ; out_279_loc ; k_374_loc ; out_342_loc ; st_306_loc ; key_ex_387_loc ; result_375_loc ; st_274_loc])) [interface] (
    @ct (block_result_t)) :=
  (({code  temp_410 ←
        (key_expansion_aes (k_404) (nk_405) (nr_406) (key_schedule_length_407) (
            key_length_408) (iterations_409)) ;;
      ChoiceEqualityMonad.bind_code (M := result2 int8) (L1 := path.sort leb [ k_369_loc ; key_ex_387_loc ; k_374_loc ; result_375_loc]) (L2 := path.sort leb [ out_318_loc ; k_369_loc ; out_279_loc ; k_374_loc ; out_342_loc ; st_306_loc ; key_ex_387_loc ; result_375_loc ; st_274_loc]) (is_true0 := _) (
        ({code @pkg_core_definition.ret _ temp_410 } : code _ [interface] _)) (
        fun key_ex_412 => ({code  temp_413 ←
            (block_cipher_aes (input_411) (key_ex_412) (nr_406)) ;;
          @pkg_core_definition.ret (result block_t int8) ( (@Ok block_t int8 (
              temp_413))) } : code _ [interface] _)) } : code (fset (
          path.sort leb [ out_318_loc ; k_369_loc ; out_279_loc ; k_374_loc ; out_342_loc ; st_306_loc ; key_ex_387_loc ; result_375_loc ; st_274_loc])) [interface] _)).
Fail Next Obligation.


Program Definition aes128_encrypt_block
  (k_414 : key128_t)
  (input_417 : block_t)
  : code (fset (
      path.sort leb [ st_274_loc ; k_374_loc ; result_375_loc ; out_342_loc ; st_306_loc ; out_279_loc ; k_369_loc ; key_ex_387_loc ; out_318_loc])) [interface] (
    @ct (block_t)) :=
  (({code  temp_415 ←
        (array_to_seq (k_414)) ;;
      let temp_415 : seq uint8 :=
        (temp_415) in
       temp_416 ←
        (seq_from_seq (temp_415)) ;;
       temp_418 ←
        (aes_encrypt_block (temp_416) (input_417) (key_length_v) (rounds_v) (
                             key_schedule_length_v) (key_length_v) (iterations_v)) ;;
       temp_419 ←
        (result_unwrap (ct_T temp_418)) ;;
      @pkg_core_definition.ret block_t ( (temp_419)) } : code (fset (
          path.sort leb [ st_274_loc ; k_374_loc ; result_375_loc ; out_342_loc ; st_306_loc ; out_279_loc ; k_369_loc ; key_ex_387_loc ; out_318_loc])) [interface] _)).
Fail Next Obligation.

Definition input_421_loc : Location :=
  (block_t : choice_type ; 436%nat).
Program Definition aes_ctr_key_block
  (k_429 : byte_seq)
  (n_422 : aes_nonce_t)
  (c_425 : uint32)
  (nk_430 : uint_size)
  (nr_431 : uint_size)
  (key_schedule_length_432 : uint_size)
  (key_length_433 : uint_size)
  (iterations_434 : uint_size)
  : code (fset (
      path.sort leb [ key_ex_387_loc ; st_306_loc ; out_318_loc ; st_274_loc ; out_279_loc ; k_369_loc ; result_375_loc ; input_421_loc ; k_374_loc ; out_342_loc])) [interface] (
    @ct (block_result_t)) :=
  (({code  temp_420 ←
        (array_new_ (default) (blocksize_v)) ;;
      #put input_421_loc := 
        (temp_420) ;;
      input_421 ← get input_421_loc ;;
      let input_421 : block_t :=
        (input_421) in
       temp_423 ←
        (array_to_seq (n_422)) ;;
      let temp_423 : seq uint8 :=
        (temp_423) in
       temp_424 ←
        (array_update (input_421) (usize 0) (temp_423)) ;;
      input_421 ← get input_421_loc ;;
      
      #put input_421_loc := 
        (temp_424) ;;
      input_421 ← get input_421_loc ;;
      
       temp_426 ←
        (uint32_to_be_bytes (c_425)) ;;
       temp_427 ←
        (array_to_seq (ct_T temp_426)) ;;
      let temp_427 : seq uint8 :=
        (temp_427) in
       temp_428 ←
        (array_update (ct_T input_421) (usize 12) (temp_427)) ;;
      input_421 ← get input_421_loc ;;
      
      #put input_421_loc := 
        (temp_428) ;;
      input_421 ← get input_421_loc ;;
      
       temp_435 ←
        (aes_encrypt_block (k_429) (input_421) (nk_430) (nr_431) (
            key_schedule_length_432) (key_length_433) (iterations_434)) ;;
      @pkg_core_definition.ret block_result_t ( (temp_435)) } : code (fset (
          path.sort leb [ key_ex_387_loc ; st_306_loc ; out_318_loc ; st_274_loc ; out_279_loc ; k_369_loc ; result_375_loc ; input_421_loc ; k_374_loc ; out_342_loc])) [interface] _)).
Fail Next Obligation.

Definition out_439_loc : Location :=
  (block_t : choice_type ; 441%nat).
Program Definition xor_block
  (block_437 : block_t)
  (key_block_440 : block_t)
  : code (fset (path.sort leb [ out_439_loc])) [interface] (@ct (block_t)) :=
  (({code #put out_439_loc := 
        (block_437) ;;
      out_439 ← get out_439_loc ;;
      let out_439 : block_t :=
        (out_439) in
       out_439 ←
        (foldi (usize 0) (blocksize_v) (fun i_438 (out_439 : block_t) =>
            ({code  out_439 ←
                (array_upd out_439 (i_438) ((array_index (out_439) (i_438)) .^ (
                      array_index (key_block_440) (i_438)))) ;;
              let out_439 : block_t :=
                (out_439) in
              
              @pkg_core_definition.ret _ ( ((out_439))) } : code (fset (
                  path.sort leb [ out_439_loc])) [interface] _))
          out_439) ;;
      
      @pkg_core_definition.ret block_t ( (out_439)) } : code (fset (
          path.sort leb [ out_439_loc])) [interface] _)).
Fail Next Obligation.

Definition ctr_452_loc : Location :=
  (uint32 : choice_type ; 479%nat).
Definition blocks_out_459_loc : Location :=
  (seq uint8 : choice_type ; 480%nat).
Program Definition aes_counter_mode
  (key_450 : byte_seq)
  (nonce_451 : aes_nonce_t)
  (counter_442 : uint32)
  (msg_443 : byte_seq)
  (nk_453 : uint_size)
  (nr_454 : uint_size)
  (key_schedule_length_455 : uint_size)
  (key_length_456 : uint_size)
  (iterations_457 : uint_size)
  : code (fset (
      path.sort leb [ out_439_loc ; out_318_loc ; out_279_loc ; ctr_452_loc ; result_375_loc ; st_306_loc ; st_274_loc ; k_374_loc ; blocks_out_459_loc ; out_342_loc ; input_421_loc ; key_ex_387_loc ; k_369_loc])) [interface] (
           @ct (byte_seq_result_t)) :=
  (({code #put ctr_452_loc := 
              (counter_442) ;;
              ctr_452 ← get ctr_452_loc ;;
              let ctr_452 : uint32 :=
                (ctr_452) in
         temp_444 ←
        (seq_len (msg_443)) ;;
       temp_445 ←
        (seq_new_ (default) (temp_444)) ;;
      #put blocks_out_459_loc := 
        (temp_445) ;;
      blocks_out_459 ← get blocks_out_459_loc ;;
      let blocks_out_459 : seq uint8 :=
        (blocks_out_459) in
       temp_446 ←
        (seq_num_exact_chunks (msg_443) (blocksize_v)) ;;
      let n_blocks_447 : uint_size :=
        (temp_446) in
      ChoiceEqualityMonad.bind_code (M := result2 int8) (L1 := path.sort leb [ ctr_452_loc ; input_421_loc ; out_439_loc ; k_369_loc ; out_279_loc ; out_318_loc ; result_375_loc ; out_342_loc ; key_ex_387_loc ; st_306_loc ; blocks_out_459_loc ; st_274_loc ; k_374_loc]) (L2 := path.sort leb [ out_318_loc ; st_274_loc ; k_374_loc ; result_375_loc ; st_306_loc ; out_279_loc ; key_ex_387_loc ; ctr_452_loc ; input_421_loc ; out_342_loc ; blocks_out_459_loc ; k_369_loc ; out_439_loc]) (is_true0 := _)
         (foldi_bind_code (M := result2 int8) (L1 := path.sort leb [ ctr_452_loc ; input_421_loc ; out_439_loc ; k_369_loc ; out_279_loc ; out_318_loc ; result_375_loc ; out_342_loc ; key_ex_387_loc ; st_306_loc ; blocks_out_459_loc ; st_274_loc ; k_374_loc]) (L2 := _) (is_true0 := _)  (
          usize 0) (n_blocks_447) (@Ok (uint32 '× seq uint8) (int8) ((ctr_452, blocks_out_459))) ((fun i_448 '(
          ctr_452,
          blocks_out_459
        ) =>
        ({code  temp_449 ←
            (seq_get_exact_chunk (msg_443) (blocksize_v) (i_448)) ;;
          let msg_block_460 : seq uint8 :=
            (temp_449) in
           temp_458 ←
            (aes_ctr_key_block (key_450) (nonce_451) (ctr_452) (nk_453) (
                nr_454) (key_schedule_length_455) (key_length_456) (
                iterations_457)) ;;
          (ChoiceEqualityMonad.bind_code (M := result2 int8) (L1 := path.sort leb [ blocks_out_459_loc ; out_318_loc ; out_342_loc ; result_375_loc ; key_ex_387_loc ; st_306_loc ; k_374_loc ; out_279_loc ; ctr_452_loc ; st_274_loc ; input_421_loc ; k_369_loc]) (L2 := path.sort leb [ ctr_452_loc ; input_421_loc ; out_439_loc ; k_369_loc ; out_279_loc ; out_318_loc ; result_375_loc ; out_342_loc ; key_ex_387_loc ; st_306_loc ; blocks_out_459_loc ; st_274_loc ; k_374_loc]) (is_true0 := _) (
                                           {code @pkg_core_definition.ret _ temp_458 } : code _ [interface] _)

                                         (fun key_block_462 => ({code
temp_461 ←
                (array_from_seq (blocksize_v) (msg_block_460)) ;;
               temp_463 ←
                (xor_block (temp_461) (key_block_462)) ;;
               temp_464 ←
                (array_to_seq (temp_463 : block_t)) ;;
            let temp_464 : seq uint8 :=
                (temp_464) in
               temp_465 ←
                (seq_set_chunk (blocks_out_459) (blocksize_v) (i_448) (
                    temp_464)) ;;
              blocks_out_459 ← get blocks_out_459_loc ;;
              
              #put blocks_out_459_loc := 
                (temp_465) ;;
              blocks_out_459 ← get blocks_out_459_loc ;;
               temp_466 ←
                (secret (@repr U32 1)) ;;
              let temp_466 : int32 :=
                (temp_466) in
              ctr_452 ← get ctr_452_loc ;;
              
              #put ctr_452_loc := 
                ((ctr_452) .+ (temp_466)) ;;
              ctr_452 ← get ctr_452_loc ;;

              @pkg_core_definition.ret _ (Ok ((ctr_452, blocks_out_459
                  ) : uint32 '× (seq uint8))) } : code _ [interface] _))


          ) } : code (fset (
                          path.sort leb [ ctr_452_loc ; input_421_loc ; out_439_loc ; k_369_loc ; out_279_loc ; out_318_loc ; result_375_loc ; out_342_loc ; key_ex_387_loc ; st_306_loc ; blocks_out_459_loc ; st_274_loc ; k_374_loc])) [interface] _)))) (fun '(ctr_452, blocks_out_459) => ({code
         temp_467 ←
           (seq_get_remainder_chunk (msg_443) (blocksize_v)) ;;
          let last_block_468 : seq uint8 :=
            (temp_467) in
           temp_469 ←
            (seq_len (last_block_468)) ;;
          let last_block_len_470 : uint_size :=
            (temp_469 : uint_size_type) in
          if_bind_code (M := result2 int8) (Lx := path.sort leb [ st_306_loc ; key_ex_387_loc ; input_421_loc ; st_274_loc ; out_439_loc ; ctr_452_loc ; out_279_loc ; k_374_loc ; result_375_loc ; out_342_loc ; k_369_loc ; out_318_loc ; blocks_out_459_loc]) (Ly := []) (L2 := path.sort leb [ out_318_loc ; st_274_loc ; k_374_loc ; result_375_loc ; st_306_loc ; out_279_loc ; key_ex_387_loc ; ctr_452_loc ; input_421_loc ; out_342_loc ; blocks_out_459_loc ; k_369_loc ; out_439_loc]) (it1 := _) (it2 := _) (
                         (last_block_len_470) !=.? (usize 0) : bool_ChoiceEquality) ({code
  temp_471 ←
  (array_new_ (default  : int8) (blocksize_v)) ;;
  temp_472 ←
         (array_update_start (ct_T temp_471) (last_block_468)) ;;
               let last_block_474 : block_t :=
                (temp_472) in
               temp_473 ←
                (aes_ctr_key_block (key_450) (nonce_451) (ctr_452) (nk_453) (
                    nr_454) (key_schedule_length_455) (key_length_456) (
                                     iterations_457)) ;;
               ChoiceEqualityMonad.bind_code (M := result2 int8) (L1 := path.sort leb [ ctr_452_loc ; out_279_loc ; out_439_loc ; k_369_loc ; input_421_loc ; blocks_out_459_loc ; key_ex_387_loc ; out_318_loc ; result_375_loc ; out_342_loc ; st_274_loc ; k_374_loc ; st_306_loc]) (L2 := path.sort leb [ st_306_loc ; key_ex_387_loc ; input_421_loc ; st_274_loc ; out_439_loc ; ctr_452_loc ; out_279_loc ; k_374_loc ; result_375_loc ; out_342_loc ; k_369_loc ; out_318_loc ; blocks_out_459_loc]) (is_true0 := _) (({code @pkg_core_definition.ret _ temp_473 } : code _ [interface] _)) (
      fun key_block_475 => ({code  temp_476 ←
                    (xor_block (last_block_474) (key_block_475)) ;;
                   temp_477 ←
                    (array_slice_range (temp_476 : block_t) ((usize 0, last_block_len_470
                        ))) ;;
                   temp_478 ←
                    (seq_set_chunk (blocks_out_459) (blocksize_v) (
                        n_blocks_447) (temp_477)) ;;
                  blocks_out_459 ← get blocks_out_459_loc ;;
                  
                  #put blocks_out_459_loc := 
                    (temp_478) ;;
                  blocks_out_459 ← get blocks_out_459_loc ;;
                  let blocks_out_459 : seq uint8 :=
                    (blocks_out_459) in
                
                  @pkg_core_definition.ret (result (seq uint8) uint8) ( (Ok ((blocks_out_459
                          )))) } : code _ [interface] _))

} : code (fset ( path.sort leb [ st_306_loc ; key_ex_387_loc ; input_421_loc ; st_274_loc ; out_439_loc ; ctr_452_loc ; out_279_loc ; k_374_loc ; result_375_loc ; out_342_loc ; k_369_loc ; out_318_loc ; blocks_out_459_loc])) [interface] _) (({code  (@pkg_core_definition.ret _ ( (Ok (blocks_out_459
                  )))) } : code _ [interface] _)) ((fun '(blocks_out_459) =>
          ({code @pkg_core_definition.ret (result byte_seq int8) ( (
              @Ok byte_seq int8 (
                blocks_out_459))) } : code _ [interface] _)))
  } : code _ [interface] _))
         })).
Fail Next Obligation.


Program Definition aes128_encrypt
  (key_481 : key128_t)
  (nonce_484 : aes_nonce_t)
  (counter_485 : uint32)
  (msg_486 : byte_seq)
  : code (fset (
      path.sort leb [ out_318_loc ; k_374_loc ; k_369_loc ; st_274_loc ; key_ex_387_loc ; input_421_loc ; out_439_loc ; out_279_loc ; out_342_loc ; ctr_452_loc ; result_375_loc ; st_306_loc ; blocks_out_459_loc])) [interface] (
    @ct (byte_seq)) :=
  (({code  temp_482 ←
        (array_to_seq (key_481)) ;;
      let temp_482 : seq uint8 :=
        (temp_482) in
       temp_483 ←
        (seq_from_seq (temp_482)) ;;
       temp_487 ←
        (aes_counter_mode (temp_483) (nonce_484) (counter_485) (msg_486) (
            key_length_v) (rounds_v) (key_schedule_length_v) (key_length_v) (
                            iterations_v)) ;;
       temp_488 ←
        (result_unwrap (ct_T temp_487)) ;;
      @pkg_core_definition.ret (seq uint8) ( (temp_488)) } : code (fset (
          path.sort leb [ out_318_loc ; k_374_loc ; k_369_loc ; st_274_loc ; key_ex_387_loc ; input_421_loc ; out_439_loc ; out_279_loc ; out_342_loc ; ctr_452_loc ; result_375_loc ; st_306_loc ; blocks_out_459_loc])) [interface] _)).
Fail Next Obligation.


Program Definition aes128_decrypt
  (key_489 : key128_t)
  (nonce_492 : aes_nonce_t)
  (counter_493 : uint32)
  (ctxt_494 : byte_seq)
  : code (fset (
      path.sort leb [ st_306_loc ; out_439_loc ; key_ex_387_loc ; k_374_loc ; out_342_loc ; blocks_out_459_loc ; out_318_loc ; result_375_loc ; ctr_452_loc ; k_369_loc ; st_274_loc ; input_421_loc ; out_279_loc])) [interface] (
    @ct (byte_seq)) :=
  (({code  temp_490 ←
        (array_to_seq (key_489)) ;;
      let temp_490 : seq uint8 :=
        (temp_490) in
       temp_491 ←
        (seq_from_seq (temp_490)) ;;
       temp_495 ←
        (aes_counter_mode (temp_491) (nonce_492) (counter_493) (ctxt_494) (
            key_length_v) (rounds_v) (key_schedule_length_v) (key_length_v) (
            iterations_v)) ;;
       temp_496 ←
        (result_unwrap (ct_T temp_495)) ;;
      @pkg_core_definition.ret (seq uint8) ( (temp_496)) } : code (fset (
          path.sort leb [ st_306_loc ; out_439_loc ; key_ex_387_loc ; k_374_loc ; out_342_loc ; blocks_out_459_loc ; out_318_loc ; result_375_loc ; ctr_452_loc ; k_369_loc ; st_274_loc ; input_421_loc ; out_279_loc])) [interface] _)).
Fail Next Obligation.

