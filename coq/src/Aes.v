Require Import Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
Require Import Hacspec.Lib.

Definition blocksize : uint_size :=
  usize 16.

Definition ivsize : uint_size :=
  usize 12.

Definition key_length : uint_size :=
  usize 4.

Definition rounds : uint_size :=
  usize 10.

Definition key_schedule_length : uint_size :=
  usize 176.

Definition iterations : uint_size :=
  usize 40.

Definition block := nseq (uint8) (blocksize).

Definition word := nseq (uint8) (key_length).

Definition round_key := nseq (uint8) (blocksize).

Definition nonce := nseq (uint8) (ivsize).

Definition s_box := nseq (uint8) (usize 256).

Definition r_con := nseq (uint8) (usize 15).

Definition bytes144 := nseq (uint8) (usize 144).

Definition bytes176 := nseq (uint8) (key_schedule_length).

Definition key128 := nseq (uint8) (blocksize).

Definition sbox : s_box :=
  array_from_list uint8 (
    let l :=
      [
        secret (repr 99);
        secret (repr 124);
        secret (repr 119);
        secret (repr 123);
        secret (repr 242);
        secret (repr 107);
        secret (repr 111);
        secret (repr 197);
        secret (repr 48);
        secret (repr 1);
        secret (repr 103);
        secret (repr 43);
        secret (repr 254);
        secret (repr 215);
        secret (repr 171);
        secret (repr 118);
        secret (repr 202);
        secret (repr 130);
        secret (repr 201);
        secret (repr 125);
        secret (repr 250);
        secret (repr 89);
        secret (repr 71);
        secret (repr 240);
        secret (repr 173);
        secret (repr 212);
        secret (repr 162);
        secret (repr 175);
        secret (repr 156);
        secret (repr 164);
        secret (repr 114);
        secret (repr 192);
        secret (repr 183);
        secret (repr 253);
        secret (repr 147);
        secret (repr 38);
        secret (repr 54);
        secret (repr 63);
        secret (repr 247);
        secret (repr 204);
        secret (repr 52);
        secret (repr 165);
        secret (repr 229);
        secret (repr 241);
        secret (repr 113);
        secret (repr 216);
        secret (repr 49);
        secret (repr 21);
        secret (repr 4);
        secret (repr 199);
        secret (repr 35);
        secret (repr 195);
        secret (repr 24);
        secret (repr 150);
        secret (repr 5);
        secret (repr 154);
        secret (repr 7);
        secret (repr 18);
        secret (repr 128);
        secret (repr 226);
        secret (repr 235);
        secret (repr 39);
        secret (repr 178);
        secret (repr 117);
        secret (repr 9);
        secret (repr 131);
        secret (repr 44);
        secret (repr 26);
        secret (repr 27);
        secret (repr 110);
        secret (repr 90);
        secret (repr 160);
        secret (repr 82);
        secret (repr 59);
        secret (repr 214);
        secret (repr 179);
        secret (repr 41);
        secret (repr 227);
        secret (repr 47);
        secret (repr 132);
        secret (repr 83);
        secret (repr 209);
        secret (repr 0);
        secret (repr 237);
        secret (repr 32);
        secret (repr 252);
        secret (repr 177);
        secret (repr 91);
        secret (repr 106);
        secret (repr 203);
        secret (repr 190);
        secret (repr 57);
        secret (repr 74);
        secret (repr 76);
        secret (repr 88);
        secret (repr 207);
        secret (repr 208);
        secret (repr 239);
        secret (repr 170);
        secret (repr 251);
        secret (repr 67);
        secret (repr 77);
        secret (repr 51);
        secret (repr 133);
        secret (repr 69);
        secret (repr 249);
        secret (repr 2);
        secret (repr 127);
        secret (repr 80);
        secret (repr 60);
        secret (repr 159);
        secret (repr 168);
        secret (repr 81);
        secret (repr 163);
        secret (repr 64);
        secret (repr 143);
        secret (repr 146);
        secret (repr 157);
        secret (repr 56);
        secret (repr 245);
        secret (repr 188);
        secret (repr 182);
        secret (repr 218);
        secret (repr 33);
        secret (repr 16);
        secret (repr 255);
        secret (repr 243);
        secret (repr 210);
        secret (repr 205);
        secret (repr 12);
        secret (repr 19);
        secret (repr 236);
        secret (repr 95);
        secret (repr 151);
        secret (repr 68);
        secret (repr 23);
        secret (repr 196);
        secret (repr 167);
        secret (repr 126);
        secret (repr 61);
        secret (repr 100);
        secret (repr 93);
        secret (repr 25);
        secret (repr 115);
        secret (repr 96);
        secret (repr 129);
        secret (repr 79);
        secret (repr 220);
        secret (repr 34);
        secret (repr 42);
        secret (repr 144);
        secret (repr 136);
        secret (repr 70);
        secret (repr 238);
        secret (repr 184);
        secret (repr 20);
        secret (repr 222);
        secret (repr 94);
        secret (repr 11);
        secret (repr 219);
        secret (repr 224);
        secret (repr 50);
        secret (repr 58);
        secret (repr 10);
        secret (repr 73);
        secret (repr 6);
        secret (repr 36);
        secret (repr 92);
        secret (repr 194);
        secret (repr 211);
        secret (repr 172);
        secret (repr 98);
        secret (repr 145);
        secret (repr 149);
        secret (repr 228);
        secret (repr 121);
        secret (repr 231);
        secret (repr 200);
        secret (repr 55);
        secret (repr 109);
        secret (repr 141);
        secret (repr 213);
        secret (repr 78);
        secret (repr 169);
        secret (repr 108);
        secret (repr 86);
        secret (repr 244);
        secret (repr 234);
        secret (repr 101);
        secret (repr 122);
        secret (repr 174);
        secret (repr 8);
        secret (repr 186);
        secret (repr 120);
        secret (repr 37);
        secret (repr 46);
        secret (repr 28);
        secret (repr 166);
        secret (repr 180);
        secret (repr 198);
        secret (repr 232);
        secret (repr 221);
        secret (repr 116);
        secret (repr 31);
        secret (repr 75);
        secret (repr 189);
        secret (repr 139);
        secret (repr 138);
        secret (repr 112);
        secret (repr 62);
        secret (repr 181);
        secret (repr 102);
        secret (repr 72);
        secret (repr 3);
        secret (repr 246);
        secret (repr 14);
        secret (repr 97);
        secret (repr 53);
        secret (repr 87);
        secret (repr 185);
        secret (repr 134);
        secret (repr 193);
        secret (repr 29);
        secret (repr 158);
        secret (repr 225);
        secret (repr 248);
        secret (repr 152);
        secret (repr 17);
        secret (repr 105);
        secret (repr 217);
        secret (repr 142);
        secret (repr 148);
        secret (repr 155);
        secret (repr 30);
        secret (repr 135);
        secret (repr 233);
        secret (repr 206);
        secret (repr 85);
        secret (repr 40);
        secret (repr 223);
        secret (repr 140);
        secret (repr 161);
        secret (repr 137);
        secret (repr 13);
        secret (repr 191);
        secret (repr 230);
        secret (repr 66);
        secret (repr 104);
        secret (repr 65);
        secret (repr 153);
        secret (repr 45);
        secret (repr 15);
        secret (repr 176);
        secret (repr 84);
        secret (repr 187);
        secret (repr 22)
      ] in  l).

Definition rcon : r_con :=
  array_from_list uint8 (
    let l :=
      [
        secret (repr 141);
        secret (repr 1);
        secret (repr 2);
        secret (repr 4);
        secret (repr 8);
        secret (repr 16);
        secret (repr 32);
        secret (repr 64);
        secret (repr 128);
        secret (repr 27);
        secret (repr 54);
        secret (repr 108);
        secret (repr 216);
        secret (repr 171);
        secret (repr 77)
      ] in  l).

Definition sub_bytes (state_0 : block) : block :=
  let st_1 :=
    state_0 in 
  let st_1 :=
    foldi (usize 0) (blocksize) (fun i_2 st_1 =>
      let st_1 :=
        array_upd st_1 (i_2) (
          array_index (sbox) (
            uint8_declassify (array_index (state_0) (i_2)))) in 
      (st_1))
    st_1 in 
  st_1.

Definition shift_row
  (i_3 : uint_size)
  (shift_4 : uint_size)
  (state_5 : block)
  : block :=
  let out_6 :=
    state_5 in 
  let out_6 :=
    array_upd out_6 (i_3) (
      array_index (state_5) (
        (i_3) + ((usize 4) * ((shift_4) %% (usize 4))))) in 
  let out_6 :=
    array_upd out_6 ((i_3) + (usize 4)) (
      array_index (state_5) (
        (i_3) + ((usize 4) * (((shift_4) + (usize 1)) %% (usize 4))))) in 
  let out_6 :=
    array_upd out_6 ((i_3) + (usize 8)) (
      array_index (state_5) (
        (i_3) + ((usize 4) * (((shift_4) + (usize 2)) %% (usize 4))))) in 
  let out_6 :=
    array_upd out_6 ((i_3) + (usize 12)) (
      array_index (state_5) (
        (i_3) + ((usize 4) * (((shift_4) + (usize 3)) %% (usize 4))))) in 
  out_6.

Definition shift_rows (state_7 : block) : block :=
  let state_8 :=
    shift_row (usize 1) (usize 1) (state_7) in 
  let state_9 :=
    shift_row (usize 2) (usize 2) (state_8) in 
  shift_row (usize 3) (usize 3) (state_9).

Definition xtime (x_10 : uint8) : uint8 :=
  let x1_11 :=
    (x_10) shift_left (usize 1) in 
  let x7_12 :=
    (x_10) shift_right (usize 7) in 
  let x71_13 :=
    (x7_12) .& (secret (repr 1)) in 
  let x711b_14 :=
    (x71_13) .* (secret (repr 27)) in 
  (x1_11) .^ (x711b_14).

Definition mix_column (c_15 : uint_size) (state_16 : block) : block :=
  let i0_17 :=
    (usize 4) * (c_15) in 
  let s0_18 :=
    array_index (state_16) (i0_17) in 
  let s1_19 :=
    array_index (state_16) ((i0_17) + (usize 1)) in 
  let s2_20 :=
    array_index (state_16) ((i0_17) + (usize 2)) in 
  let s3_21 :=
    array_index (state_16) ((i0_17) + (usize 3)) in 
  let st_22 :=
    state_16 in 
  let tmp_23 :=
    (((s0_18) .^ (s1_19)) .^ (s2_20)) .^ (s3_21) in 
  let st_22 :=
    array_upd st_22 (i0_17) (
      ((s0_18) .^ (tmp_23)) .^ (xtime ((s0_18) .^ (s1_19)))) in 
  let st_22 :=
    array_upd st_22 ((i0_17) + (usize 1)) (
      ((s1_19) .^ (tmp_23)) .^ (xtime ((s1_19) .^ (s2_20)))) in 
  let st_22 :=
    array_upd st_22 ((i0_17) + (usize 2)) (
      ((s2_20) .^ (tmp_23)) .^ (xtime ((s2_20) .^ (s3_21)))) in 
  let st_22 :=
    array_upd st_22 ((i0_17) + (usize 3)) (
      ((s3_21) .^ (tmp_23)) .^ (xtime ((s3_21) .^ (s0_18)))) in 
  st_22.

Definition mix_columns (state_24 : block) : block :=
  let state_25 :=
    mix_column (usize 0) (state_24) in 
  let state_26 :=
    mix_column (usize 1) (state_25) in 
  let state_27 :=
    mix_column (usize 2) (state_26) in 
  mix_column (usize 3) (state_27).

Definition add_round_key (state_28 : block) (key_29 : round_key) : block :=
  let out_30 :=
    state_28 in 
  let out_30 :=
    foldi (usize 0) (blocksize) (fun i_31 out_30 =>
      let out_30 :=
        array_upd out_30 (i_31) (
          (array_index (out_30) (i_31)) .^ (array_index (key_29) (i_31))) in 
      (out_30))
    out_30 in 
  out_30.

Definition aes_enc (state_32 : block) (round_key_33 : round_key) : block :=
  let state_34 :=
    sub_bytes (state_32) in 
  let state_35 :=
    shift_rows (state_34) in 
  let state_36 :=
    mix_columns (state_35) in 
  add_round_key (state_36) (round_key_33).

Definition aes_enc_last (state_37 : block) (round_key_38 : round_key) : block :=
  let state_39 :=
    sub_bytes (state_37) in 
  let state_40 :=
    shift_rows (state_39) in 
  add_round_key (state_40) (round_key_38).

Definition rounds_aes (state_41 : block) (key_42 : byte_seq) : block :=
  let out_43 :=
    state_41 in 
  let out_43 :=
    foldi (usize 0) (seq_num_chunks (key_42) (blocksize)) (fun i_44 out_43 =>
      let '(_, key_block_45) :=
        seq_get_chunk (key_42) (blocksize) (i_44) in 
      let out_43 :=
        aes_enc (out_43) (array_from_seq (blocksize) (key_block_45)) in 
      (out_43))
    out_43 in 
  out_43.

Definition block_cipher_aes
  (input_46 : block)
  (key_47 : byte_seq)
  (nr_48 : uint_size)
  : block :=
  let k0_49 :=
    array_from_slice_range (secret (repr 0)) (blocksize) (key_47) (
      (usize 0, usize 16)) in 
  let k_50 :=
    seq_from_slice_range (key_47) ((usize 16, (nr_48) * (usize 16))) in 
  let kn_51 :=
    array_from_slice (secret (repr 0)) (blocksize) (key_47) (
      (nr_48) * (usize 16)) (usize 16) in 
  let state_52 :=
    add_round_key (input_46) (k0_49) in 
  let state_53 :=
    rounds_aes (state_52) (k_50) in 
  aes_enc_last (state_53) (kn_51).

Definition rotate_word (w_54 : word) : word :=
  array_from_list uint8 (
    let l :=
      [
        array_index (w_54) (usize 1);
        array_index (w_54) (usize 2);
        array_index (w_54) (usize 3);
        array_index (w_54) (usize 0)
      ] in  l).

Definition slice_word (w_55 : word) : word :=
  array_from_list uint8 (
    let l :=
      [
        array_index (sbox) (
          @cast _ uint32 _ (uint8_declassify (array_index (w_55) (usize 0))));
        array_index (sbox) (
          @cast _ uint32 _ (uint8_declassify (array_index (w_55) (usize 1))));
        array_index (sbox) (
          @cast _ uint32 _ (uint8_declassify (array_index (w_55) (usize 2))));
        array_index (sbox) (
          @cast _ uint32 _ (uint8_declassify (array_index (w_55) (usize 3))))
      ] in  l).

Definition aes_keygen_assist (w_56 : word) (rcon_57 : uint8) : word :=
  let k_58 :=
    rotate_word (w_56) in 
  let k_58 :=
    slice_word (k_58) in 
  let k_58 :=
    array_upd k_58 (usize 0) ((array_index (k_58) (usize 0)) .^ (rcon_57)) in 
  k_58.

Definition key_expansion_word
  (w0_59 : word)
  (w1_60 : word)
  (i_61 : uint_size)
  (nk_62 : uint_size)
  (nr_63 : uint_size)
  : (bool × word) :=
  let k_64 :=
    w1_60 in 
  let success_65 :=
    false in 
  let '(k_64, success_65) :=
    if (i_61) <.? ((usize 4) * ((nr_63) + (usize 1))):bool then (
      let '(k_64) :=
        if ((i_61) %% (nk_62)) =.? (usize 0):bool then (
          let k_64 :=
            aes_keygen_assist (k_64) (array_index (rcon) ((i_61) / (nk_62))) in 
          (k_64)
        ) else (
          let '(k_64) :=
            if ((nk_62) >.? (usize 6)) && (
              ((i_61) %% (nk_62)) =.? (usize 4)):bool then (
              let k_64 :=
                slice_word (k_64) in 
              (k_64)
            ) else ( (k_64)
            ) in 
          (k_64)
        ) in 
      let k_64 :=
        foldi (usize 0) (usize 4) (fun i_66 k_64 =>
          let k_64 :=
            array_upd k_64 (i_66) (
              (array_index (k_64) (i_66)) .^ (array_index (w0_59) (i_66))) in 
          (k_64))
        k_64 in 
      let success_65 :=
        true in 
      (k_64, success_65)
    ) else (
      let k_64 :=
        array_new_ (secret (repr 0)) (key_length) in 
      (k_64, success_65)
    ) in 
  (success_65, k_64).

Definition key_expansion_aes
  (key_67 : byte_seq)
  (nk_68 : uint_size)
  (nr_69 : uint_size)
  (key_schedule_length_70 : uint_size)
  (key_length_71 : uint_size)
  (iterations_72 : uint_size)
  : (bool × byte_seq) :=
  let key_ex_73 :=
    seq_new_ (secret (repr 0)) (key_schedule_length_70) in 
  let key_ex_73 :=
    seq_update_start (key_ex_73) (key_67) in 
  let word_size_74 :=
    key_length_71 in 
  let success_75 :=
    true in 
  let '(key_ex_73, success_75) :=
    foldi (usize 0) (iterations_72) (fun j_76 '(key_ex_73, success_75) =>
      let '(key_ex_73, success_75) :=
        if success_75:bool then (
          let i_77 :=
            (j_76) + (word_size_74) in 
          let '(exp_success_78, word_79) :=
            key_expansion_word (
              array_from_slice (secret (repr 0)) (key_length) (key_ex_73) (
                (usize 4) * ((i_77) - (word_size_74))) (usize 4)) (
              array_from_slice (secret (repr 0)) (key_length) (key_ex_73) (
                ((usize 4) * (i_77)) - (usize 4)) (usize 4)) (i_77) (nk_68) (
              nr_69) in 
          let '(key_ex_73, success_75) :=
            if negb (exp_success_78):bool then (
              let success_75 :=
                false in 
              let key_ex_73 :=
                seq_new_ (secret (repr 0)) (usize 0) in 
              (key_ex_73, success_75)
            ) else ( (key_ex_73, success_75)
            ) in 
          let key_ex_73 :=
            seq_update (key_ex_73) ((usize 4) * (i_77)) (word_79) in 
          (key_ex_73, success_75)
        ) else ( (key_ex_73, success_75)
        ) in 
      (key_ex_73, success_75))
    (key_ex_73, success_75) in 
  (success_75, key_ex_73).

Definition aes_encrypt_block
  (k_80 : byte_seq)
  (input_81 : block)
  (nk_82 : uint_size)
  (nr_83 : uint_size)
  (key_schedule_length_84 : uint_size)
  (key_length_85 : uint_size)
  (iterations_86 : uint_size)
  : (bool × block) :=
  let '(success_87, key_ex_88) :=
    key_expansion_aes (k_80) (nk_82) (nr_83) (key_schedule_length_84) (
      key_length_85) (iterations_86) in 
  let result_89 :=
    if (success_87):bool then (
      (true, block_cipher_aes (input_81) (key_ex_88) (nr_83))) else (
      (false, array_new_ (secret (repr 0)) (blocksize))) in 
  result_89.

Definition aes128_encrypt_block
  (k_90 : key128)
  (input_91 : block)
  : (bool × block) :=
  aes_encrypt_block (seq_from_seq (k_90)) (input_91) (key_length) (rounds) (
    key_schedule_length) (key_length) (iterations).

Definition aes_ctr_keyblock
  (k_92 : byte_seq)
  (n_93 : nonce)
  (c_94 : uint32)
  (nk_95 : uint_size)
  (nr_96 : uint_size)
  (key_schedule_length_97 : uint_size)
  (key_length_98 : uint_size)
  (iterations_99 : uint_size)
  : (bool × block) :=
  let input_100 :=
    array_new_ (secret (repr 0)) (blocksize) in 
  let input_100 :=
    array_update (input_100) (usize 0) (n_93) in 
  let input_100 :=
    array_update (input_100) (usize 12) (uint32_to_be_bytes (c_94)) in 
  aes_encrypt_block (k_92) (input_100) (nk_95) (nr_96) (
    key_schedule_length_97) (key_length_98) (iterations_99).

Definition xor_block (block_101 : block) (keyblock_102 : block) : block :=
  let out_103 :=
    block_101 in 
  let out_103 :=
    foldi (usize 0) (blocksize) (fun i_104 out_103 =>
      let out_103 :=
        array_upd out_103 (i_104) (
          (array_index (out_103) (i_104)) .^ (
            array_index (keyblock_102) (i_104))) in 
      (out_103))
    out_103 in 
  out_103.

Definition aes_counter_mode
  (key_105 : byte_seq)
  (nonce_106 : nonce)
  (counter_107 : uint32)
  (msg_108 : byte_seq)
  (nk_109 : uint_size)
  (nr_110 : uint_size)
  (key_schedule_length_111 : uint_size)
  (key_length_112 : uint_size)
  (iterations_113 : uint_size)
  : (bool × byte_seq) :=
  let ctr_114 :=
    counter_107 in 
  let blocks_out_115 :=
    seq_new_ (secret (repr 0)) (seq_len (msg_108)) in 
  let success_116 :=
    true in 
  let '(ctr_114, blocks_out_115, success_116) :=
    foldi (usize 0) (seq_num_chunks (msg_108) (blocksize)) (fun i_117 '(
        ctr_114,
        blocks_out_115,
        success_116
      ) =>
      let '(ctr_114, blocks_out_115, success_116) :=
        if success_116:bool then (
          let '(block_len_118, msg_block_119) :=
            seq_get_chunk (msg_108) (blocksize) (i_117) in 
          let '(kb_success_120, key_block_121) :=
            aes_ctr_keyblock (key_105) (nonce_106) (ctr_114) (nk_109) (nr_110) (
              key_schedule_length_111) (key_length_112) (iterations_113) in 
          let '(blocks_out_115, success_116) :=
            if negb (kb_success_120):bool then (
              let success_116 :=
                false in 
              let blocks_out_115 :=
                seq_new_ (secret (repr 0)) (usize 0) in 
              (blocks_out_115, success_116)
            ) else ( (blocks_out_115, success_116)
            ) in 
          let '(ctr_114, blocks_out_115) :=
            if (seq_len (msg_block_119)) =.? (blocksize):bool then (
              let blocks_out_115 :=
                seq_set_chunk (blocks_out_115) (blocksize) (i_117) (
                  xor_block (array_from_seq (blocksize) (msg_block_119)) (
                    key_block_121)) in 
              let ctr_114 :=
                (ctr_114) .+ (secret (repr 1)) in 
              (ctr_114, blocks_out_115)
            ) else (
              let last_block_122 :=
                array_update_start (array_new_ (secret (repr 0)) (blocksize)) (
                  msg_block_119) in 
              let blocks_out_115 :=
                seq_set_chunk (blocks_out_115) (blocksize) (i_117) (
                  array_slice_range (
                    xor_block (last_block_122) (key_block_121)) (
                    (usize 0, block_len_118))) in 
              (ctr_114, blocks_out_115)
            ) in 
          (ctr_114, blocks_out_115, success_116)
        ) else ( (ctr_114, blocks_out_115, success_116)
        ) in 
      (ctr_114, blocks_out_115, success_116))
    (ctr_114, blocks_out_115, success_116) in 
  (success_116, blocks_out_115).

Definition aes128_encrypt
  (key_123 : key128)
  (nonce_124 : nonce)
  (counter_125 : uint32)
  (msg_126 : byte_seq)
  : byte_seq :=
  let '(success_127, result_128) :=
    aes_counter_mode (seq_from_seq (key_123)) (nonce_124) (counter_125) (
      msg_126) (key_length) (rounds) (key_schedule_length) (key_length) (
      iterations) in 
  result_128.

Definition aes128_decrypt
  (key_129 : key128)
  (nonce_130 : nonce)
  (counter_131 : uint32)
  (ctxt_132 : byte_seq)
  : byte_seq :=
  let '(success_133, result_134) :=
    aes_counter_mode (seq_from_seq (key_129)) (nonce_130) (counter_131) (
      ctxt_132) (key_length) (rounds) (key_schedule_length) (key_length) (
      iterations) in 
  result_134.

