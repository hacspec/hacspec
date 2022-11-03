(** This file was automatically generated using Hacspec **)
Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
Require Import Hacspec_Lib.

Definition block_size_v : uint_size :=
  usize 128.

Definition len_size_v : uint_size :=
  usize 16.

Definition k_size_v : uint_size :=
  usize 80.

Definition hash_size_v : uint_size :=
  (usize 512) / (usize 8).

Definition block_t := nseq (uint8) (block_size_v).

Definition op_table_type_t := nseq (uint_size) (usize 12).

Definition sha512_digest_t := nseq (uint8) (hash_size_v).

Definition round_constants_table_t := nseq (uint64) (k_size_v).

Definition hash_t := nseq (uint64) (usize 8).

Definition ch (x_2158 : uint64) (y_2159 : uint64) (z_2160 : uint64) : uint64 :=
  ((x_2158) .& (y_2159)) .^ ((not (x_2158)) .& (z_2160)).

Definition maj (x_2161 : uint64) (y_2162 : uint64) (z_2163 : uint64) : uint64 :=
  ((x_2161) .& (y_2162)) .^ (((x_2161) .& (z_2163)) .^ ((y_2162) .& (z_2163))).

Definition op_table_v : op_table_type_t :=
  array_from_list uint_size (let l :=
      [
        usize 28;
        usize 34;
        usize 39;
        usize 14;
        usize 18;
        usize 41;
        usize 1;
        usize 8;
        usize 7;
        usize 19;
        usize 61;
        usize 6
      ] in  l).

Definition k_table_v : round_constants_table_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 4794697086780616226) : int64;
        secret (@repr WORDSIZE64 8158064640168781261) : int64;
        secret (@repr WORDSIZE64 13096744586834688815) : int64;
        secret (@repr WORDSIZE64 16840607885511220156) : int64;
        secret (@repr WORDSIZE64 4131703408338449720) : int64;
        secret (@repr WORDSIZE64 6480981068601479193) : int64;
        secret (@repr WORDSIZE64 10538285296894168987) : int64;
        secret (@repr WORDSIZE64 12329834152419229976) : int64;
        secret (@repr WORDSIZE64 15566598209576043074) : int64;
        secret (@repr WORDSIZE64 1334009975649890238) : int64;
        secret (@repr WORDSIZE64 2608012711638119052) : int64;
        secret (@repr WORDSIZE64 6128411473006802146) : int64;
        secret (@repr WORDSIZE64 8268148722764581231) : int64;
        secret (@repr WORDSIZE64 9286055187155687089) : int64;
        secret (@repr WORDSIZE64 11230858885718282805) : int64;
        secret (@repr WORDSIZE64 13951009754708518548) : int64;
        secret (@repr WORDSIZE64 16472876342353939154) : int64;
        secret (@repr WORDSIZE64 17275323862435702243) : int64;
        secret (@repr WORDSIZE64 1135362057144423861) : int64;
        secret (@repr WORDSIZE64 2597628984639134821) : int64;
        secret (@repr WORDSIZE64 3308224258029322869) : int64;
        secret (@repr WORDSIZE64 5365058923640841347) : int64;
        secret (@repr WORDSIZE64 6679025012923562964) : int64;
        secret (@repr WORDSIZE64 8573033837759648693) : int64;
        secret (@repr WORDSIZE64 10970295158949994411) : int64;
        secret (@repr WORDSIZE64 12119686244451234320) : int64;
        secret (@repr WORDSIZE64 12683024718118986047) : int64;
        secret (@repr WORDSIZE64 13788192230050041572) : int64;
        secret (@repr WORDSIZE64 14330467153632333762) : int64;
        secret (@repr WORDSIZE64 15395433587784984357) : int64;
        secret (@repr WORDSIZE64 489312712824947311) : int64;
        secret (@repr WORDSIZE64 1452737877330783856) : int64;
        secret (@repr WORDSIZE64 2861767655752347644) : int64;
        secret (@repr WORDSIZE64 3322285676063803686) : int64;
        secret (@repr WORDSIZE64 5560940570517711597) : int64;
        secret (@repr WORDSIZE64 5996557281743188959) : int64;
        secret (@repr WORDSIZE64 7280758554555802590) : int64;
        secret (@repr WORDSIZE64 8532644243296465576) : int64;
        secret (@repr WORDSIZE64 9350256976987008742) : int64;
        secret (@repr WORDSIZE64 10552545826968843579) : int64;
        secret (@repr WORDSIZE64 11727347734174303076) : int64;
        secret (@repr WORDSIZE64 12113106623233404929) : int64;
        secret (@repr WORDSIZE64 14000437183269869457) : int64;
        secret (@repr WORDSIZE64 14369950271660146224) : int64;
        secret (@repr WORDSIZE64 15101387698204529176) : int64;
        secret (@repr WORDSIZE64 15463397548674623760) : int64;
        secret (@repr WORDSIZE64 17586052441742319658) : int64;
        secret (@repr WORDSIZE64 1182934255886127544) : int64;
        secret (@repr WORDSIZE64 1847814050463011016) : int64;
        secret (@repr WORDSIZE64 2177327727835720531) : int64;
        secret (@repr WORDSIZE64 2830643537854262169) : int64;
        secret (@repr WORDSIZE64 3796741975233480872) : int64;
        secret (@repr WORDSIZE64 4115178125766777443) : int64;
        secret (@repr WORDSIZE64 5681478168544905931) : int64;
        secret (@repr WORDSIZE64 6601373596472566643) : int64;
        secret (@repr WORDSIZE64 7507060721942968483) : int64;
        secret (@repr WORDSIZE64 8399075790359081724) : int64;
        secret (@repr WORDSIZE64 8693463985226723168) : int64;
        secret (@repr WORDSIZE64 9568029438360202098) : int64;
        secret (@repr WORDSIZE64 10144078919501101548) : int64;
        secret (@repr WORDSIZE64 10430055236837252648) : int64;
        secret (@repr WORDSIZE64 11840083180663258601) : int64;
        secret (@repr WORDSIZE64 13761210420658862357) : int64;
        secret (@repr WORDSIZE64 14299343276471374635) : int64;
        secret (@repr WORDSIZE64 14566680578165727644) : int64;
        secret (@repr WORDSIZE64 15097957966210449927) : int64;
        secret (@repr WORDSIZE64 16922976911328602910) : int64;
        secret (@repr WORDSIZE64 17689382322260857208) : int64;
        secret (@repr WORDSIZE64 500013540394364858) : int64;
        secret (@repr WORDSIZE64 748580250866718886) : int64;
        secret (@repr WORDSIZE64 1242879168328830382) : int64;
        secret (@repr WORDSIZE64 1977374033974150939) : int64;
        secret (@repr WORDSIZE64 2944078676154940804) : int64;
        secret (@repr WORDSIZE64 3659926193048069267) : int64;
        secret (@repr WORDSIZE64 4368137639120453308) : int64;
        secret (@repr WORDSIZE64 4836135668995329356) : int64;
        secret (@repr WORDSIZE64 5532061633213252278) : int64;
        secret (@repr WORDSIZE64 6448918945643986474) : int64;
        secret (@repr WORDSIZE64 6902733635092675308) : int64;
        secret (@repr WORDSIZE64 7801388544844847127) : int64
      ] in  l).

Definition hash_init_v : hash_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 7640891576956012808) : int64;
        secret (@repr WORDSIZE64 13503953896175478587) : int64;
        secret (@repr WORDSIZE64 4354685564936845355) : int64;
        secret (@repr WORDSIZE64 11912009170470909681) : int64;
        secret (@repr WORDSIZE64 5840696475078001361) : int64;
        secret (@repr WORDSIZE64 11170449401992604703) : int64;
        secret (@repr WORDSIZE64 2270897969802886507) : int64;
        secret (@repr WORDSIZE64 6620516959819538809) : int64
      ] in  l).

Definition sigma
  (x_2164 : uint64)
  (i_2165 : uint_size)
  (op_2166 : uint_size)
  : uint64 :=
  let tmp_2167 : uint64 :=
    uint64_rotate_right (x_2164) (array_index (op_table_v) (((usize 3) * (
            i_2165)) + (usize 2))) in 
  let '(tmp_2167) :=
    if (op_2166) =.? (usize 0):bool then (let tmp_2167 :=
        (x_2164) shift_right (array_index (op_table_v) (((usize 3) * (
                i_2165)) + (usize 2))) in 
      (tmp_2167)) else ((tmp_2167)) in 
  ((uint64_rotate_right (x_2164) (array_index (op_table_v) ((usize 3) * (
            i_2165)))) .^ (uint64_rotate_right (x_2164) (array_index (
          op_table_v) (((usize 3) * (i_2165)) + (usize 1))))) .^ (tmp_2167).

Definition schedule (block_2168 : block_t) : round_constants_table_t :=
  let b_2169 : seq uint64 :=
    array_to_be_uint64s (block_2168) in 
  let s_2170 : round_constants_table_t :=
    array_new_ (default) (k_size_v) in 
  let s_2170 :=
    foldi (usize 0) (k_size_v) (fun i_2171 s_2170 =>
      let '(s_2170) :=
        if (i_2171) <.? (usize 16):bool then (let s_2170 :=
            array_upd s_2170 (i_2171) (seq_index (b_2169) (i_2171)) in 
          (s_2170)) else (let t16_2172 : uint64 :=
            array_index (s_2170) ((i_2171) - (usize 16)) in 
          let t15_2173 : uint64 :=
            array_index (s_2170) ((i_2171) - (usize 15)) in 
          let t7_2174 : uint64 :=
            array_index (s_2170) ((i_2171) - (usize 7)) in 
          let t2_2175 : uint64 :=
            array_index (s_2170) ((i_2171) - (usize 2)) in 
          let s1_2176 : uint64 :=
            sigma (t2_2175) (usize 3) (usize 0) in 
          let s0_2177 : uint64 :=
            sigma (t15_2173) (usize 2) (usize 0) in 
          let s_2170 :=
            array_upd s_2170 (i_2171) ((((s1_2176) .+ (t7_2174)) .+ (
                  s0_2177)) .+ (t16_2172)) in 
          (s_2170)) in 
      (s_2170))
    s_2170 in 
  s_2170.

Definition shuffle
  (ws_2178 : round_constants_table_t)
  (hashi_2179 : hash_t)
  : hash_t :=
  let h_2180 : hash_t :=
    hashi_2179 in 
  let h_2180 :=
    foldi (usize 0) (k_size_v) (fun i_2181 h_2180 =>
      let a0_2182 : uint64 :=
        array_index (h_2180) (usize 0) in 
      let b0_2183 : uint64 :=
        array_index (h_2180) (usize 1) in 
      let c0_2184 : uint64 :=
        array_index (h_2180) (usize 2) in 
      let d0_2185 : uint64 :=
        array_index (h_2180) (usize 3) in 
      let e0_2186 : uint64 :=
        array_index (h_2180) (usize 4) in 
      let f0_2187 : uint64 :=
        array_index (h_2180) (usize 5) in 
      let g0_2188 : uint64 :=
        array_index (h_2180) (usize 6) in 
      let h0_2189 : uint64 :=
        array_index (h_2180) (usize 7) in 
      let t1_2190 : uint64 :=
        ((((h0_2189) .+ (sigma (e0_2186) (usize 1) (usize 1))) .+ (ch (
                e0_2186) (f0_2187) (g0_2188))) .+ (array_index (k_table_v) (
              i_2181))) .+ (array_index (ws_2178) (i_2181)) in 
      let t2_2191 : uint64 :=
        (sigma (a0_2182) (usize 0) (usize 1)) .+ (maj (a0_2182) (b0_2183) (
            c0_2184)) in 
      let h_2180 :=
        array_upd h_2180 (usize 0) ((t1_2190) .+ (t2_2191)) in 
      let h_2180 :=
        array_upd h_2180 (usize 1) (a0_2182) in 
      let h_2180 :=
        array_upd h_2180 (usize 2) (b0_2183) in 
      let h_2180 :=
        array_upd h_2180 (usize 3) (c0_2184) in 
      let h_2180 :=
        array_upd h_2180 (usize 4) ((d0_2185) .+ (t1_2190)) in 
      let h_2180 :=
        array_upd h_2180 (usize 5) (e0_2186) in 
      let h_2180 :=
        array_upd h_2180 (usize 6) (f0_2187) in 
      let h_2180 :=
        array_upd h_2180 (usize 7) (g0_2188) in 
      (h_2180))
    h_2180 in 
  h_2180.

Definition compress (block_2192 : block_t) (h_in_2193 : hash_t) : hash_t :=
  let s_2194 : round_constants_table_t :=
    schedule (block_2192) in 
  let h_2195 : hash_t :=
    shuffle (s_2194) (h_in_2193) in 
  let h_2195 :=
    foldi (usize 0) (usize 8) (fun i_2196 h_2195 =>
      let h_2195 :=
        array_upd h_2195 (i_2196) ((array_index (h_2195) (i_2196)) .+ (
            array_index (h_in_2193) (i_2196))) in 
      (h_2195))
    h_2195 in 
  h_2195.

Definition hash (msg_2197 : byte_seq) : sha512_digest_t :=
  let h_2198 : hash_t :=
    hash_init_v in 
  let last_block_2199 : block_t :=
    array_new_ (default) (block_size_v) in 
  let last_block_len_2200 : uint_size :=
    usize 0 in 
  let '(h_2198, last_block_2199, last_block_len_2200) :=
    foldi (usize 0) (seq_num_chunks (msg_2197) (block_size_v)) (fun i_2201 '(
        h_2198,
        last_block_2199,
        last_block_len_2200
      ) =>
      let '(block_len_2202, block_2203) :=
        seq_get_chunk (msg_2197) (block_size_v) (i_2201) in 
      let '(h_2198, last_block_2199, last_block_len_2200) :=
        if (block_len_2202) <.? (block_size_v):bool then (let last_block_2199 :=
            array_update_start (array_new_ (default) (block_size_v)) (
              block_2203) in 
          let last_block_len_2200 :=
            block_len_2202 in 
          (h_2198, last_block_2199, last_block_len_2200)) else (
          let compress_input_2204 : block_t :=
            array_from_seq (block_size_v) (block_2203) in 
          let h_2198 :=
            compress (compress_input_2204) (h_2198) in 
          (h_2198, last_block_2199, last_block_len_2200)) in 
      (h_2198, last_block_2199, last_block_len_2200))
    (h_2198, last_block_2199, last_block_len_2200) in 
  let last_block_2199 :=
    array_upd last_block_2199 (last_block_len_2200) (secret (
        @repr WORDSIZE8 128) : int8) in 
  let len_bist_2205 : uint128 :=
    secret (pub_u128 ((seq_len (msg_2197)) * (usize 8))) : int128 in 
  let '(h_2198, last_block_2199) :=
    if (last_block_len_2200) <.? ((block_size_v) - (len_size_v)):bool then (
      let last_block_2199 :=
        array_update (last_block_2199) ((block_size_v) - (len_size_v)) (
          array_to_seq (uint128_to_be_bytes (len_bist_2205))) in 
      let h_2198 :=
        compress (last_block_2199) (h_2198) in 
      (h_2198, last_block_2199)) else (let pad_block_2206 : block_t :=
        array_new_ (default) (block_size_v) in 
      let pad_block_2206 :=
        array_update (pad_block_2206) ((block_size_v) - (len_size_v)) (
          array_to_seq (uint128_to_be_bytes (len_bist_2205))) in 
      let h_2198 :=
        compress (last_block_2199) (h_2198) in 
      let h_2198 :=
        compress (pad_block_2206) (h_2198) in 
      (h_2198, last_block_2199)) in 
  array_from_seq (hash_size_v) (array_to_be_bytes (h_2198)).

Definition sha512 (msg_2207 : byte_seq) : sha512_digest_t :=
  hash (msg_2207).

