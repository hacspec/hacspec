(** This file was automatically generated using Hacspec **)
Set Warnings "-notation-overridden,-ambiguous-paths".
Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
Require Import Hacspec_Lib.

Definition s_box_t := nseq (int8) (usize 256).

Definition r_con_t := nseq (int8) (usize 15).

Definition p_bytes256_t := nseq (int8) (usize 256).

Definition sbox_v : s_box_t :=
  array_from_list int8 (let l :=
      [
        @repr WORDSIZE8 99;
        @repr WORDSIZE8 124;
        @repr WORDSIZE8 119;
        @repr WORDSIZE8 123;
        @repr WORDSIZE8 242;
        @repr WORDSIZE8 107;
        @repr WORDSIZE8 111;
        @repr WORDSIZE8 197;
        @repr WORDSIZE8 48;
        @repr WORDSIZE8 1;
        @repr WORDSIZE8 103;
        @repr WORDSIZE8 43;
        @repr WORDSIZE8 254;
        @repr WORDSIZE8 215;
        @repr WORDSIZE8 171;
        @repr WORDSIZE8 118;
        @repr WORDSIZE8 202;
        @repr WORDSIZE8 130;
        @repr WORDSIZE8 201;
        @repr WORDSIZE8 125;
        @repr WORDSIZE8 250;
        @repr WORDSIZE8 89;
        @repr WORDSIZE8 71;
        @repr WORDSIZE8 240;
        @repr WORDSIZE8 173;
        @repr WORDSIZE8 212;
        @repr WORDSIZE8 162;
        @repr WORDSIZE8 175;
        @repr WORDSIZE8 156;
        @repr WORDSIZE8 164;
        @repr WORDSIZE8 114;
        @repr WORDSIZE8 192;
        @repr WORDSIZE8 183;
        @repr WORDSIZE8 253;
        @repr WORDSIZE8 147;
        @repr WORDSIZE8 38;
        @repr WORDSIZE8 54;
        @repr WORDSIZE8 63;
        @repr WORDSIZE8 247;
        @repr WORDSIZE8 204;
        @repr WORDSIZE8 52;
        @repr WORDSIZE8 165;
        @repr WORDSIZE8 229;
        @repr WORDSIZE8 241;
        @repr WORDSIZE8 113;
        @repr WORDSIZE8 216;
        @repr WORDSIZE8 49;
        @repr WORDSIZE8 21;
        @repr WORDSIZE8 4;
        @repr WORDSIZE8 199;
        @repr WORDSIZE8 35;
        @repr WORDSIZE8 195;
        @repr WORDSIZE8 24;
        @repr WORDSIZE8 150;
        @repr WORDSIZE8 5;
        @repr WORDSIZE8 154;
        @repr WORDSIZE8 7;
        @repr WORDSIZE8 18;
        @repr WORDSIZE8 128;
        @repr WORDSIZE8 226;
        @repr WORDSIZE8 235;
        @repr WORDSIZE8 39;
        @repr WORDSIZE8 178;
        @repr WORDSIZE8 117;
        @repr WORDSIZE8 9;
        @repr WORDSIZE8 131;
        @repr WORDSIZE8 44;
        @repr WORDSIZE8 26;
        @repr WORDSIZE8 27;
        @repr WORDSIZE8 110;
        @repr WORDSIZE8 90;
        @repr WORDSIZE8 160;
        @repr WORDSIZE8 82;
        @repr WORDSIZE8 59;
        @repr WORDSIZE8 214;
        @repr WORDSIZE8 179;
        @repr WORDSIZE8 41;
        @repr WORDSIZE8 227;
        @repr WORDSIZE8 47;
        @repr WORDSIZE8 132;
        @repr WORDSIZE8 83;
        @repr WORDSIZE8 209;
        @repr WORDSIZE8 0;
        @repr WORDSIZE8 237;
        @repr WORDSIZE8 32;
        @repr WORDSIZE8 252;
        @repr WORDSIZE8 177;
        @repr WORDSIZE8 91;
        @repr WORDSIZE8 106;
        @repr WORDSIZE8 203;
        @repr WORDSIZE8 190;
        @repr WORDSIZE8 57;
        @repr WORDSIZE8 74;
        @repr WORDSIZE8 76;
        @repr WORDSIZE8 88;
        @repr WORDSIZE8 207;
        @repr WORDSIZE8 208;
        @repr WORDSIZE8 239;
        @repr WORDSIZE8 170;
        @repr WORDSIZE8 251;
        @repr WORDSIZE8 67;
        @repr WORDSIZE8 77;
        @repr WORDSIZE8 51;
        @repr WORDSIZE8 133;
        @repr WORDSIZE8 69;
        @repr WORDSIZE8 249;
        @repr WORDSIZE8 2;
        @repr WORDSIZE8 127;
        @repr WORDSIZE8 80;
        @repr WORDSIZE8 60;
        @repr WORDSIZE8 159;
        @repr WORDSIZE8 168;
        @repr WORDSIZE8 81;
        @repr WORDSIZE8 163;
        @repr WORDSIZE8 64;
        @repr WORDSIZE8 143;
        @repr WORDSIZE8 146;
        @repr WORDSIZE8 157;
        @repr WORDSIZE8 56;
        @repr WORDSIZE8 245;
        @repr WORDSIZE8 188;
        @repr WORDSIZE8 182;
        @repr WORDSIZE8 218;
        @repr WORDSIZE8 33;
        @repr WORDSIZE8 16;
        @repr WORDSIZE8 255;
        @repr WORDSIZE8 243;
        @repr WORDSIZE8 210;
        @repr WORDSIZE8 205;
        @repr WORDSIZE8 12;
        @repr WORDSIZE8 19;
        @repr WORDSIZE8 236;
        @repr WORDSIZE8 95;
        @repr WORDSIZE8 151;
        @repr WORDSIZE8 68;
        @repr WORDSIZE8 23;
        @repr WORDSIZE8 196;
        @repr WORDSIZE8 167;
        @repr WORDSIZE8 126;
        @repr WORDSIZE8 61;
        @repr WORDSIZE8 100;
        @repr WORDSIZE8 93;
        @repr WORDSIZE8 25;
        @repr WORDSIZE8 115;
        @repr WORDSIZE8 96;
        @repr WORDSIZE8 129;
        @repr WORDSIZE8 79;
        @repr WORDSIZE8 220;
        @repr WORDSIZE8 34;
        @repr WORDSIZE8 42;
        @repr WORDSIZE8 144;
        @repr WORDSIZE8 136;
        @repr WORDSIZE8 70;
        @repr WORDSIZE8 238;
        @repr WORDSIZE8 184;
        @repr WORDSIZE8 20;
        @repr WORDSIZE8 222;
        @repr WORDSIZE8 94;
        @repr WORDSIZE8 11;
        @repr WORDSIZE8 219;
        @repr WORDSIZE8 224;
        @repr WORDSIZE8 50;
        @repr WORDSIZE8 58;
        @repr WORDSIZE8 10;
        @repr WORDSIZE8 73;
        @repr WORDSIZE8 6;
        @repr WORDSIZE8 36;
        @repr WORDSIZE8 92;
        @repr WORDSIZE8 194;
        @repr WORDSIZE8 211;
        @repr WORDSIZE8 172;
        @repr WORDSIZE8 98;
        @repr WORDSIZE8 145;
        @repr WORDSIZE8 149;
        @repr WORDSIZE8 228;
        @repr WORDSIZE8 121;
        @repr WORDSIZE8 231;
        @repr WORDSIZE8 200;
        @repr WORDSIZE8 55;
        @repr WORDSIZE8 109;
        @repr WORDSIZE8 141;
        @repr WORDSIZE8 213;
        @repr WORDSIZE8 78;
        @repr WORDSIZE8 169;
        @repr WORDSIZE8 108;
        @repr WORDSIZE8 86;
        @repr WORDSIZE8 244;
        @repr WORDSIZE8 234;
        @repr WORDSIZE8 101;
        @repr WORDSIZE8 122;
        @repr WORDSIZE8 174;
        @repr WORDSIZE8 8;
        @repr WORDSIZE8 186;
        @repr WORDSIZE8 120;
        @repr WORDSIZE8 37;
        @repr WORDSIZE8 46;
        @repr WORDSIZE8 28;
        @repr WORDSIZE8 166;
        @repr WORDSIZE8 180;
        @repr WORDSIZE8 198;
        @repr WORDSIZE8 232;
        @repr WORDSIZE8 221;
        @repr WORDSIZE8 116;
        @repr WORDSIZE8 31;
        @repr WORDSIZE8 75;
        @repr WORDSIZE8 189;
        @repr WORDSIZE8 139;
        @repr WORDSIZE8 138;
        @repr WORDSIZE8 112;
        @repr WORDSIZE8 62;
        @repr WORDSIZE8 181;
        @repr WORDSIZE8 102;
        @repr WORDSIZE8 72;
        @repr WORDSIZE8 3;
        @repr WORDSIZE8 246;
        @repr WORDSIZE8 14;
        @repr WORDSIZE8 97;
        @repr WORDSIZE8 53;
        @repr WORDSIZE8 87;
        @repr WORDSIZE8 185;
        @repr WORDSIZE8 134;
        @repr WORDSIZE8 193;
        @repr WORDSIZE8 29;
        @repr WORDSIZE8 158;
        @repr WORDSIZE8 225;
        @repr WORDSIZE8 248;
        @repr WORDSIZE8 152;
        @repr WORDSIZE8 17;
        @repr WORDSIZE8 105;
        @repr WORDSIZE8 217;
        @repr WORDSIZE8 142;
        @repr WORDSIZE8 148;
        @repr WORDSIZE8 155;
        @repr WORDSIZE8 30;
        @repr WORDSIZE8 135;
        @repr WORDSIZE8 233;
        @repr WORDSIZE8 206;
        @repr WORDSIZE8 85;
        @repr WORDSIZE8 40;
        @repr WORDSIZE8 223;
        @repr WORDSIZE8 140;
        @repr WORDSIZE8 161;
        @repr WORDSIZE8 137;
        @repr WORDSIZE8 13;
        @repr WORDSIZE8 191;
        @repr WORDSIZE8 230;
        @repr WORDSIZE8 66;
        @repr WORDSIZE8 104;
        @repr WORDSIZE8 65;
        @repr WORDSIZE8 153;
        @repr WORDSIZE8 45;
        @repr WORDSIZE8 15;
        @repr WORDSIZE8 176;
        @repr WORDSIZE8 84;
        @repr WORDSIZE8 187;
        @repr WORDSIZE8 22
      ] in  l).

Definition rcon_v : r_con_t :=
  array_from_list int8 (let l :=
      [
        @repr WORDSIZE8 141;
        @repr WORDSIZE8 1;
        @repr WORDSIZE8 2;
        @repr WORDSIZE8 4;
        @repr WORDSIZE8 8;
        @repr WORDSIZE8 16;
        @repr WORDSIZE8 32;
        @repr WORDSIZE8 64;
        @repr WORDSIZE8 128;
        @repr WORDSIZE8 27;
        @repr WORDSIZE8 54;
        @repr WORDSIZE8 108;
        @repr WORDSIZE8 216;
        @repr WORDSIZE8 171;
        @repr WORDSIZE8 77
      ] in  l).

Definition index_u32 (s_1732 : int128) (i_1733 : uint_size)  : int32 :=
  @cast _ uint32 _ (((s_1732) shift_right ((i_1733) * (usize 32))) .% ((
        @repr WORDSIZE128 1) shift_left (usize 32))).

Definition index_u8 (s_1734 : int32) (i_1735 : uint_size)  : int8 :=
  @cast _ uint8 _ (((s_1734) shift_right ((i_1735) * (usize 8))) .% ((
        @repr WORDSIZE32 1) shift_left (usize 8))).

Definition rebuild_u32
  (s0_1736 : int8)
  (s1_1737 : int8)
  (s2_1738 : int8)
  (s3_1739 : int8)
  
  : int32 :=
  (@cast _ uint32 _ (s0_1736)) .| (((@cast _ uint32 _ (s1_1737)) shift_left (
        usize 8)) .| (((@cast _ uint32 _ (s2_1738)) shift_left (usize 16)) .| ((
          @cast _ uint32 _ (s3_1739)) shift_left (usize 24)))).

Definition rebuild_u128
  (s0_1740 : int32)
  (s1_1741 : int32)
  (s2_1742 : int32)
  (s3_1743 : int32)
  
  : int128 :=
  (@cast _ uint128 _ (s0_1740)) .| (((@cast _ uint128 _ (s1_1741)) shift_left (
        usize 32)) .| (((@cast _ uint128 _ (s2_1742)) shift_left (
          usize 64)) .| ((@cast _ uint128 _ (s3_1743)) shift_left (usize 96)))).

Definition subword (v_1744 : int32)  : int32 :=
  rebuild_u32 (array_index (sbox_v) (index_u8 (v_1744) (usize 0))) (
    array_index (sbox_v) (index_u8 (v_1744) (usize 1))) (array_index (sbox_v) (
      index_u8 (v_1744) (usize 2))) (array_index (sbox_v) (index_u8 (v_1744) (
        usize 3))).

Definition rotword (v_1745 : int32)  : int32 :=
  rebuild_u32 (index_u8 (v_1745) (usize 1)) (index_u8 (v_1745) (usize 2)) (
    index_u8 (v_1745) (usize 3)) (index_u8 (v_1745) (usize 0)).

Definition vpshufd1
  (s_1746 : int128)
  (o_1747 : int8)
  (i_1748 : uint_size)
  
  : int32 :=
  index_u32 ((s_1746) shift_right ((usize 32) * (@cast _ uint32 _ (((
              o_1747) shift_right ((usize 2) * (i_1748))) .% (
            @repr WORDSIZE8 4))))) (usize 0).

Definition vpshufd (s_1749 : int128) (o_1750 : int8)  : int128 :=
  let d1_1751 : int32 :=
    vpshufd1 (s_1749) (o_1750) (usize 0) in 
  let d2_1752 : int32 :=
    vpshufd1 (s_1749) (o_1750) (usize 1) in 
  let d3_1753 : int32 :=
    vpshufd1 (s_1749) (o_1750) (usize 2) in 
  let d4_1754 : int32 :=
    vpshufd1 (s_1749) (o_1750) (usize 3) in 
  rebuild_u128 (d1_1751) (d2_1752) (d3_1753) (d4_1754).

Definition vshufps
  (s1_1755 : int128)
  (s2_1756 : int128)
  (o_1757 : int8)
  
  : int128 :=
  let d1_1758 : int32 :=
    vpshufd1 (s1_1755) (o_1757) (usize 0) in 
  let d2_1759 : int32 :=
    vpshufd1 (s1_1755) (o_1757) (usize 1) in 
  let d3_1760 : int32 :=
    vpshufd1 (s2_1756) (o_1757) (usize 2) in 
  let d4_1761 : int32 :=
    vpshufd1 (s2_1756) (o_1757) (usize 3) in 
  rebuild_u128 (d1_1758) (d2_1759) (d3_1760) (d4_1761).

Definition key_combine
  (rkey_1762 : int128)
  (temp1_1763 : int128)
  (temp2_1764 : int128)
  
  : (int128 '× int128) :=
  let temp1_1765 : int128 :=
    vpshufd (temp1_1763) (@repr WORDSIZE8 255) in 
  let temp2_1766 : int128 :=
    vshufps (temp2_1764) (rkey_1762) (@repr WORDSIZE8 16) in 
  let rkey_1767 : int128 :=
    (rkey_1762) .^ (temp2_1766) in 
  let temp2_1768 : int128 :=
    vshufps (temp2_1766) (rkey_1767) (@repr WORDSIZE8 140) in 
  let rkey_1769 : int128 :=
    (rkey_1767) .^ (temp2_1768) in 
  let rkey_1770 : int128 :=
    (rkey_1769) .^ (temp1_1765) in 
  (rkey_1770, temp2_1768).

Definition aeskeygenassist (v1_1771 : int128) (v2_1772 : int8)  : int128 :=
  let x1_1773 : int32 :=
    index_u32 (v1_1771) (usize 1) in 
  let x3_1774 : int32 :=
    index_u32 (v1_1771) (usize 3) in 
  let y0_1775 : int32 :=
    subword (x1_1773) in 
  let y1_1776 : int32 :=
    (rotword (y0_1775)) .^ (@cast _ uint32 _ (v2_1772)) in 
  let y2_1777 : int32 :=
    subword (x3_1774) in 
  let y3_1778 : int32 :=
    (rotword (y2_1777)) .^ (@cast _ uint32 _ (v2_1772)) in 
  rebuild_u128 (y0_1775) (y1_1776) (y2_1777) (y3_1778).

Definition key_expand
  (rcon_1779 : int8)
  (rkey_1780 : int128)
  (temp2_1781 : int128)
  
  : (int128 '× int128) :=
  let temp1_1782 : int128 :=
    aeskeygenassist (rkey_1780) (rcon_1779) in 
  let '(rkey_1783, temp2_1784) :=
    key_combine (rkey_1780) (temp1_1782) (temp2_1781) in 
  (rkey_1783, temp2_1784).

Notation "'key_list_t'" := (seq int128) : hacspec_scope.

Definition keys_expand (key_1785 : int128)  : key_list_t :=
  let rkeys_1786 : key_list_t :=
    seq_new_ (default : int128) (usize 0) in 
  let key_1787 : int128 :=
    key_1785 in 
  let rkeys_1786 :=
    seq_push (rkeys_1786) (key_1787) in 
  let temp2_1788 : int128 :=
    @repr WORDSIZE128 0 in 
  let '(rkeys_1786, key_1787, temp2_1788) :=
    foldi (usize 1) (usize 11) (fun round_1789 '(
        rkeys_1786,
        key_1787,
        temp2_1788
      ) =>
      let rcon_1790 : int8 :=
        array_index (rcon_v) (round_1789) in 
      let '(key_temp_1791, temp2_temp_1792) :=
        key_expand (rcon_1790) (key_1787) (temp2_1788) in 
      let key_1787 :=
        key_temp_1791 in 
      let temp2_1788 :=
        temp2_temp_1792 in 
      let rkeys_1786 :=
        seq_push (rkeys_1786) (key_1787) in 
      (rkeys_1786, key_1787, temp2_1788))
    (rkeys_1786, key_1787, temp2_1788) in 
  rkeys_1786.

Definition subbytes (s_1793 : int128)  : int128 :=
  rebuild_u128 (subword (index_u32 (s_1793) (usize 0))) (subword (index_u32 (
        s_1793) (usize 1))) (subword (index_u32 (s_1793) (usize 2))) (subword (
      index_u32 (s_1793) (usize 3))).

Definition matrix_index
  (s_1794 : int128)
  (i_1795 : uint_size)
  (j_1796 : uint_size)
  
  : int8 :=
  index_u8 (index_u32 (s_1794) (j_1796)) (i_1795).

Definition shiftrows (s_1797 : int128)  : int128 :=
  rebuild_u128 (rebuild_u32 (matrix_index (s_1797) (usize 0) (usize 0)) (
      matrix_index (s_1797) (usize 1) (usize 1)) (matrix_index (s_1797) (
        usize 2) (usize 2)) (matrix_index (s_1797) (usize 3) (usize 3))) (
    rebuild_u32 (matrix_index (s_1797) (usize 0) (usize 1)) (matrix_index (
        s_1797) (usize 1) (usize 2)) (matrix_index (s_1797) (usize 2) (
        usize 3)) (matrix_index (s_1797) (usize 3) (usize 0))) (rebuild_u32 (
      matrix_index (s_1797) (usize 0) (usize 2)) (matrix_index (s_1797) (
        usize 1) (usize 3)) (matrix_index (s_1797) (usize 2) (usize 0)) (
      matrix_index (s_1797) (usize 3) (usize 1))) (rebuild_u32 (matrix_index (
        s_1797) (usize 0) (usize 3)) (matrix_index (s_1797) (usize 1) (
        usize 0)) (matrix_index (s_1797) (usize 2) (usize 1)) (matrix_index (
        s_1797) (usize 3) (usize 2))).

Definition xtime (x_1798 : int8)  : int8 :=
  let x1_1799 : int8 :=
    (x_1798) shift_left (usize 1) in 
  let x7_1800 : int8 :=
    (x_1798) shift_right (usize 7) in 
  let x71_1801 : int8 :=
    (x7_1800) .& (@repr WORDSIZE8 1) in 
  let x711b_1802 : int8 :=
    (x71_1801) .* (@repr WORDSIZE8 27) in 
  (x1_1799) .^ (x711b_1802).

Definition mixcolumn (c_1803 : uint_size) (state_1804 : int128)  : int32 :=
  let s0_1805 : int8 :=
    matrix_index (state_1804) (usize 0) (c_1803) in 
  let s1_1806 : int8 :=
    matrix_index (state_1804) (usize 1) (c_1803) in 
  let s2_1807 : int8 :=
    matrix_index (state_1804) (usize 2) (c_1803) in 
  let s3_1808 : int8 :=
    matrix_index (state_1804) (usize 3) (c_1803) in 
  let tmp_1809 : int8 :=
    (((s0_1805) .^ (s1_1806)) .^ (s2_1807)) .^ (s3_1808) in 
  let r0_1810 : int8 :=
    ((s0_1805) .^ (tmp_1809)) .^ (xtime ((s0_1805) .^ (s1_1806))) in 
  let r1_1811 : int8 :=
    ((s1_1806) .^ (tmp_1809)) .^ (xtime ((s1_1806) .^ (s2_1807))) in 
  let r2_1812 : int8 :=
    ((s2_1807) .^ (tmp_1809)) .^ (xtime ((s2_1807) .^ (s3_1808))) in 
  let r3_1813 : int8 :=
    ((s3_1808) .^ (tmp_1809)) .^ (xtime ((s3_1808) .^ (s0_1805))) in 
  rebuild_u32 (r0_1810) (r1_1811) (r2_1812) (r3_1813).

Definition mixcolumns (state_1814 : int128)  : int128 :=
  let c0_1815 : int32 :=
    mixcolumn (usize 0) (state_1814) in 
  let c1_1816 : int32 :=
    mixcolumn (usize 1) (state_1814) in 
  let c2_1817 : int32 :=
    mixcolumn (usize 2) (state_1814) in 
  let c3_1818 : int32 :=
    mixcolumn (usize 3) (state_1814) in 
  rebuild_u128 (c0_1815) (c1_1816) (c2_1817) (c3_1818).

Definition aesenc (state_1819 : int128) (rkey_1820 : int128)  : int128 :=
  let state_1821 : int128 :=
    shiftrows (state_1819) in 
  let state_1822 : int128 :=
    subbytes (state_1821) in 
  let state_1823 : int128 :=
    mixcolumns (state_1822) in 
  (state_1823) .^ (rkey_1820).

Definition aesenclast (state_1824 : int128) (rkey_1825 : int128)  : int128 :=
  let state_1826 : int128 :=
    shiftrows (state_1824) in 
  let state_1827 : int128 :=
    subbytes (state_1826) in 
  (state_1827) .^ (rkey_1825).

Definition aes_rounds (rkeys_1828 : key_list_t) (inp_1829 : int128)  : int128 :=
  let state_1830 : int128 :=
    (inp_1829) .^ (seq_index (rkeys_1828) (usize 0)) in 
  let state_1830 :=
    foldi (usize 1) (usize 10) (fun round_1831 state_1830 =>
      let state_1830 :=
        aesenc (state_1830) (seq_index (rkeys_1828) (round_1831)) in 
      (state_1830))
    state_1830 in 
  aesenclast (state_1830) (seq_index (rkeys_1828) (usize 10)).

Definition aes (key_1832 : int128) (inp_1833 : int128)  : int128 :=
  let rkeys_1834 : seq int128 :=
    keys_expand (key_1832) in 
  aes_rounds (rkeys_1834) (inp_1833).

