(** This file was automatically generated using Hacspec **)
Set Warnings "-notation-overridden,-ambiguous-paths".
Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
Require Import Hacspec_Bls12_381.

Require Import Hacspec_Lib.

Require Import Hacspec_Sha256.

Definition fp_hash_canvas_t := nseq (int8) (64).
Definition fp_hash_t :=
  nat_mod 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab.

Definition arr_fp_t := nseq (uint64) (usize 6).

Definition b_in_bytes_v : uint_size :=
  usize 32.

Definition s_in_bytes_v : uint_size :=
  usize 64.

Definition l_v : uint_size :=
  usize 64.

Definition p_1_2_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 936899308823769933) : int64;
        secret (@repr WORDSIZE64 2706051889235351147) : int64;
        secret (@repr WORDSIZE64 12843041017062132063) : int64;
        secret (@repr WORDSIZE64 12941209323636816658) : int64;
        secret (@repr WORDSIZE64 1105070755758604287) : int64;
        secret (@repr WORDSIZE64 15924587544893707605) : int64
      ] in  l).

Definition p_1_4_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 468449654411884966) : int64;
        secret (@repr WORDSIZE64 10576397981472451381) : int64;
        secret (@repr WORDSIZE64 15644892545385841839) : int64;
        secret (@repr WORDSIZE64 15693976698673184137) : int64;
        secret (@repr WORDSIZE64 552535377879302143) : int64;
        secret (@repr WORDSIZE64 17185665809301629611) : int64
      ] in  l).

Definition p_3_4_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 468449654411884966) : int64;
        secret (@repr WORDSIZE64 10576397981472451381) : int64;
        secret (@repr WORDSIZE64 15644892545385841839) : int64;
        secret (@repr WORDSIZE64 15693976698673184137) : int64;
        secret (@repr WORDSIZE64 552535377879302143) : int64;
        secret (@repr WORDSIZE64 17185665809301629610) : int64
      ] in  l).

Definition expand_message_xmd
  (msg_1708 : byte_seq)
  (dst_1709 : byte_seq)
  (len_in_bytes_1710 : uint_size)
  : byte_seq :=
  let ell_1711 : uint_size :=
    (((len_in_bytes_1710) + (b_in_bytes_v)) - (usize 1)) / (b_in_bytes_v) in 
  let dst_prime_1712 : seq uint8 :=
    seq_push (dst_1709) (uint8_from_usize (seq_len (dst_1709))) in 
  let z_pad_1713 : seq uint8 :=
    seq_new_ (default : uint8) (s_in_bytes_v) in 
  let l_i_b_str_1714 : seq uint8 :=
    seq_new_ (default : uint8) (usize 2) in 
  let l_i_b_str_1714 :=
    seq_upd l_i_b_str_1714 (usize 0) (uint8_from_usize ((len_in_bytes_1710) / (
          usize 256))) in 
  let l_i_b_str_1714 :=
    seq_upd l_i_b_str_1714 (usize 1) (uint8_from_usize (len_in_bytes_1710)) in 
  let msg_prime_1715 : seq uint8 :=
    seq_concat (seq_concat (seq_concat (seq_concat (z_pad_1713) (msg_1708)) (
          l_i_b_str_1714)) (seq_new_ (default : uint8) (usize 1))) (
      dst_prime_1712) in 
  let b_0_1716 : seq uint8 :=
    seq_from_seq (array_to_seq (hash (msg_prime_1715))) in 
  let b_i_1717 : seq uint8 :=
    seq_from_seq (array_to_seq (hash (seq_concat (seq_push (b_0_1716) (secret (
              @repr WORDSIZE8 1) : int8)) (dst_prime_1712)))) in 
  let uniform_bytes_1718 : seq uint8 :=
    seq_from_seq (b_i_1717) in 
  let '(b_i_1717, uniform_bytes_1718) :=
    foldi (usize 2) ((ell_1711) + (usize 1)) (fun i_1719 '(
        b_i_1717,
        uniform_bytes_1718
      ) =>
      let t_1720 : seq uint8 :=
        seq_from_seq (b_0_1716) in 
      let b_i_1717 :=
        seq_from_seq (array_to_seq (hash (seq_concat (seq_push ((
                  t_1720) seq_xor (b_i_1717)) (uint8_from_usize (i_1719))) (
              dst_prime_1712)))) in 
      let uniform_bytes_1718 :=
        seq_concat (uniform_bytes_1718) (b_i_1717) in 
      (b_i_1717, uniform_bytes_1718))
    (b_i_1717, uniform_bytes_1718) in 
  seq_truncate (uniform_bytes_1718) (len_in_bytes_1710).

Definition fp_hash_to_field
  (msg_1721 : byte_seq)
  (dst_1722 : byte_seq)
  (count_1723 : uint_size)
  : seq fp_t :=
  let len_in_bytes_1724 : uint_size :=
    (count_1723) * (l_v) in 
  let uniform_bytes_1725 : seq uint8 :=
    expand_message_xmd (msg_1721) (dst_1722) (len_in_bytes_1724) in 
  let output_1726 : seq fp_t :=
    seq_new_ (default : fp_t) (count_1723) in 
  let output_1726 :=
    foldi (usize 0) (count_1723) (fun i_1727 output_1726 =>
      let elm_offset_1728 : uint_size :=
        (l_v) * (i_1727) in 
      let tv_1729 : seq uint8 :=
        seq_slice (uniform_bytes_1725) (elm_offset_1728) (l_v) in 
      let u_i_1730 : fp_t :=
        nat_mod_from_byte_seq_be (seq_slice (nat_mod_to_byte_seq_be (
              nat_mod_from_byte_seq_be (tv_1729) : fp_hash_t)) (usize 16) (
            usize 48)) : fp_t in 
      let output_1726 :=
        seq_upd output_1726 (i_1727) (u_i_1730) in 
      (output_1726))
    output_1726 in 
  output_1726.

Definition fp_sgn0 (x_1731 : fp_t) : bool :=
  ((x_1731) rem (nat_mod_two )) =.? (nat_mod_one ).

Definition fp_is_square (x_1732 : fp_t) : bool :=
  let c1_1733 : fp_t :=
    nat_mod_from_byte_seq_be (array_to_be_bytes (p_1_2_v)) : fp_t in 
  let tv_1734 : fp_t :=
    nat_mod_pow_self (x_1732) (c1_1733) in 
  ((tv_1734) =.? (nat_mod_zero )) || ((tv_1734) =.? (nat_mod_one )).

Definition fp_sqrt (x_1735 : fp_t) : fp_t :=
  let c1_1736 : fp_t :=
    nat_mod_from_byte_seq_be (array_to_be_bytes (p_1_4_v)) : fp_t in 
  nat_mod_pow_self (x_1735) (c1_1736).

Definition g1_curve_func (x_1737 : fp_t) : fp_t :=
  (((x_1737) *% (x_1737)) *% (x_1737)) +% (nat_mod_from_literal (_) (
      @repr WORDSIZE128 4) : fp_t).

Definition g1_map_to_curve_svdw (u_1738 : fp_t) : g1_t :=
  let z_1739 : fp_t :=
    (nat_mod_zero ) -% (nat_mod_from_literal (_) (
        @repr WORDSIZE128 3) : fp_t) in 
  let gz_1740 : fp_t :=
    g1_curve_func (z_1739) in 
  let tv1_1741 : fp_t :=
    ((u_1738) *% (u_1738)) *% (gz_1740) in 
  let tv2_1742 : fp_t :=
    (nat_mod_one ) +% (tv1_1741) in 
  let tv1_1743 : fp_t :=
    (nat_mod_one ) -% (tv1_1741) in 
  let tv3_1744 : fp_t :=
    nat_mod_inv ((tv1_1743) *% (tv2_1742)) in 
  let tv4_1745 : fp_t :=
    fp_sqrt (((nat_mod_zero ) -% (gz_1740)) *% (((nat_mod_from_literal (_) (
              @repr WORDSIZE128 3) : fp_t) *% (z_1739)) *% (z_1739))) in 
  let '(tv4_1745) :=
    if fp_sgn0 (tv4_1745):bool then (let tv4_1745 :=
        (nat_mod_zero ) -% (tv4_1745) in 
      (tv4_1745)) else ((tv4_1745)) in 
  let tv5_1746 : fp_t :=
    (((u_1738) *% (tv1_1743)) *% (tv3_1744)) *% (tv4_1745) in 
  let tv6_1747 : fp_t :=
    (((nat_mod_zero ) -% (nat_mod_from_literal (_) (
            @repr WORDSIZE128 4) : fp_t)) *% (gz_1740)) *% (nat_mod_inv (((
            nat_mod_from_literal (_) (@repr WORDSIZE128 3) : fp_t) *% (
            z_1739)) *% (z_1739))) in 
  let x1_1748 : fp_t :=
    (((nat_mod_zero ) -% (z_1739)) *% (nat_mod_inv (nat_mod_two ))) -% (
      tv5_1746) in 
  let x2_1749 : fp_t :=
    (((nat_mod_zero ) -% (z_1739)) *% (nat_mod_inv (nat_mod_two ))) +% (
      tv5_1746) in 
  let x3_1750 : fp_t :=
    (z_1739) +% (((tv6_1747) *% (((tv2_1742) *% (tv2_1742)) *% (tv3_1744))) *% (
        ((tv2_1742) *% (tv2_1742)) *% (tv3_1744))) in 
  let x_1751 : fp_t :=
    (if (fp_is_square (g1_curve_func (x1_1748))):bool then (x1_1748) else ((if (
            fp_is_square (g1_curve_func (x2_1749))):bool then (x2_1749) else (
            x3_1750)))) in 
  let y_1752 : fp_t :=
    fp_sqrt (g1_curve_func (x_1751)) in 
  let '(y_1752) :=
    if (fp_sgn0 (u_1738)) !=.? (fp_sgn0 (y_1752)):bool then (let y_1752 :=
        (nat_mod_zero ) -% (y_1752) in 
      (y_1752)) else ((y_1752)) in 
  (x_1751, y_1752, false).

Definition g1_clear_cofactor (x_1753 : g1_t) : g1_t :=
  let h_eff_1754 : scalar_t :=
    nat_mod_from_literal (_) (
      @repr WORDSIZE128 15132376222941642753) : scalar_t in 
  g1mul (h_eff_1754) (x_1753).

Definition g1_hash_to_curve_svdw
  (msg_1755 : byte_seq)
  (dst_1756 : byte_seq)
  : g1_t :=
  let u_1757 : seq fp_t :=
    fp_hash_to_field (msg_1755) (dst_1756) (usize 2) in 
  let q0_1758 : (fp_t × fp_t × bool) :=
    g1_map_to_curve_svdw (seq_index (u_1757) (usize 0)) in 
  let q1_1759 : (fp_t × fp_t × bool) :=
    g1_map_to_curve_svdw (seq_index (u_1757) (usize 1)) in 
  let r_1760 : (fp_t × fp_t × bool) :=
    g1add (q0_1758) (q1_1759) in 
  let p_1761 : (fp_t × fp_t × bool) :=
    g1_clear_cofactor (r_1760) in 
  p_1761.

Definition g1_encode_to_curve_svdw
  (msg_1762 : byte_seq)
  (dst_1763 : byte_seq)
  : g1_t :=
  let u_1764 : seq fp_t :=
    fp_hash_to_field (msg_1762) (dst_1763) (usize 1) in 
  let q_1765 : (fp_t × fp_t × bool) :=
    g1_map_to_curve_svdw (seq_index (u_1764) (usize 0)) in 
  let p_1766 : (fp_t × fp_t × bool) :=
    g1_clear_cofactor (q_1765) in 
  p_1766.

Definition fp2_hash_to_field
  (msg_1767 : byte_seq)
  (dst_1768 : byte_seq)
  (count_1769 : uint_size)
  : seq fp2_t :=
  let len_in_bytes_1770 : uint_size :=
    ((count_1769) * (usize 2)) * (l_v) in 
  let uniform_bytes_1771 : seq uint8 :=
    expand_message_xmd (msg_1767) (dst_1768) (len_in_bytes_1770) in 
  let output_1772 : seq (fp_t × fp_t) :=
    seq_new_ (default : fp2_t) (count_1769) in 
  let output_1772 :=
    foldi (usize 0) (count_1769) (fun i_1773 output_1772 =>
      let elm_offset_1774 : uint_size :=
        ((l_v) * (i_1773)) * (usize 2) in 
      let tv_1775 : seq uint8 :=
        seq_slice (uniform_bytes_1771) (elm_offset_1774) (l_v) in 
      let e_1_1776 : fp_t :=
        nat_mod_from_byte_seq_be (seq_slice (nat_mod_to_byte_seq_be (
              nat_mod_from_byte_seq_be (tv_1775) : fp_hash_t)) (usize 16) (
            usize 48)) : fp_t in 
      let elm_offset_1777 : uint_size :=
        (l_v) * ((usize 1) + ((i_1773) * (usize 2))) in 
      let tv_1778 : seq uint8 :=
        seq_slice (uniform_bytes_1771) (elm_offset_1777) (l_v) in 
      let e_2_1779 : fp_t :=
        nat_mod_from_byte_seq_be (seq_slice (nat_mod_to_byte_seq_be (
              nat_mod_from_byte_seq_be (tv_1778) : fp_hash_t)) (usize 16) (
            usize 48)) : fp_t in 
      let output_1772 :=
        seq_upd output_1772 (i_1773) ((e_1_1776, e_2_1779)) in 
      (output_1772))
    output_1772 in 
  output_1772.

Definition fp2_sgn0 (x_1780 : fp2_t) : bool :=
  let '(x0_1781, x1_1782) :=
    x_1780 in 
  let sign_0_1783 : bool :=
    fp_sgn0 (x0_1781) in 
  let zero_0_1784 : bool :=
    (x0_1781) =.? (nat_mod_zero ) in 
  let sign_1_1785 : bool :=
    fp_sgn0 (x1_1782) in 
  (sign_0_1783) || ((zero_0_1784) && (sign_1_1785)).

Definition fp2_is_square (x_1786 : fp2_t) : bool :=
  let c1_1787 : fp_t :=
    nat_mod_from_byte_seq_be (array_to_be_bytes (p_1_2_v)) : fp_t in 
  let '(x1_1788, x2_1789) :=
    x_1786 in 
  let tv1_1790 : fp_t :=
    (x1_1788) *% (x1_1788) in 
  let tv2_1791 : fp_t :=
    (x2_1789) *% (x2_1789) in 
  let tv1_1792 : fp_t :=
    (tv1_1790) +% (tv2_1791) in 
  let tv1_1793 : fp_t :=
    nat_mod_pow_self (tv1_1792) (c1_1787) in 
  let neg1_1794 : fp_t :=
    (nat_mod_zero ) -% (nat_mod_one ) in 
  (tv1_1793) !=.? (neg1_1794).

Definition fp2exp (n_1795 : fp2_t) (k_1796 : fp_t) : fp2_t :=
  let c_1797 : (fp_t × fp_t) :=
    fp2fromfp (nat_mod_one ) in 
  let c_1797 :=
    foldi (usize 0) (usize 381) (fun i_1798 c_1797 =>
      let c_1797 :=
        fp2mul (c_1797) (c_1797) in 
      let '(c_1797) :=
        if nat_mod_bit (k_1796) ((usize 380) - (i_1798)):bool then (
          let c_1797 :=
            fp2mul (c_1797) (n_1795) in 
          (c_1797)) else ((c_1797)) in 
      (c_1797))
    c_1797 in 
  c_1797.

Definition fp2_sqrt (a_1799 : fp2_t) : fp2_t :=
  let c1_1800 : fp_t :=
    nat_mod_from_byte_seq_be (array_to_be_bytes (p_3_4_v)) : fp_t in 
  let c2_1801 : fp_t :=
    nat_mod_from_byte_seq_be (array_to_be_bytes (p_1_2_v)) : fp_t in 
  let a1_1802 : (fp_t × fp_t) :=
    fp2exp (a_1799) (c1_1800) in 
  let alpha_1803 : (fp_t × fp_t) :=
    fp2mul (a1_1802) (fp2mul (a1_1802) (a_1799)) in 
  let x0_1804 : (fp_t × fp_t) :=
    fp2mul (a1_1802) (a_1799) in 
  let neg1_1805 : (fp_t × fp_t) :=
    ((nat_mod_zero ) -% (nat_mod_one ), nat_mod_zero ) in 
  let b_1806 : (fp_t × fp_t) :=
    fp2exp (fp2add (fp2fromfp (nat_mod_one )) (alpha_1803)) (c2_1801) in 
  (if ((alpha_1803) =.? (neg1_1805)):bool then (fp2mul ((
          nat_mod_zero ,
          nat_mod_one 
        )) (x0_1804)) else (fp2mul (b_1806) (x0_1804))).

Definition g2_curve_func (x_1807 : fp2_t) : fp2_t :=
  fp2add (fp2mul (x_1807) (fp2mul (x_1807) (x_1807))) ((
      nat_mod_from_literal (_) (@repr WORDSIZE128 4) : fp_t,
      nat_mod_from_literal (_) (@repr WORDSIZE128 4) : fp_t
    )).

Definition g2_map_to_curve_svdw (u_1808 : fp2_t) : g2_t :=
  let z_1809 : (fp_t × fp_t) :=
    fp2neg (fp2fromfp (nat_mod_one )) in 
  let gz_1810 : (fp_t × fp_t) :=
    g2_curve_func (z_1809) in 
  let tv1_1811 : (fp_t × fp_t) :=
    fp2mul (fp2mul (u_1808) (u_1808)) (gz_1810) in 
  let tv2_1812 : (fp_t × fp_t) :=
    fp2add (fp2fromfp (nat_mod_one )) (tv1_1811) in 
  let tv1_1813 : (fp_t × fp_t) :=
    fp2sub (fp2fromfp (nat_mod_one )) (tv1_1811) in 
  let tv3_1814 : (fp_t × fp_t) :=
    fp2inv (fp2mul (tv1_1813) (tv2_1812)) in 
  let tv4_1815 : (fp_t × fp_t) :=
    fp2_sqrt (fp2mul (fp2neg (gz_1810)) (fp2mul (fp2fromfp (
            nat_mod_from_literal (_) (@repr WORDSIZE128 3) : fp_t)) (fp2mul (
            z_1809) (z_1809)))) in 
  let '(tv4_1815) :=
    if fp2_sgn0 (tv4_1815):bool then (let tv4_1815 :=
        fp2neg (tv4_1815) in 
      (tv4_1815)) else ((tv4_1815)) in 
  let tv5_1816 : (fp_t × fp_t) :=
    fp2mul (fp2mul (fp2mul (u_1808) (tv1_1813)) (tv3_1814)) (tv4_1815) in 
  let tv6_1817 : (fp_t × fp_t) :=
    fp2mul (fp2mul (fp2neg (fp2fromfp (nat_mod_from_literal (_) (
              @repr WORDSIZE128 4) : fp_t))) (gz_1810)) (fp2inv (fp2mul (
          fp2fromfp (nat_mod_from_literal (_) (@repr WORDSIZE128 3) : fp_t)) (
          fp2mul (z_1809) (z_1809)))) in 
  let x1_1818 : (fp_t × fp_t) :=
    fp2sub (fp2mul (fp2neg (z_1809)) (fp2inv (fp2fromfp (nat_mod_two )))) (
      tv5_1816) in 
  let x2_1819 : (fp_t × fp_t) :=
    fp2add (fp2mul (fp2neg (z_1809)) (fp2inv (fp2fromfp (nat_mod_two )))) (
      tv5_1816) in 
  let tv7_1820 : (fp_t × fp_t) :=
    fp2mul (fp2mul (tv2_1812) (tv2_1812)) (tv3_1814) in 
  let x3_1821 : (fp_t × fp_t) :=
    fp2add (z_1809) (fp2mul (tv6_1817) (fp2mul (tv7_1820) (tv7_1820))) in 
  let x_1822 : (fp_t × fp_t) :=
    (if (fp2_is_square (g2_curve_func (x1_1818))):bool then (x1_1818) else ((
          if (fp2_is_square (g2_curve_func (x2_1819))):bool then (
            x2_1819) else (x3_1821)))) in 
  let y_1823 : (fp_t × fp_t) :=
    fp2_sqrt (g2_curve_func (x_1822)) in 
  let '(y_1823) :=
    if (fp2_sgn0 (u_1808)) !=.? (fp2_sgn0 (y_1823)):bool then (let y_1823 :=
        fp2neg (y_1823) in 
      (y_1823)) else ((y_1823)) in 
  (x_1822, y_1823, false).

Definition psi (p_1824 : g2_t) : g2_t :=
  let c1_1825 : (fp_t × fp_t) :=
    fp2inv (fp2exp ((nat_mod_one , nat_mod_one )) (((nat_mod_zero ) -% (
            nat_mod_one )) *% (nat_mod_inv (nat_mod_from_literal (_) (
              @repr WORDSIZE128 3) : fp_t)))) in 
  let c2_1826 : (fp_t × fp_t) :=
    fp2inv (fp2exp ((nat_mod_one , nat_mod_one )) (((nat_mod_zero ) -% (
            nat_mod_one )) *% (nat_mod_inv (nat_mod_two )))) in 
  let '(x_1827, y_1828, inf_1829) :=
    p_1824 in 
  let qx_1830 : (fp_t × fp_t) :=
    fp2mul (c1_1825) (fp2conjugate (x_1827)) in 
  let qy_1831 : (fp_t × fp_t) :=
    fp2mul (c2_1826) (fp2conjugate (y_1828)) in 
  (qx_1830, qy_1831, inf_1829).

Definition g2_clear_cofactor (p_1832 : g2_t) : g2_t :=
  let c1_1833 : scalar_t :=
    nat_mod_from_literal (_) (
      @repr WORDSIZE128 15132376222941642752) : scalar_t in 
  let t1_1834 : ((fp_t × fp_t) × (fp_t × fp_t) × bool) :=
    g2mul (c1_1833) (p_1832) in 
  let t1_1835 : ((fp_t × fp_t) × (fp_t × fp_t) × bool) :=
    g2neg (t1_1834) in 
  let t2_1836 : ((fp_t × fp_t) × (fp_t × fp_t) × bool) :=
    psi (p_1832) in 
  let t3_1837 : ((fp_t × fp_t) × (fp_t × fp_t) × bool) :=
    g2double (p_1832) in 
  let t3_1838 : ((fp_t × fp_t) × (fp_t × fp_t) × bool) :=
    psi (psi (t3_1837)) in 
  let t3_1839 : ((fp_t × fp_t) × (fp_t × fp_t) × bool) :=
    g2add (t3_1838) (g2neg (t2_1836)) in 
  let t2_1840 : ((fp_t × fp_t) × (fp_t × fp_t) × bool) :=
    g2add (t1_1835) (t2_1836) in 
  let t2_1841 : ((fp_t × fp_t) × (fp_t × fp_t) × bool) :=
    g2mul (c1_1833) (t2_1840) in 
  let t2_1842 : ((fp_t × fp_t) × (fp_t × fp_t) × bool) :=
    g2neg (t2_1841) in 
  let t3_1843 : ((fp_t × fp_t) × (fp_t × fp_t) × bool) :=
    g2add (t3_1839) (t2_1842) in 
  let t3_1844 : ((fp_t × fp_t) × (fp_t × fp_t) × bool) :=
    g2add (t3_1843) (g2neg (t1_1835)) in 
  let q_1845 : ((fp_t × fp_t) × (fp_t × fp_t) × bool) :=
    g2add (t3_1844) (g2neg (p_1832)) in 
  q_1845.

Definition g2_hash_to_curve_svdw
  (msg_1846 : byte_seq)
  (dst_1847 : byte_seq)
  : g2_t :=
  let u_1848 : seq fp2_t :=
    fp2_hash_to_field (msg_1846) (dst_1847) (usize 2) in 
  let q0_1849 : ((fp_t × fp_t) × (fp_t × fp_t) × bool) :=
    g2_map_to_curve_svdw (seq_index (u_1848) (usize 0)) in 
  let q1_1850 : ((fp_t × fp_t) × (fp_t × fp_t) × bool) :=
    g2_map_to_curve_svdw (seq_index (u_1848) (usize 1)) in 
  let r_1851 : ((fp_t × fp_t) × (fp_t × fp_t) × bool) :=
    g2add (q0_1849) (q1_1850) in 
  let p_1852 : ((fp_t × fp_t) × (fp_t × fp_t) × bool) :=
    g2_clear_cofactor (r_1851) in 
  p_1852.

Definition g2_encode_to_curve_svdw
  (msg_1853 : byte_seq)
  (dst_1854 : byte_seq)
  : g2_t :=
  let u_1855 : seq fp2_t :=
    fp2_hash_to_field (msg_1853) (dst_1854) (usize 1) in 
  let q_1856 : ((fp_t × fp_t) × (fp_t × fp_t) × bool) :=
    g2_map_to_curve_svdw (seq_index (u_1855) (usize 0)) in 
  let p_1857 : ((fp_t × fp_t) × (fp_t × fp_t) × bool) :=
    g2_clear_cofactor (q_1856) in 
  p_1857.

Definition g1_iso_a_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 5707120929990979) : int64;
        secret (@repr WORDSIZE64 4425131892511951234) : int64;
        secret (@repr WORDSIZE64 12748169179688756904) : int64;
        secret (@repr WORDSIZE64 15629909748249821612) : int64;
        secret (@repr WORDSIZE64 10994253769421683071) : int64;
        secret (@repr WORDSIZE64 6698022561392380957) : int64
      ] in  l).

Definition g1_iso_b_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1360808972976160816) : int64;
        secret (@repr WORDSIZE64 111203405409480251) : int64;
        secret (@repr WORDSIZE64 2312248699302920304) : int64;
        secret (@repr WORDSIZE64 11581500465278574325) : int64;
        secret (@repr WORDSIZE64 6495071758858381989) : int64;
        secret (@repr WORDSIZE64 15117538217124375520) : int64
      ] in  l).

Definition g1_xnum_k_0_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1270119733718627136) : int64;
        secret (@repr WORDSIZE64 13261148298159854981) : int64;
        secret (@repr WORDSIZE64 7723742117508874335) : int64;
        secret (@repr WORDSIZE64 17465657917644792520) : int64;
        secret (@repr WORDSIZE64 6201670911048166766) : int64;
        secret (@repr WORDSIZE64 12586459670690286007) : int64
      ] in  l).

Definition g1_xnum_k_1_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1668951808976071471) : int64;
        secret (@repr WORDSIZE64 398773841247578140) : int64;
        secret (@repr WORDSIZE64 8941869963990959127) : int64;
        secret (@repr WORDSIZE64 17682789360670468203) : int64;
        secret (@repr WORDSIZE64 5204176168283587414) : int64;
        secret (@repr WORDSIZE64 16732261237459223483) : int64
      ] in  l).

Definition g1_xnum_k_2_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 960393023080265964) : int64;
        secret (@repr WORDSIZE64 2094253841180170779) : int64;
        secret (@repr WORDSIZE64 14844748873776858085) : int64;
        secret (@repr WORDSIZE64 7528018573573808732) : int64;
        secret (@repr WORDSIZE64 10776056440809943711) : int64;
        secret (@repr WORDSIZE64 16147550488514976944) : int64
      ] in  l).

Definition g1_xnum_k_3_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1691355743628586423) : int64;
        secret (@repr WORDSIZE64 5622191986793862162) : int64;
        secret (@repr WORDSIZE64 15561595211679121189) : int64;
        secret (@repr WORDSIZE64 17416319752018800771) : int64;
        secret (@repr WORDSIZE64 5996228842464768403) : int64;
        secret (@repr WORDSIZE64 14245880009877842017) : int64
      ] in  l).

Definition g1_xnum_k_4_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1051997788391994435) : int64;
        secret (@repr WORDSIZE64 7368650625050054228) : int64;
        secret (@repr WORDSIZE64 11086623519836470079) : int64;
        secret (@repr WORDSIZE64 607681821319080984) : int64;
        secret (@repr WORDSIZE64 10978131499682789316) : int64;
        secret (@repr WORDSIZE64 5842660658088809945) : int64
      ] in  l).

Definition g1_xnum_k_5_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1598992431623377919) : int64;
        secret (@repr WORDSIZE64 130921168661596853) : int64;
        secret (@repr WORDSIZE64 15797696746983946651) : int64;
        secret (@repr WORDSIZE64 11444679715590672272) : int64;
        secret (@repr WORDSIZE64 11567228658253249817) : int64;
        secret (@repr WORDSIZE64 14777367860349315459) : int64
      ] in  l).

Definition g1_xnum_k_6_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 967946631563726121) : int64;
        secret (@repr WORDSIZE64 7653628713030275775) : int64;
        secret (@repr WORDSIZE64 12760252618317466849) : int64;
        secret (@repr WORDSIZE64 10378793938173061930) : int64;
        secret (@repr WORDSIZE64 10205808941053849290) : int64;
        secret (@repr WORDSIZE64 15985511645807504772) : int64
      ] in  l).

Definition g1_xnum_k_7_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1709149555065084898) : int64;
        secret (@repr WORDSIZE64 16750075057192140371) : int64;
        secret (@repr WORDSIZE64 3849985779734105521) : int64;
        secret (@repr WORDSIZE64 11998370262181639475) : int64;
        secret (@repr WORDSIZE64 4159013751748851119) : int64;
        secret (@repr WORDSIZE64 11298218755092433038) : int64
      ] in  l).

Definition g1_xnum_k_8_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 580186936973955012) : int64;
        secret (@repr WORDSIZE64 8903813505199544589) : int64;
        secret (@repr WORDSIZE64 14140024565662700916) : int64;
        secret (@repr WORDSIZE64 11728946595272970718) : int64;
        secret (@repr WORDSIZE64 5738313744366653077) : int64;
        secret (@repr WORDSIZE64 7886252005760951063) : int64
      ] in  l).

Definition g1_xnum_k_9_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1628930385436977092) : int64;
        secret (@repr WORDSIZE64 3318087848058654498) : int64;
        secret (@repr WORDSIZE64 15937899882900905113) : int64;
        secret (@repr WORDSIZE64 7449821001803307903) : int64;
        secret (@repr WORDSIZE64 11752436998487615353) : int64;
        secret (@repr WORDSIZE64 9161465579737517214) : int64
      ] in  l).

Definition g1_xnum_k_10_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1167027828517898210) : int64;
        secret (@repr WORDSIZE64 8275623842221021965) : int64;
        secret (@repr WORDSIZE64 18049808134997311382) : int64;
        secret (@repr WORDSIZE64 15351349873550116966) : int64;
        secret (@repr WORDSIZE64 17769927732099571180) : int64;
        secret (@repr WORDSIZE64 14584871380308065147) : int64
      ] in  l).

Definition g1_xnum_k_11_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 495550047642324592) : int64;
        secret (@repr WORDSIZE64 13627494601717575229) : int64;
        secret (@repr WORDSIZE64 3591512392926246844) : int64;
        secret (@repr WORDSIZE64 2576269112800734056) : int64;
        secret (@repr WORDSIZE64 14000314106239596831) : int64;
        secret (@repr WORDSIZE64 12234233096825917993) : int64
      ] in  l).

Definition g1_xden_k_0_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 633474091881273774) : int64;
        secret (@repr WORDSIZE64 1779737893574802031) : int64;
        secret (@repr WORDSIZE64 132274872219551930) : int64;
        secret (@repr WORDSIZE64 11283074393783708770) : int64;
        secret (@repr WORDSIZE64 13067430171545714168) : int64;
        secret (@repr WORDSIZE64 11041975239630265116) : int64
      ] in  l).

Definition g1_xden_k_1_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1321272531362356291) : int64;
        secret (@repr WORDSIZE64 5238936591227237942) : int64;
        secret (@repr WORDSIZE64 8089002360232247308) : int64;
        secret (@repr WORDSIZE64 82967328719421271) : int64;
        secret (@repr WORDSIZE64 1430641118356186857) : int64;
        secret (@repr WORDSIZE64 16557527386785790975) : int64
      ] in  l).

Definition g1_xden_k_2_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 804282852993868382) : int64;
        secret (@repr WORDSIZE64 9311163821600184607) : int64;
        secret (@repr WORDSIZE64 8037026956533927121) : int64;
        secret (@repr WORDSIZE64 18205324308570099372) : int64;
        secret (@repr WORDSIZE64 15466434890074226396) : int64;
        secret (@repr WORDSIZE64 18213183315621985817) : int64
      ] in  l).

Definition g1_xden_k_3_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 234844145893171966) : int64;
        secret (@repr WORDSIZE64 14428037799351479124) : int64;
        secret (@repr WORDSIZE64 6559532710647391569) : int64;
        secret (@repr WORDSIZE64 6110444250091843536) : int64;
        secret (@repr WORDSIZE64 5293652763671852484) : int64;
        secret (@repr WORDSIZE64 1373009181854280920) : int64
      ] in  l).

Definition g1_xden_k_4_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1416629893867312296) : int64;
        secret (@repr WORDSIZE64 751851957792514173) : int64;
        secret (@repr WORDSIZE64 18437674587247370939) : int64;
        secret (@repr WORDSIZE64 10190314345946351322) : int64;
        secret (@repr WORDSIZE64 11228207967368476701) : int64;
        secret (@repr WORDSIZE64 6025034940388909598) : int64
      ] in  l).

Definition g1_xden_k_5_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1041270466333271993) : int64;
        secret (@repr WORDSIZE64 6140956605115975401) : int64;
        secret (@repr WORDSIZE64 4131830461445745997) : int64;
        secret (@repr WORDSIZE64 739642499118176303) : int64;
        secret (@repr WORDSIZE64 8358912131254619921) : int64;
        secret (@repr WORDSIZE64 13847998906088228005) : int64
      ] in  l).

Definition g1_xden_k_6_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 536714149743900185) : int64;
        secret (@repr WORDSIZE64 1098328982230230817) : int64;
        secret (@repr WORDSIZE64 6273329123533496713) : int64;
        secret (@repr WORDSIZE64 5633448088282521244) : int64;
        secret (@repr WORDSIZE64 16894043798660571244) : int64;
        secret (@repr WORDSIZE64 17016134625831438906) : int64
      ] in  l).

Definition g1_xden_k_7_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1488347500898461874) : int64;
        secret (@repr WORDSIZE64 3509418672874520985) : int64;
        secret (@repr WORDSIZE64 7962192351555381416) : int64;
        secret (@repr WORDSIZE64 1843909372225399896) : int64;
        secret (@repr WORDSIZE64 1127511003250156243) : int64;
        secret (@repr WORDSIZE64 1294742680819751518) : int64
      ] in  l).

Definition g1_xden_k_8_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 725340084226051970) : int64;
        secret (@repr WORDSIZE64 6814521545734988748) : int64;
        secret (@repr WORDSIZE64 16176803544133875307) : int64;
        secret (@repr WORDSIZE64 8363199516777220149) : int64;
        secret (@repr WORDSIZE64 252877309218538352) : int64;
        secret (@repr WORDSIZE64 5149562959837648449) : int64
      ] in  l).

Definition g1_xden_k_9_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 675470927100193492) : int64;
        secret (@repr WORDSIZE64 5146891164735334016) : int64;
        secret (@repr WORDSIZE64 17762958817130696759) : int64;
        secret (@repr WORDSIZE64 8565656522589412373) : int64;
        secret (@repr WORDSIZE64 10599026333335446784) : int64;
        secret (@repr WORDSIZE64 3270603789344496906) : int64
      ] in  l).

Definition g1_ynum_k_0_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 652344406751465184) : int64;
        secret (@repr WORDSIZE64 2710356675495255290) : int64;
        secret (@repr WORDSIZE64 1273695771440998738) : int64;
        secret (@repr WORDSIZE64 3121750372618945491) : int64;
        secret (@repr WORDSIZE64 14775319642720936898) : int64;
        secret (@repr WORDSIZE64 13733803417833814835) : int64
      ] in  l).

Definition g1_ynum_k_1_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1389807578337138705) : int64;
        secret (@repr WORDSIZE64 15352831428748068483) : int64;
        secret (@repr WORDSIZE64 1307144967559264317) : int64;
        secret (@repr WORDSIZE64 1121505450578652468) : int64;
        secret (@repr WORDSIZE64 15475889019760388287) : int64;
        secret (@repr WORDSIZE64 16183658160488302230) : int64
      ] in  l).

Definition g1_ynum_k_2_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 57553299067792998) : int64;
        secret (@repr WORDSIZE64 17628079362768849300) : int64;
        secret (@repr WORDSIZE64 2689461337731570914) : int64;
        secret (@repr WORDSIZE64 14070580367580990887) : int64;
        secret (@repr WORDSIZE64 15162865775551710499) : int64;
        secret (@repr WORDSIZE64 13321614990632673782) : int64
      ] in  l).

Definition g1_ynum_k_3_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 141972750621744161) : int64;
        secret (@repr WORDSIZE64 8689824239172478807) : int64;
        secret (@repr WORDSIZE64 15288216298323671324) : int64;
        secret (@repr WORDSIZE64 712874875091754233) : int64;
        secret (@repr WORDSIZE64 16014900032503684588) : int64;
        secret (@repr WORDSIZE64 11976580453200426187) : int64
      ] in  l).

Definition g1_ynum_k_4_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 633886036738506515) : int64;
        secret (@repr WORDSIZE64 6678644607214234052) : int64;
        secret (@repr WORDSIZE64 1825425679455244472) : int64;
        secret (@repr WORDSIZE64 8755912272271186652) : int64;
        secret (@repr WORDSIZE64 3379943669301788840) : int64;
        secret (@repr WORDSIZE64 4735212769449148123) : int64
      ] in  l).

Definition g1_ynum_k_5_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1612358804494830442) : int64;
        secret (@repr WORDSIZE64 2454990789666711200) : int64;
        secret (@repr WORDSIZE64 8405916841409361853) : int64;
        secret (@repr WORDSIZE64 8525415512662168654) : int64;
        secret (@repr WORDSIZE64 2323684950984523890) : int64;
        secret (@repr WORDSIZE64 11074978966450447856) : int64
      ] in  l).

Definition g1_ynum_k_6_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 336375361001233340) : int64;
        secret (@repr WORDSIZE64 12882959944969186108) : int64;
        secret (@repr WORDSIZE64 16671121624101127371) : int64;
        secret (@repr WORDSIZE64 5922586712221110071) : int64;
        secret (@repr WORDSIZE64 5163511947597922654) : int64;
        secret (@repr WORDSIZE64 14511152726087948018) : int64
      ] in  l).

Definition g1_ynum_k_7_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 686738286210365551) : int64;
        secret (@repr WORDSIZE64 16039894141796533876) : int64;
        secret (@repr WORDSIZE64 1660145734357211167) : int64;
        secret (@repr WORDSIZE64 18231571463891878950) : int64;
        secret (@repr WORDSIZE64 4825120264949852469) : int64;
        secret (@repr WORDSIZE64 11627815551290637097) : int64
      ] in  l).

Definition g1_ynum_k_8_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 719520515476580427) : int64;
        secret (@repr WORDSIZE64 16756942182913253819) : int64;
        secret (@repr WORDSIZE64 10320769399998235244) : int64;
        secret (@repr WORDSIZE64 2200974244968450750) : int64;
        secret (@repr WORDSIZE64 7626373186594408355) : int64;
        secret (@repr WORDSIZE64 6933025920263103879) : int64
      ] in  l).

Definition g1_ynum_k_9_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1016611174344998325) : int64;
        secret (@repr WORDSIZE64 2466492548686891555) : int64;
        secret (@repr WORDSIZE64 14135124294293452542) : int64;
        secret (@repr WORDSIZE64 475233659467912251) : int64;
        secret (@repr WORDSIZE64 11186783513499056751) : int64;
        secret (@repr WORDSIZE64 3147922594245844016) : int64
      ] in  l).

Definition g1_ynum_k_10_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1833315000454533566) : int64;
        secret (@repr WORDSIZE64 1007974600900082579) : int64;
        secret (@repr WORDSIZE64 14785260176242854207) : int64;
        secret (@repr WORDSIZE64 15066861003931772432) : int64;
        secret (@repr WORDSIZE64 3584647998681889532) : int64;
        secret (@repr WORDSIZE64 16722834201330696498) : int64
      ] in  l).

Definition g1_ynum_k_11_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1780164921828767454) : int64;
        secret (@repr WORDSIZE64 13337622794239929804) : int64;
        secret (@repr WORDSIZE64 5923739534552515142) : int64;
        secret (@repr WORDSIZE64 3345046972101780530) : int64;
        secret (@repr WORDSIZE64 5321510883028162054) : int64;
        secret (@repr WORDSIZE64 14846055306840460686) : int64
      ] in  l).

Definition g1_ynum_k_12_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 799438051374502809) : int64;
        secret (@repr WORDSIZE64 15083972834952036164) : int64;
        secret (@repr WORDSIZE64 8838227588559581326) : int64;
        secret (@repr WORDSIZE64 13846054168121598783) : int64;
        secret (@repr WORDSIZE64 488730451382505970) : int64;
        secret (@repr WORDSIZE64 958146249756188408) : int64
      ] in  l).

Definition g1_ynum_k_13_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 163716820423854747) : int64;
        secret (@repr WORDSIZE64 8285498163857659356) : int64;
        secret (@repr WORDSIZE64 8465424830341846400) : int64;
        secret (@repr WORDSIZE64 1433942577299613084) : int64;
        secret (@repr WORDSIZE64 14325828012864645732) : int64;
        secret (@repr WORDSIZE64 4817114329354076467) : int64
      ] in  l).

Definition g1_ynum_k_14_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 414658151749832465) : int64;
        secret (@repr WORDSIZE64 189531577938912252) : int64;
        secret (@repr WORDSIZE64 6802473390048830824) : int64;
        secret (@repr WORDSIZE64 15684647020317539556) : int64;
        secret (@repr WORDSIZE64 7755485098777620407) : int64;
        secret (@repr WORDSIZE64 9685868895687483979) : int64
      ] in  l).

Definition g1_ynum_k_15_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1578157964224562126) : int64;
        secret (@repr WORDSIZE64 5666948055268535989) : int64;
        secret (@repr WORDSIZE64 14634479491382401593) : int64;
        secret (@repr WORDSIZE64 6317940024988860850) : int64;
        secret (@repr WORDSIZE64 13142913832013798519) : int64;
        secret (@repr WORDSIZE64 338991247778166276) : int64
      ] in  l).

Definition g1_yden_k_0_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1590100849350973618) : int64;
        secret (@repr WORDSIZE64 5915497081334721257) : int64;
        secret (@repr WORDSIZE64 6924968209373727718) : int64;
        secret (@repr WORDSIZE64 17204633670617869946) : int64;
        secret (@repr WORDSIZE64 572916540828819565) : int64;
        secret (@repr WORDSIZE64 92203205520679873) : int64
      ] in  l).

Definition g1_yden_k_1_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1829261189398470686) : int64;
        secret (@repr WORDSIZE64 1877083417397643448) : int64;
        secret (@repr WORDSIZE64 9640042925497046428) : int64;
        secret (@repr WORDSIZE64 11862766565471805471) : int64;
        secret (@repr WORDSIZE64 8693114993904885301) : int64;
        secret (@repr WORDSIZE64 3672140328108400701) : int64
      ] in  l).

Definition g1_yden_k_2_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 400243331105348135) : int64;
        secret (@repr WORDSIZE64 8046435537999802711) : int64;
        secret (@repr WORDSIZE64 8702226981475745585) : int64;
        secret (@repr WORDSIZE64 879791671491744492) : int64;
        secret (@repr WORDSIZE64 11994630442058346377) : int64;
        secret (@repr WORDSIZE64 2172204746352322546) : int64
      ] in  l).

Definition g1_yden_k_3_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1637008473169220501) : int64;
        secret (@repr WORDSIZE64 17441636237435581649) : int64;
        secret (@repr WORDSIZE64 15066165676546511630) : int64;
        secret (@repr WORDSIZE64 1314387578457599809) : int64;
        secret (@repr WORDSIZE64 8247046336453711789) : int64;
        secret (@repr WORDSIZE64 12164906044230685718) : int64
      ] in  l).

Definition g1_yden_k_4_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 855930740911588324) : int64;
        secret (@repr WORDSIZE64 12685735333705453020) : int64;
        secret (@repr WORDSIZE64 14326404096614579120) : int64;
        secret (@repr WORDSIZE64 6066025509460822294) : int64;
        secret (@repr WORDSIZE64 11676450493790612973) : int64;
        secret (@repr WORDSIZE64 15724621714793234461) : int64
      ] in  l).

Definition g1_yden_k_5_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 637792788410719021) : int64;
        secret (@repr WORDSIZE64 11507373155986977154) : int64;
        secret (@repr WORDSIZE64 13186912195705886849) : int64;
        secret (@repr WORDSIZE64 14262012144631372388) : int64;
        secret (@repr WORDSIZE64 5328758613570342114) : int64;
        secret (@repr WORDSIZE64 199925847119476652) : int64
      ] in  l).

Definition g1_yden_k_6_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1612297190139091759) : int64;
        secret (@repr WORDSIZE64 14103733843373163083) : int64;
        secret (@repr WORDSIZE64 6840121186619029743) : int64;
        secret (@repr WORDSIZE64 6760859324815900753) : int64;
        secret (@repr WORDSIZE64 15418807805142572985) : int64;
        secret (@repr WORDSIZE64 4402853133867972444) : int64
      ] in  l).

Definition g1_yden_k_7_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1631410310868805610) : int64;
        secret (@repr WORDSIZE64 269334146695233390) : int64;
        secret (@repr WORDSIZE64 16547411811928854487) : int64;
        secret (@repr WORDSIZE64 18353100669930795314) : int64;
        secret (@repr WORDSIZE64 13339932232668798692) : int64;
        secret (@repr WORDSIZE64 6984591927261867737) : int64
      ] in  l).

Definition g1_yden_k_8_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1758313625630302499) : int64;
        secret (@repr WORDSIZE64 1881349400343039172) : int64;
        secret (@repr WORDSIZE64 18013005311323887904) : int64;
        secret (@repr WORDSIZE64 12377427846571989832) : int64;
        secret (@repr WORDSIZE64 5967237584920922243) : int64;
        secret (@repr WORDSIZE64 7720081932193848650) : int64
      ] in  l).

Definition g1_yden_k_9_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1619701357752249884) : int64;
        secret (@repr WORDSIZE64 16898074901591262352) : int64;
        secret (@repr WORDSIZE64 3609344159736760251) : int64;
        secret (@repr WORDSIZE64 5983130161189999867) : int64;
        secret (@repr WORDSIZE64 14355327869992416094) : int64;
        secret (@repr WORDSIZE64 3778226018344582997) : int64
      ] in  l).

Definition g1_yden_k_10_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 347606589330687421) : int64;
        secret (@repr WORDSIZE64 5255719044972187933) : int64;
        secret (@repr WORDSIZE64 11271894388753671721) : int64;
        secret (@repr WORDSIZE64 1033887512062764488) : int64;
        secret (@repr WORDSIZE64 8189165486932690436) : int64;
        secret (@repr WORDSIZE64 70004379462101672) : int64
      ] in  l).

Definition g1_yden_k_11_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 778202887894139711) : int64;
        secret (@repr WORDSIZE64 17691595219776375879) : int64;
        secret (@repr WORDSIZE64 9193253711563866834) : int64;
        secret (@repr WORDSIZE64 10092455202333888821) : int64;
        secret (@repr WORDSIZE64 1655469341950262250) : int64;
        secret (@repr WORDSIZE64 10845992994110574738) : int64
      ] in  l).

Definition g1_yden_k_12_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 781015344221683683) : int64;
        secret (@repr WORDSIZE64 14078588081290548374) : int64;
        secret (@repr WORDSIZE64 6067271023149908518) : int64;
        secret (@repr WORDSIZE64 9033357708497886086) : int64;
        secret (@repr WORDSIZE64 10592474449179118273) : int64;
        secret (@repr WORDSIZE64 2204988348113831372) : int64
      ] in  l).

Definition g1_yden_k_13_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 172830037692534587) : int64;
        secret (@repr WORDSIZE64 7101012286790006514) : int64;
        secret (@repr WORDSIZE64 13787308004332873665) : int64;
        secret (@repr WORDSIZE64 14660498759553796110) : int64;
        secret (@repr WORDSIZE64 4757234684169342080) : int64;
        secret (@repr WORDSIZE64 15130647872920159991) : int64
      ] in  l).

Definition g1_yden_k_14_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1013206390650290238) : int64;
        secret (@repr WORDSIZE64 7720336747103001025) : int64;
        secret (@repr WORDSIZE64 8197694151986493523) : int64;
        secret (@repr WORDSIZE64 3625112747029342752) : int64;
        secret (@repr WORDSIZE64 6675167463148394368) : int64;
        secret (@repr WORDSIZE64 4905905684016745359) : int64
      ] in  l).

Definition g1_simple_swu_iso (u_1858 : fp_t) : (fp_t × fp_t) :=
  let z_1859 : fp_t :=
    nat_mod_from_literal (_) (@repr WORDSIZE128 11) : fp_t in 
  let a_1860 : fp_t :=
    nat_mod_from_byte_seq_be (array_to_be_bytes (g1_iso_a_v)) : fp_t in 
  let b_1861 : fp_t :=
    nat_mod_from_byte_seq_be (array_to_be_bytes (g1_iso_b_v)) : fp_t in 
  let tv1_1862 : fp_t :=
    nat_mod_inv ((((z_1859) *% (z_1859)) *% (nat_mod_exp (u_1858) (
            @repr WORDSIZE32 4))) +% (((z_1859) *% (u_1858)) *% (u_1858))) in 
  let x1_1863 : fp_t :=
    (((nat_mod_zero ) -% (b_1861)) *% (nat_mod_inv (a_1860))) *% ((
        nat_mod_one ) +% (tv1_1862)) in 
  let '(x1_1863) :=
    if (tv1_1862) =.? (nat_mod_zero ):bool then (let x1_1863 :=
        (b_1861) *% (nat_mod_inv ((z_1859) *% (a_1860))) in 
      (x1_1863)) else ((x1_1863)) in 
  let gx1_1864 : fp_t :=
    ((nat_mod_exp (x1_1863) (@repr WORDSIZE32 3)) +% ((a_1860) *% (
          x1_1863))) +% (b_1861) in 
  let x2_1865 : fp_t :=
    (((z_1859) *% (u_1858)) *% (u_1858)) *% (x1_1863) in 
  let gx2_1866 : fp_t :=
    ((nat_mod_exp (x2_1865) (@repr WORDSIZE32 3)) +% ((a_1860) *% (
          x2_1865))) +% (b_1861) in 
  let '(x_1867, y_1868) :=
    (if (fp_is_square (gx1_1864)):bool then ((x1_1863, fp_sqrt (gx1_1864)
        )) else ((x2_1865, fp_sqrt (gx2_1866)))) in 
  let '(y_1868) :=
    if (fp_sgn0 (u_1858)) !=.? (fp_sgn0 (y_1868)):bool then (let y_1868 :=
        (nat_mod_zero ) -% (y_1868) in 
      (y_1868)) else ((y_1868)) in 
  (x_1867, y_1868).

Definition g1_isogeny_map (x_1869 : fp_t) (y_1870 : fp_t) : g1_t :=
  let xnum_k_1871 : seq fp_t :=
    seq_new_ (default : fp_t) (usize 12) in 
  let xnum_k_1871 :=
    seq_upd xnum_k_1871 (usize 0) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_xnum_k_0_v)) : fp_t) in 
  let xnum_k_1871 :=
    seq_upd xnum_k_1871 (usize 1) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_xnum_k_1_v)) : fp_t) in 
  let xnum_k_1871 :=
    seq_upd xnum_k_1871 (usize 2) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_xnum_k_2_v)) : fp_t) in 
  let xnum_k_1871 :=
    seq_upd xnum_k_1871 (usize 3) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_xnum_k_3_v)) : fp_t) in 
  let xnum_k_1871 :=
    seq_upd xnum_k_1871 (usize 4) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_xnum_k_4_v)) : fp_t) in 
  let xnum_k_1871 :=
    seq_upd xnum_k_1871 (usize 5) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_xnum_k_5_v)) : fp_t) in 
  let xnum_k_1871 :=
    seq_upd xnum_k_1871 (usize 6) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_xnum_k_6_v)) : fp_t) in 
  let xnum_k_1871 :=
    seq_upd xnum_k_1871 (usize 7) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_xnum_k_7_v)) : fp_t) in 
  let xnum_k_1871 :=
    seq_upd xnum_k_1871 (usize 8) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_xnum_k_8_v)) : fp_t) in 
  let xnum_k_1871 :=
    seq_upd xnum_k_1871 (usize 9) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_xnum_k_9_v)) : fp_t) in 
  let xnum_k_1871 :=
    seq_upd xnum_k_1871 (usize 10) (nat_mod_from_byte_seq_be (
        array_to_be_bytes (g1_xnum_k_10_v)) : fp_t) in 
  let xnum_k_1871 :=
    seq_upd xnum_k_1871 (usize 11) (nat_mod_from_byte_seq_be (
        array_to_be_bytes (g1_xnum_k_11_v)) : fp_t) in 
  let xden_k_1872 : seq fp_t :=
    seq_new_ (default : fp_t) (usize 10) in 
  let xden_k_1872 :=
    seq_upd xden_k_1872 (usize 0) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_xden_k_0_v)) : fp_t) in 
  let xden_k_1872 :=
    seq_upd xden_k_1872 (usize 1) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_xden_k_1_v)) : fp_t) in 
  let xden_k_1872 :=
    seq_upd xden_k_1872 (usize 2) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_xden_k_2_v)) : fp_t) in 
  let xden_k_1872 :=
    seq_upd xden_k_1872 (usize 3) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_xden_k_3_v)) : fp_t) in 
  let xden_k_1872 :=
    seq_upd xden_k_1872 (usize 4) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_xden_k_4_v)) : fp_t) in 
  let xden_k_1872 :=
    seq_upd xden_k_1872 (usize 5) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_xden_k_5_v)) : fp_t) in 
  let xden_k_1872 :=
    seq_upd xden_k_1872 (usize 6) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_xden_k_6_v)) : fp_t) in 
  let xden_k_1872 :=
    seq_upd xden_k_1872 (usize 7) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_xden_k_7_v)) : fp_t) in 
  let xden_k_1872 :=
    seq_upd xden_k_1872 (usize 8) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_xden_k_8_v)) : fp_t) in 
  let xden_k_1872 :=
    seq_upd xden_k_1872 (usize 9) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_xden_k_9_v)) : fp_t) in 
  let ynum_k_1873 : seq fp_t :=
    seq_new_ (default : fp_t) (usize 16) in 
  let ynum_k_1873 :=
    seq_upd ynum_k_1873 (usize 0) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_ynum_k_0_v)) : fp_t) in 
  let ynum_k_1873 :=
    seq_upd ynum_k_1873 (usize 1) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_ynum_k_1_v)) : fp_t) in 
  let ynum_k_1873 :=
    seq_upd ynum_k_1873 (usize 2) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_ynum_k_2_v)) : fp_t) in 
  let ynum_k_1873 :=
    seq_upd ynum_k_1873 (usize 3) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_ynum_k_3_v)) : fp_t) in 
  let ynum_k_1873 :=
    seq_upd ynum_k_1873 (usize 4) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_ynum_k_4_v)) : fp_t) in 
  let ynum_k_1873 :=
    seq_upd ynum_k_1873 (usize 5) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_ynum_k_5_v)) : fp_t) in 
  let ynum_k_1873 :=
    seq_upd ynum_k_1873 (usize 6) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_ynum_k_6_v)) : fp_t) in 
  let ynum_k_1873 :=
    seq_upd ynum_k_1873 (usize 7) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_ynum_k_7_v)) : fp_t) in 
  let ynum_k_1873 :=
    seq_upd ynum_k_1873 (usize 8) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_ynum_k_8_v)) : fp_t) in 
  let ynum_k_1873 :=
    seq_upd ynum_k_1873 (usize 9) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_ynum_k_9_v)) : fp_t) in 
  let ynum_k_1873 :=
    seq_upd ynum_k_1873 (usize 10) (nat_mod_from_byte_seq_be (
        array_to_be_bytes (g1_ynum_k_10_v)) : fp_t) in 
  let ynum_k_1873 :=
    seq_upd ynum_k_1873 (usize 11) (nat_mod_from_byte_seq_be (
        array_to_be_bytes (g1_ynum_k_11_v)) : fp_t) in 
  let ynum_k_1873 :=
    seq_upd ynum_k_1873 (usize 12) (nat_mod_from_byte_seq_be (
        array_to_be_bytes (g1_ynum_k_12_v)) : fp_t) in 
  let ynum_k_1873 :=
    seq_upd ynum_k_1873 (usize 13) (nat_mod_from_byte_seq_be (
        array_to_be_bytes (g1_ynum_k_13_v)) : fp_t) in 
  let ynum_k_1873 :=
    seq_upd ynum_k_1873 (usize 14) (nat_mod_from_byte_seq_be (
        array_to_be_bytes (g1_ynum_k_14_v)) : fp_t) in 
  let ynum_k_1873 :=
    seq_upd ynum_k_1873 (usize 15) (nat_mod_from_byte_seq_be (
        array_to_be_bytes (g1_ynum_k_15_v)) : fp_t) in 
  let yden_k_1874 : seq fp_t :=
    seq_new_ (default : fp_t) (usize 15) in 
  let yden_k_1874 :=
    seq_upd yden_k_1874 (usize 0) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_yden_k_0_v)) : fp_t) in 
  let yden_k_1874 :=
    seq_upd yden_k_1874 (usize 1) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_yden_k_1_v)) : fp_t) in 
  let yden_k_1874 :=
    seq_upd yden_k_1874 (usize 2) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_yden_k_2_v)) : fp_t) in 
  let yden_k_1874 :=
    seq_upd yden_k_1874 (usize 3) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_yden_k_3_v)) : fp_t) in 
  let yden_k_1874 :=
    seq_upd yden_k_1874 (usize 4) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_yden_k_4_v)) : fp_t) in 
  let yden_k_1874 :=
    seq_upd yden_k_1874 (usize 5) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_yden_k_5_v)) : fp_t) in 
  let yden_k_1874 :=
    seq_upd yden_k_1874 (usize 6) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_yden_k_6_v)) : fp_t) in 
  let yden_k_1874 :=
    seq_upd yden_k_1874 (usize 7) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_yden_k_7_v)) : fp_t) in 
  let yden_k_1874 :=
    seq_upd yden_k_1874 (usize 8) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_yden_k_8_v)) : fp_t) in 
  let yden_k_1874 :=
    seq_upd yden_k_1874 (usize 9) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_yden_k_9_v)) : fp_t) in 
  let yden_k_1874 :=
    seq_upd yden_k_1874 (usize 10) (nat_mod_from_byte_seq_be (
        array_to_be_bytes (g1_yden_k_10_v)) : fp_t) in 
  let yden_k_1874 :=
    seq_upd yden_k_1874 (usize 11) (nat_mod_from_byte_seq_be (
        array_to_be_bytes (g1_yden_k_11_v)) : fp_t) in 
  let yden_k_1874 :=
    seq_upd yden_k_1874 (usize 12) (nat_mod_from_byte_seq_be (
        array_to_be_bytes (g1_yden_k_12_v)) : fp_t) in 
  let yden_k_1874 :=
    seq_upd yden_k_1874 (usize 13) (nat_mod_from_byte_seq_be (
        array_to_be_bytes (g1_yden_k_13_v)) : fp_t) in 
  let yden_k_1874 :=
    seq_upd yden_k_1874 (usize 14) (nat_mod_from_byte_seq_be (
        array_to_be_bytes (g1_yden_k_14_v)) : fp_t) in 
  let xnum_1875 : fp_t :=
    nat_mod_zero  in 
  let xx_1876 : fp_t :=
    nat_mod_one  in 
  let '(xnum_1875, xx_1876) :=
    foldi (usize 0) (seq_len (xnum_k_1871)) (fun i_1877 '(xnum_1875, xx_1876) =>
      let xnum_1875 :=
        (xnum_1875) +% ((xx_1876) *% (seq_index (xnum_k_1871) (i_1877))) in 
      let xx_1876 :=
        (xx_1876) *% (x_1869) in 
      (xnum_1875, xx_1876))
    (xnum_1875, xx_1876) in 
  let xden_1878 : fp_t :=
    nat_mod_zero  in 
  let xx_1879 : fp_t :=
    nat_mod_one  in 
  let '(xden_1878, xx_1879) :=
    foldi (usize 0) (seq_len (xden_k_1872)) (fun i_1880 '(xden_1878, xx_1879) =>
      let xden_1878 :=
        (xden_1878) +% ((xx_1879) *% (seq_index (xden_k_1872) (i_1880))) in 
      let xx_1879 :=
        (xx_1879) *% (x_1869) in 
      (xden_1878, xx_1879))
    (xden_1878, xx_1879) in 
  let xden_1878 :=
    (xden_1878) +% (xx_1879) in 
  let ynum_1881 : fp_t :=
    nat_mod_zero  in 
  let xx_1882 : fp_t :=
    nat_mod_one  in 
  let '(ynum_1881, xx_1882) :=
    foldi (usize 0) (seq_len (ynum_k_1873)) (fun i_1883 '(ynum_1881, xx_1882) =>
      let ynum_1881 :=
        (ynum_1881) +% ((xx_1882) *% (seq_index (ynum_k_1873) (i_1883))) in 
      let xx_1882 :=
        (xx_1882) *% (x_1869) in 
      (ynum_1881, xx_1882))
    (ynum_1881, xx_1882) in 
  let yden_1884 : fp_t :=
    nat_mod_zero  in 
  let xx_1885 : fp_t :=
    nat_mod_one  in 
  let '(yden_1884, xx_1885) :=
    foldi (usize 0) (seq_len (yden_k_1874)) (fun i_1886 '(yden_1884, xx_1885) =>
      let yden_1884 :=
        (yden_1884) +% ((xx_1885) *% (seq_index (yden_k_1874) (i_1886))) in 
      let xx_1885 :=
        (xx_1885) *% (x_1869) in 
      (yden_1884, xx_1885))
    (yden_1884, xx_1885) in 
  let yden_1884 :=
    (yden_1884) +% (xx_1885) in 
  let xr_1887 : fp_t :=
    (xnum_1875) *% (nat_mod_inv (xden_1878)) in 
  let yr_1888 : fp_t :=
    ((y_1870) *% (ynum_1881)) *% (nat_mod_inv (yden_1884)) in 
  let inf_1889 : bool :=
    false in 
  let '(inf_1889) :=
    if ((xden_1878) =.? (nat_mod_zero )) || ((yden_1884) =.? (
        nat_mod_zero )):bool then (let inf_1889 :=
        true in 
      (inf_1889)) else ((inf_1889)) in 
  (xr_1887, yr_1888, inf_1889).

Definition g1_map_to_curve_sswu (u_1890 : fp_t) : g1_t :=
  let '(xp_1891, yp_1892) :=
    g1_simple_swu_iso (u_1890) in 
  let p_1893 : (fp_t × fp_t × bool) :=
    g1_isogeny_map (xp_1891) (yp_1892) in 
  p_1893.

Definition g1_hash_to_curve_sswu
  (msg_1894 : byte_seq)
  (dst_1895 : byte_seq)
  : g1_t :=
  let u_1896 : seq fp_t :=
    fp_hash_to_field (msg_1894) (dst_1895) (usize 2) in 
  let q0_1897 : (fp_t × fp_t × bool) :=
    g1_map_to_curve_sswu (seq_index (u_1896) (usize 0)) in 
  let q1_1898 : (fp_t × fp_t × bool) :=
    g1_map_to_curve_sswu (seq_index (u_1896) (usize 1)) in 
  let r_1899 : (fp_t × fp_t × bool) :=
    g1add (q0_1897) (q1_1898) in 
  let p_1900 : (fp_t × fp_t × bool) :=
    g1_clear_cofactor (r_1899) in 
  p_1900.

Definition g1_encode_to_curve_sswu
  (msg_1901 : byte_seq)
  (dst_1902 : byte_seq)
  : g1_t :=
  let u_1903 : seq fp_t :=
    fp_hash_to_field (msg_1901) (dst_1902) (usize 1) in 
  let q_1904 : (fp_t × fp_t × bool) :=
    g1_map_to_curve_sswu (seq_index (u_1903) (usize 0)) in 
  let p_1905 : (fp_t × fp_t × bool) :=
    g1_clear_cofactor (q_1904) in 
  p_1905.

Definition g2_xnum_k_0_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 416399692810564414) : int64;
        secret (@repr WORDSIZE64 13500519111022079365) : int64;
        secret (@repr WORDSIZE64 3658379999393219626) : int64;
        secret (@repr WORDSIZE64 9850925049107374429) : int64;
        secret (@repr WORDSIZE64 6640057249351452444) : int64;
        secret (@repr WORDSIZE64 7077594464397203414) : int64
      ] in  l).

Definition g2_xnum_k_1_i_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1249199078431693244) : int64;
        secret (@repr WORDSIZE64 3608069185647134863) : int64;
        secret (@repr WORDSIZE64 10975139998179658879) : int64;
        secret (@repr WORDSIZE64 11106031073612571672) : int64;
        secret (@repr WORDSIZE64 1473427674344805717) : int64;
        secret (@repr WORDSIZE64 2786039319482058522) : int64
      ] in  l).

Definition g2_xnum_k_2_r_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1249199078431693244) : int64;
        secret (@repr WORDSIZE64 3608069185647134863) : int64;
        secret (@repr WORDSIZE64 10975139998179658879) : int64;
        secret (@repr WORDSIZE64 11106031073612571672) : int64;
        secret (@repr WORDSIZE64 1473427674344805717) : int64;
        secret (@repr WORDSIZE64 2786039319482058526) : int64
      ] in  l).

Definition g2_xnum_k_2_i_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 624599539215846622) : int64;
        secret (@repr WORDSIZE64 1804034592823567431) : int64;
        secret (@repr WORDSIZE64 14710942035944605247) : int64;
        secret (@repr WORDSIZE64 14776387573661061644) : int64;
        secret (@repr WORDSIZE64 736713837172402858) : int64;
        secret (@repr WORDSIZE64 10616391696595805069) : int64
      ] in  l).

Definition g2_xnum_k_3_r_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1665598771242257658) : int64;
        secret (@repr WORDSIZE64 17108588296669214228) : int64;
        secret (@repr WORDSIZE64 14633519997572878506) : int64;
        secret (@repr WORDSIZE64 2510212049010394485) : int64;
        secret (@repr WORDSIZE64 8113484923696258161) : int64;
        secret (@repr WORDSIZE64 9863633783879261905) : int64
      ] in  l).

Definition g2_xden_k_0_i_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1873798617647539866) : int64;
        secret (@repr WORDSIZE64 5412103778470702295) : int64;
        secret (@repr WORDSIZE64 7239337960414712511) : int64;
        secret (@repr WORDSIZE64 7435674573564081700) : int64;
        secret (@repr WORDSIZE64 2210141511517208575) : int64;
        secret (@repr WORDSIZE64 13402431016077863523) : int64
      ] in  l).

Definition g2_xden_k_1_i_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1873798617647539866) : int64;
        secret (@repr WORDSIZE64 5412103778470702295) : int64;
        secret (@repr WORDSIZE64 7239337960414712511) : int64;
        secret (@repr WORDSIZE64 7435674573564081700) : int64;
        secret (@repr WORDSIZE64 2210141511517208575) : int64;
        secret (@repr WORDSIZE64 13402431016077863583) : int64
      ] in  l).

Definition g2_ynum_k_0_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1526798873638736187) : int64;
        secret (@repr WORDSIZE64 6459500568425337235) : int64;
        secret (@repr WORDSIZE64 1116230615302104219) : int64;
        secret (@repr WORDSIZE64 17673314439684154624) : int64;
        secret (@repr WORDSIZE64 18197961889718808424) : int64;
        secret (@repr WORDSIZE64 1355520937843676934) : int64
      ] in  l).

Definition g2_ynum_k_1_i_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 416399692810564414) : int64;
        secret (@repr WORDSIZE64 13500519111022079365) : int64;
        secret (@repr WORDSIZE64 3658379999393219626) : int64;
        secret (@repr WORDSIZE64 9850925049107374429) : int64;
        secret (@repr WORDSIZE64 6640057249351452444) : int64;
        secret (@repr WORDSIZE64 7077594464397203390) : int64
      ] in  l).

Definition g2_ynum_k_2_r_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1249199078431693244) : int64;
        secret (@repr WORDSIZE64 3608069185647134863) : int64;
        secret (@repr WORDSIZE64 10975139998179658879) : int64;
        secret (@repr WORDSIZE64 11106031073612571672) : int64;
        secret (@repr WORDSIZE64 1473427674344805717) : int64;
        secret (@repr WORDSIZE64 2786039319482058524) : int64
      ] in  l).

Definition g2_ynum_k_2_i_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 624599539215846622) : int64;
        secret (@repr WORDSIZE64 1804034592823567431) : int64;
        secret (@repr WORDSIZE64 14710942035944605247) : int64;
        secret (@repr WORDSIZE64 14776387573661061644) : int64;
        secret (@repr WORDSIZE64 736713837172402858) : int64;
        secret (@repr WORDSIZE64 10616391696595805071) : int64
      ] in  l).

Definition g2_ynum_k_3_r_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1318599027233453979) : int64;
        secret (@repr WORDSIZE64 18155985086623849168) : int64;
        secret (@repr WORDSIZE64 8510412652460270214) : int64;
        secret (@repr WORDSIZE64 12747851915130467410) : int64;
        secret (@repr WORDSIZE64 5654561228188306393) : int64;
        secret (@repr WORDSIZE64 16263467779354626832) : int64
      ] in  l).

Definition g2_yden_k_0_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1873798617647539866) : int64;
        secret (@repr WORDSIZE64 5412103778470702295) : int64;
        secret (@repr WORDSIZE64 7239337960414712511) : int64;
        secret (@repr WORDSIZE64 7435674573564081700) : int64;
        secret (@repr WORDSIZE64 2210141511517208575) : int64;
        secret (@repr WORDSIZE64 13402431016077863163) : int64
      ] in  l).

Definition g2_yden_k_1_i_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1873798617647539866) : int64;
        secret (@repr WORDSIZE64 5412103778470702295) : int64;
        secret (@repr WORDSIZE64 7239337960414712511) : int64;
        secret (@repr WORDSIZE64 7435674573564081700) : int64;
        secret (@repr WORDSIZE64 2210141511517208575) : int64;
        secret (@repr WORDSIZE64 13402431016077863379) : int64
      ] in  l).

Definition g2_yden_k_2_i_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1873798617647539866) : int64;
        secret (@repr WORDSIZE64 5412103778470702295) : int64;
        secret (@repr WORDSIZE64 7239337960414712511) : int64;
        secret (@repr WORDSIZE64 7435674573564081700) : int64;
        secret (@repr WORDSIZE64 2210141511517208575) : int64;
        secret (@repr WORDSIZE64 13402431016077863577) : int64
      ] in  l).

Definition g2_simple_swu_iso (u_1906 : fp2_t) : (fp2_t × fp2_t) :=
  let z_1907 : (fp_t × fp_t) :=
    fp2neg ((nat_mod_two , nat_mod_one )) in 
  let a_1908 : (fp_t × fp_t) :=
    (nat_mod_zero , nat_mod_from_literal (_) (@repr WORDSIZE128 240) : fp_t) in 
  let b_1909 : (fp_t × fp_t) :=
    (
      nat_mod_from_literal (_) (@repr WORDSIZE128 1012) : fp_t,
      nat_mod_from_literal (_) (@repr WORDSIZE128 1012) : fp_t
    ) in 
  let tv1_1910 : (fp_t × fp_t) :=
    fp2inv (fp2add (fp2mul (fp2mul (z_1907) (z_1907)) (fp2mul (fp2mul (u_1906) (
              u_1906)) (fp2mul (u_1906) (u_1906)))) (fp2mul (z_1907) (fp2mul (
            u_1906) (u_1906)))) in 
  let x1_1911 : (fp_t × fp_t) :=
    fp2mul (fp2mul (fp2neg (b_1909)) (fp2inv (a_1908))) (fp2add (fp2fromfp (
          nat_mod_one )) (tv1_1910)) in 
  let '(x1_1911) :=
    if (tv1_1910) =.? (fp2zero ):bool then (let x1_1911 :=
        fp2mul (b_1909) (fp2inv (fp2mul (z_1907) (a_1908))) in 
      (x1_1911)) else ((x1_1911)) in 
  let gx1_1912 : (fp_t × fp_t) :=
    fp2add (fp2add (fp2mul (fp2mul (x1_1911) (x1_1911)) (x1_1911)) (fp2mul (
          a_1908) (x1_1911))) (b_1909) in 
  let x2_1913 : (fp_t × fp_t) :=
    fp2mul (fp2mul (z_1907) (fp2mul (u_1906) (u_1906))) (x1_1911) in 
  let gx2_1914 : (fp_t × fp_t) :=
    fp2add (fp2add (fp2mul (fp2mul (x2_1913) (x2_1913)) (x2_1913)) (fp2mul (
          a_1908) (x2_1913))) (b_1909) in 
  let '(x_1915, y_1916) :=
    (if (fp2_is_square (gx1_1912)):bool then ((x1_1911, fp2_sqrt (gx1_1912)
        )) else ((x2_1913, fp2_sqrt (gx2_1914)))) in 
  let '(y_1916) :=
    if (fp2_sgn0 (u_1906)) !=.? (fp2_sgn0 (y_1916)):bool then (let y_1916 :=
        fp2neg (y_1916) in 
      (y_1916)) else ((y_1916)) in 
  (x_1915, y_1916).

Definition g2_isogeny_map (x_1917 : fp2_t) (y_1918 : fp2_t) : g2_t :=
  let xnum_k_1919 : seq (fp_t × fp_t) :=
    seq_new_ (default : fp2_t) (usize 4) in 
  let xnum_k_1919 :=
    seq_upd xnum_k_1919 (usize 0) ((
        nat_mod_from_byte_seq_be (array_to_be_bytes (g2_xnum_k_0_v)) : fp_t,
        nat_mod_from_byte_seq_be (array_to_be_bytes (g2_xnum_k_0_v)) : fp_t
      )) in 
  let xnum_k_1919 :=
    seq_upd xnum_k_1919 (usize 1) ((
        nat_mod_zero ,
        nat_mod_from_byte_seq_be (array_to_be_bytes (g2_xnum_k_1_i_v)) : fp_t
      )) in 
  let xnum_k_1919 :=
    seq_upd xnum_k_1919 (usize 2) ((
        nat_mod_from_byte_seq_be (array_to_be_bytes (g2_xnum_k_2_r_v)) : fp_t,
        nat_mod_from_byte_seq_be (array_to_be_bytes (g2_xnum_k_2_i_v)) : fp_t
      )) in 
  let xnum_k_1919 :=
    seq_upd xnum_k_1919 (usize 3) ((
        nat_mod_from_byte_seq_be (array_to_be_bytes (g2_xnum_k_3_r_v)) : fp_t,
        nat_mod_zero 
      )) in 
  let xden_k_1920 : seq (fp_t × fp_t) :=
    seq_new_ (default : fp2_t) (usize 2) in 
  let xden_k_1920 :=
    seq_upd xden_k_1920 (usize 0) ((
        nat_mod_zero ,
        nat_mod_from_byte_seq_be (array_to_be_bytes (g2_xden_k_0_i_v)) : fp_t
      )) in 
  let xden_k_1920 :=
    seq_upd xden_k_1920 (usize 1) ((
        nat_mod_from_literal (_) (@repr WORDSIZE128 12) : fp_t,
        nat_mod_from_byte_seq_be (array_to_be_bytes (g2_xden_k_1_i_v)) : fp_t
      )) in 
  let ynum_k_1921 : seq (fp_t × fp_t) :=
    seq_new_ (default : fp2_t) (usize 4) in 
  let ynum_k_1921 :=
    seq_upd ynum_k_1921 (usize 0) ((
        nat_mod_from_byte_seq_be (array_to_be_bytes (g2_ynum_k_0_v)) : fp_t,
        nat_mod_from_byte_seq_be (array_to_be_bytes (g2_ynum_k_0_v)) : fp_t
      )) in 
  let ynum_k_1921 :=
    seq_upd ynum_k_1921 (usize 1) ((
        nat_mod_zero ,
        nat_mod_from_byte_seq_be (array_to_be_bytes (g2_ynum_k_1_i_v)) : fp_t
      )) in 
  let ynum_k_1921 :=
    seq_upd ynum_k_1921 (usize 2) ((
        nat_mod_from_byte_seq_be (array_to_be_bytes (g2_ynum_k_2_r_v)) : fp_t,
        nat_mod_from_byte_seq_be (array_to_be_bytes (g2_ynum_k_2_i_v)) : fp_t
      )) in 
  let ynum_k_1921 :=
    seq_upd ynum_k_1921 (usize 3) ((
        nat_mod_from_byte_seq_be (array_to_be_bytes (g2_ynum_k_3_r_v)) : fp_t,
        nat_mod_zero 
      )) in 
  let yden_k_1922 : seq (fp_t × fp_t) :=
    seq_new_ (default : fp2_t) (usize 3) in 
  let yden_k_1922 :=
    seq_upd yden_k_1922 (usize 0) ((
        nat_mod_from_byte_seq_be (array_to_be_bytes (g2_yden_k_0_v)) : fp_t,
        nat_mod_from_byte_seq_be (array_to_be_bytes (g2_yden_k_0_v)) : fp_t
      )) in 
  let yden_k_1922 :=
    seq_upd yden_k_1922 (usize 1) ((
        nat_mod_zero ,
        nat_mod_from_byte_seq_be (array_to_be_bytes (g2_yden_k_1_i_v)) : fp_t
      )) in 
  let yden_k_1922 :=
    seq_upd yden_k_1922 (usize 2) ((
        nat_mod_from_literal (_) (@repr WORDSIZE128 18) : fp_t,
        nat_mod_from_byte_seq_be (array_to_be_bytes (g2_yden_k_2_i_v)) : fp_t
      )) in 
  let xnum_1923 : (fp_t × fp_t) :=
    fp2zero  in 
  let xx_1924 : (fp_t × fp_t) :=
    fp2fromfp (nat_mod_one ) in 
  let '(xnum_1923, xx_1924) :=
    foldi (usize 0) (seq_len (xnum_k_1919)) (fun i_1925 '(xnum_1923, xx_1924) =>
      let xnum_1923 :=
        fp2add (xnum_1923) (fp2mul (xx_1924) (seq_index (xnum_k_1919) (
              i_1925))) in 
      let xx_1924 :=
        fp2mul (xx_1924) (x_1917) in 
      (xnum_1923, xx_1924))
    (xnum_1923, xx_1924) in 
  let xden_1926 : (fp_t × fp_t) :=
    fp2zero  in 
  let xx_1927 : (fp_t × fp_t) :=
    fp2fromfp (nat_mod_one ) in 
  let '(xden_1926, xx_1927) :=
    foldi (usize 0) (seq_len (xden_k_1920)) (fun i_1928 '(xden_1926, xx_1927) =>
      let xden_1926 :=
        fp2add (xden_1926) (fp2mul (xx_1927) (seq_index (xden_k_1920) (
              i_1928))) in 
      let xx_1927 :=
        fp2mul (xx_1927) (x_1917) in 
      (xden_1926, xx_1927))
    (xden_1926, xx_1927) in 
  let xden_1926 :=
    fp2add (xden_1926) (xx_1927) in 
  let ynum_1929 : (fp_t × fp_t) :=
    fp2zero  in 
  let xx_1930 : (fp_t × fp_t) :=
    fp2fromfp (nat_mod_one ) in 
  let '(ynum_1929, xx_1930) :=
    foldi (usize 0) (seq_len (ynum_k_1921)) (fun i_1931 '(ynum_1929, xx_1930) =>
      let ynum_1929 :=
        fp2add (ynum_1929) (fp2mul (xx_1930) (seq_index (ynum_k_1921) (
              i_1931))) in 
      let xx_1930 :=
        fp2mul (xx_1930) (x_1917) in 
      (ynum_1929, xx_1930))
    (ynum_1929, xx_1930) in 
  let yden_1932 : (fp_t × fp_t) :=
    fp2zero  in 
  let xx_1933 : (fp_t × fp_t) :=
    fp2fromfp (nat_mod_one ) in 
  let '(yden_1932, xx_1933) :=
    foldi (usize 0) (seq_len (yden_k_1922)) (fun i_1934 '(yden_1932, xx_1933) =>
      let yden_1932 :=
        fp2add (yden_1932) (fp2mul (xx_1933) (seq_index (yden_k_1922) (
              i_1934))) in 
      let xx_1933 :=
        fp2mul (xx_1933) (x_1917) in 
      (yden_1932, xx_1933))
    (yden_1932, xx_1933) in 
  let yden_1932 :=
    fp2add (yden_1932) (xx_1933) in 
  let xr_1935 : (fp_t × fp_t) :=
    fp2mul (xnum_1923) (fp2inv (xden_1926)) in 
  let yr_1936 : (fp_t × fp_t) :=
    fp2mul (y_1918) (fp2mul (ynum_1929) (fp2inv (yden_1932))) in 
  let inf_1937 : bool :=
    false in 
  let '(inf_1937) :=
    if ((xden_1926) =.? (fp2zero )) || ((yden_1932) =.? (fp2zero )):bool then (
      let inf_1937 :=
        true in 
      (inf_1937)) else ((inf_1937)) in 
  (xr_1935, yr_1936, inf_1937).

Definition g2_map_to_curve_sswu (u_1938 : fp2_t) : g2_t :=
  let '(xp_1939, yp_1940) :=
    g2_simple_swu_iso (u_1938) in 
  let p_1941 : ((fp_t × fp_t) × (fp_t × fp_t) × bool) :=
    g2_isogeny_map (xp_1939) (yp_1940) in 
  p_1941.

Definition g2_hash_to_curve_sswu
  (msg_1942 : byte_seq)
  (dst_1943 : byte_seq)
  : g2_t :=
  let u_1944 : seq fp2_t :=
    fp2_hash_to_field (msg_1942) (dst_1943) (usize 2) in 
  let q0_1945 : ((fp_t × fp_t) × (fp_t × fp_t) × bool) :=
    g2_map_to_curve_sswu (seq_index (u_1944) (usize 0)) in 
  let q1_1946 : ((fp_t × fp_t) × (fp_t × fp_t) × bool) :=
    g2_map_to_curve_sswu (seq_index (u_1944) (usize 1)) in 
  let r_1947 : ((fp_t × fp_t) × (fp_t × fp_t) × bool) :=
    g2add (q0_1945) (q1_1946) in 
  let p_1948 : ((fp_t × fp_t) × (fp_t × fp_t) × bool) :=
    g2_clear_cofactor (r_1947) in 
  p_1948.

Definition g2_encode_to_curve_sswu
  (msg_1949 : byte_seq)
  (dst_1950 : byte_seq)
  : g2_t :=
  let u_1951 : seq fp2_t :=
    fp2_hash_to_field (msg_1949) (dst_1950) (usize 1) in 
  let q_1952 : ((fp_t × fp_t) × (fp_t × fp_t) × bool) :=
    g2_map_to_curve_sswu (seq_index (u_1951) (usize 0)) in 
  let p_1953 : ((fp_t × fp_t) × (fp_t × fp_t) × bool) :=
    g2_clear_cofactor (q_1952) in 
  p_1953.

