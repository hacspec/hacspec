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
  (msg_1835 : byte_seq)
  (dst_1836 : byte_seq)
  (len_in_bytes_1837 : uint_size)
  
  : byte_seq :=
  let ell_1838 : uint_size :=
    (((len_in_bytes_1837) + (b_in_bytes_v)) - (usize 1)) / (b_in_bytes_v) in 
  let dst_prime_1839 : seq uint8 :=
    seq_push (dst_1836) (uint8_from_usize (seq_len (dst_1836))) in 
  let z_pad_1840 : seq uint8 :=
    seq_new_ (default : uint8) (s_in_bytes_v) in 
  let l_i_b_str_1841 : seq uint8 :=
    seq_new_ (default : uint8) (usize 2) in 
  let l_i_b_str_1841 :=
    seq_upd l_i_b_str_1841 (usize 0) (uint8_from_usize ((len_in_bytes_1837) / (
          usize 256))) in 
  let l_i_b_str_1841 :=
    seq_upd l_i_b_str_1841 (usize 1) (uint8_from_usize (len_in_bytes_1837)) in 
  let msg_prime_1842 : seq uint8 :=
    seq_concat (seq_concat (seq_concat (seq_concat (z_pad_1840) (msg_1835)) (
          l_i_b_str_1841)) (seq_new_ (default : uint8) (usize 1))) (
      dst_prime_1839) in 
  let b_0_1843 : seq uint8 :=
    seq_from_seq (array_to_seq (hash (msg_prime_1842))) in 
  let b_i_1844 : seq uint8 :=
    seq_from_seq (array_to_seq (hash (seq_concat (seq_push (b_0_1843) (secret (
              @repr WORDSIZE8 1) : int8)) (dst_prime_1839)))) in 
  let uniform_bytes_1845 : seq uint8 :=
    seq_from_seq (b_i_1844) in 
  let '(b_i_1844, uniform_bytes_1845) :=
    foldi (usize 2) ((ell_1838) + (usize 1)) (fun i_1846 '(
        b_i_1844,
        uniform_bytes_1845
      ) =>
      let t_1847 : seq uint8 :=
        seq_from_seq (b_0_1843) in 
      let b_i_1844 :=
        seq_from_seq (array_to_seq (hash (seq_concat (seq_push ((
                  t_1847) seq_xor (b_i_1844)) (uint8_from_usize (i_1846))) (
              dst_prime_1839)))) in 
      let uniform_bytes_1845 :=
        seq_concat (uniform_bytes_1845) (b_i_1844) in 
      (b_i_1844, uniform_bytes_1845))
    (b_i_1844, uniform_bytes_1845) in 
  seq_truncate (uniform_bytes_1845) (len_in_bytes_1837).

Definition fp_hash_to_field
  (msg_1848 : byte_seq)
  (dst_1849 : byte_seq)
  (count_1850 : uint_size)
  
  : seq fp_t :=
  let len_in_bytes_1851 : uint_size :=
    (count_1850) * (l_v) in 
  let uniform_bytes_1852 : seq uint8 :=
    expand_message_xmd (msg_1848) (dst_1849) (len_in_bytes_1851) in 
  let output_1853 : seq fp_t :=
    seq_new_ (default : fp_t) (count_1850) in 
  let output_1853 :=
    foldi (usize 0) (count_1850) (fun i_1854 output_1853 =>
      let elm_offset_1855 : uint_size :=
        (l_v) * (i_1854) in 
      let tv_1856 : seq uint8 :=
        seq_slice (uniform_bytes_1852) (elm_offset_1855) (l_v) in 
      let u_i_1857 : fp_t :=
        nat_mod_from_byte_seq_be (seq_slice (nat_mod_to_byte_seq_be (
              nat_mod_from_byte_seq_be (tv_1856) : fp_hash_t)) (usize 16) (
            usize 48)) : fp_t in 
      let output_1853 :=
        seq_upd output_1853 (i_1854) (u_i_1857) in 
      (output_1853))
    output_1853 in 
  output_1853.

Definition fp_sgn0 (x_1858 : fp_t)  : bool :=
  ((x_1858) rem (nat_mod_two )) =.? (nat_mod_one ).

Definition fp_is_square (x_1859 : fp_t)  : bool :=
  let c1_1860 : fp_t :=
    nat_mod_from_byte_seq_be (array_to_be_bytes (p_1_2_v)) : fp_t in 
  let tv_1861 : fp_t :=
    nat_mod_pow_self (x_1859) (c1_1860) in 
  ((tv_1861) =.? (nat_mod_zero )) || ((tv_1861) =.? (nat_mod_one )).

Definition fp_sqrt (x_1862 : fp_t)  : fp_t :=
  let c1_1863 : fp_t :=
    nat_mod_from_byte_seq_be (array_to_be_bytes (p_1_4_v)) : fp_t in 
  nat_mod_pow_self (x_1862) (c1_1863).

Definition g1_curve_func (x_1864 : fp_t)  : fp_t :=
  (((x_1864) *% (x_1864)) *% (x_1864)) +% (nat_mod_from_literal (_) (
      @repr WORDSIZE128 4) : fp_t).

Definition g1_map_to_curve_svdw (u_1865 : fp_t)  : g1_t :=
  let z_1866 : fp_t :=
    (nat_mod_zero ) -% (nat_mod_from_literal (_) (
        @repr WORDSIZE128 3) : fp_t) in 
  let gz_1867 : fp_t :=
    g1_curve_func (z_1866) in 
  let tv1_1868 : fp_t :=
    ((u_1865) *% (u_1865)) *% (gz_1867) in 
  let tv2_1869 : fp_t :=
    (nat_mod_one ) +% (tv1_1868) in 
  let tv1_1870 : fp_t :=
    (nat_mod_one ) -% (tv1_1868) in 
  let tv3_1871 : fp_t :=
    nat_mod_inv ((tv1_1870) *% (tv2_1869)) in 
  let tv4_1872 : fp_t :=
    fp_sqrt (((nat_mod_zero ) -% (gz_1867)) *% (((nat_mod_from_literal (_) (
              @repr WORDSIZE128 3) : fp_t) *% (z_1866)) *% (z_1866))) in 
  let '(tv4_1872) :=
    if fp_sgn0 (tv4_1872):bool then (let tv4_1872 :=
        (nat_mod_zero ) -% (tv4_1872) in 
      (tv4_1872)) else ((tv4_1872)) in 
  let tv5_1873 : fp_t :=
    (((u_1865) *% (tv1_1870)) *% (tv3_1871)) *% (tv4_1872) in 
  let tv6_1874 : fp_t :=
    (((nat_mod_zero ) -% (nat_mod_from_literal (_) (
            @repr WORDSIZE128 4) : fp_t)) *% (gz_1867)) *% (nat_mod_inv (((
            nat_mod_from_literal (_) (@repr WORDSIZE128 3) : fp_t) *% (
            z_1866)) *% (z_1866))) in 
  let x1_1875 : fp_t :=
    (((nat_mod_zero ) -% (z_1866)) *% (nat_mod_inv (nat_mod_two ))) -% (
      tv5_1873) in 
  let x2_1876 : fp_t :=
    (((nat_mod_zero ) -% (z_1866)) *% (nat_mod_inv (nat_mod_two ))) +% (
      tv5_1873) in 
  let x3_1877 : fp_t :=
    (z_1866) +% (((tv6_1874) *% (((tv2_1869) *% (tv2_1869)) *% (tv3_1871))) *% (
        ((tv2_1869) *% (tv2_1869)) *% (tv3_1871))) in 
  let x_1878 : fp_t :=
    (if (fp_is_square (g1_curve_func (x1_1875))):bool then (x1_1875) else ((if (
            fp_is_square (g1_curve_func (x2_1876))):bool then (x2_1876) else (
            x3_1877)))) in 
  let y_1879 : fp_t :=
    fp_sqrt (g1_curve_func (x_1878)) in 
  let '(y_1879) :=
    if (fp_sgn0 (u_1865)) !=.? (fp_sgn0 (y_1879)):bool then (let y_1879 :=
        (nat_mod_zero ) -% (y_1879) in 
      (y_1879)) else ((y_1879)) in 
  (x_1878, y_1879, false).

Definition g1_clear_cofactor (x_1880 : g1_t)  : g1_t :=
  let h_eff_1881 : scalar_t :=
    nat_mod_from_literal (_) (
      @repr WORDSIZE128 15132376222941642753) : scalar_t in 
  g1mul (h_eff_1881) (x_1880).

Definition g1_hash_to_curve_svdw
  (msg_1882 : byte_seq)
  (dst_1883 : byte_seq)
  
  : g1_t :=
  let u_1884 : seq fp_t :=
    fp_hash_to_field (msg_1882) (dst_1883) (usize 2) in 
  let q0_1885 : (fp_t '× fp_t '× bool) :=
    g1_map_to_curve_svdw (seq_index (u_1884) (usize 0)) in 
  let q1_1886 : (fp_t '× fp_t '× bool) :=
    g1_map_to_curve_svdw (seq_index (u_1884) (usize 1)) in 
  let r_1887 : (fp_t '× fp_t '× bool) :=
    g1add (q0_1885) (q1_1886) in 
  let p_1888 : (fp_t '× fp_t '× bool) :=
    g1_clear_cofactor (r_1887) in 
  p_1888.

Definition g1_encode_to_curve_svdw
  (msg_1889 : byte_seq)
  (dst_1890 : byte_seq)
  
  : g1_t :=
  let u_1891 : seq fp_t :=
    fp_hash_to_field (msg_1889) (dst_1890) (usize 1) in 
  let q_1892 : (fp_t '× fp_t '× bool) :=
    g1_map_to_curve_svdw (seq_index (u_1891) (usize 0)) in 
  let p_1893 : (fp_t '× fp_t '× bool) :=
    g1_clear_cofactor (q_1892) in 
  p_1893.

Definition fp2_hash_to_field
  (msg_1894 : byte_seq)
  (dst_1895 : byte_seq)
  (count_1896 : uint_size)
  
  : seq fp2_t :=
  let len_in_bytes_1897 : uint_size :=
    ((count_1896) * (usize 2)) * (l_v) in 
  let uniform_bytes_1898 : seq uint8 :=
    expand_message_xmd (msg_1894) (dst_1895) (len_in_bytes_1897) in 
  let output_1899 : seq (fp_t '× fp_t) :=
    seq_new_ (default : fp2_t) (count_1896) in 
  let output_1899 :=
    foldi (usize 0) (count_1896) (fun i_1900 output_1899 =>
      let elm_offset_1901 : uint_size :=
        ((l_v) * (i_1900)) * (usize 2) in 
      let tv_1902 : seq uint8 :=
        seq_slice (uniform_bytes_1898) (elm_offset_1901) (l_v) in 
      let e_1_1903 : fp_t :=
        nat_mod_from_byte_seq_be (seq_slice (nat_mod_to_byte_seq_be (
              nat_mod_from_byte_seq_be (tv_1902) : fp_hash_t)) (usize 16) (
            usize 48)) : fp_t in 
      let elm_offset_1904 : uint_size :=
        (l_v) * ((usize 1) + ((i_1900) * (usize 2))) in 
      let tv_1905 : seq uint8 :=
        seq_slice (uniform_bytes_1898) (elm_offset_1904) (l_v) in 
      let e_2_1906 : fp_t :=
        nat_mod_from_byte_seq_be (seq_slice (nat_mod_to_byte_seq_be (
              nat_mod_from_byte_seq_be (tv_1905) : fp_hash_t)) (usize 16) (
            usize 48)) : fp_t in 
      let output_1899 :=
        seq_upd output_1899 (i_1900) ((e_1_1903, e_2_1906)) in 
      (output_1899))
    output_1899 in 
  output_1899.

Definition fp2_sgn0 (x_1907 : fp2_t)  : bool :=
  let '(x0_1908, x1_1909) :=
    x_1907 in 
  let sign_0_1910 : bool :=
    fp_sgn0 (x0_1908) in 
  let zero_0_1911 : bool :=
    (x0_1908) =.? (nat_mod_zero ) in 
  let sign_1_1912 : bool :=
    fp_sgn0 (x1_1909) in 
  (sign_0_1910) || ((zero_0_1911) && (sign_1_1912)).

Definition fp2_is_square (x_1913 : fp2_t)  : bool :=
  let c1_1914 : fp_t :=
    nat_mod_from_byte_seq_be (array_to_be_bytes (p_1_2_v)) : fp_t in 
  let '(x1_1915, x2_1916) :=
    x_1913 in 
  let tv1_1917 : fp_t :=
    (x1_1915) *% (x1_1915) in 
  let tv2_1918 : fp_t :=
    (x2_1916) *% (x2_1916) in 
  let tv1_1919 : fp_t :=
    (tv1_1917) +% (tv2_1918) in 
  let tv1_1920 : fp_t :=
    nat_mod_pow_self (tv1_1919) (c1_1914) in 
  let neg1_1921 : fp_t :=
    (nat_mod_zero ) -% (nat_mod_one ) in 
  (tv1_1920) !=.? (neg1_1921).

Definition fp2exp (n_1922 : fp2_t) (k_1923 : fp_t)  : fp2_t :=
  let c_1924 : (fp_t '× fp_t) :=
    fp2fromfp (nat_mod_one ) in 
  let c_1924 :=
    foldi (usize 0) (usize 381) (fun i_1925 c_1924 =>
      let c_1924 :=
        fp2mul (c_1924) (c_1924) in 
      let '(c_1924) :=
        if nat_mod_bit (k_1923) ((usize 380) - (i_1925)):bool then (
          let c_1924 :=
            fp2mul (c_1924) (n_1922) in 
          (c_1924)) else ((c_1924)) in 
      (c_1924))
    c_1924 in 
  c_1924.

Definition fp2_sqrt (a_1926 : fp2_t)  : fp2_t :=
  let c1_1927 : fp_t :=
    nat_mod_from_byte_seq_be (array_to_be_bytes (p_3_4_v)) : fp_t in 
  let c2_1928 : fp_t :=
    nat_mod_from_byte_seq_be (array_to_be_bytes (p_1_2_v)) : fp_t in 
  let a1_1929 : (fp_t '× fp_t) :=
    fp2exp (a_1926) (c1_1927) in 
  let alpha_1930 : (fp_t '× fp_t) :=
    fp2mul (a1_1929) (fp2mul (a1_1929) (a_1926)) in 
  let x0_1931 : (fp_t '× fp_t) :=
    fp2mul (a1_1929) (a_1926) in 
  let neg1_1932 : (fp_t '× fp_t) :=
    ((nat_mod_zero ) -% (nat_mod_one ), nat_mod_zero ) in 
  let b_1933 : (fp_t '× fp_t) :=
    fp2exp (fp2add (fp2fromfp (nat_mod_one )) (alpha_1930)) (c2_1928) in 
  (if ((alpha_1930) =.? (neg1_1932)):bool then (fp2mul ((
          nat_mod_zero ,
          nat_mod_one 
        )) (x0_1931)) else (fp2mul (b_1933) (x0_1931))).

Definition g2_curve_func (x_1934 : fp2_t)  : fp2_t :=
  fp2add (fp2mul (x_1934) (fp2mul (x_1934) (x_1934))) ((
      nat_mod_from_literal (_) (@repr WORDSIZE128 4) : fp_t,
      nat_mod_from_literal (_) (@repr WORDSIZE128 4) : fp_t
    )).

Definition g2_map_to_curve_svdw (u_1935 : fp2_t)  : g2_t :=
  let z_1936 : (fp_t '× fp_t) :=
    fp2neg (fp2fromfp (nat_mod_one )) in 
  let gz_1937 : (fp_t '× fp_t) :=
    g2_curve_func (z_1936) in 
  let tv1_1938 : (fp_t '× fp_t) :=
    fp2mul (fp2mul (u_1935) (u_1935)) (gz_1937) in 
  let tv2_1939 : (fp_t '× fp_t) :=
    fp2add (fp2fromfp (nat_mod_one )) (tv1_1938) in 
  let tv1_1940 : (fp_t '× fp_t) :=
    fp2sub (fp2fromfp (nat_mod_one )) (tv1_1938) in 
  let tv3_1941 : (fp_t '× fp_t) :=
    fp2inv (fp2mul (tv1_1940) (tv2_1939)) in 
  let tv4_1942 : (fp_t '× fp_t) :=
    fp2_sqrt (fp2mul (fp2neg (gz_1937)) (fp2mul (fp2fromfp (
            nat_mod_from_literal (_) (@repr WORDSIZE128 3) : fp_t)) (fp2mul (
            z_1936) (z_1936)))) in 
  let '(tv4_1942) :=
    if fp2_sgn0 (tv4_1942):bool then (let tv4_1942 :=
        fp2neg (tv4_1942) in 
      (tv4_1942)) else ((tv4_1942)) in 
  let tv5_1943 : (fp_t '× fp_t) :=
    fp2mul (fp2mul (fp2mul (u_1935) (tv1_1940)) (tv3_1941)) (tv4_1942) in 
  let tv6_1944 : (fp_t '× fp_t) :=
    fp2mul (fp2mul (fp2neg (fp2fromfp (nat_mod_from_literal (_) (
              @repr WORDSIZE128 4) : fp_t))) (gz_1937)) (fp2inv (fp2mul (
          fp2fromfp (nat_mod_from_literal (_) (@repr WORDSIZE128 3) : fp_t)) (
          fp2mul (z_1936) (z_1936)))) in 
  let x1_1945 : (fp_t '× fp_t) :=
    fp2sub (fp2mul (fp2neg (z_1936)) (fp2inv (fp2fromfp (nat_mod_two )))) (
      tv5_1943) in 
  let x2_1946 : (fp_t '× fp_t) :=
    fp2add (fp2mul (fp2neg (z_1936)) (fp2inv (fp2fromfp (nat_mod_two )))) (
      tv5_1943) in 
  let tv7_1947 : (fp_t '× fp_t) :=
    fp2mul (fp2mul (tv2_1939) (tv2_1939)) (tv3_1941) in 
  let x3_1948 : (fp_t '× fp_t) :=
    fp2add (z_1936) (fp2mul (tv6_1944) (fp2mul (tv7_1947) (tv7_1947))) in 
  let x_1949 : (fp_t '× fp_t) :=
    (if (fp2_is_square (g2_curve_func (x1_1945))):bool then (x1_1945) else ((
          if (fp2_is_square (g2_curve_func (x2_1946))):bool then (
            x2_1946) else (x3_1948)))) in 
  let y_1950 : (fp_t '× fp_t) :=
    fp2_sqrt (g2_curve_func (x_1949)) in 
  let '(y_1950) :=
    if (fp2_sgn0 (u_1935)) !=.? (fp2_sgn0 (y_1950)):bool then (let y_1950 :=
        fp2neg (y_1950) in 
      (y_1950)) else ((y_1950)) in 
  (x_1949, y_1950, false).

Definition psi (p_1951 : g2_t)  : g2_t :=
  let c1_1952 : (fp_t '× fp_t) :=
    fp2inv (fp2exp ((nat_mod_one , nat_mod_one )) (((nat_mod_zero ) -% (
            nat_mod_one )) *% (nat_mod_inv (nat_mod_from_literal (_) (
              @repr WORDSIZE128 3) : fp_t)))) in 
  let c2_1953 : (fp_t '× fp_t) :=
    fp2inv (fp2exp ((nat_mod_one , nat_mod_one )) (((nat_mod_zero ) -% (
            nat_mod_one )) *% (nat_mod_inv (nat_mod_two )))) in 
  let '(x_1954, y_1955, inf_1956) :=
    p_1951 in 
  let qx_1957 : (fp_t '× fp_t) :=
    fp2mul (c1_1952) (fp2conjugate (x_1954)) in 
  let qy_1958 : (fp_t '× fp_t) :=
    fp2mul (c2_1953) (fp2conjugate (y_1955)) in 
  (qx_1957, qy_1958, inf_1956).

Definition g2_clear_cofactor (p_1959 : g2_t)  : g2_t :=
  let c1_1960 : scalar_t :=
    nat_mod_from_literal (_) (
      @repr WORDSIZE128 15132376222941642752) : scalar_t in 
  let t1_1961 : ((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool) :=
    g2mul (c1_1960) (p_1959) in 
  let t1_1962 : ((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool) :=
    g2neg (t1_1961) in 
  let t2_1963 : ((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool) :=
    psi (p_1959) in 
  let t3_1964 : ((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool) :=
    g2double (p_1959) in 
  let t3_1965 : ((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool) :=
    psi (psi (t3_1964)) in 
  let t3_1966 : ((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool) :=
    g2add (t3_1965) (g2neg (t2_1963)) in 
  let t2_1967 : ((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool) :=
    g2add (t1_1962) (t2_1963) in 
  let t2_1968 : ((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool) :=
    g2mul (c1_1960) (t2_1967) in 
  let t2_1969 : ((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool) :=
    g2neg (t2_1968) in 
  let t3_1970 : ((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool) :=
    g2add (t3_1966) (t2_1969) in 
  let t3_1971 : ((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool) :=
    g2add (t3_1970) (g2neg (t1_1962)) in 
  let q_1972 : ((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool) :=
    g2add (t3_1971) (g2neg (p_1959)) in 
  q_1972.

Definition g2_hash_to_curve_svdw
  (msg_1973 : byte_seq)
  (dst_1974 : byte_seq)
  
  : g2_t :=
  let u_1975 : seq fp2_t :=
    fp2_hash_to_field (msg_1973) (dst_1974) (usize 2) in 
  let q0_1976 : ((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool) :=
    g2_map_to_curve_svdw (seq_index (u_1975) (usize 0)) in 
  let q1_1977 : ((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool) :=
    g2_map_to_curve_svdw (seq_index (u_1975) (usize 1)) in 
  let r_1978 : ((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool) :=
    g2add (q0_1976) (q1_1977) in 
  let p_1979 : ((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool) :=
    g2_clear_cofactor (r_1978) in 
  p_1979.

Definition g2_encode_to_curve_svdw
  (msg_1980 : byte_seq)
  (dst_1981 : byte_seq)
  
  : g2_t :=
  let u_1982 : seq fp2_t :=
    fp2_hash_to_field (msg_1980) (dst_1981) (usize 1) in 
  let q_1983 : ((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool) :=
    g2_map_to_curve_svdw (seq_index (u_1982) (usize 0)) in 
  let p_1984 : ((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool) :=
    g2_clear_cofactor (q_1983) in 
  p_1984.

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

Definition g1_simple_swu_iso (u_1985 : fp_t)  : (fp_t '× fp_t) :=
  let z_1986 : fp_t :=
    nat_mod_from_literal (_) (@repr WORDSIZE128 11) : fp_t in 
  let a_1987 : fp_t :=
    nat_mod_from_byte_seq_be (array_to_be_bytes (g1_iso_a_v)) : fp_t in 
  let b_1988 : fp_t :=
    nat_mod_from_byte_seq_be (array_to_be_bytes (g1_iso_b_v)) : fp_t in 
  let tv1_1989 : fp_t :=
    nat_mod_inv ((((z_1986) *% (z_1986)) *% (nat_mod_exp (u_1985) (
            @repr WORDSIZE32 4))) +% (((z_1986) *% (u_1985)) *% (u_1985))) in 
  let x1_1990 : fp_t :=
    (((nat_mod_zero ) -% (b_1988)) *% (nat_mod_inv (a_1987))) *% ((
        nat_mod_one ) +% (tv1_1989)) in 
  let '(x1_1990) :=
    if (tv1_1989) =.? (nat_mod_zero ):bool then (let x1_1990 :=
        (b_1988) *% (nat_mod_inv ((z_1986) *% (a_1987))) in 
      (x1_1990)) else ((x1_1990)) in 
  let gx1_1991 : fp_t :=
    ((nat_mod_exp (x1_1990) (@repr WORDSIZE32 3)) +% ((a_1987) *% (
          x1_1990))) +% (b_1988) in 
  let x2_1992 : fp_t :=
    (((z_1986) *% (u_1985)) *% (u_1985)) *% (x1_1990) in 
  let gx2_1993 : fp_t :=
    ((nat_mod_exp (x2_1992) (@repr WORDSIZE32 3)) +% ((a_1987) *% (
          x2_1992))) +% (b_1988) in 
  let '(x_1994, y_1995) :=
    (if (fp_is_square (gx1_1991)):bool then ((x1_1990, fp_sqrt (gx1_1991)
        )) else ((x2_1992, fp_sqrt (gx2_1993)))) in 
  let '(y_1995) :=
    if (fp_sgn0 (u_1985)) !=.? (fp_sgn0 (y_1995)):bool then (let y_1995 :=
        (nat_mod_zero ) -% (y_1995) in 
      (y_1995)) else ((y_1995)) in 
  (x_1994, y_1995).

Definition g1_isogeny_map (x_1996 : fp_t) (y_1997 : fp_t)  : g1_t :=
  let xnum_k_1998 : seq fp_t :=
    seq_new_ (default : fp_t) (usize 12) in 
  let xnum_k_1998 :=
    seq_upd xnum_k_1998 (usize 0) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_xnum_k_0_v)) : fp_t) in 
  let xnum_k_1998 :=
    seq_upd xnum_k_1998 (usize 1) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_xnum_k_1_v)) : fp_t) in 
  let xnum_k_1998 :=
    seq_upd xnum_k_1998 (usize 2) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_xnum_k_2_v)) : fp_t) in 
  let xnum_k_1998 :=
    seq_upd xnum_k_1998 (usize 3) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_xnum_k_3_v)) : fp_t) in 
  let xnum_k_1998 :=
    seq_upd xnum_k_1998 (usize 4) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_xnum_k_4_v)) : fp_t) in 
  let xnum_k_1998 :=
    seq_upd xnum_k_1998 (usize 5) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_xnum_k_5_v)) : fp_t) in 
  let xnum_k_1998 :=
    seq_upd xnum_k_1998 (usize 6) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_xnum_k_6_v)) : fp_t) in 
  let xnum_k_1998 :=
    seq_upd xnum_k_1998 (usize 7) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_xnum_k_7_v)) : fp_t) in 
  let xnum_k_1998 :=
    seq_upd xnum_k_1998 (usize 8) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_xnum_k_8_v)) : fp_t) in 
  let xnum_k_1998 :=
    seq_upd xnum_k_1998 (usize 9) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_xnum_k_9_v)) : fp_t) in 
  let xnum_k_1998 :=
    seq_upd xnum_k_1998 (usize 10) (nat_mod_from_byte_seq_be (
        array_to_be_bytes (g1_xnum_k_10_v)) : fp_t) in 
  let xnum_k_1998 :=
    seq_upd xnum_k_1998 (usize 11) (nat_mod_from_byte_seq_be (
        array_to_be_bytes (g1_xnum_k_11_v)) : fp_t) in 
  let xden_k_1999 : seq fp_t :=
    seq_new_ (default : fp_t) (usize 10) in 
  let xden_k_1999 :=
    seq_upd xden_k_1999 (usize 0) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_xden_k_0_v)) : fp_t) in 
  let xden_k_1999 :=
    seq_upd xden_k_1999 (usize 1) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_xden_k_1_v)) : fp_t) in 
  let xden_k_1999 :=
    seq_upd xden_k_1999 (usize 2) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_xden_k_2_v)) : fp_t) in 
  let xden_k_1999 :=
    seq_upd xden_k_1999 (usize 3) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_xden_k_3_v)) : fp_t) in 
  let xden_k_1999 :=
    seq_upd xden_k_1999 (usize 4) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_xden_k_4_v)) : fp_t) in 
  let xden_k_1999 :=
    seq_upd xden_k_1999 (usize 5) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_xden_k_5_v)) : fp_t) in 
  let xden_k_1999 :=
    seq_upd xden_k_1999 (usize 6) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_xden_k_6_v)) : fp_t) in 
  let xden_k_1999 :=
    seq_upd xden_k_1999 (usize 7) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_xden_k_7_v)) : fp_t) in 
  let xden_k_1999 :=
    seq_upd xden_k_1999 (usize 8) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_xden_k_8_v)) : fp_t) in 
  let xden_k_1999 :=
    seq_upd xden_k_1999 (usize 9) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_xden_k_9_v)) : fp_t) in 
  let ynum_k_2000 : seq fp_t :=
    seq_new_ (default : fp_t) (usize 16) in 
  let ynum_k_2000 :=
    seq_upd ynum_k_2000 (usize 0) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_ynum_k_0_v)) : fp_t) in 
  let ynum_k_2000 :=
    seq_upd ynum_k_2000 (usize 1) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_ynum_k_1_v)) : fp_t) in 
  let ynum_k_2000 :=
    seq_upd ynum_k_2000 (usize 2) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_ynum_k_2_v)) : fp_t) in 
  let ynum_k_2000 :=
    seq_upd ynum_k_2000 (usize 3) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_ynum_k_3_v)) : fp_t) in 
  let ynum_k_2000 :=
    seq_upd ynum_k_2000 (usize 4) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_ynum_k_4_v)) : fp_t) in 
  let ynum_k_2000 :=
    seq_upd ynum_k_2000 (usize 5) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_ynum_k_5_v)) : fp_t) in 
  let ynum_k_2000 :=
    seq_upd ynum_k_2000 (usize 6) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_ynum_k_6_v)) : fp_t) in 
  let ynum_k_2000 :=
    seq_upd ynum_k_2000 (usize 7) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_ynum_k_7_v)) : fp_t) in 
  let ynum_k_2000 :=
    seq_upd ynum_k_2000 (usize 8) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_ynum_k_8_v)) : fp_t) in 
  let ynum_k_2000 :=
    seq_upd ynum_k_2000 (usize 9) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_ynum_k_9_v)) : fp_t) in 
  let ynum_k_2000 :=
    seq_upd ynum_k_2000 (usize 10) (nat_mod_from_byte_seq_be (
        array_to_be_bytes (g1_ynum_k_10_v)) : fp_t) in 
  let ynum_k_2000 :=
    seq_upd ynum_k_2000 (usize 11) (nat_mod_from_byte_seq_be (
        array_to_be_bytes (g1_ynum_k_11_v)) : fp_t) in 
  let ynum_k_2000 :=
    seq_upd ynum_k_2000 (usize 12) (nat_mod_from_byte_seq_be (
        array_to_be_bytes (g1_ynum_k_12_v)) : fp_t) in 
  let ynum_k_2000 :=
    seq_upd ynum_k_2000 (usize 13) (nat_mod_from_byte_seq_be (
        array_to_be_bytes (g1_ynum_k_13_v)) : fp_t) in 
  let ynum_k_2000 :=
    seq_upd ynum_k_2000 (usize 14) (nat_mod_from_byte_seq_be (
        array_to_be_bytes (g1_ynum_k_14_v)) : fp_t) in 
  let ynum_k_2000 :=
    seq_upd ynum_k_2000 (usize 15) (nat_mod_from_byte_seq_be (
        array_to_be_bytes (g1_ynum_k_15_v)) : fp_t) in 
  let yden_k_2001 : seq fp_t :=
    seq_new_ (default : fp_t) (usize 15) in 
  let yden_k_2001 :=
    seq_upd yden_k_2001 (usize 0) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_yden_k_0_v)) : fp_t) in 
  let yden_k_2001 :=
    seq_upd yden_k_2001 (usize 1) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_yden_k_1_v)) : fp_t) in 
  let yden_k_2001 :=
    seq_upd yden_k_2001 (usize 2) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_yden_k_2_v)) : fp_t) in 
  let yden_k_2001 :=
    seq_upd yden_k_2001 (usize 3) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_yden_k_3_v)) : fp_t) in 
  let yden_k_2001 :=
    seq_upd yden_k_2001 (usize 4) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_yden_k_4_v)) : fp_t) in 
  let yden_k_2001 :=
    seq_upd yden_k_2001 (usize 5) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_yden_k_5_v)) : fp_t) in 
  let yden_k_2001 :=
    seq_upd yden_k_2001 (usize 6) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_yden_k_6_v)) : fp_t) in 
  let yden_k_2001 :=
    seq_upd yden_k_2001 (usize 7) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_yden_k_7_v)) : fp_t) in 
  let yden_k_2001 :=
    seq_upd yden_k_2001 (usize 8) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_yden_k_8_v)) : fp_t) in 
  let yden_k_2001 :=
    seq_upd yden_k_2001 (usize 9) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_yden_k_9_v)) : fp_t) in 
  let yden_k_2001 :=
    seq_upd yden_k_2001 (usize 10) (nat_mod_from_byte_seq_be (
        array_to_be_bytes (g1_yden_k_10_v)) : fp_t) in 
  let yden_k_2001 :=
    seq_upd yden_k_2001 (usize 11) (nat_mod_from_byte_seq_be (
        array_to_be_bytes (g1_yden_k_11_v)) : fp_t) in 
  let yden_k_2001 :=
    seq_upd yden_k_2001 (usize 12) (nat_mod_from_byte_seq_be (
        array_to_be_bytes (g1_yden_k_12_v)) : fp_t) in 
  let yden_k_2001 :=
    seq_upd yden_k_2001 (usize 13) (nat_mod_from_byte_seq_be (
        array_to_be_bytes (g1_yden_k_13_v)) : fp_t) in 
  let yden_k_2001 :=
    seq_upd yden_k_2001 (usize 14) (nat_mod_from_byte_seq_be (
        array_to_be_bytes (g1_yden_k_14_v)) : fp_t) in 
  let xnum_2002 : fp_t :=
    nat_mod_zero  in 
  let xx_2003 : fp_t :=
    nat_mod_one  in 
  let '(xnum_2002, xx_2003) :=
    foldi (usize 0) (seq_len (xnum_k_1998)) (fun i_2004 '(xnum_2002, xx_2003) =>
      let xnum_2002 :=
        (xnum_2002) +% ((xx_2003) *% (seq_index (xnum_k_1998) (i_2004))) in 
      let xx_2003 :=
        (xx_2003) *% (x_1996) in 
      (xnum_2002, xx_2003))
    (xnum_2002, xx_2003) in 
  let xden_2005 : fp_t :=
    nat_mod_zero  in 
  let xx_2006 : fp_t :=
    nat_mod_one  in 
  let '(xden_2005, xx_2006) :=
    foldi (usize 0) (seq_len (xden_k_1999)) (fun i_2007 '(xden_2005, xx_2006) =>
      let xden_2005 :=
        (xden_2005) +% ((xx_2006) *% (seq_index (xden_k_1999) (i_2007))) in 
      let xx_2006 :=
        (xx_2006) *% (x_1996) in 
      (xden_2005, xx_2006))
    (xden_2005, xx_2006) in 
  let xden_2005 :=
    (xden_2005) +% (xx_2006) in 
  let ynum_2008 : fp_t :=
    nat_mod_zero  in 
  let xx_2009 : fp_t :=
    nat_mod_one  in 
  let '(ynum_2008, xx_2009) :=
    foldi (usize 0) (seq_len (ynum_k_2000)) (fun i_2010 '(ynum_2008, xx_2009) =>
      let ynum_2008 :=
        (ynum_2008) +% ((xx_2009) *% (seq_index (ynum_k_2000) (i_2010))) in 
      let xx_2009 :=
        (xx_2009) *% (x_1996) in 
      (ynum_2008, xx_2009))
    (ynum_2008, xx_2009) in 
  let yden_2011 : fp_t :=
    nat_mod_zero  in 
  let xx_2012 : fp_t :=
    nat_mod_one  in 
  let '(yden_2011, xx_2012) :=
    foldi (usize 0) (seq_len (yden_k_2001)) (fun i_2013 '(yden_2011, xx_2012) =>
      let yden_2011 :=
        (yden_2011) +% ((xx_2012) *% (seq_index (yden_k_2001) (i_2013))) in 
      let xx_2012 :=
        (xx_2012) *% (x_1996) in 
      (yden_2011, xx_2012))
    (yden_2011, xx_2012) in 
  let yden_2011 :=
    (yden_2011) +% (xx_2012) in 
  let xr_2014 : fp_t :=
    (xnum_2002) *% (nat_mod_inv (xden_2005)) in 
  let yr_2015 : fp_t :=
    ((y_1997) *% (ynum_2008)) *% (nat_mod_inv (yden_2011)) in 
  let inf_2016 : bool :=
    false in 
  let '(inf_2016) :=
    if ((xden_2005) =.? (nat_mod_zero )) || ((yden_2011) =.? (
        nat_mod_zero )):bool then (let inf_2016 :=
        true in 
      (inf_2016)) else ((inf_2016)) in 
  (xr_2014, yr_2015, inf_2016).

Definition g1_map_to_curve_sswu (u_2017 : fp_t)  : g1_t :=
  let '(xp_2018, yp_2019) :=
    g1_simple_swu_iso (u_2017) in 
  let p_2020 : (fp_t '× fp_t '× bool) :=
    g1_isogeny_map (xp_2018) (yp_2019) in 
  p_2020.

Definition g1_hash_to_curve_sswu
  (msg_2021 : byte_seq)
  (dst_2022 : byte_seq)
  
  : g1_t :=
  let u_2023 : seq fp_t :=
    fp_hash_to_field (msg_2021) (dst_2022) (usize 2) in 
  let q0_2024 : (fp_t '× fp_t '× bool) :=
    g1_map_to_curve_sswu (seq_index (u_2023) (usize 0)) in 
  let q1_2025 : (fp_t '× fp_t '× bool) :=
    g1_map_to_curve_sswu (seq_index (u_2023) (usize 1)) in 
  let r_2026 : (fp_t '× fp_t '× bool) :=
    g1add (q0_2024) (q1_2025) in 
  let p_2027 : (fp_t '× fp_t '× bool) :=
    g1_clear_cofactor (r_2026) in 
  p_2027.

Definition g1_encode_to_curve_sswu
  (msg_2028 : byte_seq)
  (dst_2029 : byte_seq)
  
  : g1_t :=
  let u_2030 : seq fp_t :=
    fp_hash_to_field (msg_2028) (dst_2029) (usize 1) in 
  let q_2031 : (fp_t '× fp_t '× bool) :=
    g1_map_to_curve_sswu (seq_index (u_2030) (usize 0)) in 
  let p_2032 : (fp_t '× fp_t '× bool) :=
    g1_clear_cofactor (q_2031) in 
  p_2032.

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

Definition g2_simple_swu_iso (u_2033 : fp2_t)  : (fp2_t '× fp2_t) :=
  let z_2034 : (fp_t '× fp_t) :=
    fp2neg ((nat_mod_two , nat_mod_one )) in 
  let a_2035 : (fp_t '× fp_t) :=
    (nat_mod_zero , nat_mod_from_literal (_) (@repr WORDSIZE128 240) : fp_t) in 
  let b_2036 : (fp_t '× fp_t) :=
    (
      nat_mod_from_literal (_) (@repr WORDSIZE128 1012) : fp_t,
      nat_mod_from_literal (_) (@repr WORDSIZE128 1012) : fp_t
    ) in 
  let tv1_2037 : (fp_t '× fp_t) :=
    fp2inv (fp2add (fp2mul (fp2mul (z_2034) (z_2034)) (fp2mul (fp2mul (u_2033) (
              u_2033)) (fp2mul (u_2033) (u_2033)))) (fp2mul (z_2034) (fp2mul (
            u_2033) (u_2033)))) in 
  let x1_2038 : (fp_t '× fp_t) :=
    fp2mul (fp2mul (fp2neg (b_2036)) (fp2inv (a_2035))) (fp2add (fp2fromfp (
          nat_mod_one )) (tv1_2037)) in 
  let '(x1_2038) :=
    if (tv1_2037) =.? (fp2zero ):bool then (let x1_2038 :=
        fp2mul (b_2036) (fp2inv (fp2mul (z_2034) (a_2035))) in 
      (x1_2038)) else ((x1_2038)) in 
  let gx1_2039 : (fp_t '× fp_t) :=
    fp2add (fp2add (fp2mul (fp2mul (x1_2038) (x1_2038)) (x1_2038)) (fp2mul (
          a_2035) (x1_2038))) (b_2036) in 
  let x2_2040 : (fp_t '× fp_t) :=
    fp2mul (fp2mul (z_2034) (fp2mul (u_2033) (u_2033))) (x1_2038) in 
  let gx2_2041 : (fp_t '× fp_t) :=
    fp2add (fp2add (fp2mul (fp2mul (x2_2040) (x2_2040)) (x2_2040)) (fp2mul (
          a_2035) (x2_2040))) (b_2036) in 
  let '(x_2042, y_2043) :=
    (if (fp2_is_square (gx1_2039)):bool then ((x1_2038, fp2_sqrt (gx1_2039)
        )) else ((x2_2040, fp2_sqrt (gx2_2041)))) in 
  let '(y_2043) :=
    if (fp2_sgn0 (u_2033)) !=.? (fp2_sgn0 (y_2043)):bool then (let y_2043 :=
        fp2neg (y_2043) in 
      (y_2043)) else ((y_2043)) in 
  (x_2042, y_2043).

Definition g2_isogeny_map (x_2044 : fp2_t) (y_2045 : fp2_t)  : g2_t :=
  let xnum_k_2046 : seq (fp_t '× fp_t) :=
    seq_new_ (default : fp2_t) (usize 4) in 
  let xnum_k_2046 :=
    seq_upd xnum_k_2046 (usize 0) ((
        nat_mod_from_byte_seq_be (array_to_be_bytes (g2_xnum_k_0_v)) : fp_t,
        nat_mod_from_byte_seq_be (array_to_be_bytes (g2_xnum_k_0_v)) : fp_t
      )) in 
  let xnum_k_2046 :=
    seq_upd xnum_k_2046 (usize 1) ((
        nat_mod_zero ,
        nat_mod_from_byte_seq_be (array_to_be_bytes (g2_xnum_k_1_i_v)) : fp_t
      )) in 
  let xnum_k_2046 :=
    seq_upd xnum_k_2046 (usize 2) ((
        nat_mod_from_byte_seq_be (array_to_be_bytes (g2_xnum_k_2_r_v)) : fp_t,
        nat_mod_from_byte_seq_be (array_to_be_bytes (g2_xnum_k_2_i_v)) : fp_t
      )) in 
  let xnum_k_2046 :=
    seq_upd xnum_k_2046 (usize 3) ((
        nat_mod_from_byte_seq_be (array_to_be_bytes (g2_xnum_k_3_r_v)) : fp_t,
        nat_mod_zero 
      )) in 
  let xden_k_2047 : seq (fp_t '× fp_t) :=
    seq_new_ (default : fp2_t) (usize 2) in 
  let xden_k_2047 :=
    seq_upd xden_k_2047 (usize 0) ((
        nat_mod_zero ,
        nat_mod_from_byte_seq_be (array_to_be_bytes (g2_xden_k_0_i_v)) : fp_t
      )) in 
  let xden_k_2047 :=
    seq_upd xden_k_2047 (usize 1) ((
        nat_mod_from_literal (_) (@repr WORDSIZE128 12) : fp_t,
        nat_mod_from_byte_seq_be (array_to_be_bytes (g2_xden_k_1_i_v)) : fp_t
      )) in 
  let ynum_k_2048 : seq (fp_t '× fp_t) :=
    seq_new_ (default : fp2_t) (usize 4) in 
  let ynum_k_2048 :=
    seq_upd ynum_k_2048 (usize 0) ((
        nat_mod_from_byte_seq_be (array_to_be_bytes (g2_ynum_k_0_v)) : fp_t,
        nat_mod_from_byte_seq_be (array_to_be_bytes (g2_ynum_k_0_v)) : fp_t
      )) in 
  let ynum_k_2048 :=
    seq_upd ynum_k_2048 (usize 1) ((
        nat_mod_zero ,
        nat_mod_from_byte_seq_be (array_to_be_bytes (g2_ynum_k_1_i_v)) : fp_t
      )) in 
  let ynum_k_2048 :=
    seq_upd ynum_k_2048 (usize 2) ((
        nat_mod_from_byte_seq_be (array_to_be_bytes (g2_ynum_k_2_r_v)) : fp_t,
        nat_mod_from_byte_seq_be (array_to_be_bytes (g2_ynum_k_2_i_v)) : fp_t
      )) in 
  let ynum_k_2048 :=
    seq_upd ynum_k_2048 (usize 3) ((
        nat_mod_from_byte_seq_be (array_to_be_bytes (g2_ynum_k_3_r_v)) : fp_t,
        nat_mod_zero 
      )) in 
  let yden_k_2049 : seq (fp_t '× fp_t) :=
    seq_new_ (default : fp2_t) (usize 3) in 
  let yden_k_2049 :=
    seq_upd yden_k_2049 (usize 0) ((
        nat_mod_from_byte_seq_be (array_to_be_bytes (g2_yden_k_0_v)) : fp_t,
        nat_mod_from_byte_seq_be (array_to_be_bytes (g2_yden_k_0_v)) : fp_t
      )) in 
  let yden_k_2049 :=
    seq_upd yden_k_2049 (usize 1) ((
        nat_mod_zero ,
        nat_mod_from_byte_seq_be (array_to_be_bytes (g2_yden_k_1_i_v)) : fp_t
      )) in 
  let yden_k_2049 :=
    seq_upd yden_k_2049 (usize 2) ((
        nat_mod_from_literal (_) (@repr WORDSIZE128 18) : fp_t,
        nat_mod_from_byte_seq_be (array_to_be_bytes (g2_yden_k_2_i_v)) : fp_t
      )) in 
  let xnum_2050 : (fp_t '× fp_t) :=
    fp2zero  in 
  let xx_2051 : (fp_t '× fp_t) :=
    fp2fromfp (nat_mod_one ) in 
  let '(xnum_2050, xx_2051) :=
    foldi (usize 0) (seq_len (xnum_k_2046)) (fun i_2052 '(xnum_2050, xx_2051) =>
      let xnum_2050 :=
        fp2add (xnum_2050) (fp2mul (xx_2051) (seq_index (xnum_k_2046) (
              i_2052))) in 
      let xx_2051 :=
        fp2mul (xx_2051) (x_2044) in 
      (xnum_2050, xx_2051))
    (xnum_2050, xx_2051) in 
  let xden_2053 : (fp_t '× fp_t) :=
    fp2zero  in 
  let xx_2054 : (fp_t '× fp_t) :=
    fp2fromfp (nat_mod_one ) in 
  let '(xden_2053, xx_2054) :=
    foldi (usize 0) (seq_len (xden_k_2047)) (fun i_2055 '(xden_2053, xx_2054) =>
      let xden_2053 :=
        fp2add (xden_2053) (fp2mul (xx_2054) (seq_index (xden_k_2047) (
              i_2055))) in 
      let xx_2054 :=
        fp2mul (xx_2054) (x_2044) in 
      (xden_2053, xx_2054))
    (xden_2053, xx_2054) in 
  let xden_2053 :=
    fp2add (xden_2053) (xx_2054) in 
  let ynum_2056 : (fp_t '× fp_t) :=
    fp2zero  in 
  let xx_2057 : (fp_t '× fp_t) :=
    fp2fromfp (nat_mod_one ) in 
  let '(ynum_2056, xx_2057) :=
    foldi (usize 0) (seq_len (ynum_k_2048)) (fun i_2058 '(ynum_2056, xx_2057) =>
      let ynum_2056 :=
        fp2add (ynum_2056) (fp2mul (xx_2057) (seq_index (ynum_k_2048) (
              i_2058))) in 
      let xx_2057 :=
        fp2mul (xx_2057) (x_2044) in 
      (ynum_2056, xx_2057))
    (ynum_2056, xx_2057) in 
  let yden_2059 : (fp_t '× fp_t) :=
    fp2zero  in 
  let xx_2060 : (fp_t '× fp_t) :=
    fp2fromfp (nat_mod_one ) in 
  let '(yden_2059, xx_2060) :=
    foldi (usize 0) (seq_len (yden_k_2049)) (fun i_2061 '(yden_2059, xx_2060) =>
      let yden_2059 :=
        fp2add (yden_2059) (fp2mul (xx_2060) (seq_index (yden_k_2049) (
              i_2061))) in 
      let xx_2060 :=
        fp2mul (xx_2060) (x_2044) in 
      (yden_2059, xx_2060))
    (yden_2059, xx_2060) in 
  let yden_2059 :=
    fp2add (yden_2059) (xx_2060) in 
  let xr_2062 : (fp_t '× fp_t) :=
    fp2mul (xnum_2050) (fp2inv (xden_2053)) in 
  let yr_2063 : (fp_t '× fp_t) :=
    fp2mul (y_2045) (fp2mul (ynum_2056) (fp2inv (yden_2059))) in 
  let inf_2064 : bool :=
    false in 
  let '(inf_2064) :=
    if ((xden_2053) =.? (fp2zero )) || ((yden_2059) =.? (fp2zero )):bool then (
      let inf_2064 :=
        true in 
      (inf_2064)) else ((inf_2064)) in 
  (xr_2062, yr_2063, inf_2064).

Definition g2_map_to_curve_sswu (u_2065 : fp2_t)  : g2_t :=
  let '(xp_2066, yp_2067) :=
    g2_simple_swu_iso (u_2065) in 
  let p_2068 : ((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool) :=
    g2_isogeny_map (xp_2066) (yp_2067) in 
  p_2068.

Definition g2_hash_to_curve_sswu
  (msg_2069 : byte_seq)
  (dst_2070 : byte_seq)
  
  : g2_t :=
  let u_2071 : seq fp2_t :=
    fp2_hash_to_field (msg_2069) (dst_2070) (usize 2) in 
  let q0_2072 : ((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool) :=
    g2_map_to_curve_sswu (seq_index (u_2071) (usize 0)) in 
  let q1_2073 : ((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool) :=
    g2_map_to_curve_sswu (seq_index (u_2071) (usize 1)) in 
  let r_2074 : ((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool) :=
    g2add (q0_2072) (q1_2073) in 
  let p_2075 : ((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool) :=
    g2_clear_cofactor (r_2074) in 
  p_2075.

Definition g2_encode_to_curve_sswu
  (msg_2076 : byte_seq)
  (dst_2077 : byte_seq)
  
  : g2_t :=
  let u_2078 : seq fp2_t :=
    fp2_hash_to_field (msg_2076) (dst_2077) (usize 1) in 
  let q_2079 : ((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool) :=
    g2_map_to_curve_sswu (seq_index (u_2078) (usize 0)) in 
  let p_2080 : ((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool) :=
    g2_clear_cofactor (q_2079) in 
  p_2080.

