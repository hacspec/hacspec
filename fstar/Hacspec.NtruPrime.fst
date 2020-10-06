module Hacspec.NtruPrime

#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"

open Hacspec.Lib
open FStar.Mul

let build_irreducible (p_1846 : uint_size) : seq pub_int128 =
  let irr_1847 = seq_new_ (pub_i128 0x0) ((p_1846) + (usize 1)) in
  let irr_1847 = array_upd irr_1847 (usize 0) (- (pub_i128 0x1)) in
  let irr_1847 = array_upd irr_1847 (usize 1) (- (pub_i128 0x1)) in
  let irr_1847 = array_upd irr_1847 (p_1846) (pub_i128 0x1) in
  irr_1847

let round_to_3
  (poly_1848 : seq pub_int128)
  (q_1849 : pub_int128)
  : seq pub_int128 =
  let result_1850 = seq_clone (poly_1848) in
  let q_12_1851 = ((q_1849) -. (pub_i128 0x1)) /. (pub_i128 0x2) in
  let (result_1850) =
    foldi (usize 0) (seq_len (poly_1848)) (fun i_1852 (result_1850) ->
      let (result_1850) =
        if (array_index (poly_1848) (i_1852)) >. (q_12_1851) then begin
          let result_1850 =
            array_upd result_1850 (i_1852) (
              (array_index (poly_1848) (i_1852)) -. (q_1849))
          in
          (result_1850)
        end else begin (result_1850)
        end
      in
      (result_1850))
    (result_1850)
  in
  let (result_1850) =
    foldi (usize 0) (seq_len (result_1850)) (fun i_1853 (result_1850) ->
      let (result_1850) =
        if ((array_index (result_1850) (i_1853)) %. (pub_i128 0x3)) != (
          pub_i128 0x0) then begin
          let result_1850 =
            array_upd result_1850 (i_1853) (
              (array_index (result_1850) (i_1853)) -. (pub_i128 0x1))
          in
          let (result_1850) =
            if ((array_index (result_1850) (i_1853)) %. (pub_i128 0x3)) != (
              pub_i128 0x0) then begin
              let result_1850 =
                array_upd result_1850 (i_1853) (
                  (array_index (result_1850) (i_1853)) +. (pub_i128 0x2))
              in
              (result_1850)
            end else begin (result_1850)
            end
          in
          (result_1850)
        end else begin (result_1850)
        end
      in
      (result_1850))
    (result_1850)
  in
  result_1850

let encrypt
  (r_1854 : seq pub_int128)
  (h_1855 : seq pub_int128)
  (q_1856 : pub_int128)
  (irreducible_1857 : seq pub_int128)
  : seq pub_int128 =
  let pre_1858 = mul_poly_irr (r_1854) (h_1855) (irreducible_1857) (q_1856) in
  round_to_3 (pre_1858) (q_1856)

let ntru_prime_653_encrypt
  (r_1859 : seq pub_int128)
  (h_1860 : seq pub_int128)
  : seq pub_int128 =
  let p_1861 = usize 653 in
  let q_1862 = pub_i128 0x120d in
  let w_1863 = usize 288 in
  let irreducible_1864 = build_irreducible (p_1861) in
  encrypt (r_1859) (h_1860) (q_1862) (irreducible_1864)

let ntru_prime_653_decrypt
  (c_1865 : seq pub_int128)
  (key_f_1866 : seq pub_int128)
  (key_v_1867 : seq pub_int128)
  : (seq pub_int128 & bool) =
  let p_1868 = usize 653 in
  let q_1869 = pub_i128 0x120d in
  let w_1870 = usize 288 in
  let irreducible_1871 = build_irreducible (p_1868) in
  let f_c_1872 =
    mul_poly_irr (key_f_1866) (c_1865) (irreducible_1871) (q_1869)
  in
  let f_3_c_and_decryption_ok_1873 =
    poly_to_ring (irreducible_1871) (
      add_poly (f_c_1872) (add_poly (f_c_1872) (f_c_1872) (q_1869)) (q_1869)) (
      q_1869)
  in
  let (f_3_c_1874, ok_decrypt_1875) = f_3_c_and_decryption_ok_1873 in
  let f_3_c_1876 = f_3_c_1874 in
  let q_12_1877 = ((q_1869) -. (pub_i128 0x1)) /. (pub_i128 0x2) in
  let (f_3_c_1876) =
    foldi (usize 0) (seq_len (f_3_c_1876)) (fun i_1878 (f_3_c_1876) ->
      let (f_3_c_1876) =
        if (array_index (f_3_c_1876) (i_1878)) >. (q_12_1877) then begin
          let f_3_c_1876 =
            array_upd f_3_c_1876 (i_1878) (
              (array_index (f_3_c_1876) (i_1878)) -. (q_1869))
          in
          (f_3_c_1876)
        end else begin (f_3_c_1876)
        end
      in
      (f_3_c_1876))
    (f_3_c_1876)
  in
  let e_1879 = seq_new_ (pub_i128 0x0) (seq_len (f_3_c_1876)) in
  let (e_1879) =
    foldi (usize 0) (seq_len (e_1879)) (fun i_1880 (e_1879) ->
      let e_1879 =
        array_upd e_1879 (i_1880) (
          (array_index (f_3_c_1876) (i_1880)) %. (pub_i128 0x3))
      in
      (e_1879))
    (e_1879)
  in
  let e_1879 = make_positive (e_1879) (pub_i128 0x3) in
  let r_1881 =
    mul_poly_irr (e_1879) (key_v_1867) (irreducible_1871) (pub_i128 0x3)
  in
  let (r_1881) =
    foldi (usize 0) (seq_len (r_1881)) (fun i_1882 (r_1881) ->
      let (r_1881) =
        if (array_index (r_1881) (i_1882)) == (pub_i128 0x2) then begin
          let r_1881 = array_upd r_1881 (i_1882) (- (pub_i128 0x1)) in
          (r_1881)
        end else begin (r_1881)
        end
      in
      (r_1881))
    (r_1881)
  in
  (r_1881, ok_decrypt_1875)

