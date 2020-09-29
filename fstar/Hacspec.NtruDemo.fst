module Hacspec.NtruDemo

#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"

open Hacspec.Lib
open FStar.Mul

let build_irreducible (p_1843 : uint_size) : seq pub_int128 =
  let irr_1844 =
    seq_new_ #((pub_int128)) #((pub_i128 0x0)) ((p_1843) + (usize 1))
  in
  let irr_1844 = array_upd irr_1844 (usize 0) (- (pub_i128 0x1)) in
  let irr_1844 = array_upd irr_1844 (usize 1) (- (pub_i128 0x1)) in
  let irr_1844 = array_upd irr_1844 (p_1843) (pub_i128 0x1) in
  irr_1844

let round_to_3
  (poly_1845 : seq pub_int128)
  (q_1846 : pub_int128)
  : seq pub_int128 =
  let result_1847 = seq_clone (poly_1845) in
  let q_12_1848 = ((q_1846) -. (pub_i128 0x1)) /. (pub_i128 0x2) in
  let (result_1847) =
    foldi (usize 0) (seq_len (poly_1845)) (fun (i_1849, (result_1847)) ->
      let (result_1847) =
        if (array_index (poly_1845) (i_1849)) >. (q_12_1848) then begin
          let result_1847 =
            array_upd result_1847 (i_1849) (
              (array_index (poly_1845) (i_1849)) -. (q_1846))
          in
          (result_1847)
        end else begin (result_1847)
        end
      in
      (result_1847))
    (result_1847)
  in
  let (result_1847) =
    foldi (usize 0) (seq_len (result_1847)) (fun (i_1850, (result_1847)) ->
      let (result_1847) =
        if ((array_index (result_1847) (i_1850)) %. (pub_i128 0x3)) != (
          pub_i128 0x0) then begin
          let result_1847 =
            array_upd result_1847 (i_1850) (
              (array_index (result_1847) (i_1850)) -. (pub_i128 0x1))
          in
          let (result_1847) =
            if ((array_index (result_1847) (i_1850)) %. (pub_i128 0x3)) != (
              pub_i128 0x0) then begin
              let result_1847 =
                array_upd result_1847 (i_1850) (
                  (array_index (result_1847) (i_1850)) +. (pub_i128 0x2))
              in
              (result_1847)
            end else begin (result_1847)
            end
          in
          (result_1847)
        end else begin (result_1847)
        end
      in
      (result_1847))
    (result_1847)
  in
  result_1847

let encrypt
  (r_1851 : seq pub_int128)
  (h_1852 : seq pub_int128)
  (q_1853 : pub_int128)
  (irreducible_1854 : seq pub_int128)
  : seq pub_int128 =
  let pre_1855 = mul_poly_irr (r_1851) (h_1852) (irreducible_1854) (q_1853) in
  round_to_3 (pre_1855) (q_1853)

let ntru_prime_653_encrypt
  (r_1856 : seq pub_int128)
  (h_1857 : seq pub_int128)
  : seq pub_int128 =
  let p_1858 = usize 653 in
  let q_1859 = pub_i128 0x120d in
  let w_1860 = usize 288 in
  let irreducible_1861 = build_irreducible (p_1858) in
  encrypt (r_1856) (h_1857) (q_1859) (irreducible_1861)

let ntru_prime_653_decrypt
  (c_1862 : seq pub_int128)
  (key_f_1863 : seq pub_int128)
  (key_v_1864 : seq pub_int128)
  : (seq pub_int128 & bool) =
  let p_1865 = usize 653 in
  let q_1866 = pub_i128 0x120d in
  let w_1867 = usize 288 in
  let irreducible_1868 = build_irreducible (p_1865) in
  let f_c_1869 =
    mul_poly_irr (key_f_1863) (c_1862) (irreducible_1868) (q_1866)
  in
  let f_3_c_and_decryption_ok_1870 =
    poly_to_ring (irreducible_1868) (
      add_poly (f_c_1869) (add_poly (f_c_1869) (f_c_1869) (q_1866)) (q_1866)) (
      q_1866)
  in
  let (f_3_c_1871, ok_decrypt_1872) = f_3_c_and_decryption_ok_1870 in
  let f_3_c_1873 = f_3_c_1871 in
  let q_12_1874 = ((q_1866) -. (pub_i128 0x1)) /. (pub_i128 0x2) in
  let (f_3_c_1873) =
    foldi (usize 0) (seq_len (f_3_c_1873)) (fun (i_1875, (f_3_c_1873)) ->
      let (f_3_c_1873) =
        if (array_index (f_3_c_1873) (i_1875)) >. (q_12_1874) then begin
          let f_3_c_1873 =
            array_upd f_3_c_1873 (i_1875) (
              (array_index (f_3_c_1873) (i_1875)) -. (q_1866))
          in
          (f_3_c_1873)
        end else begin (f_3_c_1873)
        end
      in
      (f_3_c_1873))
    (f_3_c_1873)
  in
  let e_1876 =
    seq_new_ #((pub_int128)) #((pub_i128 0x0)) (seq_len (f_3_c_1873))
  in
  let (e_1876) =
    foldi (usize 0) (seq_len (e_1876)) (fun (i_1877, (e_1876)) ->
      let e_1876 =
        array_upd e_1876 (i_1877) (
          (array_index (f_3_c_1873) (i_1877)) %. (pub_i128 0x3))
      in
      (e_1876))
    (e_1876)
  in
  let e_1876 = make_positive (e_1876) (pub_i128 0x3) in
  let r_1878 =
    mul_poly_irr (e_1876) (key_v_1864) (irreducible_1868) (pub_i128 0x3)
  in
  let (r_1878) =
    foldi (usize 0) (seq_len (r_1878)) (fun (i_1879, (r_1878)) ->
      let (r_1878) =
        if (array_index (r_1878) (i_1879)) == (pub_i128 0x2) then begin
          let r_1878 = array_upd r_1878 (i_1879) (- (pub_i128 0x1)) in
          (r_1878)
        end else begin (r_1878)
        end
      in
      (r_1878))
    (r_1878)
  in
  (r_1878, ok_decrypt_1872)

