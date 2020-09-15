module NtruDemo

open Rustspec
open FStar.Mul

module RSeq = Rustspec.Seq

let build_irreducible (p_1842 : usize) : RSeq.seq i128 =
  let irr_1843 = RSeq.new_ #i128 (p_1842 + 1ul) in
  let irr_1843 = array_upd irr_1843 (0ul) (- Int128.uint_to_t 1) in
  let irr_1843 = array_upd irr_1843 (1ul) (- Int128.uint_to_t 1) in
  let irr_1843 = array_upd irr_1843 (p_1842) (Int128.uint_to_t 1) in
  irr_1843

let round_to_3 (poly_1844 : RSeq.seq i128) (q_1845 : i128) : RSeq.seq i128 =
  let result_1846 = clone (poly_1844) in
  let q_12_1847 = q_1845 - Int128.uint_to_t 1 / Int128.uint_to_t 2 in
  let (result_1846) =
    foldi (0ul) (len (poly_1844)) (fun (i_1848, (result_1846)) ->
      let (result_1846) =
        if array_index (poly_1844) (i_1848) > q_12_1847 then begin
          let result_1846 =
            array_upd result_1846 (i_1848) (
              array_index (poly_1844) (i_1848) - q_1845)
          in
          (result_1846)
        end else begin (result_1846)
        end
      in
      (result_1846))
    (result_1846)
  in
  let (result_1846) =
    foldi (0ul) (len (result_1846)) (fun (i_1849, (result_1846)) ->
      let (result_1846) =
        if array_index (result_1846) (
          i_1849) % Int128.uint_to_t 3 != Int128.uint_to_t 0 then begin
          let result_1846 =
            array_upd result_1846 (i_1849) (
              array_index (result_1846) (i_1849) - Int128.uint_to_t 1)
          in
          let (result_1846) =
            if array_index (result_1846) (
              i_1849) % Int128.uint_to_t 3 != Int128.uint_to_t 0 then begin
              let result_1846 =
                array_upd result_1846 (i_1849) (
                  array_index (result_1846) (i_1849) + Int128.uint_to_t 2)
              in
              (result_1846)
            end else begin (result_1846)
            end
          in
          (result_1846)
        end else begin (result_1846)
        end
      in
      (result_1846))
    (result_1846)
  in
  result_1846

let encrypt
  (r_1850 : RSeq.seq i128)
  (h_1851 : RSeq.seq i128)
  (q_1852 : i128)
  (irreducible_1853 : RSeq.seq i128)
  : RSeq.seq i128 =
  let pre_1854 = mul_poly_irr (r_1850) (h_1851) (irreducible_1853) (q_1852) in
  round_to_3 (pre_1854) (q_1852)

let ntru_prime_653_encrypt
  (r_1855 : RSeq.seq i128)
  (h_1856 : RSeq.seq i128)
  : RSeq.seq i128 =
  let p_1857 = 653ul in
  let q_1858 = Int128.uint_to_t 4621 in
  let w_1859 = 288ul in
  let irreducible_1860 = build_irreducible (p_1857) in
  encrypt (r_1855) (h_1856) (q_1858) (irreducible_1860)

let ntru_prime_653_decrypt
  (c_1861 : RSeq.seq i128)
  (key_f_1862 : RSeq.seq i128)
  (key_v_1863 : RSeq.seq i128)
  : (RSeq.seq i128 & bool) =
  let p_1864 = 653ul in
  let q_1865 = Int128.uint_to_t 4621 in
  let w_1866 = 288ul in
  let irreducible_1867 = build_irreducible (p_1864) in
  let f_c_1868 =
    mul_poly_irr (key_f_1862) (c_1861) (irreducible_1867) (q_1865)
  in
  let f_3_c_and_decryption_ok_1869 =
    poly_to_ring (irreducible_1867) (
      add_poly (f_c_1868) (add_poly (f_c_1868) (f_c_1868) (q_1865)) (q_1865)) (
      q_1865)
  in
  let (f_3_c_1870, ok_decrypt_1871) = f_3_c_and_decryption_ok_1869 in
  let f_3_c_1872 = f_3_c_1870 in
  let q_12_1873 = q_1865 - Int128.uint_to_t 1 / Int128.uint_to_t 2 in
  let (f_3_c_1872) =
    foldi (0ul) (len (f_3_c_1872)) (fun (i_1874, (f_3_c_1872)) ->
      let (f_3_c_1872) =
        if array_index (f_3_c_1872) (i_1874) > q_12_1873 then begin
          let f_3_c_1872 =
            array_upd f_3_c_1872 (i_1874) (
              array_index (f_3_c_1872) (i_1874) - q_1865)
          in
          (f_3_c_1872)
        end else begin (f_3_c_1872)
        end
      in
      (f_3_c_1872))
    (f_3_c_1872)
  in
  let e_1875 = RSeq.new_ #i128 (len (f_3_c_1872)) in
  let (e_1875) =
    foldi (0ul) (len (e_1875)) (fun (i_1876, (e_1875)) ->
      let e_1875 =
        array_upd e_1875 (i_1876) (
          array_index (f_3_c_1872) (i_1876) % Int128.uint_to_t 3)
      in
      (e_1875))
    (e_1875)
  in
  let e_1875 = make_positive (e_1875) (Int128.uint_to_t 3) in
  let r_1877 =
    mul_poly_irr (e_1875) (key_v_1863) (irreducible_1867) (Int128.uint_to_t 3)
  in
  let (r_1877) =
    foldi (0ul) (len (r_1877)) (fun (i_1878, (r_1877)) ->
      let (r_1877) =
        if array_index (r_1877) (i_1878) == Int128.uint_to_t 2 then begin
          let r_1877 = array_upd r_1877 (i_1878) (- Int128.uint_to_t 1) in
          (r_1877)
        end else begin (r_1877)
        end
      in
      (r_1877))
    (r_1877)
  in
  (r_1877, ok_decrypt_1871)

