module Hacspec.NtruDemo

#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"

open Hacspec.Lib
open FStar.Mul

let build_irreducible (p_1836 : uint_size) : seq pub_int128 =
  let irr_1837 = seq_new_ (pub_i128 0x0) #pub_int128 ((p_1836) + (usize 1)) in
  let irr_1837 = array_upd irr_1837 (usize 0) (- (pub_i128 0x1)) in
  let irr_1837 = array_upd irr_1837 (usize 1) (- (pub_i128 0x1)) in
  let irr_1837 = array_upd irr_1837 (p_1836) (pub_i128 0x1) in
  irr_1837

let round_to_3
  (poly_1838 : seq pub_int128)
  (q_1839 : pub_int128)
  : seq pub_int128 =
  let result_1840 = seq_clone #pub_int128 (poly_1838) in
  let q_12_1841 = ((q_1839) -. (pub_i128 0x1)) /. (pub_i128 0x2) in
  let (result_1840) =
    foldi (usize 0) (seq_len #pub_int128 (poly_1838)) (fun (
        i_1842,
        (result_1840)
      ) ->
      let (result_1840) =
        if (array_index (poly_1838) (i_1842)) >. (q_12_1841) then begin
          let result_1840 =
            array_upd result_1840 (i_1842) (
              (array_index (poly_1838) (i_1842)) -. (q_1839))
          in
          (result_1840)
        end else begin (result_1840)
        end
      in
      (result_1840))
    (result_1840)
  in
  let (result_1840) =
    foldi (usize 0) (seq_len #pub_int128 (result_1840)) (fun (
        i_1843,
        (result_1840)
      ) ->
      let (result_1840) =
        if ((array_index (result_1840) (i_1843)) %. (pub_i128 0x3)) != (
          pub_i128 0x0) then begin
          let result_1840 =
            array_upd result_1840 (i_1843) (
              (array_index (result_1840) (i_1843)) -. (pub_i128 0x1))
          in
          let (result_1840) =
            if ((array_index (result_1840) (i_1843)) %. (pub_i128 0x3)) != (
              pub_i128 0x0) then begin
              let result_1840 =
                array_upd result_1840 (i_1843) (
                  (array_index (result_1840) (i_1843)) +. (pub_i128 0x2))
              in
              (result_1840)
            end else begin (result_1840)
            end
          in
          (result_1840)
        end else begin (result_1840)
        end
      in
      (result_1840))
    (result_1840)
  in
  result_1840

let encrypt
  (r_1844 : seq pub_int128)
  (h_1845 : seq pub_int128)
  (q_1846 : pub_int128)
  (irreducible_1847 : seq pub_int128)
  : seq pub_int128 =
  let pre_1848 = mul_poly_irr (r_1844) (h_1845) (irreducible_1847) (q_1846) in
  round_to_3 (pre_1848) (q_1846)

let ntru_prime_653_encrypt
  (r_1849 : seq pub_int128)
  (h_1850 : seq pub_int128)
  : seq pub_int128 =
  let p_1851 = usize 653 in
  let q_1852 = pub_i128 0x120d in
  let w_1853 = usize 288 in
  let irreducible_1854 = build_irreducible (p_1851) in
  encrypt (r_1849) (h_1850) (q_1852) (irreducible_1854)

let ntru_prime_653_decrypt
  (c_1855 : seq pub_int128)
  (key_f_1856 : seq pub_int128)
  (key_v_1857 : seq pub_int128)
  : (seq pub_int128 & bool) =
  let p_1858 = usize 653 in
  let q_1859 = pub_i128 0x120d in
  let w_1860 = usize 288 in
  let irreducible_1861 = build_irreducible (p_1858) in
  let f_c_1862 =
    mul_poly_irr (key_f_1856) (c_1855) (irreducible_1861) (q_1859)
  in
  let f_3_c_and_decryption_ok_1863 =
    poly_to_ring (irreducible_1861) (
      add_poly (f_c_1862) (add_poly (f_c_1862) (f_c_1862) (q_1859)) (q_1859)) (
      q_1859)
  in
  let (f_3_c_1864, ok_decrypt_1865) = f_3_c_and_decryption_ok_1863 in
  let f_3_c_1866 = f_3_c_1864 in
  let q_12_1867 = ((q_1859) -. (pub_i128 0x1)) /. (pub_i128 0x2) in
  let (f_3_c_1866) =
    foldi (usize 0) (seq_len #pub_int128 (f_3_c_1866)) (fun (
        i_1868,
        (f_3_c_1866)
      ) ->
      let (f_3_c_1866) =
        if (array_index (f_3_c_1866) (i_1868)) >. (q_12_1867) then begin
          let f_3_c_1866 =
            array_upd f_3_c_1866 (i_1868) (
              (array_index (f_3_c_1866) (i_1868)) -. (q_1859))
          in
          (f_3_c_1866)
        end else begin (f_3_c_1866)
        end
      in
      (f_3_c_1866))
    (f_3_c_1866)
  in
  let e_1869 =
    seq_new_ (pub_i128 0x0) #pub_int128 (seq_len #pub_int128 (f_3_c_1866))
  in
  let (e_1869) =
    foldi (usize 0) (seq_len #pub_int128 (e_1869)) (fun (i_1870, (e_1869)) ->
      let e_1869 =
        array_upd e_1869 (i_1870) (
          (array_index (f_3_c_1866) (i_1870)) %. (pub_i128 0x3))
      in
      (e_1869))
    (e_1869)
  in
  let e_1869 = make_positive (e_1869) (pub_i128 0x3) in
  let r_1871 =
    mul_poly_irr (e_1869) (key_v_1857) (irreducible_1861) (pub_i128 0x3)
  in
  let (r_1871) =
    foldi (usize 0) (seq_len #pub_int128 (r_1871)) (fun (i_1872, (r_1871)) ->
      let (r_1871) =
        if (array_index (r_1871) (i_1872)) == (pub_i128 0x2) then begin
          let r_1871 = array_upd r_1871 (i_1872) (- (pub_i128 0x1)) in
          (r_1871)
        end else begin (r_1871)
        end
      in
      (r_1871))
    (r_1871)
  in
  (r_1871, ok_decrypt_1865)

