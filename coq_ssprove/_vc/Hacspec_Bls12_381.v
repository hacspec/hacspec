(** This file was automatically generated using Hacspec **)
Set Warnings "-notation-overridden,-ambiguous-paths".
From Crypt Require Import choice_type Package Prelude.
Import PackageNotation.
From extructures Require Import ord fset.
From mathcomp.word Require Import ssrZ word.
From Jasmin Require Import word.

From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope list_scope.
Open Scope Z_scope.
Open Scope bool_scope.

Require Import ChoiceEquality.
Require Import LocationUtility.
Require Import Hacspec_Lib_Comparable.
Require Import Hacspec_Lib_Pre.
Require Import Hacspec_Lib.

Open Scope hacspec_scope.

Obligation Tactic := try timeout 8 solve_ssprove_obligations.


Definition fp_canvas_t := nseq (int8) (usize 48).
Definition fp_t :=
  nat_mod 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab.

Definition serialized_fp_t := nseq (uint8) (usize 48).

Definition array_fp_t := nseq (uint64) (usize 6).

Definition scalar_canvas_t := nseq (int8) (usize 32).
Definition scalar_t :=
  nat_mod 0x8000000000000000000000000000000000000000000000000000000000000000.

Notation "'g1_t'" := ((fp_t '× fp_t '× bool_ChoiceEquality)) : hacspec_scope.

Notation "'fp2_t'" := ((fp_t '× fp_t)) : hacspec_scope.

Notation "'g2_t'" := ((fp2_t '× fp2_t '× bool_ChoiceEquality
)) : hacspec_scope.

Notation "'fp6_t'" := ((fp2_t '× fp2_t '× fp2_t)) : hacspec_scope.

Notation "'fp12_t'" := ((fp6_t '× fp6_t)) : hacspec_scope.


Notation "'fp2fromfp_inp'" :=(
  fp_t : choice_type) (in custom pack_type at level 2).
Notation "'fp2fromfp_inp'" :=(fp_t : ChoiceEquality) (at level 2).
Notation "'fp2fromfp_out'" :=(
  fp2_t : choice_type) (in custom pack_type at level 2).
Notation "'fp2fromfp_out'" :=(fp2_t : ChoiceEquality) (at level 2).
Definition FP2FROMFP : nat :=
  1821.
Program Definition fp2fromfp (n_1820 : fp_t)
  : both (fset.fset0) [interface] (fp2_t) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 n_1820,
          nat_mod_zero 
        ))
      ) : both (fset.fset0) [interface] (fp2_t)).
Fail Next Obligation.


Notation "'fp2zero_inp'" :=(
  unit_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'fp2zero_inp'" :=(unit_ChoiceEquality : ChoiceEquality) (at level 2).
Notation "'fp2zero_out'" :=(
  fp2_t : choice_type) (in custom pack_type at level 2).
Notation "'fp2zero_out'" :=(fp2_t : ChoiceEquality) (at level 2).
Definition FP2ZERO : nat :=
  1822.
Program Definition fp2zero  : both (fset.fset0) [interface] (fp2_t) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (fp2fromfp (nat_mod_zero ))
      ) : both (fset.fset0) [interface] (fp2_t)).
Fail Next Obligation.


Notation "'fp2neg_inp'" :=(
  fp2_t : choice_type) (in custom pack_type at level 2).
Notation "'fp2neg_inp'" :=(fp2_t : ChoiceEquality) (at level 2).
Notation "'fp2neg_out'" :=(
  fp2_t : choice_type) (in custom pack_type at level 2).
Notation "'fp2neg_out'" :=(fp2_t : ChoiceEquality) (at level 2).
Definition FP2NEG : nat :=
  1826.
Program Definition fp2neg (n_1823 : fp2_t)
  : both (fset.fset0) [interface] (fp2_t) :=
  ((letb '(n1_1824, n2_1825) : (fp_t '× fp_t) := lift_to_both0 n_1823 in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          (nat_mod_zero ) -% (lift_to_both0 n1_1824),
          (nat_mod_zero ) -% (lift_to_both0 n2_1825)
        ))
      ) : both (fset.fset0) [interface] (fp2_t)).
Fail Next Obligation.


Notation "'fp2add_inp'" :=(
  fp2_t '× fp2_t : choice_type) (in custom pack_type at level 2).
Notation "'fp2add_inp'" :=(fp2_t '× fp2_t : ChoiceEquality) (at level 2).
Notation "'fp2add_out'" :=(
  fp2_t : choice_type) (in custom pack_type at level 2).
Notation "'fp2add_out'" :=(fp2_t : ChoiceEquality) (at level 2).
Definition FP2ADD : nat :=
  1833.
Program Definition fp2add (n_1827 : fp2_t) (m_1830 : fp2_t)
  : both (fset.fset0) [interface] (fp2_t) :=
  ((letb '(n1_1828, n2_1829) : (fp_t '× fp_t) := lift_to_both0 n_1827 in
      letb '(m1_1831, m2_1832) : (fp_t '× fp_t) := lift_to_both0 m_1830 in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          (lift_to_both0 n1_1828) +% (lift_to_both0 m1_1831),
          (lift_to_both0 n2_1829) +% (lift_to_both0 m2_1832)
        ))
      ) : both (fset.fset0) [interface] (fp2_t)).
Fail Next Obligation.


Notation "'fp2sub_inp'" :=(
  fp2_t '× fp2_t : choice_type) (in custom pack_type at level 2).
Notation "'fp2sub_inp'" :=(fp2_t '× fp2_t : ChoiceEquality) (at level 2).
Notation "'fp2sub_out'" :=(
  fp2_t : choice_type) (in custom pack_type at level 2).
Notation "'fp2sub_out'" :=(fp2_t : ChoiceEquality) (at level 2).
Definition FP2SUB : nat :=
  1836.
Program Definition fp2sub (n_1834 : fp2_t) (m_1835 : fp2_t)
  : both (fset.fset0) [interface] (fp2_t) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (fp2add (
          lift_to_both0 n_1834) (fp2neg (lift_to_both0 m_1835)))
      ) : both (fset.fset0) [interface] (fp2_t)).
Fail Next Obligation.


Notation "'fp2mul_inp'" :=(
  fp2_t '× fp2_t : choice_type) (in custom pack_type at level 2).
Notation "'fp2mul_inp'" :=(fp2_t '× fp2_t : ChoiceEquality) (at level 2).
Notation "'fp2mul_out'" :=(
  fp2_t : choice_type) (in custom pack_type at level 2).
Notation "'fp2mul_out'" :=(fp2_t : ChoiceEquality) (at level 2).
Definition FP2MUL : nat :=
  1845.
Program Definition fp2mul (n_1837 : fp2_t) (m_1840 : fp2_t)
  : both (fset.fset0) [interface] (fp2_t) :=
  ((letb '(n1_1838, n2_1839) : (fp_t '× fp_t) := lift_to_both0 n_1837 in
      letb '(m1_1841, m2_1842) : (fp_t '× fp_t) := lift_to_both0 m_1840 in
      letb x1_1843 : fp_t :=
        ((lift_to_both0 n1_1838) *% (lift_to_both0 m1_1841)) -% ((
            lift_to_both0 n2_1839) *% (lift_to_both0 m2_1842)) in
      letb x2_1844 : fp_t :=
        ((lift_to_both0 n1_1838) *% (lift_to_both0 m2_1842)) +% ((
            lift_to_both0 n2_1839) *% (lift_to_both0 m1_1841)) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 x1_1843,
          lift_to_both0 x2_1844
        ))
      ) : both (fset.fset0) [interface] (fp2_t)).
Fail Next Obligation.


Notation "'fp2inv_inp'" :=(
  fp2_t : choice_type) (in custom pack_type at level 2).
Notation "'fp2inv_inp'" :=(fp2_t : ChoiceEquality) (at level 2).
Notation "'fp2inv_out'" :=(
  fp2_t : choice_type) (in custom pack_type at level 2).
Notation "'fp2inv_out'" :=(fp2_t : ChoiceEquality) (at level 2).
Definition FP2INV : nat :=
  1853.
Program Definition fp2inv (n_1846 : fp2_t)
  : both (fset.fset0) [interface] (fp2_t) :=
  ((letb '(n1_1847, n2_1848) : (fp_t '× fp_t) := lift_to_both0 n_1846 in
      letb t0_1849 : fp_t :=
        ((lift_to_both0 n1_1847) *% (lift_to_both0 n1_1847)) +% ((
            lift_to_both0 n2_1848) *% (lift_to_both0 n2_1848)) in
      letb t1_1850 : fp_t := nat_mod_inv (lift_to_both0 t0_1849) in
      letb x1_1851 : fp_t :=
        (lift_to_both0 n1_1847) *% (lift_to_both0 t1_1850) in
      letb x2_1852 : fp_t :=
        (nat_mod_zero ) -% ((lift_to_both0 n2_1848) *% (
            lift_to_both0 t1_1850)) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 x1_1851,
          lift_to_both0 x2_1852
        ))
      ) : both (fset.fset0) [interface] (fp2_t)).
Fail Next Obligation.


Notation "'fp2conjugate_inp'" :=(
  fp2_t : choice_type) (in custom pack_type at level 2).
Notation "'fp2conjugate_inp'" :=(fp2_t : ChoiceEquality) (at level 2).
Notation "'fp2conjugate_out'" :=(
  fp2_t : choice_type) (in custom pack_type at level 2).
Notation "'fp2conjugate_out'" :=(fp2_t : ChoiceEquality) (at level 2).
Definition FP2CONJUGATE : nat :=
  1857.
Program Definition fp2conjugate (n_1854 : fp2_t)
  : both (fset.fset0) [interface] (fp2_t) :=
  ((letb '(n1_1855, n2_1856) : (fp_t '× fp_t) := lift_to_both0 n_1854 in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 n1_1855,
          (nat_mod_zero ) -% (lift_to_both0 n2_1856)
        ))
      ) : both (fset.fset0) [interface] (fp2_t)).
Fail Next Obligation.


Notation "'fp6fromfp2_inp'" :=(
  fp2_t : choice_type) (in custom pack_type at level 2).
Notation "'fp6fromfp2_inp'" :=(fp2_t : ChoiceEquality) (at level 2).
Notation "'fp6fromfp2_out'" :=(
  fp6_t : choice_type) (in custom pack_type at level 2).
Notation "'fp6fromfp2_out'" :=(fp6_t : ChoiceEquality) (at level 2).
Definition FP6FROMFP2 : nat :=
  1859.
Program Definition fp6fromfp2 (n_1858 : fp2_t)
  : both (fset.fset0) [interface] (fp6_t) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 n_1858,
          fp2zero ,
          fp2zero 
        ))
      ) : both (fset.fset0) [interface] (fp6_t)).
Fail Next Obligation.


Notation "'fp6zero_inp'" :=(
  unit_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'fp6zero_inp'" :=(unit_ChoiceEquality : ChoiceEquality) (at level 2).
Notation "'fp6zero_out'" :=(
  fp6_t : choice_type) (in custom pack_type at level 2).
Notation "'fp6zero_out'" :=(fp6_t : ChoiceEquality) (at level 2).
Definition FP6ZERO : nat :=
  1860.
Program Definition fp6zero  : both (fset.fset0) [interface] (fp6_t) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (fp6fromfp2 (fp2zero ))
      ) : both (fset.fset0) [interface] (fp6_t)).
Fail Next Obligation.


Notation "'fp6neg_inp'" :=(
  fp6_t : choice_type) (in custom pack_type at level 2).
Notation "'fp6neg_inp'" :=(fp6_t : ChoiceEquality) (at level 2).
Notation "'fp6neg_out'" :=(
  fp6_t : choice_type) (in custom pack_type at level 2).
Notation "'fp6neg_out'" :=(fp6_t : ChoiceEquality) (at level 2).
Definition FP6NEG : nat :=
  1865.
Program Definition fp6neg (n_1861 : fp6_t)
  : both (fset.fset0) [interface] (fp6_t) :=
  ((letb '(n1_1862, n2_1863, n3_1864) : (fp2_t '× fp2_t '× fp2_t) :=
        lift_to_both0 n_1861 in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          fp2sub (fp2zero ) (lift_to_both0 n1_1862),
          fp2sub (fp2zero ) (lift_to_both0 n2_1863),
          fp2sub (fp2zero ) (lift_to_both0 n3_1864)
        ))
      ) : both (fset.fset0) [interface] (fp6_t)).
Fail Next Obligation.


Notation "'fp6add_inp'" :=(
  fp6_t '× fp6_t : choice_type) (in custom pack_type at level 2).
Notation "'fp6add_inp'" :=(fp6_t '× fp6_t : ChoiceEquality) (at level 2).
Notation "'fp6add_out'" :=(
  fp6_t : choice_type) (in custom pack_type at level 2).
Notation "'fp6add_out'" :=(fp6_t : ChoiceEquality) (at level 2).
Definition FP6ADD : nat :=
  1874.
Program Definition fp6add (n_1866 : fp6_t) (m_1870 : fp6_t)
  : both (fset.fset0) [interface] (fp6_t) :=
  ((letb '(n1_1867, n2_1868, n3_1869) : (fp2_t '× fp2_t '× fp2_t) :=
        lift_to_both0 n_1866 in
      letb '(m1_1871, m2_1872, m3_1873) : (fp2_t '× fp2_t '× fp2_t) :=
        lift_to_both0 m_1870 in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          fp2add (lift_to_both0 n1_1867) (lift_to_both0 m1_1871),
          fp2add (lift_to_both0 n2_1868) (lift_to_both0 m2_1872),
          fp2add (lift_to_both0 n3_1869) (lift_to_both0 m3_1873)
        ))
      ) : both (fset.fset0) [interface] (fp6_t)).
Fail Next Obligation.


Notation "'fp6sub_inp'" :=(
  fp6_t '× fp6_t : choice_type) (in custom pack_type at level 2).
Notation "'fp6sub_inp'" :=(fp6_t '× fp6_t : ChoiceEquality) (at level 2).
Notation "'fp6sub_out'" :=(
  fp6_t : choice_type) (in custom pack_type at level 2).
Notation "'fp6sub_out'" :=(fp6_t : ChoiceEquality) (at level 2).
Definition FP6SUB : nat :=
  1877.
Program Definition fp6sub (n_1875 : fp6_t) (m_1876 : fp6_t)
  : both (fset.fset0) [interface] (fp6_t) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (fp6add (
          lift_to_both0 n_1875) (fp6neg (lift_to_both0 m_1876)))
      ) : both (fset.fset0) [interface] (fp6_t)).
Fail Next Obligation.


Notation "'fp6mul_inp'" :=(
  fp6_t '× fp6_t : choice_type) (in custom pack_type at level 2).
Notation "'fp6mul_inp'" :=(fp6_t '× fp6_t : ChoiceEquality) (at level 2).
Notation "'fp6mul_out'" :=(
  fp6_t : choice_type) (in custom pack_type at level 2).
Notation "'fp6mul_out'" :=(fp6_t : ChoiceEquality) (at level 2).
Definition FP6MUL : nat :=
  1899.
Program Definition fp6mul (n_1878 : fp6_t) (m_1882 : fp6_t)
  : both (fset.fset0) [interface] (fp6_t) :=
  ((letb '(n1_1879, n2_1880, n3_1881) : (fp2_t '× fp2_t '× fp2_t) :=
        lift_to_both0 n_1878 in
      letb '(m1_1883, m2_1884, m3_1885) : (fp2_t '× fp2_t '× fp2_t) :=
        lift_to_both0 m_1882 in
      letb eps_1886 : (fp_t '× fp_t) := prod_b(nat_mod_one , nat_mod_one ) in
      letb t1_1887 : (fp_t '× fp_t) :=
        fp2mul (lift_to_both0 n1_1879) (lift_to_both0 m1_1883) in
      letb t2_1888 : (fp_t '× fp_t) :=
        fp2mul (lift_to_both0 n2_1880) (lift_to_both0 m2_1884) in
      letb t3_1889 : (fp_t '× fp_t) :=
        fp2mul (lift_to_both0 n3_1881) (lift_to_both0 m3_1885) in
      letb t4_1890 : (fp_t '× fp_t) :=
        fp2mul (fp2add (lift_to_both0 n2_1880) (lift_to_both0 n3_1881)) (
          fp2add (lift_to_both0 m2_1884) (lift_to_both0 m3_1885)) in
      letb t5_1891 : (fp_t '× fp_t) :=
        fp2sub (fp2sub (lift_to_both0 t4_1890) (lift_to_both0 t2_1888)) (
          lift_to_both0 t3_1889) in
      letb x_1892 : (fp_t '× fp_t) :=
        fp2add (fp2mul (lift_to_both0 t5_1891) (lift_to_both0 eps_1886)) (
          lift_to_both0 t1_1887) in
      letb t4_1893 : (fp_t '× fp_t) :=
        fp2mul (fp2add (lift_to_both0 n1_1879) (lift_to_both0 n2_1880)) (
          fp2add (lift_to_both0 m1_1883) (lift_to_both0 m2_1884)) in
      letb t5_1894 : (fp_t '× fp_t) :=
        fp2sub (fp2sub (lift_to_both0 t4_1893) (lift_to_both0 t1_1887)) (
          lift_to_both0 t2_1888) in
      letb y_1895 : (fp_t '× fp_t) :=
        fp2add (lift_to_both0 t5_1894) (fp2mul (lift_to_both0 eps_1886) (
            lift_to_both0 t3_1889)) in
      letb t4_1896 : (fp_t '× fp_t) :=
        fp2mul (fp2add (lift_to_both0 n1_1879) (lift_to_both0 n3_1881)) (
          fp2add (lift_to_both0 m1_1883) (lift_to_both0 m3_1885)) in
      letb t5_1897 : (fp_t '× fp_t) :=
        fp2sub (fp2sub (lift_to_both0 t4_1896) (lift_to_both0 t1_1887)) (
          lift_to_both0 t3_1889) in
      letb z_1898 : (fp_t '× fp_t) :=
        fp2add (lift_to_both0 t5_1897) (lift_to_both0 t2_1888) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 x_1892,
          lift_to_both0 y_1895,
          lift_to_both0 z_1898
        ))
      ) : both (fset.fset0) [interface] (fp6_t)).
Fail Next Obligation.


Notation "'fp6inv_inp'" :=(
  fp6_t : choice_type) (in custom pack_type at level 2).
Notation "'fp6inv_inp'" :=(fp6_t : ChoiceEquality) (at level 2).
Notation "'fp6inv_out'" :=(
  fp6_t : choice_type) (in custom pack_type at level 2).
Notation "'fp6inv_out'" :=(fp6_t : ChoiceEquality) (at level 2).
Definition FP6INV : nat :=
  1921.
Program Definition fp6inv (n_1900 : fp6_t)
  : both (fset.fset0) [interface] (fp6_t) :=
  ((letb '(n1_1901, n2_1902, n3_1903) : (fp2_t '× fp2_t '× fp2_t) :=
        lift_to_both0 n_1900 in
      letb eps_1904 : (fp_t '× fp_t) := prod_b(nat_mod_one , nat_mod_one ) in
      letb t1_1905 : (fp_t '× fp_t) :=
        fp2mul (lift_to_both0 n1_1901) (lift_to_both0 n1_1901) in
      letb t2_1906 : (fp_t '× fp_t) :=
        fp2mul (lift_to_both0 n2_1902) (lift_to_both0 n2_1902) in
      letb t3_1907 : (fp_t '× fp_t) :=
        fp2mul (lift_to_both0 n3_1903) (lift_to_both0 n3_1903) in
      letb t4_1908 : (fp_t '× fp_t) :=
        fp2mul (lift_to_both0 n1_1901) (lift_to_both0 n2_1902) in
      letb t5_1909 : (fp_t '× fp_t) :=
        fp2mul (lift_to_both0 n1_1901) (lift_to_both0 n3_1903) in
      letb t6_1910 : (fp_t '× fp_t) :=
        fp2mul (lift_to_both0 n2_1902) (lift_to_both0 n3_1903) in
      letb x0_1911 : (fp_t '× fp_t) :=
        fp2sub (lift_to_both0 t1_1905) (fp2mul (lift_to_both0 eps_1904) (
            lift_to_both0 t6_1910)) in
      letb y0_1912 : (fp_t '× fp_t) :=
        fp2sub (fp2mul (lift_to_both0 eps_1904) (lift_to_both0 t3_1907)) (
          lift_to_both0 t4_1908) in
      letb z0_1913 : (fp_t '× fp_t) :=
        fp2sub (lift_to_both0 t2_1906) (lift_to_both0 t5_1909) in
      letb t0_1914 : (fp_t '× fp_t) :=
        fp2mul (lift_to_both0 n1_1901) (lift_to_both0 x0_1911) in
      letb t0_1915 : (fp_t '× fp_t) :=
        fp2add (lift_to_both0 t0_1914) (fp2mul (lift_to_both0 eps_1904) (
            fp2mul (lift_to_both0 n3_1903) (lift_to_both0 y0_1912))) in
      letb t0_1916 : (fp_t '× fp_t) :=
        fp2add (lift_to_both0 t0_1915) (fp2mul (lift_to_both0 eps_1904) (
            fp2mul (lift_to_both0 n2_1902) (lift_to_both0 z0_1913))) in
      letb t0_1917 : (fp_t '× fp_t) := fp2inv (lift_to_both0 t0_1916) in
      letb x_1918 : (fp_t '× fp_t) :=
        fp2mul (lift_to_both0 x0_1911) (lift_to_both0 t0_1917) in
      letb y_1919 : (fp_t '× fp_t) :=
        fp2mul (lift_to_both0 y0_1912) (lift_to_both0 t0_1917) in
      letb z_1920 : (fp_t '× fp_t) :=
        fp2mul (lift_to_both0 z0_1913) (lift_to_both0 t0_1917) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 x_1918,
          lift_to_both0 y_1919,
          lift_to_both0 z_1920
        ))
      ) : both (fset.fset0) [interface] (fp6_t)).
Fail Next Obligation.


Notation "'fp12fromfp6_inp'" :=(
  fp6_t : choice_type) (in custom pack_type at level 2).
Notation "'fp12fromfp6_inp'" :=(fp6_t : ChoiceEquality) (at level 2).
Notation "'fp12fromfp6_out'" :=(
  fp12_t : choice_type) (in custom pack_type at level 2).
Notation "'fp12fromfp6_out'" :=(fp12_t : ChoiceEquality) (at level 2).
Definition FP12FROMFP6 : nat :=
  1923.
Program Definition fp12fromfp6 (n_1922 : fp6_t)
  : both (fset.fset0) [interface] (fp12_t) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 n_1922,
          fp6zero 
        ))
      ) : both (fset.fset0) [interface] (fp12_t)).
Fail Next Obligation.


Notation "'fp12neg_inp'" :=(
  fp12_t : choice_type) (in custom pack_type at level 2).
Notation "'fp12neg_inp'" :=(fp12_t : ChoiceEquality) (at level 2).
Notation "'fp12neg_out'" :=(
  fp12_t : choice_type) (in custom pack_type at level 2).
Notation "'fp12neg_out'" :=(fp12_t : ChoiceEquality) (at level 2).
Definition FP12NEG : nat :=
  1927.
Program Definition fp12neg (n_1924 : fp12_t)
  : both (fset.fset0) [interface] (fp12_t) :=
  ((letb '(n1_1925, n2_1926) : (fp6_t '× fp6_t) := lift_to_both0 n_1924 in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          fp6sub (fp6zero ) (lift_to_both0 n1_1925),
          fp6sub (fp6zero ) (lift_to_both0 n2_1926)
        ))
      ) : both (fset.fset0) [interface] (fp12_t)).
Fail Next Obligation.


Notation "'fp12add_inp'" :=(
  fp12_t '× fp12_t : choice_type) (in custom pack_type at level 2).
Notation "'fp12add_inp'" :=(fp12_t '× fp12_t : ChoiceEquality) (at level 2).
Notation "'fp12add_out'" :=(
  fp12_t : choice_type) (in custom pack_type at level 2).
Notation "'fp12add_out'" :=(fp12_t : ChoiceEquality) (at level 2).
Definition FP12ADD : nat :=
  1934.
Program Definition fp12add (n_1928 : fp12_t) (m_1931 : fp12_t)
  : both (fset.fset0) [interface] (fp12_t) :=
  ((letb '(n1_1929, n2_1930) : (fp6_t '× fp6_t) := lift_to_both0 n_1928 in
      letb '(m1_1932, m2_1933) : (fp6_t '× fp6_t) := lift_to_both0 m_1931 in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          fp6add (lift_to_both0 n1_1929) (lift_to_both0 m1_1932),
          fp6add (lift_to_both0 n2_1930) (lift_to_both0 m2_1933)
        ))
      ) : both (fset.fset0) [interface] (fp12_t)).
Fail Next Obligation.


Notation "'fp12sub_inp'" :=(
  fp12_t '× fp12_t : choice_type) (in custom pack_type at level 2).
Notation "'fp12sub_inp'" :=(fp12_t '× fp12_t : ChoiceEquality) (at level 2).
Notation "'fp12sub_out'" :=(
  fp12_t : choice_type) (in custom pack_type at level 2).
Notation "'fp12sub_out'" :=(fp12_t : ChoiceEquality) (at level 2).
Definition FP12SUB : nat :=
  1937.
Program Definition fp12sub (n_1935 : fp12_t) (m_1936 : fp12_t)
  : both (fset.fset0) [interface] (fp12_t) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (fp12add (
          lift_to_both0 n_1935) (fp12neg (lift_to_both0 m_1936)))
      ) : both (fset.fset0) [interface] (fp12_t)).
Fail Next Obligation.


Notation "'fp12mul_inp'" :=(
  fp12_t '× fp12_t : choice_type) (in custom pack_type at level 2).
Notation "'fp12mul_inp'" :=(fp12_t '× fp12_t : ChoiceEquality) (at level 2).
Notation "'fp12mul_out'" :=(
  fp12_t : choice_type) (in custom pack_type at level 2).
Notation "'fp12mul_out'" :=(fp12_t : ChoiceEquality) (at level 2).
Definition FP12MUL : nat :=
  1950.
Program Definition fp12mul (n_1938 : fp12_t) (m_1941 : fp12_t)
  : both (fset.fset0) [interface] (fp12_t) :=
  ((letb '(n1_1939, n2_1940) : (fp6_t '× fp6_t) := lift_to_both0 n_1938 in
      letb '(m1_1942, m2_1943) : (fp6_t '× fp6_t) := lift_to_both0 m_1941 in
      letb gamma_1944 : (fp2_t '× fp2_t '× fp2_t) :=
        prod_b(fp2zero , fp2fromfp (nat_mod_one ), fp2zero ) in
      letb t1_1945 : (fp2_t '× fp2_t '× fp2_t) :=
        fp6mul (lift_to_both0 n1_1939) (lift_to_both0 m1_1942) in
      letb t2_1946 : (fp2_t '× fp2_t '× fp2_t) :=
        fp6mul (lift_to_both0 n2_1940) (lift_to_both0 m2_1943) in
      letb x_1947 : (fp2_t '× fp2_t '× fp2_t) :=
        fp6add (lift_to_both0 t1_1945) (fp6mul (lift_to_both0 t2_1946) (
            lift_to_both0 gamma_1944)) in
      letb y_1948 : (fp2_t '× fp2_t '× fp2_t) :=
        fp6mul (fp6add (lift_to_both0 n1_1939) (lift_to_both0 n2_1940)) (
          fp6add (lift_to_both0 m1_1942) (lift_to_both0 m2_1943)) in
      letb y_1949 : (fp2_t '× fp2_t '× fp2_t) :=
        fp6sub (fp6sub (lift_to_both0 y_1948) (lift_to_both0 t1_1945)) (
          lift_to_both0 t2_1946) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 x_1947,
          lift_to_both0 y_1949
        ))
      ) : both (fset.fset0) [interface] (fp12_t)).
Fail Next Obligation.


Notation "'fp12inv_inp'" :=(
  fp12_t : choice_type) (in custom pack_type at level 2).
Notation "'fp12inv_inp'" :=(fp12_t : ChoiceEquality) (at level 2).
Notation "'fp12inv_out'" :=(
  fp12_t : choice_type) (in custom pack_type at level 2).
Notation "'fp12inv_out'" :=(fp12_t : ChoiceEquality) (at level 2).
Definition FP12INV : nat :=
  1961.
Program Definition fp12inv (n_1951 : fp12_t)
  : both (fset.fset0) [interface] (fp12_t) :=
  ((letb '(n1_1952, n2_1953) : (fp6_t '× fp6_t) := lift_to_both0 n_1951 in
      letb gamma_1954 : (fp2_t '× fp2_t '× fp2_t) :=
        prod_b(fp2zero , fp2fromfp (nat_mod_one ), fp2zero ) in
      letb t1_1955 : (fp2_t '× fp2_t '× fp2_t) :=
        fp6mul (lift_to_both0 n1_1952) (lift_to_both0 n1_1952) in
      letb t2_1956 : (fp2_t '× fp2_t '× fp2_t) :=
        fp6mul (lift_to_both0 n2_1953) (lift_to_both0 n2_1953) in
      letb t1_1957 : (fp2_t '× fp2_t '× fp2_t) :=
        fp6sub (lift_to_both0 t1_1955) (fp6mul (lift_to_both0 gamma_1954) (
            lift_to_both0 t2_1956)) in
      letb t2_1958 : (fp2_t '× fp2_t '× fp2_t) :=
        fp6inv (lift_to_both0 t1_1957) in
      letb x_1959 : (fp2_t '× fp2_t '× fp2_t) :=
        fp6mul (lift_to_both0 n1_1952) (lift_to_both0 t2_1958) in
      letb y_1960 : (fp2_t '× fp2_t '× fp2_t) :=
        fp6neg (fp6mul (lift_to_both0 n2_1953) (lift_to_both0 t2_1958)) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 x_1959,
          lift_to_both0 y_1960
        ))
      ) : both (fset.fset0) [interface] (fp12_t)).
Fail Next Obligation.

Definition c_1962_loc : ChoiceEqualityLocation :=
  ((fp6_t '× fp6_t) ; 1963%nat).
Notation "'fp12exp_inp'" :=(
  fp12_t '× scalar_t : choice_type) (in custom pack_type at level 2).
Notation "'fp12exp_inp'" :=(fp12_t '× scalar_t : ChoiceEquality) (at level 2).
Notation "'fp12exp_out'" :=(
  fp12_t : choice_type) (in custom pack_type at level 2).
Notation "'fp12exp_out'" :=(fp12_t : ChoiceEquality) (at level 2).
Definition FP12EXP : nat :=
  1967.
Program Definition fp12exp (n_1966 : fp12_t) (k_1965 : scalar_t)
  : both (CEfset ([c_1962_loc])) [interface] (fp12_t) :=
  ((letbm c_1962 : (fp6_t '× fp6_t) loc( c_1962_loc ) :=
        fp12fromfp6 (fp6fromfp2 (fp2fromfp (nat_mod_one ))) in
      letb c_1962 :=
        foldi_both' (lift_to_both0 (usize 0)) (lift_to_both0 (
              usize 256)) c_1962 (L := (CEfset ([c_1962_loc]))) (
            I := [interface]) (fun i_1964 c_1962 =>
            letbm c_1962 loc( c_1962_loc ) :=
              fp12mul (lift_to_both0 c_1962) (lift_to_both0 c_1962) in
            letb '(c_1962) :=
              if nat_mod_bit (lift_to_both0 k_1965) ((lift_to_both0 (
                    usize 255)) .- (lift_to_both0 i_1964)) :bool_ChoiceEquality
              then lift_scope (L1 := CEfset ([c_1962_loc])) (L2 := CEfset (
                  [c_1962_loc])) (I1 := [interface]) (
                I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
                letbm c_1962 loc( c_1962_loc ) :=
                  fp12mul (lift_to_both0 c_1962) (lift_to_both0 n_1966) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                  lift_to_both0 c_1962)
                )
              else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                lift_to_both0 c_1962)
               in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 c_1962)
            ) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 c_1962)
      ) : both (CEfset ([c_1962_loc])) [interface] (fp12_t)).
Fail Next Obligation.


Notation "'fp12conjugate_inp'" :=(
  fp12_t : choice_type) (in custom pack_type at level 2).
Notation "'fp12conjugate_inp'" :=(fp12_t : ChoiceEquality) (at level 2).
Notation "'fp12conjugate_out'" :=(
  fp12_t : choice_type) (in custom pack_type at level 2).
Notation "'fp12conjugate_out'" :=(fp12_t : ChoiceEquality) (at level 2).
Definition FP12CONJUGATE : nat :=
  1971.
Program Definition fp12conjugate (n_1968 : fp12_t)
  : both (fset.fset0) [interface] (fp12_t) :=
  ((letb '(n1_1969, n2_1970) : (fp6_t '× fp6_t) := lift_to_both0 n_1968 in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 n1_1969,
          fp6neg (lift_to_both0 n2_1970)
        ))
      ) : both (fset.fset0) [interface] (fp12_t)).
Fail Next Obligation.


Notation "'fp12zero_inp'" :=(
  unit_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'fp12zero_inp'" :=(unit_ChoiceEquality : ChoiceEquality) (at level 2).
Notation "'fp12zero_out'" :=(
  fp12_t : choice_type) (in custom pack_type at level 2).
Notation "'fp12zero_out'" :=(fp12_t : ChoiceEquality) (at level 2).
Definition FP12ZERO : nat :=
  1972.
Program Definition fp12zero  : both (fset.fset0) [interface] (fp12_t) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (fp12fromfp6 (fp6zero ))
      ) : both (fset.fset0) [interface] (fp12_t)).
Fail Next Obligation.


Notation "'g1add_a_inp'" :=(
  g1_t '× g1_t : choice_type) (in custom pack_type at level 2).
Notation "'g1add_a_inp'" :=(g1_t '× g1_t : ChoiceEquality) (at level 2).
Notation "'g1add_a_out'" :=(
  g1_t : choice_type) (in custom pack_type at level 2).
Notation "'g1add_a_out'" :=(g1_t : ChoiceEquality) (at level 2).
Definition G1ADD_A : nat :=
  1984.
Program Definition g1add_a (p_1973 : g1_t) (q_1976 : g1_t)
  : both (fset.fset0) [interface] (g1_t) :=
  ((letb '(x1_1974, y1_1975, _) : (fp_t '× fp_t '× bool_ChoiceEquality) :=
        lift_to_both0 p_1973 in
      letb '(x2_1977, y2_1978, _) : (fp_t '× fp_t '× bool_ChoiceEquality) :=
        lift_to_both0 q_1976 in
      letb x_diff_1979 : fp_t :=
        (lift_to_both0 x2_1977) -% (lift_to_both0 x1_1974) in
      letb y_diff_1980 : fp_t :=
        (lift_to_both0 y2_1978) -% (lift_to_both0 y1_1975) in
      letb xovery_1981 : fp_t :=
        (lift_to_both0 y_diff_1980) *% (nat_mod_inv (
            lift_to_both0 x_diff_1979)) in
      letb x3_1982 : fp_t :=
        ((nat_mod_exp (lift_to_both0 xovery_1981) (lift_to_both0 (
                @repr U32 2))) -% (lift_to_both0 x1_1974)) -% (
          lift_to_both0 x2_1977) in
      letb y3_1983 : fp_t :=
        ((lift_to_both0 xovery_1981) *% ((lift_to_both0 x1_1974) -% (
              lift_to_both0 x3_1982))) -% (lift_to_both0 y1_1975) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 x3_1982,
          lift_to_both0 y3_1983,
          lift_to_both0 ((false : bool_ChoiceEquality))
        ))
      ) : both (fset.fset0) [interface] (g1_t)).
Fail Next Obligation.


Notation "'g1double_a_inp'" :=(
  g1_t : choice_type) (in custom pack_type at level 2).
Notation "'g1double_a_inp'" :=(g1_t : ChoiceEquality) (at level 2).
Notation "'g1double_a_out'" :=(
  g1_t : choice_type) (in custom pack_type at level 2).
Notation "'g1double_a_out'" :=(g1_t : ChoiceEquality) (at level 2).
Definition G1DOUBLE_A : nat :=
  1992.
Program Definition g1double_a (p_1985 : g1_t)
  : both (fset.fset0) [interface] (g1_t) :=
  ((letb '(x1_1986, y1_1987, _) : (fp_t '× fp_t '× bool_ChoiceEquality) :=
        lift_to_both0 p_1985 in
      letb x12_1988 : fp_t :=
        nat_mod_exp (lift_to_both0 x1_1986) (lift_to_both0 (@repr U32 2)) in
      letb xovery_1989 : fp_t :=
        ((nat_mod_from_literal (
              0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab) (
              lift_to_both0 (@repr U128 3))) *% (lift_to_both0 x12_1988)) *% (
          nat_mod_inv ((nat_mod_two ) *% (lift_to_both0 y1_1987))) in
      letb x3_1990 : fp_t :=
        (nat_mod_exp (lift_to_both0 xovery_1989) (lift_to_both0 (
              @repr U32 2))) -% ((nat_mod_two ) *% (lift_to_both0 x1_1986)) in
      letb y3_1991 : fp_t :=
        ((lift_to_both0 xovery_1989) *% ((lift_to_both0 x1_1986) -% (
              lift_to_both0 x3_1990))) -% (lift_to_both0 y1_1987) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 x3_1990,
          lift_to_both0 y3_1991,
          lift_to_both0 ((false : bool_ChoiceEquality))
        ))
      ) : both (fset.fset0) [interface] (g1_t)).
Fail Next Obligation.


Notation "'g1double_inp'" :=(
  g1_t : choice_type) (in custom pack_type at level 2).
Notation "'g1double_inp'" :=(g1_t : ChoiceEquality) (at level 2).
Notation "'g1double_out'" :=(
  g1_t : choice_type) (in custom pack_type at level 2).
Notation "'g1double_out'" :=(g1_t : ChoiceEquality) (at level 2).
Definition G1DOUBLE : nat :=
  1997.
Program Definition g1double (p_1993 : g1_t)
  : both (fset.fset0) [interface] (g1_t) :=
  ((letb '(x1_1994, y1_1995, inf1_1996) : (fp_t '× fp_t '× bool_ChoiceEquality
        ) :=
        lift_to_both0 p_1993 in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        if is_pure (I := [interface]) (((lift_to_both0 y1_1995) !=.? (
              nat_mod_zero )) && (negb (lift_to_both0 inf1_1996)))
        then g1double_a (lift_to_both0 p_1993)
        else prod_b(
          nat_mod_zero ,
          nat_mod_zero ,
          lift_to_both0 ((true : bool_ChoiceEquality))
        ))
      ) : both (fset.fset0) [interface] (g1_t)).
Fail Next Obligation.


Notation "'g1add_inp'" :=(
  g1_t '× g1_t : choice_type) (in custom pack_type at level 2).
Notation "'g1add_inp'" :=(g1_t '× g1_t : ChoiceEquality) (at level 2).
Notation "'g1add_out'" :=(g1_t : choice_type) (in custom pack_type at level 2).
Notation "'g1add_out'" :=(g1_t : ChoiceEquality) (at level 2).
Definition G1ADD : nat :=
  2006.
Program Definition g1add (p_1998 : g1_t) (q_2002 : g1_t)
  : both (fset.fset0) [interface] (g1_t) :=
  ((letb '(x1_1999, y1_2000, inf1_2001) : (fp_t '× fp_t '× bool_ChoiceEquality
        ) :=
        lift_to_both0 p_1998 in
      letb '(x2_2003, y2_2004, inf2_2005) : (
          fp_t '×
          fp_t '×
          bool_ChoiceEquality
        ) :=
        lift_to_both0 q_2002 in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        if is_pure (I := [interface]) (lift_to_both0 inf1_2001)
        then lift_to_both0 q_2002
        else if is_pure (I := [interface]) (lift_to_both0 inf2_2005)
        then lift_to_both0 p_1998
        else if is_pure (I := [interface]) ((lift_to_both0 p_1998) =.? (
            lift_to_both0 q_2002))
        then g1double (lift_to_both0 p_1998)
        else if is_pure (I := [interface]) (negb (((lift_to_both0 x1_1999) =.? (
                lift_to_both0 x2_2003)) && ((lift_to_both0 y1_2000) =.? ((
                  nat_mod_zero ) -% (lift_to_both0 y2_2004)))))
        then g1add_a (lift_to_both0 p_1998) (lift_to_both0 q_2002)
        else prod_b(
          nat_mod_zero ,
          nat_mod_zero ,
          lift_to_both0 ((true : bool_ChoiceEquality))
        ))
      ) : both (fset.fset0) [interface] (g1_t)).
Fail Next Obligation.

Definition t_2007_loc : ChoiceEqualityLocation :=
  ((fp_t '× fp_t '× bool_ChoiceEquality) ; 2008%nat).
Notation "'g1mul_inp'" :=(
  scalar_t '× g1_t : choice_type) (in custom pack_type at level 2).
Notation "'g1mul_inp'" :=(scalar_t '× g1_t : ChoiceEquality) (at level 2).
Notation "'g1mul_out'" :=(g1_t : choice_type) (in custom pack_type at level 2).
Notation "'g1mul_out'" :=(g1_t : ChoiceEquality) (at level 2).
Definition G1MUL : nat :=
  2012.
Program Definition g1mul (m_2010 : scalar_t) (p_2011 : g1_t)
  : both (CEfset ([t_2007_loc])) [interface] (g1_t) :=
  ((letbm t_2007 : (fp_t '× fp_t '× bool_ChoiceEquality) loc( t_2007_loc ) :=
        prod_b(
          nat_mod_zero ,
          nat_mod_zero ,
          lift_to_both0 ((true : bool_ChoiceEquality))
        ) in
      letb t_2007 :=
        foldi_both' (lift_to_both0 (usize 0)) (lift_to_both0 (
              usize 256)) t_2007 (L := (CEfset ([t_2007_loc]))) (
            I := [interface]) (fun i_2009 t_2007 =>
            letbm t_2007 loc( t_2007_loc ) := g1double (lift_to_both0 t_2007) in
            letb '(t_2007) :=
              if nat_mod_bit (lift_to_both0 m_2010) ((lift_to_both0 (
                    usize 255)) .- (lift_to_both0 i_2009)) :bool_ChoiceEquality
              then lift_scope (L1 := CEfset ([t_2007_loc])) (L2 := CEfset (
                  [t_2007_loc])) (I1 := [interface]) (
                I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
                letbm t_2007 loc( t_2007_loc ) :=
                  g1add (lift_to_both0 t_2007) (lift_to_both0 p_2011) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                  lift_to_both0 t_2007)
                )
              else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                lift_to_both0 t_2007)
               in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 t_2007)
            ) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 t_2007)
      ) : both (CEfset ([t_2007_loc])) [interface] (g1_t)).
Fail Next Obligation.


Notation "'g1neg_inp'" :=(g1_t : choice_type) (in custom pack_type at level 2).
Notation "'g1neg_inp'" :=(g1_t : ChoiceEquality) (at level 2).
Notation "'g1neg_out'" :=(g1_t : choice_type) (in custom pack_type at level 2).
Notation "'g1neg_out'" :=(g1_t : ChoiceEquality) (at level 2).
Definition G1NEG : nat :=
  2017.
Program Definition g1neg (p_2013 : g1_t)
  : both (fset.fset0) [interface] (g1_t) :=
  ((letb '(x_2014, y_2015, inf_2016) : (fp_t '× fp_t '× bool_ChoiceEquality
        ) :=
        lift_to_both0 p_2013 in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 x_2014,
          (nat_mod_zero ) -% (lift_to_both0 y_2015),
          lift_to_both0 inf_2016
        ))
      ) : both (fset.fset0) [interface] (g1_t)).
Fail Next Obligation.


Notation "'g2add_a_inp'" :=(
  g2_t '× g2_t : choice_type) (in custom pack_type at level 2).
Notation "'g2add_a_inp'" :=(g2_t '× g2_t : ChoiceEquality) (at level 2).
Notation "'g2add_a_out'" :=(
  g2_t : choice_type) (in custom pack_type at level 2).
Notation "'g2add_a_out'" :=(g2_t : ChoiceEquality) (at level 2).
Definition G2ADD_A : nat :=
  2033.
Program Definition g2add_a (p_2018 : g2_t) (q_2021 : g2_t)
  : both (fset.fset0) [interface] (g2_t) :=
  ((letb '(x1_2019, y1_2020, _) : (fp2_t '× fp2_t '× bool_ChoiceEquality) :=
        lift_to_both0 p_2018 in
      letb '(x2_2022, y2_2023, _) : (fp2_t '× fp2_t '× bool_ChoiceEquality) :=
        lift_to_both0 q_2021 in
      letb x_diff_2024 : (fp_t '× fp_t) :=
        fp2sub (lift_to_both0 x2_2022) (lift_to_both0 x1_2019) in
      letb y_diff_2025 : (fp_t '× fp_t) :=
        fp2sub (lift_to_both0 y2_2023) (lift_to_both0 y1_2020) in
      letb xovery_2026 : (fp_t '× fp_t) :=
        fp2mul (lift_to_both0 y_diff_2025) (fp2inv (
            lift_to_both0 x_diff_2024)) in
      letb t1_2027 : (fp_t '× fp_t) :=
        fp2mul (lift_to_both0 xovery_2026) (lift_to_both0 xovery_2026) in
      letb t2_2028 : (fp_t '× fp_t) :=
        fp2sub (lift_to_both0 t1_2027) (lift_to_both0 x1_2019) in
      letb x3_2029 : (fp_t '× fp_t) :=
        fp2sub (lift_to_both0 t2_2028) (lift_to_both0 x2_2022) in
      letb t1_2030 : (fp_t '× fp_t) :=
        fp2sub (lift_to_both0 x1_2019) (lift_to_both0 x3_2029) in
      letb t2_2031 : (fp_t '× fp_t) :=
        fp2mul (lift_to_both0 xovery_2026) (lift_to_both0 t1_2030) in
      letb y3_2032 : (fp_t '× fp_t) :=
        fp2sub (lift_to_both0 t2_2031) (lift_to_both0 y1_2020) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 x3_2029,
          lift_to_both0 y3_2032,
          lift_to_both0 ((false : bool_ChoiceEquality))
        ))
      ) : both (fset.fset0) [interface] (g2_t)).
Fail Next Obligation.


Notation "'g2double_a_inp'" :=(
  g2_t : choice_type) (in custom pack_type at level 2).
Notation "'g2double_a_inp'" :=(g2_t : ChoiceEquality) (at level 2).
Notation "'g2double_a_out'" :=(
  g2_t : choice_type) (in custom pack_type at level 2).
Notation "'g2double_a_out'" :=(g2_t : ChoiceEquality) (at level 2).
Definition G2DOUBLE_A : nat :=
  2047.
Program Definition g2double_a (p_2034 : g2_t)
  : both (fset.fset0) [interface] (g2_t) :=
  ((letb '(x1_2035, y1_2036, _) : (fp2_t '× fp2_t '× bool_ChoiceEquality) :=
        lift_to_both0 p_2034 in
      letb x12_2037 : (fp_t '× fp_t) :=
        fp2mul (lift_to_both0 x1_2035) (lift_to_both0 x1_2035) in
      letb t1_2038 : (fp_t '× fp_t) :=
        fp2mul (fp2fromfp (nat_mod_from_literal (
              0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab) (
              lift_to_both0 (@repr U128 3)))) (lift_to_both0 x12_2037) in
      letb t2_2039 : (fp_t '× fp_t) :=
        fp2inv (fp2mul (fp2fromfp (nat_mod_two )) (lift_to_both0 y1_2036)) in
      letb xovery_2040 : (fp_t '× fp_t) :=
        fp2mul (lift_to_both0 t1_2038) (lift_to_both0 t2_2039) in
      letb t1_2041 : (fp_t '× fp_t) :=
        fp2mul (lift_to_both0 xovery_2040) (lift_to_both0 xovery_2040) in
      letb t2_2042 : (fp_t '× fp_t) :=
        fp2mul (fp2fromfp (nat_mod_two )) (lift_to_both0 x1_2035) in
      letb x3_2043 : (fp_t '× fp_t) :=
        fp2sub (lift_to_both0 t1_2041) (lift_to_both0 t2_2042) in
      letb t1_2044 : (fp_t '× fp_t) :=
        fp2sub (lift_to_both0 x1_2035) (lift_to_both0 x3_2043) in
      letb t2_2045 : (fp_t '× fp_t) :=
        fp2mul (lift_to_both0 xovery_2040) (lift_to_both0 t1_2044) in
      letb y3_2046 : (fp_t '× fp_t) :=
        fp2sub (lift_to_both0 t2_2045) (lift_to_both0 y1_2036) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 x3_2043,
          lift_to_both0 y3_2046,
          lift_to_both0 ((false : bool_ChoiceEquality))
        ))
      ) : both (fset.fset0) [interface] (g2_t)).
Fail Next Obligation.


Notation "'g2double_inp'" :=(
  g2_t : choice_type) (in custom pack_type at level 2).
Notation "'g2double_inp'" :=(g2_t : ChoiceEquality) (at level 2).
Notation "'g2double_out'" :=(
  g2_t : choice_type) (in custom pack_type at level 2).
Notation "'g2double_out'" :=(g2_t : ChoiceEquality) (at level 2).
Definition G2DOUBLE : nat :=
  2052.
Program Definition g2double (p_2048 : g2_t)
  : both (fset.fset0) [interface] (g2_t) :=
  ((letb '(x1_2049, y1_2050, inf1_2051) : (
          fp2_t '×
          fp2_t '×
          bool_ChoiceEquality
        ) :=
        lift_to_both0 p_2048 in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        if is_pure (I := [interface]) (((lift_to_both0 y1_2050) !=.? (
              fp2zero )) && (negb (lift_to_both0 inf1_2051)))
        then g2double_a (lift_to_both0 p_2048)
        else prod_b(
          fp2zero ,
          fp2zero ,
          lift_to_both0 ((true : bool_ChoiceEquality))
        ))
      ) : both (fset.fset0) [interface] (g2_t)).
Fail Next Obligation.


Notation "'g2add_inp'" :=(
  g2_t '× g2_t : choice_type) (in custom pack_type at level 2).
Notation "'g2add_inp'" :=(g2_t '× g2_t : ChoiceEquality) (at level 2).
Notation "'g2add_out'" :=(g2_t : choice_type) (in custom pack_type at level 2).
Notation "'g2add_out'" :=(g2_t : ChoiceEquality) (at level 2).
Definition G2ADD : nat :=
  2061.
Program Definition g2add (p_2053 : g2_t) (q_2057 : g2_t)
  : both (fset.fset0) [interface] (g2_t) :=
  ((letb '(x1_2054, y1_2055, inf1_2056) : (
          fp2_t '×
          fp2_t '×
          bool_ChoiceEquality
        ) :=
        lift_to_both0 p_2053 in
      letb '(x2_2058, y2_2059, inf2_2060) : (
          fp2_t '×
          fp2_t '×
          bool_ChoiceEquality
        ) :=
        lift_to_both0 q_2057 in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        if is_pure (I := [interface]) (lift_to_both0 inf1_2056)
        then lift_to_both0 q_2057
        else if is_pure (I := [interface]) (lift_to_both0 inf2_2060)
        then lift_to_both0 p_2053
        else if is_pure (I := [interface]) ((lift_to_both0 p_2053) =.? (
            lift_to_both0 q_2057))
        then g2double (lift_to_both0 p_2053)
        else if is_pure (I := [interface]) (negb (((lift_to_both0 x1_2054) =.? (
                lift_to_both0 x2_2058)) && ((lift_to_both0 y1_2055) =.? (
                fp2neg (lift_to_both0 y2_2059)))))
        then g2add_a (lift_to_both0 p_2053) (lift_to_both0 q_2057)
        else prod_b(
          fp2zero ,
          fp2zero ,
          lift_to_both0 ((true : bool_ChoiceEquality))
        ))
      ) : both (fset.fset0) [interface] (g2_t)).
Fail Next Obligation.

Definition t_2062_loc : ChoiceEqualityLocation :=
  ((fp2_t '× fp2_t '× bool_ChoiceEquality) ; 2063%nat).
Notation "'g2mul_inp'" :=(
  scalar_t '× g2_t : choice_type) (in custom pack_type at level 2).
Notation "'g2mul_inp'" :=(scalar_t '× g2_t : ChoiceEquality) (at level 2).
Notation "'g2mul_out'" :=(g2_t : choice_type) (in custom pack_type at level 2).
Notation "'g2mul_out'" :=(g2_t : ChoiceEquality) (at level 2).
Definition G2MUL : nat :=
  2067.
Program Definition g2mul (m_2065 : scalar_t) (p_2066 : g2_t)
  : both (CEfset ([t_2062_loc])) [interface] (g2_t) :=
  ((letbm t_2062 : (fp2_t '× fp2_t '× bool_ChoiceEquality
        ) loc( t_2062_loc ) :=
        prod_b(fp2zero , fp2zero , lift_to_both0 ((true : bool_ChoiceEquality))
        ) in
      letb t_2062 :=
        foldi_both' (lift_to_both0 (usize 0)) (lift_to_both0 (
              usize 256)) t_2062 (L := (CEfset ([t_2062_loc]))) (
            I := [interface]) (fun i_2064 t_2062 =>
            letbm t_2062 loc( t_2062_loc ) := g2double (lift_to_both0 t_2062) in
            letb '(t_2062) :=
              if nat_mod_bit (lift_to_both0 m_2065) ((lift_to_both0 (
                    usize 255)) .- (lift_to_both0 i_2064)) :bool_ChoiceEquality
              then lift_scope (L1 := CEfset ([t_2062_loc])) (L2 := CEfset (
                  [t_2062_loc])) (I1 := [interface]) (
                I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
                letbm t_2062 loc( t_2062_loc ) :=
                  g2add (lift_to_both0 t_2062) (lift_to_both0 p_2066) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                  lift_to_both0 t_2062)
                )
              else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                lift_to_both0 t_2062)
               in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 t_2062)
            ) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 t_2062)
      ) : both (CEfset ([t_2062_loc])) [interface] (g2_t)).
Fail Next Obligation.


Notation "'g2neg_inp'" :=(g2_t : choice_type) (in custom pack_type at level 2).
Notation "'g2neg_inp'" :=(g2_t : ChoiceEquality) (at level 2).
Notation "'g2neg_out'" :=(g2_t : choice_type) (in custom pack_type at level 2).
Notation "'g2neg_out'" :=(g2_t : ChoiceEquality) (at level 2).
Definition G2NEG : nat :=
  2072.
Program Definition g2neg (p_2068 : g2_t)
  : both (fset.fset0) [interface] (g2_t) :=
  ((letb '(x_2069, y_2070, inf_2071) : (fp2_t '× fp2_t '× bool_ChoiceEquality
        ) :=
        lift_to_both0 p_2068 in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 x_2069,
          fp2neg (lift_to_both0 y_2070),
          lift_to_both0 inf_2071
        ))
      ) : both (fset.fset0) [interface] (g2_t)).
Fail Next Obligation.


Notation "'twist_inp'" :=(g1_t : choice_type) (in custom pack_type at level 2).
Notation "'twist_inp'" :=(g1_t : ChoiceEquality) (at level 2).
Notation "'twist_out'" :=((fp12_t '× fp12_t
  ) : choice_type) (in custom pack_type at level 2).
Notation "'twist_out'" :=((fp12_t '× fp12_t) : ChoiceEquality) (at level 2).
Definition TWIST : nat :=
  2078.
Program Definition twist (p_2073 : g1_t)
  : both (fset.fset0) [interface] ((fp12_t '× fp12_t)) :=
  ((letb '(p0_2074, p1_2075, _) : (fp_t '× fp_t '× bool_ChoiceEquality) :=
        lift_to_both0 p_2073 in
      letb x_2076 : ((fp2_t '× fp2_t '× fp2_t) '× fp6_t) :=
        prod_b(
          prod_b(fp2zero , fp2fromfp (lift_to_both0 p0_2074), fp2zero ),
          fp6zero 
        ) in
      letb y_2077 : (fp6_t '× (fp2_t '× fp2_t '× fp2_t)) :=
        prod_b(
          fp6zero ,
          prod_b(fp2zero , fp2fromfp (lift_to_both0 p1_2075), fp2zero )
        ) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 x_2076,
          lift_to_both0 y_2077
        ))
      ) : both (fset.fset0) [interface] ((fp12_t '× fp12_t))).
Fail Next Obligation.


Notation "'line_double_p_inp'" :=(
  g2_t '× g1_t : choice_type) (in custom pack_type at level 2).
Notation "'line_double_p_inp'" :=(g2_t '× g1_t : ChoiceEquality) (at level 2).
Notation "'line_double_p_out'" :=(
  fp12_t : choice_type) (in custom pack_type at level 2).
Notation "'line_double_p_out'" :=(fp12_t : ChoiceEquality) (at level 2).
Definition LINE_DOUBLE_P : nat :=
  2090.
Program Definition line_double_p (r_2079 : g2_t) (p_2087 : g1_t)
  : both (fset.fset0) [interface] (fp12_t) :=
  ((letb '(r0_2080, r1_2081, _) : (fp2_t '× fp2_t '× bool_ChoiceEquality) :=
        lift_to_both0 r_2079 in
      letb a_2082 : (fp_t '× fp_t) :=
        fp2mul (fp2fromfp (nat_mod_from_literal (
              0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab) (
              lift_to_both0 (@repr U128 3)))) (fp2mul (lift_to_both0 r0_2080) (
            lift_to_both0 r0_2080)) in
      letb a_2083 : (fp_t '× fp_t) :=
        fp2mul (lift_to_both0 a_2082) (fp2inv (fp2mul (fp2fromfp (
                nat_mod_two )) (lift_to_both0 r1_2081))) in
      letb b_2084 : (fp_t '× fp_t) :=
        fp2sub (lift_to_both0 r1_2081) (fp2mul (lift_to_both0 a_2083) (
            lift_to_both0 r0_2080)) in
      letb a_2085 : (fp6_t '× fp6_t) :=
        fp12fromfp6 (fp6fromfp2 (lift_to_both0 a_2083)) in
      letb b_2086 : (fp6_t '× fp6_t) :=
        fp12fromfp6 (fp6fromfp2 (lift_to_both0 b_2084)) in
      letb '(x_2088, y_2089) : (fp12_t '× fp12_t) :=
        twist (lift_to_both0 p_2087) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (fp12neg (fp12sub (
            fp12sub (lift_to_both0 y_2089) (fp12mul (lift_to_both0 a_2085) (
                lift_to_both0 x_2088))) (lift_to_both0 b_2086)))
      ) : both (fset.fset0) [interface] (fp12_t)).
Fail Next Obligation.


Notation "'line_add_p_inp'" :=(
  g2_t '× g2_t '× g1_t : choice_type) (in custom pack_type at level 2).
Notation "'line_add_p_inp'" :=(
  g2_t '× g2_t '× g1_t : ChoiceEquality) (at level 2).
Notation "'line_add_p_out'" :=(
  fp12_t : choice_type) (in custom pack_type at level 2).
Notation "'line_add_p_out'" :=(fp12_t : ChoiceEquality) (at level 2).
Definition LINE_ADD_P : nat :=
  2104.
Program Definition line_add_p (r_2091 : g2_t) (q_2094 : g2_t) (p_2101 : g1_t)
  : both (fset.fset0) [interface] (fp12_t) :=
  ((letb '(r0_2092, r1_2093, _) : (fp2_t '× fp2_t '× bool_ChoiceEquality) :=
        lift_to_both0 r_2091 in
      letb '(q0_2095, q1_2096, _) : (fp2_t '× fp2_t '× bool_ChoiceEquality) :=
        lift_to_both0 q_2094 in
      letb a_2097 : (fp_t '× fp_t) :=
        fp2mul (fp2sub (lift_to_both0 q1_2096) (lift_to_both0 r1_2093)) (
          fp2inv (fp2sub (lift_to_both0 q0_2095) (lift_to_both0 r0_2092))) in
      letb b_2098 : (fp_t '× fp_t) :=
        fp2sub (lift_to_both0 r1_2093) (fp2mul (lift_to_both0 a_2097) (
            lift_to_both0 r0_2092)) in
      letb a_2099 : (fp6_t '× fp6_t) :=
        fp12fromfp6 (fp6fromfp2 (lift_to_both0 a_2097)) in
      letb b_2100 : (fp6_t '× fp6_t) :=
        fp12fromfp6 (fp6fromfp2 (lift_to_both0 b_2098)) in
      letb '(x_2102, y_2103) : (fp12_t '× fp12_t) :=
        twist (lift_to_both0 p_2101) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (fp12neg (fp12sub (
            fp12sub (lift_to_both0 y_2103) (fp12mul (lift_to_both0 a_2099) (
                lift_to_both0 x_2102))) (lift_to_both0 b_2100)))
      ) : both (fset.fset0) [interface] (fp12_t)).
Fail Next Obligation.


Notation "'frobenius_inp'" :=(
  fp12_t : choice_type) (in custom pack_type at level 2).
Notation "'frobenius_inp'" :=(fp12_t : ChoiceEquality) (at level 2).
Notation "'frobenius_out'" :=(
  fp12_t : choice_type) (in custom pack_type at level 2).
Notation "'frobenius_out'" :=(fp12_t : ChoiceEquality) (at level 2).
Definition FROBENIUS : nat :=
  2134.
Program Definition frobenius (f_2105 : fp12_t)
  : both (fset.fset0) [interface] (fp12_t) :=
  ((letb '((g0_2106, g1_2107, g2_2108), (h0_2109, h1_2110, h2_2111)) : (
          fp6_t '×
          fp6_t
        ) :=
        lift_to_both0 f_2105 in
      letb t1_2112 : (fp_t '× fp_t) := fp2conjugate (lift_to_both0 g0_2106) in
      letb t2_2113 : (fp_t '× fp_t) := fp2conjugate (lift_to_both0 h0_2109) in
      letb t3_2114 : (fp_t '× fp_t) := fp2conjugate (lift_to_both0 g1_2107) in
      letb t4_2115 : (fp_t '× fp_t) := fp2conjugate (lift_to_both0 h1_2110) in
      letb t5_2116 : (fp_t '× fp_t) := fp2conjugate (lift_to_both0 g2_2108) in
      letb t6_2117 : (fp_t '× fp_t) := fp2conjugate (lift_to_both0 h2_2111) in
      letb c1_2118 : array_fp_t :=
        @array_from_list uint64 ([
            (secret (lift_to_both0 (@repr U64 10162220747404304312))) : uint64;
            (secret (lift_to_both0 (@repr U64 17761815663483519293))) : uint64;
            (secret (lift_to_both0 (@repr U64 8873291758750579140))) : uint64;
            (secret (lift_to_both0 (@repr U64 1141103941765652303))) : uint64;
            (secret (lift_to_both0 (@repr U64 13993175198059990303))) : uint64;
            (secret (lift_to_both0 (@repr U64 1802798568193066599))) : uint64
          ]) in
      letb c1_2119 : seq uint8 := array_to_le_bytes (lift_to_both0 c1_2118) in
      letb c1_2120 : fp_t := nat_mod_from_byte_seq_le (lift_to_both0 c1_2119) in
      letb c2_2121 : array_fp_t :=
        @array_from_list uint64 ([
            (secret (lift_to_both0 (@repr U64 3240210268673559283))) : uint64;
            (secret (lift_to_both0 (@repr U64 2895069921743240898))) : uint64;
            (secret (lift_to_both0 (@repr U64 17009126888523054175))) : uint64;
            (secret (lift_to_both0 (@repr U64 6098234018649060207))) : uint64;
            (secret (lift_to_both0 (@repr U64 9865672654120263608))) : uint64;
            (secret (lift_to_both0 (@repr U64 71000049454473266))) : uint64
          ]) in
      letb c2_2122 : seq uint8 := array_to_le_bytes (lift_to_both0 c2_2121) in
      letb c2_2123 : fp_t := nat_mod_from_byte_seq_le (lift_to_both0 c2_2122) in
      letb gamma11_2124 : (fp_t '× fp_t) :=
        prod_b(lift_to_both0 c1_2120, lift_to_both0 c2_2123) in
      letb gamma12_2125 : (fp_t '× fp_t) :=
        fp2mul (lift_to_both0 gamma11_2124) (lift_to_both0 gamma11_2124) in
      letb gamma13_2126 : (fp_t '× fp_t) :=
        fp2mul (lift_to_both0 gamma12_2125) (lift_to_both0 gamma11_2124) in
      letb gamma14_2127 : (fp_t '× fp_t) :=
        fp2mul (lift_to_both0 gamma13_2126) (lift_to_both0 gamma11_2124) in
      letb gamma15_2128 : (fp_t '× fp_t) :=
        fp2mul (lift_to_both0 gamma14_2127) (lift_to_both0 gamma11_2124) in
      letb t2_2129 : (fp_t '× fp_t) :=
        fp2mul (lift_to_both0 t2_2113) (lift_to_both0 gamma11_2124) in
      letb t3_2130 : (fp_t '× fp_t) :=
        fp2mul (lift_to_both0 t3_2114) (lift_to_both0 gamma12_2125) in
      letb t4_2131 : (fp_t '× fp_t) :=
        fp2mul (lift_to_both0 t4_2115) (lift_to_both0 gamma13_2126) in
      letb t5_2132 : (fp_t '× fp_t) :=
        fp2mul (lift_to_both0 t5_2116) (lift_to_both0 gamma14_2127) in
      letb t6_2133 : (fp_t '× fp_t) :=
        fp2mul (lift_to_both0 t6_2117) (lift_to_both0 gamma15_2128) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          prod_b(
            lift_to_both0 t1_2112,
            lift_to_both0 t3_2130,
            lift_to_both0 t5_2132
          ),
          prod_b(
            lift_to_both0 t2_2129,
            lift_to_both0 t4_2131,
            lift_to_both0 t6_2133
          )
        ))
      ) : both (fset.fset0) [interface] (fp12_t)).
Fail Next Obligation.


Notation "'final_exponentiation_inp'" :=(
  fp12_t : choice_type) (in custom pack_type at level 2).
Notation "'final_exponentiation_inp'" :=(fp12_t : ChoiceEquality) (at level 2).
Notation "'final_exponentiation_out'" :=(
  fp12_t : choice_type) (in custom pack_type at level 2).
Notation "'final_exponentiation_out'" :=(fp12_t : ChoiceEquality) (at level 2).
Definition FINAL_EXPONENTIATION : nat :=
  2169.
Program Definition final_exponentiation (f_2135 : fp12_t)
  : both (CEfset ([c_1962_loc])) [interface] (fp12_t) :=
  ((letb fp6_2136 : (fp6_t '× fp6_t) := fp12conjugate (lift_to_both0 f_2135) in
      letb finv_2137 : (fp6_t '× fp6_t) := fp12inv (lift_to_both0 f_2135) in
      letb fp6_1_2138 : (fp6_t '× fp6_t) :=
        fp12mul (lift_to_both0 fp6_2136) (lift_to_both0 finv_2137) in
      letb fp8_2139 : (fp6_t '× fp6_t) :=
        frobenius (frobenius (lift_to_both0 fp6_1_2138)) in
      letb f_2140 : (fp6_t '× fp6_t) :=
        fp12mul (lift_to_both0 fp8_2139) (lift_to_both0 fp6_1_2138) in
      letb u_2141 : scalar_t :=
        nat_mod_from_literal (
          0x8000000000000000000000000000000000000000000000000000000000000000) (
          lift_to_both0 (@repr U128 15132376222941642752)) in
      letb u_half_2142 : scalar_t :=
        nat_mod_from_literal (
          0x8000000000000000000000000000000000000000000000000000000000000000) (
          lift_to_both0 (@repr U128 7566188111470821376)) in
      letb t0_2143 : (fp6_t '× fp6_t) :=
        fp12mul (lift_to_both0 f_2140) (lift_to_both0 f_2140) in
      letb t1_2144 : (fp6_t '× fp6_t) :=
        fp12exp (lift_to_both0 t0_2143) (lift_to_both0 u_2141) in
      letb t1_2145 : (fp6_t '× fp6_t) :=
        fp12conjugate (lift_to_both0 t1_2144) in
      letb t2_2146 : (fp6_t '× fp6_t) :=
        fp12exp (lift_to_both0 t1_2145) (lift_to_both0 u_half_2142) in
      letb t2_2147 : (fp6_t '× fp6_t) :=
        fp12conjugate (lift_to_both0 t2_2146) in
      letb t3_2148 : (fp6_t '× fp6_t) :=
        fp12conjugate (lift_to_both0 f_2140) in
      letb t1_2149 : (fp6_t '× fp6_t) :=
        fp12mul (lift_to_both0 t3_2148) (lift_to_both0 t1_2145) in
      letb t1_2150 : (fp6_t '× fp6_t) :=
        fp12conjugate (lift_to_both0 t1_2149) in
      letb t1_2151 : (fp6_t '× fp6_t) :=
        fp12mul (lift_to_both0 t1_2150) (lift_to_both0 t2_2147) in
      letb t2_2152 : (fp6_t '× fp6_t) :=
        fp12exp (lift_to_both0 t1_2151) (lift_to_both0 u_2141) in
      letb t2_2153 : (fp6_t '× fp6_t) :=
        fp12conjugate (lift_to_both0 t2_2152) in
      letb t3_2154 : (fp6_t '× fp6_t) :=
        fp12exp (lift_to_both0 t2_2153) (lift_to_both0 u_2141) in
      letb t3_2155 : (fp6_t '× fp6_t) :=
        fp12conjugate (lift_to_both0 t3_2154) in
      letb t1_2156 : (fp6_t '× fp6_t) :=
        fp12conjugate (lift_to_both0 t1_2151) in
      letb t3_2157 : (fp6_t '× fp6_t) :=
        fp12mul (lift_to_both0 t1_2156) (lift_to_both0 t3_2155) in
      letb t1_2158 : (fp6_t '× fp6_t) :=
        fp12conjugate (lift_to_both0 t1_2156) in
      letb t1_2159 : (fp6_t '× fp6_t) :=
        frobenius (frobenius (frobenius (lift_to_both0 t1_2158))) in
      letb t2_2160 : (fp6_t '× fp6_t) :=
        frobenius (frobenius (lift_to_both0 t2_2153)) in
      letb t1_2161 : (fp6_t '× fp6_t) :=
        fp12mul (lift_to_both0 t1_2159) (lift_to_both0 t2_2160) in
      letb t2_2162 : (fp6_t '× fp6_t) :=
        fp12exp (lift_to_both0 t3_2157) (lift_to_both0 u_2141) in
      letb t2_2163 : (fp6_t '× fp6_t) :=
        fp12conjugate (lift_to_both0 t2_2162) in
      letb t2_2164 : (fp6_t '× fp6_t) :=
        fp12mul (lift_to_both0 t2_2163) (lift_to_both0 t0_2143) in
      letb t2_2165 : (fp6_t '× fp6_t) :=
        fp12mul (lift_to_both0 t2_2164) (lift_to_both0 f_2140) in
      letb t1_2166 : (fp6_t '× fp6_t) :=
        fp12mul (lift_to_both0 t1_2161) (lift_to_both0 t2_2165) in
      letb t2_2167 : (fp6_t '× fp6_t) := frobenius (lift_to_both0 t3_2157) in
      letb t1_2168 : (fp6_t '× fp6_t) :=
        fp12mul (lift_to_both0 t1_2166) (lift_to_both0 t2_2167) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 t1_2168)
      ) : both (CEfset ([c_1962_loc])) [interface] (fp12_t)).
Fail Next Obligation.

Definition r_2170_loc : ChoiceEqualityLocation :=
  ((fp2_t '× fp2_t '× bool_ChoiceEquality) ; 2172%nat).
Definition f_2171_loc : ChoiceEqualityLocation :=
  ((fp6_t '× fp6_t) ; 2173%nat).
Notation "'pairing_inp'" :=(
  g1_t '× g2_t : choice_type) (in custom pack_type at level 2).
Notation "'pairing_inp'" :=(g1_t '× g2_t : ChoiceEquality) (at level 2).
Notation "'pairing_out'" :=(
  fp12_t : choice_type) (in custom pack_type at level 2).
Notation "'pairing_out'" :=(fp12_t : ChoiceEquality) (at level 2).
Definition PAIRING : nat :=
  2180.
Program Definition pairing (p_2177 : g1_t) (q_2175 : g2_t)
  : both (CEfset ([c_1962_loc ; r_2170_loc ; f_2171_loc])) [interface] (
    fp12_t) :=
  ((letb t_2174 : scalar_t :=
        nat_mod_from_literal (
          0x8000000000000000000000000000000000000000000000000000000000000000) (
          lift_to_both0 (@repr U128 15132376222941642752)) in
      letbm r_2170 : (fp2_t '× fp2_t '× bool_ChoiceEquality
        ) loc( r_2170_loc ) :=
        lift_to_both0 q_2175 in
      letbm f_2171 : (fp6_t '× fp6_t) loc( f_2171_loc ) :=
        fp12fromfp6 (fp6fromfp2 (fp2fromfp (nat_mod_one ))) in
      letb '(r_2170, f_2171) :=
        foldi_both' (lift_to_both0 (usize 1)) (lift_to_both0 (
              usize 64)) prod_ce(r_2170, f_2171) (L := (CEfset (
                [c_1962_loc ; r_2170_loc ; f_2171_loc]))) (I := [interface]) (
            fun i_2176 '(r_2170, f_2171) =>
            letb lrr_2178 : (fp6_t '× fp6_t) :=
              line_double_p (lift_to_both0 r_2170) (lift_to_both0 p_2177) in
            letbm r_2170 loc( r_2170_loc ) := g2double (lift_to_both0 r_2170) in
            letbm f_2171 loc( f_2171_loc ) :=
              fp12mul (fp12mul (lift_to_both0 f_2171) (lift_to_both0 f_2171)) (
                lift_to_both0 lrr_2178) in
            letb '(r_2170, f_2171) :=
              if nat_mod_bit (lift_to_both0 t_2174) (((lift_to_both0 (
                      usize 64)) .- (lift_to_both0 i_2176)) .- (lift_to_both0 (
                    usize 1))) :bool_ChoiceEquality
              then lift_scope (L1 := CEfset ([r_2170_loc ; f_2171_loc])) (
                L2 := CEfset ([r_2170_loc ; f_2171_loc])) (I1 := [interface]) (
                I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
                letb lrq_2179 : (fp6_t '× fp6_t) :=
                  line_add_p (lift_to_both0 r_2170) (lift_to_both0 q_2175) (
                    lift_to_both0 p_2177) in
                letbm r_2170 loc( r_2170_loc ) :=
                  g2add (lift_to_both0 r_2170) (lift_to_both0 q_2175) in
                letbm f_2171 loc( f_2171_loc ) :=
                  fp12mul (lift_to_both0 f_2171) (lift_to_both0 lrq_2179) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                    lift_to_both0 r_2170,
                    lift_to_both0 f_2171
                  ))
                )
              else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                  lift_to_both0 r_2170,
                  lift_to_both0 f_2171
                ))
               in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                lift_to_both0 r_2170,
                lift_to_both0 f_2171
              ))
            ) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (final_exponentiation (
          fp12conjugate (lift_to_both0 f_2171)))
      ) : both (CEfset ([c_1962_loc ; r_2170_loc ; f_2171_loc])) [interface] (
      fp12_t)).
Fail Next Obligation.


Notation "'test_fp2_prop_add_neg_inp'" :=(
  fp2_t : choice_type) (in custom pack_type at level 2).
Notation "'test_fp2_prop_add_neg_inp'" :=(fp2_t : ChoiceEquality) (at level 2).
Notation "'test_fp2_prop_add_neg_out'" :=(
  bool_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'test_fp2_prop_add_neg_out'" :=(
  bool_ChoiceEquality : ChoiceEquality) (at level 2).
Definition TEST_FP2_PROP_ADD_NEG : nat :=
  2183.
Program Definition test_fp2_prop_add_neg (a_2181 : fp2_t)
  : both (fset.fset0) [interface] (bool_ChoiceEquality) :=
  ((letb b_2182 : (fp_t '× fp_t) := fp2neg (lift_to_both0 a_2181) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) ((fp2fromfp (
            nat_mod_zero )) =.? (fp2add (lift_to_both0 a_2181) (
            lift_to_both0 b_2182)))
      ) : both (fset.fset0) [interface] (bool_ChoiceEquality)).
Fail Next Obligation.


Notation "'test_fp2_prop_mul_inv_inp'" :=(
  fp2_t : choice_type) (in custom pack_type at level 2).
Notation "'test_fp2_prop_mul_inv_inp'" :=(fp2_t : ChoiceEquality) (at level 2).
Notation "'test_fp2_prop_mul_inv_out'" :=(
  bool_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'test_fp2_prop_mul_inv_out'" :=(
  bool_ChoiceEquality : ChoiceEquality) (at level 2).
Definition TEST_FP2_PROP_MUL_INV : nat :=
  2186.
Program Definition test_fp2_prop_mul_inv (a_2184 : fp2_t)
  : both (fset.fset0) [interface] (bool_ChoiceEquality) :=
  ((letb b_2185 : (fp_t '× fp_t) := fp2inv (lift_to_both0 a_2184) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) ((fp2fromfp (
            nat_mod_one )) =.? (fp2mul (lift_to_both0 a_2184) (
            lift_to_both0 b_2185)))
      ) : both (fset.fset0) [interface] (bool_ChoiceEquality)).
Fail Next Obligation.


Notation "'test_extraction_issue_inp'" :=(
  unit_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'test_extraction_issue_inp'" :=(
  unit_ChoiceEquality : ChoiceEquality) (at level 2).
Notation "'test_extraction_issue_out'" :=(
  bool_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'test_extraction_issue_out'" :=(
  bool_ChoiceEquality : ChoiceEquality) (at level 2).
Definition TEST_EXTRACTION_ISSUE : nat :=
  2188.
Program Definition test_extraction_issue 
  : both (fset.fset0) [interface] (bool_ChoiceEquality) :=
  ((letb b_2187 : (fp_t '× fp_t) :=
        fp2inv (prod_b(nat_mod_one , nat_mod_one )) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) ((fp2fromfp (
            nat_mod_one )) =.? (fp2mul (prod_b(nat_mod_one , nat_mod_one )) (
            lift_to_both0 b_2187)))
      ) : both (fset.fset0) [interface] (bool_ChoiceEquality)).
Fail Next Obligation.


Notation "'test_fp6_prop_mul_inv_inp'" :=(
  fp6_t : choice_type) (in custom pack_type at level 2).
Notation "'test_fp6_prop_mul_inv_inp'" :=(fp6_t : ChoiceEquality) (at level 2).
Notation "'test_fp6_prop_mul_inv_out'" :=(
  bool_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'test_fp6_prop_mul_inv_out'" :=(
  bool_ChoiceEquality : ChoiceEquality) (at level 2).
Definition TEST_FP6_PROP_MUL_INV : nat :=
  2191.
Program Definition test_fp6_prop_mul_inv (a_2189 : fp6_t)
  : both (fset.fset0) [interface] (bool_ChoiceEquality) :=
  ((letb b_2190 : (fp2_t '× fp2_t '× fp2_t) :=
        fp6inv (lift_to_both0 a_2189) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) ((fp6fromfp2 (fp2fromfp (
              nat_mod_one ))) =.? (fp6mul (lift_to_both0 a_2189) (
            lift_to_both0 b_2190)))
      ) : both (fset.fset0) [interface] (bool_ChoiceEquality)).
Fail Next Obligation.


Notation "'test_fp6_prop_add_neg_inp'" :=(
  fp6_t : choice_type) (in custom pack_type at level 2).
Notation "'test_fp6_prop_add_neg_inp'" :=(fp6_t : ChoiceEquality) (at level 2).
Notation "'test_fp6_prop_add_neg_out'" :=(
  bool_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'test_fp6_prop_add_neg_out'" :=(
  bool_ChoiceEquality : ChoiceEquality) (at level 2).
Definition TEST_FP6_PROP_ADD_NEG : nat :=
  2194.
Program Definition test_fp6_prop_add_neg (a_2192 : fp6_t)
  : both (fset.fset0) [interface] (bool_ChoiceEquality) :=
  ((letb b_2193 : (fp2_t '× fp2_t '× fp2_t) :=
        fp6neg (lift_to_both0 a_2192) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) ((fp6fromfp2 (fp2fromfp (
              nat_mod_zero ))) =.? (fp6add (lift_to_both0 a_2192) (
            lift_to_both0 b_2193)))
      ) : both (fset.fset0) [interface] (bool_ChoiceEquality)).
Fail Next Obligation.


Notation "'test_fp12_prop_add_neg_inp'" :=(
  fp12_t : choice_type) (in custom pack_type at level 2).
Notation "'test_fp12_prop_add_neg_inp'" :=(
  fp12_t : ChoiceEquality) (at level 2).
Notation "'test_fp12_prop_add_neg_out'" :=(
  bool_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'test_fp12_prop_add_neg_out'" :=(
  bool_ChoiceEquality : ChoiceEquality) (at level 2).
Definition TEST_FP12_PROP_ADD_NEG : nat :=
  2197.
Program Definition test_fp12_prop_add_neg (a_2195 : fp12_t)
  : both (fset.fset0) [interface] (bool_ChoiceEquality) :=
  ((letb b_2196 : (fp6_t '× fp6_t) := fp12neg (lift_to_both0 a_2195) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) ((fp12fromfp6 (
            fp6fromfp2 (fp2fromfp (nat_mod_zero )))) =.? (fp12add (
            lift_to_both0 a_2195) (lift_to_both0 b_2196)))
      ) : both (fset.fset0) [interface] (bool_ChoiceEquality)).
Fail Next Obligation.


Notation "'test_fp12_prop_mul_inv_inp'" :=(
  fp12_t : choice_type) (in custom pack_type at level 2).
Notation "'test_fp12_prop_mul_inv_inp'" :=(
  fp12_t : ChoiceEquality) (at level 2).
Notation "'test_fp12_prop_mul_inv_out'" :=(
  bool_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'test_fp12_prop_mul_inv_out'" :=(
  bool_ChoiceEquality : ChoiceEquality) (at level 2).
Definition TEST_FP12_PROP_MUL_INV : nat :=
  2200.
Program Definition test_fp12_prop_mul_inv (a_2198 : fp12_t)
  : both (fset.fset0) [interface] (bool_ChoiceEquality) :=
  ((letb b_2199 : (fp6_t '× fp6_t) := fp12inv (lift_to_both0 a_2198) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) ((fp12fromfp6 (
            fp6fromfp2 (fp2fromfp (nat_mod_one )))) =.? (fp12mul (
            lift_to_both0 a_2198) (lift_to_both0 b_2199)))
      ) : both (fset.fset0) [interface] (bool_ChoiceEquality)).
Fail Next Obligation.

