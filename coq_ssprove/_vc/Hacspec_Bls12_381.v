(** This file was automatically generated using Hacspec **)
Set Warnings "-notation-overridden,-ambiguous-paths".
From Crypt Require Import choice_type Package Prelude.
Import PackageNotation.
From extructures Require Import ord fset.
From mathcomp Require Import ssrZ word.
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
  1701.
Program Definition fp2fromfp
  : both_package (fset.fset0) [interface] [(FP2FROMFP,(
      fp2fromfp_inp,fp2fromfp_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(n_1700) := temp_inp : fp_t in
    
    ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
            lift_to_both0 n_1700,
            nat_mod_zero 
          ))
        ) : both (fset.fset0) [interface] (fp2_t)))in
  both_package' _ _ (FP2FROMFP,(fp2fromfp_inp,fp2fromfp_out)) temp_package_both.
Fail Next Obligation.


Notation "'fp2zero_inp'" :=(
  unit_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'fp2zero_inp'" :=(unit_ChoiceEquality : ChoiceEquality) (at level 2).
Notation "'fp2zero_out'" :=(
  fp2_t : choice_type) (in custom pack_type at level 2).
Notation "'fp2zero_out'" :=(fp2_t : ChoiceEquality) (at level 2).
Definition FP2ZERO : nat :=
  1702.
Program Definition fp2zero
  : both_package (fset.fset0) [interface
  #val #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out ] [(FP2ZERO,(
      fp2zero_inp,fp2zero_out))] :=
  let temp_package_both := (fun temp_inp => 
    
    let fp2fromfp := fun x_0 => package_both fp2fromfp (x_0) in
    ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (fp2fromfp (
            nat_mod_zero ))
        ) : both (fset.fset0) [interface
      #val #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out ] (fp2_t)))in
  both_package' _ _ (FP2ZERO,(fp2zero_inp,fp2zero_out)) temp_package_both.
Fail Next Obligation.


Notation "'fp2neg_inp'" :=(
  fp2_t : choice_type) (in custom pack_type at level 2).
Notation "'fp2neg_inp'" :=(fp2_t : ChoiceEquality) (at level 2).
Notation "'fp2neg_out'" :=(
  fp2_t : choice_type) (in custom pack_type at level 2).
Notation "'fp2neg_out'" :=(fp2_t : ChoiceEquality) (at level 2).
Definition FP2NEG : nat :=
  1706.
Program Definition fp2neg
  : both_package (fset.fset0) [interface] [(FP2NEG,(fp2neg_inp,fp2neg_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(n_1703) := temp_inp : fp2_t in
    
    ((letb '(n1_1704, n2_1705) : (fp_t '× fp_t) := lift_to_both0 n_1703 in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
            (nat_mod_zero ) -% (lift_to_both0 n1_1704),
            (nat_mod_zero ) -% (lift_to_both0 n2_1705)
          ))
        ) : both (fset.fset0) [interface] (fp2_t)))in
  both_package' _ _ (FP2NEG,(fp2neg_inp,fp2neg_out)) temp_package_both.
Fail Next Obligation.


Notation "'fp2add_inp'" :=(
  fp2_t '× fp2_t : choice_type) (in custom pack_type at level 2).
Notation "'fp2add_inp'" :=(fp2_t '× fp2_t : ChoiceEquality) (at level 2).
Notation "'fp2add_out'" :=(
  fp2_t : choice_type) (in custom pack_type at level 2).
Notation "'fp2add_out'" :=(fp2_t : ChoiceEquality) (at level 2).
Definition FP2ADD : nat :=
  1713.
Program Definition fp2add
  : both_package (fset.fset0) [interface] [(FP2ADD,(fp2add_inp,fp2add_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(n_1707 , m_1710) := temp_inp : fp2_t '× fp2_t in
    
    ((letb '(n1_1708, n2_1709) : (fp_t '× fp_t) := lift_to_both0 n_1707 in
        letb '(m1_1711, m2_1712) : (fp_t '× fp_t) := lift_to_both0 m_1710 in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
            (lift_to_both0 n1_1708) +% (lift_to_both0 m1_1711),
            (lift_to_both0 n2_1709) +% (lift_to_both0 m2_1712)
          ))
        ) : both (fset.fset0) [interface] (fp2_t)))in
  both_package' _ _ (FP2ADD,(fp2add_inp,fp2add_out)) temp_package_both.
Fail Next Obligation.


Notation "'fp2sub_inp'" :=(
  fp2_t '× fp2_t : choice_type) (in custom pack_type at level 2).
Notation "'fp2sub_inp'" :=(fp2_t '× fp2_t : ChoiceEquality) (at level 2).
Notation "'fp2sub_out'" :=(
  fp2_t : choice_type) (in custom pack_type at level 2).
Notation "'fp2sub_out'" :=(fp2_t : ChoiceEquality) (at level 2).
Definition FP2SUB : nat :=
  1716.
Program Definition fp2sub
  : both_package (fset.fset0) [interface
  #val #[ FP2ADD ] : fp2add_inp → fp2add_out ;
  #val #[ FP2NEG ] : fp2neg_inp → fp2neg_out ] [(FP2SUB,(
      fp2sub_inp,fp2sub_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(n_1714 , m_1715) := temp_inp : fp2_t '× fp2_t in
    
    let fp2add := fun x_0 x_1 => package_both fp2add (x_0,x_1) in
    let fp2neg := fun x_0 => package_both fp2neg (x_0) in
    ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (fp2add (
            lift_to_both0 n_1714) (fp2neg (lift_to_both0 m_1715)))
        ) : both (fset.fset0) [interface
      #val #[ FP2ADD ] : fp2add_inp → fp2add_out ;
      #val #[ FP2NEG ] : fp2neg_inp → fp2neg_out ] (fp2_t)))in
  both_package' _ _ (FP2SUB,(fp2sub_inp,fp2sub_out)) temp_package_both.
Fail Next Obligation.


Notation "'fp2mul_inp'" :=(
  fp2_t '× fp2_t : choice_type) (in custom pack_type at level 2).
Notation "'fp2mul_inp'" :=(fp2_t '× fp2_t : ChoiceEquality) (at level 2).
Notation "'fp2mul_out'" :=(
  fp2_t : choice_type) (in custom pack_type at level 2).
Notation "'fp2mul_out'" :=(fp2_t : ChoiceEquality) (at level 2).
Definition FP2MUL : nat :=
  1725.
Program Definition fp2mul
  : both_package (fset.fset0) [interface] [(FP2MUL,(fp2mul_inp,fp2mul_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(n_1717 , m_1720) := temp_inp : fp2_t '× fp2_t in
    
    ((letb '(n1_1718, n2_1719) : (fp_t '× fp_t) := lift_to_both0 n_1717 in
        letb '(m1_1721, m2_1722) : (fp_t '× fp_t) := lift_to_both0 m_1720 in
        letb x1_1723 : fp_t :=
          ((lift_to_both0 n1_1718) *% (lift_to_both0 m1_1721)) -% ((
              lift_to_both0 n2_1719) *% (lift_to_both0 m2_1722)) in
        letb x2_1724 : fp_t :=
          ((lift_to_both0 n1_1718) *% (lift_to_both0 m2_1722)) +% ((
              lift_to_both0 n2_1719) *% (lift_to_both0 m1_1721)) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
            lift_to_both0 x1_1723,
            lift_to_both0 x2_1724
          ))
        ) : both (fset.fset0) [interface] (fp2_t)))in
  both_package' _ _ (FP2MUL,(fp2mul_inp,fp2mul_out)) temp_package_both.
Fail Next Obligation.


Notation "'fp2inv_inp'" :=(
  fp2_t : choice_type) (in custom pack_type at level 2).
Notation "'fp2inv_inp'" :=(fp2_t : ChoiceEquality) (at level 2).
Notation "'fp2inv_out'" :=(
  fp2_t : choice_type) (in custom pack_type at level 2).
Notation "'fp2inv_out'" :=(fp2_t : ChoiceEquality) (at level 2).
Definition FP2INV : nat :=
  1733.
Program Definition fp2inv
  : both_package (fset.fset0) [interface] [(FP2INV,(fp2inv_inp,fp2inv_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(n_1726) := temp_inp : fp2_t in
    
    ((letb '(n1_1727, n2_1728) : (fp_t '× fp_t) := lift_to_both0 n_1726 in
        letb t0_1729 : fp_t :=
          ((lift_to_both0 n1_1727) *% (lift_to_both0 n1_1727)) +% ((
              lift_to_both0 n2_1728) *% (lift_to_both0 n2_1728)) in
        letb t1_1730 : fp_t := nat_mod_inv (lift_to_both0 t0_1729) in
        letb x1_1731 : fp_t :=
          (lift_to_both0 n1_1727) *% (lift_to_both0 t1_1730) in
        letb x2_1732 : fp_t :=
          (nat_mod_zero ) -% ((lift_to_both0 n2_1728) *% (
              lift_to_both0 t1_1730)) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
            lift_to_both0 x1_1731,
            lift_to_both0 x2_1732
          ))
        ) : both (fset.fset0) [interface] (fp2_t)))in
  both_package' _ _ (FP2INV,(fp2inv_inp,fp2inv_out)) temp_package_both.
Fail Next Obligation.


Notation "'fp2conjugate_inp'" :=(
  fp2_t : choice_type) (in custom pack_type at level 2).
Notation "'fp2conjugate_inp'" :=(fp2_t : ChoiceEquality) (at level 2).
Notation "'fp2conjugate_out'" :=(
  fp2_t : choice_type) (in custom pack_type at level 2).
Notation "'fp2conjugate_out'" :=(fp2_t : ChoiceEquality) (at level 2).
Definition FP2CONJUGATE : nat :=
  1737.
Program Definition fp2conjugate
  : both_package (fset.fset0) [interface] [(FP2CONJUGATE,(
      fp2conjugate_inp,fp2conjugate_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(n_1734) := temp_inp : fp2_t in
    
    ((letb '(n1_1735, n2_1736) : (fp_t '× fp_t) := lift_to_both0 n_1734 in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
            lift_to_both0 n1_1735,
            (nat_mod_zero ) -% (lift_to_both0 n2_1736)
          ))
        ) : both (fset.fset0) [interface] (fp2_t)))in
  both_package' _ _ (FP2CONJUGATE,(
      fp2conjugate_inp,fp2conjugate_out)) temp_package_both.
Fail Next Obligation.


Notation "'fp6fromfp2_inp'" :=(
  fp2_t : choice_type) (in custom pack_type at level 2).
Notation "'fp6fromfp2_inp'" :=(fp2_t : ChoiceEquality) (at level 2).
Notation "'fp6fromfp2_out'" :=(
  fp6_t : choice_type) (in custom pack_type at level 2).
Notation "'fp6fromfp2_out'" :=(fp6_t : ChoiceEquality) (at level 2).
Definition FP6FROMFP2 : nat :=
  1739.
Program Definition fp6fromfp2
  : both_package (fset.fset0) [interface
  #val #[ FP2ZERO ] : fp2zero_inp → fp2zero_out ] [(FP6FROMFP2,(
      fp6fromfp2_inp,fp6fromfp2_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(n_1738) := temp_inp : fp2_t in
    
    let fp2zero := package_both fp2zero tt in
    ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
            lift_to_both0 n_1738,
            fp2zero ,
            fp2zero 
          ))
        ) : both (fset.fset0) [interface
      #val #[ FP2ZERO ] : fp2zero_inp → fp2zero_out ] (fp6_t)))in
  both_package' _ _ (FP6FROMFP2,(
      fp6fromfp2_inp,fp6fromfp2_out)) temp_package_both.
Fail Next Obligation.


Notation "'fp6zero_inp'" :=(
  unit_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'fp6zero_inp'" :=(unit_ChoiceEquality : ChoiceEquality) (at level 2).
Notation "'fp6zero_out'" :=(
  fp6_t : choice_type) (in custom pack_type at level 2).
Notation "'fp6zero_out'" :=(fp6_t : ChoiceEquality) (at level 2).
Definition FP6ZERO : nat :=
  1740.
Program Definition fp6zero
  : both_package (fset.fset0) [interface
  #val #[ FP2ZERO ] : fp2zero_inp → fp2zero_out ;
  #val #[ FP6FROMFP2 ] : fp6fromfp2_inp → fp6fromfp2_out ] [(FP6ZERO,(
      fp6zero_inp,fp6zero_out))] :=
  let temp_package_both := (fun temp_inp => 
    
    let fp2zero := package_both fp2zero tt in
    let fp6fromfp2 := fun x_0 => package_both fp6fromfp2 (x_0) in
    ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (fp6fromfp2 (fp2zero ))
        ) : both (fset.fset0) [interface
      #val #[ FP2ZERO ] : fp2zero_inp → fp2zero_out ;
      #val #[ FP6FROMFP2 ] : fp6fromfp2_inp → fp6fromfp2_out ] (fp6_t)))in
  both_package' _ _ (FP6ZERO,(fp6zero_inp,fp6zero_out)) temp_package_both.
Fail Next Obligation.


Notation "'fp6neg_inp'" :=(
  fp6_t : choice_type) (in custom pack_type at level 2).
Notation "'fp6neg_inp'" :=(fp6_t : ChoiceEquality) (at level 2).
Notation "'fp6neg_out'" :=(
  fp6_t : choice_type) (in custom pack_type at level 2).
Notation "'fp6neg_out'" :=(fp6_t : ChoiceEquality) (at level 2).
Definition FP6NEG : nat :=
  1745.
Program Definition fp6neg
  : both_package (fset.fset0) [interface
  #val #[ FP2SUB ] : fp2sub_inp → fp2sub_out ;
  #val #[ FP2ZERO ] : fp2zero_inp → fp2zero_out ] [(FP6NEG,(
      fp6neg_inp,fp6neg_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(n_1741) := temp_inp : fp6_t in
    
    let fp2sub := fun x_0 x_1 => package_both fp2sub (x_0,x_1) in
    let fp2zero := package_both fp2zero tt in
    ((letb '(n1_1742, n2_1743, n3_1744) : (fp2_t '× fp2_t '× fp2_t) :=
          lift_to_both0 n_1741 in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
            fp2sub (fp2zero ) (lift_to_both0 n1_1742),
            fp2sub (fp2zero ) (lift_to_both0 n2_1743),
            fp2sub (fp2zero ) (lift_to_both0 n3_1744)
          ))
        ) : both (fset.fset0) [interface
      #val #[ FP2SUB ] : fp2sub_inp → fp2sub_out ;
      #val #[ FP2ZERO ] : fp2zero_inp → fp2zero_out ] (fp6_t)))in
  both_package' _ _ (FP6NEG,(fp6neg_inp,fp6neg_out)) temp_package_both.
Fail Next Obligation.


Notation "'fp6add_inp'" :=(
  fp6_t '× fp6_t : choice_type) (in custom pack_type at level 2).
Notation "'fp6add_inp'" :=(fp6_t '× fp6_t : ChoiceEquality) (at level 2).
Notation "'fp6add_out'" :=(
  fp6_t : choice_type) (in custom pack_type at level 2).
Notation "'fp6add_out'" :=(fp6_t : ChoiceEquality) (at level 2).
Definition FP6ADD : nat :=
  1754.
Program Definition fp6add
  : both_package (fset.fset0) [interface
  #val #[ FP2ADD ] : fp2add_inp → fp2add_out ] [(FP6ADD,(
      fp6add_inp,fp6add_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(n_1746 , m_1750) := temp_inp : fp6_t '× fp6_t in
    
    let fp2add := fun x_0 x_1 => package_both fp2add (x_0,x_1) in
    ((letb '(n1_1747, n2_1748, n3_1749) : (fp2_t '× fp2_t '× fp2_t) :=
          lift_to_both0 n_1746 in
        letb '(m1_1751, m2_1752, m3_1753) : (fp2_t '× fp2_t '× fp2_t) :=
          lift_to_both0 m_1750 in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
            fp2add (lift_to_both0 n1_1747) (lift_to_both0 m1_1751),
            fp2add (lift_to_both0 n2_1748) (lift_to_both0 m2_1752),
            fp2add (lift_to_both0 n3_1749) (lift_to_both0 m3_1753)
          ))
        ) : both (fset.fset0) [interface
      #val #[ FP2ADD ] : fp2add_inp → fp2add_out ] (fp6_t)))in
  both_package' _ _ (FP6ADD,(fp6add_inp,fp6add_out)) temp_package_both.
Fail Next Obligation.


Notation "'fp6sub_inp'" :=(
  fp6_t '× fp6_t : choice_type) (in custom pack_type at level 2).
Notation "'fp6sub_inp'" :=(fp6_t '× fp6_t : ChoiceEquality) (at level 2).
Notation "'fp6sub_out'" :=(
  fp6_t : choice_type) (in custom pack_type at level 2).
Notation "'fp6sub_out'" :=(fp6_t : ChoiceEquality) (at level 2).
Definition FP6SUB : nat :=
  1757.
Program Definition fp6sub
  : both_package (fset.fset0) [interface
  #val #[ FP6ADD ] : fp6add_inp → fp6add_out ;
  #val #[ FP6NEG ] : fp6neg_inp → fp6neg_out ] [(FP6SUB,(
      fp6sub_inp,fp6sub_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(n_1755 , m_1756) := temp_inp : fp6_t '× fp6_t in
    
    let fp6add := fun x_0 x_1 => package_both fp6add (x_0,x_1) in
    let fp6neg := fun x_0 => package_both fp6neg (x_0) in
    ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (fp6add (
            lift_to_both0 n_1755) (fp6neg (lift_to_both0 m_1756)))
        ) : both (fset.fset0) [interface
      #val #[ FP6ADD ] : fp6add_inp → fp6add_out ;
      #val #[ FP6NEG ] : fp6neg_inp → fp6neg_out ] (fp6_t)))in
  both_package' _ _ (FP6SUB,(fp6sub_inp,fp6sub_out)) temp_package_both.
Fail Next Obligation.


Notation "'fp6mul_inp'" :=(
  fp6_t '× fp6_t : choice_type) (in custom pack_type at level 2).
Notation "'fp6mul_inp'" :=(fp6_t '× fp6_t : ChoiceEquality) (at level 2).
Notation "'fp6mul_out'" :=(
  fp6_t : choice_type) (in custom pack_type at level 2).
Notation "'fp6mul_out'" :=(fp6_t : ChoiceEquality) (at level 2).
Definition FP6MUL : nat :=
  1779.
Program Definition fp6mul
  : both_package (fset.fset0) [interface
  #val #[ FP2ADD ] : fp2add_inp → fp2add_out ;
  #val #[ FP2MUL ] : fp2mul_inp → fp2mul_out ;
  #val #[ FP2SUB ] : fp2sub_inp → fp2sub_out ] [(FP6MUL,(
      fp6mul_inp,fp6mul_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(n_1758 , m_1762) := temp_inp : fp6_t '× fp6_t in
    
    let fp2add := fun x_0 x_1 => package_both fp2add (x_0,x_1) in
    let fp2mul := fun x_0 x_1 => package_both fp2mul (x_0,x_1) in
    let fp2sub := fun x_0 x_1 => package_both fp2sub (x_0,x_1) in
    ((letb '(n1_1759, n2_1760, n3_1761) : (fp2_t '× fp2_t '× fp2_t) :=
          lift_to_both0 n_1758 in
        letb '(m1_1763, m2_1764, m3_1765) : (fp2_t '× fp2_t '× fp2_t) :=
          lift_to_both0 m_1762 in
        letb eps_1766 : (fp_t '× fp_t) := prod_b(nat_mod_one , nat_mod_one ) in
        letb t1_1767 : (fp_t '× fp_t) :=
          fp2mul (lift_to_both0 n1_1759) (lift_to_both0 m1_1763) in
        letb t2_1768 : (fp_t '× fp_t) :=
          fp2mul (lift_to_both0 n2_1760) (lift_to_both0 m2_1764) in
        letb t3_1769 : (fp_t '× fp_t) :=
          fp2mul (lift_to_both0 n3_1761) (lift_to_both0 m3_1765) in
        letb t4_1770 : (fp_t '× fp_t) :=
          fp2mul (fp2add (lift_to_both0 n2_1760) (lift_to_both0 n3_1761)) (
            fp2add (lift_to_both0 m2_1764) (lift_to_both0 m3_1765)) in
        letb t5_1771 : (fp_t '× fp_t) :=
          fp2sub (fp2sub (lift_to_both0 t4_1770) (lift_to_both0 t2_1768)) (
            lift_to_both0 t3_1769) in
        letb x_1772 : (fp_t '× fp_t) :=
          fp2add (fp2mul (lift_to_both0 t5_1771) (lift_to_both0 eps_1766)) (
            lift_to_both0 t1_1767) in
        letb t4_1773 : (fp_t '× fp_t) :=
          fp2mul (fp2add (lift_to_both0 n1_1759) (lift_to_both0 n2_1760)) (
            fp2add (lift_to_both0 m1_1763) (lift_to_both0 m2_1764)) in
        letb t5_1774 : (fp_t '× fp_t) :=
          fp2sub (fp2sub (lift_to_both0 t4_1773) (lift_to_both0 t1_1767)) (
            lift_to_both0 t2_1768) in
        letb y_1775 : (fp_t '× fp_t) :=
          fp2add (lift_to_both0 t5_1774) (fp2mul (lift_to_both0 eps_1766) (
              lift_to_both0 t3_1769)) in
        letb t4_1776 : (fp_t '× fp_t) :=
          fp2mul (fp2add (lift_to_both0 n1_1759) (lift_to_both0 n3_1761)) (
            fp2add (lift_to_both0 m1_1763) (lift_to_both0 m3_1765)) in
        letb t5_1777 : (fp_t '× fp_t) :=
          fp2sub (fp2sub (lift_to_both0 t4_1776) (lift_to_both0 t1_1767)) (
            lift_to_both0 t3_1769) in
        letb z_1778 : (fp_t '× fp_t) :=
          fp2add (lift_to_both0 t5_1777) (lift_to_both0 t2_1768) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
            lift_to_both0 x_1772,
            lift_to_both0 y_1775,
            lift_to_both0 z_1778
          ))
        ) : both (fset.fset0) [interface
      #val #[ FP2ADD ] : fp2add_inp → fp2add_out ;
      #val #[ FP2MUL ] : fp2mul_inp → fp2mul_out ;
      #val #[ FP2SUB ] : fp2sub_inp → fp2sub_out ] (fp6_t)))in
  both_package' _ _ (FP6MUL,(fp6mul_inp,fp6mul_out)) temp_package_both.
Fail Next Obligation.


Notation "'fp6inv_inp'" :=(
  fp6_t : choice_type) (in custom pack_type at level 2).
Notation "'fp6inv_inp'" :=(fp6_t : ChoiceEquality) (at level 2).
Notation "'fp6inv_out'" :=(
  fp6_t : choice_type) (in custom pack_type at level 2).
Notation "'fp6inv_out'" :=(fp6_t : ChoiceEquality) (at level 2).
Definition FP6INV : nat :=
  1801.
Program Definition fp6inv
  : both_package (fset.fset0) [interface
  #val #[ FP2ADD ] : fp2add_inp → fp2add_out ;
  #val #[ FP2INV ] : fp2inv_inp → fp2inv_out ;
  #val #[ FP2MUL ] : fp2mul_inp → fp2mul_out ;
  #val #[ FP2SUB ] : fp2sub_inp → fp2sub_out ] [(FP6INV,(
      fp6inv_inp,fp6inv_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(n_1780) := temp_inp : fp6_t in
    
    let fp2add := fun x_0 x_1 => package_both fp2add (x_0,x_1) in
    let fp2inv := fun x_0 => package_both fp2inv (x_0) in
    let fp2mul := fun x_0 x_1 => package_both fp2mul (x_0,x_1) in
    let fp2sub := fun x_0 x_1 => package_both fp2sub (x_0,x_1) in
    ((letb '(n1_1781, n2_1782, n3_1783) : (fp2_t '× fp2_t '× fp2_t) :=
          lift_to_both0 n_1780 in
        letb eps_1784 : (fp_t '× fp_t) := prod_b(nat_mod_one , nat_mod_one ) in
        letb t1_1785 : (fp_t '× fp_t) :=
          fp2mul (lift_to_both0 n1_1781) (lift_to_both0 n1_1781) in
        letb t2_1786 : (fp_t '× fp_t) :=
          fp2mul (lift_to_both0 n2_1782) (lift_to_both0 n2_1782) in
        letb t3_1787 : (fp_t '× fp_t) :=
          fp2mul (lift_to_both0 n3_1783) (lift_to_both0 n3_1783) in
        letb t4_1788 : (fp_t '× fp_t) :=
          fp2mul (lift_to_both0 n1_1781) (lift_to_both0 n2_1782) in
        letb t5_1789 : (fp_t '× fp_t) :=
          fp2mul (lift_to_both0 n1_1781) (lift_to_both0 n3_1783) in
        letb t6_1790 : (fp_t '× fp_t) :=
          fp2mul (lift_to_both0 n2_1782) (lift_to_both0 n3_1783) in
        letb x0_1791 : (fp_t '× fp_t) :=
          fp2sub (lift_to_both0 t1_1785) (fp2mul (lift_to_both0 eps_1784) (
              lift_to_both0 t6_1790)) in
        letb y0_1792 : (fp_t '× fp_t) :=
          fp2sub (fp2mul (lift_to_both0 eps_1784) (lift_to_both0 t3_1787)) (
            lift_to_both0 t4_1788) in
        letb z0_1793 : (fp_t '× fp_t) :=
          fp2sub (lift_to_both0 t2_1786) (lift_to_both0 t5_1789) in
        letb t0_1794 : (fp_t '× fp_t) :=
          fp2mul (lift_to_both0 n1_1781) (lift_to_both0 x0_1791) in
        letb t0_1795 : (fp_t '× fp_t) :=
          fp2add (lift_to_both0 t0_1794) (fp2mul (lift_to_both0 eps_1784) (
              fp2mul (lift_to_both0 n3_1783) (lift_to_both0 y0_1792))) in
        letb t0_1796 : (fp_t '× fp_t) :=
          fp2add (lift_to_both0 t0_1795) (fp2mul (lift_to_both0 eps_1784) (
              fp2mul (lift_to_both0 n2_1782) (lift_to_both0 z0_1793))) in
        letb t0_1797 : (fp_t '× fp_t) := fp2inv (lift_to_both0 t0_1796) in
        letb x_1798 : (fp_t '× fp_t) :=
          fp2mul (lift_to_both0 x0_1791) (lift_to_both0 t0_1797) in
        letb y_1799 : (fp_t '× fp_t) :=
          fp2mul (lift_to_both0 y0_1792) (lift_to_both0 t0_1797) in
        letb z_1800 : (fp_t '× fp_t) :=
          fp2mul (lift_to_both0 z0_1793) (lift_to_both0 t0_1797) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
            lift_to_both0 x_1798,
            lift_to_both0 y_1799,
            lift_to_both0 z_1800
          ))
        ) : both (fset.fset0) [interface
      #val #[ FP2ADD ] : fp2add_inp → fp2add_out ;
      #val #[ FP2INV ] : fp2inv_inp → fp2inv_out ;
      #val #[ FP2MUL ] : fp2mul_inp → fp2mul_out ;
      #val #[ FP2SUB ] : fp2sub_inp → fp2sub_out ] (fp6_t)))in
  both_package' _ _ (FP6INV,(fp6inv_inp,fp6inv_out)) temp_package_both.
Fail Next Obligation.


Notation "'fp12fromfp6_inp'" :=(
  fp6_t : choice_type) (in custom pack_type at level 2).
Notation "'fp12fromfp6_inp'" :=(fp6_t : ChoiceEquality) (at level 2).
Notation "'fp12fromfp6_out'" :=(
  fp12_t : choice_type) (in custom pack_type at level 2).
Notation "'fp12fromfp6_out'" :=(fp12_t : ChoiceEquality) (at level 2).
Definition FP12FROMFP6 : nat :=
  1803.
Program Definition fp12fromfp6
  : both_package (fset.fset0) [interface
  #val #[ FP6ZERO ] : fp6zero_inp → fp6zero_out ] [(FP12FROMFP6,(
      fp12fromfp6_inp,fp12fromfp6_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(n_1802) := temp_inp : fp6_t in
    
    let fp6zero := package_both fp6zero tt in
    ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
            lift_to_both0 n_1802,
            fp6zero 
          ))
        ) : both (fset.fset0) [interface
      #val #[ FP6ZERO ] : fp6zero_inp → fp6zero_out ] (fp12_t)))in
  both_package' _ _ (FP12FROMFP6,(
      fp12fromfp6_inp,fp12fromfp6_out)) temp_package_both.
Fail Next Obligation.


Notation "'fp12neg_inp'" :=(
  fp12_t : choice_type) (in custom pack_type at level 2).
Notation "'fp12neg_inp'" :=(fp12_t : ChoiceEquality) (at level 2).
Notation "'fp12neg_out'" :=(
  fp12_t : choice_type) (in custom pack_type at level 2).
Notation "'fp12neg_out'" :=(fp12_t : ChoiceEquality) (at level 2).
Definition FP12NEG : nat :=
  1807.
Program Definition fp12neg
  : both_package (fset.fset0) [interface
  #val #[ FP6SUB ] : fp6sub_inp → fp6sub_out ;
  #val #[ FP6ZERO ] : fp6zero_inp → fp6zero_out ] [(FP12NEG,(
      fp12neg_inp,fp12neg_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(n_1804) := temp_inp : fp12_t in
    
    let fp6sub := fun x_0 x_1 => package_both fp6sub (x_0,x_1) in
    let fp6zero := package_both fp6zero tt in
    ((letb '(n1_1805, n2_1806) : (fp6_t '× fp6_t) := lift_to_both0 n_1804 in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
            fp6sub (fp6zero ) (lift_to_both0 n1_1805),
            fp6sub (fp6zero ) (lift_to_both0 n2_1806)
          ))
        ) : both (fset.fset0) [interface
      #val #[ FP6SUB ] : fp6sub_inp → fp6sub_out ;
      #val #[ FP6ZERO ] : fp6zero_inp → fp6zero_out ] (fp12_t)))in
  both_package' _ _ (FP12NEG,(fp12neg_inp,fp12neg_out)) temp_package_both.
Fail Next Obligation.


Notation "'fp12add_inp'" :=(
  fp12_t '× fp12_t : choice_type) (in custom pack_type at level 2).
Notation "'fp12add_inp'" :=(fp12_t '× fp12_t : ChoiceEquality) (at level 2).
Notation "'fp12add_out'" :=(
  fp12_t : choice_type) (in custom pack_type at level 2).
Notation "'fp12add_out'" :=(fp12_t : ChoiceEquality) (at level 2).
Definition FP12ADD : nat :=
  1814.
Program Definition fp12add
  : both_package (fset.fset0) [interface
  #val #[ FP6ADD ] : fp6add_inp → fp6add_out ] [(FP12ADD,(
      fp12add_inp,fp12add_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(n_1808 , m_1811) := temp_inp : fp12_t '× fp12_t in
    
    let fp6add := fun x_0 x_1 => package_both fp6add (x_0,x_1) in
    ((letb '(n1_1809, n2_1810) : (fp6_t '× fp6_t) := lift_to_both0 n_1808 in
        letb '(m1_1812, m2_1813) : (fp6_t '× fp6_t) := lift_to_both0 m_1811 in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
            fp6add (lift_to_both0 n1_1809) (lift_to_both0 m1_1812),
            fp6add (lift_to_both0 n2_1810) (lift_to_both0 m2_1813)
          ))
        ) : both (fset.fset0) [interface
      #val #[ FP6ADD ] : fp6add_inp → fp6add_out ] (fp12_t)))in
  both_package' _ _ (FP12ADD,(fp12add_inp,fp12add_out)) temp_package_both.
Fail Next Obligation.


Notation "'fp12sub_inp'" :=(
  fp12_t '× fp12_t : choice_type) (in custom pack_type at level 2).
Notation "'fp12sub_inp'" :=(fp12_t '× fp12_t : ChoiceEquality) (at level 2).
Notation "'fp12sub_out'" :=(
  fp12_t : choice_type) (in custom pack_type at level 2).
Notation "'fp12sub_out'" :=(fp12_t : ChoiceEquality) (at level 2).
Definition FP12SUB : nat :=
  1817.
Program Definition fp12sub
  : both_package (fset.fset0) [interface
  #val #[ FP12ADD ] : fp12add_inp → fp12add_out ;
  #val #[ FP12NEG ] : fp12neg_inp → fp12neg_out ] [(FP12SUB,(
      fp12sub_inp,fp12sub_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(n_1815 , m_1816) := temp_inp : fp12_t '× fp12_t in
    
    let fp12add := fun x_0 x_1 => package_both fp12add (x_0,x_1) in
    let fp12neg := fun x_0 => package_both fp12neg (x_0) in
    ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (fp12add (
            lift_to_both0 n_1815) (fp12neg (lift_to_both0 m_1816)))
        ) : both (fset.fset0) [interface
      #val #[ FP12ADD ] : fp12add_inp → fp12add_out ;
      #val #[ FP12NEG ] : fp12neg_inp → fp12neg_out ] (fp12_t)))in
  both_package' _ _ (FP12SUB,(fp12sub_inp,fp12sub_out)) temp_package_both.
Fail Next Obligation.


Notation "'fp12mul_inp'" :=(
  fp12_t '× fp12_t : choice_type) (in custom pack_type at level 2).
Notation "'fp12mul_inp'" :=(fp12_t '× fp12_t : ChoiceEquality) (at level 2).
Notation "'fp12mul_out'" :=(
  fp12_t : choice_type) (in custom pack_type at level 2).
Notation "'fp12mul_out'" :=(fp12_t : ChoiceEquality) (at level 2).
Definition FP12MUL : nat :=
  1830.
Program Definition fp12mul
  : both_package (fset.fset0) [interface
  #val #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out ;
  #val #[ FP2ZERO ] : fp2zero_inp → fp2zero_out ;
  #val #[ FP6ADD ] : fp6add_inp → fp6add_out ;
  #val #[ FP6MUL ] : fp6mul_inp → fp6mul_out ;
  #val #[ FP6SUB ] : fp6sub_inp → fp6sub_out ] [(FP12MUL,(
      fp12mul_inp,fp12mul_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(n_1818 , m_1821) := temp_inp : fp12_t '× fp12_t in
    
    let fp2fromfp := fun x_0 => package_both fp2fromfp (x_0) in
    let fp2zero := package_both fp2zero tt in
    let fp6add := fun x_0 x_1 => package_both fp6add (x_0,x_1) in
    let fp6mul := fun x_0 x_1 => package_both fp6mul (x_0,x_1) in
    let fp6sub := fun x_0 x_1 => package_both fp6sub (x_0,x_1) in
    ((letb '(n1_1819, n2_1820) : (fp6_t '× fp6_t) := lift_to_both0 n_1818 in
        letb '(m1_1822, m2_1823) : (fp6_t '× fp6_t) := lift_to_both0 m_1821 in
        letb gamma_1824 : (fp2_t '× fp2_t '× fp2_t) :=
          prod_b(fp2zero , fp2fromfp (nat_mod_one ), fp2zero ) in
        letb t1_1825 : (fp2_t '× fp2_t '× fp2_t) :=
          fp6mul (lift_to_both0 n1_1819) (lift_to_both0 m1_1822) in
        letb t2_1826 : (fp2_t '× fp2_t '× fp2_t) :=
          fp6mul (lift_to_both0 n2_1820) (lift_to_both0 m2_1823) in
        letb x_1827 : (fp2_t '× fp2_t '× fp2_t) :=
          fp6add (lift_to_both0 t1_1825) (fp6mul (lift_to_both0 t2_1826) (
              lift_to_both0 gamma_1824)) in
        letb y_1828 : (fp2_t '× fp2_t '× fp2_t) :=
          fp6mul (fp6add (lift_to_both0 n1_1819) (lift_to_both0 n2_1820)) (
            fp6add (lift_to_both0 m1_1822) (lift_to_both0 m2_1823)) in
        letb y_1829 : (fp2_t '× fp2_t '× fp2_t) :=
          fp6sub (fp6sub (lift_to_both0 y_1828) (lift_to_both0 t1_1825)) (
            lift_to_both0 t2_1826) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
            lift_to_both0 x_1827,
            lift_to_both0 y_1829
          ))
        ) : both (fset.fset0) [interface
      #val #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out ;
      #val #[ FP2ZERO ] : fp2zero_inp → fp2zero_out ;
      #val #[ FP6ADD ] : fp6add_inp → fp6add_out ;
      #val #[ FP6MUL ] : fp6mul_inp → fp6mul_out ;
      #val #[ FP6SUB ] : fp6sub_inp → fp6sub_out ] (fp12_t)))in
  both_package' _ _ (FP12MUL,(fp12mul_inp,fp12mul_out)) temp_package_both.
Fail Next Obligation.


Notation "'fp12inv_inp'" :=(
  fp12_t : choice_type) (in custom pack_type at level 2).
Notation "'fp12inv_inp'" :=(fp12_t : ChoiceEquality) (at level 2).
Notation "'fp12inv_out'" :=(
  fp12_t : choice_type) (in custom pack_type at level 2).
Notation "'fp12inv_out'" :=(fp12_t : ChoiceEquality) (at level 2).
Definition FP12INV : nat :=
  1841.
Program Definition fp12inv
  : both_package (fset.fset0) [interface
  #val #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out ;
  #val #[ FP2ZERO ] : fp2zero_inp → fp2zero_out ;
  #val #[ FP6INV ] : fp6inv_inp → fp6inv_out ;
  #val #[ FP6MUL ] : fp6mul_inp → fp6mul_out ;
  #val #[ FP6NEG ] : fp6neg_inp → fp6neg_out ;
  #val #[ FP6SUB ] : fp6sub_inp → fp6sub_out ] [(FP12INV,(
      fp12inv_inp,fp12inv_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(n_1831) := temp_inp : fp12_t in
    
    let fp2fromfp := fun x_0 => package_both fp2fromfp (x_0) in
    let fp2zero := package_both fp2zero tt in
    let fp6inv := fun x_0 => package_both fp6inv (x_0) in
    let fp6mul := fun x_0 x_1 => package_both fp6mul (x_0,x_1) in
    let fp6neg := fun x_0 => package_both fp6neg (x_0) in
    let fp6sub := fun x_0 x_1 => package_both fp6sub (x_0,x_1) in
    ((letb '(n1_1832, n2_1833) : (fp6_t '× fp6_t) := lift_to_both0 n_1831 in
        letb gamma_1834 : (fp2_t '× fp2_t '× fp2_t) :=
          prod_b(fp2zero , fp2fromfp (nat_mod_one ), fp2zero ) in
        letb t1_1835 : (fp2_t '× fp2_t '× fp2_t) :=
          fp6mul (lift_to_both0 n1_1832) (lift_to_both0 n1_1832) in
        letb t2_1836 : (fp2_t '× fp2_t '× fp2_t) :=
          fp6mul (lift_to_both0 n2_1833) (lift_to_both0 n2_1833) in
        letb t1_1837 : (fp2_t '× fp2_t '× fp2_t) :=
          fp6sub (lift_to_both0 t1_1835) (fp6mul (lift_to_both0 gamma_1834) (
              lift_to_both0 t2_1836)) in
        letb t2_1838 : (fp2_t '× fp2_t '× fp2_t) :=
          fp6inv (lift_to_both0 t1_1837) in
        letb x_1839 : (fp2_t '× fp2_t '× fp2_t) :=
          fp6mul (lift_to_both0 n1_1832) (lift_to_both0 t2_1838) in
        letb y_1840 : (fp2_t '× fp2_t '× fp2_t) :=
          fp6neg (fp6mul (lift_to_both0 n2_1833) (lift_to_both0 t2_1838)) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
            lift_to_both0 x_1839,
            lift_to_both0 y_1840
          ))
        ) : both (fset.fset0) [interface
      #val #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out ;
      #val #[ FP2ZERO ] : fp2zero_inp → fp2zero_out ;
      #val #[ FP6INV ] : fp6inv_inp → fp6inv_out ;
      #val #[ FP6MUL ] : fp6mul_inp → fp6mul_out ;
      #val #[ FP6NEG ] : fp6neg_inp → fp6neg_out ;
      #val #[ FP6SUB ] : fp6sub_inp → fp6sub_out ] (fp12_t)))in
  both_package' _ _ (FP12INV,(fp12inv_inp,fp12inv_out)) temp_package_both.
Fail Next Obligation.

Definition c_1842_loc : ChoiceEqualityLocation :=
  ((fp6_t '× fp6_t) ; 1843%nat).
Notation "'fp12exp_inp'" :=(
  fp12_t '× scalar_t : choice_type) (in custom pack_type at level 2).
Notation "'fp12exp_inp'" :=(fp12_t '× scalar_t : ChoiceEquality) (at level 2).
Notation "'fp12exp_out'" :=(
  fp12_t : choice_type) (in custom pack_type at level 2).
Notation "'fp12exp_out'" :=(fp12_t : ChoiceEquality) (at level 2).
Definition FP12EXP : nat :=
  1847.
Program Definition fp12exp
  : both_package (CEfset ([c_1842_loc])) [interface
  #val #[ FP12FROMFP6 ] : fp12fromfp6_inp → fp12fromfp6_out ;
  #val #[ FP12MUL ] : fp12mul_inp → fp12mul_out ;
  #val #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out ;
  #val #[ FP6FROMFP2 ] : fp6fromfp2_inp → fp6fromfp2_out ] [(FP12EXP,(
      fp12exp_inp,fp12exp_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(n_1846 , k_1845) := temp_inp : fp12_t '× scalar_t in
    
    let fp12fromfp6 := fun x_0 => package_both fp12fromfp6 (x_0) in
    let fp12mul := fun x_0 x_1 => package_both fp12mul (x_0,x_1) in
    let fp2fromfp := fun x_0 => package_both fp2fromfp (x_0) in
    let fp6fromfp2 := fun x_0 => package_both fp6fromfp2 (x_0) in
    ((letbm c_1842 : (fp6_t '× fp6_t) loc( c_1842_loc ) :=
          fp12fromfp6 (fp6fromfp2 (fp2fromfp (nat_mod_one ))) in
        letb c_1842 :=
          foldi_both' (lift_to_both0 (usize 0)) (lift_to_both0 (
                usize 256)) c_1842 (L := (CEfset ([c_1842_loc]))) (I := (
              [interface
              #val #[ FP12FROMFP6 ] : fp12fromfp6_inp → fp12fromfp6_out ;
              #val #[ FP12MUL ] : fp12mul_inp → fp12mul_out ;
              #val #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out ;
              #val #[ FP6FROMFP2 ] : fp6fromfp2_inp → fp6fromfp2_out
              ])) (fun i_1844 c_1842 =>
            letbm c_1842 loc( c_1842_loc ) :=
              fp12mul (lift_to_both0 c_1842) (lift_to_both0 c_1842) in
            letb 'c_1842 :=
              if nat_mod_bit (lift_to_both0 k_1845) ((lift_to_both0 (
                    usize 255)) .- (lift_to_both0 i_1844)) :bool_ChoiceEquality
              then lift_scope (L1 := CEfset ([c_1842_loc])) (L2 := CEfset (
                [c_1842_loc])) (I1 := [interface
              #val #[ FP12MUL ] : fp12mul_inp → fp12mul_out
              ]) (I2 := [interface
              #val #[ FP12MUL ] : fp12mul_inp → fp12mul_out
              ]) (H_loc_incl := _) (H_opsig_incl := _) (
                letbm c_1842 loc( c_1842_loc ) :=
                  fp12mul (lift_to_both0 c_1842) (lift_to_both0 n_1846) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                  lift_to_both0 c_1842)
                )
              else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                lift_to_both0 c_1842)
               in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 c_1842)
            ) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 c_1842)
        ) : both (CEfset ([c_1842_loc])) [interface
      #val #[ FP12FROMFP6 ] : fp12fromfp6_inp → fp12fromfp6_out ;
      #val #[ FP12MUL ] : fp12mul_inp → fp12mul_out ;
      #val #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out ;
      #val #[ FP6FROMFP2 ] : fp6fromfp2_inp → fp6fromfp2_out ] (fp12_t)))in
  both_package' _ _ (FP12EXP,(fp12exp_inp,fp12exp_out)) temp_package_both.
Fail Next Obligation.


Notation "'fp12conjugate_inp'" :=(
  fp12_t : choice_type) (in custom pack_type at level 2).
Notation "'fp12conjugate_inp'" :=(fp12_t : ChoiceEquality) (at level 2).
Notation "'fp12conjugate_out'" :=(
  fp12_t : choice_type) (in custom pack_type at level 2).
Notation "'fp12conjugate_out'" :=(fp12_t : ChoiceEquality) (at level 2).
Definition FP12CONJUGATE : nat :=
  1851.
Program Definition fp12conjugate
  : both_package (fset.fset0) [interface
  #val #[ FP6NEG ] : fp6neg_inp → fp6neg_out ] [(FP12CONJUGATE,(
      fp12conjugate_inp,fp12conjugate_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(n_1848) := temp_inp : fp12_t in
    
    let fp6neg := fun x_0 => package_both fp6neg (x_0) in
    ((letb '(n1_1849, n2_1850) : (fp6_t '× fp6_t) := lift_to_both0 n_1848 in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
            lift_to_both0 n1_1849,
            fp6neg (lift_to_both0 n2_1850)
          ))
        ) : both (fset.fset0) [interface
      #val #[ FP6NEG ] : fp6neg_inp → fp6neg_out ] (fp12_t)))in
  both_package' _ _ (FP12CONJUGATE,(
      fp12conjugate_inp,fp12conjugate_out)) temp_package_both.
Fail Next Obligation.


Notation "'fp12zero_inp'" :=(
  unit_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'fp12zero_inp'" :=(unit_ChoiceEquality : ChoiceEquality) (at level 2).
Notation "'fp12zero_out'" :=(
  fp12_t : choice_type) (in custom pack_type at level 2).
Notation "'fp12zero_out'" :=(fp12_t : ChoiceEquality) (at level 2).
Definition FP12ZERO : nat :=
  1852.
Program Definition fp12zero
  : both_package (fset.fset0) [interface
  #val #[ FP12FROMFP6 ] : fp12fromfp6_inp → fp12fromfp6_out ;
  #val #[ FP6ZERO ] : fp6zero_inp → fp6zero_out ] [(FP12ZERO,(
      fp12zero_inp,fp12zero_out))] :=
  let temp_package_both := (fun temp_inp => 
    
    let fp12fromfp6 := fun x_0 => package_both fp12fromfp6 (x_0) in
    let fp6zero := package_both fp6zero tt in
    ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (fp12fromfp6 (fp6zero ))
        ) : both (fset.fset0) [interface
      #val #[ FP12FROMFP6 ] : fp12fromfp6_inp → fp12fromfp6_out ;
      #val #[ FP6ZERO ] : fp6zero_inp → fp6zero_out ] (fp12_t)))in
  both_package' _ _ (FP12ZERO,(fp12zero_inp,fp12zero_out)) temp_package_both.
Fail Next Obligation.


Notation "'g1add_a_inp'" :=(
  g1_t '× g1_t : choice_type) (in custom pack_type at level 2).
Notation "'g1add_a_inp'" :=(g1_t '× g1_t : ChoiceEquality) (at level 2).
Notation "'g1add_a_out'" :=(
  g1_t : choice_type) (in custom pack_type at level 2).
Notation "'g1add_a_out'" :=(g1_t : ChoiceEquality) (at level 2).
Definition G1ADD_A : nat :=
  1864.
Program Definition g1add_a
  : both_package (fset.fset0) [interface] [(G1ADD_A,(
      g1add_a_inp,g1add_a_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(p_1853 , q_1856) := temp_inp : g1_t '× g1_t in
    
    ((letb '(x1_1854, y1_1855, _) : (fp_t '× fp_t '× bool_ChoiceEquality) :=
          lift_to_both0 p_1853 in
        letb '(x2_1857, y2_1858, _) : (fp_t '× fp_t '× bool_ChoiceEquality) :=
          lift_to_both0 q_1856 in
        letb x_diff_1859 : fp_t :=
          (lift_to_both0 x2_1857) -% (lift_to_both0 x1_1854) in
        letb y_diff_1860 : fp_t :=
          (lift_to_both0 y2_1858) -% (lift_to_both0 y1_1855) in
        letb xovery_1861 : fp_t :=
          (lift_to_both0 y_diff_1860) *% (nat_mod_inv (
              lift_to_both0 x_diff_1859)) in
        letb x3_1862 : fp_t :=
          ((nat_mod_exp (lift_to_both0 xovery_1861) (lift_to_both0 (
                  @repr U32 2))) -% (lift_to_both0 x1_1854)) -% (
            lift_to_both0 x2_1857) in
        letb y3_1863 : fp_t :=
          ((lift_to_both0 xovery_1861) *% ((lift_to_both0 x1_1854) -% (
                lift_to_both0 x3_1862))) -% (lift_to_both0 y1_1855) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
            lift_to_both0 x3_1862,
            lift_to_both0 y3_1863,
            lift_to_both0 ((false : bool_ChoiceEquality))
          ))
        ) : both (fset.fset0) [interface] (g1_t)))in
  both_package' _ _ (G1ADD_A,(g1add_a_inp,g1add_a_out)) temp_package_both.
Fail Next Obligation.


Notation "'g1double_a_inp'" :=(
  g1_t : choice_type) (in custom pack_type at level 2).
Notation "'g1double_a_inp'" :=(g1_t : ChoiceEquality) (at level 2).
Notation "'g1double_a_out'" :=(
  g1_t : choice_type) (in custom pack_type at level 2).
Notation "'g1double_a_out'" :=(g1_t : ChoiceEquality) (at level 2).
Definition G1DOUBLE_A : nat :=
  1872.
Program Definition g1double_a
  : both_package (fset.fset0) [interface] [(G1DOUBLE_A,(
      g1double_a_inp,g1double_a_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(p_1865) := temp_inp : g1_t in
    
    ((letb '(x1_1866, y1_1867, _) : (fp_t '× fp_t '× bool_ChoiceEquality) :=
          lift_to_both0 p_1865 in
        letb x12_1868 : fp_t :=
          nat_mod_exp (lift_to_both0 x1_1866) (lift_to_both0 (@repr U32 2)) in
        letb xovery_1869 : fp_t :=
          ((nat_mod_from_literal (
                0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab) (
                lift_to_both0 (@repr U128 3))) *% (lift_to_both0 x12_1868)) *% (
            nat_mod_inv ((nat_mod_two ) *% (lift_to_both0 y1_1867))) in
        letb x3_1870 : fp_t :=
          (nat_mod_exp (lift_to_both0 xovery_1869) (lift_to_both0 (
                @repr U32 2))) -% ((nat_mod_two ) *% (lift_to_both0 x1_1866)) in
        letb y3_1871 : fp_t :=
          ((lift_to_both0 xovery_1869) *% ((lift_to_both0 x1_1866) -% (
                lift_to_both0 x3_1870))) -% (lift_to_both0 y1_1867) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
            lift_to_both0 x3_1870,
            lift_to_both0 y3_1871,
            lift_to_both0 ((false : bool_ChoiceEquality))
          ))
        ) : both (fset.fset0) [interface] (g1_t)))in
  both_package' _ _ (G1DOUBLE_A,(
      g1double_a_inp,g1double_a_out)) temp_package_both.
Fail Next Obligation.


Notation "'g1double_inp'" :=(
  g1_t : choice_type) (in custom pack_type at level 2).
Notation "'g1double_inp'" :=(g1_t : ChoiceEquality) (at level 2).
Notation "'g1double_out'" :=(
  g1_t : choice_type) (in custom pack_type at level 2).
Notation "'g1double_out'" :=(g1_t : ChoiceEquality) (at level 2).
Definition G1DOUBLE : nat :=
  1877.
Program Definition g1double
  : both_package (fset.fset0) [interface
  #val #[ G1DOUBLE_A ] : g1double_a_inp → g1double_a_out ] [(G1DOUBLE,(
      g1double_inp,g1double_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(p_1873) := temp_inp : g1_t in
    
    let g1double_a := fun x_0 => package_both g1double_a (x_0) in
    ((letb '(x1_1874, y1_1875, inf1_1876) : (
            fp_t '×
            fp_t '×
            bool_ChoiceEquality
          ) :=
          lift_to_both0 p_1873 in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          if is_pure (I := [interface]) (((lift_to_both0 y1_1875) !=.? (
                nat_mod_zero )) && (negb (lift_to_both0 inf1_1876)))
          then g1double_a (lift_to_both0 p_1873)
          else prod_b(
            nat_mod_zero ,
            nat_mod_zero ,
            lift_to_both0 ((true : bool_ChoiceEquality))
          ))
        ) : both (fset.fset0) [interface
      #val #[ G1DOUBLE_A ] : g1double_a_inp → g1double_a_out ] (g1_t)))in
  both_package' _ _ (G1DOUBLE,(g1double_inp,g1double_out)) temp_package_both.
Fail Next Obligation.


Notation "'g1add_inp'" :=(
  g1_t '× g1_t : choice_type) (in custom pack_type at level 2).
Notation "'g1add_inp'" :=(g1_t '× g1_t : ChoiceEquality) (at level 2).
Notation "'g1add_out'" :=(g1_t : choice_type) (in custom pack_type at level 2).
Notation "'g1add_out'" :=(g1_t : ChoiceEquality) (at level 2).
Definition G1ADD : nat :=
  1886.
Program Definition g1add
  : both_package (fset.fset0) [interface
  #val #[ G1ADD_A ] : g1add_a_inp → g1add_a_out ;
  #val #[ G1DOUBLE ] : g1double_inp → g1double_out ] [(G1ADD,(
      g1add_inp,g1add_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(p_1878 , q_1882) := temp_inp : g1_t '× g1_t in
    
    let g1add_a := fun x_0 x_1 => package_both g1add_a (x_0,x_1) in
    let g1double := fun x_0 => package_both g1double (x_0) in
    ((letb '(x1_1879, y1_1880, inf1_1881) : (
            fp_t '×
            fp_t '×
            bool_ChoiceEquality
          ) :=
          lift_to_both0 p_1878 in
        letb '(x2_1883, y2_1884, inf2_1885) : (
            fp_t '×
            fp_t '×
            bool_ChoiceEquality
          ) :=
          lift_to_both0 q_1882 in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          if is_pure (I := [interface]) (lift_to_both0 inf1_1881)
          then lift_to_both0 q_1882
          else if is_pure (I := [interface]) (lift_to_both0 inf2_1885)
          then lift_to_both0 p_1878
          else if is_pure (I := [interface]) ((lift_to_both0 p_1878) =.? (
              lift_to_both0 q_1882))
          then g1double (lift_to_both0 p_1878)
          else if is_pure (I := [interface]) (negb (((
                  lift_to_both0 x1_1879) =.? (lift_to_both0 x2_1883)) && ((
                  lift_to_both0 y1_1880) =.? ((nat_mod_zero ) -% (
                    lift_to_both0 y2_1884)))))
          then g1add_a (lift_to_both0 p_1878) (lift_to_both0 q_1882)
          else prod_b(
            nat_mod_zero ,
            nat_mod_zero ,
            lift_to_both0 ((true : bool_ChoiceEquality))
          ))
        ) : both (fset.fset0) [interface
      #val #[ G1ADD_A ] : g1add_a_inp → g1add_a_out ;
      #val #[ G1DOUBLE ] : g1double_inp → g1double_out ] (g1_t)))in
  both_package' _ _ (G1ADD,(g1add_inp,g1add_out)) temp_package_both.
Fail Next Obligation.

Definition t_1887_loc : ChoiceEqualityLocation :=
  ((fp_t '× fp_t '× bool_ChoiceEquality) ; 1888%nat).
Notation "'g1mul_inp'" :=(
  scalar_t '× g1_t : choice_type) (in custom pack_type at level 2).
Notation "'g1mul_inp'" :=(scalar_t '× g1_t : ChoiceEquality) (at level 2).
Notation "'g1mul_out'" :=(g1_t : choice_type) (in custom pack_type at level 2).
Notation "'g1mul_out'" :=(g1_t : ChoiceEquality) (at level 2).
Definition G1MUL : nat :=
  1892.
Program Definition g1mul
  : both_package (CEfset ([t_1887_loc])) [interface
  #val #[ G1ADD ] : g1add_inp → g1add_out ;
  #val #[ G1DOUBLE ] : g1double_inp → g1double_out ] [(G1MUL,(
      g1mul_inp,g1mul_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(m_1890 , p_1891) := temp_inp : scalar_t '× g1_t in
    
    let g1add := fun x_0 x_1 => package_both g1add (x_0,x_1) in
    let g1double := fun x_0 => package_both g1double (x_0) in
    ((letbm t_1887 : (fp_t '× fp_t '× bool_ChoiceEquality
          ) loc( t_1887_loc ) :=
          prod_b(
            nat_mod_zero ,
            nat_mod_zero ,
            lift_to_both0 ((true : bool_ChoiceEquality))
          ) in
        letb t_1887 :=
          foldi_both' (lift_to_both0 (usize 0)) (lift_to_both0 (
                usize 256)) t_1887 (L := (CEfset ([t_1887_loc]))) (I := (
              [interface #val #[ G1ADD ] : g1add_inp → g1add_out ;
              #val #[ G1DOUBLE ] : g1double_inp → g1double_out
              ])) (fun i_1889 t_1887 =>
            letbm t_1887 loc( t_1887_loc ) := g1double (lift_to_both0 t_1887) in
            letb 't_1887 :=
              if nat_mod_bit (lift_to_both0 m_1890) ((lift_to_both0 (
                    usize 255)) .- (lift_to_both0 i_1889)) :bool_ChoiceEquality
              then lift_scope (L1 := CEfset ([t_1887_loc])) (L2 := CEfset (
                [t_1887_loc])) (I1 := [interface
              #val #[ G1ADD ] : g1add_inp → g1add_out ]) (I2 := [interface
              #val #[ G1ADD ] : g1add_inp → g1add_out ;
              #val #[ G1DOUBLE ] : g1double_inp → g1double_out
              ]) (H_loc_incl := _) (H_opsig_incl := _) (
                letbm t_1887 loc( t_1887_loc ) :=
                  g1add (lift_to_both0 t_1887) (lift_to_both0 p_1891) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                  lift_to_both0 t_1887)
                )
              else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                lift_to_both0 t_1887)
               in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 t_1887)
            ) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 t_1887)
        ) : both (CEfset ([t_1887_loc])) [interface
      #val #[ G1ADD ] : g1add_inp → g1add_out ;
      #val #[ G1DOUBLE ] : g1double_inp → g1double_out ] (g1_t)))in
  both_package' _ _ (G1MUL,(g1mul_inp,g1mul_out)) temp_package_both.
Fail Next Obligation.


Notation "'g1neg_inp'" :=(g1_t : choice_type) (in custom pack_type at level 2).
Notation "'g1neg_inp'" :=(g1_t : ChoiceEquality) (at level 2).
Notation "'g1neg_out'" :=(g1_t : choice_type) (in custom pack_type at level 2).
Notation "'g1neg_out'" :=(g1_t : ChoiceEquality) (at level 2).
Definition G1NEG : nat :=
  1897.
Program Definition g1neg
  : both_package (fset.fset0) [interface] [(G1NEG,(g1neg_inp,g1neg_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(p_1893) := temp_inp : g1_t in
    
    ((letb '(x_1894, y_1895, inf_1896) : (fp_t '× fp_t '× bool_ChoiceEquality
          ) :=
          lift_to_both0 p_1893 in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
            lift_to_both0 x_1894,
            (nat_mod_zero ) -% (lift_to_both0 y_1895),
            lift_to_both0 inf_1896
          ))
        ) : both (fset.fset0) [interface] (g1_t)))in
  both_package' _ _ (G1NEG,(g1neg_inp,g1neg_out)) temp_package_both.
Fail Next Obligation.


Notation "'g2add_a_inp'" :=(
  g2_t '× g2_t : choice_type) (in custom pack_type at level 2).
Notation "'g2add_a_inp'" :=(g2_t '× g2_t : ChoiceEquality) (at level 2).
Notation "'g2add_a_out'" :=(
  g2_t : choice_type) (in custom pack_type at level 2).
Notation "'g2add_a_out'" :=(g2_t : ChoiceEquality) (at level 2).
Definition G2ADD_A : nat :=
  1913.
Program Definition g2add_a
  : both_package (fset.fset0) [interface
  #val #[ FP2INV ] : fp2inv_inp → fp2inv_out ;
  #val #[ FP2MUL ] : fp2mul_inp → fp2mul_out ;
  #val #[ FP2SUB ] : fp2sub_inp → fp2sub_out ] [(G2ADD_A,(
      g2add_a_inp,g2add_a_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(p_1898 , q_1901) := temp_inp : g2_t '× g2_t in
    
    let fp2inv := fun x_0 => package_both fp2inv (x_0) in
    let fp2mul := fun x_0 x_1 => package_both fp2mul (x_0,x_1) in
    let fp2sub := fun x_0 x_1 => package_both fp2sub (x_0,x_1) in
    ((letb '(x1_1899, y1_1900, _) : (fp2_t '× fp2_t '× bool_ChoiceEquality) :=
          lift_to_both0 p_1898 in
        letb '(x2_1902, y2_1903, _) : (fp2_t '× fp2_t '× bool_ChoiceEquality
          ) :=
          lift_to_both0 q_1901 in
        letb x_diff_1904 : (fp_t '× fp_t) :=
          fp2sub (lift_to_both0 x2_1902) (lift_to_both0 x1_1899) in
        letb y_diff_1905 : (fp_t '× fp_t) :=
          fp2sub (lift_to_both0 y2_1903) (lift_to_both0 y1_1900) in
        letb xovery_1906 : (fp_t '× fp_t) :=
          fp2mul (lift_to_both0 y_diff_1905) (fp2inv (
              lift_to_both0 x_diff_1904)) in
        letb t1_1907 : (fp_t '× fp_t) :=
          fp2mul (lift_to_both0 xovery_1906) (lift_to_both0 xovery_1906) in
        letb t2_1908 : (fp_t '× fp_t) :=
          fp2sub (lift_to_both0 t1_1907) (lift_to_both0 x1_1899) in
        letb x3_1909 : (fp_t '× fp_t) :=
          fp2sub (lift_to_both0 t2_1908) (lift_to_both0 x2_1902) in
        letb t1_1910 : (fp_t '× fp_t) :=
          fp2sub (lift_to_both0 x1_1899) (lift_to_both0 x3_1909) in
        letb t2_1911 : (fp_t '× fp_t) :=
          fp2mul (lift_to_both0 xovery_1906) (lift_to_both0 t1_1910) in
        letb y3_1912 : (fp_t '× fp_t) :=
          fp2sub (lift_to_both0 t2_1911) (lift_to_both0 y1_1900) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
            lift_to_both0 x3_1909,
            lift_to_both0 y3_1912,
            lift_to_both0 ((false : bool_ChoiceEquality))
          ))
        ) : both (fset.fset0) [interface
      #val #[ FP2INV ] : fp2inv_inp → fp2inv_out ;
      #val #[ FP2MUL ] : fp2mul_inp → fp2mul_out ;
      #val #[ FP2SUB ] : fp2sub_inp → fp2sub_out ] (g2_t)))in
  both_package' _ _ (G2ADD_A,(g2add_a_inp,g2add_a_out)) temp_package_both.
Fail Next Obligation.


Notation "'g2double_a_inp'" :=(
  g2_t : choice_type) (in custom pack_type at level 2).
Notation "'g2double_a_inp'" :=(g2_t : ChoiceEquality) (at level 2).
Notation "'g2double_a_out'" :=(
  g2_t : choice_type) (in custom pack_type at level 2).
Notation "'g2double_a_out'" :=(g2_t : ChoiceEquality) (at level 2).
Definition G2DOUBLE_A : nat :=
  1927.
Program Definition g2double_a
  : both_package (fset.fset0) [interface
  #val #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out ;
  #val #[ FP2INV ] : fp2inv_inp → fp2inv_out ;
  #val #[ FP2MUL ] : fp2mul_inp → fp2mul_out ;
  #val #[ FP2SUB ] : fp2sub_inp → fp2sub_out ] [(G2DOUBLE_A,(
      g2double_a_inp,g2double_a_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(p_1914) := temp_inp : g2_t in
    
    let fp2fromfp := fun x_0 => package_both fp2fromfp (x_0) in
    let fp2inv := fun x_0 => package_both fp2inv (x_0) in
    let fp2mul := fun x_0 x_1 => package_both fp2mul (x_0,x_1) in
    let fp2sub := fun x_0 x_1 => package_both fp2sub (x_0,x_1) in
    ((letb '(x1_1915, y1_1916, _) : (fp2_t '× fp2_t '× bool_ChoiceEquality) :=
          lift_to_both0 p_1914 in
        letb x12_1917 : (fp_t '× fp_t) :=
          fp2mul (lift_to_both0 x1_1915) (lift_to_both0 x1_1915) in
        letb t1_1918 : (fp_t '× fp_t) :=
          fp2mul (fp2fromfp (nat_mod_from_literal (
                0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab) (
                lift_to_both0 (@repr U128 3)))) (lift_to_both0 x12_1917) in
        letb t2_1919 : (fp_t '× fp_t) :=
          fp2inv (fp2mul (fp2fromfp (nat_mod_two )) (lift_to_both0 y1_1916)) in
        letb xovery_1920 : (fp_t '× fp_t) :=
          fp2mul (lift_to_both0 t1_1918) (lift_to_both0 t2_1919) in
        letb t1_1921 : (fp_t '× fp_t) :=
          fp2mul (lift_to_both0 xovery_1920) (lift_to_both0 xovery_1920) in
        letb t2_1922 : (fp_t '× fp_t) :=
          fp2mul (fp2fromfp (nat_mod_two )) (lift_to_both0 x1_1915) in
        letb x3_1923 : (fp_t '× fp_t) :=
          fp2sub (lift_to_both0 t1_1921) (lift_to_both0 t2_1922) in
        letb t1_1924 : (fp_t '× fp_t) :=
          fp2sub (lift_to_both0 x1_1915) (lift_to_both0 x3_1923) in
        letb t2_1925 : (fp_t '× fp_t) :=
          fp2mul (lift_to_both0 xovery_1920) (lift_to_both0 t1_1924) in
        letb y3_1926 : (fp_t '× fp_t) :=
          fp2sub (lift_to_both0 t2_1925) (lift_to_both0 y1_1916) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
            lift_to_both0 x3_1923,
            lift_to_both0 y3_1926,
            lift_to_both0 ((false : bool_ChoiceEquality))
          ))
        ) : both (fset.fset0) [interface
      #val #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out ;
      #val #[ FP2INV ] : fp2inv_inp → fp2inv_out ;
      #val #[ FP2MUL ] : fp2mul_inp → fp2mul_out ;
      #val #[ FP2SUB ] : fp2sub_inp → fp2sub_out ] (g2_t)))in
  both_package' _ _ (G2DOUBLE_A,(
      g2double_a_inp,g2double_a_out)) temp_package_both.
Fail Next Obligation.


Notation "'g2double_inp'" :=(
  g2_t : choice_type) (in custom pack_type at level 2).
Notation "'g2double_inp'" :=(g2_t : ChoiceEquality) (at level 2).
Notation "'g2double_out'" :=(
  g2_t : choice_type) (in custom pack_type at level 2).
Notation "'g2double_out'" :=(g2_t : ChoiceEquality) (at level 2).
Definition G2DOUBLE : nat :=
  1932.
Program Definition g2double
  : both_package (fset.fset0) [interface
  #val #[ FP2ZERO ] : fp2zero_inp → fp2zero_out ;
  #val #[ G2DOUBLE_A ] : g2double_a_inp → g2double_a_out ] [(G2DOUBLE,(
      g2double_inp,g2double_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(p_1928) := temp_inp : g2_t in
    
    let fp2zero := package_both fp2zero tt in
    let g2double_a := fun x_0 => package_both g2double_a (x_0) in
    ((letb '(x1_1929, y1_1930, inf1_1931) : (
            fp2_t '×
            fp2_t '×
            bool_ChoiceEquality
          ) :=
          lift_to_both0 p_1928 in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          if is_pure (I := [interface]) (((lift_to_both0 y1_1930) !=.? (
                fp2zero )) && (negb (lift_to_both0 inf1_1931)))
          then g2double_a (lift_to_both0 p_1928)
          else prod_b(
            fp2zero ,
            fp2zero ,
            lift_to_both0 ((true : bool_ChoiceEquality))
          ))
        ) : both (fset.fset0) [interface
      #val #[ FP2ZERO ] : fp2zero_inp → fp2zero_out ;
      #val #[ G2DOUBLE_A ] : g2double_a_inp → g2double_a_out ] (g2_t)))in
  both_package' _ _ (G2DOUBLE,(g2double_inp,g2double_out)) temp_package_both.
Fail Next Obligation.


Notation "'g2add_inp'" :=(
  g2_t '× g2_t : choice_type) (in custom pack_type at level 2).
Notation "'g2add_inp'" :=(g2_t '× g2_t : ChoiceEquality) (at level 2).
Notation "'g2add_out'" :=(g2_t : choice_type) (in custom pack_type at level 2).
Notation "'g2add_out'" :=(g2_t : ChoiceEquality) (at level 2).
Definition G2ADD : nat :=
  1941.
Program Definition g2add
  : both_package (fset.fset0) [interface
  #val #[ FP2NEG ] : fp2neg_inp → fp2neg_out ;
  #val #[ FP2ZERO ] : fp2zero_inp → fp2zero_out ;
  #val #[ G2ADD_A ] : g2add_a_inp → g2add_a_out ;
  #val #[ G2DOUBLE ] : g2double_inp → g2double_out ] [(G2ADD,(
      g2add_inp,g2add_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(p_1933 , q_1937) := temp_inp : g2_t '× g2_t in
    
    let fp2neg := fun x_0 => package_both fp2neg (x_0) in
    let fp2zero := package_both fp2zero tt in
    let g2add_a := fun x_0 x_1 => package_both g2add_a (x_0,x_1) in
    let g2double := fun x_0 => package_both g2double (x_0) in
    ((letb '(x1_1934, y1_1935, inf1_1936) : (
            fp2_t '×
            fp2_t '×
            bool_ChoiceEquality
          ) :=
          lift_to_both0 p_1933 in
        letb '(x2_1938, y2_1939, inf2_1940) : (
            fp2_t '×
            fp2_t '×
            bool_ChoiceEquality
          ) :=
          lift_to_both0 q_1937 in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          if is_pure (I := [interface]) (lift_to_both0 inf1_1936)
          then lift_to_both0 q_1937
          else if is_pure (I := [interface]) (lift_to_both0 inf2_1940)
          then lift_to_both0 p_1933
          else if is_pure (I := [interface]) ((lift_to_both0 p_1933) =.? (
              lift_to_both0 q_1937))
          then g2double (lift_to_both0 p_1933)
          else if is_pure (I := [interface]) (negb (((
                  lift_to_both0 x1_1934) =.? (lift_to_both0 x2_1938)) && ((
                  lift_to_both0 y1_1935) =.? (fp2neg (lift_to_both0 y2_1939)))))
          then g2add_a (lift_to_both0 p_1933) (lift_to_both0 q_1937)
          else prod_b(
            fp2zero ,
            fp2zero ,
            lift_to_both0 ((true : bool_ChoiceEquality))
          ))
        ) : both (fset.fset0) [interface
      #val #[ FP2NEG ] : fp2neg_inp → fp2neg_out ;
      #val #[ FP2ZERO ] : fp2zero_inp → fp2zero_out ;
      #val #[ G2ADD_A ] : g2add_a_inp → g2add_a_out ;
      #val #[ G2DOUBLE ] : g2double_inp → g2double_out ] (g2_t)))in
  both_package' _ _ (G2ADD,(g2add_inp,g2add_out)) temp_package_both.
Fail Next Obligation.

Definition t_1942_loc : ChoiceEqualityLocation :=
  ((fp2_t '× fp2_t '× bool_ChoiceEquality) ; 1943%nat).
Notation "'g2mul_inp'" :=(
  scalar_t '× g2_t : choice_type) (in custom pack_type at level 2).
Notation "'g2mul_inp'" :=(scalar_t '× g2_t : ChoiceEquality) (at level 2).
Notation "'g2mul_out'" :=(g2_t : choice_type) (in custom pack_type at level 2).
Notation "'g2mul_out'" :=(g2_t : ChoiceEquality) (at level 2).
Definition G2MUL : nat :=
  1947.
Program Definition g2mul
  : both_package (CEfset ([t_1942_loc])) [interface
  #val #[ FP2ZERO ] : fp2zero_inp → fp2zero_out ;
  #val #[ G2ADD ] : g2add_inp → g2add_out ;
  #val #[ G2DOUBLE ] : g2double_inp → g2double_out ] [(G2MUL,(
      g2mul_inp,g2mul_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(m_1945 , p_1946) := temp_inp : scalar_t '× g2_t in
    
    let fp2zero := package_both fp2zero tt in
    let g2add := fun x_0 x_1 => package_both g2add (x_0,x_1) in
    let g2double := fun x_0 => package_both g2double (x_0) in
    ((letbm t_1942 : (fp2_t '× fp2_t '× bool_ChoiceEquality
          ) loc( t_1942_loc ) :=
          prod_b(
            fp2zero ,
            fp2zero ,
            lift_to_both0 ((true : bool_ChoiceEquality))
          ) in
        letb t_1942 :=
          foldi_both' (lift_to_both0 (usize 0)) (lift_to_both0 (
                usize 256)) t_1942 (L := (CEfset ([t_1942_loc]))) (I := (
              [interface #val #[ FP2ZERO ] : fp2zero_inp → fp2zero_out ;
              #val #[ G2ADD ] : g2add_inp → g2add_out ;
              #val #[ G2DOUBLE ] : g2double_inp → g2double_out
              ])) (fun i_1944 t_1942 =>
            letbm t_1942 loc( t_1942_loc ) := g2double (lift_to_both0 t_1942) in
            letb 't_1942 :=
              if nat_mod_bit (lift_to_both0 m_1945) ((lift_to_both0 (
                    usize 255)) .- (lift_to_both0 i_1944)) :bool_ChoiceEquality
              then lift_scope (L1 := CEfset ([t_1942_loc])) (L2 := CEfset (
                [t_1942_loc])) (I1 := [interface
              #val #[ G2ADD ] : g2add_inp → g2add_out ]) (I2 := [interface
              #val #[ G2ADD ] : g2add_inp → g2add_out ;
              #val #[ G2DOUBLE ] : g2double_inp → g2double_out
              ]) (H_loc_incl := _) (H_opsig_incl := _) (
                letbm t_1942 loc( t_1942_loc ) :=
                  g2add (lift_to_both0 t_1942) (lift_to_both0 p_1946) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                  lift_to_both0 t_1942)
                )
              else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                lift_to_both0 t_1942)
               in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 t_1942)
            ) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 t_1942)
        ) : both (CEfset ([t_1942_loc])) [interface
      #val #[ FP2ZERO ] : fp2zero_inp → fp2zero_out ;
      #val #[ G2ADD ] : g2add_inp → g2add_out ;
      #val #[ G2DOUBLE ] : g2double_inp → g2double_out ] (g2_t)))in
  both_package' _ _ (G2MUL,(g2mul_inp,g2mul_out)) temp_package_both.
Fail Next Obligation.


Notation "'g2neg_inp'" :=(g2_t : choice_type) (in custom pack_type at level 2).
Notation "'g2neg_inp'" :=(g2_t : ChoiceEquality) (at level 2).
Notation "'g2neg_out'" :=(g2_t : choice_type) (in custom pack_type at level 2).
Notation "'g2neg_out'" :=(g2_t : ChoiceEquality) (at level 2).
Definition G2NEG : nat :=
  1952.
Program Definition g2neg
  : both_package (fset.fset0) [interface
  #val #[ FP2NEG ] : fp2neg_inp → fp2neg_out ] [(G2NEG,(
      g2neg_inp,g2neg_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(p_1948) := temp_inp : g2_t in
    
    let fp2neg := fun x_0 => package_both fp2neg (x_0) in
    ((letb '(x_1949, y_1950, inf_1951) : (
            fp2_t '×
            fp2_t '×
            bool_ChoiceEquality
          ) :=
          lift_to_both0 p_1948 in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
            lift_to_both0 x_1949,
            fp2neg (lift_to_both0 y_1950),
            lift_to_both0 inf_1951
          ))
        ) : both (fset.fset0) [interface
      #val #[ FP2NEG ] : fp2neg_inp → fp2neg_out ] (g2_t)))in
  both_package' _ _ (G2NEG,(g2neg_inp,g2neg_out)) temp_package_both.
Fail Next Obligation.


Notation "'twist_inp'" :=(g1_t : choice_type) (in custom pack_type at level 2).
Notation "'twist_inp'" :=(g1_t : ChoiceEquality) (at level 2).
Notation "'twist_out'" :=((fp12_t '× fp12_t
  ) : choice_type) (in custom pack_type at level 2).
Notation "'twist_out'" :=((fp12_t '× fp12_t) : ChoiceEquality) (at level 2).
Definition TWIST : nat :=
  1958.
Program Definition twist
  : both_package (fset.fset0) [interface
  #val #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out ;
  #val #[ FP2ZERO ] : fp2zero_inp → fp2zero_out ;
  #val #[ FP6ZERO ] : fp6zero_inp → fp6zero_out ] [(TWIST,(
      twist_inp,twist_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(p_1953) := temp_inp : g1_t in
    
    let fp2fromfp := fun x_0 => package_both fp2fromfp (x_0) in
    let fp2zero := package_both fp2zero tt in
    let fp6zero := package_both fp6zero tt in
    ((letb '(p0_1954, p1_1955, _) : (fp_t '× fp_t '× bool_ChoiceEquality) :=
          lift_to_both0 p_1953 in
        letb x_1956 : ((fp2_t '× fp2_t '× fp2_t) '× fp6_t) :=
          prod_b(
            prod_b(fp2zero , fp2fromfp (lift_to_both0 p0_1954), fp2zero ),
            fp6zero 
          ) in
        letb y_1957 : (fp6_t '× (fp2_t '× fp2_t '× fp2_t)) :=
          prod_b(
            fp6zero ,
            prod_b(fp2zero , fp2fromfp (lift_to_both0 p1_1955), fp2zero )
          ) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
            lift_to_both0 x_1956,
            lift_to_both0 y_1957
          ))
        ) : both (fset.fset0) [interface
      #val #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out ;
      #val #[ FP2ZERO ] : fp2zero_inp → fp2zero_out ;
      #val #[ FP6ZERO ] : fp6zero_inp → fp6zero_out ] ((fp12_t '× fp12_t
        ))))in
  both_package' _ _ (TWIST,(twist_inp,twist_out)) temp_package_both.
Fail Next Obligation.


Notation "'line_double_p_inp'" :=(
  g2_t '× g1_t : choice_type) (in custom pack_type at level 2).
Notation "'line_double_p_inp'" :=(g2_t '× g1_t : ChoiceEquality) (at level 2).
Notation "'line_double_p_out'" :=(
  fp12_t : choice_type) (in custom pack_type at level 2).
Notation "'line_double_p_out'" :=(fp12_t : ChoiceEquality) (at level 2).
Definition LINE_DOUBLE_P : nat :=
  1970.
Program Definition line_double_p
  : both_package (fset.fset0) [interface
  #val #[ FP12FROMFP6 ] : fp12fromfp6_inp → fp12fromfp6_out ;
  #val #[ FP12MUL ] : fp12mul_inp → fp12mul_out ;
  #val #[ FP12NEG ] : fp12neg_inp → fp12neg_out ;
  #val #[ FP12SUB ] : fp12sub_inp → fp12sub_out ;
  #val #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out ;
  #val #[ FP2INV ] : fp2inv_inp → fp2inv_out ;
  #val #[ FP2MUL ] : fp2mul_inp → fp2mul_out ;
  #val #[ FP2SUB ] : fp2sub_inp → fp2sub_out ;
  #val #[ FP6FROMFP2 ] : fp6fromfp2_inp → fp6fromfp2_out ;
  #val #[ TWIST ] : twist_inp → twist_out ] [(LINE_DOUBLE_P,(
      line_double_p_inp,line_double_p_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(r_1959 , p_1967) := temp_inp : g2_t '× g1_t in
    
    let fp12fromfp6 := fun x_0 => package_both fp12fromfp6 (x_0) in
    let fp12mul := fun x_0 x_1 => package_both fp12mul (x_0,x_1) in
    let fp12neg := fun x_0 => package_both fp12neg (x_0) in
    let fp12sub := fun x_0 x_1 => package_both fp12sub (x_0,x_1) in
    let fp2fromfp := fun x_0 => package_both fp2fromfp (x_0) in
    let fp2inv := fun x_0 => package_both fp2inv (x_0) in
    let fp2mul := fun x_0 x_1 => package_both fp2mul (x_0,x_1) in
    let fp2sub := fun x_0 x_1 => package_both fp2sub (x_0,x_1) in
    let fp6fromfp2 := fun x_0 => package_both fp6fromfp2 (x_0) in
    let twist := fun x_0 => package_both twist (x_0) in
    ((letb '(r0_1960, r1_1961, _) : (fp2_t '× fp2_t '× bool_ChoiceEquality) :=
          lift_to_both0 r_1959 in
        letb a_1962 : (fp_t '× fp_t) :=
          fp2mul (fp2fromfp (nat_mod_from_literal (
                0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab) (
                lift_to_both0 (@repr U128 3)))) (fp2mul (
              lift_to_both0 r0_1960) (lift_to_both0 r0_1960)) in
        letb a_1963 : (fp_t '× fp_t) :=
          fp2mul (lift_to_both0 a_1962) (fp2inv (fp2mul (fp2fromfp (
                  nat_mod_two )) (lift_to_both0 r1_1961))) in
        letb b_1964 : (fp_t '× fp_t) :=
          fp2sub (lift_to_both0 r1_1961) (fp2mul (lift_to_both0 a_1963) (
              lift_to_both0 r0_1960)) in
        letb a_1965 : (fp6_t '× fp6_t) :=
          fp12fromfp6 (fp6fromfp2 (lift_to_both0 a_1963)) in
        letb b_1966 : (fp6_t '× fp6_t) :=
          fp12fromfp6 (fp6fromfp2 (lift_to_both0 b_1964)) in
        letb '(x_1968, y_1969) : (fp12_t '× fp12_t) :=
          twist (lift_to_both0 p_1967) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (fp12neg (fp12sub (
              fp12sub (lift_to_both0 y_1969) (fp12mul (lift_to_both0 a_1965) (
                  lift_to_both0 x_1968))) (lift_to_both0 b_1966)))
        ) : both (fset.fset0) [interface
      #val #[ FP12FROMFP6 ] : fp12fromfp6_inp → fp12fromfp6_out ;
      #val #[ FP12MUL ] : fp12mul_inp → fp12mul_out ;
      #val #[ FP12NEG ] : fp12neg_inp → fp12neg_out ;
      #val #[ FP12SUB ] : fp12sub_inp → fp12sub_out ;
      #val #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out ;
      #val #[ FP2INV ] : fp2inv_inp → fp2inv_out ;
      #val #[ FP2MUL ] : fp2mul_inp → fp2mul_out ;
      #val #[ FP2SUB ] : fp2sub_inp → fp2sub_out ;
      #val #[ FP6FROMFP2 ] : fp6fromfp2_inp → fp6fromfp2_out ;
      #val #[ TWIST ] : twist_inp → twist_out ] (fp12_t)))in
  both_package' _ _ (LINE_DOUBLE_P,(
      line_double_p_inp,line_double_p_out)) temp_package_both.
Fail Next Obligation.


Notation "'line_add_p_inp'" :=(
  g2_t '× g2_t '× g1_t : choice_type) (in custom pack_type at level 2).
Notation "'line_add_p_inp'" :=(
  g2_t '× g2_t '× g1_t : ChoiceEquality) (at level 2).
Notation "'line_add_p_out'" :=(
  fp12_t : choice_type) (in custom pack_type at level 2).
Notation "'line_add_p_out'" :=(fp12_t : ChoiceEquality) (at level 2).
Definition LINE_ADD_P : nat :=
  1984.
Program Definition line_add_p
  : both_package (fset.fset0) [interface
  #val #[ FP12FROMFP6 ] : fp12fromfp6_inp → fp12fromfp6_out ;
  #val #[ FP12MUL ] : fp12mul_inp → fp12mul_out ;
  #val #[ FP12NEG ] : fp12neg_inp → fp12neg_out ;
  #val #[ FP12SUB ] : fp12sub_inp → fp12sub_out ;
  #val #[ FP2INV ] : fp2inv_inp → fp2inv_out ;
  #val #[ FP2MUL ] : fp2mul_inp → fp2mul_out ;
  #val #[ FP2SUB ] : fp2sub_inp → fp2sub_out ;
  #val #[ FP6FROMFP2 ] : fp6fromfp2_inp → fp6fromfp2_out ;
  #val #[ TWIST ] : twist_inp → twist_out ] [(LINE_ADD_P,(
      line_add_p_inp,line_add_p_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(r_1971 , q_1974 , p_1981) := temp_inp : g2_t '× g2_t '× g1_t in
    
    let fp12fromfp6 := fun x_0 => package_both fp12fromfp6 (x_0) in
    let fp12mul := fun x_0 x_1 => package_both fp12mul (x_0,x_1) in
    let fp12neg := fun x_0 => package_both fp12neg (x_0) in
    let fp12sub := fun x_0 x_1 => package_both fp12sub (x_0,x_1) in
    let fp2inv := fun x_0 => package_both fp2inv (x_0) in
    let fp2mul := fun x_0 x_1 => package_both fp2mul (x_0,x_1) in
    let fp2sub := fun x_0 x_1 => package_both fp2sub (x_0,x_1) in
    let fp6fromfp2 := fun x_0 => package_both fp6fromfp2 (x_0) in
    let twist := fun x_0 => package_both twist (x_0) in
    ((letb '(r0_1972, r1_1973, _) : (fp2_t '× fp2_t '× bool_ChoiceEquality) :=
          lift_to_both0 r_1971 in
        letb '(q0_1975, q1_1976, _) : (fp2_t '× fp2_t '× bool_ChoiceEquality
          ) :=
          lift_to_both0 q_1974 in
        letb a_1977 : (fp_t '× fp_t) :=
          fp2mul (fp2sub (lift_to_both0 q1_1976) (lift_to_both0 r1_1973)) (
            fp2inv (fp2sub (lift_to_both0 q0_1975) (lift_to_both0 r0_1972))) in
        letb b_1978 : (fp_t '× fp_t) :=
          fp2sub (lift_to_both0 r1_1973) (fp2mul (lift_to_both0 a_1977) (
              lift_to_both0 r0_1972)) in
        letb a_1979 : (fp6_t '× fp6_t) :=
          fp12fromfp6 (fp6fromfp2 (lift_to_both0 a_1977)) in
        letb b_1980 : (fp6_t '× fp6_t) :=
          fp12fromfp6 (fp6fromfp2 (lift_to_both0 b_1978)) in
        letb '(x_1982, y_1983) : (fp12_t '× fp12_t) :=
          twist (lift_to_both0 p_1981) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (fp12neg (fp12sub (
              fp12sub (lift_to_both0 y_1983) (fp12mul (lift_to_both0 a_1979) (
                  lift_to_both0 x_1982))) (lift_to_both0 b_1980)))
        ) : both (fset.fset0) [interface
      #val #[ FP12FROMFP6 ] : fp12fromfp6_inp → fp12fromfp6_out ;
      #val #[ FP12MUL ] : fp12mul_inp → fp12mul_out ;
      #val #[ FP12NEG ] : fp12neg_inp → fp12neg_out ;
      #val #[ FP12SUB ] : fp12sub_inp → fp12sub_out ;
      #val #[ FP2INV ] : fp2inv_inp → fp2inv_out ;
      #val #[ FP2MUL ] : fp2mul_inp → fp2mul_out ;
      #val #[ FP2SUB ] : fp2sub_inp → fp2sub_out ;
      #val #[ FP6FROMFP2 ] : fp6fromfp2_inp → fp6fromfp2_out ;
      #val #[ TWIST ] : twist_inp → twist_out ] (fp12_t)))in
  both_package' _ _ (LINE_ADD_P,(
      line_add_p_inp,line_add_p_out)) temp_package_both.
Fail Next Obligation.


Notation "'frobenius_inp'" :=(
  fp12_t : choice_type) (in custom pack_type at level 2).
Notation "'frobenius_inp'" :=(fp12_t : ChoiceEquality) (at level 2).
Notation "'frobenius_out'" :=(
  fp12_t : choice_type) (in custom pack_type at level 2).
Notation "'frobenius_out'" :=(fp12_t : ChoiceEquality) (at level 2).
Definition FROBENIUS : nat :=
  2014.
Program Definition frobenius
  : both_package (fset.fset0) [interface
  #val #[ FP2CONJUGATE ] : fp2conjugate_inp → fp2conjugate_out ;
  #val #[ FP2MUL ] : fp2mul_inp → fp2mul_out ] [(FROBENIUS,(
      frobenius_inp,frobenius_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(f_1985) := temp_inp : fp12_t in
    
    let fp2conjugate := fun x_0 => package_both fp2conjugate (x_0) in
    let fp2mul := fun x_0 x_1 => package_both fp2mul (x_0,x_1) in
    ((letb '((g0_1986, g1_1987, g2_1988), (h0_1989, h1_1990, h2_1991)) : (
            fp6_t '×
            fp6_t
          ) :=
          lift_to_both0 f_1985 in
        letb t1_1992 : (fp_t '× fp_t) :=
          fp2conjugate (lift_to_both0 g0_1986) in
        letb t2_1993 : (fp_t '× fp_t) :=
          fp2conjugate (lift_to_both0 h0_1989) in
        letb t3_1994 : (fp_t '× fp_t) :=
          fp2conjugate (lift_to_both0 g1_1987) in
        letb t4_1995 : (fp_t '× fp_t) :=
          fp2conjugate (lift_to_both0 h1_1990) in
        letb t5_1996 : (fp_t '× fp_t) :=
          fp2conjugate (lift_to_both0 g2_1988) in
        letb t6_1997 : (fp_t '× fp_t) :=
          fp2conjugate (lift_to_both0 h2_1991) in
        letb c1_1998 : array_fp_t :=
          array_from_list uint64 ([
              (secret (lift_to_both0 (
                    @repr U64 10162220747404304312))) : uint64;
              (secret (lift_to_both0 (
                    @repr U64 17761815663483519293))) : uint64;
              (secret (lift_to_both0 (@repr U64 8873291758750579140))) : uint64;
              (secret (lift_to_both0 (@repr U64 1141103941765652303))) : uint64;
              (secret (lift_to_both0 (
                    @repr U64 13993175198059990303))) : uint64;
              (secret (lift_to_both0 (@repr U64 1802798568193066599))) : uint64
            ]) in
        letb c1_1999 : seq uint8 := array_to_le_bytes (lift_to_both0 c1_1998) in
        letb c1_2000 : fp_t :=
          nat_mod_from_byte_seq_le (lift_to_both0 c1_1999) in
        letb c2_2001 : array_fp_t :=
          array_from_list uint64 ([
              (secret (lift_to_both0 (@repr U64 3240210268673559283))) : uint64;
              (secret (lift_to_both0 (@repr U64 2895069921743240898))) : uint64;
              (secret (lift_to_both0 (
                    @repr U64 17009126888523054175))) : uint64;
              (secret (lift_to_both0 (@repr U64 6098234018649060207))) : uint64;
              (secret (lift_to_both0 (@repr U64 9865672654120263608))) : uint64;
              (secret (lift_to_both0 (@repr U64 71000049454473266))) : uint64
            ]) in
        letb c2_2002 : seq uint8 := array_to_le_bytes (lift_to_both0 c2_2001) in
        letb c2_2003 : fp_t :=
          nat_mod_from_byte_seq_le (lift_to_both0 c2_2002) in
        letb gamma11_2004 : (fp_t '× fp_t) :=
          prod_b(lift_to_both0 c1_2000, lift_to_both0 c2_2003) in
        letb gamma12_2005 : (fp_t '× fp_t) :=
          fp2mul (lift_to_both0 gamma11_2004) (lift_to_both0 gamma11_2004) in
        letb gamma13_2006 : (fp_t '× fp_t) :=
          fp2mul (lift_to_both0 gamma12_2005) (lift_to_both0 gamma11_2004) in
        letb gamma14_2007 : (fp_t '× fp_t) :=
          fp2mul (lift_to_both0 gamma13_2006) (lift_to_both0 gamma11_2004) in
        letb gamma15_2008 : (fp_t '× fp_t) :=
          fp2mul (lift_to_both0 gamma14_2007) (lift_to_both0 gamma11_2004) in
        letb t2_2009 : (fp_t '× fp_t) :=
          fp2mul (lift_to_both0 t2_1993) (lift_to_both0 gamma11_2004) in
        letb t3_2010 : (fp_t '× fp_t) :=
          fp2mul (lift_to_both0 t3_1994) (lift_to_both0 gamma12_2005) in
        letb t4_2011 : (fp_t '× fp_t) :=
          fp2mul (lift_to_both0 t4_1995) (lift_to_both0 gamma13_2006) in
        letb t5_2012 : (fp_t '× fp_t) :=
          fp2mul (lift_to_both0 t5_1996) (lift_to_both0 gamma14_2007) in
        letb t6_2013 : (fp_t '× fp_t) :=
          fp2mul (lift_to_both0 t6_1997) (lift_to_both0 gamma15_2008) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
            prod_b(
              lift_to_both0 t1_1992,
              lift_to_both0 t3_2010,
              lift_to_both0 t5_2012
            ),
            prod_b(
              lift_to_both0 t2_2009,
              lift_to_both0 t4_2011,
              lift_to_both0 t6_2013
            )
          ))
        ) : both (fset.fset0) [interface
      #val #[ FP2CONJUGATE ] : fp2conjugate_inp → fp2conjugate_out ;
      #val #[ FP2MUL ] : fp2mul_inp → fp2mul_out ] (fp12_t)))in
  both_package' _ _ (FROBENIUS,(frobenius_inp,frobenius_out)) temp_package_both.
Fail Next Obligation.


Notation "'final_exponentiation_inp'" :=(
  fp12_t : choice_type) (in custom pack_type at level 2).
Notation "'final_exponentiation_inp'" :=(fp12_t : ChoiceEquality) (at level 2).
Notation "'final_exponentiation_out'" :=(
  fp12_t : choice_type) (in custom pack_type at level 2).
Notation "'final_exponentiation_out'" :=(fp12_t : ChoiceEquality) (at level 2).
Definition FINAL_EXPONENTIATION : nat :=
  2049.
Program Definition final_exponentiation
  : both_package (CEfset ([])) [interface
  #val #[ FP12CONJUGATE ] : fp12conjugate_inp → fp12conjugate_out ;
  #val #[ FP12EXP ] : fp12exp_inp → fp12exp_out ;
  #val #[ FP12INV ] : fp12inv_inp → fp12inv_out ;
  #val #[ FP12MUL ] : fp12mul_inp → fp12mul_out ;
  #val #[ FROBENIUS ] : frobenius_inp → frobenius_out ] [(
    FINAL_EXPONENTIATION,(
      final_exponentiation_inp,final_exponentiation_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(f_2015) := temp_inp : fp12_t in
    
    let fp12conjugate := fun x_0 => package_both fp12conjugate (x_0) in
    let fp12exp := fun x_0 x_1 => package_both fp12exp (x_0,x_1) in
    let fp12inv := fun x_0 => package_both fp12inv (x_0) in
    let fp12mul := fun x_0 x_1 => package_both fp12mul (x_0,x_1) in
    let frobenius := fun x_0 => package_both frobenius (x_0) in
    ((letb fp6_2016 : (fp6_t '× fp6_t) :=
          fp12conjugate (lift_to_both0 f_2015) in
        letb finv_2017 : (fp6_t '× fp6_t) := fp12inv (lift_to_both0 f_2015) in
        letb fp6_1_2018 : (fp6_t '× fp6_t) :=
          fp12mul (lift_to_both0 fp6_2016) (lift_to_both0 finv_2017) in
        letb fp8_2019 : (fp6_t '× fp6_t) :=
          frobenius (frobenius (lift_to_both0 fp6_1_2018)) in
        letb f_2020 : (fp6_t '× fp6_t) :=
          fp12mul (lift_to_both0 fp8_2019) (lift_to_both0 fp6_1_2018) in
        letb u_2021 : scalar_t :=
          nat_mod_from_literal (
            0x8000000000000000000000000000000000000000000000000000000000000000) (
            lift_to_both0 (@repr U128 15132376222941642752)) in
        letb u_half_2022 : scalar_t :=
          nat_mod_from_literal (
            0x8000000000000000000000000000000000000000000000000000000000000000) (
            lift_to_both0 (@repr U128 7566188111470821376)) in
        letb t0_2023 : (fp6_t '× fp6_t) :=
          fp12mul (lift_to_both0 f_2020) (lift_to_both0 f_2020) in
        letb t1_2024 : (fp6_t '× fp6_t) :=
          fp12exp (lift_to_both0 t0_2023) (lift_to_both0 u_2021) in
        letb t1_2025 : (fp6_t '× fp6_t) :=
          fp12conjugate (lift_to_both0 t1_2024) in
        letb t2_2026 : (fp6_t '× fp6_t) :=
          fp12exp (lift_to_both0 t1_2025) (lift_to_both0 u_half_2022) in
        letb t2_2027 : (fp6_t '× fp6_t) :=
          fp12conjugate (lift_to_both0 t2_2026) in
        letb t3_2028 : (fp6_t '× fp6_t) :=
          fp12conjugate (lift_to_both0 f_2020) in
        letb t1_2029 : (fp6_t '× fp6_t) :=
          fp12mul (lift_to_both0 t3_2028) (lift_to_both0 t1_2025) in
        letb t1_2030 : (fp6_t '× fp6_t) :=
          fp12conjugate (lift_to_both0 t1_2029) in
        letb t1_2031 : (fp6_t '× fp6_t) :=
          fp12mul (lift_to_both0 t1_2030) (lift_to_both0 t2_2027) in
        letb t2_2032 : (fp6_t '× fp6_t) :=
          fp12exp (lift_to_both0 t1_2031) (lift_to_both0 u_2021) in
        letb t2_2033 : (fp6_t '× fp6_t) :=
          fp12conjugate (lift_to_both0 t2_2032) in
        letb t3_2034 : (fp6_t '× fp6_t) :=
          fp12exp (lift_to_both0 t2_2033) (lift_to_both0 u_2021) in
        letb t3_2035 : (fp6_t '× fp6_t) :=
          fp12conjugate (lift_to_both0 t3_2034) in
        letb t1_2036 : (fp6_t '× fp6_t) :=
          fp12conjugate (lift_to_both0 t1_2031) in
        letb t3_2037 : (fp6_t '× fp6_t) :=
          fp12mul (lift_to_both0 t1_2036) (lift_to_both0 t3_2035) in
        letb t1_2038 : (fp6_t '× fp6_t) :=
          fp12conjugate (lift_to_both0 t1_2036) in
        letb t1_2039 : (fp6_t '× fp6_t) :=
          frobenius (frobenius (frobenius (lift_to_both0 t1_2038))) in
        letb t2_2040 : (fp6_t '× fp6_t) :=
          frobenius (frobenius (lift_to_both0 t2_2033)) in
        letb t1_2041 : (fp6_t '× fp6_t) :=
          fp12mul (lift_to_both0 t1_2039) (lift_to_both0 t2_2040) in
        letb t2_2042 : (fp6_t '× fp6_t) :=
          fp12exp (lift_to_both0 t3_2037) (lift_to_both0 u_2021) in
        letb t2_2043 : (fp6_t '× fp6_t) :=
          fp12conjugate (lift_to_both0 t2_2042) in
        letb t2_2044 : (fp6_t '× fp6_t) :=
          fp12mul (lift_to_both0 t2_2043) (lift_to_both0 t0_2023) in
        letb t2_2045 : (fp6_t '× fp6_t) :=
          fp12mul (lift_to_both0 t2_2044) (lift_to_both0 f_2020) in
        letb t1_2046 : (fp6_t '× fp6_t) :=
          fp12mul (lift_to_both0 t1_2041) (lift_to_both0 t2_2045) in
        letb t2_2047 : (fp6_t '× fp6_t) := frobenius (lift_to_both0 t3_2037) in
        letb t1_2048 : (fp6_t '× fp6_t) :=
          fp12mul (lift_to_both0 t1_2046) (lift_to_both0 t2_2047) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 t1_2048)
        ) : both (CEfset ([])) [interface
      #val #[ FP12CONJUGATE ] : fp12conjugate_inp → fp12conjugate_out ;
      #val #[ FP12EXP ] : fp12exp_inp → fp12exp_out ;
      #val #[ FP12INV ] : fp12inv_inp → fp12inv_out ;
      #val #[ FP12MUL ] : fp12mul_inp → fp12mul_out ;
      #val #[ FROBENIUS ] : frobenius_inp → frobenius_out ] (fp12_t)))in
  both_package' _ _ (FINAL_EXPONENTIATION,(
      final_exponentiation_inp,final_exponentiation_out)) temp_package_both.
Fail Next Obligation.

Definition r_2050_loc : ChoiceEqualityLocation :=
  ((fp2_t '× fp2_t '× bool_ChoiceEquality) ; 2052%nat).
Definition f_2051_loc : ChoiceEqualityLocation :=
  ((fp6_t '× fp6_t) ; 2053%nat).
Notation "'pairing_inp'" :=(
  g1_t '× g2_t : choice_type) (in custom pack_type at level 2).
Notation "'pairing_inp'" :=(g1_t '× g2_t : ChoiceEquality) (at level 2).
Notation "'pairing_out'" :=(
  fp12_t : choice_type) (in custom pack_type at level 2).
Notation "'pairing_out'" :=(fp12_t : ChoiceEquality) (at level 2).
Definition PAIRING : nat :=
  2060.
Program Definition pairing
  : both_package (CEfset ([r_2050_loc ; f_2051_loc])) [interface
  #val #[ FINAL_EXPONENTIATION ] : final_exponentiation_inp → final_exponentiation_out ;
  #val #[ FP12CONJUGATE ] : fp12conjugate_inp → fp12conjugate_out ;
  #val #[ FP12FROMFP6 ] : fp12fromfp6_inp → fp12fromfp6_out ;
  #val #[ FP12MUL ] : fp12mul_inp → fp12mul_out ;
  #val #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out ;
  #val #[ FP6FROMFP2 ] : fp6fromfp2_inp → fp6fromfp2_out ;
  #val #[ G2ADD ] : g2add_inp → g2add_out ;
  #val #[ G2DOUBLE ] : g2double_inp → g2double_out ;
  #val #[ LINE_ADD_P ] : line_add_p_inp → line_add_p_out ;
  #val #[ LINE_DOUBLE_P ] : line_double_p_inp → line_double_p_out ] [(
    PAIRING,(pairing_inp,pairing_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(p_2057 , q_2055) := temp_inp : g1_t '× g2_t in
    
    let final_exponentiation := fun x_0 => package_both final_exponentiation (
      x_0) in
    let fp12conjugate := fun x_0 => package_both fp12conjugate (x_0) in
    let fp12fromfp6 := fun x_0 => package_both fp12fromfp6 (x_0) in
    let fp12mul := fun x_0 x_1 => package_both fp12mul (x_0,x_1) in
    let fp2fromfp := fun x_0 => package_both fp2fromfp (x_0) in
    let fp6fromfp2 := fun x_0 => package_both fp6fromfp2 (x_0) in
    let g2add := fun x_0 x_1 => package_both g2add (x_0,x_1) in
    let g2double := fun x_0 => package_both g2double (x_0) in
    let line_add_p := fun x_0 x_1 x_2 => package_both line_add_p (
      x_0,x_1,x_2) in
    let line_double_p := fun x_0 x_1 => package_both line_double_p (x_0,x_1) in
    ((letb t_2054 : scalar_t :=
          nat_mod_from_literal (
            0x8000000000000000000000000000000000000000000000000000000000000000) (
            lift_to_both0 (@repr U128 15132376222941642752)) in
        letbm r_2050 : (fp2_t '× fp2_t '× bool_ChoiceEquality
          ) loc( r_2050_loc ) :=
          lift_to_both0 q_2055 in
        letbm f_2051 : (fp6_t '× fp6_t) loc( f_2051_loc ) :=
          fp12fromfp6 (fp6fromfp2 (fp2fromfp (nat_mod_one ))) in
        letb '(r_2050, f_2051) :=
          foldi_both' (lift_to_both0 (usize 1)) (lift_to_both0 (
                usize 64)) prod_ce(r_2050, f_2051) (L := (CEfset (
                [r_2050_loc ; f_2051_loc]))) (I := ([interface
              #val #[ FINAL_EXPONENTIATION ] : final_exponentiation_inp → final_exponentiation_out ;
              #val #[ FP12CONJUGATE ] : fp12conjugate_inp → fp12conjugate_out ;
              #val #[ FP12FROMFP6 ] : fp12fromfp6_inp → fp12fromfp6_out ;
              #val #[ FP12MUL ] : fp12mul_inp → fp12mul_out ;
              #val #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out ;
              #val #[ FP6FROMFP2 ] : fp6fromfp2_inp → fp6fromfp2_out ;
              #val #[ G2ADD ] : g2add_inp → g2add_out ;
              #val #[ G2DOUBLE ] : g2double_inp → g2double_out ;
              #val #[ LINE_ADD_P ] : line_add_p_inp → line_add_p_out ;
              #val #[ LINE_DOUBLE_P ] : line_double_p_inp → line_double_p_out
              ])) (fun i_2056 '(r_2050, f_2051) =>
            letb lrr_2058 : (fp6_t '× fp6_t) :=
              line_double_p (lift_to_both0 r_2050) (lift_to_both0 p_2057) in
            letbm r_2050 loc( r_2050_loc ) := g2double (lift_to_both0 r_2050) in
            letbm f_2051 loc( f_2051_loc ) :=
              fp12mul (fp12mul (lift_to_both0 f_2051) (lift_to_both0 f_2051)) (
                lift_to_both0 lrr_2058) in
            letb '(r_2050, f_2051) :=
              if nat_mod_bit (lift_to_both0 t_2054) (((lift_to_both0 (
                      usize 64)) .- (lift_to_both0 i_2056)) .- (lift_to_both0 (
                    usize 1))) :bool_ChoiceEquality
              then lift_scope (L1 := CEfset (
                [r_2050_loc ; f_2051_loc])) (L2 := CEfset (
                [r_2050_loc ; f_2051_loc])) (I1 := [interface
              #val #[ FP12MUL ] : fp12mul_inp → fp12mul_out ;
              #val #[ G2ADD ] : g2add_inp → g2add_out ;
              #val #[ LINE_ADD_P ] : line_add_p_inp → line_add_p_out
              ]) (I2 := [interface
              #val #[ FP12MUL ] : fp12mul_inp → fp12mul_out ;
              #val #[ G2ADD ] : g2add_inp → g2add_out ;
              #val #[ G2DOUBLE ] : g2double_inp → g2double_out ;
              #val #[ LINE_ADD_P ] : line_add_p_inp → line_add_p_out ;
              #val #[ LINE_DOUBLE_P ] : line_double_p_inp → line_double_p_out
              ]) (H_loc_incl := _) (H_opsig_incl := _) (letb lrq_2059 : (
                    fp6_t '×
                    fp6_t
                  ) :=
                  line_add_p (lift_to_both0 r_2050) (lift_to_both0 q_2055) (
                    lift_to_both0 p_2057) in
                letbm r_2050 loc( r_2050_loc ) :=
                  g2add (lift_to_both0 r_2050) (lift_to_both0 q_2055) in
                letbm f_2051 loc( f_2051_loc ) :=
                  fp12mul (lift_to_both0 f_2051) (lift_to_both0 lrq_2059) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                    lift_to_both0 r_2050,
                    lift_to_both0 f_2051
                  ))
                )
              else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                  lift_to_both0 r_2050,
                  lift_to_both0 f_2051
                ))
               in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                lift_to_both0 r_2050,
                lift_to_both0 f_2051
              ))
            ) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (final_exponentiation (
            fp12conjugate (lift_to_both0 f_2051)))
        ) : both (CEfset ([r_2050_loc ; f_2051_loc])) [interface
      #val #[ FINAL_EXPONENTIATION ] : final_exponentiation_inp → final_exponentiation_out ;
      #val #[ FP12CONJUGATE ] : fp12conjugate_inp → fp12conjugate_out ;
      #val #[ FP12FROMFP6 ] : fp12fromfp6_inp → fp12fromfp6_out ;
      #val #[ FP12MUL ] : fp12mul_inp → fp12mul_out ;
      #val #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out ;
      #val #[ FP6FROMFP2 ] : fp6fromfp2_inp → fp6fromfp2_out ;
      #val #[ G2ADD ] : g2add_inp → g2add_out ;
      #val #[ G2DOUBLE ] : g2double_inp → g2double_out ;
      #val #[ LINE_ADD_P ] : line_add_p_inp → line_add_p_out ;
      #val #[ LINE_DOUBLE_P ] : line_double_p_inp → line_double_p_out ] (
        fp12_t)))in
  both_package' _ _ (PAIRING,(pairing_inp,pairing_out)) temp_package_both.
Fail Next Obligation.


Notation "'test_fp2_prop_add_neg_inp'" :=(
  fp2_t : choice_type) (in custom pack_type at level 2).
Notation "'test_fp2_prop_add_neg_inp'" :=(fp2_t : ChoiceEquality) (at level 2).
Notation "'test_fp2_prop_add_neg_out'" :=(
  bool_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'test_fp2_prop_add_neg_out'" :=(
  bool_ChoiceEquality : ChoiceEquality) (at level 2).
Definition TEST_FP2_PROP_ADD_NEG : nat :=
  2063.
Program Definition test_fp2_prop_add_neg
  : both_package (fset.fset0) [interface
  #val #[ FP2ADD ] : fp2add_inp → fp2add_out ;
  #val #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out ;
  #val #[ FP2NEG ] : fp2neg_inp → fp2neg_out ] [(TEST_FP2_PROP_ADD_NEG,(
      test_fp2_prop_add_neg_inp,test_fp2_prop_add_neg_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(a_2061) := temp_inp : fp2_t in
    
    let fp2add := fun x_0 x_1 => package_both fp2add (x_0,x_1) in
    let fp2fromfp := fun x_0 => package_both fp2fromfp (x_0) in
    let fp2neg := fun x_0 => package_both fp2neg (x_0) in
    ((letb b_2062 : (fp_t '× fp_t) := fp2neg (lift_to_both0 a_2061) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) ((fp2fromfp (
              nat_mod_zero )) =.? (fp2add (lift_to_both0 a_2061) (
              lift_to_both0 b_2062)))
        ) : both (fset.fset0) [interface
      #val #[ FP2ADD ] : fp2add_inp → fp2add_out ;
      #val #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out ;
      #val #[ FP2NEG ] : fp2neg_inp → fp2neg_out ] (bool_ChoiceEquality)))in
  both_package' _ _ (TEST_FP2_PROP_ADD_NEG,(
      test_fp2_prop_add_neg_inp,test_fp2_prop_add_neg_out)) temp_package_both.
Fail Next Obligation.


Notation "'test_fp2_prop_mul_inv_inp'" :=(
  fp2_t : choice_type) (in custom pack_type at level 2).
Notation "'test_fp2_prop_mul_inv_inp'" :=(fp2_t : ChoiceEquality) (at level 2).
Notation "'test_fp2_prop_mul_inv_out'" :=(
  bool_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'test_fp2_prop_mul_inv_out'" :=(
  bool_ChoiceEquality : ChoiceEquality) (at level 2).
Definition TEST_FP2_PROP_MUL_INV : nat :=
  2066.
Program Definition test_fp2_prop_mul_inv
  : both_package (fset.fset0) [interface
  #val #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out ;
  #val #[ FP2INV ] : fp2inv_inp → fp2inv_out ;
  #val #[ FP2MUL ] : fp2mul_inp → fp2mul_out ] [(TEST_FP2_PROP_MUL_INV,(
      test_fp2_prop_mul_inv_inp,test_fp2_prop_mul_inv_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(a_2064) := temp_inp : fp2_t in
    
    let fp2fromfp := fun x_0 => package_both fp2fromfp (x_0) in
    let fp2inv := fun x_0 => package_both fp2inv (x_0) in
    let fp2mul := fun x_0 x_1 => package_both fp2mul (x_0,x_1) in
    ((letb b_2065 : (fp_t '× fp_t) := fp2inv (lift_to_both0 a_2064) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) ((fp2fromfp (
              nat_mod_one )) =.? (fp2mul (lift_to_both0 a_2064) (
              lift_to_both0 b_2065)))
        ) : both (fset.fset0) [interface
      #val #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out ;
      #val #[ FP2INV ] : fp2inv_inp → fp2inv_out ;
      #val #[ FP2MUL ] : fp2mul_inp → fp2mul_out ] (bool_ChoiceEquality)))in
  both_package' _ _ (TEST_FP2_PROP_MUL_INV,(
      test_fp2_prop_mul_inv_inp,test_fp2_prop_mul_inv_out)) temp_package_both.
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
  2068.
Program Definition test_extraction_issue
  : both_package (fset.fset0) [interface
  #val #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out ;
  #val #[ FP2INV ] : fp2inv_inp → fp2inv_out ;
  #val #[ FP2MUL ] : fp2mul_inp → fp2mul_out ] [(TEST_EXTRACTION_ISSUE,(
      test_extraction_issue_inp,test_extraction_issue_out))] :=
  let temp_package_both := (fun temp_inp => 
    
    let fp2fromfp := fun x_0 => package_both fp2fromfp (x_0) in
    let fp2inv := fun x_0 => package_both fp2inv (x_0) in
    let fp2mul := fun x_0 x_1 => package_both fp2mul (x_0,x_1) in
    ((letb b_2067 : (fp_t '× fp_t) :=
          fp2inv (prod_b(nat_mod_one , nat_mod_one )) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) ((fp2fromfp (
              nat_mod_one )) =.? (fp2mul (prod_b(nat_mod_one , nat_mod_one )) (
              lift_to_both0 b_2067)))
        ) : both (fset.fset0) [interface
      #val #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out ;
      #val #[ FP2INV ] : fp2inv_inp → fp2inv_out ;
      #val #[ FP2MUL ] : fp2mul_inp → fp2mul_out ] (bool_ChoiceEquality)))in
  both_package' _ _ (TEST_EXTRACTION_ISSUE,(
      test_extraction_issue_inp,test_extraction_issue_out)) temp_package_both.
Fail Next Obligation.


Notation "'test_fp6_prop_mul_inv_inp'" :=(
  fp6_t : choice_type) (in custom pack_type at level 2).
Notation "'test_fp6_prop_mul_inv_inp'" :=(fp6_t : ChoiceEquality) (at level 2).
Notation "'test_fp6_prop_mul_inv_out'" :=(
  bool_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'test_fp6_prop_mul_inv_out'" :=(
  bool_ChoiceEquality : ChoiceEquality) (at level 2).
Definition TEST_FP6_PROP_MUL_INV : nat :=
  2071.
Program Definition test_fp6_prop_mul_inv
  : both_package (fset.fset0) [interface
  #val #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out ;
  #val #[ FP6FROMFP2 ] : fp6fromfp2_inp → fp6fromfp2_out ;
  #val #[ FP6INV ] : fp6inv_inp → fp6inv_out ;
  #val #[ FP6MUL ] : fp6mul_inp → fp6mul_out ] [(TEST_FP6_PROP_MUL_INV,(
      test_fp6_prop_mul_inv_inp,test_fp6_prop_mul_inv_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(a_2069) := temp_inp : fp6_t in
    
    let fp2fromfp := fun x_0 => package_both fp2fromfp (x_0) in
    let fp6fromfp2 := fun x_0 => package_both fp6fromfp2 (x_0) in
    let fp6inv := fun x_0 => package_both fp6inv (x_0) in
    let fp6mul := fun x_0 x_1 => package_both fp6mul (x_0,x_1) in
    ((letb b_2070 : (fp2_t '× fp2_t '× fp2_t) :=
          fp6inv (lift_to_both0 a_2069) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) ((fp6fromfp2 (
              fp2fromfp (nat_mod_one ))) =.? (fp6mul (lift_to_both0 a_2069) (
              lift_to_both0 b_2070)))
        ) : both (fset.fset0) [interface
      #val #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out ;
      #val #[ FP6FROMFP2 ] : fp6fromfp2_inp → fp6fromfp2_out ;
      #val #[ FP6INV ] : fp6inv_inp → fp6inv_out ;
      #val #[ FP6MUL ] : fp6mul_inp → fp6mul_out ] (bool_ChoiceEquality)))in
  both_package' _ _ (TEST_FP6_PROP_MUL_INV,(
      test_fp6_prop_mul_inv_inp,test_fp6_prop_mul_inv_out)) temp_package_both.
Fail Next Obligation.


Notation "'test_fp6_prop_add_neg_inp'" :=(
  fp6_t : choice_type) (in custom pack_type at level 2).
Notation "'test_fp6_prop_add_neg_inp'" :=(fp6_t : ChoiceEquality) (at level 2).
Notation "'test_fp6_prop_add_neg_out'" :=(
  bool_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'test_fp6_prop_add_neg_out'" :=(
  bool_ChoiceEquality : ChoiceEquality) (at level 2).
Definition TEST_FP6_PROP_ADD_NEG : nat :=
  2074.
Program Definition test_fp6_prop_add_neg
  : both_package (fset.fset0) [interface
  #val #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out ;
  #val #[ FP6ADD ] : fp6add_inp → fp6add_out ;
  #val #[ FP6FROMFP2 ] : fp6fromfp2_inp → fp6fromfp2_out ;
  #val #[ FP6NEG ] : fp6neg_inp → fp6neg_out ] [(TEST_FP6_PROP_ADD_NEG,(
      test_fp6_prop_add_neg_inp,test_fp6_prop_add_neg_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(a_2072) := temp_inp : fp6_t in
    
    let fp2fromfp := fun x_0 => package_both fp2fromfp (x_0) in
    let fp6add := fun x_0 x_1 => package_both fp6add (x_0,x_1) in
    let fp6fromfp2 := fun x_0 => package_both fp6fromfp2 (x_0) in
    let fp6neg := fun x_0 => package_both fp6neg (x_0) in
    ((letb b_2073 : (fp2_t '× fp2_t '× fp2_t) :=
          fp6neg (lift_to_both0 a_2072) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) ((fp6fromfp2 (
              fp2fromfp (nat_mod_zero ))) =.? (fp6add (lift_to_both0 a_2072) (
              lift_to_both0 b_2073)))
        ) : both (fset.fset0) [interface
      #val #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out ;
      #val #[ FP6ADD ] : fp6add_inp → fp6add_out ;
      #val #[ FP6FROMFP2 ] : fp6fromfp2_inp → fp6fromfp2_out ;
      #val #[ FP6NEG ] : fp6neg_inp → fp6neg_out ] (bool_ChoiceEquality)))in
  both_package' _ _ (TEST_FP6_PROP_ADD_NEG,(
      test_fp6_prop_add_neg_inp,test_fp6_prop_add_neg_out)) temp_package_both.
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
  2077.
Program Definition test_fp12_prop_add_neg
  : both_package (fset.fset0) [interface
  #val #[ FP12ADD ] : fp12add_inp → fp12add_out ;
  #val #[ FP12FROMFP6 ] : fp12fromfp6_inp → fp12fromfp6_out ;
  #val #[ FP12NEG ] : fp12neg_inp → fp12neg_out ;
  #val #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out ;
  #val #[ FP6FROMFP2 ] : fp6fromfp2_inp → fp6fromfp2_out ] [(
    TEST_FP12_PROP_ADD_NEG,(
      test_fp12_prop_add_neg_inp,test_fp12_prop_add_neg_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(a_2075) := temp_inp : fp12_t in
    
    let fp12add := fun x_0 x_1 => package_both fp12add (x_0,x_1) in
    let fp12fromfp6 := fun x_0 => package_both fp12fromfp6 (x_0) in
    let fp12neg := fun x_0 => package_both fp12neg (x_0) in
    let fp2fromfp := fun x_0 => package_both fp2fromfp (x_0) in
    let fp6fromfp2 := fun x_0 => package_both fp6fromfp2 (x_0) in
    ((letb b_2076 : (fp6_t '× fp6_t) := fp12neg (lift_to_both0 a_2075) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) ((fp12fromfp6 (
              fp6fromfp2 (fp2fromfp (nat_mod_zero )))) =.? (fp12add (
              lift_to_both0 a_2075) (lift_to_both0 b_2076)))
        ) : both (fset.fset0) [interface
      #val #[ FP12ADD ] : fp12add_inp → fp12add_out ;
      #val #[ FP12FROMFP6 ] : fp12fromfp6_inp → fp12fromfp6_out ;
      #val #[ FP12NEG ] : fp12neg_inp → fp12neg_out ;
      #val #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out ;
      #val #[ FP6FROMFP2 ] : fp6fromfp2_inp → fp6fromfp2_out ] (
        bool_ChoiceEquality)))in
  both_package' _ _ (TEST_FP12_PROP_ADD_NEG,(
      test_fp12_prop_add_neg_inp,test_fp12_prop_add_neg_out)) temp_package_both.
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
  2080.
Program Definition test_fp12_prop_mul_inv
  : both_package (fset.fset0) [interface
  #val #[ FP12FROMFP6 ] : fp12fromfp6_inp → fp12fromfp6_out ;
  #val #[ FP12INV ] : fp12inv_inp → fp12inv_out ;
  #val #[ FP12MUL ] : fp12mul_inp → fp12mul_out ;
  #val #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out ;
  #val #[ FP6FROMFP2 ] : fp6fromfp2_inp → fp6fromfp2_out ] [(
    TEST_FP12_PROP_MUL_INV,(
      test_fp12_prop_mul_inv_inp,test_fp12_prop_mul_inv_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(a_2078) := temp_inp : fp12_t in
    
    let fp12fromfp6 := fun x_0 => package_both fp12fromfp6 (x_0) in
    let fp12inv := fun x_0 => package_both fp12inv (x_0) in
    let fp12mul := fun x_0 x_1 => package_both fp12mul (x_0,x_1) in
    let fp2fromfp := fun x_0 => package_both fp2fromfp (x_0) in
    let fp6fromfp2 := fun x_0 => package_both fp6fromfp2 (x_0) in
    ((letb b_2079 : (fp6_t '× fp6_t) := fp12inv (lift_to_both0 a_2078) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) ((fp12fromfp6 (
              fp6fromfp2 (fp2fromfp (nat_mod_one )))) =.? (fp12mul (
              lift_to_both0 a_2078) (lift_to_both0 b_2079)))
        ) : both (fset.fset0) [interface
      #val #[ FP12FROMFP6 ] : fp12fromfp6_inp → fp12fromfp6_out ;
      #val #[ FP12INV ] : fp12inv_inp → fp12inv_out ;
      #val #[ FP12MUL ] : fp12mul_inp → fp12mul_out ;
      #val #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out ;
      #val #[ FP6FROMFP2 ] : fp6fromfp2_inp → fp6fromfp2_out ] (
        bool_ChoiceEquality)))in
  both_package' _ _ (TEST_FP12_PROP_MUL_INV,(
      test_fp12_prop_mul_inv_inp,test_fp12_prop_mul_inv_out)) temp_package_both.
Fail Next Obligation.

