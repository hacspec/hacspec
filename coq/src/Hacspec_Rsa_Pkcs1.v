(** This file was automatically generated using Hacspec **)
Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
Require Import Hacspec_Lib.

Require Import Hacspec_Sha256.

Definition bit_size_v : int32 :=
  @repr WORDSIZE32 2048.

Definition byte_size_v : int32 :=
  (@repr WORDSIZE32 2048) ./ (@repr WORDSIZE32 8).

Definition hlen_v : uint_size :=
  usize 32.

Definition rsa_int_t := nat_mod pow2 2048.

Inductive error_t :=
| InvalidLength : error_t
| MessageTooLarge : error_t.

Definition eqb_error_t (x y : error_t) : bool :=
match x with
   | InvalidLength => match y with | InvalidLength=> true | _ => false end
   | MessageTooLarge => match y with | MessageTooLarge=> true | _ => false end
   end.

Definition eqb_leibniz_error_t (x y : error_t) : eqb_error_t x y = true <-> x = y.
Proof. split. intros; destruct x ; destruct y ; try (f_equal ; apply eqb_leibniz) ; easy. intros ; subst ; destruct y ; try reflexivity ; try (apply eqb_refl). Qed.

Instance eq_dec_error_t : EqDec (error_t) :=
Build_EqDec (error_t) (eqb_error_t) (eqb_leibniz_error_t).


Notation "'pk_t'" := ((rsa_int_t × rsa_int_t)) : hacspec_scope.

Notation "'sk_t'" := ((rsa_int_t × rsa_int_t)) : hacspec_scope.

Notation "'key_pair_t'" := ((pk_t × sk_t)) : hacspec_scope.

Notation "'byte_seq_result_t'" := ((result byte_seq error_t)) : hacspec_scope.

Notation "'rsa_int_result_t'" := ((result rsa_int_t error_t)) : hacspec_scope.

Definition rsaep (pk_1929 : pk_t) (m_1930 : rsa_int_t) : rsa_int_result_t :=
  let '(n_1931, e_1932) :=
    pk_1929 in 
  (if ((m_1930) >.? ((n_1931) -% (nat_mod_one ))):bool then (
      @Err rsa_int_t error_t (MessageTooLarge)) else (@Ok rsa_int_t error_t (
        nat_mod_pow_mod (m_1930) (e_1932) (n_1931)))).

Definition rsadp (sk_1933 : sk_t) (c_1934 : rsa_int_t) : rsa_int_result_t :=
  let '(n_1935, d_1936) :=
    sk_1933 in 
  (if ((c_1934) >.? ((n_1935) -% (nat_mod_one ))):bool then (
      @Err rsa_int_t error_t (MessageTooLarge)) else (@Ok rsa_int_t error_t (
        nat_mod_pow_mod (c_1934) (d_1936) (n_1935)))).

Definition rsasp1 (sk_1937 : sk_t) (m_1938 : rsa_int_t) : rsa_int_result_t :=
  let '(n_1939, d_1940) :=
    sk_1937 in 
  (if ((m_1938) >.? ((n_1939) -% (nat_mod_one ))):bool then (
      @Err rsa_int_t error_t (MessageTooLarge)) else (@Ok rsa_int_t error_t (
        nat_mod_pow_mod (m_1938) (d_1940) (n_1939)))).

Definition rsavp1 (pk_1941 : pk_t) (s_1942 : rsa_int_t) : rsa_int_result_t :=
  let '(n_1943, e_1944) :=
    pk_1941 in 
  (if ((s_1942) >.? ((n_1943) -% (nat_mod_one ))):bool then (
      @Err rsa_int_t error_t (MessageTooLarge)) else (@Ok rsa_int_t error_t (
        nat_mod_pow_mod (s_1942) (e_1944) (n_1943)))).

Definition i2osp
  (x_1945 : rsa_int_t)
  (x_len_1946 : int32)
  : byte_seq_result_t :=
  (if (((x_1945) >=.? (nat_mod_exp (nat_mod_from_literal (0x) (
              @repr WORDSIZE128 256) : rsa_int_t) (x_len_1946))) && ((
          x_len_1946) !=.? (byte_size_v))):bool then (@Err byte_seq error_t (
        InvalidLength)) else (@Ok byte_seq error_t (seq_slice (
          nat_mod_to_byte_seq_be (x_1945)) (@cast _ uint32 _ ((byte_size_v) .- (
              x_len_1946))) (@cast _ uint32 _ (x_len_1946))))).

Definition os2ip (x_1947 : byte_seq) : rsa_int_t :=
  nat_mod_from_byte_seq_be (x_1947) : rsa_int_t.

Definition mgf1
  (mgf_seed_1948 : byte_seq)
  (mask_len_1949 : uint_size)
  : byte_seq_result_t :=
  let result_1950 : (result byte_seq error_t) :=
    @Err byte_seq error_t (InvalidLength) in 
  ifbnd (mask_len_1949) <.? ((usize 2) .^ ((usize 32) * (hlen_v))) : bool
  thenbnd (let t_1951 : seq uint8 :=
      seq_new_ (default) (usize 0) in 
    bind (foldibnd (usize 0) to (((mask_len_1949) + (usize 32)) / (
          usize 32)) for t_1951 >> (fun i_1952 t_1951 =>
      bind (i2osp (nat_mod_from_literal (0x) (pub_u128 (i_1952)) : rsa_int_t) (
          @repr WORDSIZE32 4)) (fun x_1953 => let t_1951 :=
          seq_concat (t_1951) (array_to_seq (sha256 (seq_concat (
                mgf_seed_1948) (x_1953)))) in 
        Ok ((t_1951))))) (fun t_1951 => let result_1950 :=
        @Ok byte_seq error_t (seq_slice (t_1951) (usize 0) (mask_len_1949)) in 
      Ok ((result_1950))))
  else ((result_1950)) >> (fun '(result_1950) =>
  result_1950).

