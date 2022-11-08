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
| MessageTooLarge : error_t
| DecryptionFailed : error_t
| VerificationFailed : error_t.

Definition eqb_error_t (x y : error_t) : bool :=
match x with
   | InvalidLength => match y with | InvalidLength=> true | _ => false end
   | MessageTooLarge => match y with | MessageTooLarge=> true | _ => false end
   | DecryptionFailed => match y with | DecryptionFailed=> true | _ => false end
   | VerificationFailed =>
       match y with
       | VerificationFailed=> true
       | _ => false
       end
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

Definition rsaep (pk_2375 : pk_t) (m_2376 : rsa_int_t) : rsa_int_result_t :=
  let '(n_2377, e_2378) :=
    pk_2375 in 
  (if ((m_2376) >.? ((n_2377) -% (nat_mod_one ))):bool then (
      @Err rsa_int_t error_t (MessageTooLarge)) else (@Ok rsa_int_t error_t (
        nat_mod_pow_mod (m_2376) (e_2378) (n_2377)))).

Definition rsadp (sk_2379 : sk_t) (c_2380 : rsa_int_t) : rsa_int_result_t :=
  let '(n_2381, d_2382) :=
    sk_2379 in 
  (if ((c_2380) >.? ((n_2381) -% (nat_mod_one ))):bool then (
      @Err rsa_int_t error_t (MessageTooLarge)) else (@Ok rsa_int_t error_t (
        nat_mod_pow_mod (c_2380) (d_2382) (n_2381)))).

Definition rsasp1 (sk_2383 : sk_t) (m_2384 : rsa_int_t) : rsa_int_result_t :=
  let '(n_2385, d_2386) :=
    sk_2383 in 
  (if ((m_2384) >.? ((n_2385) -% (nat_mod_one ))):bool then (
      @Err rsa_int_t error_t (MessageTooLarge)) else (@Ok rsa_int_t error_t (
        nat_mod_pow_mod (m_2384) (d_2386) (n_2385)))).

Definition rsavp1 (pk_2387 : pk_t) (s_2388 : rsa_int_t) : rsa_int_result_t :=
  let '(n_2389, e_2390) :=
    pk_2387 in 
  (if ((s_2388) >.? ((n_2389) -% (nat_mod_one ))):bool then (
      @Err rsa_int_t error_t (MessageTooLarge)) else (@Ok rsa_int_t error_t (
        nat_mod_pow_mod (s_2388) (e_2390) (n_2389)))).

Definition i2osp
  (x_2391 : rsa_int_t)
  (x_len_2392 : int32)
  : byte_seq_result_t :=
  (if (((x_2391) >=.? (nat_mod_exp (nat_mod_from_literal (0x) (
              @repr WORDSIZE128 256) : rsa_int_t) (x_len_2392))) && ((
          x_len_2392) !=.? (byte_size_v))):bool then (@Err byte_seq error_t (
        InvalidLength)) else (@Ok byte_seq error_t (seq_slice (
          nat_mod_to_byte_seq_be (x_2391)) (@cast _ uint32 _ ((byte_size_v) .- (
              x_len_2392))) (@cast _ uint32 _ (x_len_2392))))).

Definition os2ip (x_2393 : byte_seq) : rsa_int_t :=
  nat_mod_from_byte_seq_be (x_2393) : rsa_int_t.

Definition mgf1
  (mgf_seed_2394 : byte_seq)
  (mask_len_2395 : uint_size)
  : byte_seq_result_t :=
  let result_2396 : (result byte_seq error_t) :=
    @Err byte_seq error_t (InvalidLength) in 
  let '(result_2396) :=
    if (mask_len_2395) <.? ((usize 2) .^ ((usize 32) * (hlen_v))):bool then (
      let t_2397 : seq uint8 :=
        seq_new_ (default) (usize 0) in 
      let t_2397 :=
        foldi (usize 0) (((mask_len_2395) + (usize 32)) / (
              usize 32)) (fun i_2398 t_2397 =>
          let x_2399 : byte_seq :=
            i2osp (nat_mod_from_literal (0x) (pub_u128 (i_2398)) : rsa_int_t) (
              @repr WORDSIZE32 4) in 
          let t_2397 :=
            seq_concat (t_2397) (array_to_seq (sha256 (seq_concat (
                  mgf_seed_2394) (x_2399)))) in 
          (t_2397))
        t_2397 in 
      let result_2396 :=
        @Ok byte_seq error_t (seq_slice (t_2397) (usize 0) (mask_len_2395)) in 
      (result_2396)) else ((result_2396)) in 
  result_2396.

