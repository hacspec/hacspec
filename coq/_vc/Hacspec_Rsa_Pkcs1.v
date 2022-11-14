(** This file was automatically generated using Hacspec **)
Set Warnings "-notation-overridden,-ambiguous-paths".
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

Definition rsaep (pk_2433 : pk_t) (m_2434 : rsa_int_t) : rsa_int_result_t :=
  let '(n_2435, e_2436) :=
    pk_2433 in 
  (if ((m_2434) >.? ((n_2435) -% (nat_mod_one ))):bool then (
      @Err rsa_int_t error_t (MessageTooLarge)) else (@Ok rsa_int_t error_t (
        nat_mod_pow_mod (m_2434) (e_2436) (n_2435)))).

Definition rsadp (sk_2437 : sk_t) (c_2438 : rsa_int_t) : rsa_int_result_t :=
  let '(n_2439, d_2440) :=
    sk_2437 in 
  (if ((c_2438) >.? ((n_2439) -% (nat_mod_one ))):bool then (
      @Err rsa_int_t error_t (MessageTooLarge)) else (@Ok rsa_int_t error_t (
        nat_mod_pow_mod (c_2438) (d_2440) (n_2439)))).

Definition rsasp1 (sk_2441 : sk_t) (m_2442 : rsa_int_t) : rsa_int_result_t :=
  let '(n_2443, d_2444) :=
    sk_2441 in 
  (if ((m_2442) >.? ((n_2443) -% (nat_mod_one ))):bool then (
      @Err rsa_int_t error_t (MessageTooLarge)) else (@Ok rsa_int_t error_t (
        nat_mod_pow_mod (m_2442) (d_2444) (n_2443)))).

Definition rsavp1 (pk_2445 : pk_t) (s_2446 : rsa_int_t) : rsa_int_result_t :=
  let '(n_2447, e_2448) :=
    pk_2445 in 
  (if ((s_2446) >.? ((n_2447) -% (nat_mod_one ))):bool then (
      @Err rsa_int_t error_t (MessageTooLarge)) else (@Ok rsa_int_t error_t (
        nat_mod_pow_mod (s_2446) (e_2448) (n_2447)))).

Definition i2osp
  (x_2449 : rsa_int_t)
  (x_len_2450 : int32)
  : byte_seq_result_t :=
  (if (((x_2449) >=.? (nat_mod_exp (nat_mod_from_literal (0x) (
              @repr WORDSIZE128 256) : rsa_int_t) (x_len_2450))) && ((
          x_len_2450) !=.? (byte_size_v))):bool then (@Err byte_seq error_t (
        InvalidLength)) else (@Ok byte_seq error_t (seq_slice (
          nat_mod_to_byte_seq_be (x_2449)) (@cast _ uint32 _ ((byte_size_v) .- (
              x_len_2450))) (@cast _ uint32 _ (x_len_2450))))).

Definition os2ip (x_2451 : byte_seq) : rsa_int_t :=
  nat_mod_from_byte_seq_be (x_2451) : rsa_int_t.

Definition mgf1
  (mgf_seed_2452 : byte_seq)
  (mask_len_2453 : uint_size)
  : byte_seq_result_t :=
  let result_2454 : (result byte_seq error_t) :=
    @Err byte_seq error_t (InvalidLength) in 
  let '(result_2454) :=
    if (mask_len_2453) <.? ((usize 2) .^ ((usize 32) * (hlen_v))):bool then (
      let t_2455 : seq uint8 :=
        seq_new_ (default : uint8) (usize 0) in 
      let t_2455 :=
        foldi (usize 0) (((mask_len_2453) + (usize 32)) / (
              usize 32)) (fun i_2456 t_2455 =>
          let x_2457 : byte_seq :=
            i2osp (nat_mod_from_literal (0x) (pub_u128 (i_2456)) : rsa_int_t) (
              @repr WORDSIZE32 4) in 
          let t_2455 :=
            seq_concat (t_2455) (array_to_seq (sha256 (seq_concat (
                  mgf_seed_2452) (x_2457)))) in 
          (t_2455))
        t_2455 in 
      let result_2454 :=
        @Ok byte_seq error_t (seq_slice (t_2455) (usize 0) (mask_len_2453)) in 
      (result_2454)) else ((result_2454)) in 
  result_2454.

