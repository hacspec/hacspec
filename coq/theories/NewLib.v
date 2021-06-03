(*** Integers *)
From Coq Require Import ZArith List Vector.
Import ListNotations.
(* Require Import IntTypes. *)

Require Import MachineIntegers.
From Coqprime Require GZnZ.

Axiom secret : forall {WS : WORDSIZE},  (@int WS) -> (@int WS). 


(* CompCert integers' signedness is only interpreted through 'signed' and 'unsigned',
   and not in the representation. Therefore, uints are just names for their respective ints.
*)
Definition uint8 := int8.
Definition uint16 := int16.
Definition uint32 := int32.
Definition uint64 := int64.
Definition uint128 := int128.

Definition uint_size := int32.
Definition int_size := int32.

(* Represents any type that can be converted to uint_size and back *)
Class UInt_sizable (A : Type) := {
  usize : A -> uint_size;
  from_uint_size : uint_size -> A; 
}.
Arguments usize {_} {_}.
Arguments from_uint_size {_} {_}.

Global Instance nat_uint_sizable : UInt_sizable nat := {
  usize n := repr (Z.of_nat n);
  from_uint_size n := Z.to_nat (unsigned n);
}.

Global Instance N_uint_sizable : UInt_sizable N := {
  usize n := repr (Z.of_N n);
  from_uint_size n := Z.to_N (unsigned n);
}.

Global Instance Z_uint_sizable : UInt_sizable Z := {
  usize n := repr n;
  from_uint_size n := unsigned n;
}.


(* Same, but for int_size *)
Class Int_sizable (A : Type) := {
  isize : A -> int_size;
  from_int_size : int_size -> A; 
}.

Arguments isize {_} {_}.
Arguments from_int_size {_} {_}.

Global Instance nat_Int_sizable : Int_sizable nat := {
  isize n := repr (Z.of_nat n);
  from_int_size n := Z.to_nat (signed n);
}.

Global Instance N_Int_sizable : Int_sizable N := {
  isize n := repr (Z.of_N n);
  from_int_size n := Z.to_N (signed n);
}.

Global Instance Z_Int_sizable : Int_sizable Z := {
  isize n := repr n;
  from_int_size n := signed n;
}.


(**** Public integers *)

(* Definition pub_u8 (n:range_t U8) : u:pub_uint8{v u == n} := uint #U8 #PUB n *)
Definition pub_u8 (n : Z) : int8 := repr n.

(* Definition pub_i8 (n:N) : u:pub_int8{v u == n} := sint #S8 #PUB n *)
Definition pub_i8 (n : Z) : int8 := repr n.

(* Definition pub_u16 (n:N) : u:pub_uint16{v u == n} := uint #U16 #PUB n *)
Definition pub_u16 (n : Z) : int16 := repr n.

(* Definition pub_i16 (n:N) : u:pub_int16{v u == n} := sint #S16 #PUB n *)
Definition pub_i16 (n : Z) : int16 := repr n.

(* Definition pub_u32 (n:N) : u:pub_uint32{v u == n} := uint #U32 #PUB n *)
Definition pub_u32 (n : Z) : int32 := repr n.

(* Definition pub_i32 (n:N) : u:pub_int32{v u == n} := sint #S32 #PUB n *)
Definition pub_i32 (n : Z) : int32 := repr n.

(* Definition pub_u64 (n:N) : u:pub_uint64{v u == n} := uint #U64 #PUB n *)
Definition pub_u64 (n : Z) : int64 := repr n.

(* Definition pub_i64 (n:N) : u:pub_int64{v u == n} := sint #S64 #PUB n *)
Definition pub_i64 (n : Z) : int64 := repr n.

(* Definition pub_u128 (n:N) : u:pub_uint128{v u == n} := uint #U128 #PUB n *)
Definition pub_u128 (n : Z) : int128 := repr n.

(* Definition pub_i128 (n:N) : u:pub_int128{v u == n} := sint #S128 #PUB n *)
Definition pub_i128 (n : Z) : int128 := repr n.

(**** Operations *)

(* Should maybe use size of s instead? *)
Definition uint8_rotate_left (u: int8) (s: int8) : int8 := rol u s.

Definition uint8_rotate_right (u: int8) (s: int8) : int8 := ror u s.

Definition uint16_rotate_left (u: int16) (s: int16) : int16 :=
  rol u s.

Definition uint16_rotate_right (u: int16) (s: int16) : int16 :=
  ror u s.

Definition uint32_rotate_left (u: int32) (s: int32) : int32 :=
  rol u s.

Definition uint32_rotate_right (u: int32) (s: int32) : int32 :=
  ror u s.

Definition uint64_rotate_left (u: int64) (s: int64) : int64 :=
  rol u s.

Definition uint64_rotate_right (u: int64) (s: int64) : int64 :=
  ror u s.

Definition uint128_rotate_left (u: int128) (s: int128) : int128 :=
  rol u s.

Definition uint128_rotate_right (u: int128) (s: int128) : int128 :=
  ror u s.

(* should use size u instead of u? *)
Definition usize_shift_right (u: uint_size) (s: int32) : uint_size :=
  (ror u s).

(* should use size u instead of u? *)
Definition usize_shift_left (u: uint_size) (s: int32) : uint_size :=
  (rol u s).

Definition pub_uint128_wrapping_add (x y: int128) : int128 :=
  add x y.


(*** Loops *)

Infix "+" := (@add WORDSIZE32).
Infix "-" := (@sub WORDSIZE32).
Infix "==" := (@eq WORDSIZE32) (at level 32).
Definition one := (@one WORDSIZE32).
Definition zero := (@zero WORDSIZE32).

(* 
Fixpoint foldi_
  {acc: Type}
  (cur_i: uint_size)
  (hi: uint_size) (* {cur_i <= hi} *)
  (f: uint_size -> acc -> acc) (* {i < hi} *)
  (cur: acc)
    : acc :=

  if cur_i == hi then cur else
  foldi_ (cur_i + one) hi f (f cur_i cur). *)

Open Scope nat_scope.
Fixpoint foldi_ 
  {acc : Type}
  (fuel : nat)
  (i : uint_size)
  (f : uint_size -> acc -> acc)
  (cur : acc) : acc :=
  match fuel with
  | 0 => cur
  | S n' => foldi_ n' (add i one) f (f i cur)
  end.
Close Scope nat_scope.
Definition foldi
  {acc: Type}
  (lo: uint_size)
  (hi: uint_size) (* {lo <= hi} *)
  (f: (uint_size) -> acc -> acc) (* {i < hi} *)
  (init: acc) : acc :=
  match Z.sub (unsigned hi) (unsigned lo) with
  | Z0 => init
  | Zneg p => init
  | Zpos p => foldi_ (Pos.to_nat p) lo f init
  end.

(* Coercion Int32.repr : Z >-> int. *)
(* Definition N_to_int n : int := Z.of_N n. *)
(* Coercion N_to_int : N >-> int. *)

(* Compute (foldi 1 2 (fun i acc => i + 1) 0). *)

(*** Seq *)

(* module LSeq = Lib.Sequence *)
(* module LBSeq = Lib.ByteSequence *)


Definition nseq := Vector.t.
Definition lseq (A : Type) (len : uint_size) := Vector.t A (from_uint_size len).

Definition seq (A : Type) := list A.

Definition byte_seq := seq int8.
Definition list_len := length.


Definition seq_len {A: Type} (s: seq A) : N := N.of_nat (length s).

(* Definition uint_size_to_nat (n :uint_size) : nat := Z.to_nat (unsigned n). *)


Definition seq_new_ {A: Type} (init : A) (len: nat) : nseq A len :=
  const init len.

(* Fixpoint of_list {A} (l : list A) : lseq A (usize (length l)) :=
match l as l' return lseq A (usize (length l')) with
  |Datatypes.nil => Vector.nil _
  |(h :: tail)%list => (Vector.cons _ h (usize (1 + length l)) (of_list tail))
end. *)

Definition array_from_list (A: Type) (l: list A) : nseq A (length l)
  := of_list l.

(**** Array manipulation *)

Class Default (A : Type) := {
  default : A
}.

(* Default instances for common types *)
Global Instance nat_default : Default nat := {
  default := 0%nat
}.
Global Instance N_default : Default N := {
  default := 0%N
}.
Global Instance Z_default : Default Z := {
  default := 0%Z
}.
Global Instance uint_size_default : Default uint_size := {
  default := zero
}.
Global Instance int_size_default : Default int_size := {
  default := zero
}.
Global Instance int_default {WS : WORDSIZE} : Default int := {
  default := repr 0
}.
Global Arguments default {_} {_}.


Definition array_new_ {A: Type} (init:A) (len: nat)  : nseq A len :=
  const init len.

Open Scope nat_scope.
Definition array_index {A: Type} `{Default A} {len : nat} (s: nseq A len) (i: nat) : A.
Proof.
  destruct (i <? len) eqn:H1.
  (* If i < len, index normally *)
  - rewrite Nat.ltb_lt in H1. 
    exact (Vector.nth s (Fin.of_nat_lt H1)). 
  (* otherwise return default element *)
  - exact default.
Defined.


Definition array_upd {A: Type} {len : nat} (s: nseq A len) (i: nat) (new_v: A) : nseq A len.
Proof.
  destruct (i <? len) eqn:H.
  (* If i < len, update normally *)
  - rewrite Nat.ltb_lt in H. 
    exact (Vector.replace s (Fin.of_nat_lt H) new_v).
  (* otherwise return original array *)
  - exact s.
Defined.

(* Definition array_upd {A: Type} {len : uint_size} (s: lseq A len) (i: uint_size) (new_v: A) : lseq A len := List.upd s i new_v. *)

Definition array_from_seq
  {a: Type}
  (out_len:nat)
  (input: seq a)
  (* {H : List.length input = out_len} *)
    : t a (length input) :=
  Vector.of_list input.

Definition slice {A} (l : seq A) (i j : nat) : seq A := 
  if j <=? i then [] else firstn (j-i+1) (skipn i l).

(* Compute (slice [1;2;3;4;5] 1 0). *)

Definition lseq_slice {A n} (l : nseq A n) (i j : nat) : nseq A _ :=
  of_list (slice (to_list l) i j).


(* 

Definition update_sub {A len slen} (v : t A len) (i n) (sub : t A slen) :=
  Vector.append
    (Vector.append (slice v 0 start ) sub) *)

Axiom update_sub : forall {A len slen}, t A len -> nat -> nat -> seq A -> t A slen.

Definition array_from_slice
  {a: Type}
  (default_value: a)
  (out_len: nat)
  (input: seq a)
  (start: nat)
  (slice_len: nat)
    : nseq a out_len :=
    let out := const default_value out_len in
    update_sub out 0 slice_len (slice input start (start + slice_len)).
  

Definition array_slice
  {a: Type}
  (input: seq a)
  (start: nat)
  (slice_len: nat)
    : nseq a _ :=
  let out := slice input start (start + slice_len) in
  array_from_seq slice_len out.


Definition array_from_slice_range
  {a: Type}
  (default_value: a)
  (out_len: nat)
  (input: seq a)
  (start_fin: (nat * nat))
    : nseq a out_len :=
    let out := array_new_ default_value out_len in
    let (start, fin) := start_fin in
    update_sub out 0 (fin - start) (slice input start fin).

  
Definition array_slice_range
  {a: Type}
  {len : nat}
  (input: nseq a len)
  (start_fin:(nat * nat))
    : nseq a _ :=
  lseq_slice input (fst start_fin) (snd start_fin).
  

Definition array_update_start
  {a: Type}
  {len: nat}
  (s: nseq a len)
  (start_s: seq a)
    : nseq a len :=
    update_sub s 0 (length start_s) start_s.


Definition array_len  {a: Type} {len: nat} (s: nseq a len) := len.

(**** Seq manipulation *)

Definition seq_slice
  {a: Type}
  (s: seq a)
  (start: nat)
  (len: nat)
    : nseq a _ :=
  array_from_seq len (slice s start (start + len)).


Definition seq_update
  {a: Type}
  (s: seq a)
  (start: nat)
  (input: seq a)
    : nseq a (length s) :=
  update_sub (of_list s) start (length input) input.

Definition sub {a} (s : list a) start n := 
  slice s start (start + n).

Definition seq_update_slice
  {a : Type}
  (out: seq a)
  (start_out: nat)
  (input: seq a)
  (start_in: nat)
  (len: nat)
    : nseq a (length out)
  :=
  update_sub (of_list out) start_out len
    (sub input start_in len).

Definition seq_concat
  {a : Type}
  (s1 :seq a)
  (s2: seq a)
  : nseq a _ :=
  of_list (List.rev_append s1 s2).


(**** Chunking *)

Definition seq_num_chunks {a: Type} (s: seq a) (chunk_len: nat) : nat :=
  ((length s) + chunk_len - 1) / chunk_len. 

Definition seq_chunk_len
  {a: Type}
  (s: seq a)
  (chunk_len: nat)
  (chunk_num: nat)
    : nat :=
  let idx_start := chunk_len * chunk_num in
  if (length s) <? idx_start + chunk_len then
    (length s) - idx_start
  else
    chunk_len.

(* Definition seq_chunk_same_len_same_chunk_len
  {a: Type}
  (s1 s2: seq a)
  (chunk_len: nat)
  (chunk_num: nat)
  : Lemma
    (requires (LSeq.length s1 := LSeq.length s2 /\ chunk_len * chunk_num <= Seq.length s1))
    (ensures (seq_chunk_len s1 chunk_len chunk_lseq. Admitted. *)

Definition seq_get_chunk
  {a: Type}
  (s: seq a)
  (chunk_len: nat)
  (chunk_num: nat)
  : (nat * seq a)
    (* (requires (chunk_len * chunk_num <= Seq.length s))
    (ensures (fun '(out_len, chunk) =>
      out_len := seq_chunk_len s chunk_len chunk_num /\ LSeq.length chunk := out_len
    )) *)
 :=
  let idx_start := chunk_len * chunk_num in
  let out_len := seq_chunk_len s chunk_len chunk_num in
  (out_len, slice
    s idx_start (idx_start + seq_chunk_len s chunk_len chunk_num)).

Definition seq_set_chunk
  {a: Type}
  {len : nat}
  (s: nseq a len)
  (chunk_len: nat)
  (chunk_num: nat)
  (chunk: seq a )
    : nseq a len
  :=
 let idx_start := chunk_len * chunk_num in
 let out_len := seq_chunk_len (Vector.to_list s) chunk_len chunk_num in
  update_sub s idx_start out_len chunk.

(**** Numeric operations *)

Definition array_xor
  {a: Type}
 `{Default a}
  {len: nat}
  (xor: a -> a -> a)
  (s1: nseq a len)
  (s2 : nseq a len)
    : nseq a len
  :=
  let out := s1 in
  foldi (usize 0) (usize len) (fun i out =>
    let i := from_uint_size i in
    array_upd out i (xor (array_index s1 i) (array_index s2 i))
  ) out.

Definition array_eq
  {a: Type}
  {len: nat}
  (eq: a -> a -> bool)
  (s1: nseq a len)
  (s2 : nseq a len)
    : bool := Vector.eqb _ eq s1 s2.

(**** Integers to arrays *)
Axiom uint32_to_le_bytes : int32 -> nseq int8 4.
(* Definition uint32_to_le_bytes (x: uint32) : nseq uint8 4 :=
  LBSeq.uint_to_bytes_le x. *)

Axiom uint32_to_be_bytes : int32 -> nseq int8 4.
(* Definition uint32_to_be_bytes (x: uint32) : nseq uint8 4 :=
  LBSeq.uint_to_bytes_be x *)

Axiom uint32_from_le_bytes : nseq int8 4 -> int32.
(* Definition uint32_from_le_bytes (s: nseq uint8 4) : uint32 :=
  LBSeq.uint_from_bytes_le s *)

Axiom uint32_from_be_bytes : nseq int8 4 -> int32.
(* Definition uint32_from_be_bytes (s: nseq uint8 4) : uint32 :=
  LBSeq.uint_from_bytes_be s *)

Axiom uint64_to_le_bytes : int64 -> nseq int8 8.
(* Definition uint64_to_le_bytes (x: uint64) : nseq uint8 8 :=
  LBSeq.uint_to_bytes_le x *)

Axiom uint64_to_be_bytes : int64 -> nseq int8 8.
(* Definition uint64_to_be_bytes (x: uint64) : nseq uint8 8 :=
  LBSeq.uint_to_bytes_be x *)

Axiom uint64_from_le_bytes : nseq int8 8 -> int64.
(* Definition uint64_from_le_bytes (s: nseq uint8 8) : uint64 :=
  LBSeq.uint_from_bytes_le s *)

Axiom uint64_from_be_bytes : nseq int8 8 -> int64.
(* Definition uint64_from_be_bytes (s: nseq uint8 8) : uint64 :=
  LBSeq.uint_from_bytes_be s *)

Axiom uint128_to_le_bytes : int128 -> nseq int8 16.
(* Definition uint128_to_le_bytes (x: uint128) : nseq uint8 16 :=
  LBSeq.uint_to_bytes_le x *)

Axiom uint128_to_be_bytes : int128 -> nseq int8 16.
(* Definition uint128_to_be_bytes (x: uint128) : nseq uint8 16 :=
  LBSeq.uint_to_bytes_be x *)

Axiom uint128_from_le_bytes : nseq int8 16 -> int128.
(* Definition uint128_from_le_bytes (input: nseq uint8 16) : uint128 :=
  LBSeq.uint_from_bytes_le input *)

Axiom uint128_from_be_bytes : nseq int8 16 -> int128.
(* Definition uint128_from_be_bytes (s: nseq uint8 16) : uint128 :=
  LBSeq.uint_from_bytes_be s *)

Axiom u32_to_le_bytes : int32 -> nseq int8 4.
(* Definition u32_to_le_bytes (x: pub_uint32) : nseq pub_uint8 4 :=
  LBSeq.uint_to_bytes_le x *)

Axiom u32_to_be_bytes : int32 -> nseq int8 4.
(* Definition u32_to_be_bytes (x: pub_uint32) : nseq pub_uint8 4 :=
  LBSeq.uint_to_bytes_be x *)

Axiom u32_from_le_bytes : nseq int8 4 -> int32.
(* Definition u32_from_le_bytes (s: nseq pub_uint8 4) : pub_uint32 :=
  LBSeq.uint_from_bytes_le s *)

Axiom u32_from_be_bytes : nseq int8 4 -> int32.
(* Definition u32_from_be_bytes (s: nseq pub_uint8 4) : pub_uint32 :=
  LBSeq.uint_from_bytes_be s *)

Axiom u64_to_le_bytes : int64 -> nseq int8 8.
(* Definition u64_to_le_bytes (x: int64) : nseq int8 8 :=
  LBSeq.uint_to_bytes_le x *)

Axiom u64_to_be_bytes : int64 -> nseq int8 8.
(* Definition u64_to_be_bytes (x: int64) : nseq int8 8 :=
  LBSeq.uint_to_bytes_be x *)

Axiom u64_from_le_bytes : nseq int8 8 -> int64.
(* Definition u64_from_le_bytes (s: nseq int8 8) : int64 :=
  LBSeq.uint_from_bytes_le s *)

Axiom u64_from_be_bytes : nseq int8 8 -> int64.
(* Definition u64_from_be_bytes (s: nseq int8 8) : int64 :=
  LBSeq.uint_from_bytes_be s *)

Axiom u128_to_le_bytes : int128 -> nseq int8 16.
(* Definition u128_to_le_bytes (x: int128) : nseq int8 16 :=
  LBSeq.uint_to_bytes_le x *)

Axiom u128_to_be_bytes : int128 -> nseq int8 16.
(* Definition u128_to_be_bytes (x: int128) : nseq int8 16 :=
  LBSeq.uint_to_bytes_be x *)

Axiom u128_from_le_bytes : nseq int8 16 -> int128.
(* Definition u128_from_le_bytes (input: nseq int8 16) : int128 :=
  LBSeq.uint_from_bytes_le input *)

Axiom u128_from_be_bytes : nseq int8 16 -> int128.
(* Definition u128_from_be_bytes (s: nseq int8 16) : pub_uint128 :=
  LBSeq.uint_from_bytes_be s *)


(*** Nats *)


Definition nat_mod (p : N) : Set := GZnZ.znz (Z.of_N p).
(* Definition nat_mod (p : uint_size) := nat_mod (from_uint_size p). *)

Definition nat_mod_zero {p : N} : nat_mod p := GZnZ.zero (Z.of_N p).
Definition nat_mod_one {p : N} : nat_mod p := GZnZ.one (Z.of_N p).
Definition nat_mod_two {p : N} : nat_mod p := GZnZ.mkznz (Z.of_N p) _ (GZnZ.modz (Z.of_N p) 2).


(* convenience coercions from nat_mod to Z and N *)
Coercion Z.of_N : N >-> Z.

Definition nat_mod_add {n : N} (a : nat_mod n) (b : nat_mod n) : nat_mod n := GZnZ.add n a b.
   
Infix "+%" := nat_mod_add (at level 33) : hacspec_scope.

Definition nat_mod_mul {n : N} (a:nat_mod n) (b:nat_mod n) : nat_mod n := GZnZ.add n a b.
Infix "*%" := nat_mod_mul (at level 33) : hacspec_scope.

Definition nat_mod_sub {n : N} (a:nat_mod n) (b:nat_mod n) : nat_mod n := GZnZ.sub n a b.
Infix "-%" := nat_mod_mul (at level 33) : hacspec_scope.

Definition nat_mod_div {n : N} (a:nat_mod n) (b:nat_mod n) : nat_mod n := GZnZ.div n a b.
Infix "/%" := nat_mod_mul (at level 33) : hacspec_scope.

Definition nat_modeg {n : N} (a:nat_mod n) : nat_mod n := GZnZ.opp n a.

Definition nat_mod_inv {n : N} (a:nat_mod n) : nat_mod n := GZnZ.inv n a.

Definition nat_mod_exp {p : N} (a:nat_mod p) (n : uint_size) : nat_mod p :=
  let n : nat := Z.to_nat (from_uint_size n) in 
  let fix exp_ (e : nat_mod p) (n : nat) :=
    match n with
    | 0%nat => nat_mod_one
    | S n => nat_mod_mul a (exp_ a n)
    end in
  exp_ a n.

Close Scope nat_scope.
Open Scope Z_scope.

(* We assume x < m *)
Definition nat_mod_from_secret_literal {m : N} (x:int128) : nat_mod m.
Proof.
  unfold nat_mod.
  (* since we assume x < m, it will be true that (unsigned x) = (unsigned x) mod m  *)
  remember ((unsigned x) mod m) as zmodm.
  apply (GZnZ.mkznz m zmodm).
  rewrite Heqzmodm.
  rewrite Zmod_mod.
  reflexivity.
  Show Proof.
Defined.

Definition nat_mod_from_literal (m : N) (x:int128) : nat_mod m := nat_mod_from_secret_literal x.

Axiom nat_mod_to_public_byte_seq_le : forall (n : N) (len : uint_size), nat_mod n -> nseq int8 (from_uint_size len).

Definition nat_mod_bit {n : N} (a : nat_mod n) (i : uint_size) :=
  Z.testbit (GZnZ.val n a) (from_uint_size i).


(*   
Definition nat_mod_to_public_byte_seq_le (n: pos)  (len: uint_size) (x: nat_mod_mod n) : lseq pub_uint8 len =
  Definition n' := n % (pow2 (8 * len)) in
  Lib.ByteSequence.nat_mod_to_bytes_le len n'*)

Axiom nat_mod_to_public_byte_seq_be : forall (n : N) (len : uint_size), nat_mod n -> nseq int8 (from_uint_size len).
(* Definition nat_to_public_byte_seq_be (n: pos)  (len: uint_size) (x: nat_mod n) : lseq pub_uint8 len =
  Definition n' := n % (pow2 (8 * len)) in
  Lib.ByteSequence.nat_to_bytes_be len n' *)

Axiom array_to_le_bytes : forall {A l}, nseq A l -> nseq int64 l.
Axiom nat_mod_from_byte_seq_le : forall  {A l n}, nseq A l -> nat_mod n.  


(* We assume 2^x < m *)
Definition nat_mod_pow2 (m : N) (x : N) : nat_mod m.
Proof.
  remember (Z.pow 2 x mod m) as y.
  apply (GZnZ.mkznz m y).
  rewrite Heqy.
  rewrite Zmod_mod.
  reflexivity.
Defined.

Section Coercions.

  (* Integer coercions *)
  (* We have nat >-> N >-> Z >-> int/int32 *)
  Global Coercion repr : Z >-> int.
  
  Definition Z_to_uint_size (n : Z) : uint_size := repr n.
  Definition Z_to_int_size (n : Z) : int_size := repr n.

  Global Coercion Z_to_uint_size : Z >-> uint_size.
  Global Coercion Z_to_int_size : Z >-> int_size.

  Definition N_to_int `{WORDSIZE} (n : N) : int := repr (Z.of_N n).
  Global Coercion N.of_nat : nat >-> N.
  Global Coercion N_to_int : N >-> int.
  Definition N_to_uint_size (n : N) : uint_size := repr n.
  Global Coercion N_to_uint_size : N >-> uint_size.
  Definition nat_to_int `{WORDSIZE} (n : nat) := repr (Z.of_nat n).
  Global Coercion nat_to_int : nat >-> int.  
  Definition uint_size_to_nat (n : uint_size) : nat := from_uint_size n.
  Global Coercion uint_size_to_nat : uint_size >-> nat.

  Global Coercion GZnZ.val : GZnZ.znz >-> Z.

End Coercions.



(* Comparisons, boolean equality, and notation *)

Class EqDec (A : Type) :=
  { eqb : A -> A -> bool ;
    eqb_leibniz : forall x y, eqb x y = true -> x = y }.

Infix "=.?" := eqb (at level 40) : hacspec_scope.
Infix "!=.?" := (fun a b => negb (eqb a b)) (at level 40) : hacspec_scope.

Class Comparable (A : Type) := {
  ltb : A -> A -> bool;
  leb : A -> A -> bool;
  gtb : A -> A -> bool;
  geb : A -> A -> bool;
}.
Infix "<.?" := ltb (at level 42) : hacspec_scope.
Infix "<=.?" := leb (at level 42) : hacspec_scope.
Infix ">.?" := gtb (at level 42) : hacspec_scope.
Infix ">=.?" := geb (at level 42) : hacspec_scope.

Global Program Instance nat_eqdec : EqDec nat := {
  eqb := Nat.eqb;
  eqb_leibniz :=  fun a b => proj1 (Nat.eqb_eq a b) ;
}.

Global Instance nat_comparable : Comparable nat := {
  ltb := Nat.ltb;
  leb := Nat.leb;
  gtb a b := Nat.ltb b a; 
  geb a b := Nat.leb b a;
}.

Global Instance N_eqdec : EqDec N := {
  eqb := N.eqb;
  eqb_leibniz :=  fun a b => proj1 (N.eqb_eq a b) ;
}.

Global Instance N_comparable : Comparable N := {
  ltb := N.ltb;
  leb := N.leb;
  gtb a b := N.ltb b a; 
  geb a b := N.leb b a;
}.

Global Instance Z_eqdec : EqDec Z := {
  eqb := Z.eqb;
  eqb_leibniz :=  fun a b => proj1 (Z.eqb_eq a b) ;
}.

Global Instance Z_comparable : Comparable Z := {
  ltb := Z.ltb;
  leb := Z.leb;
  gtb a b := Z.ltb b a; 
  geb a b := Z.leb b a;
}.

Lemma int_eqb_eq : forall {WS : WORDSIZE} (a b : int), eq a b = true <-> a = b.
Proof.
  intros. split.
  - apply same_if_eq.
  - intros. rewrite H. apply eq_true.
Qed.

Global Instance int_eqdec `{WORDSIZE}: EqDec int := {
  eqb := eq;
  eqb_leibniz :=  fun a b => proj1 (int_eqb_eq a b) ;
}.

Global Instance int_comparable `{WORDSIZE} : Comparable int := {
  ltb := lt;
  leb a b := if eq a b then true else lt a b ;
  gtb a b := lt b a; 
  geb a b := if eq a b then true else lt b a;
}.

Definition nat_mod_val (p : N) (a : nat_mod p) : Z := GZnZ.val p a.

Axiom nat_mod_eqb_spec : forall {p} (a b : nat_mod p), Z.eqb (nat_mod_val p a) (nat_mod_val p b) = true -> a = b.

Global Instance nat_mod_eqdec {p} : EqDec (nat_mod p) := {
  eqb a b := Z.eqb (nat_mod_val p a) (nat_mod_val p b);
  eqb_leibniz := nat_mod_eqb_spec;
}.

Global Instance nat_mod_comparable `{p : N} : Comparable (nat_mod p) := {
  ltb a b := Z.ltb (nat_mod_val p a) (nat_mod_val p b);
  leb a b := if Zeq_bool a b then true else Z.ltb (nat_mod_val p a) (nat_mod_val p b) ;
  gtb a b := Z.ltb (nat_mod_val p b) (nat_mod_val p a); 
  geb a b := if Zeq_bool b a then true else Z.ltb (nat_mod_val p b) (nat_mod_val p a) ;
}.

Global Instance bool_eqdec : EqDec bool := {
  eqb := Bool.eqb;
  eqb_leibniz := Bool.eqb_prop;
}.

Global Instance string_eqdec : EqDec String.string := {
  eqb := String.eqb;
  eqb_leibniz :=  fun a b => proj1 (String.eqb_eq a b) ;
}.

Require Import Sumbool.
Open Scope list_scope.

Fixpoint list_eqdec {A} `{EqDec A} (l1 l2 : list A) : bool :=
  match l1, l2 with
  | x::xs, y::ys => if eqb x y then list_eqdec xs ys else false
  | [], [] => true
  | _,_ => false
  end.

Lemma list_eqdec_sound : forall {A} `{EqDec A} (l1 l2 : list A), list_eqdec l1 l2 = true -> l1 = l2.
Proof.
  intros A H l1. induction l1; intros; induction l2; simpl in *; try reflexivity; try inversion H0.
   (* inductive case *)
  apply Field_theory.if_true in H0; destruct H0.
  f_equal.
  (* show heads are equal *)
  - apply (eqb_leibniz a a0 H0).
  (* show tails are equal using induction hypothesis *)
  - apply IHl1. assumption. 
Qed.


Global Instance List_eqdec {A} `{EqDec A} : EqDec (list A) := {
  eqb := list_eqdec; 
  eqb_leibniz := list_eqdec_sound;
}.
Require Import Program.Equality.
Lemma vector_eqb_sound : forall {A : Type} {n : nat} `{EqDec A} (v1 v2 : t A n), Vector.eqb _ eqb v1 v2 = true -> v1 = v2.
Proof.
  intros A n H v1. induction v1; intros; simpl in *; dependent destruction v2.
  - reflexivity.
  - f_equal; rewrite Bool.andb_true_iff in H0; destruct H0.
    + apply eqb_leibniz. assumption.
    + apply IHv1. assumption.
Qed.

Global Program Instance Vector_eqdec {A n} `{EqDec A}: EqDec (Vector.t A n) := {
  eqb := Vector.eqb _ eqb; 
  eqb_leibniz := vector_eqb_sound;
}.

Global Program Instance Dec_eq_prod (A B : Type) `{EqDec A} `{EqDec B} : EqDec (A * B) := {
  eqb '(a0, b0) '(a1, b1) := andb (eqb a0 a1) (eqb b0 b1)
}.
Next Obligation.
  symmetry in H1.
  apply Bool.andb_true_eq in H1. destruct H1.
  symmetry in H1. apply (eqb_leibniz a0 a) in H1.
  symmetry in H2. apply (eqb_leibniz b0 b) in H2.
  rewrite H1, H2. reflexivity.
Defined.


(* Axiom most_significant_bit : scalar -> uint_size -> uint_size. *)




(* Require Import DecidableClass.
Global Instance nat_mod_eq_dec {p : N} (a b : nat_mod p) : Decidable (a = b) := {
  Decidable_witness := eqb a b;
  Decidable_spec := eqb_spec a b;
}.

Global Instance nat_mod_eq_dec {p} (a b : nat_mod p) : Decidable (a = b) := {
  Decidable_witness := eqb a b;
  Decidable_spec := eqb_spec a b;
}.


Definition decide_eq {A : Type} (a b : A) `{Decidable (a = b)}  := decide (a = b).
Infix "==?" := decide_eq (at level 40) : hacspec_scope.

(* Comparable instances have decidable equality *)
Instance Comparable_to_Decidable {A} `(Comparable A) {a b : A} : Decidable (a = b) := {
  Decidable_witness := eqb a b;
  Decidable_spec := eqb_spec a b;
}.



 *)
