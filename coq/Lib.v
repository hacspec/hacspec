
(* Require Import FStar.Mul. *)

(*** Integers *)
From Coq Require Import ZArith Vector.
(* Require Import Int.PArray. *)
(* From Coq Require Import Numbers.Cyclic.Abstract.CyclicAxioms. *)

Require Import IntTypes.



Definition uint_size := nat.
(* Definition uint_size := range_t U32. *)
Definition int_size := nat.
(* Definition int_size := range_t S32. *)

Open Scope N_scope.
Axiom uint_size_to_nat : uint_size -> nat.
(* Definition usize (n:range_t U32) : u:uint_size{u == n} := n *)
(* Definition isize (n:range_t S32) : u:int_size{u == n} := n *)

Notation "'usize' n" := n (at level 56) : hacspec_scope.
Notation "'isize' n" := n (at level 56) : hacspec_scope.

(* Axiom usize isize : N -> uint_size. *)



Axiom 
  uint8
  uint16
  uint32
  uint64
  uint128
  int8
  int16
  int32
  int64
  int128 
  pub_uint8 
  pub_int8 
  pub_uint16 
  pub_int16 
  pub_uint32 
  pub_int32 
  pub_uint64 
  pub_int64 
  pub_uint128 
  pub_int128 
  : Type.

(* Definition size_t := uint_t U32 PUB *)
(* Axiom uint_size : forall (n : inttype), n < U32. *)
(* Axiom size : (n:size_nat) : size_t = uint #U32 #PUB n *)



(**** Public integers *)

(* Definition pub_u8 (n:range_t U8) : u:pub_uint8{v u == n} := uint #U8 #PUB n *)
Definition pub_u8 (n : range_t U8) := n.

(* Definition pub_i8 (n:range_t S8) : u:pub_int8{v u == n} := sint #S8 #PUB n *)
Definition pub_i8 (n : range_t S8) := n.

(* Definition pub_u16 (n:range_t U16) : u:pub_uint16{v u == n} := uint #U16 #PUB n *)
Definition pub_u16 (n : range_t U16) := n.

(* Definition pub_i16 (n:range_t S16) : u:pub_int16{v u == n} := sint #S16 #PUB n *)
Definition pub_i16 (n : range_t S16) := n.

(* Definition pub_u32 (n:range_t U32) : u:pub_uint32{v u == n} := uint #U32 #PUB n *)
Definition pub_u32 (n : range_t U32) := n.

(* Definition pub_i32 (n:range_t S32) : u:pub_int32{v u == n} := sint #S32 #PUB n *)
Definition pub_i32 (n : range_t S32) := n.

(* Definition pub_u64 (n:range_t U64) : u:pub_uint64{v u == n} := uint #U64 #PUB n *)
Definition pub_u64 (n : range_t U64) := n.

(* Definition pub_i64 (n:range_t S64) : u:pub_int64{v u == n} := sint #S64 #PUB n *)
Definition pub_i64 (n : range_t S64) := n.

(* Definition pub_u128 (n:range_t U128) : u:pub_uint128{v u == n} := uint #U128 #PUB n *)
Definition pub_u128 (n : range_t U128) := n.

(* Definition pub_i128 (n:range_t S128) : u:pub_int128{v u == n} := sint #S128 #PUB n *)
Definition pub_i128 (n : range_t S128) := n.

(**** Operations *)

Axiom size_t : Type.
Axiom size : forall {intt : Type}, intt -> size_t.
(* second argument is size *)
Axiom rotate_left : forall {inttype : Type}, inttype -> size_t -> inttype.
Axiom rotate_right : forall {inttype : Type}, inttype -> size_t -> inttype.
Axiom shift_left : forall {inttype shiftval : Type}, inttype -> shiftval -> inttype.
Axiom shift_right : forall {inttype shiftval : Type}, inttype -> shiftval -> inttype.

Definition uint8_rotate_left (u: uint8) (s: uint8) : uint8 :=
  rotate_left u (size s).

Definition uint8_rotate_right (u: uint8) (s: uint8) : uint8 :=
  rotate_right u (size s).

Definition uint16_rotate_left (u: uint16) (s: uint16) : uint16 :=
  rotate_left u (size s).

Definition uint16_rotate_right (u: uint16) (s: uint16) : uint16 :=
  rotate_right u (size s).

Definition uint32_rotate_left (u: uint32) (s: uint32) : uint32 :=
  rotate_left u (size s).

Definition uint32_rotate_right (u: uint32) (s: uint32) : uint32 :=
  rotate_right u (size s).

Definition uint64_rotate_left (u: uint64) (s: uint64) : uint64 :=
  rotate_left u (size s).

Definition uint64_rotate_right (u: uint64) (s: uint64) : uint64 :=
  rotate_right u (size s).

Definition uint128_rotate_left (u: uint128) (s: uint128) : uint128 :=
  rotate_left u (size s).

Definition uint128_rotate_right (u: uint128) (s: uint128) : uint128 :=
  rotate_right u (size s).

Axiom to_uint_size : size_t -> uint_size.

Definition usize_shift_right (u: uint_size) (s: pub_uint32) : uint_size :=
  to_uint_size (shift_right (size u) s).

Definition usize_shift_left (u: uint_size) (s: pub_uint32) : uint_size :=
  to_uint_size (shift_left (size u) s).


Axiom pub_uint128_wrapping_add : pub_uint128 -> pub_uint128 -> pub_uint128. 
  (* x +. y *)

(*** Loops *)

Axiom foldi :
  forall {acc: Type},
  uint_size ->
  uint_size ->
  (uint_size -> acc -> acc) ->
  acc -> acc.

(*** Sequences (lists) *)
From Coq Require Import List.

(* module LSeq := Lib.Sequence *)
(* module LBSeq := Lib.ByteSequence *)

(* We use vectors to define lseq *)
Definition lseq := Vector.t.

(* Definition lseq_to_list {A len} (s : lseq A len) := 
  match s with
  | mkLseq _ _ l => l
  end. *)

(* simplification *)
Definition seq (A : Type) := list A.

Definition list_len := length.

Definition byte_seq := seq uint8.

Definition nseq (A : Type) (len: nat) := lseq A len.

Definition seq_len {A: Type} (s: seq A) : N := N.of_nat (length s).

Definition seq_new_ {A: Type} (init : A) (len: uint_size) : lseq A len :=
  const init len.

Definition array_from_list {A: Type} (l: list A) : lseq A (length l)
  := of_list l.

(**** Array manipulation *)


Definition array_new_ {A: Type} (init:A) (len: uint_size)  : lseq A len :=
  const init len.

Definition array_index {A: Type} {len : uint_size} (s: lseq A len) (i: uint_size) : A.
Admitted.
(* Definition array_index {A: Type} {len : uint_size} (s: lseq A len) (i: uint_size) : A :=
  List.nth (N.to_nat i) (lseq_to_list s). *)

Definition array_upd {A: Type} {len : uint_size} (s: lseq A len) (i: uint_size) (new_v: A) : lseq A len.
Admitted.

(* Definition array_upd {A: Type} {len : uint_size} (s: lseq A len) (i: uint_size) (new_v: A) : lseq A len := List.upd s i new_v. *)

Definition array_from_seq
  {a: Type}
  (out_len:uint_size)
  (input: seq a)
    : lseq a out_len. Admitted.

Definition array_from_slice
  {a: Type}
  (default_value: a)
  (out_len: uint_size)
  (input: seq a)
  (start: uint_size)
  (slice_len: uint_size)
    : lseq a out_len. Admitted.

Definition array_slice
  {a: Type}
  (input: seq a)
  (start: uint_size)
  (slice_len: uint_size)
    : lseq a slice_len.
  Admitted.

Definition array_from_slice_range
  {a: Type}
  (default_value: a)
  (out_len: uint_size)
  (input: seq a)
  (start_fin: (uint_size * uint_size))
    : lseq a out_len. Admitted.
    
Definition array_slice_range
  {a: Type}
  {len : uint_size}
  (input: lseq a len)
  (start_fin:(uint_size * uint_size))
    : lseq a (snd start_fin - fst start_fin). Admitted.

Definition array_update_start
  {a: Type}
  {len: uint_size}
  (s: lseq a len)
  (start_s: seq a)
    : lseq a len. Admitted.

Definition array_len  {a: Type} {len: uint_size} (s: lseq a len) := len.

(**** Seq manipulation *)

Definition seq_slice
  {a: Type}
  (s: seq a)
  (start: uint_size)
  (len: uint_size)
    : lseq a len. Admitted.

Definition seq_update
  {a: Type}
  (s: seq a)
  (start: uint_size)
  (input: seq a)
    : nseq a (N.of_nat (length s)). Admitted.

Definition seq_concat
  {a: Type}
  (s1 :seq a)
  (s2: seq a)
  : lseq a (N.of_nat (length s1 + length s2)).
  Admitted.

(**** Chunking *)

Definition seq_num_chunks {a: Type} (s: seq a) (chunk_len: uint_size) : uint_size :=
  ((N.of_nat (length s)) + chunk_len - 1) / chunk_len. 

Definition seq_chunk_len
  {a: Type}
  (s: seq a)
  (chunk_len: uint_size)
  (chunk_num: uint_size)
    : uint_size :=
  let idx_start := chunk_len * chunk_num in
  if N.of_nat (length s) <? idx_start + chunk_len then
    N.of_nat (length s) - idx_start
  else
    chunk_len.

(* Definition seq_chunk_same_len_same_chunk_len
  {a: Type}
  (s1 s2: seq a)
  (chunk_len: uint_size)
  (chunk_num: uint_size)
  : Lemma
    (requires (LSeq.length s1 := LSeq.length s2 /\ chunk_len * chunk_num <= Seq.length s1))
    (ensures (seq_chunk_len s1 chunk_len chunk_lseq. Admitted. *)

(* Definition seq_get_chunk
  {a: Type}
  (s: seq a)
  (chunk_len: uint_size)
  (chunk_num: uint_size)
  : Pure (uint_size & seq a)
    (requires (chunk_len * chunk_num <= Seq.length s))
    (ensures (fun (out_len, chunk) ->
      out_len := seq_chunk_len s chunk_len chunk_num /\ LSeq.length chunk := out_len
    ))
 . :=
  let idx_start := chunk_len * chunk_num in
  let out_len := seq_chunk_len s chunk_len chunk_num in
  (out_len, LSeq.slice #a #(Seq.length s)
    s idx_start (idx_start + seq_chunk_len s chunk_len chunk_num)) *)

(* Definition seq_set_chunk
  {a: Type}
  {len : uint_size} (* change to nseq but update_sub missing for nseq *)
  (s: lseq a len)
  (chunk_len: uint_size)
  (chunk_num: uint_size)
  (chunk: seq a )
    : Pure (lseq a len)
      (requires (
        chunk_len * chunk_num <= Seq.length s /\
        LSeq.length chunk := seq_chunk_len s chunk_len chunk_num
      ))
      (ensures (fun out -> True))
  :=
 let idx_start := chunk_len * chunk_num in
 let out_len := seq_chunk_len s chunk_len chunk_num in
  LSeq.update_sub s idx_start out_len chunk *)

(**** Numeric operations *)

Definition array_xor
  {a: Type}
  {len: uint_size}
  (xor: a -> a -> a)
  (s1: lseq a len)
  (s2 : lseq a len)
    : lseq a len
  :=
  let out := s1 in
  foldi 0 len (fun i out =>
    array_upd out i (xor (array_index s1 i) (array_index s2 i))
  ) out.

Definition array_eq
  {a: Type}
  {len: uint_size}
  (eq: a -> a -> bool)
  (s1: lseq a len)
  (s2 : lseq a len)
    : bool
  :=
  let out := true in
  foldi 0 len (fun i out =>
    andb out (eq (array_index s1 i) (array_index s2 i))
  ) out.

(* 
Definition array_from_seq
  {a: Type}
  (out_len:uint_size)
  (input: seq a{Seq.length input := out_len})
    : lseq A out_len
  := input. Admitted.

Definition array_from_slice
  {a: Type}
  (default_value: a)
  (out_len: uint_size)
  (input: seq a)
  (start: uint_size)
  (slice_len: uint_size{start + slice_len <= LSeq.length input /\ slice_len <= out_len})
    : lseq A out_len
  :=
  let out := LSeq.create out_len default_value in
  LSeq.update_sub out 0 slice_len (LSeq.slice #a #(Seq.length input) input start (start + slice_len)). Admitted.

Definition array_slice
  {a: Type}
  (input: seq a)
  (start: uint_size)
  (slice_len: uint_size{start + slice_len <= LSeq.length input})
    : lseq A slice_len
  :=
  Seq.slice input start (start + slice_len).

Definition array_from_slice_range
  {a: Type}
  (default_value: a)
  (out_len: uint_size)
  (input: seq a)
  (start_fin: (uint_size & uint_size){
     fst start_fin >= 0 /\ snd start_fin <= LSeq.length input /\ snd start_fin >= fst start_fin /\
     snd start_fin - fst start_fin <= out_len
   })
    : lseq A out_len
 :=
  let out := array_new_ default_value out_len in
  let (start, fin) := start_fin in
  LSeq.update_sub out 0 (fin - start) (Seq.slice input start fin).

Definition array_slice_range
  {a: Type}
  {len : uint_size}
  (input: lseq A len)
  (start_fin:(uint_size & uint_size){
    fst start_fin >= 0 /\ snd start_fin <= len /\ snd start_fin >= fst start_fin
  })
    : lseq A (snd start_fin - fst start_fin)uint_size
  :=
  let (start, fin) := start_fin in
  LSeq.slice input start fin.

Definition array_update_start
  {a: Type}
  {len: uint_size}
  (s: lseq A len)
  (start_s: seq a{Seq.length start_s <= len})
    : lseq A len
  :=
  LSeq.update_sub s 0 (Seq.length start_s) start_s.

Definition array_len  {a: Type} {len: uint_size} (s: lseq A len) := len

(**** Seq manipulation *).

Definition seq_slice
  {a: Type}
  (s: seq a)
  (start: uint_size)
  (len: uint_size{start + len <= LSeq.length s})
    : lseq A len
  :=
  LSeq.slice #a #(Seq.length s) s start (start + len).

Definition seq_update
  {a: Type}
  (s: seq a)
  (start: uint_size)
  (input: seq a{start + LSeq.length input <= LSeq.length s})
    : nseq a (LSeq.length s)
  :=
  LSeq.update_sub #a #(LSeq.length s) s start (LSeq.length input) input.

Definition seq_concat
  {a: Type}
  (s1 :seq a)
  (s2: seq a{range (LSeq.length s1 + LSeq.length s2) U32})
  : lseq A (LSeq.length s1 + LSeq.length s2)
  :=
  LSeq.concat #a #(LSeq.length s1) #(LSeq.length s2) s1 s2


(**** Chunking *).

Definition seq_num_chunks {a: Type} (s: seq a) (chunk_len: uint_size{chunk_len > 0}) : uint_size :=
  (Seq.length s + chunk_len - 1) / chunk_len.

Definition seq_chunk_len
  {a: Type}
  (s: seq a)
  (chunk_len: uint_size)
  (chunk_num: uint_size{chunk_len * chunk_num <= Seq.length s})
    : Tot (out_len:uint_size{out_len <= chunk_len})
 . :=
  Definition idx_start := chunk_len * chunk_num in
  if idx_start + chunk_len > Seq.length s then
    Seq.length s - idx_start
  else
    chunk_len.

Definition seq_chunk_same_len_same_chunk_len
  {a: Type}
  (s1 s2: seq a)
  (chunk_len: uint_size)
  (chunk_num: uint_size)
  : Lemma
    (requires (LSeq.length s1 := LSeq.length s2 /\ chunk_len * chunk_num <= Seq.length s1))
    (ensures (seq_chunk_len s1 chunk_len chunk_lseq.

Definition seq_get_chunk
  {a: Type}
  (s: seq a)
  (chunk_len: uint_size)
  (chunk_num: uint_size)
  : Pure (uint_size & seq a)
    (requires (chunk_len * chunk_num <= Seq.length s))
    (ensures (fun (out_len, chunk) ->
      out_len := seq_chunk_len s chunk_len chunk_num /\ LSeq.length chunk := out_len
    ))
 . :=
  Definition idx_start := chunk_len * chunk_num in
  Definition out_len := seq_chunk_len s chunk_len chunk_num in
  (out_len, LSeq.slice #a #(Seq.length s)
    s idx_start (idx_start + seq_chunk_len s chunk_len chunk_num))

Definition seq_set_chunk
  {a: Type}
  {len : uint_size} (* change to nseq but update_sub missing for nseq *)
  (s: lseq A len)
  (chunk_len: uint_size)
  (chunk_num: uint_size)
  (chunk: seq a )
    : Pure (lseq A len)
      (requires (
        chunk_len * chunk_num <= Seq.length s /\
        LSeq.length chunk := seq_chunk_len s chunk_len chunk_num
      ))
      (ensures (fun out -> True))
  :=
  Definition idx_start := chunk_len * chunk_num in
  Definition out_len := seq_chunk_len s chunk_len chunk_num in
  LSeq.update_sub s idx_start out_len chunk

(**** Numeric operations *)

Definition array_xor
  {a: Type}
  {len: uint_size}
  (xor: a -> a -> a)
  (s1: lseq A len)
  (s2 : lseq A len)
    : lseq A len
  :=
  Definition out := s1 in
  foldi 0 len (fun i out ->
    array_upd out i (array_index s1 i `xor` array_index s2 i)
  ) out

Definition array_eq
  {a: Type}
  {len: uint_size}
  (eq: a -> a -> bool)
  (s1: lseq A len)
  (s2 : lseq A len)
    : bool
  :=
  Definition out := true in
  foldi 0 len (fun i out ->
    out && (array_index s1 i `eq` array_index s2 i)
  ) out *)


(**** Integers to arrays *)
Axiom uint32_to_le_bytes : uint32 -> lseq uint8 4.
(* Definition uint32_to_le_bytes (x: uint32) : lseq uint8 4 :=
  LBSeq.uint_to_bytes_le x. *)

Axiom uint32_to_be_bytes : uint32 -> lseq uint8 4.
(* Definition uint32_to_be_bytes (x: uint32) : lseq uint8 4 :=
  LBSeq.uint_to_bytes_be x *)

Axiom uint32_from_le_bytes : lseq uint8 4 -> uint32.
(* Definition uint32_from_le_bytes (s: lseq uint8 4) : uint32 :=
  LBSeq.uint_from_bytes_le s *)

Axiom uint32_from_be_bytes : lseq uint8 4 -> uint32.
(* Definition uint32_from_be_bytes (s: lseq uint8 4) : uint32 :=
  LBSeq.uint_from_bytes_be s *)

Axiom uint64_to_le_bytes : uint64 -> lseq uint8 8.
(* Definition uint64_to_le_bytes (x: uint64) : lseq uint8 8 :=
  LBSeq.uint_to_bytes_le x *)

Axiom uint64_to_be_bytes : uint64 -> lseq uint8 8.
(* Definition uint64_to_be_bytes (x: uint64) : lseq uint8 8 :=
  LBSeq.uint_to_bytes_be x *)

Axiom uint64_from_le_bytes : lseq uint8 8 -> uint64.
(* Definition uint64_from_le_bytes (s: lseq uint8 8) : uint64 :=
  LBSeq.uint_from_bytes_le s *)

Axiom uint64_from_be_bytes : lseq uint8 8 -> uint64.
(* Definition uint64_from_be_bytes (s: lseq uint8 8) : uint64 :=
  LBSeq.uint_from_bytes_be s *)

Axiom uint128_to_le_bytes : uint128 -> lseq uint8 16.
(* Definition uint128_to_le_bytes (x: uint128) : lseq uint8 16 :=
  LBSeq.uint_to_bytes_le x *)

Axiom uint128_to_be_bytes : uint128 -> lseq uint8 16.
(* Definition uint128_to_be_bytes (x: uint128) : lseq uint8 16 :=
  LBSeq.uint_to_bytes_be x *)

Axiom uint128_from_le_bytes : lseq uint8 16 -> uint128.
(* Definition uint128_from_le_bytes (input: lseq uint8 16) : uint128 :=
  LBSeq.uint_from_bytes_le input *)

Axiom uint128_from_be_bytes : lseq uint8 16 -> uint128.
(* Definition uint128_from_be_bytes (s: lseq uint8 16) : uint128 :=
  LBSeq.uint_from_bytes_be s *)

Axiom u32_to_le_bytes : pub_uint32 -> lseq pub_uint8 4.
(* Definition u32_to_le_bytes (x: pub_uint32) : lseq pub_uint8 4 :=
  LBSeq.uint_to_bytes_le x *)

Axiom u32_to_be_bytes : pub_uint32 -> lseq pub_uint8 4.
(* Definition u32_to_be_bytes (x: pub_uint32) : lseq pub_uint8 4 :=
  LBSeq.uint_to_bytes_be x *)

Axiom u32_from_le_bytes : lseq pub_uint8 4 -> pub_uint32.
(* Definition u32_from_le_bytes (s: lseq pub_uint8 4) : pub_uint32 :=
  LBSeq.uint_from_bytes_le s *)

Axiom u32_from_be_bytes : lseq pub_uint8 4 -> pub_uint32.
(* Definition u32_from_be_bytes (s: lseq pub_uint8 4) : pub_uint32 :=
  LBSeq.uint_from_bytes_be s *)

Axiom u64_to_le_bytes : pub_uint64 -> lseq pub_uint8 8.
(* Definition u64_to_le_bytes (x: pub_uint64) : lseq pub_uint8 8 :=
  LBSeq.uint_to_bytes_le x *)

Axiom u64_to_be_bytes : pub_uint64 -> lseq pub_uint8 8.
(* Definition u64_to_be_bytes (x: pub_uint64) : lseq pub_uint8 8 :=
  LBSeq.uint_to_bytes_be x *)

Axiom u64_from_le_bytes : lseq pub_uint8 8 -> pub_uint64.
(* Definition u64_from_le_bytes (s: lseq pub_uint8 8) : pub_uint64 :=
  LBSeq.uint_from_bytes_le s *)

Axiom u64_from_be_bytes : lseq pub_uint8 8 -> pub_uint64.
(* Definition u64_from_be_bytes (s: lseq pub_uint8 8) : pub_uint64 :=
  LBSeq.uint_from_bytes_be s *)

Axiom u128_to_le_bytes : pub_uint128 -> lseq pub_uint8 16.
(* Definition u128_to_le_bytes (x: pub_uint128) : lseq pub_uint8 16 :=
  LBSeq.uint_to_bytes_le x *)

Axiom u128_to_be_bytes : pub_uint128 -> lseq pub_uint8 16.
(* Definition u128_to_be_bytes (x: pub_uint128) : lseq pub_uint8 16 :=
  LBSeq.uint_to_bytes_be x *)

Axiom u128_from_le_bytes : lseq pub_uint8 16 -> pub_uint128.
(* Definition u128_from_le_bytes (input: lseq pub_uint8 16) : pub_uint128 :=
  LBSeq.uint_from_bytes_le input *)

Axiom u128_from_be_bytes : lseq pub_uint8 16 -> pub_uint128.
(* Definition u128_from_be_bytes (s: lseq pub_uint8 16) : pub_uint128 :=
  LBSeq.uint_from_bytes_be s *)

(*** Nats *)

(* type representing nats less than n *)
Definition nat_mod (n: N) := N.
(* Definition nat_mod (n: nat) := {x : nat | x < n}. *)

(* 
Definition nat_mod_add {n:nat} (a:nat_mod n) (b:nat_mod n) : nat_mod n.
Proof.
  unfold nat_mod. destruct a. destruct b.
  apply (exist _ (x + x0 mod n)).
   *)
Definition nat_mod_add {n:N} (a:nat_mod n) (b:nat_mod n) : nat_mod n :=
   (a + b) mod n.

Infix "+" := nat_mod_add : hacspec_scope.


Definition nat_mod_mul {n:N} (a:nat_mod n) (b:nat_mod n) : nat_mod n :=
  (a * b) mod n.

Infix "*" := nat_mod_mul : hacspec_scope.

Axiom uint128_to_N : uint128 -> N.

Definition nat_from_secret_literal (m:N) (x:uint128) : nat_mod m :=
  uint128_to_N x.

Axiom pub_uint128_to_N : pub_uint128 -> N.

Definition nat_from_literal (m:N) (x:pub_uint128) : nat_mod m :=
  pub_uint128_to_N x.

(*   
Definition nat_to_public_byte_seq_le (n: pos)  (len: uint_size) (x: nat_mod n) : lseq pub_uint8 len =
  Definition n' := n % (pow2 (8 * len)) in
  Lib.ByteSequence.nat_to_bytes_le len n'

Definition nat_to_public_byte_seq_be (n: pos)  (len: uint_size) (x: nat_mod n) : lseq pub_uint8 len =
  Definition n' := n % (pow2 (8 * len)) in
  Lib.ByteSequence.nat_to_bytes_be len n' *)


Definition nat_pow2 (m : N) (x : N) : nat_mod m := pow2 x.
