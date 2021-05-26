(*** Integers *)
From Coq Require Import ZArith List Vector.
Import ListNotations.
(* Require Import IntTypes. *)

Require Import MachineIntegers.
From Coqprime Require GZnZ.


Definition uint_size := int32.
Definition int_size := int32.

(**** Usize  *)
Definition usize (n : uint_size) := n.
Definition isize (n : uint_size) := n.




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

Definition lseq := Vector.t.

Definition seq (A : Type) := list A.

Definition byte_seq := seq int8.
Definition list_len := length.

Definition nseq (A : Type) (len: nat) := lseq A len.

Definition seq_len {A: Type} (s: seq A) : N := N.of_nat (length s).

(* Definition uint_size_to_nat (n :uint_size) : nat := Z.to_nat (unsigned n). *)


Definition seq_new_ {A: Type} (init : A) (len: nat) : lseq A len :=
  const init len.

Definition array_from_list {A: Type} (l: list A) : lseq A (length l)
  := of_list l.

(**** Array manipulation *)

Axiom array_default_val : forall A, A.

Definition array_new_ {A: Type} (init:A) (len: nat)  : lseq A len :=
  const init len.

Check (Fin.t 4).
Open Scope nat_scope.
Definition array_index {A: Type} {len : nat} (s: lseq A len) (i: nat) {H : i < len} : A :=
  Vector.nth s (Fin.of_nat_lt H). 

  (* Definition array_index {A: Type} {len : uint_size} (s: lseq A len) (i: uint_size) : A :=
  List.nth (N.to_nat i) (lseq_to_list s). *)

Definition array_upd {A: Type} {len : nat} (s: lseq A len) (i: nat) (new_v: A) {H : i < len} : lseq A len :=
  Vector.replace s (Fin.of_nat_lt H) new_v.

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

Definition lseq_slice {A n} (l : lseq A n) (i j : nat) : lseq A _ :=
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
  (*   (slice_len: nat{start + slice_len <= LSeq.length input /\ slice_len <= out_len}) *)
  (slice_len: nat)
    : lseq a out_len :=
    let out := const default_value out_len in
    update_sub out 0 slice_len (slice input start (start + slice_len)).
  

Definition array_slice
  {a: Type}
  (input: seq a)
  (start: nat)
  (slice_len: nat)
    : lseq a _ :=
  let out := slice input start (start + slice_len) in
  array_from_seq slice_len out.


Definition array_from_slice_range
  {a: Type}
  (default_value: a)
  (out_len: nat)
  (input: seq a)
  (start_fin: (nat * nat))
    : lseq a out_len :=
    let out := array_new_ default_value out_len in
    let (start, fin) := start_fin in
    update_sub out 0 (fin - start) (slice input start fin).

  
Definition array_slice_range
  {a: Type}
  {len : nat}
  (input: lseq a len)
  (start_fin:(nat * nat))
    : lseq a _ :=
  lseq_slice input (fst start_fin) (snd start_fin).
  

Definition array_update_start
  {a: Type}
  {len: nat}
  (s: lseq a len)
  (start_s: seq a)
    : lseq a len :=
    update_sub s 0 (length start_s) start_s.


Definition array_len  {a: Type} {len: nat} (s: lseq a len) := len.

(**** Seq manipulation *)

Definition seq_slice
  {a: Type}
  (s: seq a)
  (start: nat)
  (len: nat)
    : lseq a _ :=
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
  : lseq a _ :=
  of_list (List.rev_append s1 s2).


(**** Chunking *)

(* Definition seq_num_chunks {a: Type} (s: seq a) (chunk_len: uint_size) : uint_size :=
  ((length s) + chunk_len - 1) / chunk_len. 

Definition seq_chunk_len
  {a: Type}
  (s: seq a)
  (chunk_len: uint_size)
  (chunk_num: uint_size)
    : uint_size :=
  let idx_start := chunk_len * chunk_num in
  if (length s) <? idx_start + chunk_len then
    (length s) - idx_start
  else
    chunk_len. *)

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
  {len: nat}
  (xor: a -> a -> a)
  (s1: lseq a len)
  (s2 : lseq a len)
    : lseq a len
  . Admitted.
  (* :=
  let out := s1 in
  foldi 0 len (fun i out =>
    array_upd out i (xor (array_index s1 i) (array_index s2 i))
  ) out. *)

Definition array_eq
  {a: Type}
  {len: nat}
  (eq: a -> a -> bool)
  (s1: lseq a len)
  (s2 : lseq a len)
    : bool
  . Admitted.
  (* :=
  let out := true in
  foldi 0 len (fun i out =>
    andb out (eq (array_index s1 i) (array_index s2 i))
  ) out. *)

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
Axiom uint32_to_le_bytes : int32 -> lseq int8 4.
(* Definition uint32_to_le_bytes (x: uint32) : lseq uint8 4 :=
  LBSeq.uint_to_bytes_le x. *)

Axiom uint32_to_be_bytes : int32 -> lseq int8 4.
(* Definition uint32_to_be_bytes (x: uint32) : lseq uint8 4 :=
  LBSeq.uint_to_bytes_be x *)

Axiom uint32_from_le_bytes : lseq int8 4 -> int32.
(* Definition uint32_from_le_bytes (s: lseq uint8 4) : uint32 :=
  LBSeq.uint_from_bytes_le s *)

Axiom uint32_from_be_bytes : lseq int8 4 -> int32.
(* Definition uint32_from_be_bytes (s: lseq uint8 4) : uint32 :=
  LBSeq.uint_from_bytes_be s *)

Axiom uint64_to_le_bytes : int64 -> lseq int8 8.
(* Definition uint64_to_le_bytes (x: uint64) : lseq uint8 8 :=
  LBSeq.uint_to_bytes_le x *)

Axiom uint64_to_be_bytes : int64 -> lseq int8 8.
(* Definition uint64_to_be_bytes (x: uint64) : lseq uint8 8 :=
  LBSeq.uint_to_bytes_be x *)

Axiom uint64_from_le_bytes : lseq int8 8 -> int64.
(* Definition uint64_from_le_bytes (s: lseq uint8 8) : uint64 :=
  LBSeq.uint_from_bytes_le s *)

Axiom uint64_from_be_bytes : lseq int8 8 -> int64.
(* Definition uint64_from_be_bytes (s: lseq uint8 8) : uint64 :=
  LBSeq.uint_from_bytes_be s *)

Axiom uint128_to_le_bytes : int128 -> lseq int8 16.
(* Definition uint128_to_le_bytes (x: uint128) : lseq uint8 16 :=
  LBSeq.uint_to_bytes_le x *)

Axiom uint128_to_be_bytes : int128 -> lseq int8 16.
(* Definition uint128_to_be_bytes (x: uint128) : lseq uint8 16 :=
  LBSeq.uint_to_bytes_be x *)

Axiom uint128_from_le_bytes : lseq int8 16 -> int128.
(* Definition uint128_from_le_bytes (input: lseq uint8 16) : uint128 :=
  LBSeq.uint_from_bytes_le input *)

Axiom uint128_from_be_bytes : lseq int8 16 -> int128.
(* Definition uint128_from_be_bytes (s: lseq uint8 16) : uint128 :=
  LBSeq.uint_from_bytes_be s *)

Axiom u32_to_le_bytes : int32 -> lseq int8 4.
(* Definition u32_to_le_bytes (x: pub_uint32) : lseq pub_uint8 4 :=
  LBSeq.uint_to_bytes_le x *)

Axiom u32_to_be_bytes : int32 -> lseq int8 4.
(* Definition u32_to_be_bytes (x: pub_uint32) : lseq pub_uint8 4 :=
  LBSeq.uint_to_bytes_be x *)

Axiom u32_from_le_bytes : lseq int8 4 -> int32.
(* Definition u32_from_le_bytes (s: lseq pub_uint8 4) : pub_uint32 :=
  LBSeq.uint_from_bytes_le s *)

Axiom u32_from_be_bytes : lseq int8 4 -> int32.
(* Definition u32_from_be_bytes (s: lseq pub_uint8 4) : pub_uint32 :=
  LBSeq.uint_from_bytes_be s *)

Axiom u64_to_le_bytes : int64 -> lseq int8 8.
(* Definition u64_to_le_bytes (x: int64) : lseq int8 8 :=
  LBSeq.uint_to_bytes_le x *)

Axiom u64_to_be_bytes : int64 -> lseq int8 8.
(* Definition u64_to_be_bytes (x: int64) : lseq int8 8 :=
  LBSeq.uint_to_bytes_be x *)

Axiom u64_from_le_bytes : lseq int8 8 -> int64.
(* Definition u64_from_le_bytes (s: lseq int8 8) : int64 :=
  LBSeq.uint_from_bytes_le s *)

Axiom u64_from_be_bytes : lseq int8 8 -> int64.
(* Definition u64_from_be_bytes (s: lseq int8 8) : int64 :=
  LBSeq.uint_from_bytes_be s *)

Axiom u128_to_le_bytes : int128 -> lseq int8 16.
(* Definition u128_to_le_bytes (x: int128) : lseq int8 16 :=
  LBSeq.uint_to_bytes_le x *)

Axiom u128_to_be_bytes : int128 -> lseq int8 16.
(* Definition u128_to_be_bytes (x: int128) : lseq int8 16 :=
  LBSeq.uint_to_bytes_be x *)

Axiom u128_from_le_bytes : lseq int8 16 -> int128.
(* Definition u128_from_le_bytes (input: lseq int8 16) : int128 :=
  LBSeq.uint_from_bytes_le input *)

Axiom u128_from_be_bytes : lseq int8 16 -> int128.
(* Definition u128_from_be_bytes (s: lseq int8 16) : pub_uint128 :=
  LBSeq.uint_from_bytes_be s *)

(*** Nats *)

Definition nat_mod (p : N) : Set := GZnZ.znz (Z.of_N p).

(* convenience coercions from nat_mod to Z and N *)
Coercion GZnZ.val : GZnZ.znz >-> Z.
Coercion Z.of_N : N >-> Z.

Open Scope Z_scope.


Definition nat_mod_add {n : N} (a : nat_mod n) (b : nat_mod n) : nat_mod n := GZnZ.add n a b.
   
Infix "+" := nat_mod_add : hacspec_scope.

Definition nat_mod_mul {n : N} (a:nat_mod n) (b:nat_mod n) : nat_mod n := GZnZ.add n a b.
Infix "*" := nat_mod_mul : hacspec_scope.

Definition nat_mod_sub {n : N} (a:nat_mod n) (b:nat_mod n) : nat_mod n := GZnZ.sub n a b.
Infix "-" := nat_mod_mul : hacspec_scope.

Definition nat_mod_div {n : N} (a:nat_mod n) (b:nat_mod n) : nat_mod n := GZnZ.div n a b.
Infix "/" := nat_mod_mul : hacspec_scope.

Definition nat_mod_neg {n : N} (a:nat_mod n) : nat_mod n := GZnZ.opp n a.

Definition nat_mod_inv {n : N} (a:nat_mod n) : nat_mod n := GZnZ.inv n a.

(* We assume x < m *)
Definition nat_from_secret_literal (m : N) (x:int128) : nat_mod m.
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


Definition nat_from_literal (m : N) (x:int128) : nat_mod m := nat_from_secret_literal m x.

(*   
Definition nat_to_public_byte_seq_le (n: pos)  (len: uint_size) (x: nat_mod n) : lseq pub_uint8 len =
  Definition n' := n % (pow2 (8 * len)) in
  Lib.ByteSequence.nat_to_bytes_le len n'

Definition nat_to_public_byte_seq_be (n: pos)  (len: uint_size) (x: nat_mod n) : lseq pub_uint8 len =
  Definition n' := n % (pow2 (8 * len)) in
  Lib.ByteSequence.nat_to_bytes_be len n' *)

(* We assume 2^x < m *)
Definition nat_pow2 (m : N) (x : N) : nat_mod m.
Proof.
  remember (Z.pow 2 x mod m) as y.
  apply (GZnZ.mkznz m y).
  rewrite Heqy.
  rewrite Zmod_mod.
  reflexivity.
Defined.
