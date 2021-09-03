Global Set Warnings "-ambiguous-paths".
Global Set Warnings "-uniform-inheritance".
Global Set Warnings "-auto-template".
Global Set Warnings "-disj-pattern-notation".
(*** Integers *)
From Coq Require Import ZArith List Vector.
Import ListNotations.
(* Require Import IntTypes. *)

Require Import MachineIntegers.
From Coqprime Require GZnZ.

Declare Scope hacspec_scope.

Axiom secret : forall {WS : WORDSIZE},  (@int WS) -> (@int WS). 

Axiom uint8_declassify : int8 -> int8.
Axiom int8_declassify : int8 -> int8.
Axiom uint16_declassify : int16 -> int16.
Axiom int16_declassify : int16 -> int16.
Axiom uint32_declassify : int32 -> int32.
Axiom int32_declassify : int32 -> int32.
Axiom uint64_declassify : int64 -> int64.
Axiom int64_declassify : int64 -> int64.
Axiom uint128_declassify : int128 -> int128.
Axiom int128_declassify : int128 -> int128.

Axiom uint8_classify : int8 -> int8.
Axiom int8_classify : int8 -> int8.
Axiom uint16_classify : int16 -> int16.
Axiom int16_classify : int16 -> int16.
Axiom uint32_classify : int32 -> int32.
Axiom int32_classify : int32 -> int32.
Axiom uint64_classify : int64 -> int64.
Axiom int64_classify : int64 -> int64.
Axiom uint128_classify : int128 -> int128.
Axiom int128_classify : int128 -> int128.


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
Infix "usize_shift_right" := (usize_shift_right) (at level 77) : hacspec_scope. 

(* should use size u instead of u? *)
Definition usize_shift_left (u: uint_size) (s: int32) : uint_size :=
  (rol u s).
Infix "usize_shift_left" := (usize_shift_left) (at level 77) : hacspec_scope. 
  
Definition pub_uint128_wrapping_add (x y: int128) : int128 :=
  add x y.

Definition shift_left_ `{WS : WORDSIZE} (i : @int WS) (j : uint_size) :=
  MachineIntegers.shl i (repr (from_uint_size j)).

Definition shift_right_ `{WS : WORDSIZE} (i : @int WS) (j : uint_size) :=
  MachineIntegers.shr i (repr (from_uint_size j)) .

Infix "shift_left" := (shift_left_) (at level 77) : hacspec_scope. 
Infix "shift_right" := (shift_right_) (at level 77) : hacspec_scope. 

Infix "%%" := Z.rem (at level 40, left associativity) : Z_scope.
Infix ".+" := (MachineIntegers.add) (at level 77) : hacspec_scope.
Infix ".-" := (MachineIntegers.sub) (at level 77) : hacspec_scope.
Infix ".*" := (MachineIntegers.mul) (at level 77) : hacspec_scope.
Infix "./" := (MachineIntegers.divs) (at level 77) : hacspec_scope.
Infix ".%" := (MachineIntegers.mods) (at level 77) : hacspec_scope.
Infix ".^" := (MachineIntegers.xor) (at level 77) : hacspec_scope.
Infix ".&" := (MachineIntegers.and) (at level 77) : hacspec_scope.
Infix ".|" := (MachineIntegers.or) (at level 77) : hacspec_scope.
Infix "==" := (MachineIntegers.eq) (at level 32) : hacspec_scope.
(* Definition one := (@one WORDSIZE32). *)
(* Definition zero := (@zero WORDSIZE32). *)
Notation "A × B" := (prod A B) (at level 79, left associativity) : hacspec_scope.
(*** Loops *)

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

(* Typeclass handling of default elements, for use in sequences/arrays. 
   We provide instances for the library integer types *)
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

(*** Seq *)

Definition nseq := Vector.t.

Definition seq (A : Type) := list A.

(* Automatic conversion from nseq/vector/array to seq/list *)
Global Coercion Vector.to_list : Vector.t >-> list.

Definition byte_seq := seq int8.
Definition list_len := length.

Definition seq_index {A: Type} `{Default A} (s: seq A) (i : nat) :=
  List.nth i s default.

Definition seq_len {A: Type} (s: seq A) : N := N.of_nat (length s).

Definition seq_new_ {A: Type} (init : A) (len: nat) : seq A :=
  const init len.

Definition array_from_list (A: Type) (l: list A) : nseq A (length l)
  := of_list l.

(* automatic conversion from list to array *)
Global Coercion array_from_list : list >-> nseq.


(**** Array manipulation *)


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

(* substitutes a sequence (list) into an array (nseq), given index interval  *)
(* Axiom update_sub : forall {A len }, nseq A len -> nat -> nat -> seq A -> t A len. *)
Definition update_sub {A len slen} `{Default A} (v : nseq A len) (i : nat) (n : nat) (sub : nseq A slen) : nseq A len :=
  let fix rec x acc :=
    match x with
    | 0 => acc
    (* | 0 => array_upd acc 0 (array_index sub 0) *)
    | S x => rec x (array_upd acc (i+x) (array_index sub x))
    end in
  rec (n - i + 1) v.

(* Sanity check *)
(* Compute (to_list (update_sub [1;2;3;4;5] 0 4 (of_list [9;8;7;6;12]))). *)

Definition array_from_seq
  {a: Type}
 `{Default a}
  (out_len:nat)
  (input: seq a)
  (* {H : List.length input = out_len} *)
    : nseq a out_len :=
    let out := Vector.const default out_len in
    update_sub out 0 (out_len - 1) input. 
  (* Vector.of_list input. *)

Global Coercion array_from_seq : seq >-> nseq.

Definition slice {A} (l : seq A) (i j : nat) : seq A := 
  if j <=? i then [] else firstn (j-i+1) (skipn i l).

Definition lseq_slice {A n} (l : nseq A n) (i j : nat) : nseq A _ :=
  of_list (slice (to_list l) i j).

Definition array_from_slice
  {a: Type}
 `{Default a}
  (default_value: a)
  (out_len: nat)
  (input: seq a)
  (start: nat)
  (slice_len: nat)
    : nseq a out_len :=
    let out := const default_value out_len in
    update_sub out 0 slice_len (lseq_slice (of_list input) start (start + slice_len)).
  

Definition array_slice
  {a: Type}
 `{Default a}
  (input: seq a)
  (start: nat)
  (slice_len: nat)
    : nseq a _ :=
  let out := slice input start (start + slice_len) in
  array_from_seq slice_len out.


Definition array_from_slice_range
  {a: Type}
 `{Default a}
  (default_value: a)
  (out_len: nat)
  (input: seq a)
  (start_fin: (uint_size * uint_size))
    : nseq a out_len :=
    let out := array_new_ default_value out_len in
    let (start, fin) := start_fin in
    update_sub out 0 ((from_uint_size fin) - (from_uint_size start)) (of_list (slice input (from_uint_size start) (from_uint_size fin))).

  
Definition array_slice_range
  {a: Type}
  {len : nat}
  (input: nseq a len)
  (start_fin:(uint_size * uint_size))
    : nseq a _ :=
  lseq_slice input (from_uint_size (fst start_fin)) (from_uint_size (snd start_fin)).
  
Definition array_update
  {a: Type}
 `{Default a}
  {len: nat}
  (s: nseq a len)
  (start : nat)
  (start_s: seq a)
    : nseq a len :=
    update_sub s start (length start_s) (of_list start_s).

Definition array_update_start
  {a: Type}
 `{Default a}
  {len: nat}
  (s: nseq a len)
  (start_s: seq a)
    : nseq a len :=
    update_sub s 0 (length start_s) (of_list start_s).


Definition array_len  {a: Type} {len: nat} (s: nseq a len) := len.
(* May also come up as 'length' instead of 'len' *)
Definition array_length  {a: Type} {len: nat} (s: nseq a len) := len.

(**** Seq manipulation *)

Definition seq_slice
  {a: Type}
 `{Default a}
  (s: seq a)
  (start: nat)
  (len: nat)
    : nseq a _ :=
  array_from_seq len (slice s start (start + len)).

Definition seq_slice_range
  {a: Type}
 `{Default a}
  (input: seq a)
  (start_fin:(uint_size * uint_size))
    : nseq a _ :=
  seq_slice input (from_uint_size (fst start_fin)) (from_uint_size (snd start_fin)).

(* updating a subsequence in a sequence *)
Definition seq_update
  {a: Type}
 `{Default a}
  (s: seq a)
  (start: nat)
  (input: seq a)
    : seq a :=
  update_sub (of_list s) start (length input) (of_list input).

(* updating only a single value in a sequence*)
Definition seq_upd 
  {a: Type}
 `{Default a}
  (s: seq a)
  (start: nat)
  (v: a)
    : seq a :=
  update_sub (of_list s) start 1 (of_list [v]).

Definition sub {a} (s : list a) start n := 
  slice s start (start + n).

Definition seq_update_start
  {a: Type}
 `{Default a}
  (s: seq a)
  (start_s: seq a)
    : seq a :=
    update_sub (of_list s) 0 (length start_s) (of_list start_s).

Definition array_update_slice
  {a : Type}
 `{Default a}
  {l : nat}
  (out: nseq a l)
  (start_out: nat)
  (input: nseq a l)
  (start_in: nat)
  (len: nat)
    : nseq a (length out)
  :=
  update_sub (of_list out) start_out len
    (of_list (sub input start_in len)).

Definition seq_update_slice
  {a : Type}
 `{Default a}
  (out: seq a)
  (start_out: nat)
  (input: seq a)
  (start_in: nat)
  (len: nat)
    : nseq a (length out)
  :=
  update_sub (of_list out) start_out len
    (of_list (sub input start_in len)).

Definition seq_concat
  {a : Type}
  (s1 :seq a)
  (s2: seq a)
  : nseq a _ :=
  of_list (List.rev_append s1 s2).

Definition seq_from_slice_range
  {a: Type}
 `{Default a}
  (input: seq a)
  (start_fin: (uint_size * uint_size))
  : seq a :=
  let out := array_new_ (default) (length input) in
  let (start, fin) := start_fin in
    update_sub out 0 ((from_uint_size fin) - (from_uint_size start)) (of_list (slice input (from_uint_size start) (from_uint_size fin))).

Definition seq_from_seq {A} (l : seq A) := l.


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
  : (uint_size * seq a)
    (* (requires (chunk_len * chunk_num <= Seq.length s))
    (ensures (fun '(out_len, chunk) =>
      out_len := seq_chunk_len s chunk_len chunk_num /\ LSeq.length chunk := out_len
    )) *)
 :=
  let idx_start := chunk_len * chunk_num in
  let out_len := seq_chunk_len s chunk_len chunk_num in
  (usize out_len, slice
    s idx_start (idx_start + seq_chunk_len s chunk_len chunk_num)).

Definition seq_set_chunk
  {a: Type}
 `{Default a}
  (s: seq a)
  (chunk_len: nat)
  (chunk_num: nat)
  (chunk: seq a ) : seq a :=
 let idx_start := chunk_len * chunk_num in
 let out_len := seq_chunk_len s chunk_len chunk_num in
  Vector.to_list (update_sub (of_list s) idx_start out_len (of_list chunk)).


Definition seq_num_exact_chunks {a} (l : seq a) (chunk_size : uint_size) : uint_size :=
  divs (repr (Z.of_nat (length l))) chunk_size.

(* Until #84 is fixed this returns an empty sequence if not enough *)
Definition seq_get_exact_chunk {a} (l : seq a) (chunk_size chunk_num: uint_size) : seq a :=
  let '(len, chunk) := seq_get_chunk l (from_uint_size chunk_size) (from_uint_size chunk_num) in
  if eq len chunk_size then [] else chunk.

Definition seq_set_exact_chunk {a} `{H : Default a} := @seq_set_chunk a H.

Definition seq_get_remainder_chunk : forall {a}, seq a -> uint_size -> seq a :=
  fun _ l chunk_size =>
    let chunks := seq_num_chunks l (from_uint_size chunk_size) in
    let last_chunk := if 0 <? chunks then
      chunks - 1
    else 0 in
    let (len, chunk) := seq_get_chunk l (from_uint_size chunk_size) last_chunk in
    if eq len chunk_size then
      []
    else chunk.

(**** Numeric operations *)

(* takes two nseq's and joins them using a function op : a -> a -> a *)
Definition array_join_map
  {a: Type}
 `{Default a}
  {len: nat}
  (op: a -> a -> a)
  (s1: nseq a len)
  (s2 : nseq a len) :=
  let out := s1 in
  foldi (usize 0) (usize len) (fun i out =>
    let i := from_uint_size i in
    array_upd out i (op (array_index s1 i) (array_index s2 i))
  ) out.

Infix "array_xor" := (array_join_map xor) (at level 33) : hacspec_scope.
Infix "array_add" := (array_join_map add) (at level 33) : hacspec_scope.
Infix "array_minus" := (array_join_map sub) (at level 33) : hacspec_scope.
Infix "array_mul" := (array_join_map mul) (at level 33) : hacspec_scope.
Infix "array_div" := (array_join_map divs) (at level 33) : hacspec_scope.
Infix "array_or" := (array_join_map or) (at level 33) : hacspec_scope.
Infix "array_and" := (array_join_map and) (at level 33) : hacspec_scope.

Definition array_eq_
  {a: Type}
  {len: nat}
  (eq: a -> a -> bool)
  (s1: nseq a len)
  (s2 : nseq a len)
    : bool := Vector.eqb _ eq s1 s2.

Infix "array_eq" := (array_eq_ eq) (at level 33) : hacspec_scope.
Infix "array_neq" := (fun s1 s2 => negb (array_eq_ eq s1 s2)) (at level 33) : hacspec_scope.


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


Definition nat_mod (p : Z) : Set := GZnZ.znz p.


Definition nat_mod_equal {p} (a b : nat_mod p) : bool :=
  Z.eqb (GZnZ.val p a) (GZnZ.val p b).

Definition nat_mod_zero {p} : nat_mod p := GZnZ.zero p.
Definition nat_mod_one {p} : nat_mod p := GZnZ.one p.
Definition nat_mod_two {p} : nat_mod p := GZnZ.mkznz p _ (GZnZ.modz p 2).


(* convenience coercions from nat_mod to Z and N *)
(* Coercion Z.of_N : N >-> Z. *)

Definition nat_mod_add {n : Z} (a : nat_mod n) (b : nat_mod n) : nat_mod n := GZnZ.add n a b.
   
Infix "+%" := nat_mod_add (at level 33) : hacspec_scope.

Definition nat_mod_mul {n : Z} (a:nat_mod n) (b:nat_mod n) : nat_mod n := GZnZ.add n a b.
Infix "*%" := nat_mod_mul (at level 33) : hacspec_scope.

Definition nat_mod_sub {n : Z} (a:nat_mod n) (b:nat_mod n) : nat_mod n := GZnZ.sub n a b.
Infix "-%" := nat_mod_mul (at level 33) : hacspec_scope.

Definition nat_mod_div {n : Z} (a:nat_mod n) (b:nat_mod n) : nat_mod n := GZnZ.div n a b.
Infix "/%" := nat_mod_mul (at level 33) : hacspec_scope.

Definition nat_modeg {n : Z} (a:nat_mod n) : nat_mod n := GZnZ.opp n a.

Definition nat_mod_inv {n : Z} (a:nat_mod n) : nat_mod n := GZnZ.inv n a.

Definition nat_mod_exp {p : Z} (a:nat_mod p) (n : uint_size) : nat_mod p :=
  let n : nat := Z.to_nat (from_uint_size n) in 
  let fix exp_ (e : nat_mod p) (n : nat) :=
    match n with
    | 0%nat => nat_mod_one
    | S n => nat_mod_mul a (exp_ a n)
    end in
  exp_ a n.

Definition nat_mod_pow {p} := @nat_mod_exp p.

Close Scope nat_scope.
Open Scope Z_scope.

(* We assume x < m *)
Definition nat_mod_from_secret_literal {m : Z} (x:int128) : nat_mod m.
Proof.
  unfold nat_mod.
  (* since we assume x < m, it will be true that (unsigned x) = (unsigned x) mod m  *)
  remember ((unsigned x) mod m) as zmodm.
  apply (GZnZ.mkznz m zmodm).
  rewrite Heqzmodm.
  rewrite Zmod_mod.
  reflexivity.
Defined.

Definition nat_mod_from_literal (m : Z) (x:int128) : nat_mod m := nat_mod_from_secret_literal x.

Axiom nat_mod_to_byte_seq_le : forall {n : Z}, nat_mod n -> seq int8.
Axiom nat_mod_to_byte_seq_be : forall {n : Z}, nat_mod n -> seq int8.
Axiom nat_mod_to_public_byte_seq_le : forall (n : Z), nat_mod n -> seq int8.
Axiom nat_mod_to_public_byte_seq_be : forall (n : Z), nat_mod n -> seq int8.

Definition nat_mod_bit {n : Z} (a : nat_mod n) (i : uint_size) :=
  Z.testbit (GZnZ.val n a) (from_uint_size i).

(* Alias for nat_mod_bit *)
Definition nat_get_mod_bit {p} (a : nat_mod p) := nat_mod_bit a.
(*   
Definition nat_mod_to_public_byte_seq_le (n: pos)  (len: uint_size) (x: nat_mod_mod n) : lseq pub_uint8 len =
  Definition n' := n % (pow2 (8 * len)) in
  Lib.ByteSequence.nat_mod_to_bytes_le len n'*)

(* Definition nat_to_public_byte_seq_be (n: pos)  (len: uint_size) (x: nat_mod n) : lseq pub_uint8 len =
  Definition n' := n % (pow2 (8 * len)) in
  Lib.ByteSequence.nat_to_bytes_be len n' *)

Axiom array_declassify_eq : forall  {A l}, nseq A l -> nseq A l -> bool.
Axiom array_to_le_uint32s : forall {A l}, nseq A l -> nseq uint32 l.
Axiom array_to_be_uint32s : forall {l}, nseq uint8 l -> nseq uint32 (l/4).
Axiom array_to_le_bytes : forall {A l}, nseq A l -> seq uint8.
Axiom array_to_be_bytes : forall {A l}, nseq A l -> seq uint8.
Axiom nat_mod_from_byte_seq_le : forall  {A n}, seq A -> nat_mod n.  
Axiom most_significant_bit : forall {m}, nat_mod m -> uint_size -> uint_size.


(* We assume 2^x < m *)
Definition nat_mod_pow2 (m : Z) (x : N) : nat_mod m.
Proof.
  remember (Z.pow 2 (Z.of_N x) mod m) as y.
  apply (GZnZ.mkznz m y).
  rewrite Heqy.
  rewrite Zmod_mod.
  reflexivity.
Defined.


Section Casting.

  (* Type casts, as defined in Section 4.5 in https://arxiv.org/pdf/1106.3448.pdf *)
  Class Cast A B := cast : A -> B.

  Arguments cast {_} _ {_}.

  Notation "' x" := (cast _ x) (at level 20) : hacspec_scope. 
  Open Scope hacspec_scope.

  (* Casting to self is always possible *)
  Global Instance cast_self {A} : Cast A A := {
    cast a := a
  }.

  Global Instance cast_transitive {A B C} `{Hab: Cast A B} `{Hbc: Cast B C} : Cast A C := {
    cast a := Hbc (Hab a)
  }.

  Global Instance cast_prod {A B C D} `{Cast A B} `{Cast C D} : Cast (A * C) (B * D) := {
    cast '(a, c) := ('a, 'c)
  }.

  Global Instance cast_option {A B} `{Cast A B} : Cast (option A) (option B) := {
    cast a := match a with Some a => Some ('a) | None => None end
  }.

  Global Instance cast_option_b {A B} `{Cast A B} : Cast A (option B) := {
    cast a := Some ('a)
  }.

  (* Global Instances for common types *)

  Global Instance cast_nat_to_N : Cast nat N := {
    cast := N.of_nat
  }.

  Global Instance cast_N_to_Z : Cast N Z := {
    cast := Z.of_N
  }.
  
  Global Instance cast_Z_to_int {WORDSIZE} : Cast Z (@int WORDSIZE) := {
    cast n := repr n
  }.

  Global Instance cast_natmod_to_Z {p} : Cast (nat_mod p) Z := {
    cast n := GZnZ.val p n
  }.

  (* Note: should be aware of typeclass resolution with int/uint since they are just aliases of each other currently *)
  Global Instance cast_int8_to_uint32 : Cast int8 uint32 := {
    cast n := repr (unsigned n)
  }.
  Global Instance cast_int8_to_int32 : Cast int8 int32 := {
    cast n := repr (signed n)
  }.

  Global Instance cast_uint8_to_uint32 : Cast uint8 uint32 := {
    cast n := repr (unsigned n)
  }.

  Global Instance cast_int_to_nat `{WORDSIZE} : Cast int nat := {
    cast n := Z.to_nat (signed n)
  }.

  Close Scope hacspec_scope.
End Casting.


Global Arguments pair {_ _} & _ _.
Global Arguments id {_} & _. 
Section Coercions.
  (* First, in order to have automatic coercions for tuples, we add bidirectionality hints: *)

  (* Integer coercions *)
  (* We have nat >-> N >-> Z >-> int/int32 *)
  (* and uint >-> Z *)
  (* and N >-> nat *)

  Global Coercion N.to_nat : N >-> nat.
  Global Coercion Z.of_N : N >-> Z.

  Global Coercion repr : Z >-> int.
  
  Definition Z_to_int `{WORDSIZE} (n : Z) : int := repr n.
  Global Coercion  Z_to_int : Z >-> int.

  Definition Z_to_uint_size (n : Z) : uint_size := repr n.
  Global Coercion Z_to_uint_size : Z >-> uint_size.
  Definition Z_to_int_size (n : Z) : int_size := repr n.
  Global Coercion Z_to_int_size : Z >-> int_size.

  Definition N_to_int `{WORDSIZE} (n : N) : int := repr (Z.of_N n).
  Global Coercion N.of_nat : nat >-> N.
  Global Coercion N_to_int : N >-> int.
  Definition N_to_uint_size (n : Z) : uint_size := repr n.
  Global Coercion N_to_uint_size : Z >-> uint_size.
  Definition nat_to_int `{WORDSIZE} (n : nat) := repr (Z.of_nat n).
  Global Coercion nat_to_int : nat >-> int.  

  Definition uint_size_to_nat (n : uint_size) : nat := from_uint_size n.
  Global Coercion uint_size_to_nat : uint_size >-> nat.

  Definition uint_size_to_Z (n : uint_size) : Z := from_uint_size n.
  Global Coercion uint_size_to_Z : uint_size >-> Z.

  Definition uint32_to_nat (n : uint32) : nat := unsigned n.
  Global Coercion uint32_to_nat : uint32 >-> nat.
  

  Global Coercion GZnZ.val : GZnZ.znz >-> Z.

  Definition int8_to_nat (n : int8) : nat := unsigned n.
  Global Coercion int8_to_nat : int8 >-> nat.
  Definition int16_to_nat (n : int16) : nat := unsigned n.
  Global Coercion int16_to_nat : int16 >-> nat.
  Definition int32_to_nat (n : int32) : nat := unsigned n.
  Global Coercion int32_to_nat : int32 >-> nat.
  Definition int64_to_nat (n : int64) : nat := unsigned n.
  Global Coercion int64_to_nat : int64 >-> nat.
  Definition int128_to_nat (n : int128) : nat := unsigned n.
  Global Coercion int128_to_nat : int128 >-> nat.

  (* coercions int8 >-> int16 >-> ... int128 *)

  Definition int8_to_int16 (n : int8) : int16 := repr n.
  Global Coercion int8_to_int16 : int8 >-> int16.

  Definition int8_to_int32 (n : int8) : int32 := repr n.
  Global Coercion int8_to_int32 : int8 >-> int32.

  Definition int16_to_int32 (n : int16) : int32 := repr n.
  Global Coercion int16_to_int32 : int16 >-> int32.

  Definition int32_to_int64 (n : int32) : int64 := repr n.
  Global Coercion int32_to_int64 : int32 >-> int64.

  Definition int64_to_int128 (n : int64) : int128 := repr n.
  Global Coercion int64_to_int128 : int64 >-> int128.

  Definition int32_to_int128 (n : int32) : int128 := repr n.
  Global Coercion int32_to_int128 : int32 >-> int128.

  Definition uint_size_to_int64 (n : uint_size) : int64 := repr n.
  Global Coercion uint_size_to_int64 : uint_size >-> int64.
  

  (* coercions into nat_mod *)
  Definition Z_in_nat_mod {m : Z} (x:Z) : nat_mod m.
  Proof.
    unfold nat_mod.
    remember ((x) mod m) as zmodm.
    apply (GZnZ.mkznz m zmodm).
    rewrite Heqzmodm.
    rewrite Zmod_mod.
    reflexivity.
  Defined.
  (* Global Coercion Z_in_nat_mod : Z >-> nat_mod.  *)

  Definition int_in_nat_mod {m : Z} `{WORDSIZE} (x:int) : nat_mod m.
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
  Global Coercion int_in_nat_mod : int >-> nat_mod.
   
  Definition uint_size_in_nat_mod (n : uint_size) : nat_mod 16 := int_in_nat_mod n.
  Global Coercion uint_size_in_nat_mod : uint_size >-> nat_mod.

End Coercions.


(*** Casting *)


Definition uint64_from_uint8 (n : int8) : int64 := repr n.
Definition uint8_from_uint64 (n : int8) : int64 := repr n.


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

Definition nat_mod_val (p : Z) (a : nat_mod p) : Z := GZnZ.val p a.

Axiom nat_mod_eqb_spec : forall {p} (a b : nat_mod p), Z.eqb (nat_mod_val p a) (nat_mod_val p b) = true -> a = b.

Global Instance nat_mod_eqdec {p} : EqDec (nat_mod p) := {
  eqb a b := Z.eqb (nat_mod_val p a) (nat_mod_val p b);
  eqb_leibniz := nat_mod_eqb_spec;
}.

Global Instance nat_mod_comparable `{p : Z} : Comparable (nat_mod p) := {
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

(*** Result *)

Inductive result (a: Type) (b: Type) :=
  | Ok : a -> result a b
  | Err : b -> result a b.

Arguments Ok {_ _}.
Arguments Err {_ _}.
