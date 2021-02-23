
(* Require Import FStar.Mul. *)

(*** Integers *)
From Coq Require Import ZArith.
(* Require Import Int.PArray. *)
(* From Coq Require Import Numbers.Cyclic.Abstract.CyclicAxioms. *)
From Coq Require Import Numbers.Cyclic.ZModulo.ZModulo.


(**** Usize  *)
(* TODO check this *)
Definition U32 : N := 2^32 - 1.
Definition S32 : Z := 2^31 - 1.

Module uint32 : PositiveNotOne.
  Definition p : positive := 2^32 - 1.
  Theorem not_one : p <> 1%positive.
  Proof. discriminate. Qed.    
End uint32.

Module U32 := ZModuloCyclicType uint32. Import U32.
  

(* 
let uint_size = range_t U32
let int_size = range_t S32 *)
Open Scope N_scope.
Definition uint_size := {n:N | n <= U32}.
Open Scope Z_scope.
Definition int_size := {n:Z | n <= S32}.

(* Definition usize (n:range_t U32) : u:uint_size{u == n} := n *)
Definition usize := uint_size.

(* Definition isize (n:range_t S32) : u:int_size{u == n} := n *)
Definition isize (n : {n : n < S32} : {u : u = n}:= int_size.

(**** Public integers *)

Definition pub_u8 (n:range_t U8) : u:pub_uint8{v u == n} := uint #U8 #PUB n

Definition pub_i8 (n:range_t S8) : u:pub_int8{v u == n} := sint #S8 #PUB n

Definition pub_u16 (n:range_t U16) : u:pub_uint16{v u == n} := uint #U16 #PUB n

Definition pub_i16 (n:range_t S16) : u:pub_int16{v u == n} := sint #S16 #PUB n

Definition pub_u32 (n:range_t U32) : u:pub_uint32{v u == n} := uint #U32 #PUB n

Definition pub_i32 (n:range_t S32) : u:pub_int32{v u == n} := sint #S32 #PUB n

Definition pub_u64 (n:range_t U64) : u:pub_uint64{v u == n} := uint #U64 #PUB n

Definition pub_i64 (n:range_t S64) : u:pub_int64{v u == n} := sint #S64 #PUB n

Definition pub_u128 (n:range_t U128) : u:pub_uint128{v u == n} := uint #U128 #PUB n

Definition pub_i128 (n:range_t S128) : u:pub_int128{v u == n} := sint #S128 #PUB n

(**** Operations *)

Definition uint8_rotate_left (u: uint8) (s: uint_size{s > 0 /\ s < 8}) : uint8 =
  rotate_left u (size s)

Definition uint8_rotate_right (u: uint8) (s: uint_size{s > 0 /\ s < 8}) : uint8 =
  rotate_right u (size s)

Definition uint16_rotate_left (u: uint16) (s: uint_size{s > 0 /\ s < 16}) : uint16 =
  rotate_left u (size s)

Definition uint16_rotate_right (u: uint16) (s: uint_size{s > 0 /\ s < 16}) : uint16 =
  rotate_right u (size s)

Definition uint32_rotate_left (u: uint32) (s: uint_size{s > 0 /\ s < 32}) : uint32 =
  rotate_left u (size s)

Definition uint32_rotate_right (u: uint32) (s: uint_size{s > 0 /\ s < 32}) : uint32 =
  rotate_right u (size s)

Definition uint64_rotate_left (u: uint64) (s: uint_size{s > 0 /\ s < 64}) : uint64 =
  rotate_left u (size s)

Definition uint64_rotate_right (u: uint64) (s: uint_size{s > 0 /\ s < 64}) : uint64 =
  rotate_right u (size s)

Definition uint128_rotate_left (u: uint128) (s: uint_size{s > 0 /\ s < 128}) : uint128 =
  rotate_left u (size s)

Definition uint128_rotate_right (u: uint128) (s: uint_size{s > 0 /\ s < 128}) : uint128 =
  rotate_right u (size s)

Definition usize_shift_right (u: uint_size) (s: pub_uint32{v s < 32}) : uint_size =
  v (shift_right (size u) s)

Definition usize_shift_left (u: uint_size) (s: pub_uint32{v s < 32}) : uint_size =
  v (shift_left (size u) s)

Definition pub_uint128_wrapping_add (x y: pub_uint128) : pub_uint128 =
  x +. y

(*** Loops *)

Definition rec foldi_
  (#acc: Type)
  (cur_i: uint_size)
  (hi: uint_size{cur_i <:= hi})
  (f: (i:uint_size{i < hi}) -> acc -> acc)
  (cur: acc)
    : Tot acc (decreases (hi - cur_i))
  =
  if cur_i := hi then cur else
  foldi_ (cur_i + 1) hi f (f cur_i cur)

Definition foldi
  (#acc: Type)
  (lo: uint_size)
  (hi: uint_size{lo <:= hi})
  (f: (i:uint_size{i < hi}) -> acc -> acc)
  (init: acc)
    : acc
  =
  foldi_ lo hi f init

(*** Seq *)

module LSeq := Lib.Sequence
module LBSeq := Lib.ByteSequence

Definition lseq (a: Type) (len: uint_size) := LSeq.lseq a len

Definition seq (a: Type) := s:LSeq.seq a{range (LSeq.length s) U32}
 Definition byte_seq := seq uint8

Definition nseq (a: Type) (len: nat) := s:LSeq.seq a{LSeq.length s == len}

Definition seq_len (#a: Type) (s: seq a) : nat := Seq.length s

Definition seq_new_ (#a: Type) (init:a) (len: uint_size) : lseq a len =
  Seq.create len init

Definition array_from_list
  (#a: Type)
  (l: list a{List.Tot.length l <:= max_size_t})
    : lseq a (List.Tot.length l)
  =
  LSeq.of_list l

(**** Array manipulation *)


Definition array_new_ (#a: Type) (init:a) (len: uint_size)  : lseq a len =
  LSeq.create len init

Definition array_index (#a: Type) (#len:uint_size) (s: lseq a len) (i: uint_size{i < len}) : a =
  LSeq.index s i

Definition array_upd (#a: Type) (#len:uint_size) (s: lseq a len) (i: uint_size{i < len}) (new_v: a) : lseq a len := LSeq.upd s i new_v

Definition array_from_seq
  (#a: Type)
  (out_len:uint_size)
  (input: seq a{Seq.length input := out_len})
    : lseq a out_len
  := input

Definition array_from_slice
  (#a: Type)
  (default_value: a)
  (out_len: uint_size)
  (input: seq a)
  (start: uint_size)
  (slice_len: uint_size{start + slice_len <:= LSeq.length input /\ slice_len <:= out_len})
    : lseq a out_len
  =
  Definition out := LSeq.create out_len default_value in
  LSeq.update_sub out 0 slice_len (LSeq.slice #a #(Seq.length input) input start (start + slice_len))

Definition array_slice
  (#a: Type)
  (input: seq a)
  (start: uint_size)
  (slice_len: uint_size{start + slice_len <:= LSeq.length input})
    : lseq a slice_len
  =
  Seq.slice input start (start + slice_len)

Definition array_from_slice_range
  (#a: Type)
  (default_value: a)
  (out_len: uint_size)
  (input: seq a)
  (start_fin: (uint_size & uint_size){
     fst start_fin >:= 0 /\ snd start_fin <:= LSeq.length input /\ snd start_fin >:= fst start_fin /\
     snd start_fin - fst start_fin <:= out_len
   })
    : lseq a out_len
  =
  Definition out := array_new_ default_value out_len in
  Definition (start, fin) := start_fin in
  LSeq.update_sub out 0 (fin - start) (Seq.slice input start fin)

Definition array_slice_range
  (#a: Type)
  (#len:uint_size)
  (input: lseq a len)
  (start_fin:(uint_size & uint_size){
    fst start_fin >:= 0 /\ snd start_fin <:= len /\ snd start_fin >:= fst start_fin
  })
    : lseq a (snd start_fin - fst start_fin)
  =
  Definition (start, fin) := start_fin in
  LSeq.slice input start fin

Definition array_update_start
  (#a: Type)
  (#len: uint_size)
  (s: lseq a len)
  (start_s: seq a{Seq.length start_s <:= len})
    : lseq a len
  =
  LSeq.update_sub s 0 (Seq.length start_s) start_s

Definition array_len  (#a: Type) (#len: uint_size) (s: lseq a len) := len

(**** Seq manipulation *)

Definition seq_slice
  (#a: Type)
  (s: seq a)
  (start: uint_size)
  (len: uint_size{start + len <:= LSeq.length s})
    : lseq a len
  =
  LSeq.slice #a #(Seq.length s) s start (start + len)

Definition seq_update
  (#a: Type)
  (s: seq a)
  (start: uint_size)
  (input: seq a{start + LSeq.length input <:= LSeq.length s})
    : nseq a (LSeq.length s)
  =
  LSeq.update_sub #a #(LSeq.length s) s start (LSeq.length input) input

Definition seq_concat
  (#a: Type)
  (s1 :seq a)
  (s2: seq a{range (LSeq.length s1 + LSeq.length s2) U32})
  : lseq a (LSeq.length s1 + LSeq.length s2)
  =
  LSeq.concat #a #(LSeq.length s1) #(LSeq.length s2) s1 s2


(**** Chunking *)

Definition seq_num_chunks (#a: Type) (s: seq a) (chunk_len: uint_size{chunk_len > 0}) : uint_size =
  (Seq.length s + chunk_len - 1) / chunk_len

Definition seq_chunk_len
  (#a: Type)
  (s: seq a)
  (chunk_len: uint_size)
  (chunk_num: uint_size{chunk_len * chunk_num <:= Seq.length s})
    : Tot (out_len:uint_size{out_len <:= chunk_len})
  =
  Definition idx_start := chunk_len * chunk_num in
  if idx_start + chunk_len > Seq.length s then
    Seq.length s - idx_start
  else
    chunk_len

Definition seq_chunk_same_len_same_chunk_len
  (#a: Type)
  (s1 s2: seq a)
  (chunk_len: uint_size)
  (chunk_num: uint_size)
  : Lemma
    (requires (LSeq.length s1 := LSeq.length s2 /\ chunk_len * chunk_num <:= Seq.length s1))
    (ensures (seq_chunk_len s1 chunk_len chunk_num := seq_chunk_len s2 chunk_len chunk_num))
    [SMTPat (seq_chunk_len s1 chunk_len chunk_num); SMTPat (seq_chunk_len s2 chunk_len chunk_num)]
  =
  ()

Definition seq_get_chunk
  (#a: Type)
  (s: seq a)
  (chunk_len: uint_size)
  (chunk_num: uint_size)
  : Pure (uint_size & seq a)
    (requires (chunk_len * chunk_num <:= Seq.length s))
    (ensures (fun (out_len, chunk) ->
      out_len := seq_chunk_len s chunk_len chunk_num /\ LSeq.length chunk := out_len
    ))
  =
  Definition idx_start := chunk_len * chunk_num in
  Definition out_len := seq_chunk_len s chunk_len chunk_num in
  (out_len, LSeq.slice #a #(Seq.length s)
    s idx_start (idx_start + seq_chunk_len s chunk_len chunk_num))

Definition seq_set_chunk
  (#a: Type)
  (#len:uint_size) (* change to nseq but update_sub missing for nseq *)
  (s: lseq a len)
  (chunk_len: uint_size)
  (chunk_num: uint_size)
  (chunk: seq a )
    : Pure (lseq a len)
      (requires (
        chunk_len * chunk_num <:= Seq.length s /\
        LSeq.length chunk := seq_chunk_len s chunk_len chunk_num
      ))
      (ensures (fun out -> True))
  =
  Definition idx_start := chunk_len * chunk_num in
  Definition out_len := seq_chunk_len s chunk_len chunk_num in
  LSeq.update_sub s idx_start out_len chunk

(**** Numeric operations *)

Definition array_xor
  (#a: Type)
  (#len: uint_size)
  (xor: a -> a -> a)
  (s1: lseq a len)
  (s2 : lseq a len)
    : lseq a len
  =
  Definition out := s1 in
  foldi 0 len (fun i out ->
    array_upd out i (array_index s1 i `xor` array_index s2 i)
  ) out

Definition array_eq
  (#a: Type)
  (#len: uint_size)
  (eq: a -> a -> bool)
  (s1: lseq a len)
  (s2 : lseq a len)
    : bool
  =
  Definition out := true in
  foldi 0 len (fun i out ->
    out && (array_index s1 i `eq` array_index s2 i)
  ) out

(**** Integers to arrays *)

Definition uint32_to_le_bytes (x: uint32) : lseq uint8 4 =
  LBSeq.uint_to_bytes_le x

Definition uint32_to_be_bytes (x: uint32) : lseq uint8 4 =
  LBSeq.uint_to_bytes_be x

Definition uint32_from_le_bytes (s: lseq uint8 4) : uint32 =
  LBSeq.uint_from_bytes_le s

Definition uint32_from_be_bytes (s: lseq uint8 4) : uint32 =
  LBSeq.uint_from_bytes_be s

Definition uint64_to_le_bytes (x: uint64) : lseq uint8 8 =
  LBSeq.uint_to_bytes_le x

Definition uint64_to_be_bytes (x: uint64) : lseq uint8 8 =
  LBSeq.uint_to_bytes_be x

Definition uint64_from_le_bytes (s: lseq uint8 8) : uint64 =
  LBSeq.uint_from_bytes_le s

Definition uint64_from_be_bytes (s: lseq uint8 8) : uint64 =
  LBSeq.uint_from_bytes_be s

Definition uint128_to_le_bytes (x: uint128) : lseq uint8 16 =
  LBSeq.uint_to_bytes_le x

Definition uint128_to_be_bytes (x: uint128) : lseq uint8 16 =
  LBSeq.uint_to_bytes_be x

Definition uint128_from_le_bytes (input: lseq uint8 16) : uint128 =
  LBSeq.uint_from_bytes_le input

Definition uint128_from_be_bytes (s: lseq uint8 16) : uint128 =
  LBSeq.uint_from_bytes_be s

Definition u32_to_le_bytes (x: pub_uint32) : lseq pub_uint8 4 =
  LBSeq.uint_to_bytes_le x

Definition u32_to_be_bytes (x: pub_uint32) : lseq pub_uint8 4 =
  LBSeq.uint_to_bytes_be x

Definition u32_from_le_bytes (s: lseq pub_uint8 4) : pub_uint32 =
  LBSeq.uint_from_bytes_le s

Definition u32_from_be_bytes (s: lseq pub_uint8 4) : pub_uint32 =
  LBSeq.uint_from_bytes_be s

Definition u64_to_le_bytes (x: pub_uint64) : lseq pub_uint8 8 =
  LBSeq.uint_to_bytes_le x

Definition u64_to_be_bytes (x: pub_uint64) : lseq pub_uint8 8 =
  LBSeq.uint_to_bytes_be x

Definition u64_from_le_bytes (s: lseq pub_uint8 8) : pub_uint64 =
  LBSeq.uint_from_bytes_le s

Definition u64_from_be_bytes (s: lseq pub_uint8 8) : pub_uint64 =
  LBSeq.uint_from_bytes_be s

Definition u128_to_le_bytes (x: pub_uint128) : lseq pub_uint8 16 =
  LBSeq.uint_to_bytes_le x

Definition u128_to_be_bytes (x: pub_uint128) : lseq pub_uint8 16 =
  LBSeq.uint_to_bytes_be x

Definition u128_from_le_bytes (input: lseq pub_uint8 16) : pub_uint128 =
  LBSeq.uint_from_bytes_le input

Definition u128_from_be_bytes (s: lseq pub_uint8 16) : pub_uint128 =
  LBSeq.uint_from_bytes_be s

(*** Nats *)

Definition nat_mod (n: nat) := x:nat{x < n}

val (+%) (#n:pos) (a:nat_mod n) (b:nat_mod n) : nat_mod n
Definition (+%) #n a b := (a + b) % n

val ( *% ) (#n:pos) (a:nat_mod n) (b:nat_mod n) : nat_mod n
Definition ( *% ) #n a b := (a * b) % n

Definition nat_from_secret_literal (m:pos) (x:uint128{v x < m}) : n:nat_mod m{v x == n} =
  v x

Definition nat_from_literal (m: pos) (x:pub_uint128{v x < m}) : n:nat_mod m{v x == n} =
  v x

Definition nat_to_public_byte_seq_le (n: pos)  (len: uint_size) (x: nat_mod n) : lseq pub_uint8 len =
  Definition n' := n % (pow2 (8 * len)) in
  Lib.ByteSequence.nat_to_bytes_le len n'

Definition nat_to_public_byte_seq_be (n: pos)  (len: uint_size) (x: nat_mod n) : lseq pub_uint8 len =
  Definition n' := n % (pow2 (8 * len)) in
  Lib.ByteSequence.nat_to_bytes_be len n'


Definition nat_pow2 (m:pos) (x: nat{pow2 x < m}) : nat_mod m := pow2 x

End Lib.