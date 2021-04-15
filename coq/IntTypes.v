(* From https://github.com/project-everest/hacl-star/blob/dev/lib/Lib.IntTypes.fsti *)
From Coq Require Import ZArith.

Inductive inttype : Type :=
  U1 | U8 | U16 | U32 | U64 | U128 | S8 | S16 | S32 | S64 | S128.

Definition unsigned i := 
  match i with
  | U1 | U8 | U16 | U32 | U64 | U128 => true
  | _ => false
  end.

Definition signed i :=
  match i with
  | S8 | S16 | S32 | S64 | S128 => true
  | _ => false
  end.

(* Operations on the underlying machine integer base types *)
Open Scope N_scope.

Definition numbytes i : N :=
  match i with
  | U1   => 1
  | U8   => 1
  | S8   => 1
  | U16  => 2
  | S16  => 2
  | U32  => 4
  | S32  => 4
  | U64  => 8
  | S64  => 8
  | U128 => 16
  | S128 => 16
  end.

Definition bits i : N :=
  match i with
  | U1   => 1
  | U8   => 8
  | S8   => 8
  | U16  => 16
  | S16  => 16
  | U32  => 32
  | S32  => 32
  | U64  => 64
  | S64  => 64
  | U128 => 128
  | S128 => 128
  end.
  
Definition pow2 i := N.pow i 2.

Definition modulus (t:inttype) := pow2 (bits t).

Definition maxint (t:inttype) :=
  if unsigned t then pow2 (bits t) - 1 else pow2 (bits t - 1) - 1.

Definition minint (t:inttype) :=
  if unsigned t then 0 else 0 - (pow2 (bits t - 1)).

Definition range (n:N) (t:inttype) : Type :=
  minint t <= n /\ n <= maxint t.

Definition range_t (t:inttype) := forall x, range x t.

(* PUBLIC Machine Integers *)

(* Definition pub_int_t i := match i with
  | U1   => UInt8.t{UInt8.v n < 2}
  | U8   => UInt8.t
  | U16  => UInt16.t
  | U32  => UInt32.t
  | U64  => UInt64.t
  | U128 => UInt128.t
  | S8   => Int8.t
  | S16  => Int16.t
  | S32  => Int32.t
  | S64  => Int64.t
  | S128 => Int128.t
  end.


Definition pub_int_v #t (x:pub_int_t t) : range_t t :=
  match t with
  | U1   => UInt8.v x
  | U8   => UInt8.v x
  | U16  => UInt16.v x
  | U32  => UInt32.v x
  | U64  => UInt64.v x
  | U128 => UInt128.v x
  | S8   => Int8.v x
  | S16  => Int16.v x
  | S32  => Int32.v x
  | S64  => Int64.v x
  | S128 => Int128.v x *)

(* SECRET Machine Integers *)

Inductive secrecy_level :=
  | SEC
  | PUB.

Definition sec_int_t := inttype -> Type.

Context {secret : forall {A}, A -> A}.


(* Definition sec_int_v (t:inttype) := sec_int_t t -> range_t t. *)

(* GENERIC Machine Integers *)
(* 

Definition int_t (t:inttype) (l:secrecy_level) :=
  match l with
  | PUB => pub_int_t t
  | SEC => sec_int_t t
  end.

Definition v #t #l (u:int_t t l) : range_t t :=
  match l withrange_tecrecy_level) := int_t t l

Definition sint_t (t:inttype{signed t}) (l:secrecy_level) := int_t t l

Definition uint_v #t #l (u:uint_t t l) := v u

Definition sint_v #t #l (u:sint_t t l) := v u

Inductive uint1 := uint_t U1 SEC

Inductive uint8 := uint_t U8 SEC

Inductive int8 := sint_t S8 SEC

Inductive uint16 := uint_t U16 SEC

Inductive int16 := sint_t S16 SEC

Inductive uint32 := uint_t U32 SEC

Inductive int32 := sint_t S32 SEC

Inductive uint64 := uint_t U64 SEC

Inductive int64 := sint_t S64 SEC

Inductive uint128 := uint_t U128 SEC

Inductive int128 := sint_t S128 SEC

Inductive bit_t := uint_t U1 PUB

Inductive byte_t := uint_t U8 PUB

Inductive size_t := uint_t U32 PUB

// 2019.7.19: Used only by experimental Blake2b; remove?
Inductive size128_t := uint_t U128 PUB

Inductive pub_uint8 := uint_t U8 PUB

Inductive pub_int8 := sint_t S8 PUB

Inductive pub_uint16 := uint_t U16 PUB

Inductive pub_int16 := sint_t S16 PUB

Inductive pub_uint32 := uint_t U32 PUB

Inductive pub_int32 := sint_t S32 PUB

Inductive pub_uint64 := uint_t U64 PUB

Inductive pub_int64 := sint_t S64 PUB

Inductive pub_uint128 := uint_t U128 PUB

Inductive pub_int128 := sint_t S128 PUB

///
/// Casts between mathematical and machine integers
///

Definition secret: #t:inttype => x:int_t t PUB => y:int_t t SEC{v x :=:= v y}

Definition mk_int: #t:inttype => #l:secrecy_level => n:range_t t => u:int_t t l{v u :=:= n}

Definition uint (#t:inttype{unsigned t}) (#l:secrecy_level) (n:range_t t) := mk_int #t #l n

Definition sint (#t:inttype{signed t}) (#l:secrecy_level) (n:range_t t) := mk_int #t #l n

Definition v_injective: #t:inttype => #l:secrecy_level => a:int_t t l => Lemma
  (mk_int (v #t #l a) :=:= a)
  [SMTPat (v #t #l a)]

Definition v_mk_int: #t:inttype => #l:secrecy_level => n:range_t t => Lemma
  (v #t #l (mk_int #t #l n) :=:= n)
  [SMTPat (v #t #l (mk_int #t #l n))]

Definition u1 (n:range_t U1) : u:uint1{v u :=:= n} := uint #U1 #SEC n

Definition u8 (n:range_t U8) : u:uint8{v u :=:= n} := uint #U8 #SEC n

Definition i8 (n:range_t S8) : u:int8{v u :=:= n} := sint #S8 #SEC n

Definition u16 (n:range_t U16) : u:uint16{v u :=:= n} := uint #U16 #SEC n

Definition i16 (n:range_t S16) : u:int16{v u :=:= n} := sint #S16 #SEC n

Definition u32 (n:range_t U32) : u:uint32{v u :=:= n} := uint #U32 #SEC n

Definition i32 (n:range_t S32) : u:int32{v u :=:= n} := sint #S32 #SEC n

Definition u64 (n:range_t U64) : u:uint64{v u :=:= n} := uint #U64 #SEC n

Definition i64 (n:range_t S64) : u:int64{v u :=:= n} := sint #S64 #SEC n

(* We only support 64-bit literals, hence the unexpected upper limit *)
Definition u128: n:range_t U64 => u:uint128{v #U128 u :=:= n}

Definition i128 (n:range_t S64) : u:int128{v #S128 u :=:= n}

Definition max_size_t := maxint U32

Inductive size_nat := n:nat{n <:= max_size_t}

Inductive size_pos := n:pos{n <:= max_size_t}

Definition size (n:size_nat) : size_t := uint #U32 #PUB n

Definition size_v (s:size_t) := v s

Definition byte (n:nat{n < 256}) : b:byte_t{v b :=:= n} := uint #U8 #PUB n

Definition byte_v (s:byte_t) : n:size_nat{v s :=:= n} := v s

Definition size_to_uint32: s:size_t => u:uint32{u :=:= u32 (v s)}

Definition size_to_uint64: s:size_t => u:uint64{u :=:= u64 (v s)}

Definition byte_to_uint8: s:byte_t => u:uint8{u :=:= u8 (v s)} 

*)
