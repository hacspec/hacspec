module Rustspec.Int

type s_u64 = UInt64.t
type s_u128 = UInt128.t
type s_u32 = UInt32.t
type s_u16 = UInt16.t
type s_u8 = UInt8.t

type usize = UInt32.t

assume val s_u32_to_be_bytes : s_u32 -> FStar.Seq.lseq s_u8 4
