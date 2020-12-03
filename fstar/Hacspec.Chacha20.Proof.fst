module Hacspec.Chacha20.Proof

open Hacspec.Lib
open FStar.Mul

module Orig = Spec.Chacha20
module New = Hacspec.Chacha20
module Seq = Lib.Sequence

#set-options "--fuel 0 --ifuel 0 --z3rlimit 30"

let line_equiv
  (a : New.state_idx)
  (b : New.state_idx)
  (d : New.state_idx)
  (s : uint_size{
  (**) s > 0 /\ s < 32
  })
  (m : New.state)
    : Lemma (New.chacha_line a b d s m == Orig.line a b d (size s) m)
  [SMTPat (New.chacha_line a b d s m)]
  =
  assert(New.chacha_line a b d s m `Seq.equal` Orig.line a b d (size s) m)

let quarter_round_equiv
  (a : New.state_idx)
  (b : New.state_idx)
  (c : New.state_idx)
  (d : New.state_idx)
  (state : New.state)
    : Lemma (New.chacha_quarter_round a b c d state == Orig.quarter_round a b c d state)
  [SMTPat (New.chacha_quarter_round a b c d state)]
  =
  ()

let double_round_equiv (state: New.state)
    : Lemma (New.chacha_double_round state == Orig.double_round state)
  [SMTPat (New.chacha_double_round state)]
  =
  ()

let constants_equiv ()
    : Lemma (forall (i:nat{i < 4}).
      v (Seq.index #_ #4 (New.chacha20_constants_init ()) i) ==
      v (Seq.index Orig.chacha20_constants i)
    )
  =
  let l = [Orig.c0;Orig.c1;Orig.c2;Orig.c3] in
  assert_norm(List.Tot.length l == 4);
  assert_norm(List.Tot.index l 0 == Orig.c0);
  assert_norm(List.Tot.index l 1 == Orig.c1);
  assert_norm(List.Tot.index l 2 == Orig.c2);
  assert_norm(List.Tot.index l 3 == Orig.c3)

let key_to_u32s_equiv (key: New.key)
    : Lemma (New.chacha20_key_to_u32s key == Lib.ByteSequence.uints_from_bytes_le #U32 #SEC #8 key)
  [SMTPat (New.chacha20_key_to_u32s key)]
  =
  let aux (i:nat{i < 8}) : Lemma (
    Seq.index #_ #8 (New.chacha20_key_to_u32s key) i ==
    Seq.index (Lib.ByteSequence.uints_from_bytes_le #U32 #SEC #8 key) i
  ) =
    Lib.ByteSequence.index_uints_from_bytes_le #U32 #SEC #8 key i
  in
  Classical.forall_intro aux;
  assert(
    New.chacha20_key_to_u32s key `Seq.equal`
    Lib.ByteSequence.uints_from_bytes_le #U32 #SEC #8 key
  )

let iv_to_u32s_equiv (iv: New.iv)
    : Lemma (New.chacha20_iv_to_u32s iv == Lib.ByteSequence.uints_from_bytes_le #U32 #SEC #3 iv)
  [SMTPat (New.chacha20_iv_to_u32s iv)]
  =
  let aux (i:nat{i < 3}) : Lemma (
    Seq.index #_ #3 (New.chacha20_iv_to_u32s iv) i ==
    Seq.index (Lib.ByteSequence.uints_from_bytes_le #U32 #SEC #3 iv) i
  ) =
    Lib.ByteSequence.index_uints_from_bytes_le #U32 #SEC #3 iv i
  in
  Classical.forall_intro aux;
  assert(
    New.chacha20_iv_to_u32s iv `Seq.equal`
    Lib.ByteSequence.uints_from_bytes_le #U32 #SEC #3 iv
  )

let ctr_to_seq_equiv (ctr: uint32)
    : Lemma (New.chacha20_ctr_to_seq ctr == FStar.Seq.init 1 (fun _ -> ctr))
  [SMTPat (New.chacha20_ctr_to_seq ctr)]
  =
  assert(New.chacha20_ctr_to_seq ctr `Seq.equal #_ #1` FStar.Seq.init 1 (fun _ -> ctr))

#push-options "--z3rlimit 50"
let chacha_block_init_equiv (key: New.key) (ctr: uint32) (iv: New.iv)
    : Lemma (New.chacha_block_init key ctr iv == Orig.chacha20_init key iv (v ctr))
  =
  let st = Seq.create 16 (u32 0) in
  let st = Seq.update_sub st 0 4 (Seq.map Lib.IntTypes.secret Orig.chacha20_constants) in
  constants_equiv ();
  assert(Seq.sub st 0 4 `Seq.equal` New.chacha20_constants_init ());
  let st = Seq.update_sub st 4 8 (Lib.ByteSequence.uints_from_bytes_le #U32 #SEC #8 key) in
  assert(Seq.sub st 0 4 `Seq.equal` New.chacha20_constants_init ());
  assert(Seq.sub st 4 8 `Seq.equal` New.chacha20_key_to_u32s key);
  let st = Seq.(st.[12] <- ctr) in
  assert(Seq.sub st 0 4 `Seq.equal` New.chacha20_constants_init ());
  assert(Seq.sub st 4 8 `Seq.equal` New.chacha20_key_to_u32s key);
  assert(Seq.sub st 12 1 `Seq.equal` New.chacha20_ctr_to_seq ctr);
  let st = Seq.update_sub st 13 3 (Lib.ByteSequence.uints_from_bytes_le #U32 #SEC #3 iv) in
  assert(Seq.sub st 0 4 `Seq.equal` New.chacha20_constants_init ());
  assert(Seq.sub st 4 8 `Seq.equal` New.chacha20_key_to_u32s key);
  assert(Seq.sub st 12 1 `Seq.equal` New.chacha20_ctr_to_seq ctr);
  assert(Seq.sub st 13 3 `Seq.equal` New.chacha20_iv_to_u32s iv);
  assert(st `Seq.equal` Orig.chacha20_init key iv (v ctr));
  assert(New.chacha_block_init key ctr iv `Seq.equal` Orig.chacha20_init key iv (v ctr))
#pop-options

let chacha_block_inner_equiv_orig (key: New.key) (ctr: uint32) (iv: New.iv) =
  let st0 = Orig.chacha20_init key iv (v ctr) in
  let st = Orig.chacha20_add_counter st0 (v ctr) in
  let st = Orig.rounds st in
  let st = Orig.sum_state st st0 in
  Orig.chacha20_add_counter st (v ctr)

let rec repeat_left (#a: Type) (n: nat) (f: a -> a) (init: a) =
  if n = 0 then init else repeat_left (n-1) f (f init)

#push-options "--fuel 1"
let rec repeat_left_lemma (#a: Type) (n: nat) (f: a -> a) (init: a)
  : Lemma (f (repeat_left n f init) == repeat_left n f (f init))
  =
  if n = 0 then () else repeat_left_lemma (n-1) f (f init)
#pop-options

#push-options "--fuel 1"
let rec repeat_left_equals_repeat (#a: Type) (n: nat) (f: a -> a) (init: a)
    : Lemma (Lib.LoopCombinators.repeat n f init == repeat_left n f init)
  =
  if n = 0 then
    Lib.LoopCombinators.eq_repeat0 f init
  else begin
    Lib.LoopCombinators.unfold_repeat n f init (n-1);
    repeat_left_equals_repeat (n-1) f (f init);
    repeat_left_equals_repeat (n-1) f init;
    repeat_left_lemma (n-1) f init
  end
#pop-options

#push-options "--fuel 1"
let rec foldi_repeat_equiv (#a: Type) (init:a) (low: uint_size) (hi: uint_size{low <= hi})
  (f: (i:nat{i < hi}) -> a -> a)
  (g: a -> a)
  (equiv: (i:nat{i < hi}) -> (x:a) -> Lemma (f i x == g x))
    : Lemma
      (requires (True))
      (ensures (foldi low hi f init == Lib.LoopCombinators.repeat (hi - low) g init))
      (decreases (hi - low))
  =
  if low = hi then begin
    Lib.LoopCombinators.eq_repeat0 g init;
    assert(foldi 0 0 f init == init)
  end else begin
    Lib.LoopCombinators.unfold_repeat (hi - low) g init (hi - low - 1);
    assert(Lib.LoopCombinators.repeat (hi - low) g init ==
      g (Lib.LoopCombinators.repeat (hi - low -1) g init));
    (* repeat is a fold_right, whereas foldi is a fold_left. Since g and f don't depend on i
       right or left does not matter but here we should prove that repeat is equivalent to
       repeat_left
    *)
    repeat_left_equals_repeat (hi - low) g init;
    repeat_left_equals_repeat (hi - low - 1) g (g init);
    assert(Lib.LoopCombinators.repeat (hi - low) g init ==
      Lib.LoopCombinators.repeat (hi - low -1) g (g init));
    foldi_repeat_equiv (g init) (low + 1) hi f g equiv;
    equiv low init
  end
#pop-options

let chacha_block_inner_loop1_f = fun (i_41:uint_size{i_41 < 10})  (state_40: New.state) ->
    let state_40 = New.chacha_double_round (state_40) in
    (state_40)

let chacha_block_inner_loop1 (state_40: New.state) =
  foldi (usize 0) (usize 10) chacha_block_inner_loop1_f
  (state_40)

let chacha_block_inner_loop1_equiv (st: New.state)
    : Lemma (chacha_block_inner_loop1 st == Orig.rounds st)
  =
  foldi_repeat_equiv st 0 10
    chacha_block_inner_loop1_f
    Orig.double_round (fun i x -> double_round_equiv x)

let chacha_block_inner_loop2_f (st_39: New.state) =
  fun (i_42: uint_size{i_42 < 16}) (state_40: New.state) ->
    let state_40 =
      array_upd #_ #16 state_40 (i_42) (
        (array_index (state_40) (i_42)) +. (array_index (st_39) (i_42)))
    in
    (state_40)

#push-options "--fuel 2"
let rec map2_equals_foldi_lemma1
  (n: uint_size{n >= 1 /\ n <= 16})
  (i: uint_size{i <= n - 1})
  (x: New.state)
  (y: New.state)
    : Lemma (requires (True)) (ensures (
      foldi i n (chacha_block_inner_loop2_f y) x ==
      chacha_block_inner_loop2_f y (n-1) (foldi i (n-1) (chacha_block_inner_loop2_f y) x)
    ))
    (decreases (n - i))
  =
  if i = n - 1 then () else map2_equals_foldi_lemma1 n (i + 1) (chacha_block_inner_loop2_f y i x) y
#pop-options

#push-options "--fuel 2"
let rec map2_equals_foldi_lemma2
  (n: uint_size{n >= 1 /\ n <= 16})
  (i: uint_size{i <= n - 1})
  (x: New.state)
  (y: New.state)
    : Lemma (requires (True)) (ensures (
      Seq.index (foldi i n (chacha_block_inner_loop2_f y) x) (n-1) ==
      Seq.index (chacha_block_inner_loop2_f y (n-1) x) (n-1)
    ))
    (decreases (n - i))
  =
  if i = n - 1 then () else map2_equals_foldi_lemma2 n (i + 1) (chacha_block_inner_loop2_f y i x) y
#pop-options

#push-options "--fuel 2 --z3rlimit 30"
let rec map2_equals_foldi
  (n: uint_size{n >= 1 /\ n <= 16})
  (x: New.state)
  (y: New.state)
    : Lemma (Seq.sub (Seq.map2 (+.) x y) 0 n ==
      Seq.sub (foldi 0 n (chacha_block_inner_loop2_f y) x) 0 n)
  =
  if n = 1 then begin
    assert(Seq.sub (Seq.map2 (+.) x y) 0 n `Seq.equal`
      Seq.sub (foldi 0 n (chacha_block_inner_loop2_f y) x) 0 n)
  end else begin
    map2_equals_foldi (n-1) x y;
    assert(Seq.sub (Seq.map2 (+.) x y) 0 (n-1) `Seq.equal`

      Seq.sub (foldi 0 (n-1) (chacha_block_inner_loop2_f y) x) 0 (n-1));
    let aux (i: nat{i < n}) : Lemma (Seq.index (Seq.sub (Seq.map2 (+.) x y) 0 n) i ==
      Seq.index (Seq.sub (foldi 0 n (chacha_block_inner_loop2_f y) x) 0 n) i)
      =
      if i < n-1 then begin
        assert(Seq.index (Seq.sub (Seq.map2 (+.) x y) 0 n) i ==
          Seq.index (Seq.sub (Seq.map2 (+.) x y) 0 (n-1)) i);
        map2_equals_foldi_lemma1 n 0 x y;
        assert(Seq.index (foldi 0 (n-1) (chacha_block_inner_loop2_f y) x) i ==
          Seq.index (foldi 0 n (chacha_block_inner_loop2_f y) x) i)
      end else begin
        assert(Seq.index (Seq.sub (foldi 0 n (chacha_block_inner_loop2_f y) x) 0 n) i ==
          Seq.index (foldi 0 n (chacha_block_inner_loop2_f y) x) (n-1));
        map2_equals_foldi_lemma2 n 0 x y
      end
    in
    Classical.forall_intro aux;
    assert(Seq.sub (Seq.map2 (+.) x y) 0 n `Seq.equal`
      Seq.sub (foldi 0 n (chacha_block_inner_loop2_f y) x) 0 n)
  end
#pop-options

let chacha_block_inner_loop2 (state_40: New.state) (st_39: New.state) =
  foldi (usize 0) (usize 16) (chacha_block_inner_loop2_f st_39) (state_40)

let chacha_block_inner_loop2_equiv (st st0: New.state)
    : Lemma (chacha_block_inner_loop2 st st0 == Orig.sum_state st st0)
  =
  map2_equals_foldi 16 st st0

let chacha_block_inner_alt (key: New.key) (ctr: uint32) (iv: New.iv) =
  let st = New.chacha_block_init key ctr iv in
  let st0 = st in
  let st = chacha_block_inner_loop1 st in
  let st = chacha_block_inner_loop2 st st0 in
  st

open FStar.Tactics

let chacha_block_inner_new_comp (key: New.key) (ctr: uint32) (iv: New.iv)
  : Lemma (New.chacha_block_inner key ctr iv == chacha_block_inner_alt key ctr iv)
  =
  assert(New.chacha_block_inner key ctr iv == chacha_block_inner_alt key ctr iv) by begin
    norm [delta_only [
      "Hacspec.Chacha20.chacha_block_inner";
      "Hacspec.Chacha20.Proof.chacha_block_inner_alt";
      "Hacspec.Chacha20.Proof.chacha_block_inner_loop1";
      "Hacspec.Chacha20.Proof.chacha_block_inner_loop1_f";
      "Hacspec.Chacha20.Proof.chacha_block_inner_loop2";
      "Hacspec.Chacha20.Proof.chacha_block_inner_loop2_f";
      "Hacspec.Chacha20.state"
    ]];
    smt ()
  end

#push-options "--fuel 1 --z3rlimit 20"
let chacha_block_inner_equiv (key: New.key) (ctr: uint32) (iv: New.iv)
    : Lemma (chacha_block_inner_alt key ctr iv == chacha_block_inner_equiv_orig key ctr iv)
  =
  let st0' = Orig.chacha20_init key iv (v ctr) in
  let st' = Orig.chacha20_add_counter st0' (v ctr) in

  let st = New.chacha_block_init key ctr iv in
  let st0 = st in
  chacha_block_init_equiv key ctr iv;
  assert(st0 == st0');

  let st' = Orig.rounds st' in

  let st = chacha_block_inner_loop1 st in


  let st' = Orig.sum_state st' st0' in

  let st = chacha_block_inner_loop2 st st0 in

  let st' = Orig.chacha20_add_counter st' (v ctr) in
  assert(st' == chacha_block_inner_equiv_orig key ctr iv);
  assert(st == chacha_block_inner_alt key ctr iv);
  admit()
#pop-options
