require import List Int IntDiv CoreMap AllCore.
require import Array3 Array8 Array16.
require import WArray64.

from Jasmin require import JModel JMemory JArray.

(* Constants *)
op keylen : int = 32.   (* in bytes *)
op blocklen : int = 64. (* in bytes *)
op noncelen : int  = 12. (* in bytes *)

type key = W32.t Array8.t.
type block = W32.t Array16.t.
type nonce = W32.t Array3.t.
type counter = W32.t.

(* using @ as a functional substitute for ;
   internally, blocks are represented as 16 x 4-byte integers *)
type state = W32.t Array16.t.
type idx = int.
op valid_idx i = 0 <= i < 16.
type shuffle = state -> state.

op line (a:idx) (b:idx) (d:idx) (s:int) (m:state) : state =
  let m = m.[a <- (m.[a] + m.[b])] in
  let m = m.[d <- W32.rol (m.[d] +^ m.[a]) s] in m.

op (\oo) ['a 'b 'c] (f: 'a -> 'b) (g: 'b -> 'c) (a:'a) : 'c =
  g (f a).
  
op quarter_round a b c d : shuffle =
  line a b d 16 \oo
  line c d b 12 \oo
  line a b d 8  \oo
  line c d b 7.

op column_round : shuffle =
  quarter_round 0 4 8  12 \oo
  quarter_round 1 5 9  13 \oo
  quarter_round 2 6 10 14 \oo
  quarter_round 3 7 11 15.

op diagonal_round : shuffle =
  quarter_round 0 5 10 15 \oo
  quarter_round 1 6 11 12 \oo
  quarter_round 2 7 8  13 \oo
  quarter_round 3 4 9  14.

op double_round: shuffle =
    column_round \oo diagonal_round. (* 2 rounds *)

op rounds : shuffle =
    iter 10 double_round. (* 20 rounds *)

op chacha20_core (s:state) : state =
    let s' = rounds s in
    Array16.map2 (fun (x y: W32.t) => x + y) s' s.

(* state initialization *)
op c0 = W32.of_int 1634760805 (* 0x61707865 *).
op c1 = W32.of_int 857760878 (* 0x3320646e *).
op c2 = W32.of_int 2036477234 (* 0x79622d32 *).
op c3 = W32.of_int 1797285236 (* 0x6b206574 *).

op setup (k:key) (n:nonce) (c:counter): state =
  Array16.of_list witness ([ c0; c1; c2; c3] ++ 
                           to_list k ++ [c]  ++
                           to_list n).

op chacha20_block (k:key) (n:nonce) (c:counter): block =
  chacha20_core (setup k n c).

type bytes = W8.t list.
type msg = bytes.
type cph = bytes.

op bytes_of_block (b : block) : bytes =
   WArray64.to_list (WArray64.init32 (fun i => b.[i])).

op ctr_round (k:key) (n:nonce) (round_st : cph * msg * counter) =
  let (cph,m,c) = round_st in
  let stream = chacha20_block k n c in
  (cph ++ map2 (W8.(+^)) m (bytes_of_block stream),
   drop 64 m,
   c + W32.of_int 1).

op chacha20_CTR_encrypt_bytes key nonce counter m =
  let len = size m in
  let rounds = (len %/ 64) + b2i (len %% 64 <> 0) in 
  iter rounds (ctr_round key nonce) ([],m,counter).

