module LongSubtraction

module B = LowStar.Buffer
module HS = FStar.HyperStack
module S = FStar.Seq

open FStar.Mul
open FStar.HyperStack.ST

// Our specification-level type
let t = nat

// Low-level type ("stateful"). We pick words to be unsigned 64-bit integers.
let s = b:B.buffer UInt64.t { B.length b == 4 }

// The value function, going from a low-level representation in a given memory
// state to the specification-level type. There is a choice here, and we pick
// big-endian.
let v (h: HS.mem) (x: s) =
  let words = B.as_seq h x in
  UInt64.v (S.index words 0) +
  UInt64.v (S.index words 1) * pow2 64 +
  UInt64.v (S.index words 2) * pow2 (64 * 2) +
  UInt64.v (S.index words 3) * pow2 (64 * 3)

let borrow =
  x:UInt64.t { UInt64.v x == 0 \/ UInt64.v x == 1 }

val sub (dst x y: s) (b0: borrow): Stack borrow
  (requires fun h0 ->
    B.live h0 dst /\ B.live h0 x /\ B.live h0 y /\
    B.(loc_disjoint (loc_buffer x) (loc_buffer y)) /\
    B.(loc_disjoint (loc_buffer dst) (loc_buffer y)) /\
    B.(loc_disjoint (loc_buffer dst) (loc_buffer x) \/ dst == x))
  (ensures fun h0 b1 h1 ->
    B.(modifies (loc_buffer dst) h0 h1) /\
    v h1 dst - pow2 (64 * 4) * UInt64.v b1 == v h0 x - v h0 y - UInt64.v b0)
