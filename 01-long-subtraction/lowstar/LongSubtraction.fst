module LongSubtraction

module B = LowStar.Buffer
module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST
module S = FStar.Seq

open FStar.Mul
open FStar.HyperStack.ST

// Our specification-level type. Not meant to be extracted (typically, this
// would be in a separate file that is eliminated wholesale).
inline_for_extraction noextract
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

// The refinement type is convenient, but probably not essential.
let borrow =
  x:UInt8.t { UInt8.v x == 0 \/ UInt8.v x == 1 }

// Subtraction with borrowing, on two u64s. This is a simplified version of the
// standard signature that lives in HACL* (see Lib.IntTypes.Intrinsics.fsti and
// Hacl.IntTypes.Intrinsics.fst). Here, for simplicity, we assume a modern
// toolchain with support for the corresponding CPU intrinsic. The CPrologue
// thing is kind of a hack but avoids having to write glue code by hand (and
// allows asserting we got the signature right).
[@@ CPrologue "#define LongSubtraction_sub_borrow _subborrow_u64"]
assume val sub_borrow:
  b_in:borrow ->
  x: UInt64.t ->
  y: UInt64.t ->
  ret: B.pointer UInt64.t ->
  Stack borrow
    (requires fun h0 -> B.live h0 ret)
    (ensures fun h0 b_out h1 ->
      B.(modifies (loc_buffer ret) h0 h1) /\ (
      let ret = B.deref h1 ret in
      UInt64.v ret - UInt8.v b_out * pow2 64 == UInt64.v x - UInt64.v y - UInt8.v b_in))

// The `Stack` annotation indicates that this function does not generate heap
// allocations.
val sub (dst x y: s) (b0: borrow): Stack borrow
  (requires fun h0 ->
    B.live h0 dst /\ B.live h0 x /\ B.live h0 y /\
    B.(loc_disjoint (loc_buffer x) (loc_buffer y)) /\
    B.(loc_disjoint (loc_buffer dst) (loc_buffer y)) /\
    B.(loc_disjoint (loc_buffer dst) (loc_buffer x) \/ dst == x))
  (ensures fun h0 b1 h1 ->
    B.(modifies (loc_buffer dst) h0 h1) /\
    v h1 dst - pow2 (64 * 4) * UInt8.v b1 == v h0 x - v h0 y - UInt8.v b0)

#set-options "--fuel 0 --ifuel 0 --z3rlimit 200"
let sub dst x y b0 =
  let h0 = ST.get () in

  // Trick: trade reasoning about sequences for reasoning about disjointness.
  let dst0 = B.sub dst 0ul 1ul in
  let dst1 = B.sub dst 1ul 1ul in
  let dst2 = B.sub dst 2ul 1ul in
  let dst3 = B.sub dst 3ul 1ul in
  assert B.(all_disjoint [ loc_buffer dst0; loc_buffer dst1; loc_buffer dst2; loc_buffer dst3 ]);

  // Same deal here.
  let x0 = B.sub x 0ul 1ul in
  let x1 = B.sub x 1ul 1ul in
  let x2 = B.sub x 2ul 1ul in
  let x3 = B.sub x 3ul 1ul in
  assert B.(all_disjoint [ loc_buffer x0; loc_buffer x1; loc_buffer x2; loc_buffer x3 ]);

  // Not strictly necessary for the proof to go through, but helps make sure the
  // solver and I are on the same page when it comes to the disjointness
  // predicates in the presence of potential aliasing between `dst` and `x`
  assert B.(all_disjoint [ loc_buffer dst0; loc_buffer x1; loc_buffer x2; loc_buffer x3 ]);
  assert B.(all_disjoint [ loc_buffer x0; loc_buffer dst1; loc_buffer x2; loc_buffer x3 ]);
  assert B.(all_disjoint [ loc_buffer x0; loc_buffer x1; loc_buffer dst2; loc_buffer x3 ]);
  assert B.(all_disjoint [ loc_buffer x0; loc_buffer x1; loc_buffer x2; loc_buffer dst3 ]);

  let open LowStar.BufferOps in

  let b1 = sub_borrow b0 (!*x0) y.(0ul) dst0 in
  let h1 = ST.get () in
  assert (UInt64.v (B.get h1 dst 0) - UInt8.v b1 * pow2 64 ==
    UInt64.v (B.get h0 x 0) - UInt64.v (B.get h0 y 0) - UInt8.v b0);
  // This would be hella harder to prove without splitting x four-ways. I'm just
  // reluctant to jump into sequence update index etc. Tried proving `B.get h1 x
  // 1 == B.get h0 x 1` earlier and I struggled.
  assert (B.deref h1 x1 == B.deref h0 x1);
  assert (B.deref h1 x2 == B.deref h0 x2);
  assert (B.deref h1 x3 == B.deref h0 x3);

  let b2 = sub_borrow b1 (!*x1) y.(1ul) dst1 in
  let h2 = ST.get () in
  // Note that the assert is slightly more sophisticated since it refers to
  // B.get h0 x 1 -- there are multiple hidden steps of reasoning here, such as:
  // index 1 of x was not modified earlier, and deref x1 is the same as B.get x 1
  assert (UInt64.v (B.get h2 dst 1) - UInt8.v b2 * pow2 64 ==
    UInt64.v (B.get h0 x 1) - UInt64.v (B.get h0 y 1) - UInt8.v b1);
  assert (B.get h2 dst 0 == B.get h1 dst 0);

  let b3 = sub_borrow b2 (!*x2) y.(2ul) dst2 in
  let h3 = ST.get () in
  assert (UInt64.v (B.get h3 dst 2) - UInt8.v b3 * pow2 64 ==
    UInt64.v (B.get h0 x 2) - UInt64.v (B.get h0 y 2) - UInt8.v b2);
  // Framing (as opposed to sequence reasoning).
  assert (B.get h3 dst 0 == B.get h1 dst 0);
  assert (B.get h3 dst 1 == B.get h2 dst 1);

  let b4 = sub_borrow b3 (!*x3) y.(3ul) dst3 in
  let h4 = ST.get () in
  assert (UInt64.v (B.get h4 dst 3) - UInt8.v b4 * pow2 64 ==
    UInt64.v (B.get h0 x 3) - UInt64.v (B.get h0 y 3) - UInt8.v b3);
  assert (B.get h4 dst 0 == B.get h1 dst 0);
  assert (B.get h4 dst 1 == B.get h2 dst 1);
  assert (B.get h4 dst 2 == B.get h3 dst 2);

  // Now we can focus on the math proof /per se/, because we have made sure that
  // the results are as we expect and that the aliasing / dynamic frames worked
  // out properly. I like long calc chains -- low-key, easy to debug, easy to
  // maintain.

  calc (==) {
    v h4 dst - pow2 (64 * 4) * UInt8.v b4;
  (==) { }
    UInt64.v (B.get h1 dst 0) +
    UInt64.v (B.get h2 dst 1) * pow2 64 +
    UInt64.v (B.get h3 dst 2) * pow2 (64 * 2) +
    UInt64.v (B.get h4 dst 3) * pow2 (64 * 3) -
    pow2 (64 * 4) * UInt8.v b4;
  (==) { }
    UInt8.v b1 * pow2 64 +
    UInt64.v (B.get h0 x 0) - UInt64.v (B.get h0 y 0) - UInt8.v b0 +
    (UInt8.v b2 * pow2 64 +
    UInt64.v (B.get h0 x 1) - UInt64.v (B.get h0 y 1) - UInt8.v b1) * pow2 64 +
    (UInt8.v b3 * pow2 64 +
    UInt64.v (B.get h0 x 2) - UInt64.v (B.get h0 y 2) - UInt8.v b2) * pow2 (64 * 2) +
    (UInt8.v b4 * pow2 64 +
    UInt64.v (B.get h0 x 3) - UInt64.v (B.get h0 y 3) - UInt8.v b3) * pow2 (64 * 3) -
    pow2 (64 * 4) * UInt8.v b4;
  (==) { _ by (FStar.Tactics.Canon.canon ()) }
    UInt8.v b1 * pow2 64 +
    UInt64.v (B.get h0 x 0) - UInt64.v (B.get h0 y 0) +
    UInt8.v b2 * pow2 64 * pow2 64 +
      UInt64.v (B.get h0 x 1) * pow2 64 - UInt64.v (B.get h0 y 1) * pow2 64 - UInt8.v b1 * pow2 64 +
    UInt8.v b3 * pow2 64 * pow2 (64 * 2) +
    UInt64.v (B.get h0 x 2) * pow2 (64 * 2) - UInt64.v (B.get h0 y 2) * pow2 (64 * 2) - UInt8.v b2 * pow2 (64 * 2) +
    UInt8.v b4 * pow2 64 * pow2 (64 * 3) +
    UInt64.v (B.get h0 x 3) * pow2 (64 * 3) - UInt64.v (B.get h0 y 3) * pow2 (64 * 3) - UInt8.v b3 * pow2 (64 * 3) -
    UInt8.v b4 * pow2 (64 * 4) // commute this term too
    - UInt8.v b0;
  (==) {
    assert_norm (pow2 64 * pow2 64 == pow2 (64 * 2));
    assert_norm (pow2 64 * pow2 (64 * 2) == pow2 (64 * 3));
    assert_norm (pow2 64 * pow2 (64 * 3) == pow2 (64 * 4))
  }
    UInt8.v b1 * pow2 64 +
    UInt64.v (B.get h0 x 0) - UInt64.v (B.get h0 y 0) +
    UInt8.v b2 * pow2 (64 * 2) +
      UInt64.v (B.get h0 x 1) * pow2 64 - UInt64.v (B.get h0 y 1) * pow2 64 - UInt8.v b1 * pow2 64 +
    UInt8.v b3 * pow2 (64 * 3) +
    UInt64.v (B.get h0 x 2) * pow2 (64 * 2) - UInt64.v (B.get h0 y 2) * pow2 (64 * 2) - UInt8.v b2 * pow2 (64 * 2) +
    UInt8.v b4 * pow2 (64 * 4) +
    UInt64.v (B.get h0 x 3) * pow2 (64 * 3) - UInt64.v (B.get h0 y 3) * pow2 (64 * 3) - UInt8.v b3 * pow2 (64 * 3) -
    pow2 (64 * 4) * UInt8.v b4
    - UInt8.v b0;
  };

  // Note: a much shorter, but imho less readable proof, would be to just have
  // the three `assert_norm`s, followed by `assert (... the post-condition ...)
  // by canon ()`.

  b4
