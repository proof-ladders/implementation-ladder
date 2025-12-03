import Aeneas
import LongSubtraction.Funs
open Aeneas.Std Result Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false

/- This file proves properties about the functions from ../rust/src/main.rs,
   after running them through Aeneas to translate those definitions into Lean.
   The definitions are in LongSubtraction.Funs. -/

/- Because Aeneas produces a functional translation, all of BigInt, &BigInt and
   &mut BigInt translate in Lean to an Array (really, a List) of 4 U64s. We
   define the abbreviation below for convenience. -/
def BigInt := Array U64 4#usize

/- This is a proof by refinement: the view of a BigInt is simply a Nat. -/
@[simp, coe]
def toNat (x: BigInt) :=
  let x0: Nat := x.val[0]
  let x1: Nat := x.val[1]
  let x2: Nat := x.val[2]
  let x3: Nat := x.val[3]
  x0 + x1 * 2^64 + x2 * 2^(64*2) + x3 * 2^(64*3)

/- Proof of refinement for the sub-borrow helper. We put the theorem in the form
   expected by progress (i.e., ∃ ..., ...), and tag it with the right attribute
   so that further calls to `progress` can use this theorem to step through the
   translated program.

   The intuitive form for the post-condition would be something like:
     r.val - b1 * (2 ^ 64) = src1.val - src2.val - b0.val
   but remember that subtraction in Lean is total, meaning that 0 - 1 = 0... so
   this specification does not mean what we want. Furthermore, goals and
   hypotheses that contain - do not lend themselves to automation and/or
   simplification because - is neither associative nor commutative.

   Instead, we use an alternative form with only addition, which then makes life
   easier for callers and potentially allows reasoning about wraparound. -/
@[progress]
theorem sub_borrow_spec (b0: U8) (src1 src2 dst: U64) (h: b0.val = 0 ∨ b0.val = 1):
  ∃ b1 r, sub_borrow b0 src1 src2 dst = ok (b1, r) ∧
  r.val + src2.val + b0.val = src1.val + b1 * (2 ^ 64) ∧
  (b1.val = 0 ∨ b1.val = 1)
:= by
  unfold sub_borrow
  progress*
  <;> simp_all
  <;> simp_scalar
  /- to conclude, we need to show that the code path where b1.val = 2
     (underflows twice) is unreachable -/
  scalar_tac

theorem sub_spec
  (b0 : U8) (src1 : Array U64 4#usize) (src2 : Array U64 4#usize)
  (dst : Array U64 4#usize) (h: b0.val = 0 ∨ b0.val = 1):
  ∃ b1 r, sub b0 src1 src2 dst = ok (b1, r) ∧
  -- Same remark: the post-condition carefully avoids using subtractions
  toNat src1 + 2 ^ (64 * 4) * b1.val = toNat src2 + b0.val + toNat r
:= by
  unfold sub
  progress*
  simp_all
  scalar_tac
