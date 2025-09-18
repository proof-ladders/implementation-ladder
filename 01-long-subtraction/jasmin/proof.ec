require import AllCore IntDiv List WF.
from Jasmin require import JModel_x86.
require import LongSubtraction.

(* Semantics of a borrow, encoded as a 8-bit machine word. *)
op borrow_denote (b: W8.t) : bool = lsb b.

(* Semantics of an array of n limbs, with a special case of four limbs, the
data-type for “long integers”. *)
op get_limb (w: BArray32.t) (i: int) = W64.to_uint (BArray32.get64 w i) * 2 ^ (64 * i).
op limbs_denote (w: BArray32.t) (n: int) =
  foldl ( + ) 0 (map (get_limb w) (iota_ 0 n)).

op integer_denote (w: BArray32.t) : int = limbs_denote w 4.

(* Sanity check: equivalent specification of a long integer. *)
lemma integer_denoteE w :
  integer_denote w = get_limb w 0 + get_limb w 1 + get_limb w 2 + get_limb w 3.
proof. by rewrite /integer_denote /limbs_denote -iotaredE. qed.

(* Specification for the long integer subtraction with borrow *)
op subtract_limbs (x y: BArray32.t) (b: bool) (n: int) : int * bool =
  let p = limbs_denote x n in
  let q = limbs_denote y n in
  let r = p - q - b2i b in
  let c = r < 0 in
  (r + b2i c * 2 ^ (64 * n), c).

(* Functional correctness of the [of_borrow] procedure. *)
hoare of_borrow_correct borrow :
  M.of_borrow :
  borrow_denote b = borrow ==> res = borrow.
proof. by proc; auto. qed.

(* Functional correctness of the [to_borrow] procedure. *)
hoare to_borrow_correct borrow :
  M.to_borrow :
  b = borrow ==> borrow_denote res = borrow.
proof.
  proc; auto => &m />.
  case: (b{m}); last done.
  by rewrite /SETcc /= /borrow_denote/lsb  nth_one.
qed.

(* Lemmas about arrays of limbs *)
lemma limbs_denote0 w : limbs_denote w 0 = 0.
proof. by rewrite /limbs_denote -iotaredE. qed.

lemma limbs_denoteS w i :
  0 <= i =>
  limbs_denote w (i + 1) = limbs_denote w i + get_limb w i.
proof. by move => ?; rewrite {1}/limbs_denote iotaSr // map_rcons foldl_rcons. qed.

lemma limbs_denote_range w i :
  0 <= i =>
  0 <= limbs_denote w i < 2 ^ (64 * i).
proof.
  elim/natind: i.
  - move => i ??.
    have ->> : i = 0 by smt().
    by rewrite limbs_denote0.
  move => i i_ge0 /(_ i_ge0) ih _.
  rewrite limbs_denoteS // mulrDr Ring.IntID.exprD_nneg 1,2:/#.
  rewrite /get_limb.
  have := W64.to_uint_cmp (BArray32.get64 w i).
  smt().
qed.

lemma get_limb_set_eq w n x :
  0 <= n < 4 =>
  get_limb (BArray32.set64 w n x) n = W64.to_uint x * 2 ^ (64 * n).
proof. move => ?; rewrite /get_limb BArray32.get_set64E_eq /#. qed.

lemma limbs_denote_set_out w n x i :
  0 <= i <= n <= 4 =>
  limbs_denote (BArray32.set64 w n x) i = limbs_denote w i.
proof.
  move => i_n_range.
  rewrite /limbs_denote; congr.
  apply: eq_in_map => j /mem_iota [] j_lo j_hi.
  rewrite /get_limb; congr; congr.
  apply: BArray32.get_set64E_neq.
  smt().
qed.

(* Main correctness statement about the long_subtraction function *)
hoare long_subtraction_correct _x _y _b :
  M.long_subtraction :
  x = _x /\ y = _y /\ borrow_denote borrow = _b ==>
  subtract_limbs _x _y _b 4 = (integer_denote res.`1, borrow_denote res.`2).
proof.
  proc.
  seq 1: (x = _x /\ y = _y /\ b = _b).
  + by call (of_borrow_correct _b); skip.
  seq 2: (x = _x /\ y = _y /\ subtract_limbs _x _y _b 4 = (limbs_denote out 4, b)); last first.
  + call (to_borrow_correct (integer_denote _x < integer_denote _y + b2i _b)); auto.
    move => &m />.
    rewrite -!/(integer_denote _) /result_denote /borrow_denote /subtract_limbs /= => <- /#.
  while (0 <= i <= 4 /\ x = _x /\ y = _y /\ subtract_limbs _x _y _b i = (limbs_denote out i, b)); last first.
  + auto => &m />; rewrite /subtract_limbs /= !limbs_denote0; split; first smt().
    move => i ????; suff -> : i = 4; smt().
  auto => &m /> i_lo _ ih i_hi; split; 1: smt().
  rewrite limbs_denoteS // get_limb_set_eq // limbs_denote_set_out 1:/#.
  rewrite /subtract_limbs !limbs_denoteS // /=.
  rewrite /get_limb /subc /= -ih; clear ih.
  move: (limbs_denote x{m} i{m}) (limbs_denote_range x{m} i{m} i_lo) => x x_range.
  move: (limbs_denote y{m} i{m}) (limbs_denote_range y{m} i{m} i_lo) => y y_range.
  rewrite andbC -andaE; split; first smt().
  move => ->.
  rewrite /borrow_sub mulrDr Ring.IntID.exprD_nneg 1, 2:/# to_uintBb /#.
qed.

(* The correctness of the in-place version follows by functional equivalence *)
require import LongSubEquiv.
hoare long_subtraction_in_place_correct _x _y _b :
  M.long_subtraction_in_place :
  x = _x /\ y = _y /\ borrow_denote borrow = _b ==>
  subtract_limbs _x _y _b 4 = (integer_denote res.`1, borrow_denote res.`2).
proof. by conseq long_subtraction_equiv (long_subtraction_correct _x _y _b); first smt(). qed.
