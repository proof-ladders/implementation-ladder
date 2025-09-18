require import AllCore.
require import LongSubtraction.

(* Relation between arrays: contents are the same on a subset of indices *)
op arrays_eq_on (p: int -> bool) (x y: BArray32.t) : bool =
  forall (i: int), 0 <= i < 4 => p i => BArray32.get64 x i = BArray32.get64 y i.

lemma arrays_eq_on_full x y :
  arrays_eq_on (fun _ => true) x y <=> x = y.
proof.
  split; last done.
  by move => h; apply: BArray32.ext_eq64 => i i_range; apply: h; first smt().
qed.

lemma arrays_eq_on_empty p x y :
  (forall i, p i => i < 0 || 4 <= i) =>
  arrays_eq_on p x y.
proof. smt(). qed.

lemma arrays_eq_on_w p q x y :
  (forall i, 0 <= i < 4 => q i => p i) =>
  arrays_eq_on p x y =>
  arrays_eq_on q x y.
proof. by move => w xy 3?; apply: xy => //; apply: w. qed.

lemma arrays_eq_on_set_out p x y i w :
  !p i =>
  arrays_eq_on p x y =>
  arrays_eq_on p (BArray32.set64 x i w) y.
proof. by move => 5?; rewrite BArray32.get_set64E_neq /#. qed.

lemma arrays_eq_on_set p q x y i w :
  0 <= i < 4 =>
  (forall j, 0 <= j < 4 => (q j <=> i = j || p j)) =>
  arrays_eq_on p x y =>
  arrays_eq_on q (BArray32.set64 x i w) (BArray32.set64 y i w).
proof. move => 6?; rewrite !BArray32.get_set64E /#. qed.

(* Both implementations are equivalent *)
equiv long_subtraction_equiv : M.long_subtraction_in_place ~ M.long_subtraction : ={x, y, borrow} ==> ={res}.
proof.
  proc.
  sim.
  while (0 <= i{1} <= 4 /\ ={i, y, b} /\ arrays_eq_on (fun j => j < i{1}) x{1} out{2} /\ arrays_eq_on (fun j => i{1} <= j) x{1} x{2}); last first.
  + conseq (: _ ==> i{1} = 0 /\ ={i, x, y, b}); last by wp; sim.
    move => &1 &2 />; split; first by apply: arrays_eq_on_empty => />.
    move => out i x ? _ ??.
    have -> : i = 4 by smt().
    by move => h _; apply: arrays_eq_on_full; apply: arrays_eq_on_w h.
  auto => &1 &2 /> i_lo _ hout hx i_hi; split; first smt().
  split; first by rewrite hx.
  split; first by rewrite hx //; apply: arrays_eq_on_set hout; smt().
  apply: arrays_eq_on_set_out; first smt().
  apply: arrays_eq_on_w hx; smt().
qed.

