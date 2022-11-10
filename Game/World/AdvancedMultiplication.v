Require Import Unicode.Utf8.
Require Import Game.Mynat.Definition.
Require Import Game.Mynat.Add.
Require Import Game.Mynat.Mul.
Require Import Game.World.Addition.
Require Import Game.World.Multiplication.
Require Import Game.World.Proposition.
Require Import Game.World.AdvancedProposition.
Require Import Game.World.AdvancedAddition.

(* Level 1 *)

Theorem mul_pos (a b : mynat) : a ≠ 0 → b ≠ 0 → a * b ≠ 0.
Proof.
  intro f.
  intro g.
  intro h.
  destruct b.
  apply g.
  reflexivity.
  apply f.
  rewrite mul_succ in h.
  exact (add_left_eq_zero h).
Qed.

(* Level 2 *)

Theorem eq_zero_or_eq_zero_of_mul_eq_zero (a b : mynat) (h : a * b = 0) :
  a = 0 ∨ b = 0.
Proof.
  destruct b.
  right.
  reflexivity.
  rewrite mul_succ in h.
  left.
  exact (add_left_eq_zero h).
Qed.

(* Level 3 *)

Theorem mul_eq_zero_iff (a b : mynat): a * b = 0 ↔ a = 0 ∨ b = 0.
Proof.
  split.
  exact (eq_zero_or_eq_zero_of_mul_eq_zero a b).
  intro f.
  destruct f as [f|g].
  rewrite f.
  exact (zero_mul b).
  rewrite g.
  exact (mul_zero a).
Qed.

(* Level 4 *)
(* `revert f`: Replace hypothesis `f: a` with ∀a in goal *)
(* Hypothesis of the form `f: a` *)

Theorem mul_left_cancel (a b c : mynat) (ha : a ≠ 0) : a * b = a * c → b = c.
Proof.
  revert b.
  induction c.
  rewrite mul_zero.
  intro b.
  rewrite mul_eq_zero_iff.
  intro f.
  destruct f as [f|g].
  exfalso.
  apply ha.
  exact f.
  exact g.
  intro b.
  intro f.
  destruct b.
  rewrite mul_zero in f.
  symmetry in f.
  rewrite mul_eq_zero_iff in f.
  destruct f as [f|g].
  exfalso.
  apply ha.
  exact f.
  symmetry.
  exact g.
  repeat rewrite mul_succ in f.
  rewrite add_right_cancel_iff in f.
  apply IHc in f.
  rewrite succ_eq_succ_iff.
  exact f.
Qed.
