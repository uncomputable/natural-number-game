Require Import Unicode.Utf8.
Require Import Game.Mynat.Definition.
Require Import Game.Mynat.Add.
Require Import Game.World.Addition.
Require Import Game.World.Proposition.
Require Import Game.World.AdvancedProposition.
Require Import Setoid.

(* Level 1 *)

Theorem succ_inj' {a b : mynat} (hs : succ(a) = succ(b)) :  a = b.
Proof.
  apply succ_inj.
  exact hs.
Qed.

(* Level 2 *)

Theorem succ_succ_inj {a b : mynat} (h : succ(succ(a)) = succ(succ(b))): a = b.
Proof.
  apply succ_inj.
  apply succ_inj.
  exact h.
Qed.

(* Level 3 *)

Theorem succ_eq_succ_of_eq (a b : mynat) : a = b → succ(a) = succ(b).
Proof.
  intro f.
  rewrite f.
  reflexivity.
Qed.

(* Level 4 *)

Theorem succ_eq_succ_iff (a b : mynat) : succ a = succ b ↔ a = b.
Proof.
  split.
  exact succ_inj.
  intro f.
  rewrite f.
  reflexivity.
Qed.

(* Level 5 *)

Theorem add_right_cancel (a t b : mynat) : a + t = b + t → a = b.
Proof.
  intro f.
  induction t.
  repeat rewrite add_zero in f.
  exact f.
  rewrite IHt.
  reflexivity.
  apply succ_inj.
  exact f.
Qed.

(* Level 6 *)
(* `symmetry`: Switch LHS and RHS of equality *)
(* Goal of the form `A = B` *)

Theorem add_left_cancel (t a b : mynat) : t + a = t + b → a = b.
Proof.
  intro f.
  rewrite add_comm in f.
  symmetry in f.
  rewrite add_comm in f.
  symmetry in f.
  apply add_right_cancel in f.
  exact f.
Qed.

(* Level 7 *)

Theorem add_right_cancel_iff (t a b : mynat) :  a + t = b + t ↔ a = b.
Proof.
  split.
  apply add_right_cancel.
  intro f.
  induction t.
  repeat rewrite add_zero.
  exact f.
  repeat rewrite add_succ.
  rewrite IHt.
  reflexivity.
Qed.

(* Level 8 *)

Theorem eq_zero_of_add_right_eq_self {a b : mynat} : a + b = a → b = 0.
Proof.
  intro f.
  induction a.
  rewrite zero_add in f.
  exact f.
  rewrite add_comm in f.
  rewrite add_succ in f.
  rewrite add_comm in f.
  rewrite succ_eq_succ_iff in f.
  exact (IHa f).
Qed.

(* Level 9 *)
(* `A ≠ B` is a notational shorthand for `A = B → False` *)

Theorem succ_ne_zero (a : mynat) : succ a ≠ 0.
Proof.
  intro f.
  apply (zero_ne_succ a).
  symmetry.
  exact f.
Qed.

(* Level 10 *)
(* `destruct a`: Case case distinction on inductive structure that `a` has  *)

Lemma add_left_eq_zero {a b : mynat} (H : a + b = 0) : b = 0.
Proof.
  destruct b.
  reflexivity.
  exfalso.
  apply (succ_ne_zero (a + b)).
  rewrite add_succ in H.
  exact H.
Qed.

(* Level 11 *)

Lemma add_right_eq_zero {a b : mynat} : a + b = 0 → a = 0.
Proof.
  intro f.
  rewrite add_comm in f.
  apply (@add_left_eq_zero b a) in f.
  exact f.
Qed.

(* Level 12 *)

Theorem add_one_eq_succ (d : mynat) : d + 1 = succ d.
Proof.
  rewrite succ_eq_add_one.
  reflexivity.
Qed.

(* Level 13 *)

Lemma ne_succ_self (n : mynat) : n ≠ succ n.
Proof.
  induction n.
  apply zero_ne_succ.
  intro f.
  rewrite succ_eq_succ_iff in f.
  apply IHn.
  exact f.
Qed.
