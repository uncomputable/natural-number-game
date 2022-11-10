Require Import Unicode.Utf8.
Require Import Game.Mynat.Definition.
Require Import Game.Mynat.Add.
Require Import Game.Mynat.Mul.
Require Import Game.Mynat.Le.
Require Import Game.World.Addition.
Require Import Game.World.Multiplication.
Require Import Game.World.Proposition.
Require Import Game.World.AdvancedProposition.
Require Import Game.World.AdvancedAddition.
Require Import Game.World.AdvancedMultiplication.

(* Level 1 *)
(* `exists x`: Replace existentially quantified variable with `x` *)
(* Goal of the form `∃ y, ... ` *)

Lemma one_add_le_self (x : mynat) : x ≤ 1 + x.
Proof.
  rewrite le_iff_exists_add.
  exists 1.
  exact (add_comm 1 x).
Qed.

(* Level 2 *)

Lemma le_refl (x : mynat) : x ≤ x.
Proof.
  exists 0.
  reflexivity.
Qed.

(* Level 3 *)
(* `destruct f as [x g]`: Replace existentially quantified variable in hypothesis `f` with `x` *)
(* Hypothesis of the form `f: ∃ y, ...` *)

Theorem le_succ (a b : mynat) : a ≤ b → a ≤ (succ b).
Proof.
  intro f.
  destruct f as [c g].
  exists (succ c).
  rewrite add_succ.
  rewrite succ_eq_succ_iff.
  exact g.
Qed.

(* Level 4 *)

Lemma zero_le (a : mynat) : 0 ≤ a.
Proof.
  exists a.
  rewrite zero_add.
  reflexivity.
Qed.

(* Level 5 *)

Theorem le_trans (a b c : mynat) (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c.
Proof.
  destruct hab as [d hab].
  destruct hbc as [e hbc].
  rewrite hab in hbc.
  exists (d + e).
  rewrite <- add_assoc.
  exact hbc.
Qed.

(* Level 6 *)

Theorem le_antisymm (a b : mynat) (hab : a ≤ b) (hba : b ≤ a) : a = b.
Proof.
  destruct hab as [c hab].
  destruct hba as [d hba].
  rewrite hab in hba.
  rewrite add_assoc in hba.
  symmetry in hba.
  apply eq_zero_of_add_right_eq_self in hba.
  rewrite add_comm in hba.
  apply add_left_eq_zero in hba.
  rewrite hba in hab.
  symmetry in hab.
  exact hab.
Qed.

(* Level 7 *)

Lemma le_zero (a : mynat) (h : a ≤ 0) : a = 0.
Proof.
  destruct h as [c h].
  symmetry in h.
  exact (add_right_eq_zero h).
Qed.

(* Level 8 *)

Lemma succ_le_succ (a b : mynat) (h : a ≤ b) : succ a ≤ succ b.
Proof.
  destruct h as [c h].
  exists c.
  rewrite succ_add.
  rewrite succ_eq_succ_iff.
  exact h.
Qed.

(* Level 9 *)

Theorem le_total (a b : mynat) : a ≤ b ∨ b ≤ a.
Proof.
  induction a.
  left.
  exact (zero_le b).
  destruct IHa as [f|g].
  destruct f as [c f].
  destruct c.
  right.
  exists 1.
  rewrite f.
  reflexivity.
  left.
  rewrite f.
  exists c.
  rewrite add_succ.
  rewrite succ_add.
  reflexivity.
  right.
  apply le_succ.
  exact g.
Qed.

(* Level 10 *)

Lemma le_succ_self (a : mynat) : a ≤ succ a.
Proof.
  exact (le_succ a a (le_refl a)).
Qed.

(* Level 11 *)

Theorem add_le_add_right {a b : mynat} : a ≤ b → ∀ t, (a + t) ≤ (b + t).
Proof.
  intro f.
  intro t.
  destruct f as [c f].
  exists c.
  rewrite add_right_comm.
  rewrite add_right_cancel_iff.
  exact f.
Qed.

(* Level 12 *)

Theorem le_of_succ_le_succ (a b : mynat) : succ a ≤ succ b → a ≤ b.
Proof.
  intro f.
  destruct f as [c f].
  exists c.
  rewrite succ_add in f.
  rewrite succ_eq_succ_iff in f.
  exact f.
Qed.

(* Level 13 *)

Theorem not_succ_le_self (a : mynat) : ¬ (succ a ≤ a).
Proof.
  intro f.
  pose (g := le_antisymm a (succ a) (le_succ_self a)).
  apply g in f.
  apply (ne_succ_self a).
  exact f.
Qed.

(* Level 14 *)

Theorem add_le_add_left {a b : mynat} (h : a ≤ b) (t : mynat) :
  t + a ≤ t + b.
Proof.
  rewrite add_comm.
  rewrite (add_comm t b).
  apply add_le_add_right.
  exact h.
Qed.

(* Level 15 *)

Lemma lt_aux_one (a b : mynat) : a ≤ b ∧ ¬ (b ≤ a) → succ a ≤ b.
Proof.
  intro f.
  destruct f as [f g].
  destruct f as [c f].
  destruct c.
  exfalso.
  apply g.
  exists 0.
  rewrite f.
  reflexivity.
  exists c.
  rewrite succ_add.
  rewrite add_succ in f.
  exact f.
Qed.

(* Level 16 *)

Lemma lt_aux_two (a b : mynat) : succ a ≤ b → a ≤ b ∧ ¬ (b ≤ a).
Proof.
  intro f.
  split.
  destruct f as [c f].
  exists (1 + c).
  rewrite <- add_assoc.
  exact f.
  intro g.
  pose (h := le_trans (succ a) b a f g).
  exact (not_succ_le_self a h).
Qed.

(* Level 17 *)

Lemma lt_iff_succ_le (a b : mynat) : a < b ↔ succ a ≤ b.
Proof.
  split.
  exact (lt_aux_one a b).
  exact (lt_aux_two a b).
Qed.
