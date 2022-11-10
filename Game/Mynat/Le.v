Require Import Unicode.Utf8.
Require Import Game.Mynat.Definition.
Require Import Game.Mynat.Add.

Definition le (a b : mynat) := ∃ (c : mynat), b = a + c.
Notation "a ≤ b" := (le a b).

Definition lt (a b : mynat) := a ≤ b ∧ ¬ (b ≤ a).
Notation "a < b" := (lt a b).

Theorem le_iff_exists_add (a b : mynat) : a ≤ b ↔ ∃ (c : mynat), b = a + c.
Proof.
  split; intro; destruct H; exists x; exact H.
Qed.
