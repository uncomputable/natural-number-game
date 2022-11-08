Require Import Unicode.Utf8.
Require Import Game.Mynat.Definition.
Require Import Game.Mynat.Add.

Notation "a ≤ b" := (∃ (c : mynat), b = a + c).

Theorem le_iff_exists_add (a b : mynat) : a ≤ b ↔ ∃ (c : mynat), b = a + c.
Proof.
  split; intro; destruct H; exists x; exact H.
Qed.
