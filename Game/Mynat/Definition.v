Require Import Unicode.Utf8.

Inductive mynat : Set :=
| zero : mynat
| succ : mynat → mynat.

Definition one : mynat := succ zero.
Definition two : mynat := succ one.

Notation "0" := zero.
Notation "1" := one.
Notation "2" := two.

Theorem one_eq_succ_zero : one = succ zero.
Proof.
  reflexivity.
Qed.

(* `discriminate`: Prove structural inequality *)
(* Goal of the form `C1 = C2` where C1 and C2 are different constructors of the same injective type *)

Lemma zero_ne_succ (a : mynat) : (0 : mynat) ≠ succ a.
Proof.
  discriminate.
Qed.

(* `injection`: Remove the same constructor from both sides of an equality *)
(* Goal of the form `C a = C b` *)

Lemma succ_inj {a b : mynat} (h : succ a = succ b) : a = b.
Proof.
  injection h.
  intro f.
  exact f.
Qed.
