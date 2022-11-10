Require Import Unicode.Utf8.
Require Import Game.Mynat.Definition.
Require Import Game.Mynat.Mul.

Fixpoint pow (a n : mynat) : mynat :=
match n with
| 0 => 1
| succ n' => pow a n' * a
end.

Notation "a ^ n" := (pow a n).

Lemma pow_zero (a : mynat) : a ^ (0 : mynat) = 1 .
Proof.
  reflexivity.
Qed.

Lemma pow_succ (a n : mynat) : a ^ (succ n) = a ^ n * a .
Proof.
  reflexivity.
Qed.
