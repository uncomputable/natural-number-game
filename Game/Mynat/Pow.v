Require Import Unicode.Utf8.
Require Import Game.Mynat.Definition.
Require Import Game.Mynat.Mul.

Fixpoint pow (a b : mynat) : mynat :=
match b with
| 0 => 1
| succ b' => pow a b' * a
end.

Notation "a ^ b" := (pow a b).

Lemma pow_zero (m : mynat) : m ^ (0 : mynat) = 1 .
Proof.
  reflexivity.
Qed.

Lemma pow_succ (m n : mynat) : m ^ (succ n) = m ^ n * m .
Proof.
  reflexivity.
Qed.
