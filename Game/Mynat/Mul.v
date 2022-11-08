Require Import Unicode.Utf8.
Require Import Game.Mynat.Definition.
Require Import Game.Mynat.Add.

Fixpoint mul (a b : mynat) : mynat :=
match b with
| 0 => 0
| succ b' => mul a b' + a
end.

Notation "a * b" := (mul a b).

Lemma mul_zero (m : mynat) : m * 0 = 0 .
Proof.
  reflexivity.
Qed.

Lemma mul_succ (m n : mynat) : m * (succ n) = m * n + m .
Proof.
  reflexivity.
Qed.
