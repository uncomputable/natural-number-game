Require Import Unicode.Utf8.
Require Import Game.Mynat.Definition.

Fixpoint add (a b : mynat) : mynat :=
match b with
| 0 => a
| succ b' => succ(add a b')
end.

Notation "a + b" := (add a b).

Theorem add_zero (a : mynat) : a + 0 = a.
Proof.
  reflexivity.
Qed.

Theorem add_succ (a b : mynat) : a + succ b = succ (a + b).
Proof.
  reflexivity.
Qed.
