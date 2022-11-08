Require Import Unicode.Utf8.
Require Import Game.Mynat.Definition.
Require Import Game.Mynat.Add.
Require Import Game.Mynat.Mul.

(* Level 1 *)
(* `reflexivity`: Proof syntactic equality *)
(* Goal of the form `X = X` *)

Lemma example_1_tuto (x y z : mynat) : x * y + z = x * y + z.
Proof.
  reflexivity.
Qed.

(* Level 2 *)
(* `rewrite f`: Substitute equivalent parts *)
(* Hypothesis `f` of the form `A = B` *)
(* Goal of the form `... A ...` *)

Lemma example_2_tuto (x y : mynat) (h : y = x + 1) : 2 * y = 2 * (x + 1).
Proof.
  rewrite h.
  reflexivity.
Qed.

(* Level 3 *)

Lemma example_3_tuto (a b : mynat) (h : succ a = b) : succ(succ(a)) = succ(b).
Proof.
  rewrite h.
  reflexivity.
Qed.

(* Level 4 *)

Lemma add_succ_zero (a : mynat) : a + succ(0) = succ(a).
Proof.
  rewrite add_succ.
  rewrite add_zero.
  reflexivity.
Qed.
