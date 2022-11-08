Require Import Unicode.Utf8.
Require Import Game.Mynat.Definition.
Require Import Game.Mynat.Add.

(* Level 1 *)
(* `induction a`: induction on term `a` *)

Lemma zero_add (a : mynat) : 0 + a = a.
Proof.
  induction a.
  rewrite add_zero.
  reflexivity.
  rewrite add_succ.
  rewrite IHa.
  reflexivity.
Qed.

(* Level 2 *)

Lemma add_assoc (a b c : mynat) : (a + b) + c = a + (b + c).
Proof.
  induction c.
  rewrite add_zero.
  rewrite add_zero.
  reflexivity.
  rewrite add_succ.
  rewrite IHc.
  rewrite add_succ.
  rewrite add_succ.
  reflexivity.
Qed.

(* Level 3 *)

Lemma succ_add (a b : mynat) : succ a + b = succ (a + b).
Proof.
  induction b.
  rewrite add_zero.
  rewrite add_zero.
  reflexivity.
  rewrite add_succ.
  rewrite IHb.
  rewrite add_succ.
  reflexivity.
Qed.

(* Level 4 *)

Lemma add_comm (a b : mynat) : a + b = b + a.
Proof.
  induction b.
  rewrite add_zero.
  rewrite zero_add.
  reflexivity.
  rewrite add_succ.
  rewrite IHb.
  rewrite succ_add.
  reflexivity.
Qed.

(* Level 5 *)

Theorem succ_eq_add_one (n : mynat) : succ n = n + 1.
Proof.
  rewrite one_eq_succ_zero.
  rewrite add_succ.
  rewrite add_zero.
  reflexivity.
Qed.

(* Level 6 *)
(* `rewrite (f x)`: Substitute `f` with bindings `x` *)

Lemma add_right_comm (a b c : mynat) : a + b + c = a + c + b.
Proof.
  rewrite add_assoc.
  rewrite (add_comm b c).
  rewrite add_assoc.
  reflexivity.
Qed.
