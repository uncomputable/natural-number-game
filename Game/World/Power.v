Require Import Unicode.Utf8.
Require Import Game.Mynat.Definition.
Require Import Game.Mynat.Add.
Require Import Game.Mynat.Mul.
Require Import Game.Mynat.Pow.
Require Import Game.World.Addition.
Require Import Game.World.Multiplication.

(* Level 1 *)

Lemma zero_pow_zero : (0 : mynat) ^ (0 : mynat) = 1.
Proof.
  reflexivity.
Qed.

(* Level 2 *)

Lemma zero_pow_succ (a : mynat) : (0 : mynat) ^ (succ a) = 0.
Proof.
  rewrite pow_succ.
  reflexivity.
Qed.

(* Level 3 *)

Lemma pow_one (a : mynat) : a ^ (1 : mynat) = a.
Proof.
  rewrite one_eq_succ_zero.
  rewrite pow_succ.
  rewrite pow_zero.
  rewrite one_mul.
  reflexivity.
Qed.

(* Level 4 *)

Lemma one_pow (n : mynat) : (1 : mynat) ^ n = 1.
Proof.
  induction n.
  reflexivity.
  rewrite pow_succ.
  rewrite IHn.
  rewrite mul_one.
  reflexivity.
Qed.

(* Level 5 *)

Lemma pow_add (a n m : mynat) : a ^ (n + m) = a ^ n * a ^ m.
Proof.
  induction m.
  rewrite add_zero.
  rewrite pow_zero.
  rewrite mul_one.
  reflexivity.
  rewrite add_succ.
  repeat rewrite pow_succ.
  rewrite IHm.
  rewrite mul_assoc.
  reflexivity.
Qed.

(* Level 6 *)

Lemma mul_pow (a b n : mynat) : (a * b) ^ n = a ^ n * b ^ n.
Proof.
  induction n.
  repeat rewrite pow_zero.
  rewrite mul_one.
  reflexivity.
  repeat rewrite pow_succ.
  rewrite IHn.
  rewrite mul_assoc.
  rewrite (mul_left_comm (b ^ n) _ _).
  rewrite mul_assoc.
  reflexivity.
Qed.

(* Level 7 *)

Lemma pow_pow (a n m : mynat) : (a ^ n) ^ m = a ^ (n * m).
Proof.
  induction m.
  rewrite mul_zero.
  repeat rewrite pow_zero.
  reflexivity.
  rewrite pow_succ.
  rewrite IHm.
  rewrite mul_succ.
  rewrite pow_add.
  reflexivity.
Qed.

(* Level 8 *)

Lemma add_squared (a b : mynat) :
  (a + b) ^ (2 : mynat) = a ^ (2 : mynat) + b ^ (2 : mynat) + 2 * a * b.
Proof.
  rewrite two_eq_succ_one.
  rewrite one_eq_succ_zero.
  repeat rewrite pow_succ.
  repeat rewrite pow_zero.
  repeat rewrite one_mul.
  rewrite succ_mul.
  rewrite one_mul.
  rewrite mul_add.
  repeat rewrite add_mul.
  rewrite add_assoc.
  rewrite <- (add_assoc (b * a) _ _ ).
  rewrite (add_comm _ (b * b)).
  rewrite (add_comm (b * a) _).
  rewrite (mul_comm b a).
  rewrite <- add_assoc.
  reflexivity.
Qed.
