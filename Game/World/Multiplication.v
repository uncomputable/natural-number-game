Require Import Unicode.Utf8.
Require Import Game.Mynat.Definition.
Require Import Game.Mynat.Add.
Require Import Game.Mynat.Mul.
Require Import Game.World.Addition.

(* Level 1 *)

Lemma zero_mul (a : mynat) : 0 * a = 0.
Proof.
  induction a.
  reflexivity.
  rewrite mul_succ.
  rewrite IHa.
  reflexivity.
Qed.

(* Level 2 *)

Lemma mul_one (a : mynat) : a * 1 = a.
Proof.
  rewrite one_eq_succ_zero.
  rewrite mul_succ.
  rewrite mul_zero.
  rewrite zero_add.
  reflexivity.
Qed.

(* Level 3 *)

Lemma one_mul (a : mynat) : 1 * a = a .
Proof.
  induction a.
  reflexivity.
  rewrite mul_succ.
  rewrite IHa.
  rewrite succ_eq_add_one.
  reflexivity.
Qed.

(* Level 4 *)

Lemma mul_add (t a b : mynat) : t * (a + b) = t * a + t * b.
Proof.
  induction a.
  rewrite mul_zero.
  repeat rewrite zero_add.
  reflexivity.
  rewrite succ_add.
  repeat rewrite mul_succ.
  rewrite IHa.
  rewrite add_right_comm.
  reflexivity.
Qed.

(* Level 5 *)

Lemma mul_assoc (a b c : mynat) : (a * b) * c = a * (b * c).
Proof.
  induction c.
  repeat rewrite mul_zero.
  reflexivity.
  repeat rewrite mul_succ.
  rewrite IHc.
  rewrite mul_add.
  reflexivity.
Qed.

(* Level 6 *)

Lemma succ_mul (a b : mynat) : succ a * b = a * b + b.
Proof.
  induction b.
  repeat rewrite mul_zero.
  reflexivity.
  repeat rewrite mul_succ.
  rewrite IHb.
  repeat rewrite add_succ.
  rewrite add_right_comm.
  reflexivity.
Qed.

(* Level 7 *)

Lemma add_mul (a b t : mynat) : (a + b) * t = a * t + b * t.
Proof.
  induction t.
  repeat rewrite mul_zero.
  reflexivity.
  repeat rewrite mul_succ.
  rewrite IHt.
  rewrite <- add_assoc.
  rewrite <- add_assoc.
  rewrite (add_right_comm _ _ a).
  reflexivity.
Qed.

(* Level 8 *)

Lemma mul_comm (a b : mynat) : a * b = b * a.
Proof.
  induction b.
  rewrite zero_mul.
  reflexivity.
  rewrite mul_succ.
  rewrite succ_mul.
  rewrite IHb.
  reflexivity.
Qed.

(* Level 9 *)

Lemma mul_left_comm (a b c : mynat) : a * (b * c) = b * (a * c).
Proof.
  rewrite mul_comm.
  rewrite mul_assoc.
  rewrite (mul_comm c a).
  reflexivity.
Qed.
