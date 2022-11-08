Require Import Unicode.Utf8.

(* Level 1 *)

Lemma example_1_prop (P Q : Prop) (p : P) (h : P → Q) : Q.
Proof.
  apply h.
  exact p.
Qed.

(* Level 2 *)

Lemma imp_self (P : Prop) : P → P.
Proof.
  intro p.
  exact p.
Qed.

(* Level 3 *)

Lemma maze1 (P Q R S T U: Prop)
(p : P)
(h : P → Q)
(i : Q → R)
(j : Q → T)
(k : S → T)
(l : T → U)
: U.
Proof.
  pose (q := h(p)).
  pose (t := j(q)).
  pose (u := l(t)).
  exact u.
Qed.

(* Level 4 *)

Lemma maze2 (P Q R S T U: Prop)
(p : P)
(h : P → Q)
(i : Q → R)
(j : Q → T)
(k : S → T)
(l : T → U)
: U.
Proof.
  apply l.
  apply j.
  apply h.
  exact p.
Qed.

(* Level 5 *)

Lemma example_5_prop (P Q : Prop) : P → (Q → P).
Proof.
  intro p.
  intro q.
  exact p.
Qed.

(* Level 6 *)

Lemma example_6_prop (P Q R : Prop) : (P → (Q → R)) → ((P → Q) → (P → R)).
Proof.
  intro f.
  intro g.
  intro p.
  apply f.
  exact p.
  apply g.
  exact p.
Qed.

(* Level 7 *)

Lemma imp_trans (P Q R : Prop) : (P → Q) → ((Q → R) → (P → R)).
Proof.
  intro f.
  intro g.
  intro p.
  apply g.
  apply f.
  exact p.
Qed.

(* Level 8 *)

Lemma contrapositive (P Q : Prop) : (P → Q) → (¬ Q → ¬ P).
Proof.
  (* ¬Q ↔ P → false *)
  unfold not.
  intro f.
  intro g.
  intro p.
  apply g.
  apply f.
  exact p.
Qed.

(* Level 9 *)
(* `tauto`: Automatically solve easy goals *)

Lemma example_9_prop (A B C D E F G H I J K L : Prop)
(f1 : A → B) (f2 : B → E) (f3 : E → D) (f4 : D → A) (f5 : E → F)
(f6 : F → C) (f7 : B → C) (f8 : F → G) (f9 : G → J) (f10 : I → J)
(f11 : J → I) (f12 : I → H) (f13 : E → H) (f14 : H → K) (f15 : I → L)
 : A → L.
Proof.
  tauto.
Qed.
