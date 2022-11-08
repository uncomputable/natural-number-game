Require Import Unicode.Utf8.
Require Import Game.Mynat.Definition.

(* Level 1 *)
(* `exact f`: Solve goal that equals hypothesis `f` *)
(* Hypothesis `f` of the form `A` *)
(* Goal of the form `A` *)

Lemma example_1_func (P Q : Type) (p : P) (h : P → Q) : Q.
Proof.
  exact (h p).
Qed.

(* Level 2 *)
(* `intro f`: Put LHS of implication into new hypothesis `f` *)
(* Goal of the form `A → B` *)

Lemma example_2_func: mynat → mynat.
Proof.
  intro n.
  exact 1.
Qed.

(* Level 3 *)
(* `pose (f := x)`: Create new hypothesis `f` defined as `x` *)

Lemma example_3_func (P Q R S T U: Type)
(p : P)
(h : P → Q)
(i : Q → R)
(j : Q → T)
(k : S → T)
(l : T → U)
: U.
Proof.
  pose (q := h p).
  pose (t := j(q)).
  pose (u := l(t)).
  exact u.
Qed.


(* Level 4 *)
(* `apply f`: Replace goal with the LHS of the implication of hypothesis `f` *)
(* Hypothesis `f` of the form `B → A` *)
(* Goal of the form `A` *)

Lemma example_4_func (P Q R S T U: Type)
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

Lemma example_5_func (P Q : Type) : P → (Q → P).
Proof.
  intro p.
  intro q.
  exact p.
Qed.

(* Level 6 *)

Lemma example_6_func (P Q R : Type) : (P → (Q → R)) → ((P → Q) → (P → R)).
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

Lemma example_7_func (P Q F : Type) : (P → Q) → ((Q → F) → (P → F)).
Proof.
  intro f.
  intro g.
  intro p.
  apply g.
  apply f.
  exact p.
Qed.

(* Level 8 *)

Lemma example_8_func (P Q : Type) : (P → Q) → ((Q → Empty_set) → (P → Empty_set)).
Proof.
  intro f.
  intro g.
  intro p.
  apply g.
  apply f.
  exact p.
Qed.

(* Level 9 *)

Lemma example_9_func (A B C D E F G H I J K L : Type)
(f1 : A → B) (f2 : B → E) (f3 : E → D) (f4 : D → A) (f5 : E → F)
(f6 : F → C) (f7 : B → C) (f8 : F → G) (f9 : G → J) (f10 : I → J)
(f11 : J → I) (f12 : I → H) (f13 : E → H) (f14 : H → K) (f15 : I → L)
 : A → L.
Proof.
  intro a.
  apply f15.
  apply f11.
  apply f9.
  apply f8.
  apply f5.
  apply f2.
  apply f1.
  exact a.
Qed.
