Require Import Unicode.Utf8.
Require Import Classical.

(* Level 1 *)
(* `split`: Prove each part of a conjunction separately *)
(* Goal of the form `A ∧ B` *)

Lemma example_1_adv_add (P Q : Prop) (p : P) (q : Q) : P ∧ Q.
Proof.
  split.
  exact p.
  apply q.
Qed.

(* Level 2 *)
(* `destruct f as [g h]`: Split conjunction hypothesis into two child hypotheses *)
(* Hypothesis of the form `A ∧ B` *)

Lemma and_symm (P Q : Prop) : P ∧ Q → Q ∧ P.
Proof.
  intro f.
  destruct f as [p q].
  split.
  exact q.
  exact p.
Qed.

(* Level 3 *)

Lemma and_trans (P Q R : Prop) : P ∧ Q → Q ∧ R → P ∧ R.
Proof.
  intro f.
  intro g.
  destruct f as [p q].
  destruct g as [q' r].
  split.
  exact p.
  exact r.
Qed.

(* Level 4 *)

Lemma iff_trans (P Q R : Prop) : (P ↔ Q) → (Q ↔ R) → (P ↔ R).
Proof.
  intro f.
  intro g.
  destruct f as [pq qp].
  destruct g as [gr rg].
  split.
  intro p.
  apply gr.
  apply pq.
  exact p.
  intro r.
  apply qp.
  apply rg.
  exact r.
Qed.

(* Level 5 *)
(* Lean `apply f.1` ~ Coq ??? *)

Lemma iff_trans' (P Q R : Prop) : (P ↔ Q) → (Q ↔ R) → (P ↔ R).
Proof.
  intro f.
  intro g.
  rewrite f.
  rewrite g.
  reflexivity.
Qed.

(* Level 6 *)
(* `left`: Prove LHS of disjunction *)
(* Goal of the form `A ∨ B` *)

(* `right`: Prove RHS of disjunction *)
(* Goal of the form `A ∨ B` *)

Lemma example_6_adv_add (P Q : Prop) : Q → (P ∨ Q).
Proof.
  intro q.
  right.
  exact q.
Qed.

(* Level 7 *)
(* `destruct f as [g|h]`: Split disjunction hypothesis into two child hypotheses *)
(* Hypothesis of the form `A ∨ B` *)

Lemma or_symm (P Q : Prop) : P ∨ Q → Q ∨ P.
Proof.
  intro f.
  destruct f as [p|q].
  right.
  exact p.
  left.
  exact q.
Qed.

(* Level 8 *)
(* `assumption`: Solve goal that is already a hypothesis *)
(* `tactic1; tactic2`: Run tactic2 on all sub-goals produced by tactic1 *)

Lemma and_or_distrib_left (P Q R : Prop) : P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R).
Proof.
  split.
  intro f.
  destruct f as [p qr].
  destruct qr as [q|r].
  left.
  split; assumption.
  right.
  split; assumption.
  intro f.
  destruct f as [pq|pr].
  destruct pq as [p q].
  split.
  exact p.
  left.
  exact q.
  destruct pr as [p r].
  split.
  exact p.
  right.
  exact r.
Qed.

(* Level 9 *)
(* `exfalso`: Change any goal into `False` *)

Lemma contra (P Q : Prop) : (P ∧ ¬ P) → Q.
Proof.
  intro f.
  destruct f as [p np].
  exfalso.
  apply np.
  exact p.
Qed.

(* Level 10 *)
(* `destruct (classic P) as [p|np]`: Do case distinction on `P` *)
(* In other words, handle cases `P` and `¬P` separately *)
(* Requires classical logic `Classical` *)

Lemma contrapositive2 (P Q : Prop) : (¬ Q → ¬ P) → (P → Q).
Proof.
  intro f.
  intro p'.
  destruct (classic P) as [p|np];
  destruct (classic Q) as [q|nq];
  tauto.
Qed.
