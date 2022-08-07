From Coq Require Export Lists.List.
Export ListNotations.

(* Definition of the type of propositional logical expressions,
   notations, and some helpful lemmas *)

(* It turns out we never interact with a pure propositional variable, 
   so the type we use to represent it is irrelevant. *)
Inductive propVars : Set.

(* We define the type of a logical expression by these rules : 
   - Any propositional variable is a logical expression.
   - Falsum is a logical expression (this will represent contradiction)
   - If A and B are logical expressions, then so is A /\ B 
   - If A and B are logical expressions, then so is A \/ B 
   - If A and B are logical expressions, then so is A ⊃ B  
   This leads to the following inductive type and notations : *)
Inductive Lexp : Type :=
  | Var (v : propVars)
  | Falsum
  | Land (A B : Lexp)
  | Lor (A B : Lexp)
  | Limp (A B : Lexp)
.

Declare Scope Lscope.
Open Scope Lscope. 
Notation "# v" := (Var v) (at level 40) : Lscope.
Notation "⊥" := Falsum (at level 80) : Lscope.
Notation "A '/\' B" := (Land A B) (at level 80, right associativity) : Lscope.
Notation "A '\/' B" := (Lor A B) (at level 85, right associativity) : Lscope.
Notation "A '⊃' B" := (Limp A B) (at level 90, right associativity) : Lscope.
Notation "¬ A" := (A ⊃ ⊥)  (at level 75, right associativity) : Lscope.

(* Here are some helpful list lemmas and definitions for later proofs *)

Definition all_in {X : Type} (l1 l2 : list X) : Prop :=
  forall (x : X), In x l1 -> In x l2.

Lemma in_same_cons : forall (X: Type) (l1 l2 : list X) (h : X), 
  all_in l1 l2 -> all_in (h::l1) (h::l2).
Proof.
  intros X l1 l2 h H x [H'|H']; subst.
  - left; trivial.
  - right; auto.
Qed.

(* David Spitz, 03/13/2022 *)