Require Export IntuitionisticNaturalDeduction.
Require Export PropositionalLogicExpressions.
Set Warnings "-deprecated-hint-without-locality".

(* Natural Deduction for Classical Propositional Logic (NK) *)
(********************************************************************************)

(* A natural deduction system for classical propositional logic requires
   an additional classical axiom on top of the rules of NJ. The law of 
   double-negation elimination will be the simplest for later proving Gilvenko's 
   Theorem. Later in this file other classical axioms will be explored. 
   
   We replace ex falso quodlibet with the following classical axiom:
   
     Γ, ¬A ⊢c ⊥
     -----------  (¬¬E) (double negation elimination)
       Γ ⊢c A

   note that ex falso quodlibet can be derived from this rule.
*)

Reserved Notation "Γ '⊢c' A" (at level 97).
Inductive NK : list Lexp -> Lexp -> Prop :=
  | NKleaf  : forall Γ A, 
                    In A Γ -> Γ ⊢c A
  | NKimpI : forall Γ A B, 
                    A :: Γ ⊢c B -> 
                    Γ ⊢c A ⊃ B 
  | NKimpE  : forall Γ A B, 
                    Γ ⊢c A ⊃ B -> Γ ⊢c A -> 
                    Γ ⊢c B
  | NKandI : forall Γ A B, 
                    Γ ⊢c A -> Γ ⊢c B -> 
                    Γ ⊢c A /\ B 
  | NKandE_l  : forall Γ A B, 
                    Γ ⊢c A /\ B -> 
                    Γ ⊢c A 
  | NKandE_r  : forall Γ A B, 
                    Γ ⊢c A /\ B -> 
                    Γ ⊢c B 
  | NKorI_l : forall Γ A B, 
                    Γ ⊢c A -> 
                    Γ ⊢c A \/ B 
  | NKorI_r : forall Γ A B, 
                    Γ ⊢c B -> 
                    Γ ⊢c A \/ B 
  | NKorE : forall Γ A B C, 
                    Γ ⊢c A \/ B -> A :: Γ ⊢c C -> B :: Γ ⊢c C ->
                    Γ ⊢c C
  | NKdnE  : forall Γ A, 
                   (¬A) :: Γ ⊢c ⊥ ->
                    Γ ⊢c A       (* Double-negation elimination axiom *)
  where "Γ '⊢c' A" := (NK Γ A) : Lscope.
Hint Constructors NK : Lexp_db.

(* A theorem of NK is a proposition provable with no assumptions. *)
Definition NKTheorem A : Prop := [] ⊢c A.

(* Helpful derivable rules in NK: *)
   
Lemma NKweakening_aux : forall Γ A Δ,
  Γ ⊢c A -> (all_in Γ Δ) -> Δ ⊢c A.
Proof.
  intros Γ A Δ H. generalize dependent Δ. 
  induction H; eauto 4 with Lexp_db; intros Δ H'.
  - eapply NKimpI; eapply IHNK; eapply in_same_cons; assumption.
  - apply NKorE with (A:=A) (B:=B) (C:=C).
    + apply IHNK1; assumption.
    + apply IHNK2; eapply in_same_cons; assumption. 
    + apply IHNK3; eapply in_same_cons; assumption.
  - eapply NKdnE; eapply IHNK; eapply in_same_cons; assumption.
Qed. 

Theorem NKweakening : forall Γ A B,
   Γ ⊢c A -> B::Γ ⊢c A.
Proof.
  intros Γ A B H. 
  eapply NKweakening_aux; try eapply H.
  intros X H'; eapply in_cons; trivial.
Qed.

Theorem NKdeduction : forall Γ A B,
  Γ ⊢c A ⊃ B -> A::Γ ⊢c B.
Proof.
  intros Γ A B H. eapply NKweakening in H.
  assert (H': A :: Γ ⊢c A); try (eapply NKleaf; left; reflexivity).
  eapply NKimpE; eassumption.
Qed.

Lemma NKbotE : forall Γ A,
  Γ ⊢c ⊥ -> Γ ⊢c A.
Proof.
   intros Γ A H; eapply NKdnE; eapply NKweakening in H; eassumption.
Qed.
Hint Resolve NKbotE : Lexp_db.

Lemma NKdeduct_tauto : forall Γ A, 
  Γ ⊢c A ⊃ A.
Proof.
  intros; eapply NKimpI; eapply NKleaf; left; trivial.
Qed.

(********************************************************************************)

(* An aside on the equivalence of including various other classical 
   tautologies to create alternative systems of NK. These new systems
   require ex falso quodlibet for full classical strength. *)

Module equivalentNKSystems.

(* We add the Law of Excluded Middle to this system (NK') *)
Reserved Notation "Γ '⊢c'' A" (at level 97).
Inductive NK' : list Lexp -> Lexp -> Prop :=
  | NK'leaf  : forall Γ A, 
                    In A Γ -> Γ ⊢c' A
  | NK'impI : forall Γ A B, 
                    A :: Γ ⊢c' B -> 
                    Γ ⊢c' A ⊃ B 
  | NK'impE  : forall Γ A B, 
                    Γ ⊢c' A ⊃ B -> Γ ⊢c' A -> 
                    Γ ⊢c' B
  | NK'andI : forall Γ A B, 
                    Γ ⊢c' A -> Γ ⊢c' B -> 
                    Γ ⊢c' A /\ B 
  | NK'andE_l  : forall Γ A B, 
                    Γ ⊢c' A /\ B -> 
                    Γ ⊢c' A 
  | NK'andE_r  : forall Γ A B, 
                    Γ ⊢c' A /\ B -> 
                    Γ ⊢c' B 
  | NK'orI_l : forall Γ A B, 
                    Γ ⊢c' A -> 
                    Γ ⊢c' A \/ B 
  | NK'orI_r : forall Γ A B, 
                    Γ ⊢c' B -> 
                    Γ ⊢c' A \/ B 
  | NK'orE : forall Γ A B C, 
                    Γ ⊢c' A \/ B -> A :: Γ ⊢c' C -> B :: Γ ⊢c' C ->
                    Γ ⊢c' C
  | NK'botE  : forall Γ A, 
                    Γ ⊢c' ⊥ ->
                    Γ ⊢c' A                 
  | NK'em  : forall Γ A, 
                    Γ ⊢c' A \/ ¬A (* New axiom *)          
  where "Γ '⊢c'' A" := (NK' Γ A) : Lscope.
Local Hint Constructors NK' : Lexp_db.

(* Identical helpful derivable rules *)

Lemma NK'weakening_aux : forall Γ A Δ, 
  Γ ⊢c' A -> (all_in Γ Δ) -> Δ ⊢c' A.
Proof.
  intros Γ A Δ H. generalize dependent Δ. 
  induction H; eauto 4 with Lexp_db; intros Δ H'.
  - eapply NK'impI; eapply IHNK'; eapply in_same_cons; assumption.
  - apply NK'orE with (A:=A) (B:=B) (C:=C).
    + apply IHNK'1; assumption.
    + apply IHNK'2; eapply in_same_cons; assumption. 
    + apply IHNK'3; eapply in_same_cons; assumption.
Qed.

Theorem NK'weakening : forall Γ A B,
   Γ ⊢c' A -> B::Γ ⊢c' A.
Proof.
  intros Γ A B H. 
  eapply NK'weakening_aux; try eapply H.
  intros X H'; eapply in_cons; trivial.
Qed.

Theorem NK'deduction : forall Γ A B,
  Γ ⊢c' A ⊃ B -> A::Γ ⊢c' B.
Proof.
  intros Γ A B H. eapply NK'weakening in H.
  assert (H': A :: Γ ⊢c' A); try (eapply NK'leaf; left; reflexivity).
  eapply NK'impE; eassumption.
Qed.

(* We add Pierce's tautology to this system (NK'') *)
Reserved Notation "Γ '⊢c''' A" (at level 97).
Inductive NK'' : list Lexp -> Lexp -> Prop :=
  | NK''leaf  : forall Γ A, 
                    In A Γ -> Γ ⊢c'' A
  | NK''impI : forall Γ A B, 
                    A :: Γ ⊢c'' B -> 
                    Γ ⊢c'' A ⊃ B 
  | NK''impE  : forall Γ A B, 
                    Γ ⊢c'' A ⊃ B -> Γ ⊢c'' A -> 
                    Γ ⊢c'' B
  | NK''andI : forall Γ A B, 
                    Γ ⊢c'' A -> Γ ⊢c'' B -> 
                    Γ ⊢c'' A /\ B 
  | NK''andE_l  : forall Γ A B, 
                    Γ ⊢c'' A /\ B -> 
                    Γ ⊢c'' A 
  | NK''andE_r  : forall Γ A B, 
                    Γ ⊢c'' A /\ B -> 
                    Γ ⊢c'' B 
  | NK''orI_l : forall Γ A B, 
                    Γ ⊢c'' A -> 
                    Γ ⊢c'' A \/ B 
  | NK''orI_r : forall Γ A B, 
                    Γ ⊢c'' B -> 
                    Γ ⊢c'' A \/ B 
  | NK''orE : forall Γ A B C, 
                    Γ ⊢c'' A \/ B -> A :: Γ ⊢c'' C -> B :: Γ ⊢c'' C ->
                    Γ ⊢c'' C
  | NK''botE  : forall Γ A, 
                    Γ ⊢c'' ⊥ ->
                    Γ ⊢c'' A           
  | NK''pierce  : forall Γ A B, 
                    Γ ⊢c'' ((A ⊃ B) ⊃ A) ⊃ A  (* New axiom *)        
  where "Γ '⊢c''' A" := (NK'' Γ A) : Lscope.
Local Hint Constructors NK'' : Lexp_db.

(* Identical helpful derivable rules *)

Lemma NK''weakening_aux : forall Γ A Δ, 
  Γ ⊢c'' A -> (all_in Γ Δ) -> Δ ⊢c'' A.
Proof.
  intros Γ A Δ H. generalize dependent Δ. 
  induction H; eauto 4 with Lexp_db; intros Δ H'.
  - eapply NK''impI; eapply IHNK''; eapply in_same_cons; assumption.
  - apply NK''orE with (A:=A) (B:=B) (C:=C).
    + apply IHNK''1; assumption.
    + apply IHNK''2; eapply in_same_cons; assumption. 
    + apply IHNK''3; eapply in_same_cons; assumption.
Qed.

Theorem NK''weakening : forall Γ A B,
   Γ ⊢c'' A -> B::Γ ⊢c'' A.
Proof.
  intros Γ A B H. 
  eapply NK''weakening_aux; try eapply H.
  intros X H'; eapply in_cons; trivial.
Qed.

Theorem NK''deduction : forall Γ A B,
  Γ ⊢c'' A ⊃ B -> A::Γ ⊢c'' B.
Proof.
  intros Γ A B H. eapply NK''weakening in H.
  assert (H': A :: Γ ⊢c'' A); try (eapply NK''leaf; left; reflexivity).
  eapply NK''impE; eassumption.
Qed.

(********************************************************************************)
(* Proof of the equivalence of these representations of NK *)

(* Automation will prove most equivalence cases due to identical
   constuctors. The non-trivial parts of this proof involve
   deriving the various classical axioms from each other. *)

Theorem NKdn_NKem_equiv : forall Γ A,
  (Γ ⊢c A) <-> (Γ ⊢c' A).
Proof.
  intros Γ A; split; intros H; 
    induction H; eauto 2 with Lexp_db.
  - eapply NK'orE. 
      apply NK'em with (A:=A).
      eapply NK'leaf; left; trivial.
      eapply NK'botE; eassumption. 
  - eapply NKdnE; eapply NKimpE.
      eapply NKimpI; eapply NKimpE.
        eapply NKleaf; right; left; trivial.
        eapply NKorI_r; eapply NKleaf; left; trivial.
      eapply NKimpI; eapply NKimpE.
        eapply NKleaf; right; left; trivial.
        eapply NKorI_l; eapply NKleaf; left; trivial.
Qed. 

Theorem NKdn_NKpierce_equiv : forall Γ A,
  (Γ ⊢c A) <-> (Γ ⊢c'' A).
Proof.
  intros Γ A; split; intros H; 
    induction H; eauto 2 with Lexp_db.
  - eapply NK''impE.
      apply NK''pierce with (A:=A) (B:=⊥).
      eapply NK''impI; eapply NK''botE; eassumption.
  - eapply NKimpI; eapply NKdnE; eapply NKimpE.
      eapply NKleaf; left; trivial.
      eapply NKimpE.
        eapply NKleaf; right; left; trivial.
        eapply NKimpI; eapply NKdnE; eapply NKimpE.
          eapply NKleaf; right; right; left; trivial.
          eapply NKleaf; right; left; trivial.
Qed. 

Theorem NKem_NKpierce_equiv : forall Γ A,
  (Γ ⊢c' A) <-> (Γ ⊢c'' A).
Proof.
  intros Γ A; eapply iff_trans.
  - eapply iff_sym; apply NKdn_NKem_equiv.
  - apply NKdn_NKpierce_equiv.
Qed.

(* It is shown that all three representations of NK are extensionally equivalent 
   systems, in that they all prove and refute the identical sets of propositions. *)
  
End equivalentNKSystems.
  
(* David Spitz, 03/13/2022 *)
