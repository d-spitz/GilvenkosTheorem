Require Export PropositionalLogicExpressions.
Set Warnings "-deprecated-hint-without-locality".

(* Natural Deduction for Intuitionistic Propositional Logic (NJ) *)
(********************************************************************************)

(* We define rules of natural deduction using an inductive proposition. 
   The list of logical expressions to the left of the turnstile represent 
   assumptions, and the conclusion is represented by a single logical expression 
   to the right of the turnstile. 
   
   Here are the rules presented graphically:
   
     ---------  (leaf axiom)
     Γ, A ⊢ A
     
     Γ, A ⊢ B           Γ ⊢ A ⊃ B     Γ ⊢ A
     ---------  (⊃I)   -------------------  (⊃E)
     Γ ⊢ A ⊃ B                 Γ ⊢ B
    
     Γ ⊢ A     Γ ⊢ B           Γ ⊢ A /\ B             Γ ⊢ A /\ B   
     ---------------  (/\I)   -----------  (/\E_l)   ----------  (/\E_r)
     Γ ⊢ A /\ B                Γ ⊢ A                  Γ ⊢ B
     
     Γ ⊢ A                Γ ⊢ B                  Γ ⊢ A \/ B   Γ, A ⊢ C   Γ, B ⊢ C
     --------  (\/I_l)   -----------  (\/I_r)   --------------------------------  (\/E) 
     Γ ⊢ A \/ B           Γ ⊢ A \/ B                          Γ ⊢ C
     
     Γ ⊢ ⊥
     ------  (⊥E) (ex falso quodlibet)
     Γ ⊢ A
*)

Reserved Notation "Γ '⊢' A" (at level 97).
Inductive NJ : list Lexp -> Lexp -> Prop :=
  | NJleaf  : forall Γ A, 
                    In A Γ -> Γ ⊢ A
  | NJimpI : forall Γ A B, 
                    A :: Γ ⊢ B -> 
                    Γ ⊢ A ⊃ B 
  | NJimpE  : forall Γ A B, 
                    Γ ⊢ A ⊃ B -> Γ ⊢ A -> 
                    Γ ⊢ B
  | NJandI : forall Γ A B, 
                    Γ ⊢ A -> Γ ⊢ B -> 
                    Γ ⊢ A /\ B 
  | NJandE_l  : forall Γ A B, 
                    Γ ⊢ A /\ B -> 
                    Γ ⊢ A 
  | NJandE_r  : forall Γ A B, 
                    Γ ⊢ A /\ B -> 
                    Γ ⊢ B 
  | NJorI_l : forall Γ A B, 
                    Γ ⊢ A -> 
                    Γ ⊢ A \/ B 
  | NJorI_r : forall Γ A B, 
                    Γ ⊢ B -> 
                    Γ ⊢ A \/ B 
  | NJorE : forall Γ A B C, 
                    Γ ⊢ A \/ B -> A :: Γ ⊢ C -> B :: Γ ⊢ C ->
                    Γ ⊢ C
  | NJbotE  : forall Γ A, 
                    Γ ⊢ ⊥ ->
                    Γ ⊢ A                 
  where "Γ '⊢' A" := (NJ Γ A) : Lscope.
Hint Constructors NJ : Lexp_db.

(* A theorem of NJ is a proposition provable with no assumptions. *)
Definition NJTheorem A : Prop := [] ⊢ A.

(* Helpful derivable rules in NJ: 

   Credit to Floris van Doorn for this tricky weakening proof (as well
   as the various other weakening theorems) which needs a specific 
   approach for Coq to let it go through. *)

Lemma NJweakening_aux : forall Γ A Δ, 
  Γ ⊢ A -> (all_in Γ Δ) -> Δ ⊢ A.
Proof.
  intros Γ A Δ H. generalize dependent Δ. 
  induction H; eauto 4 with Lexp_db; intros Δ H'.
  - eapply NJimpI; eapply IHNJ; eapply in_same_cons; assumption.
  - apply NJorE with (A:=A) (B:=B) (C:=C).
    + apply IHNJ1; assumption.
    + apply IHNJ2; eapply in_same_cons; assumption. 
    + apply IHNJ3; eapply in_same_cons; assumption.
Qed.

Theorem NJweakening : forall Γ A B,
   Γ ⊢ A -> B::Γ ⊢ A.
Proof.
  intros Γ A B H. 
  eapply NJweakening_aux; try eapply H.
  intros X H'; eapply in_cons; trivial.
Qed.

Theorem NJdeduction : forall Γ A B,
  Γ ⊢ A ⊃ B -> A::Γ ⊢ B.
Proof.
  intros Γ A B H. eapply NJweakening in H.
  assert (H': A :: Γ ⊢ A); try (eapply NJleaf; left; reflexivity).
  eapply NJimpE; eassumption.
Qed.

Lemma NJdeduct_tauto : forall Γ A, 
  Γ ⊢ A ⊃ A.
Proof.
  intros; eapply NJimpI; eapply NJleaf; left; trivial.
Qed.

Lemma NJdnI : forall Γ A,
  Γ ⊢ A -> Γ ⊢ ¬¬A.
Proof.
  intros Γ A H.
  eapply NJimpI. eapply NJimpE.
    eapply NJleaf; left; trivial.
    eapply NJweakening in H; eassumption. 
Qed.

Lemma NJdnE_pseudo : forall Γ A,
  (Γ ⊢ ¬¬¬A) <-> (Γ ⊢ ¬A).
Proof.
  intros Γ A; split.
  - intros H. 
    eapply NJimpI. eapply NJimpE.
      eapply NJweakening in H; eassumption.
      eapply NJimpI. eapply NJimpE.
        eapply NJleaf; left; trivial.
        eapply NJleaf; right; left; trivial.
  - apply NJdnI.
Qed.

(* David Spitz, 03/13/2022 *)
