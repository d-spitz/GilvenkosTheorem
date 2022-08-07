Require Export ClassicalNaturalDeduction.
Require Export IntuitionisticNaturalDeduction.
Require Export PropositionalLogicExpressions.

(* A Proof of Gilvenko's Theorem and its consequences *)
(********************************************************************************)

(* We want to prove that for all propositions P, P is a theorem of 
   NK if and only if its double negation, ¬¬P, is a theorem of NJ. *)

(* The NJ -> NK direction of this statement is trivial, as all rules
   of NJ are contained in NK, and the double negation can be simply 
   eliminated in NK to prove the original proposition. *)
   
Lemma DN_l_aux : forall Γ A,
  Γ ⊢ A -> Γ ⊢c A.
Proof.
  intros Γ A H. 
  induction H; eauto 2 with Lexp_db.
  (* this automation simply applies the appropriate 
     identical constructors *)
Qed.

Theorem DN_l : forall Γ A,
  Γ ⊢ ¬¬A -> Γ ⊢c A.
Proof.
  intros Γ A H.
  eapply DN_l_aux in H; eapply NKdeduction in H;
  eapply NKdnE; trivial.
Qed.

(********************************************************************************)

(* To prove the NK -> NJ direction is non-trivial. We proceed
   by induction. For clarity, the cases of this induction, which 
   correspond to the rules of NK, are written as separte lemmas
   below. *)
   
Lemma DN_r_leaf : forall Γ A,
   In A Γ -> Γ ⊢ ¬¬A.
Proof.
  intros Γ A H.
  eapply NJdnI. 
  eapply NJleaf; trivial.
Qed.

Lemma DN_r_impI : forall Γ A B,
  A::Γ ⊢ ¬¬B -> Γ ⊢ ¬¬(A ⊃ B).
Proof.
  intros Γ A B H. 
  eapply NJimpI; eapply NJimpI in H.  
  eapply NJimpE.
    eapply NJleaf; left; trivial.
    eapply NJimpI; eapply NJbotE. 
    apply NJimpE with (A:=¬B) (B:=⊥).
      eapply NJdeduction; eapply NJweakening in H; eapply H.
      eapply NJimpI; eapply NJimpE.
        eapply NJleaf; right; right; left; trivial.
        eapply NJimpI; eapply NJleaf; right; left; trivial. 
Qed.

Lemma DN_r_impE : forall Γ A B,
  Γ ⊢ ¬¬(A ⊃ B) -> Γ ⊢ ¬¬A -> Γ ⊢ ¬¬B.
Proof.
  intros Γ A B H H'. 
  eapply NJimpI; eapply NJimpE.
    eapply NJweakening in H; eapply H. 
    eapply NJimpI; eapply NJimpE.
      do 2 (eapply NJweakening in H'); eapply H'.
      eapply NJimpI; eapply NJimpE.
        eapply NJleaf; right; right; left; trivial.
        eapply NJimpE.
          eapply NJleaf; right; left; trivial.
          eapply NJleaf; left; trivial.
Qed.

Lemma DN_r_andI : forall Γ A B,
  Γ ⊢ ¬¬A -> Γ ⊢ ¬¬B -> Γ ⊢ ¬¬(A /\ B).
Proof.
  intros Γ A B H H'. 
  eapply NJimpI; eapply NJweakening in H;
  eapply NJweakening in H'; eapply NJimpE.
    eapply H.
    eapply NJimpI; eapply NJimpE.
      eapply NJweakening in H'; eapply H'.
      eapply NJimpI; eapply NJimpE.
        eapply NJleaf; right; right; left; trivial.
        eapply NJandI.
          eapply NJleaf; right; left; trivial.
          eapply NJleaf; left; trivial.
Qed.

Lemma DN_r_andE_l : forall Γ A B,
  Γ ⊢ ¬¬(A /\ B) -> Γ ⊢ ¬¬A.
Proof.
  intros Γ A B H. 
  eapply NJimpI; eapply NJimpE.
    eapply NJweakening in H; eapply H.
    eapply NJimpI; eapply NJimpE.
      eapply NJleaf; right; left; trivial.
      eapply NJandE_l; eapply NJleaf; left; trivial.
Qed.

Lemma DN_r_andE_r : forall Γ A B,
  Γ ⊢ ¬¬(A /\ B) -> Γ ⊢ ¬¬B.
Proof.
  intros Γ A B H. 
  eapply NJimpI; eapply NJimpE.
    eapply NJweakening in H; eapply H.
    eapply NJimpI; eapply NJimpE.
      eapply NJleaf; right; left; trivial.
      eapply NJandE_r; eapply NJleaf; left; trivial.
Qed.

Lemma DN_r_orI_l : forall Γ A B,
  Γ ⊢ ¬¬A -> Γ ⊢ ¬¬(A \/ B).
Proof.
  intros Γ A B H. 
  eapply NJimpI; eapply NJweakening in H;
  eapply NJimpE. 
    eapply H.
    eapply NJimpI; eapply NJimpE.
      eapply NJleaf; right; left; trivial.
      eapply NJorI_l; eapply NJleaf; left; trivial.
Qed.

Lemma DN_r_orI_r : forall Γ A B,
  Γ ⊢ ¬¬B -> Γ ⊢ ¬¬(A \/ B).
Proof.
  intros Γ A B H. 
  eapply NJimpI; eapply NJweakening in H;
  eapply NJimpE. 
    eapply H.
    eapply NJimpI; eapply NJimpE.
      eapply NJleaf; right; left; trivial.
      eapply NJorI_r; eapply NJleaf; left; trivial.
Qed.

Lemma DN_r_orE : forall Γ A B C,
  Γ ⊢ ¬¬(A \/ B) -> A::Γ ⊢ ¬¬C -> B::Γ ⊢ ¬¬C -> 
    Γ ⊢ ¬¬C.
Proof.
  intros Γ A B C H1 H2 H3. 
  eapply NJimpI in H2; eapply NJimpI in H3;
  do 3 (eapply NJweakening in H2; eapply NJweakening in H3).
  eapply NJimpI; eapply NJimpE. 
    eapply NJweakening in H1; eapply H1.
    eapply NJimpI; apply NJimpE with (A:=¬C) (B:=⊥).
      eapply NJorE.
        eapply NJleaf; left; trivial.
        eapply NJimpE.
          eapply H2.
          eapply NJleaf; left; trivial.
        eapply NJimpE.
          eapply H3.
          eapply NJleaf; left; trivial.
        eapply NJleaf; right; left; trivial.
Qed.

Lemma DN_r_dnE : forall Γ A,
  (¬ A)::Γ ⊢ ¬¬(⊥) -> Γ ⊢ ¬¬A.
Proof.
  intros Γ A H.
  eapply NJimpI; eapply NJimpE.
    eapply H.
    eapply NJdeduct_tauto.
Qed. 


(* To complete our proof of this direction, we simply induct on
   our hypothesis of NK provability and apply the appropriate
   lemmas. *) 
Theorem DN_r : forall Γ A,
  Γ ⊢c A -> Γ ⊢ ¬¬A .
Proof.
  intros Γ A H.
  induction H. 
  - apply DN_r_leaf; trivial.
  - apply DN_r_impI; trivial.
  - eapply DN_r_impE; eassumption.
  - apply DN_r_andI; trivial.
  - eapply DN_r_andE_l; eassumption.
  - eapply DN_r_andE_r; eassumption.
  - apply DN_r_orI_l; trivial.
  - apply DN_r_orI_r; trivial.
  - eapply DN_r_orE; eassumption.
  - apply DN_r_dnE; trivial.
Qed.

(********************************************************************************)

(* We are ready to prove Gilvenko's theorem, first in its general form,
   then applying it to the specific case of theorems in these logics
   which must have no assumptions in Γ. *)
   
Theorem DNtranslation_general : forall Γ A,
  (Γ ⊢c A) <-> (Γ ⊢ ¬¬A).
Proof.
  intros Γ A; split.
  - apply DN_r.
  - apply DN_l.
Qed.

(* Gilvenko's theorem follows as a special case of the general translation. *)
Theorem DNtranslation : forall A,
  NKTheorem A <-> NJTheorem (¬¬A).
Proof.
  apply DNtranslation_general.
Qed.

(********************************************************************************)

(* Some corollaries of Gilvenko's theorem are presented below: *)

(* A negative version of the theorem, where for all propositions P, 
   P is not a theorem of NK if and only if its double negation, ~~P, 
   is not a theorem of NJ. 
   
   This completely links the two systems together, despite the impression
   that NJ would be "safer" or more conservative that NK. Also, informally,
   we can notice that the set of theorems of both systems have equivalent
   cardinalities, as their elements can be lined up one-to-one by matching
   each proposition with its translation. *)

Corollary DNtranslation_negative : forall A,
  ~ NKTheorem A <-> ~ NJTheorem (¬¬A).
Proof.
  intros A; apply Logic.not_iff_compat.
  apply DNtranslation.
Qed.

(* Another corollary of the theorem is that for all negated propositions
   ¬P, ¬P is provable in NK if and only if ¬P is provable in NJ. 
   
   In other words, the set of refutable propositions is identical between
   NK and NJ. *)

Corollary DNtranslation_not_general : forall Γ A,
  (Γ ⊢c ¬A) <-> (Γ ⊢ ¬A). 
Proof.
  intros Γ A; split.
  - intros H; apply DNtranslation_general in H;
    eapply NJdnE_pseudo; apply H.
  - eapply DN_l_aux. 
Qed.

Corollary DNtranslation_not : forall A,
  NKTheorem (¬A) <-> NJTheorem (¬A).
Proof.
  apply DNtranslation_not_general.
Qed.

(********************************************************************************)

(* Corollaries of the relative consistencies of NJ and NK: *)

(* A natural deduction system, ND, is consistent iff there is no proof of 
   the absurd in ND. ND is inconsistent iff there is a proof of the absurd
   in ND. *)

Definition inconsistent (ND : list Lexp -> Lexp -> Prop) : Prop :=
  ND [] (⊥).

Definition inconsistent' (ND : list Lexp -> Lexp -> Prop) : Prop :=
  exists A, and (ND [] A) (ND [] (¬A)).

Definition consistent (ND : list Lexp -> Lexp -> Prop) : Prop :=
  ~(inconsistent ND).

Definition consistent' (ND : list Lexp -> Lexp -> Prop) : Prop :=
  ~(inconsistent' ND).
  
(* In classical logic, the second definition (consistent') is sometimes 
   preferred for various reasons. Here I choose to use the first definition, 
   but the choice is inconsequential, because the two definitions of 
   consistency are equivalent here, as proven below. *)
   
Lemma consistent_consistent'_same : 
  (consistent NJ <-> consistent' NJ) /\
  (consistent NK <-> consistent' NK).
Proof.
  unfold consistent, consistent'.
  split; split; intros H H';
  try (destruct H' as [A H']; destruct H' as [H' H''];   
       apply H); 
  try (eapply NJimpE); try (eapply NKimpE);
  try (eapply H''); try (eapply H');
  try (apply H; exists (⊥); split);
  try (apply H'); try (apply NJdeduct_tauto);
    try (apply NKdeduct_tauto).
Qed.

(* Gilvenko's theorem reveals that NK and NJ are equiconsistent, that is, 
   if one is consistent, then so is the other, and if one is inconsistent, 
   then so is the other. This means that despite the strong philosophical
   divide between the logics, they actually share the exact same consistency 
   strength. *)

Theorem equiconsistency_negative : 
  inconsistent NK <-> inconsistent NJ.
Proof.
  unfold inconsistent.
  split; intros H.
  - apply DNtranslation in H. eapply NJimpE.
      apply H.
      eapply NJdeduct_tauto.
  - apply DNtranslation.
    eapply NJbotE. apply H.
Qed.

Theorem equiconsistency : 
  consistent NK <-> consistent NJ.
Proof.
  unfold consistent;
  apply Logic.not_iff_compat; apply equiconsistency_negative.
Qed.

Close Scope Lscope. 

(* David Spitz, 03/13/2022 *)