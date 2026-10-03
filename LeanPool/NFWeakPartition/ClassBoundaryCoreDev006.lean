/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.ClassBoundaryNormalizationDev005

/-! NF weak partition development: ClassBoundaryCoreDev006. -/


public section

namespace NFChoice.DirectCertificate.ClassBoundaryCoreDev006

open scoped Fol
open NFChoice.Foundation
open NFChoice.Foundation.ExactLiteralTrial
open NFChoice.DirectCertificate.ClassBoundaryNormalizationDev005

abbrev Theory : Fol.SentTheory LNF :=
  LiteralHailperinNF

@[expose]
def classEq (P Q : Fol.formula LNF) : Fol.formula LNF :=
  ∀'(P ⇔ Q)

@[expose]
def classMem (P Q : Fol.formula LNF) : Fol.formula LNF :=
  ∃'(represents (&0) (Fol.lift_formula_at P 1 1) ⊓' Q)

@[expose]
def literalAxExtProof : Theory.fst ⊢ (literalAxiomFormula .axExt).fst :=
  Fol.prf.axm (Set.mem_image_of_mem _ (literalAxiom_mem .axExt))

theorem literalAxExtFlypitch :
    (literalAxiomFormula .axExt).fst =
      ∀'(∀'((∀'(mem (&0) (&2) ⇔ mem (&0) (&1))) ⟹ ((&1) ≃ (&0)))) :=
  by rfl

theorem liftTwoSubstOne (s t : Fol.term LNF) :
    Fol.subst_term (Fol.lift_term s 2) t 1 = Fol.lift_term s 1 := by
  simpa using (Fol.lift_subst_term_medium s t 1 0)

@[expose]
noncomputable def axExtAt (s t : Fol.term LNF) :
    Theory.fst ⊢ represents s (cvPred t) ⟹ (s ≃ t) :=
  by
  have h : Theory.fst ⊢ ∀'(∀'((∀'(mem (&0) (&2) ⇔ mem (&0) (&1))) ⟹ ((&1) ≃ (&0)))) :=
    by
    rw [← literalAxExtFlypitch]
    exact literalAxExtProof
  have hs := Fol.prf.allE₂ _ s h
  have hst := Fol.prf.allE₂ _ t hs
  simpa [represents, cvPred, mem, Fol.subst_formula, Fol.subst_term, Fol.lift_term1,
    liftTwoSubstOne] using hst

/-- The one extensionality kernel shared by `df-clab`, `df-cleq`, and `df-clel`.
-/
@[expose]
noncomputable def classMemCv (x : Fol.term LNF) (Q : Fol.formula LNF) :
    Theory.fst ⊢ classMem (cvPred x) Q ⇔ applyPred Q x :=
  by
  apply Fol.biimpI
  · let source := classMem (cvPred x) Q
    have hSource : insert source Theory.fst ⊢ source := Fol.axm1
    apply Fol.exE hSource
    let body := represents (&0) (Fol.lift_formula_at (cvPred x) 1 1) ⊓' Q
    have hBody : insert body (Fol.lift_formula1 '' insert source Theory.fst) ⊢ body :=
      Fol.axm1
    have hRep :
      insert body (Fol.lift_formula1 '' insert source Theory.fst) ⊢
        represents (&0) (Fol.lift_formula_at (cvPred x) 1 1) :=
      Fol.andE1 Q hBody
    have hQ : insert body (Fol.lift_formula1 '' insert source Theory.fst) ⊢ Q :=
      Fol.andE2 _ hBody
    let delta : Set (Fol.formula LNF) :=
      insert body (Fol.lift_formula1 '' insert source Theory.fst)
    have hTheorySubset : Theory.fst ⊆ delta :=
      by
      intro f hf
      apply Set.mem_insert_of_mem
      rw [Set.image_insert_eq, Fol.SentTheory.lift_irrel Theory]
      exact Set.mem_insert_of_mem _ hf
    have hExt0 := Fol.weakening hTheorySubset (axExtAt (&0) (Fol.lift_term1 x))
    have hExt :
      delta ⊢
        represents (&0) (Fol.lift_formula_at (cvPred x) 1 1) ⟹
          ((&0) ≃ Fol.lift_term1 x) :=
      by
      rw [← cvPredLiftForWitness]
      exact hExt0
    have hEq : delta ⊢ ((&0) ≃ Fol.lift_term1 x) := Fol.prf.impE _ hExt hRep
    apply Fol.prf_subst (Fol.lift_formula_at Q 1 1) hEq
    · simpa only [Fol.lift_subst_formula_cancel] using hQ
    · exact Fol.lift_at_subst_formula_small0 Q x 1 0
  · let gamma : Set (Fol.formula LNF) := insert (applyPred Q x) Theory.fst
    have hRepSelf : gamma ⊢ represents x (cvPred x) :=
      by
      apply Fol.prf.allI
      exact Fol.biimp_refl _ (mem (&0) (Fol.lift_term1 x))
    have hQ : gamma ⊢ applyPred Q x := Fol.axm1
    have hAnd : gamma ⊢ represents x (cvPred x) ⊓' applyPred Q x := Fol.andI hRepSelf hQ
    apply Fol.exI x
    rw [classMemWitnessBodySubst]
    exact hAnd


end NFChoice.DirectCertificate.ClassBoundaryCoreDev006
