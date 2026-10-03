/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.ClassBoundaryBiimpDev009

/-! NF weak partition development: ClassBoundaryRawHandlersDev010. -/


public section

namespace NFChoice.DirectCertificate.ClassBoundaryRawHandlersDev010

open scoped Fol
open NFChoice.Foundation
open NFChoice.Foundation.ExactLiteralTrial
open NFChoice.DirectCertificate.ClassBoundaryNormalizationDev005
open NFChoice.DirectCertificate.ClassBoundaryCoreDev006
open NFChoice.DirectCertificate.ClassBoundaryBiimpDev009

abbrev Theory : Fol.SentTheory LNF :=
  LiteralHailperinNF

@[expose]
noncomputable def biimpSymm {L : Fol.Language} {Γ : Set (Fol.formula L)}
    {p q : Fol.formula L} (h : Γ ⊢ p ⇔ q) : Γ ⊢ q ⇔ p :=
  Fol.andI (Fol.andE2 (p ⟹ q) h) (Fol.andE1 (q ⟹ p) h)

@[expose]
noncomputable def andCongrRight {L : Fol.Language} {Γ : Set (Fol.formula L)}
    (p : Fol.formula L) {q r : Fol.formula L} (hqr : Γ ⊢ q ⇔ r) :
    Γ ⊢ (p ⊓' q) ⇔ (p ⊓' r) := by
  apply Fol.biimpI
  · have hSource : insert (p ⊓' q) Γ ⊢ p ⊓' q := Fol.axm1
    have hqr' : insert (p ⊓' q) Γ ⊢ q ⇔ r := Fol.weakening (Set.subset_insert _ _) hqr
    exact Fol.andI (Fol.andE1 q hSource) (biimpForward hqr' (Fol.andE2 p hSource))
  · have hSource : insert (p ⊓' r) Γ ⊢ p ⊓' r := Fol.axm1
    have hqr' : insert (p ⊓' r) Γ ⊢ q ⇔ r := Fol.weakening (Set.subset_insert _ _) hqr
    exact Fol.andI (Fol.andE1 r hSource) (biimpBackward hqr' (Fol.andE2 p hSource))

@[expose]
noncomputable def allCongr {L : Fol.Language} {Γ : Set (Fol.formula L)}
    {p q : Fol.formula L} (hpq : Fol.lift_formula1 '' Γ ⊢ p ⇔ q) : Γ ⊢ (∀'p) ⇔ (∀'q) :=
  by
  apply Fol.biimpI
  · apply Fol.prf.allI
    have hpq' := Fol.weakening (Set.image_mono (Set.subset_insert (∀'p) Γ)) hpq
    have hAllLift : Fol.lift_formula1 '' insert (∀'p) Γ ⊢ Fol.lift_formula1 (∀'p) :=
      Fol.prf.axm (Set.mem_image_of_mem _ (Set.mem_insert _ _))
    have hAll : Fol.lift_formula1 '' insert (∀'p) Γ ⊢ ∀'(Fol.lift_formula_at p 1 1) := by
      simpa [Fol.lift_formula1, Fol.lift_formula_at] using hAllLift
    have hpRaw := Fol.prf.allE₂ (Fol.lift_formula_at p 1 1) (&0) hAll
    have hp : Fol.lift_formula1 '' insert (∀'p) Γ ⊢ p := by
      simpa only [Fol.lift_subst_formula_cancel] using hpRaw
    exact biimpForward hpq' hp
  · apply Fol.prf.allI
    have hpq' := Fol.weakening (Set.image_mono (Set.subset_insert (∀'q) Γ)) hpq
    have hAllLift : Fol.lift_formula1 '' insert (∀'q) Γ ⊢ Fol.lift_formula1 (∀'q) :=
      Fol.prf.axm (Set.mem_image_of_mem _ (Set.mem_insert _ _))
    have hAll : Fol.lift_formula1 '' insert (∀'q) Γ ⊢ ∀'(Fol.lift_formula_at q 1 1) := by
      simpa [Fol.lift_formula1, Fol.lift_formula_at] using hAllLift
    have hqRaw := Fol.prf.allE₂ (Fol.lift_formula_at q 1 1) (&0) hAll
    have hq : Fol.lift_formula1 '' insert (∀'q) Γ ⊢ q := by
      simpa only [Fol.lift_subst_formula_cancel] using hqRaw
    exact biimpBackward hpq' hq

@[expose]
noncomputable def exCongr {L : Fol.Language} {Γ : Set (Fol.formula L)}
    {p q : Fol.formula L} (hpq : Fol.lift_formula1 '' Γ ⊢ p ⇔ q) : Γ ⊢ (∃'p) ⇔ (∃'q) :=
  by
  apply Fol.biimpI
  · have hSource : insert (∃'p) Γ ⊢ ∃'p := Fol.axm1
    apply Fol.exE hSource
    have hpq' : insert p (Fol.lift_formula1 '' insert (∃'p) Γ) ⊢ p ⇔ q :=
      Fol.weakening
        (by
          intro f hf
          exact Set.mem_insert_of_mem _ (Set.image_mono (Set.subset_insert (∃'p) Γ) hf))
        hpq
    have hq : insert p (Fol.lift_formula1 '' insert (∃'p) Γ) ⊢ q :=
      biimpForward hpq' Fol.axm1
    change insert p (Fol.lift_formula1 '' insert (∃'p) Γ) ⊢ ∃'(Fol.lift_formula_at q 1 1)
    apply Fol.exI (&0)
    simpa only [Fol.lift_subst_formula_cancel] using hq
  · have hSource : insert (∃'q) Γ ⊢ ∃'q := Fol.axm1
    apply Fol.exE hSource
    have hpq' : insert q (Fol.lift_formula1 '' insert (∃'q) Γ) ⊢ p ⇔ q :=
      Fol.weakening
        (by
          intro f hf
          exact Set.mem_insert_of_mem _ (Set.image_mono (Set.subset_insert (∃'q) Γ) hf))
        hpq
    have hp : insert q (Fol.lift_formula1 '' insert (∃'q) Γ) ⊢ p :=
      biimpBackward hpq' Fol.axm1
    change insert q (Fol.lift_formula1 '' insert (∃'q) Γ) ⊢ ∃'(Fol.lift_formula_at p 1 1)
    apply Fol.exI (&0)
    simpa only [Fol.lift_subst_formula_cancel] using hp

@[expose]
def liftedClassMem (P : Fol.formula LNF) : Fol.formula LNF :=
  classMem (cvPred (&0)) (Fol.lift_formula_at P 1 1)

theorem liftedApplyCancel (P : Fol.formula LNF) :
    applyPred (Fol.lift_formula_at P 1 1) (&0) = P := by
  simpa [applyPred] using Fol.lift_subst_formula_cancel P 0

@[expose]
noncomputable def rawDfCleq (P Q : Fol.formula LNF) :
    Theory.fst ⊢ classEq P Q ⇔ ∀'(liftedClassMem P ⇔ liftedClassMem Q) :=
  by
  have hP0 := classMemCv (&0) (Fol.lift_formula_at P 1 1)
  have hQ0 := classMemCv (&0) (Fol.lift_formula_at Q 1 1)
  rw [liftedApplyCancel] at hP0 hQ0
  have hP : Fol.lift_formula1 '' Theory.fst ⊢ liftedClassMem P ⇔ P :=
    by
    rw [Fol.SentTheory.lift_irrel Theory]
    simpa [liftedClassMem] using hP0
  have hQ : Fol.lift_formula1 '' Theory.fst ⊢ liftedClassMem Q ⇔ Q :=
    by
    rw [Fol.SentTheory.lift_irrel Theory]
    simpa [liftedClassMem] using hQ0
  exact biimpSymm (allCongr (biimpCongr hP hQ))

@[expose]
def liftedClassMemBody (P Q : Fol.formula LNF) : Fol.formula LNF :=
  represents (&0) (Fol.lift_formula_at P 1 1) ⊓' liftedClassMem Q

@[expose]
noncomputable def rawDfClel (P Q : Fol.formula LNF) :
    Theory.fst ⊢ classMem P Q ⇔ ∃'(liftedClassMemBody P Q) :=
  by
  have hQ0 := classMemCv (&0) (Fol.lift_formula_at Q 1 1)
  rw [liftedApplyCancel] at hQ0
  have hQ : Fol.lift_formula1 '' Theory.fst ⊢ liftedClassMem Q ⇔ Q :=
    by
    rw [Fol.SentTheory.lift_irrel Theory]
    simpa [liftedClassMem] using hQ0
  have hBody := andCongrRight (represents (&0) (Fol.lift_formula_at P 1 1)) hQ
  have hEx := exCongr hBody
  simpa [classMem, liftedClassMemBody] using biimpSymm hEx


end NFChoice.DirectCertificate.ClassBoundaryRawHandlersDev010
