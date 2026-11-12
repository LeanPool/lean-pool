/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryScopedPhase
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryVectorAction
public import LeanPool.ApollonianSuperharmonic.ProperBandCurvatureStructure
public import LeanPool.ApollonianSuperharmonic.VectorNonvanishing

-- [TABLET NODE: BandPackingSymmetryScopedPhaseUnique]

/-!
# BandPackingSymmetryScopedPhaseUnique

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem BandPackingSymmetryScopedPhaseUnique
    (g : BandPackingSymmetry) (q : Fin 4 → CircleCoordinates)
    (hq : ProperBandQuadruple q) (negative₁ negative₂ : Bool)
    (h₁ : BandPackingSymmetryScopedPhase g q negative₁)
    (h₂ : BandPackingSymmetryScopedPhase g q negative₂) :
    negative₁ = negative₂ := by
-- BODY
  have preserves : ∀ (a : BandPackingSymmetry) (v : GaussianInt),
      v ≠ 0 → BandPackingSymmetryVectorAction a v ≠ 0 := by
    intro a
    induction a with
    | identity =>
        intro v hv
        exact hv
    | negate =>
        intro v hv hz
        apply hv
        cases v
        rw [Zsqrtd.ext_iff] at hz
        simp? [BandPackingSymmetryVectorAction, GaussianQuarterTurn] at hz
        rcases hz with ⟨hre, him⟩
        ext <;> simp_all [Zsqrtd.re_zero, Zsqrtd.im_zero]
    | conjugate =>
        intro v hv hz
        apply hv
        cases v
        rw [Zsqrtd.ext_iff] at hz
        simp? [BandPackingSymmetryVectorAction, GaussianReflection] at hz
        rcases hz with ⟨hre, him⟩
        ext <;> simp_all [Zsqrtd.re_zero, Zsqrtd.im_zero]
    | shift w =>
        intro v hv
        exact hv
    | comp a b ia ib =>
        intro v hv hz
        exact ia _ (ib v hv) hz
  have curvature := ProperBandCurvatureStructure q hq
  have vector_nonzero : BandVectors.1 (q ((0 : Fin 3).succ : Fin 4)) (q 0) ≠ 0 := by
    apply VectorNonvanishing q hq.1 ((0 : Fin 3).succ : Fin 4) 0
    · decide
    · exact Or.inr curvature.1
  have transformed_nonzero :
      BandPackingSymmetryVectorAction g
        (BandVectors.1 (q ((0 : Fin 3).succ : Fin 4)) (q 0)) ≠ 0 :=
    preserves g _ vector_nonzero
  dsimp [BandPackingSymmetryScopedPhase] at h₁ h₂
  cases negative₁ <;> cases negative₂
  · rfl
  · have equal := (h₁ 0).1.symm.trans (h₂ 0).1
    simp? at equal
    have opposite :
        BandPackingSymmetryVectorAction g
            (BandVectors.1 (q ((0 : Fin 3).succ : Fin 4)) (q 0)) =
          -BandPackingSymmetryVectorAction g
            (BandVectors.1 (q ((0 : Fin 3).succ : Fin 4)) (q 0)) := by
      exact equal
    apply False.elim
    apply transformed_nonzero
    rw [Zsqrtd.ext_iff] at opposite
    rcases opposite with ⟨hre, him⟩
    simp only [Zsqrtd.re_neg, Zsqrtd.im_neg] at hre him
    apply Zsqrtd.ext <;> simp only [Zsqrtd.re_zero, Zsqrtd.im_zero] <;> omega
  · have equal := (h₁ 0).1.symm.trans (h₂ 0).1
    simp at equal
    have opposite :
        BandPackingSymmetryVectorAction g
            (BandVectors.1 (q ((0 : Fin 3).succ : Fin 4)) (q 0)) =
          -BandPackingSymmetryVectorAction g
            (BandVectors.1 (q ((0 : Fin 3).succ : Fin 4)) (q 0)) := by
      exact equal.symm
    apply False.elim
    apply transformed_nonzero
    rw [Zsqrtd.ext_iff] at opposite
    rcases opposite with ⟨hre, him⟩
    simp only [Zsqrtd.re_neg, Zsqrtd.im_neg] at hre him
    apply Zsqrtd.ext <;> simp only [Zsqrtd.re_zero, Zsqrtd.im_zero] <;> omega
  · rfl

end ApollonianSuperharmonic

end
