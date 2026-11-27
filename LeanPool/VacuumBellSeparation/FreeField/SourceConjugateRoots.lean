/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.SourceReserve
public import LeanPool.VacuumBellSeparation.FreeField.SourcePolarUnitary
public import LeanPool.VacuumBellSeparation.FreeField.BoundedRatioOperator
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute

/-!
# Conjugate Gram square roots and their actual selfadjoint ratio

Conjugation preserves positivity by the actual inner-product identity, so
uniqueness of the positive square root proves C sqrt(G) C = sqrt(Gbar).
The unbounded ratio on range sqrt(G) is constructed as a LinearPMap and
proved selfadjoint from the exact identity G+Gbar=2I.
-/

@[expose] public section

namespace VacuumBellSeparation

open ContinuousLinearMap Gaussian Gaussian.HilbertComplexification
open scoped InnerProductSpace ComplexConjugate

section Conjugation
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- The literal source conjugation is antiunitary for the constructed complex inner product. -/
theorem sourceConjugation_inner (z w : HilbertComplexification E) :
    inner ℂ (conjugation z) (conjugation w) = conj (inner ℂ z w) := by
  apply Complex.ext <;>
    simp [HilbertComplexification.inner_eq]; ring

omit [CompleteSpace E] in
theorem sourceConjugateOperator_mul
    (A B : HilbertComplexification E →L[ℂ] HilbertComplexification E) :
    conjugateOperator (A * B) = conjugateOperator A * conjugateOperator B := by
  apply ContinuousLinearMap.ext
  intro z
  simp only [conjugateOperator_apply, mul_apply_eq_comp, conjugation_conjugation]

omit [CompleteSpace E] in
theorem sourceConjugateOperator_isPositive
    {A : HilbertComplexification E →L[ℂ] HilbertComplexification E}
    (hA : A.IsPositive) : (conjugateOperator A).IsPositive := by
  refine ⟨?_, ?_⟩
  · intro x y
    change inner ℂ (conjugation (A (conjugation x))) y =
      inner ℂ x (conjugation (A (conjugation y)))
    calc
      _ = conj (inner ℂ (A (conjugation x)) (conjugation y)) := by
        simpa only [conjugation_conjugation] using
          sourceConjugation_inner (A (conjugation x)) (conjugation y)
      _ = conj (inner ℂ (conjugation x) (A (conjugation y))) :=
        congrArg conj (hA.isSymmetric (conjugation x) (conjugation y))
      _ = _ := by
        simpa only [conjugation_conjugation] using
          (sourceConjugation_inner (conjugation x) (A (conjugation y))).symm
  · intro x
    have hi := sourceConjugation_inner (A (conjugation x)) (conjugation x)
    have hir : (inner ℂ (conjugation (A (conjugation x))) x).re =
        (inner ℂ (A (conjugation x)) (conjugation x)).re := by
      simpa only [conjugation_conjugation, Complex.conj_re] using congrArg Complex.re hi
    change 0 ≤ (inner ℂ (conjugation (A (conjugation x))) x).re
    rw [hir]
    exact hA.re_inner_nonneg_left (conjugation x)

theorem sourceConjugateOperator_sqrt
    (A : HilbertComplexification E →L[ℂ] HilbertComplexification E) (hA : 0 ≤ A) :
    conjugateOperator (CFC.sqrt A) = CFC.sqrt (conjugateOperator A) := by
  symm
  apply CFC.sqrt_unique
  · rw [← sourceConjugateOperator_mul, CFC.sqrt_mul_sqrt_self A hA]
  · exact nonneg_iff_isPositive.mpr
      (sourceConjugateOperator_isPositive (nonneg_iff_isPositive.mp (CFC.sqrt_nonneg A)))
end Conjugation

variable {m : ℝ} (hm : 0 < m) (U : Set (EuclideanSpace ℝ (Fin 3)))

/-- Continuous linear map for the source gram root, of type `ComplexSourceHilbert hm U →L[ℂ]
ComplexSourceHilbert hm U`. -/
noncomputable def sourceGramRoot :
    ComplexSourceHilbert hm U →L[ℂ] ComplexSourceHilbert hm U := CFC.sqrt (sourceGram hm U)

/-- Continuous linear map for the conjugate source gram root, of type `ComplexSourceHilbert hm U
→L[ℂ] ComplexSourceHilbert hm U`. -/
noncomputable def conjugateSourceGramRoot :
    ComplexSourceHilbert hm U →L[ℂ] ComplexSourceHilbert hm U :=
  CFC.sqrt (conjugateSourceGram hm U)

theorem conjugate_sourceGramRoot :
    conjugateOperator (sourceGramRoot hm U) = conjugateSourceGramRoot hm U :=
  sourceConjugateOperator_sqrt _ (nonneg_iff_isPositive.mpr (sourceGram_isPositive hm U))

theorem sourceGramRoot_conjugation (z : ComplexSourceHilbert hm U) :
    sourceGramRoot hm U (conjugation z) = conjugation (conjugateSourceGramRoot hm U z) := by
  have hh := congrArg (fun A : ComplexSourceHilbert hm U →L[ℂ] ComplexSourceHilbert hm U =>
    conjugation (A z)) (conjugate_sourceGramRoot hm U)
  simpa only [conjugateOperator_apply, conjugation_conjugation] using hh

theorem sourceGramRoot_commute_conjugateSourceGramRoot :
    Commute (sourceGramRoot hm U) (conjugateSourceGramRoot hm U) := by
  exact (((sourceGram_commute_conjugateSourceGram hm U).cfcₙ_nnreal NNReal.sqrt).symm.cfcₙ_nnreal
    NNReal.sqrt).symm

theorem sourceGramRoot_sq_add_conjugateSourceGramRoot_sq :
    sourceGramRoot hm U * sourceGramRoot hm U +
      conjugateSourceGramRoot hm U * conjugateSourceGramRoot hm U = 2 := by
  rw [sourceGramRoot, conjugateSourceGramRoot,
    CFC.sqrt_mul_sqrt_self _ (nonneg_iff_isPositive.mpr (sourceGram_isPositive hm U)),
    CFC.sqrt_mul_sqrt_self _ (conjugateSourceGram_nonneg hm U), conjugateSourceGram_eq_two_sub]
  noncomm_ring

theorem sourceGramRoot_injective (hU : Bornology.IsBounded U) :
    Function.Injective (sourceGramRoot hm U) :=
  polarGramRoot_injective (complexSourceMap hm U) (complexSourceMap_injective hm U hU)

theorem sourceGramRoot_denseRange (hU : Bornology.IsBounded U) :
    DenseRange (sourceGramRoot hm U) :=
  polarGramRoot_denseRange (complexSourceMap hm U) (complexSourceMap_injective hm U hU)

/-- The actual positive-square-root modular ratio in source polar coordinates. -/
noncomputable def sourceModularRoot (hU : Bornology.IsBounded U) :
    ComplexSourceHilbert hm U →ₗ.[ℂ] ComplexSourceHilbert hm U :=
  boundedRatio (sourceGramRoot hm U) (conjugateSourceGramRoot hm U)
    (sourceGramRoot_injective hm U hU)

@[simp] theorem sourceModularRoot_apply (hU : Bornology.IsBounded U)
    (z : ComplexSourceHilbert hm U) :
    sourceModularRoot hm U hU ⟨sourceGramRoot hm U z, ⟨z, rfl⟩⟩ =
      conjugateSourceGramRoot hm U z :=
  boundedRatio_apply_range _ _ _ z

theorem sourceModularRoot_isSelfAdjoint (hU : Bornology.IsBounded U) :
    IsSelfAdjoint (sourceModularRoot hm U hU) :=
  boundedRatio_isSelfAdjoint _ _ _ (sourceGramRoot_denseRange hm U hU)
    (CFC.sqrt_nonneg _).isSelfAdjoint (CFC.sqrt_nonneg _).isSelfAdjoint
    (sourceGramRoot_commute_conjugateSourceGramRoot hm U)
    (sourceGramRoot_sq_add_conjugateSourceGramRoot_sq hm U)

/-- Positivity on the actual unbounded domain. -/
theorem sourceModularRoot_inner_nonneg (hU : Bornology.IsBounded U)
    (x : (sourceModularRoot hm U hU).domain) :
    0 ≤ (inner ℂ (x : ComplexSourceHilbert hm U) (sourceModularRoot hm U hU x)).re := by
  obtain ⟨z, hz, hBz⟩ := boundedRatio_representation (sourceGramRoot hm U)
    (conjugateSourceGramRoot hm U) (sourceGramRoot_injective hm U hU) x
  have hroot : conjugateSourceGramRoot hm U z = sourceModularRoot hm U hU x := hBz
  rw [← hz, ← hroot]
  have hp : 0 ≤ sourceGramRoot hm U * conjugateSourceGramRoot hm U :=
    Commute.mul_nonneg (CFC.sqrt_nonneg _) (CFC.sqrt_nonneg _)
      (sourceGramRoot_commute_conjugateSourceGramRoot hm U)
  have hi := (CFC.sqrt_nonneg (sourceGram hm U)).isSelfAdjoint.isSymmetric
    z (conjugateSourceGramRoot hm U z)
  change inner ℂ (sourceGramRoot hm U z) (conjugateSourceGramRoot hm U z) =
    inner ℂ z (sourceGramRoot hm U (conjugateSourceGramRoot hm U z)) at hi
  rw [hi]
  exact (nonneg_iff_isPositive.mp hp).re_inner_nonneg_right z

end VacuumBellSeparation
