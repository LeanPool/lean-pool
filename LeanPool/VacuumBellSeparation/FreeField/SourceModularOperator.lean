/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.SourceConjugateRoots
public import LeanPool.VacuumBellSeparation.FreeField.BoundedRatioSquare
public import LeanPool.VacuumBellSeparation.FreeField.BoundedRatioSum

/-!
# The source modular ratio as an actual positive selfadjoint operator

The domain is range G, and the action is Gz ↦ Gbar z. It equals the
maximal square of the previously constructed positive selfadjoint root.
Transport to the physical antlinear Tomita adjoint product is separate.
-/

@[expose] public section

namespace VacuumBellSeparation

open ContinuousLinearMap
open scoped InnerProductSpace

variable {m : ℝ} (hm : 0 < m) (U : Set (EuclideanSpace ℝ (Fin 3)))
variable (hU : Bornology.IsBounded U)

/-- Linear map for the source modular operator, of type `ComplexSourceHilbert hm U →ₗ.[ℂ]
ComplexSourceHilbert hm U`. -/
noncomputable def sourceModularOperator :
    ComplexSourceHilbert hm U →ₗ.[ℂ] ComplexSourceHilbert hm U :=
  boundedRatio (sourceGram hm U) (conjugateSourceGram hm U) (sourceGram_injective hm U hU)

@[simp] theorem sourceModularOperator_apply (z : ComplexSourceHilbert hm U) :
    sourceModularOperator hm U hU ⟨sourceGram hm U z, ⟨z, rfl⟩⟩ = conjugateSourceGram hm U z :=
  boundedRatio_apply_range _ _ _ z

theorem sourceModularRoot_square :
    partialComp (sourceModularRoot hm U hU) (sourceModularRoot hm U hU) =
      sourceModularOperator hm U hU := by
  rw [sourceModularRoot, boundedRatio_square_eq _ _ _
    (sourceGramRoot_commute_conjugateSourceGramRoot hm U)
    (sourceGramRoot_sq_add_conjugateSourceGramRoot_sq hm U)]
  have hA : sourceGramRoot hm U * sourceGramRoot hm U = sourceGram hm U :=
    CFC.sqrt_mul_sqrt_self _ (nonneg_iff_isPositive.mpr (sourceGram_isPositive hm U))
  have hB : conjugateSourceGramRoot hm U * conjugateSourceGramRoot hm U =
      conjugateSourceGram hm U := CFC.sqrt_mul_sqrt_self _ (conjugateSourceGram_nonneg hm U)
  simp only [hA, hB, sourceModularOperator]

include hU in
theorem sourceGram_denseRange : DenseRange (sourceGram hm U) := by
  have hker : (sourceGram hm U).ker = ⊥ := LinearMap.ker_eq_bot.mpr (sourceGram_injective hm U hU)
  have horth : (sourceGram hm U).rangeᗮ = ⊥ := by
    rw [(sourceGram hm U).orthogonal_range,
      (sourceGram_isPositive hm U).isSelfAdjoint.adjoint_eq, hker]
  have hclose := (sourceGram hm U).range.topologicalClosure_eq_top_iff.mpr horth
  exact Submodule.dense_iff_topologicalClosure_eq_top.mpr hclose

theorem sourceModularOperator_isSelfAdjoint : IsSelfAdjoint (sourceModularOperator hm U hU) := by
  apply boundedRatio_isSelfAdjoint_of_sum_eq_two _ _ _ (sourceGram_denseRange hm U hU)
    (sourceGram_isPositive hm U).isSelfAdjoint (conjugateSourceGram_nonneg hm U).isSelfAdjoint
    (sourceGram_commute_conjugateSourceGram hm U)
  rw [conjugateSourceGram_eq_two_sub]
  noncomm_ring

theorem sourceModularOperator_inner_nonneg (x : (sourceModularOperator hm U hU).domain) :
    0 ≤ (inner ℂ (x : ComplexSourceHilbert hm U) (sourceModularOperator hm U hU x)).re := by
  obtain ⟨z, hz, hBz⟩ := boundedRatio_representation (sourceGram hm U)
    (conjugateSourceGram hm U) (sourceGram_injective hm U hU) x
  change conjugateSourceGram hm U z = sourceModularOperator hm U hU x at hBz
  rw [← hz, ← hBz]
  have hsym : inner ℂ (sourceGram hm U z) (conjugateSourceGram hm U z) =
      inner ℂ z (sourceGram hm U (conjugateSourceGram hm U z)) :=
    (sourceGram_isPositive hm U).isSelfAdjoint.isSymmetric z (conjugateSourceGram hm U z)
  rw [hsym]
  exact (nonneg_iff_isPositive.mp (sourceGram_mul_conjugateSourceGram_nonneg hm
    U)).re_inner_nonneg_right z

end VacuumBellSeparation
