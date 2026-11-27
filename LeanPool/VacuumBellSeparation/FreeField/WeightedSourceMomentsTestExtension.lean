/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.WeightedSourceMomentsFactorization
public import Mathlib.Analysis.Normed.Operator.Extend

/-!
# Extending actual complex test functionals with weighted bounds

The domain is the concrete complexification of the original local test
space. Its embedding into the completed source space is proved dense.
Every weighted estimate is preserved in the extension, so applying the
bounded Gram partition does not require the partition to preserve tests.
-/

@[expose] public section

namespace VacuumBellSeparation

open Gaussian Gaussian.HilbertComplexification

/-- Complex source test space with underlying type `HilbertComplexification (SourceTestSpace hm
U)`. -/
abbrev ComplexSourceTestSpace {m : ℝ} (hm : 0 < m)
    (U : Set (EuclideanSpace ℝ (Fin 3))) := HilbertComplexification (SourceTestSpace hm U)

variable {m : ℝ} (hm : 0 < m) (U : Set (EuclideanSpace ℝ (Fin 3)))

/-- Linear isometry for the complex source test inclusion, of type `ComplexSourceTestSpace hm U
→ₗᵢ[ℂ] ComplexSourceHilbert hm U`. -/
noncomputable def complexSourceTestInclusion :
    ComplexSourceTestSpace hm U →ₗᵢ[ℂ] ComplexSourceHilbert hm U :=
  complexifyIsometry (UniformSpace.Completion.toComplₗᵢ :
    SourceTestSpace hm U →ₗᵢ[ℝ] SourceHilbert hm U)

@[simp]
theorem complexSourceTestInclusion_mk (u v : SourceTestSpace hm U) :
    complexSourceTestInclusion hm U (mk u v) =
      mk (u : SourceHilbert hm U) (v : SourceHilbert hm U) := rfl

@[simp]
theorem complexSourceTestInclusion_ofReal (u : SourceTestSpace hm U) :
    complexSourceTestInclusion hm U (ofReal u) = ofReal (u : SourceHilbert hm U) := by
  ext <;> simp [complexSourceTestInclusion]

theorem complexSourceTestInclusion_denseRange : DenseRange (complexSourceTestInclusion hm U) := by
  let e : ComplexSourceTestSpace hm U ≃ₜ (SourceTestSpace hm U × SourceTestSpace hm U) :=
    (realEquiv.toHomeomorph).trans (WithLp.homeomorphProd 2 _ _)
  let f : ComplexSourceHilbert hm U ≃ₜ (SourceHilbert hm U × SourceHilbert hm U) :=
    (realEquiv.toHomeomorph).trans (WithLp.homeomorphProd 2 _ _)
  have hd : DenseRange (Prod.map
      ((↑) : SourceTestSpace hm U → SourceHilbert hm U)
      ((↑) : SourceTestSpace hm U → SourceHilbert hm U)) :=
    UniformSpace.Completion.denseRange_coe.prodMap UniformSpace.Completion.denseRange_coe
  have hdf := f.symm.surjective.denseRange.comp hd f.symm.continuous
  have hcoe : Continuous ((↑) : SourceTestSpace hm U → SourceHilbert hm U) :=
    UniformSpace.Completion.continuous_coe (SourceTestSpace hm U)
  have hc : Continuous (f.symm ∘ Prod.map
      ((↑) : SourceTestSpace hm U → SourceHilbert hm U)
      ((↑) : SourceTestSpace hm U → SourceHilbert hm U)) :=
    f.symm.continuous.comp (Continuous.prodMap hcoe hcoe)
  exact hdf.comp e.surjective.denseRange hc

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- Continuous linear map for the extend complex source test functional, of type
`ComplexSourceHilbert hm U →L[ℂ] F`. -/
noncomputable def extendComplexSourceTestFunctional
    (T : ComplexSourceTestSpace hm U →ₗ[ℂ] F) : ComplexSourceHilbert hm U →L[ℂ] F :=
  T.extendOfNorm (complexSourceTestInclusion hm U).toLinearMap

theorem extendComplexSourceTestFunctional_eq
    (T : ComplexSourceTestSpace hm U →ₗ[ℂ] F)
    (A : ComplexSourceHilbert hm U →L[ℂ] ComplexSourceHilbert hm U)
    {C : ℝ} (hC : 0 ≤ C)
    (hT : ∀ z, ‖T z‖ ≤ C * ‖A (complexSourceTestInclusion hm U z)‖)
    (z : ComplexSourceTestSpace hm U) :
    extendComplexSourceTestFunctional hm U T (complexSourceTestInclusion hm U z) = T z := by
  apply LinearMap.extendOfNorm_eq (complexSourceTestInclusion_denseRange hm U)
  refine ⟨C * ‖A‖, fun z => ?_⟩
  exact (hT z).trans ((mul_le_mul_of_nonneg_left (A.le_opNorm _) hC).trans_eq
    (mul_assoc _ _ _).symm)

theorem extendComplexSourceTestFunctional_weight_bound
    (T : ComplexSourceTestSpace hm U →ₗ[ℂ] F)
    (A : ComplexSourceHilbert hm U →L[ℂ] ComplexSourceHilbert hm U)
    {C : ℝ} (hC : 0 ≤ C)
    (hT : ∀ z, ‖T z‖ ≤ C * ‖A (complexSourceTestInclusion hm U z)‖) :
    ∀ z, ‖extendComplexSourceTestFunctional hm U T z‖ ≤ C * ‖A z‖ := by
  intro z
  refine (complexSourceTestInclusion_denseRange hm U).induction_on
    (p := fun z => ‖extendComplexSourceTestFunctional hm U T z‖ ≤ C * ‖A z‖) z
    (isClosed_le (by fun_prop) (by fun_prop)) ?_
  intro w
  rw [extendComplexSourceTestFunctional_eq hm U T A hC hT]
  exact hT w

/-- The literal test-domain estimates suffice for a weighted moment vector.
Neither a completed functional nor a reserve inverse is supplied as input. -/
theorem exists_sourceReserve_riesz_of_test_modular_weights
    (hU : Bornology.IsBounded U) (T : ComplexSourceTestSpace hm U →ₗ[ℂ] ℂ)
    {b C₁ C₂ : ℝ} (hb : 1 / 2 ≤ b) (hb1 : b ≤ 1) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (h₁ : ∀ z, ‖T z‖ ≤ C₁ *
      ‖sourceModularWeight hm U ((1 - b) / 2) (complexSourceTestInclusion hm U z)‖)
    (h₂ : ∀ z, ‖T z‖ ≤ C₂ *
      ‖sourceModularWeight hm U (b / 2) (complexSourceTestInclusion hm U z)‖) :
    ∃ v : ComplexSourceHilbert hm U, ‖v‖ ≤ C₁ + C₂ ∧
      ∀ z, inner ℂ (complexSourceTestInclusion hm U z) ((sourceReserve hm U ^ b) v) =
        star (T z) := by
  let L := extendComplexSourceTestFunctional hm U T
  obtain ⟨v, hv, _, heq⟩ := exists_sourceReserve_riesz_of_two_modular_weights hm U hU
    L.toLinearMap hb hb1 hC₁ hC₂
    (extendComplexSourceTestFunctional_weight_bound hm U T _ hC₁ h₁)
    (extendComplexSourceTestFunctional_weight_bound hm U T _ hC₂ h₂)
  refine ⟨v, hv, fun z => ?_⟩
  have hext := extendComplexSourceTestFunctional_eq hm U T
    (sourceModularWeight hm U ((1 - b) / 2)) hC₁ h₁ z
  exact (heq (complexSourceTestInclusion hm U z)).trans
    (congrArg (starRingEnd ℂ) hext)

end VacuumBellSeparation
