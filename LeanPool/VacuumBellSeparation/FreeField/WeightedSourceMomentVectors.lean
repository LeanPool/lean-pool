/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.WeightedSourceMomentBounds
public import LeanPool.VacuumBellSeparation.FreeField.SpatialRealMomentSeries

/-!
# Genuine weighted moment vectors in the completed original source space

The actual test moments extend by density. The true dense-range reserve
factorization and Riesz theorem construct the vectors with the estimates
of Lemma 5.4. No whole-space bounded inverse of the reserve is used.
-/

@[expose] public section

namespace VacuumBellSeparation

open Gaussian Gaussian.HilbertComplexification
open scoped BigOperators ComplexConjugate

variable {m : ℝ} (hm : 0 < m) (U : Set (EuclideanSpace ℝ (Fin 3)))

theorem exists_sourceReserve_riesz_of_test_bound
    (hU : Bornology.IsBounded U) (L : ComplexSourceTestSpace hm U →ₗ[ℂ] ℂ)
    {b C : ℝ} (hb : 0 ≤ b) (hb1 : b ≤ 1) (hC : 0 ≤ C)
    (hL : ∀ x, ‖L x‖ ≤ C * ‖(sourceReserve hm U ^ b) (complexSourceTestInclusion hm U x)‖) :
    ∃ v : ComplexSourceHilbert hm U, ‖v‖ ≤ C ∧
      ∀ x, inner ℂ (complexSourceTestInclusion hm U x) ((sourceReserve hm U ^ b) v) =
        conj (L x) := by
  let T := extendComplexSourceTestFunctional hm U L
  obtain ⟨v, hv, _, heq⟩ := exists_sourceReserve_riesz_of_bound hm U hU
    T.toLinearMap hb hb1 hC
    (extendComplexSourceTestFunctional_weight_bound hm U L _ hC hL)
  refine ⟨v, hv, fun x => ?_⟩
  rw [heq]
  congr 1
  exact extendComplexSourceTestFunctional_eq hm U L _ hC hL x

@[simp]
theorem complexSourceFieldMoment_ofReal (α : Fin 3 → ℕ) (x : SourceTestSpace hm U) :
    complexSourceFieldMoment hm U α (ofReal x) = (spatialRealTestMoment x.1.1 α : ℂ) := by
  rw [complexSourceFieldMoment, complexifyFunctional_ofReal]
  change spatialTestMoment x.1.1 α = _
  exact spatialTestMoment_eq_ofReal x.1.1 α

@[simp]
theorem complexSourceMomentumMoment_ofReal (α : Fin 3 → ℕ) (x : SourceTestSpace hm U) :
    complexSourceMomentumMoment hm U α (ofReal x) = (spatialRealTestMoment x.1.2 α : ℂ) := by
  rw [complexSourceMomentumMoment, complexifyFunctional_ofReal]
  change spatialTestMoment x.1.2 α = _
  exact spatialTestMoment_eq_ofReal x.1.2 α

theorem exists_weightedSource_moment_vectors {b : ℝ} (hb : 1 / 2 ≤ b) (hb1 : b < 1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (m : ℝ) (hm : 0 < m) (T : ℝ) (_ : 0 < T)
        (U : Set (EuclideanSpace ℝ (Fin 3))), U ⊆ Metric.ball 0 T →
        ∀ α : Fin 3 → ℕ,
          ∃ u v : ComplexSourceHilbert hm U,
            ‖u‖ ≤ C * T / (1 + m * T) * Real.exp (sourceMomentLambda b * m * T) *
              (sourceMomentBase b * T) ^ (∑ j, α j) ∧
            ‖v‖ ≤ C * T ^ 2 / (1 + m * T) ^ 2 * Real.exp (sourceMomentLambda b * m * T) *
              (sourceMomentBase b * T) ^ (∑ j, α j) ∧
            (∀ x : SourceTestSpace hm U,
              inner ℂ (ofReal (x : SourceHilbert hm U)) ((sourceReserve hm U ^ b) u) =
                (spatialRealTestMoment x.1.1 α : ℂ)) ∧
            (∀ x : SourceTestSpace hm U,
              inner ℂ (ofReal (x : SourceHilbert hm U)) ((sourceReserve hm U ^ b) v) =
                (spatialRealTestMoment x.1.2 α : ℂ)) := by
  obtain ⟨C, hC, hbound⟩ := weightedSource_moment_bounds hb hb1
  refine ⟨C, hC, ?_⟩
  intro m hm T hT U hU α
  have hUb : Bornology.IsBounded U := Metric.isBounded_ball.subset hU
  have hb0 : 0 ≤ b := by linarith
  have hbase : 0 ≤ sourceMomentBase b := by
    unfold sourceMomentBase
    exact mul_nonneg (by norm_num) (sourceMomentLambda_pos hb hb1).le
  obtain ⟨u, hu, hueq⟩ := exists_sourceReserve_riesz_of_test_bound hm U hUb
    (C := C * T / (1 + m * T) * Real.exp (sourceMomentLambda b * m * T) *
      (sourceMomentBase b * T) ^ (∑ j, α j))
    (complexSourceFieldMoment hm U α) hb0 hb1.le (by positivity)
    (fun x => (hbound m hm T hT U hU α x).1)
  obtain ⟨v, hv, hveq⟩ := exists_sourceReserve_riesz_of_test_bound hm U hUb
    (C := C * T ^ 2 / (1 + m * T) ^ 2 * Real.exp (sourceMomentLambda b * m * T) *
      (sourceMomentBase b * T) ^ (∑ j, α j))
    (complexSourceMomentumMoment hm U α) hb0 hb1.le (by positivity)
    (fun x => (hbound m hm T hT U hU α x).2)
  refine ⟨u, v, hu, hv, ?_, ?_⟩
  · intro x
    simpa only [complexSourceTestInclusion_ofReal, complexSourceFieldMoment_ofReal,
      Complex.conj_ofReal] using hueq (ofReal x)
  · intro x
    simpa only [complexSourceTestInclusion_ofReal, complexSourceMomentumMoment_ofReal,
      Complex.conj_ofReal] using hveq (ofReal x)

end VacuumBellSeparation
