/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.WeightedSourceEnergyChoice

/-!
# Actual entire growth with the manuscript dimensional prefactors

The common constant depends only on b. Both literal entire Fourier
components are controlled by the original reserve-power norm, with the
correct T/(1+mT) and T²/(1+mT)² factors.
-/

@[expose] public section

namespace VacuumBellSeparation

theorem weightedSource_entire_growth {b : ℝ} (hb : 1 / 2 ≤ b) (hb1 : b < 1) :
    ∃ M : ℝ, 0 < M ∧
      ∀ (m : ℝ) (hm : 0 < m) (T : ℝ) (_ : 0 < T)
        (U : Set (EuclideanSpace ℝ (Fin 3))), U ⊆ Metric.ball 0 T →
        ∀ (z : EuclideanSpace ℂ (Fin 3)) (x : ComplexSourceTestSpace hm U),
          ‖complexSourceFieldFourier hm U (WithLp.ofLp z) x‖ ≤
            M * T / (1 + m * T) * Real.exp (sourceMomentLambda b * m * T) *
              Real.exp (sourceMomentLambda b * T * ‖z‖) *
                ‖(sourceReserve hm U ^ b) (complexSourceTestInclusion hm U x)‖ ∧
          ‖complexSourceMomentumFourier hm U (WithLp.ofLp z) x‖ ≤
            M * T ^ 2 / (1 + m * T) ^ 2 * Real.exp (sourceMomentLambda b * m * T) *
              Real.exp (sourceMomentLambda b * T * ‖z‖) *
                ‖(sourceReserve hm U ^ b) (complexSourceTestInclusion hm U x)‖ := by
  obtain ⟨C, hC, hbound⟩ := weightedSource_fourier_bounds hb hb1
  have hΛ := sourceMomentLambda_pos hb hb1
  have hΛone := one_le_sourceMomentLambda hb hb1
  refine ⟨C * sourceMomentLambda b ^ 2 * Real.exp 1, by positivity, ?_⟩
  intro m hm T hT U hU z x
  let E := sourceMomentEnergy m T b z
  have hE : 0 < E := sourceMomentEnergy_pos hb hb1 hm hT z
  have hden : 0 < 1 + m * T := by positivity
  obtain ⟨hf, hg⟩ := hbound m hm T hT U hU E z
    (sourceMomentEnergy_lower (m := m) hb hb1 hT z) x
  have hi : 1 / E ≤ sourceMomentLambda b * T / (1 + m * T) :=
    sourceMomentEnergy_inv_le hb hb1 hm hT z
  have he : Real.exp (sourceMomentLambda b * T * E) =
      Real.exp (sourceMomentLambda b * m * T) * Real.exp 1 *
        Real.exp (sourceMomentLambda b * T * ‖z‖) := by
    rw [sourceMomentEnergy_exponent hb hb1 hT z, Real.exp_add, Real.exp_add]
  have hcf : C / E ≤ C * (sourceMomentLambda b * T / (1 + m * T)) := by
    simpa only [div_eq_mul_inv, one_mul] using mul_le_mul_of_nonneg_left hi hC.le
  have hcg : C / E ^ 2 ≤ C * (sourceMomentLambda b * T / (1 + m * T)) ^ 2 := by
    have hs := pow_le_pow_left₀ (by positivity : 0 ≤ 1 / E) hi 2
    simpa only [div_pow, one_pow, div_eq_mul_inv, one_mul, inv_pow] using
      mul_le_mul_of_nonneg_left hs hC.le
  have hconst : C * sourceMomentLambda b * Real.exp 1 ≤
      C * sourceMomentLambda b ^ 2 * Real.exp 1 := by
    apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
    apply mul_le_mul_of_nonneg_left _ hC.le
    nlinarith
  constructor
  · calc
      _ ≤ (C / E * Real.exp (sourceMomentLambda b * T * E)) *
          ‖(sourceReserve hm U ^ b) (complexSourceTestInclusion hm U x)‖ := hf
      _ ≤ (C * (sourceMomentLambda b * T / (1 + m * T)) *
          Real.exp (sourceMomentLambda b * T * E)) *
            ‖(sourceReserve hm U ^ b) (complexSourceTestInclusion hm U x)‖ := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hcf (Real.exp_nonneg _)) (norm_nonneg _)
      _ = (C * sourceMomentLambda b * Real.exp 1) * T / (1 + m * T) *
          Real.exp (sourceMomentLambda b * m * T) * Real.exp (sourceMomentLambda b * T * ‖z‖) *
            ‖(sourceReserve hm U ^ b) (complexSourceTestInclusion hm U x)‖ := by
        rw [he]
        ring
      _ ≤ _ := by gcongr
  · calc
      _ ≤ (C / E ^ 2 * Real.exp (sourceMomentLambda b * T * E)) *
          ‖(sourceReserve hm U ^ b) (complexSourceTestInclusion hm U x)‖ := hg
      _ ≤ (C * (sourceMomentLambda b * T / (1 + m * T)) ^ 2 *
          Real.exp (sourceMomentLambda b * T * E)) *
            ‖(sourceReserve hm U ^ b) (complexSourceTestInclusion hm U x)‖ := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hcg (Real.exp_nonneg _)) (norm_nonneg _)
      _ = _ := by
        rw [he]
        simp only [div_eq_mul_inv, ← inv_pow]
        ring

end VacuumBellSeparation
