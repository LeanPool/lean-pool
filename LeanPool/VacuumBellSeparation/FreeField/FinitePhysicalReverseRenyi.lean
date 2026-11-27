/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.FinitePhysicalReverseNormalization
public import LeanPool.VacuumBellSeparation.Gaussian.GaussianRenyiConsequences

/-!
# The actual reverse Gaussian Rényi envelope

The manuscript's fixed reverse order has compression exponent exactly aRev.
The low-exponent constant and smallness threshold are retained literally.
The quantity is proved positive and finite before its logarithm is used.
-/

@[expose] public section

namespace VacuumBellSeparation

open Gaussian
open scoped ENNReal Matrix.Norms.L2Operator

theorem gaussianRenyiTau_rMinus : gaussianRenyiTau rMinus = aRev := by
  norm_num [gaussianRenyiTau, rMinus, aRev, theta, Lambda0]

theorem reverseOrder_max_inverse : max 2 (gaussianRenyiTau rMinus)⁻¹ = aRev⁻¹ := by
  rw [gaussianRenyiTau_rMinus]
  norm_num [aRev, theta, Lambda0]

theorem reverseOrder_smallness : (4 * max 2 (gaussianRenyiTau rMinus)⁻¹)⁻¹ = aRev / 4 := by
  rw [reverseOrder_max_inverse]
  norm_num [aRev, theta, Lambda0]

/-- This applies to either ordered pair of actual faithful Gaussian densities;
the physical reverse application puts the product density first. -/
theorem finite_reverse_order_gaussian_renyi_bound {d : ℕ}
    {ρ σ : MultiModeOscillatorSpace d →L[ℂ] MultiModeOscillatorSpace d}
    {Vρ Vσ : Matrix (Fin d × Fin 2) (Fin d × Fin 2) ℝ}
    (hρ : IsFaithfulDensity ρ) (hσ : IsFaithfulDensity σ)
    (hVρ : Vρ.IsHermitian) (hVσ : Vσ.IsHermitian)
    (hGρ : HasGaussianPhysicalCharacteristic ρ Vρ)
    (hGσ : HasGaussianPhysicalCharacteristic σ Vσ)
    {ε : ℝ} (hε : ε ≤ aRev / 4)
    (hop : ‖intrinsicGaussianRelativePerturbation ρ σ aRev‖ ≤ ε)
    (htrace : matrixTraceNorm (intrinsicGaussianRelativePerturbation ρ σ aRev) ≤ ε) :
    0 < sandwichedRenyiQuantity ρ σ rMinus ∧
      sandwichedRenyiQuantity ρ σ rMinus < ∞ ∧
      Real.log (sandwichedRenyiQuantity ρ σ rMinus).toReal ≤
        2 * rMinus * aRev⁻¹ * ε ∧
      sandwichedRenyiQuantity ρ σ rMinus ≤
        ENNReal.ofReal (Real.exp (2 * rMinus * aRev⁻¹ * ε)) := by
  have hsmall : ‖intrinsicGaussianRelativePerturbation ρ σ (gaussianRenyiTau rMinus)‖ ≤
      (4 * max 2 (gaussianRenyiTau rMinus)⁻¹)⁻¹ := by
    rw [reverseOrder_smallness, gaussianRenyiTau_rMinus]
    exact hop.trans hε
  obtain ⟨hQ0, hQt, hlog⟩ := faithful_gaussian_renyi_bound hρ hσ hVρ hVσ hGρ hGσ
    one_lt_rMinus_lt_two.1 hsmall
  rw [reverseOrder_max_inverse, gaussianRenyiTau_rMinus] at hlog
  have hlog' := hlog.trans (mul_le_mul_of_nonneg_left htrace
    (show 0 ≤ 2 * rMinus * aRev⁻¹ from
      mul_nonneg (mul_nonneg (by norm_num) (by linarith [one_lt_rMinus_lt_two.1]))
        (inv_nonneg.mpr aRev_pos_le.1.le)))
  refine ⟨hQ0, hQt, hlog', ?_⟩
  have he := ENNReal.ofReal_le_ofReal
    ((Real.log_le_iff_le_exp (ENNReal.toReal_pos hQ0.ne' hQt.ne)).mp hlog')
  simpa only [ENNReal.ofReal_toReal hQt.ne] using he

end VacuumBellSeparation
