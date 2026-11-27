/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.FiniteForwardSpatialBound
public import LeanPool.VacuumBellSeparation.Gaussian.GaussianRenyiConsequences

/-!
# The actual forward high-order Gaussian Rényi envelope

For r=n+2 the compression exponent is exactly (r-1)/r and k_r=2.
The genuine finite quantity, its logarithm, and its exponential bound
follow from the proved intrinsic Gaussian estimate.
-/

@[expose] public section

namespace VacuumBellSeparation

open Gaussian
open scoped ENNReal Matrix.Norms.L2Operator

theorem gaussianRenyiTau_sourceHighOrder (n : ℕ) :
    gaussianRenyiTau ((n + 2 : ℕ) : ℝ) = sourceHighExponent n := by
  unfold gaussianRenyiTau sourceHighExponent
  push_cast
  congr 1
  ring

theorem sourceHighOrder_max_inverse (n : ℕ) :
    max 2 (gaussianRenyiTau ((n + 2 : ℕ) : ℝ))⁻¹ = 2 := by
  rw [gaussianRenyiTau_sourceHighOrder]
  have hb := sourceHighExponent_half_le n
  have hb0 : 0 < sourceHighExponent n := by linarith
  apply max_eq_left
  rw [← one_div, div_le_iff₀ hb0]
  linarith

theorem finite_high_order_gaussian_renyi_bound {d : ℕ}
    {ρ σ : MultiModeOscillatorSpace d →L[ℂ] MultiModeOscillatorSpace d}
    {Vρ Vσ : Matrix (Fin d × Fin 2) (Fin d × Fin 2) ℝ}
    (hρ : IsFaithfulDensity ρ) (hσ : IsFaithfulDensity σ)
    (hVρ : Vρ.IsHermitian) (hVσ : Vσ.IsHermitian)
    (hGρ : HasGaussianPhysicalCharacteristic ρ Vρ)
    (hGσ : HasGaussianPhysicalCharacteristic σ Vσ)
    (n : ℕ) {ε : ℝ} (hε : ε ≤ 1 / 8)
    (hop : ‖intrinsicGaussianRelativePerturbation ρ σ (sourceHighExponent n)‖ ≤ ε)
    (htrace : matrixTraceNorm (intrinsicGaussianRelativePerturbation ρ σ
      (sourceHighExponent n)) ≤ ε) :
    0 < sandwichedRenyiQuantity ρ σ ((n + 2 : ℕ) : ℝ) ∧
      sandwichedRenyiQuantity ρ σ ((n + 2 : ℕ) : ℝ) < ∞ ∧
      Real.log (sandwichedRenyiQuantity ρ σ ((n + 2 : ℕ) : ℝ)).toReal ≤
        8 * ((n + 2 : ℕ) : ℝ) * ε ∧
      sandwichedRenyiQuantity ρ σ ((n + 2 : ℕ) : ℝ) ≤
        ENNReal.ofReal (Real.exp (8 * ((n + 2 : ℕ) : ℝ) * ε)) := by
  have hr : (1 : ℝ) < ((n + 2 : ℕ) : ℝ) := by exact_mod_cast (show 1 < n + 2 by omega)
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans hop
  have hsmall : ‖intrinsicGaussianRelativePerturbation ρ σ
      (gaussianRenyiTau ((n + 2 : ℕ) : ℝ))‖ ≤
        (4 * max 2 (gaussianRenyiTau ((n + 2 : ℕ) : ℝ))⁻¹)⁻¹ := by
    rw [sourceHighOrder_max_inverse, gaussianRenyiTau_sourceHighOrder]
    calc
      _ ≤ ε := hop
      _ ≤ 1 / 8 := hε
      _ = (4 * 2)⁻¹ := by norm_num
  obtain ⟨hQ0, hQt, hlog⟩ := faithful_gaussian_renyi_bound hρ hσ hVρ hVσ hGρ hGσ hr hsmall
  rw [sourceHighOrder_max_inverse, gaussianRenyiTau_sourceHighOrder] at hlog
  have hlog' : Real.log (sandwichedRenyiQuantity ρ σ ((n + 2 : ℕ) : ℝ)).toReal ≤
      8 * ((n + 2 : ℕ) : ℝ) * ε := by
    apply hlog.trans
    calc
      _ ≤ 2 * ((n + 2 : ℕ) : ℝ) * 2 * ε :=
        mul_le_mul_of_nonneg_left htrace (by positivity)
      _ ≤ _ := by nlinarith
  refine ⟨hQ0, hQt, hlog', ?_⟩
  have he := ENNReal.ofReal_le_ofReal
    ((Real.log_le_iff_le_exp (ENNReal.toReal_pos hQ0.ne' hQt.ne)).mp hlog')
  simpa only [ENNReal.ofReal_toReal hQt.ne] using he

end VacuumBellSeparation
