/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.CompactPowerIntertwining
public import LeanPool.VacuumBellSeparation.Gaussian.SandwichedRenyiQuantity

/-!
# Actual sandwiches at smaller inverse-reference exponents

If a positive bounded sandwich exists at exponent tau, every smaller
nonnegative exponent s is obtained by conjugating with the genuine
nonnegative CFC power sigma^((tau-s)/2). This proves bounded extension
existence directly, including s=tau; no trace-class assumption on the
sandwich or bounded inverse of the faithful density is used.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open ContinuousLinearMap
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Lower power sandwich given by `σ ^ ((τ - s) / 2) * Θ * σ ^ ((τ - s) / 2)`. -/
def lowerPowerSandwich (σ Θ : E →L[ℂ] E) (τ s : ℝ) : E →L[ℂ] E :=
  σ ^ ((τ - s) / 2) * Θ * σ ^ ((τ - s) / 2)

theorem lowerPowerSandwich_nonneg {σ Θ : E →L[ℂ] E} (hΘ : 0 ≤ Θ) (τ s : ℝ) :
    0 ≤ lowerPowerSandwich σ Θ τ s := by
  exact conjugate_nonneg_of_nonneg hΘ CFC.rpow_nonneg

theorem lowerPowerSandwich_factorization {ρ σ Θ : E →L[ℂ] E}
    (hσ : 0 ≤ σ) {τ s : ℝ} (hs : 0 ≤ s) (hst : s ≤ τ)
    (hf : σ ^ (τ / 2) * Θ * σ ^ (τ / 2) = ρ) :
    σ ^ (s / 2) * lowerPowerSandwich σ Θ τ s * σ ^ (s / 2) = ρ := by
  have ha : 0 ≤ (τ - s) / 2 := div_nonneg (sub_nonneg.mpr hst) (by norm_num)
  have hb : 0 ≤ s / 2 := by positivity
  have hleft : σ ^ (s / 2) * σ ^ ((τ - s) / 2) = σ ^ (τ / 2) := by
    rw [← positiveOperator_rpow_add_nonneg hσ hb ha]
    congr 1
    ring
  have hright : σ ^ ((τ - s) / 2) * σ ^ (s / 2) = σ ^ (τ / 2) := by
    rw [← positiveOperator_rpow_add_nonneg hσ ha hb]
    congr 1
    ring
  calc
    _ = (σ ^ (s / 2) * σ ^ ((τ - s) / 2)) * Θ *
        (σ ^ ((τ - s) / 2) * σ ^ (s / 2)) := by
      unfold lowerPowerSandwich
      noncomm_ring
    _ = ρ := by rw [hleft, hright, hf]

theorem gaussianRenyiTau_ge_half {r : ℝ} (hr : 2 ≤ r) : 1 / 2 ≤ gaussianRenyiTau r := by
  have hr₀ : 0 < r := by linarith
  unfold gaussianRenyiTau
  apply (le_div_iff₀ hr₀).mpr
  linarith

theorem renyiTwo_lowerPowerSandwich {ρ σ Θ : E →L[ℂ] E}
    (hσ : IsFaithfulDensity σ) {r : ℝ} (hr : 2 ≤ r) (hΘ : 0 ≤ Θ)
    (hf : σ ^ (gaussianRenyiTau r / 2) * Θ * σ ^ (gaussianRenyiTau r / 2) = ρ) :
    sandwichedRenyiQuantity ρ σ 2 =
      positiveTrace ((lowerPowerSandwich σ Θ (gaussianRenyiTau r) (1 / 2)) ^ (2 : ℝ)) := by
  apply sandwichedRenyiQuantity_eq_power_trace hσ (by norm_num)
    (lowerPowerSandwich_nonneg hΘ _ _)
  have h := lowerPowerSandwich_factorization hσ.1 (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (gaussianRenyiTau_ge_half hr) hf
  simpa only [gaussianRenyiTau, show (2 - 1) / (2 : ℝ) = 1 / 2 by norm_num] using h

end VacuumBellSeparation.Gaussian
