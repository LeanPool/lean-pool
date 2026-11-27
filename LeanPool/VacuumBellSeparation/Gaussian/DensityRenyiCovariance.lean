/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.DensityTraceNormDual
public import LeanPool.VacuumBellSeparation.Gaussian.SemidefiniteRenyiComparison

/-!
# True bounded-observable and covariance transfer from Rényi comparison

The actual trace-norm dual bound and the proved full-Hilbert-space r>=2
comparison control arbitrary bounded complex observables. When the actual
reference joint expectation equals the input marginal product, the same
estimate controls the literal covariance. No commutativity or assumed
trace-duality theorem is used in these transfer identities.
-/

@[expose] public section

namespace VacuumBellSeparation.Gaussian

open scoped ENNReal

variable {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem enorm_densityExpectation_sub_le_renyi (b : HilbertBasis ι ℂ E)
    {ρ σ : E →L[ℂ] E} (hρ : 0 ≤ ρ) (hρt : positiveTrace ρ = 1)
    (hσ : IsFaithfulDensity σ) {r : ℝ} (hr : 2 ≤ r) (B : E →L[ℂ] E) :
    ENNReal.ofReal ‖densityExpectation b ρ B - densityExpectation b σ B‖ ≤
      (sandwichedRenyiQuantity ρ σ r ^ (1 / (r - 1)) - 1) ^ (1 / 2 : ℝ) *
        ENNReal.ofReal ‖B‖ := by
  have hρtc : IsPositiveTraceClass ρ :=
    ⟨hρ, by rw [hρt]; exact ENNReal.one_lt_top⟩
  exact (enorm_densityExpectation_sub_le_traceNorm b hρtc hσ.isPositiveTraceClass B).trans
    (_root_.mul_le_mul_left (renyi_trace_distance hρ hρt hσ hr) _)

theorem enorm_densityCovariance_le_renyi (b : HilbertBasis ι ℂ E)
    {ρ σ A B : E →L[ℂ] E} (hρ : 0 ≤ ρ) (hρt : positiveTrace ρ = 1)
    (hσ : IsFaithfulDensity σ) {r : ℝ} (hr : 2 ≤ r)
    (hproduct : densityExpectation b σ (A * B) =
      densityExpectation b ρ A * densityExpectation b ρ B) :
    ENNReal.ofReal ‖densityExpectation b ρ (A * B) -
      densityExpectation b ρ A * densityExpectation b ρ B‖ ≤
      (sandwichedRenyiQuantity ρ σ r ^ (1 / (r - 1)) - 1) ^ (1 / 2 : ℝ) *
        (ENNReal.ofReal ‖A‖ * ENNReal.ofReal ‖B‖) := by
  rw [← hproduct]
  exact (enorm_densityExpectation_sub_le_renyi b hρ hρt hσ hr (A * B)).trans
    (_root_.mul_le_mul_right (by
      simpa only [ENNReal.ofReal_mul (norm_nonneg A)] using
        ENNReal.ofReal_le_ofReal (norm_mul_le A B)) _)

theorem enorm_contraction_densityCovariance_le_renyi (b : HilbertBasis ι ℂ E)
    {ρ σ A B : E →L[ℂ] E} (hρ : 0 ≤ ρ) (hρt : positiveTrace ρ = 1)
    (hσ : IsFaithfulDensity σ) {r : ℝ} (hr : 2 ≤ r)
    (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1)
    (hproduct : densityExpectation b σ (A * B) =
      densityExpectation b ρ A * densityExpectation b ρ B) :
    ENNReal.ofReal ‖densityExpectation b ρ (A * B) -
      densityExpectation b ρ A * densityExpectation b ρ B‖ ≤
      (sandwichedRenyiQuantity ρ σ r ^ (1 / (r - 1)) - 1) ^ (1 / 2 : ℝ) := by
  have h := enorm_densityCovariance_le_renyi b hρ hρt hσ hr hproduct
  have hn : ENNReal.ofReal ‖A‖ * ENNReal.ofReal ‖B‖ ≤ 1 := by
    calc
      _ ≤ 1 * ENNReal.ofReal ‖B‖ := _root_.mul_le_mul_left (ENNReal.ofReal_le_one.mpr hA) _
      _ = ENNReal.ofReal ‖B‖ := one_mul _
      _ ≤ 1 := ENNReal.ofReal_le_one.mpr hB
  have ht := _root_.mul_le_mul_right hn
    ((sandwichedRenyiQuantity ρ σ r ^ (1 / (r - 1)) - 1) ^ (1 / 2 : ℝ))
  exact h.trans (by simpa only [mul_one] using ht)

end VacuumBellSeparation.Gaussian
