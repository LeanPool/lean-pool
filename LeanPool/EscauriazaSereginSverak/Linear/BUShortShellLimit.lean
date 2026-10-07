/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortPointwiseSquare

/-!
# Vanishing spatial shell coefficient

The spatial cutoff derivative coefficient tends to zero as its radius
increases through the natural numbers.
-/

public section


open Filter CKN CKN.Foundation.Parabolic
open scoped Topology

noncomputable section

namespace ESS

/-- The shell error coefficient vanishes along radii `n + 1`. -/
theorem buShortShellCoeff_tendsto_zero (scale c₁ : ℝ) :
    Tendsto (fun n : ℕ =>
      buShortShellCoeff scale ((n : ℝ) + 1) c₁)
      atTop (𝓝 0) := by
  have hR : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹)
      atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hR
  have hfirst : Tendsto (fun n : ℕ =>
      ((9 * (c₁ * scale) + 54) * cutoffGradientConstant / 2) *
        ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
    have h := (tendsto_const_nhds : Tendsto
      (fun _ : ℕ => (9 * (c₁ * scale) + 54) *
        cutoffGradientConstant / 2) atTop
      (𝓝 ((9 * (c₁ * scale) + 54) *
        cutoffGradientConstant / 2))).mul hinv
    simpa only [mul_zero] using h
  have hsecond : Tendsto (fun n : ℕ =>
      (3 * cutoffSecondDerivativeConstant / 4) *
        (((n : ℝ) + 1)⁻¹) ^ 2) atTop (𝓝 0) := by
    have h := (tendsto_const_nhds : Tendsto
      (fun _ : ℕ => 3 * cutoffSecondDerivativeConstant / 4)
      atTop (𝓝 (3 * cutoffSecondDerivativeConstant / 4))).mul
        (hinv.pow 2)
    simpa only [zero_pow (by norm_num : 2 ≠ 0), mul_zero] using h
  have hsum := hfirst.add hsecond
  convert hsum using 1
  · funext n
    have hpos : 0 < (n : ℝ) + 1 := by positivity
    dsimp [buShortShellCoeff]
    field_simp
    ring_nf
  · ring_nf


end ESS
