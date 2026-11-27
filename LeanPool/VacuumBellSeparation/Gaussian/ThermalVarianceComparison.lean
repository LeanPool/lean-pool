/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.ThermalScalar
public import LeanPool.VacuumBellSeparation.Gaussian.ThermalSandwichNormalization

/-!
# The source comparison of thermal variances

The monotonicity of coth(u)-1/u, proved in `Gaussian/ThermalScalar.lean` as a step of the
library's proof of Lemma 4.3 (`coth_sub_inv_monotoneOn`), implies monotonicity of u coth(u),
which the manuscript uses in the proof of Theorem 4.1. Together with decreasing coth this yields
the exact ratio
bound for the actual normalized thermal-power covariances. Pure modes
are treated directly, and all exponent domains are positive.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

theorem coth_sub_inv_nonneg {u : ℝ} (hu : 0 < u) :
    0 ≤ Real.cosh u / Real.sinh u - u⁻¹ := by
  have hs : 0 < Real.sinh u := Real.sinh_pos_iff.mpr hu
  have h := VacuumBellSeparation.sinh_le_mul_cosh hu.le
  rw [sub_nonneg, inv_le_iff_one_le_mul₀' hu]
  rw [← mul_div_assoc, le_div_iff₀ hs]
  simpa only [one_mul] using h

theorem mul_coth_monotoneOn :
    MonotoneOn (fun u : ℝ => u * (Real.cosh u / Real.sinh u)) (Set.Ioi 0) := by
  intro u hu v hv huv
  change 0 < u at hu
  change 0 < v at hv
  have hq := VacuumBellSeparation.coth_sub_inv_monotoneOn hu hv huv
  have hm := mul_le_mul huv hq (coth_sub_inv_nonneg hu) hv.le
  have huinv := mul_inv_cancel₀ hu.ne'
  have hvinv := mul_inv_cancel₀ hv.ne'
  nlinarith

theorem coth_antitoneOn :
    AntitoneOn (fun u : ℝ => Real.cosh u / Real.sinh u) (Set.Ioi 0) := by
  have hd : ∀ u : ℝ, 0 < u → HasDerivAt (fun u => Real.cosh u / Real.sinh u)
      (-1 / Real.sinh u ^ 2) u := by
    intro u hu
    have h := (Real.hasDerivAt_cosh u).div (Real.hasDerivAt_sinh u)
      (Real.sinh_pos_iff.mpr hu).ne'
    convert h using 1
    congr 1
    nlinarith [Real.cosh_sq_sub_sinh_sq u]
  apply antitoneOn_of_deriv_nonpos (convex_Ioi 0)
  · exact fun u hu => (hd u hu).continuousAt.continuousWithinAt
  · intro u hu
    rw [interior_Ioi] at hu
    exact (hd u hu).differentiableAt.differentiableWithinAt
  · intro u hu
    rw [interior_Ioi] at hu
    rw [(hd u hu).deriv]
    exact div_nonpos_of_nonpos_of_nonneg (by norm_num) (sq_nonneg _)

theorem cosh_div_sinh_eq_exp_neg {u : ℝ} (hu : 0 < u) :
    Real.cosh u / Real.sinh u = (1 + Real.exp (-2 * u)) / (1 - Real.exp (-2 * u)) := by
  have hs : Real.sinh u ≠ 0 := (Real.sinh_pos_iff.mpr hu).ne'
  have he₁ : Real.exp (-2 * u) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have he : Real.exp u * Real.exp (-2 * u) = Real.exp (-u) := by
    rw [← Real.exp_add]
    congr 1
    ring
  apply (div_eq_div_iff hs (sub_pos.mpr he₁).ne').mpr
  rw [Real.cosh_eq, Real.sinh_eq]
  nlinarith [he]

theorem thermalQuadratureVariance_exp_neg {u : ℝ} (hu : 0 < u) :
    thermalQuadratureVariance (Real.exp (-2 * u)) =
      (1 / 2 : ℝ) * (Real.cosh u / Real.sinh u) := by
  rw [cosh_div_sinh_eq_exp_neg hu, thermalQuadratureVariance]
  have hden : 1 - Real.exp (-2 * u) ≠ 0 :=
    (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))).ne'
  field_simp [hden]

theorem coth_scaled_comparison {u a b : ℝ} (hu : 0 < u) (ha : 0 < a) (hb : 0 < b) :
    Real.cosh (a * u) / Real.sinh (a * u) ≤
      max 1 (b / a) * (Real.cosh (b * u) / Real.sinh (b * u)) := by
  have hbu : 0 < Real.cosh (b * u) / Real.sinh (b * u) :=
    div_pos (Real.cosh_pos _) (Real.sinh_pos_iff.mpr (mul_pos hb hu))
  by_cases hab : a ≤ b
  · have hm := mul_coth_monotoneOn (mul_pos ha hu) (mul_pos hb hu)
      (mul_le_mul_of_nonneg_right hab hu.le)
    have hratio : Real.cosh (a * u) / Real.sinh (a * u) ≤
        (b / a) * (Real.cosh (b * u) / Real.sinh (b * u)) := by
      apply (_root_.mul_le_mul_iff_right₀ (mul_pos ha hu)).mp
      convert hm using 1; field_simp [ha.ne']
    exact hratio.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hbu.le)
  · have hc := coth_antitoneOn (mul_pos hb hu) (mul_pos ha hu)
      (mul_le_mul_of_nonneg_right (le_of_not_ge hab) hu.le)
    exact hc.trans (by simpa only [one_mul] using
      mul_le_mul_of_nonneg_right (le_max_left (1 : ℝ) (b / a)) hbu.le)

/-- The source bound v(q^a)/v(q^b) ≤ max{1,b/a}, written without a
division by the (already positive) reference variance. -/
theorem thermalQuadratureVariance_power_comparison {q a b : ℝ}
    (hq₀ : 0 ≤ q) (hq₁ : q < 1) (ha : 0 < a) (hb : 0 < b) :
    thermalQuadratureVariance (q ^ a) ≤
      max 1 (b / a) * thermalQuadratureVariance (q ^ b) := by
  by_cases hq : q = 0
  · simp only [hq, Real.zero_rpow ha.ne', Real.zero_rpow hb.ne', thermalQuadratureVariance]
    norm_num
  · have hqpos : 0 < q := lt_of_le_of_ne hq₀ (Ne.symm hq)
    let u : ℝ := -Real.log q / 2
    have hu : 0 < u := by
      dsimp [u]
      linarith [Real.log_neg hqpos hq₁]
    have he (t : ℝ) : q ^ t = Real.exp (-2 * (t * u)) := by
      rw [Real.rpow_def_of_pos hqpos]
      congr 1
      dsimp [u]
      ring
    rw [he a, he b, thermalQuadratureVariance_exp_neg (mul_pos ha hu),
      thermalQuadratureVariance_exp_neg (mul_pos hb hu)]
    have h := mul_le_mul_of_nonneg_left (coth_scaled_comparison hu ha hb) (by norm_num :
      (0 : ℝ) ≤ 1 / 2)
    nlinarith

end VacuumBellSeparation.Gaussian
