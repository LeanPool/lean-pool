/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.EhrhardGaussian.Ehrhard.TimePerturbation

/-! # The time derivative of the interpolation functional -/

@[expose] public noncomputable section

open ProbabilityTheory

namespace EhrhardGaussian.Ehrhard

/-- The interpolation scale has the stated derivative at every nonnegative time. -/
theorem hasDerivAt_interpolationScale (R : ℝ) {ε t : ℝ} (hε : 0 < ε) (ht : 0 ≤ t) :
    HasDerivAt (interpolationScale R ε)
      (interpolationScale R ε t / (Real.exp (2 * t + ε) - 1)) t := by
  let a := Real.exp (-2 * t - ε)
  let b := Real.sqrt (1 - a)
  let E := Real.exp (2 * t + ε)
  have ha : 0 < 1 - a := sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith only [hε, ht]))
  have hb : 0 < b := Real.sqrt_pos.mpr ha
  have hE : 0 < E - 1 := sub_pos.mpr (Real.one_lt_exp_iff.mpr (by linarith only [hε, ht]))
  have hs : b ^ 2 = 1 - a := Real.sq_sqrt ha.le
  have hEa : a * E = 1 := by
    dsimp only [a, E]
    rw [← Real.exp_add, show -2 * t - ε + (2 * t + ε) = 0 by ring, Real.exp_zero]
  have hrel : a * (E - 1) = b ^ 2 := by nlinarith only [hEa, hs]
  have hd := (Real.hasDerivAt_sqrt ha.ne').comp t
    (((((hasDerivAt_id' t).const_mul (-2)).sub_const ε).exp).const_sub 1)
  have hraw : HasDerivAt (interpolationScale R ε) (R * a / b) t := by
    convert hd.const_mul R using 1
    · rfl
    · dsimp only [a, b]
      field_simp
  have hfrac : R * a / b = interpolationScale R ε t / (E - 1) := by
    apply (div_eq_div_iff hb.ne' hE.ne').mpr
    change R * a * (E - 1) = R * b * b
    calc
      _ = R * (a * (E - 1)) := by ring
      _ = R * b ^ 2 := by rw [hrel]
      _ = _ := by ring
  rw [hfrac] at hraw
  exact hraw

/-- Differentiating the time-dependent Gaussian functional differentiates its interpolation scale.
-/
theorem hasDerivAt_time_gaussianFunctional {ι : Type*} [Fintype ι]
    (θ x : ι → ℝ) (R : ℝ) {ε t : ℝ} (hε : 0 < ε) (ht : 0 ≤ t) :
    HasDerivAt (fun s => gaussianFunctional θ (interpolationScale R ε s) x)
      (interpolationScale R ε t * gaussianPDFReal 0 1
        (interpolationScale R ε t * quantileLinear θ x) * quantileLinear θ x /
          (Real.exp (2 * t + ε) - 1)) t := by
  have h := (hasDerivAt_gaussianCDF (interpolationScale R ε t * quantileLinear θ x)).comp t
    ((hasDerivAt_interpolationScale R hε ht).mul_const (quantileLinear θ x))
  convert h using 1
  · rfl
  · ring

/-- The time derivative of the Gaussian functional is nonpositive on its nonpositive quantile
sublevel. -/
theorem deriv_time_gaussianFunctional_nonpos {ι : Type*} [Fintype ι]
    (θ x : ι → ℝ) {R ε t : ℝ} (hR : 0 ≤ R) (hε : 0 < ε) (ht : 0 ≤ t)
    (hgap : quantileLinear θ x ≤ 0) :
    deriv (fun s => gaussianFunctional θ (interpolationScale R ε s) x) t ≤ 0 := by
  rw [(hasDerivAt_time_gaussianFunctional θ x R hε ht).deriv]
  apply div_nonpos_of_nonpos_of_nonneg
  · exact mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg (mul_nonneg hR (Real.sqrt_nonneg _)) (gaussianPDFReal_nonneg 0 1 _)) hgap
  · exact sub_nonneg.mpr (Real.one_le_exp_iff.mpr (by linarith only [hε, ht]))

end EhrhardGaussian.Ehrhard

end
