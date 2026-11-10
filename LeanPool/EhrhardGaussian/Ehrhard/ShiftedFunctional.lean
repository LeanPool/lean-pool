/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.EhrhardGaussian.Ehrhard.TripleWeights
public import LeanPool.EhrhardGaussian.Ehrhard.OUTimeDependent

/-! # Smoothness and strict sublevels for the shifted interpolation functional -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ContDiff

namespace EhrhardGaussian.Ehrhard

/-- The interpolation scale is smooth wherever its square root argument is positive. -/
theorem contDiffAt_interpolationScale (R ε t : ℝ) (ht : 0 < 2 * t + ε) :
    ContDiffAt ℝ ∞ (interpolationScale R ε) t := by
  have harg : 0 < 1 - Real.exp (-2 * t - ε) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith only [ht]))
  exact contDiffAt_const.mul
    ((by fun_prop : ContDiffAt ℝ ∞ (fun s : ℝ => 1 - Real.exp (-2 * s - ε)) t).sqrt harg.ne')

/-- Inner OU time is `s`, while the functional's time starts at `s-ε`.
This keeps every outer OU time nonnegative in the interpolation triangle. -/
def interpolationFunctional {k : ℕ} (θ : Fin k → ℝ) (R ε : ℝ)
    (p : ℝ × (Fin k → ℝ)) : ℝ :=
  gaussianFunctional θ (interpolationScale R ε (p.1 - ε)) p.2

/-- The shifted interpolation functional is smooth on the probability box at admissible times. -/
theorem contDiffAt_interpolationFunctional {k : ℕ} (θ : Fin k → ℝ) (R ε : ℝ)
    {t : ℝ} {x : Fin k → ℝ} (ht : 0 < 2 * t - ε) (hx : x ∈ probabilityBox) :
    ContDiffAt ℝ ∞ (interpolationFunctional θ R ε) (t, x) := by
  have hscale := (contDiffAt_interpolationScale R ε (t - ε) (by linarith only [ht])).comp (t, x)
    (contDiffAt_fst.sub contDiffAt_const)
  have hquantile := (contDiffAt_quantileLinear θ hx).comp (t, x) contDiffAt_snd
  exact contDiff_gaussianCDF.contDiffAt.comp (t, x) (hscale.mul hquantile)

/-- The time derivative of the shifted functional equals the derivative of its unshifted scale
formula. -/
theorem fderiv_interpolationFunctional_time {k : ℕ} (θ : Fin k → ℝ) (R : ℝ)
    {ε t : ℝ} (hε : 0 < ε) (ht : ε ≤ t) {x : Fin k → ℝ} (hx : x ∈ probabilityBox) :
    fderiv ℝ (interpolationFunctional θ R ε) (t, x) (1, 0) =
      deriv (fun s => gaussianFunctional θ (interpolationScale R ε s) x) (t - ε) := by
  have hdiff := ((contDiffAt_interpolationFunctional θ R ε (t := t) (by linarith only [hε, ht])
    hx).of_le
    (by simp : (1 : WithTop ℕ∞) ≤ ∞)).differentiableAt_one
  rw [← deriv_spaceTime_left hdiff]
  change deriv (fun s => gaussianFunctional θ (interpolationScale R ε (s - ε)) x) t = _
  have hbase := hasDerivAt_time_gaussianFunctional θ x R hε (sub_nonneg.mpr ht)
  have h := hbase.comp t ((hasDerivAt_id' t).sub_const ε)
  change HasDerivAt (fun s => gaussianFunctional θ (interpolationScale R ε (s - ε)) x) _ t at h
  rw [h.deriv, hbase.deriv, mul_one]

/-- A nonnegative limiting scale gives a nonnegative interpolation scale. -/
theorem interpolationScale_nonneg {R : ℝ} (hR : 0 ≤ R) (ε t : ℝ) : 0 ≤ interpolationScale R ε t :=
  mul_nonneg hR (Real.sqrt_nonneg _)

/-- The interpolation scale is bounded above by its nonnegative limiting scale. -/
theorem interpolationScale_le {R : ℝ} (hR : 0 ≤ R) (ε t : ℝ) : interpolationScale R ε t ≤ R := by
  have hs : Real.sqrt (1 - Real.exp (-2 * t - ε)) ≤ 1 :=
    Real.sqrt_le_one.mpr (by linarith only [Real.exp_pos (-2 * t - ε)])
  exact (mul_le_mul_of_nonneg_left hs hR).trans_eq (mul_one R)

/-- Every point in the strict sublevel satisfies the uniform negative quantile-gap bound. -/
theorem interpolationFunctional_sublevel_gap {k : ℕ} (θ : Fin k → ℝ)
    {R κ : ℝ} (hR : 0 ≤ R) (hκ : 0 ≤ κ) (ε t : ℝ) (x : Fin k → ℝ)
    (hsub : interpolationFunctional θ R ε (t, x) < gaussianCDF (-R * κ)) :
    quantileLinear θ x < -κ := by
  have hlin : interpolationScale R ε (t - ε) * quantileLinear θ x < -R * κ :=
    strictMono_gaussianCDF.lt_iff_lt.mp hsub
  by_contra hnot
  have hgap : -κ ≤ quantileLinear θ x := le_of_not_gt hnot
  have h₁ := mul_le_mul_of_nonneg_left hgap (interpolationScale_nonneg hR ε (t - ε))
  have h₂ := mul_le_mul_of_nonneg_right (interpolationScale_le hR ε (t - ε)) hκ
  nlinarith only [hlin, h₁, h₂]

end EhrhardGaussian.Ehrhard

end
