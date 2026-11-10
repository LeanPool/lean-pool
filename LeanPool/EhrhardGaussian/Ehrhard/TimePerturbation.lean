/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.EhrhardGaussian.Ehrhard.TriplePerturbation

/-! Uniform time parameters preserve the interpolation matrix condition. -/

@[expose] public noncomputable section

namespace EhrhardGaussian.Ehrhard

/-- The interpolation scale multiplies the limiting scale by the square root of the noise variance.
-/
def interpolationScale (R ε t : ℝ) : ℝ := R * Real.sqrt (1 - Real.exp (-2 * t - ε))

/-- The interpolation time coefficient is the ratio of the two shifted exponential variance factors.
-/
def interpolationTimeCoefficient (ε t : ℝ) : ℝ :=
  (Real.exp (2 * (t + ε)) - 1) / (Real.exp (2 * t + ε) - 1)

/-- The interpolation time coefficient is at least the exponential of the positive time shift. -/
theorem interpolationTimeCoefficient_lower {ε t : ℝ} (hε : 0 < ε) (ht : 0 ≤ t) :
    Real.exp ε ≤ interpolationTimeCoefficient ε t := by
  have hden : 0 < Real.exp (2 * t + ε) - 1 :=
    sub_pos.mpr (Real.one_lt_exp_iff.mpr (by linarith only [hε, ht]))
  have he : 1 ≤ Real.exp ε := (Real.one_lt_exp_iff.mpr hε).le
  have hnum : Real.exp (2 * (t + ε)) = Real.exp (2 * t + ε) * Real.exp ε := by
    rw [show 2 * (t + ε) = (2 * t + ε) + ε by ring, Real.exp_add]
  apply (le_div_iff₀ hden).mpr
  rw [hnum]
  nlinarith only [he]

/-- The square of the interpolation scale equals the squared limiting scale times the noise
variance. -/
theorem interpolationScale_sq {R ε t : ℝ} (hε : 0 < ε) (ht : 0 ≤ t) :
    interpolationScale R ε t ^ 2 = R ^ 2 * (1 - Real.exp (-2 * t - ε)) := by
  rw [interpolationScale, mul_pow, Real.sq_sqrt]
  exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith only [hε, ht]))

/-- The lower interpolation factor is 1 − exp(−ε). -/
theorem interpolationScale_sq_lower {R ε t : ℝ} (hε : 0 < ε) (ht : 0 ≤ t) :
    R ^ 2 * (1 - Real.exp (-ε)) ≤ interpolationScale R ε t ^ 2 := by
  rw [interpolationScale_sq hε ht]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg R)
  exact sub_le_sub_left (Real.exp_le_exp.mpr (by linarith only [ht])) 1

/-- NP16's uniform middle-matrix condition, on a compact quantile range and
an independently specified strictly negative gap. All times are covered by one
positive choice of `R`. -/
theorem exists_interpolationScale_posSemidef {p q ρ σ κ ε : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hsum : p + q = 1) (hρ : |ρ| < 1)
    (hσ : 0 < σ) (hκ : 0 < κ) (hε : 0 < ε) (L : ℝ) :
    ∃ R : ℝ, 0 < R ∧ ∀ t : ℝ, 0 ≤ t → ∀ u : Fin 3 → ℝ,
      (∀ i, |u i| ≤ L) → tripleLinearForm p q σ u ≤ -κ →
      (tripleD0 p q σ u -
        (interpolationScale R ε t ^ 2 * tripleLinearForm p q σ u) • tripleHessianMatrix p q ρ σ -
        (interpolationTimeCoefficient ε t * tripleLinearForm p q σ u) • tripleE p q σ).PosSemidef :=
          by
  have hδ : 0 < Real.exp ε - 1 := sub_pos.mpr (Real.one_lt_exp_iff.mpr hε)
  obtain ⟨Q, hQ, hbase⟩ := exists_tripleHessian_posSemidef hp hq hsum hρ hσ hδ hκ L
  let d := 1 - Real.exp (-ε)
  have hd : 0 < d := sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_neg_of_pos hε))
  let R := Real.sqrt (Q / d + 1)
  have harg : 0 < Q / d + 1 := by positivity
  have hR : 0 < R := Real.sqrt_pos.mpr harg
  have hR₂ : R ^ 2 = Q / d + 1 := Real.sq_sqrt harg.le
  have hlarge : Q ≤ R ^ 2 * d := by
    rw [hR₂, add_mul, div_mul_cancel₀ _ hd.ne', one_mul]
    linarith only [hd]
  refine ⟨R, hR, ?_⟩
  intro t ht u hu hgap
  apply hbase (interpolationScale R ε t) (interpolationTimeCoefficient ε t)
    (hlarge.trans (interpolationScale_sq_lower hε ht)) _ u hu hgap
  simpa only [add_sub_cancel] using interpolationTimeCoefficient_lower hε ht

end EhrhardGaussian.Ehrhard

end
