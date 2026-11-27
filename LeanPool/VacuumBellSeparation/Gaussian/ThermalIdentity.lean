/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.ThermalOperator

/-!
# Scalar parallel thermal identity

Finite geometric-series algebra for Lemma 4.4, equation (4.12). The sum
always contains `n+1` strictly positive terms, corresponding to `r=n+2`.
The removable value at spectral zero is handled by the sum itself.
-/

@[expose] public section

namespace VacuumBellSeparation.Gaussian

/-- The inverse sum after writing each scalar geometric mean as `a z^k`.
The analytic application uses `a=1+d`, `z=((1-d)/(1+d))^(1/r)`. -/
noncomputable def scalarGeometricParallel (n : ℕ) (a z : ℝ) : ℝ :=
  (∑ j : Fin (n + 1), (a * z ^ (j.val + 1))⁻¹)⁻¹

theorem scalarGeometricParallel_one (n : ℕ) (a : ℝ) :
    scalarGeometricParallel n a 1 = a / ((n + 1 : ℕ) : ℝ) := by
  simp [scalarGeometricParallel, mul_inv_rev, div_eq_mul_inv]

/-- The geometric-series quotient away from `z=1`. Positivity of `z`
excludes spurious roots of unity in the denominator. -/
theorem scalarGeometricParallel_eq (n : ℕ) {a z : ℝ} (ha : 0 < a)
    (hz : 0 < z) (hz1 : z ≠ 1) :
    scalarGeometricParallel n a z =
      a * z ^ (n + 1) * (1 - z) / (1 - z ^ (n + 1)) := by
  have hzinv : z⁻¹ ≠ 1 := by
    intro h
    apply hz1
    simpa only [inv_inv, inv_one] using congrArg Inv.inv h
  have hpow : z ^ (n + 1) ≠ 1 :=
    fun h => hz1 ((pow_eq_one_iff_of_nonneg hz.le (by omega)).mp h)
  have hsum : (∑ j : Fin (n + 1), (a * z ^ (j.val + 1))⁻¹) =
      a⁻¹ * z⁻¹ * ((z⁻¹ ^ (n + 1) - 1) / (z⁻¹ - 1)) := by
    calc
      _ = a⁻¹ * z⁻¹ * ∑ j : Fin (n + 1), z⁻¹ ^ j.val := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        simp only [pow_succ, mul_inv_rev, inv_pow]
        ring
      _ = _ := by rw [Fin.sum_univ_eq_sum_range, geom_sum_eq hzinv]
  rw [scalarGeometricParallel, hsum, inv_pow]
  have hzsub : z - 1 ≠ 0 := sub_ne_zero.mpr hz1
  have hpowSub : z ^ (n + 1) - 1 ≠ 0 := sub_ne_zero.mpr hpow
  field_simp [ha.ne', hz.ne', hzsub, hpowSub]


/-- Positivity is proved from the actual inverse sum, so it also covers
`z=1` where the quotient expression has a removable singularity. -/
theorem scalarGeometricParallel_pos (n : ℕ) {a z : ℝ} (ha : 0 < a)
    (hz : 0 < z) : 0 < scalarGeometricParallel n a z := by
  apply inv_pos.mpr
  exact Finset.sum_pos (fun j _ => inv_pos.mpr (mul_pos ha (pow_pos hz _)))
    Finset.univ_nonempty

/-- The symmetric closed expression away from spectral zero. It is
totalized there, so the value at zero is supplied separately. -/
noncomputable def thermalClosed (b d : ℝ) : ℝ :=
  d * (((1 + d) ^ b + (1 - d) ^ b) / ((1 + d) ^ b - (1 - d) ^ b)) - 1

theorem thermalClosed_neg (b d : ℝ) : thermalClosed b (-d) = thermalClosed b d := by
  unfold thermalClosed
  simp only [← sub_eq_add_neg, sub_neg_eq_add]
  rw [add_comm ((1 - d) ^ b),
    show (1 - d) ^ b - (1 + d) ^ b = -((1 + d) ^ b - (1 - d) ^ b) by ring,
    div_neg, neg_mul_neg]

theorem thermalIncrement_abs_eq_thermalClosed {b d : ℝ} (hb : 0 < b)
    (hdm : -1 < d) (hdp : d < 1) (hd0 : d ≠ 0) :
    thermalIncrement b |d| = thermalClosed b d := by
  rcases lt_or_gt_of_ne hd0 with hd | hd
  · rw [abs_of_neg hd, thermalIncrement_eq_of_pos hb (by linarith) (by linarith)]
    exact thermalClosed_neg b d
  · rw [abs_of_pos hd, thermalIncrement_eq_of_pos hb hd hdp.le]
    rfl

/-- The geometric-series expression equals the signed closed thermal
formula. Both signs of the nonzero spectral value are covered. -/
theorem scalarGeometricParallel_eq_thermalClosed (n : ℕ) {d : ℝ}
    (hdm : -1 < d) (hd1 : d < 1) (hd0 : d ≠ 0) :
    scalarGeometricParallel n (1 + d)
        (((1 - d) / (1 + d)) ^ (1 / ((n + 2 : ℕ) : ℝ))) =
      thermalClosed (((n + 1 : ℕ) : ℝ) / ((n + 2 : ℕ) : ℝ)) d := by
  let b : ℝ := ((n + 1 : ℕ) : ℝ) / ((n + 2 : ℕ) : ℝ)
  let z : ℝ := ((1 - d) / (1 + d)) ^ (1 / ((n + 2 : ℕ) : ℝ))
  have hp : 0 < 1 + d := by linarith
  have hm : 0 < 1 - d := by linarith
  have hr : (0 : ℝ) < ((n + 2 : ℕ) : ℝ) := by positivity
  have hb : 0 < b := by dsimp [b]; positivity
  have ht : 0 < (1 - d) / (1 + d) := div_pos hm hp
  have hz : 0 < z := Real.rpow_pos_of_pos ht _
  have hzr : z ^ (n + 2) = (1 - d) / (1 + d) := by
    rw [← Real.rpow_natCast]
    dsimp [z]
    rw [← Real.rpow_mul ht.le, div_mul_cancel₀ _ hr.ne', Real.rpow_one]
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, one_pow] at hzr
    have heq := (eq_div_iff hp.ne').mp hzr
    apply hd0
    linarith
  have hzm : z ^ (n + 1) = (1 - d) ^ b / (1 + d) ^ b := by
    rw [← Real.rpow_natCast]
    dsimp [z]
    rw [← Real.rpow_mul ht.le]
    have hexp : 1 / ((n + 2 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ) = b := by
      dsimp [b]
      ring
    rw [hexp, Real.div_rpow hm.le hp.le]
  have hproduct : (1 + d) * z ^ (n + 1) * z = 1 - d := by
    rw [mul_assoc, ← pow_succ, hzr, mul_div_cancel₀ _ hp.ne']
  have hnum : (1 + d) * z ^ (n + 1) * (1 - z) =
      (1 + d) * z ^ (n + 1) - (1 - d) := by
    nlinarith [hproduct]
  have hu : 0 < (1 + d) ^ b := Real.rpow_pos_of_pos hp b
  have hden : (1 + d) ^ b - (1 - d) ^ b ≠ 0 := by
    intro h
    have heq := (Real.rpow_left_inj hp.le hm.le hb.ne').mp (sub_eq_zero.mp h)
    apply hd0
    linarith
  change scalarGeometricParallel n (1 + d) z = thermalClosed b d
  rw [thermalClosed, scalarGeometricParallel_eq n hp hz hz1, hnum, hzm]
  field_simp [hu.ne', hden]; ring

/-- At spectral zero the inverse sum has the required continuous value,
without using a quotient with a vanishing geometric-series denominator. -/
theorem thermalIncrement_zero_eq_scalarGeometricParallel (n : ℕ) :
    thermalIncrement (((n + 1 : ℕ) : ℝ) / ((n + 2 : ℕ) : ℝ)) 0 =
      scalarGeometricParallel n 1 1 := by
  rw [thermalIncrement_zero, scalarGeometricParallel_one]
  have hm : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  have hr : (((n + 2 : ℕ) : ℝ)) ≠ 0 := by positivity
  push_cast
  field_simp; ring

/-- The scalar parallel thermal identity on the entire open interval,
including spectral zero with its continuous value. -/
theorem thermalIncrement_abs_eq_scalarGeometricParallel (n : ℕ) {d : ℝ}
    (hdm : -1 < d) (hd1 : d < 1) :
    thermalIncrement (((n + 1 : ℕ) : ℝ) / ((n + 2 : ℕ) : ℝ)) |d| =
      scalarGeometricParallel n (1 + d)
        (((1 - d) / (1 + d)) ^ (1 / ((n + 2 : ℕ) : ℝ))) := by
  by_cases hd0 : d = 0
  · subst d
    simpa using thermalIncrement_zero_eq_scalarGeometricParallel n
  · rw [thermalIncrement_abs_eq_thermalClosed (by positivity) hdm hd1 hd0,
      scalarGeometricParallel_eq_thermalClosed n hdm hd1 hd0]

end VacuumBellSeparation.Gaussian
