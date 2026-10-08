/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortAverageFactor

/-!
# Exponents under short-time rescaling

The spatial growth exponent scales quadratically, while the normal
Gaussian decay retains an inverse dyadic time scale.
-/

public section


open CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- The squared Euclidean norm in three coordinates is the sum of
the three coordinate squares (`lem:bu-small-time`). -/
theorem bu_short_vec3_norm_sq_coordinates (Y : Vec3) :
    vec3EuclideanNorm Y ^ 2 = Y 0 ^ 2 + Y 1 ^ 2 + Y 2 ^ 2 := by
  rw [vec3EuclideanNorm, Real.sq_sqrt
    (Finset.sum_nonneg fun i hi => sq_nonneg (Y i))]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  norm_num
  ring

/-- The physical Gaussian normal tail dominates the dyadic normal
tail after short-time rescaling (`lem:bu-small-time`). -/
theorem bu_short_average_normal_tail_le
    (scale β δ d : ℝ) (Y : Vec3)
    (hscale : 0 < scale) (hβ : 0 < β)
    (hδ : 0 < δ) (hδd : δ ≤ d) :
    let t := scale ^ 2 * δ / 2
    let X := scale • Y
    Real.exp (-(β * X 2 ^ 2 / (12 * t))) ≤
      Real.exp (-(β * Y 2 ^ 2 / (12 * d))) := by
  dsimp
  have hd : 0 < d := hδ.trans_le hδd
  have hQ : 0 ≤ β * Y 2 ^ 2 := mul_nonneg hβ.le (sq_nonneg _)
  have hδ2d : δ ≤ 2 * d := by linarith only [hδd, hd]
  have hmul := mul_le_mul_of_nonneg_left hδ2d hQ
  have hFraction : β * Y 2 ^ 2 / (12 * d) ≤
      β * Y 2 ^ 2 / (6 * δ) := by
    apply (div_le_div_iff₀ (by positivity : 0 < 12 * d)
      (by positivity : 0 < 6 * δ)).2
    nlinarith only [hmul]
  have hEq : -(β * (scale * Y 2) ^ 2 /
      (12 * (scale ^ 2 * δ / 2))) =
      -(β * Y 2 ^ 2 / (6 * δ)) := by
    field_simp
    ring
  rw [hEq]
  exact Real.exp_le_exp.mpr (neg_le_neg hFraction)

end ESS
