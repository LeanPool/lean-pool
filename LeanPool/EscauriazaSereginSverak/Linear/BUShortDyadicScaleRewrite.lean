/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortCellGaussianAlgebra

/-!
# Reciprocal dyadic scale

At the shifted short-time layer indexed by `k + 1`, the reciprocal
scale is the corresponding positive power of two.
-/

public section


noncomputable section

namespace ESS

/-- The reciprocal of a short-time dyadic scale is a natural power of
two (`lem:bu-small-time`). -/
theorem bu_short_dyadic_scale_reciprocal (k : ℕ) :
    (CKN.Foundation.buSmallTimeDyadicScale (k + 1 : ℤ))⁻¹ =
      (2 : ℝ) ^ (k + 1) := by
  change ((2 : ℝ) ^ (-(k + 1 : ℤ)))⁻¹ = _
  rw [zpow_neg, inv_inv]
  norm_cast

/-- A single inverse dyadic power and its Gaussian tail have the
summable form used by the cell partition (`lem:bu-small-time`). -/
theorem bu_short_dyadic_tail_rewrite (β K P : ℝ) (k : ℕ) :
    K / CKN.Foundation.buSmallTimeDyadicScale (k + 1 : ℤ) *
        Real.exp (-(β / (12 *
          CKN.Foundation.buSmallTimeDyadicScale (k + 1 : ℤ)))) * P =
      K * ((2 : ℝ) ^ (k + 1) *
        Real.exp (-((β / 12) * (2 : ℝ) ^ (k + 1)))) * P := by
  have h := bu_short_dyadic_scale_reciprocal k
  rw [div_eq_mul_inv, h]
  have harg : -(β / (12 * CKN.Foundation.buSmallTimeDyadicScale (k + 1 : ℤ))) =
      -((β / 12) * (2 : ℝ) ^ (k + 1)) := by
    rw [div_eq_mul_inv, mul_inv_rev, ← div_eq_mul_inv, div_eq_mul_inv, h]
    ring
  rw [harg]
  ring

end ESS
