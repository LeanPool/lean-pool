/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.ConvexFractionalInfiniteBallChain
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.ConvexHardyScaleSummation

/-!
# High-contrast homogenization: Provider.PolynomialHomogenization.FractionalChainGeometricHead

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Geometric heads for the fractional pointwise chain
-/

namespace HCPolySupport
namespace HighContrast

open scoped ENNReal

noncomputable section

/-- A growing geometric sequence cut off before `X q^n` reaches one has
mass controlled by `X⁻¹`. -/
theorem tsum_geometric_of_mul_pow_lt_one_le
    {X q : ℝ} (hX : 0 < X) (hq : 1 < q) :
    (∑' n : ℕ, if X * q ^ n < 1 then ENNReal.ofReal (q ^ n) else 0) ≤
      1 + (ENNReal.ofReal X)⁻¹ * ENNReal.ofReal (q / (q - 1)) := by
  let f : ℕ → ℝ≥0∞ := fun n =>
    if X * q ^ n < 1 then ENNReal.ofReal (q ^ n) else 0
  let g : ℕ → ℝ≥0∞ := fun k =>
    if X * q ^ (k + 1) ≤ 1 then
      ENNReal.ofReal (X * q ^ (k + 1)) else 0
  have hXtop : ENNReal.ofReal X ≠ ⊤ := ENNReal.ofReal_ne_top
  have hXzero : ENNReal.ofReal X ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hX
  have htail : ∀ k, f (k + 1) ≤ (ENNReal.ofReal X)⁻¹ * g k := by
    intro k
    by_cases hk : X * q ^ (k + 1) < 1
    · have hkLe : X * q ^ (k + 1) ≤ 1 := hk.le
      rw [show f (k + 1) = ENNReal.ofReal (q ^ (k + 1)) by
        simp only [f, ite_eq_left hk]]
      rw [show g k = ENNReal.ofReal (X * q ^ (k + 1)) by
        simp only [g, ite_eq_left hkLe]]
      rw [ENNReal.ofReal_mul hX.le]
      calc
        ENNReal.ofReal (q ^ (k + 1)) =
            1 * ENNReal.ofReal (q ^ (k + 1)) := by rw [one_mul]
        _ = ((ENNReal.ofReal X)⁻¹ * ENNReal.ofReal X) *
            ENNReal.ofReal (q ^ (k + 1)) := by
          rw [ENNReal.inv_mul_cancel hXzero hXtop]
        _ = (ENNReal.ofReal X)⁻¹ *
            (ENNReal.ofReal X * ENNReal.ofReal (q ^ (k + 1))) := by
          rw [mul_assoc]
        _ ≤ (ENNReal.ofReal X)⁻¹ *
            (ENNReal.ofReal X * ENNReal.ofReal (q ^ (k + 1))) := le_rfl
    · rw [show f (k + 1) = 0 by simp only [f, ite_eq_right hk]]
      exact bot_le
  have hhead := tsum_cutoff_geometric_head_le hq hX.le
    (by norm_num : (0 : ℝ) ≤ 1)
  change (∑' k : ℕ, g k) ≤ ENNReal.ofReal (q / (q - 1) * 1) at hhead
  rw [mul_one] at hhead
  change (∑' n : ℕ, f n) ≤ _
  rw [tsum_eq_zero_add' ENNReal.summable]
  calc
    f 0 + ∑' k : ℕ, f (k + 1) ≤
        1 + ∑' k : ℕ, (ENNReal.ofReal X)⁻¹ * g k := by
      exact add_le_add (by
        by_cases h0 : X * q ^ 0 < 1
        · simp only [f, ite_eq_left h0, pow_zero, ENNReal.ofReal_one, le_rfl]
        · simp only [f, ite_eq_right h0, zero_le])
        (ENNReal.tsum_le_tsum htail)
    _ = 1 + (ENNReal.ofReal X)⁻¹ * ∑' k : ℕ, g k := by
      rw [ENNReal.tsum_mul_left]
    _ ≤ 1 + (ENNReal.ofReal X)⁻¹ *
        ENNReal.ofReal (q / (q - 1)) :=
      add_le_add le_rfl (mul_le_mul_right hhead _)

end

end HighContrast
end HCPolySupport
