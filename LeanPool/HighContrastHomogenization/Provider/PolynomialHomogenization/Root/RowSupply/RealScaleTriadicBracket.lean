/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.HomogenizationError.AEEq
public import LeanPool.HighContrastHomogenization.Provider.Quenched.CoupledMixingScaleDecay

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.RowSupply.RealScaleTriadicBracket

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Triadic bracket for a physical scale

If a positive physical parameter has inverse at least the common effective
scale, its inverse can be rounded upward to one triadic generation.  The
rounded generation is still active for the common scale, and the remaining
dimensionless dilation lies between one and three.
-/

namespace HCPolySupport
namespace HighContrast
namespace RowSupply

noncomputable section

/-- Upward triadic rounding of `epsilon⁻¹` preserves activation above `x` and
leaves the residual factor `epsilon * 3^N` in the interval `[1,3]`. -/
theorem exists_triadicScaleBracket_of_commonScale_le_inv
    {epsilon x : ℝ} (hEpsilon : 0 < epsilon) (hX : 1 ≤ x)
    (hScale : x ≤ epsilon⁻¹) :
    ∃ N : ℕ,
      x ≤ (3 : ℝ) ^ N ∧
      epsilon⁻¹ ≤ (3 : ℝ) ^ N ∧
      (3 : ℝ) ^ N ≤ 3 * epsilon⁻¹ ∧
      1 ≤ epsilon * (3 : ℝ) ^ N ∧
      epsilon * (3 : ℝ) ^ N ≤ 3 := by
  have hInvOne : 1 ≤ epsilon⁻¹ := hX.trans hScale
  let N : ℕ := Quenched.triadicCeilingIndex epsilon⁻¹
  have hLower : epsilon⁻¹ ≤ (3 : ℝ) ^ N := by
    simpa only [N] using Quenched.le_pow_triadicCeilingIndex hInvOne
  have hUpper : (3 : ℝ) ^ N ≤ 3 * epsilon⁻¹ := by
    simpa only [N] using
      Quenched.pow_triadicCeilingIndex_le_three_mul hInvOne
  have hResidualLower : 1 ≤ epsilon * (3 : ℝ) ^ N := by
    have hMul := mul_le_mul_of_nonneg_left hLower hEpsilon.le
    simpa [hEpsilon.ne'] using hMul
  have hResidualUpper : epsilon * (3 : ℝ) ^ N ≤ 3 := by
    have hMul := mul_le_mul_of_nonneg_left hUpper hEpsilon.le
    calc
      epsilon * (3 : ℝ) ^ N ≤ epsilon * (3 * epsilon⁻¹) := hMul
      _ = 3 := by field_simp [hEpsilon.ne']
  exact ⟨N, hScale.trans hLower, hLower, hUpper,
    hResidualLower, hResidualUpper⟩

end

end RowSupply
end HighContrast
end HCPolySupport
