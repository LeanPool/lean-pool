/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.RowSupply.FixedParentObservationResponse

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.RowSupply.FixedParentResponsePriceAlgebra

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Fixed-parent response-price normalization

The square root in the all-depth response estimate is rewritten as the
product of the filling constant, the parent-to-cell growth, and the converted
power tail.  This is the exact form consumed by the physical-frame algebra.
-/

namespace HCPolySupport
namespace HighContrast
namespace RowSupply

open Book Book.Ch03

noncomputable section

variable {d : ℕ}

/-- The explicit all-depth response price factors into its three nonnegative
components when the observation generation is below the fixed parent. -/
theorem sqrt_observationParent_powerPrice_eq
    {s epsilon amplitude kappa : ℝ} (abar : Mat d)
    {N K M : ℤ} (hKM : K ≤ M) (hAmplitude : 0 ≤ amplitude)
    (hs : s ≤ 1 / 2) :
    Real.sqrt
        (observationParentConvolutionFactor d s epsilon abar M K *
          (amplitude *
            (((3 : ℝ) ^ M) / ((3 : ℝ) ^ N)) ^ (-kappa)) ^ 2) =
      Real.sqrt
          (observationFillingCoefficient d epsilon abar *
            (Book.Ch02.geometricDiscount (1 - 2 * s) 1)⁻¹) *
        Real.rpow (3 : ℝ)
          (s * (((M : ℤ) : ℝ) - ((K : ℤ) : ℝ))) *
        amplitude *
        Real.rpow (3 : ℝ)
          (-kappa * (((M : ℤ) : ℝ) - ((N : ℤ) : ℝ))) := by
  let C : ℝ := observationFillingCoefficient d epsilon abar *
    (Book.Ch02.geometricDiscount (1 - 2 * s) 1)⁻¹
  have hgapNat : (((M - K).toNat : ℕ) : ℤ) = M - K :=
    Int.toNat_of_nonneg (sub_nonneg.mpr hKM)
  have hgapCast : (((M - K).toNat : ℕ) : ℝ) =
      ((M : ℤ) : ℝ) - ((K : ℤ) : ℝ) := by
    exact_mod_cast hgapNat
  have hratio : ((3 : ℝ) ^ M) / ((3 : ℝ) ^ N) =
      (3 : ℝ) ^ (M - N) := by
    rw [← zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0)]
  have htail :
      (((3 : ℝ) ^ M) / ((3 : ℝ) ^ N)) ^ (-kappa) =
        Real.rpow (3 : ℝ)
          (-kappa * (((M : ℤ) : ℝ) - ((N : ℤ) : ℝ))) := by
    rw [hratio, ← Real.rpow_intCast]
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    congr 1
    push_cast
    ring
  have hbase : 0 ≤ Real.rpow (3 : ℝ)
      (s * (((M : ℤ) : ℝ) - ((K : ℤ) : ℝ))) :=
    Real.rpow_nonneg (by norm_num) _
  have htail0 : 0 ≤ Real.rpow (3 : ℝ)
      (-kappa * (((M : ℤ) : ℝ) - ((N : ℤ) : ℝ))) :=
    Real.rpow_nonneg (by norm_num) _
  have hgrowth : Real.rpow (3 : ℝ)
        (2 * s * (((M : ℤ) : ℝ) - ((K : ℤ) : ℝ))) =
      (Real.rpow (3 : ℝ)
        (s * (((M : ℤ) : ℝ) - ((K : ℤ) : ℝ)))) ^ 2 := by
    calc
      _ = Real.rpow (3 : ℝ)
          ((s * (((M : ℤ) : ℝ) - ((K : ℤ) : ℝ))) * 2) := by
            congr 1
            ring
      _ = Real.rpow (Real.rpow (3 : ℝ)
          (s * (((M : ℤ) : ℝ) - ((K : ℤ) : ℝ)))) 2 :=
            Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3) _ _
      _ = (Real.rpow (3 : ℝ)
          (s * (((M : ℤ) : ℝ) - ((K : ℤ) : ℝ)))) ^ 2 :=
            Real.rpow_two _
  unfold observationParentConvolutionFactor
  rw [hgapCast, htail]
  change Real.sqrt
      ((C * Real.rpow (3 : ℝ)
          (2 * s * (((M : ℤ) : ℝ) - ((K : ℤ) : ℝ)))) *
        (amplitude * Real.rpow (3 : ℝ)
          (-kappa * (((M : ℤ) : ℝ) - ((N : ℤ) : ℝ)))) ^ 2) = _
  rw [hgrowth]
  have hproduct0 : 0 ≤ amplitude * Real.rpow (3 : ℝ)
      (-kappa * (((M : ℤ) : ℝ) - ((N : ℤ) : ℝ))) :=
    mul_nonneg hAmplitude htail0
  rw [show C *
        (Real.rpow (3 : ℝ)
          (s * (((M : ℤ) : ℝ) - ((K : ℤ) : ℝ)))) ^ 2 *
        (amplitude * Real.rpow (3 : ℝ)
          (-kappa * (((M : ℤ) : ℝ) - ((N : ℤ) : ℝ)))) ^ 2 =
      C *
        (Real.rpow (3 : ℝ)
          (s * (((M : ℤ) : ℝ) - ((K : ℤ) : ℝ))) *
          (amplitude * Real.rpow (3 : ℝ)
            (-kappa * (((M : ℤ) : ℝ) - ((N : ℤ) : ℝ))))) ^ 2 by ring]
  rw [Real.sqrt_mul (show 0 ≤ C by
    dsimp only [C]
    exact mul_nonneg
      (zero_le_one.trans (le_max_left _ _))
      (inv_nonneg.mpr (Book.Ch02.book_geometricDiscount_nonneg (by
        have h : 0 ≤ 1 - 2 * s := by linarith only [hs]
        simpa using h))))]
  rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (mul_nonneg hbase hproduct0)]
  ring

end

end RowSupply
end HighContrast
end HCPolySupport
