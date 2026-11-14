/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.Regularity.Ported.BallForcing

/-!
# DyadicRadii

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Radius arithmetic for the small-contrast iteration
-/

namespace Algsuperdiff.StochasticProcess.Common.Regularity.Ported

open Algsuperdiff.Section4.Support

noncomputable section

/-- The dyadic radius `R 2^{-n}`. -/
def smallContrastDyadicRadius (R : ℝ) (n : ℕ) : ℝ :=
  R * (1 / 2 : ℝ) ^ (n : ℝ)

theorem smallContrastDyadicRadius_zero (R : ℝ) :
    smallContrastDyadicRadius R 0 = R := by
  simp [smallContrastDyadicRadius]

theorem smallContrastDyadicRadius_pos {R : ℝ} (hR : 0 < R) (n : ℕ) :
    0 < smallContrastDyadicRadius R n := by
  exact mul_pos hR (Real.rpow_pos_of_pos (by norm_num) _)

theorem smallContrastDyadicRadius_succ (R : ℝ) (n : ℕ) :
    smallContrastDyadicRadius R (n + 1) =
      smallContrastDyadicRadius R n / 2 := by
  rw [smallContrastDyadicRadius, smallContrastDyadicRadius,
    Nat.cast_add, Nat.cast_one, Real.rpow_add (by norm_num : (0 : ℝ) < 1 / 2)]
  norm_num
  ring

theorem smallContrastDyadicRadius_le {R : ℝ} (hR : 0 ≤ R) (n : ℕ) :
    smallContrastDyadicRadius R n ≤ R := by
  have hpow : (1 / 2 : ℝ) ^ (n : ℝ) ≤ 1 := by
    exact Real.rpow_le_one (by norm_num) (by norm_num) (Nat.cast_nonneg n)
  simpa [smallContrastDyadicRadius] using mul_le_mul_of_nonneg_left hpow hR

/-- Scale-weight factorization at one dyadic step. -/
theorem smallContrastDyadicRadius_succ_rpow {R alpha : ℝ}
    (hR : 0 ≤ R) (n : ℕ) :
    smallContrastDyadicRadius R (n + 1) ^ (1 - alpha) =
      (1 / 2 : ℝ) ^ (1 - alpha) *
        smallContrastDyadicRadius R n ^ (1 - alpha) := by
  rw [smallContrastDyadicRadius_succ]
  have hrn : 0 ≤ smallContrastDyadicRadius R n :=
    mul_nonneg hR (Real.rpow_nonneg (by norm_num) _)
  rw [show smallContrastDyadicRadius R n / 2 =
      (1 / 2 : ℝ) * smallContrastDyadicRadius R n by ring,
    Real.mul_rpow (by norm_num) hrn]

/-- Cancellation of the source scaling `r^{1-alpha} r^{-d/p}`. -/
theorem smallContrast_source_scale_cancel {d : ℕ} {alpha r : ℝ}
    (hd : 1 ≤ d) (halpha : alpha < 1) (hr : 0 < r) :
    r ^ (1 - alpha) *
        r ^ (-(d : ℝ) / schauderSourceExponent d alpha) = 1 := by
  have hdim := dimension_div_schauderSourceExponent hd halpha
  rw [← Real.rpow_add hr]
  rw [show -(d : ℝ) / schauderSourceExponent d alpha =
      -((d : ℝ) / schauderSourceExponent d alpha) by ring, hdim]
  ring_nf
  exact Real.rpow_zero r

/-- On the exponent range `[1/2,1)`, the half-scale source coefficient is bounded by a
dimension-only quantity. -/
theorem half_source_coefficient_le_dimension_only {d : ℕ} {alpha : ℝ}
    (halpha : alpha < 1) :
    2 * (1 / 2 : ℝ) ^ (-(d : ℝ) / 2) *
        (1 / 2 : ℝ) ^ (1 - alpha) ≤
      2 * (1 / 2 : ℝ) ^ (-(d : ℝ) / 2) := by
  have hgap : 0 ≤ 1 - alpha := sub_nonneg.mpr halpha.le
  have hhalf : (1 / 2 : ℝ) ^ (1 - alpha) ≤ 1 :=
    Real.rpow_le_one (by norm_num) (by norm_num) hgap
  let A : ℝ := 2 * (1 / 2 : ℝ) ^ (-(d : ℝ) / 2)
  have hA : 0 ≤ A :=
    mul_nonneg (by norm_num) (Real.rpow_nonneg (by norm_num) _)
  change A * (1 / 2 : ℝ) ^ (1 - alpha) ≤ A
  calc
    A * (1 / 2 : ℝ) ^ (1 - alpha) ≤ A * 1 :=
      mul_le_mul_of_nonneg_left hhalf hA
    _ = A := mul_one A

end

end Algsuperdiff.StochasticProcess.Common.Regularity.Ported
