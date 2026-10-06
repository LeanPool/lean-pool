/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.ProfileRowMeanEstimates

/-!
# High-contrast homogenization: Provider.Response.PreYoungBoundaryNormalization

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Boundary-row normalization

The child--parent energy uses the half-energy normalization.  Consequently,
each of the two coordinate rows carries `sqrt (4 * tau)`.  Their half-sum is
still controlled by the standard `sqrt 2 * sqrt tau` Schur-load coefficient.
-/

namespace HCPolySupport.HighContrast.Response

open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- Two coordinate-row estimates with the half-energy normalization combine
into the standard boundary-mean estimate. -/
theorem abs_boundaryMean_le_of_four_mul_responseDefect
    {tau gain meanGrad meanFlux : ℝ} {row : ℝ≥0∞}
    {H : BlockMat d} {Pcen Qcen : Vec d}
    (hgradRow :
      ENNReal.ofReal |meanGrad| ≤
        ENNReal.ofReal (Real.sqrt (4 * tau) * profileSchurLoadFlux H Qcen) +
          ENNReal.ofReal gain * row ^ (1 / 2 : ℝ))
    (hfluxRow :
      ENNReal.ofReal |meanFlux| ≤
        ENNReal.ofReal (Real.sqrt (4 * tau) * profileSchurLoadGradient H Pcen) +
          ENNReal.ofReal gain * row ^ (1 / 2 : ℝ)) :
    ENNReal.ofReal ((1 / 2 : ℝ) * |meanGrad + meanFlux|) ≤
      ENNReal.ofReal (Real.sqrt 2 * Real.sqrt tau *
          Real.sqrt (profileSchurLoad H Pcen Qcen)) +
        ENNReal.ofReal gain * row ^ (1 / 2 : ℝ) := by
  set c : ℝ≥0∞ := ENNReal.ofReal gain * row ^ (1 / 2 : ℝ) with hc
  set A : ℝ := Real.sqrt 2 * Real.sqrt tau *
    Real.sqrt (profileSchurLoad H Pcen Qcen) with hA
  have hfluxHalf := profileSchurLoadFlux_nonneg H Qcen
  have hgradHalf := profileSchurLoadGradient_nonneg H Pcen
  have hsqrtFour : Real.sqrt (4 * tau) = 2 * Real.sqrt tau := by
    calc
      Real.sqrt (4 * tau) = Real.sqrt 4 * Real.sqrt tau :=
        Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4) tau
      _ = 2 * Real.sqrt tau :=
        congrArg (fun x : ℝ ↦ x * Real.sqrt tau)
          (by
            rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num,
              Real.sqrt_sq_eq_abs]
            norm_num)
  have hsqrtTwo : (1 : ℝ) ≤ Real.sqrt 2 :=
    Real.one_le_sqrt.mpr (by norm_num)
  have hloadNonneg :
      0 ≤ Real.sqrt tau * Real.sqrt (profileSchurLoad H Pcen Qcen) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hsplit :
      Real.sqrt (4 * tau) * profileSchurLoadFlux H Qcen +
          Real.sqrt (4 * tau) * profileSchurLoadGradient H Pcen ≤ 2 * A := by
    rw [hsqrtFour, ← mul_add, ← sqrt_profileSchurLoad H Pcen Qcen]
    calc
      2 * Real.sqrt tau * Real.sqrt (profileSchurLoad H Pcen Qcen) =
          2 * (Real.sqrt tau * Real.sqrt (profileSchurLoad H Pcen Qcen)) := by
        ring
      _ ≤
          2 * (Real.sqrt 2 *
            (Real.sqrt tau * Real.sqrt (profileSchurLoad H Pcen Qcen))) :=
        mul_le_mul_of_nonneg_left (by
          simpa only [one_mul] using
            mul_le_mul_of_nonneg_right hsqrtTwo hloadNonneg) (by norm_num)
      _ = 2 * A := by rw [hA]; ring
  have hsum : ENNReal.ofReal |meanGrad + meanFlux| ≤
      ENNReal.ofReal (2 * A) + (c + c) := by
    calc
      ENNReal.ofReal |meanGrad + meanFlux| ≤
          ENNReal.ofReal (|meanGrad| + |meanFlux|) :=
        ENNReal.ofReal_le_ofReal (abs_add_le _ _)
      _ = ENNReal.ofReal |meanGrad| + ENNReal.ofReal |meanFlux| :=
        ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)
      _ ≤ (ENNReal.ofReal
              (Real.sqrt (4 * tau) * profileSchurLoadFlux H Qcen) + c) +
            (ENNReal.ofReal
              (Real.sqrt (4 * tau) * profileSchurLoadGradient H Pcen) + c) :=
        add_le_add hgradRow hfluxRow
      _ = (ENNReal.ofReal
              (Real.sqrt (4 * tau) * profileSchurLoadFlux H Qcen) +
            ENNReal.ofReal
              (Real.sqrt (4 * tau) * profileSchurLoadGradient H Pcen)) +
            (c + c) := by ring
      _ = ENNReal.ofReal
              (Real.sqrt (4 * tau) * profileSchurLoadFlux H Qcen +
                Real.sqrt (4 * tau) * profileSchurLoadGradient H Pcen) +
            (c + c) := by
        rw [ENNReal.ofReal_add
          (mul_nonneg (Real.sqrt_nonneg _) hfluxHalf)
          (mul_nonneg (Real.sqrt_nonneg _) hgradHalf)]
      _ ≤ ENNReal.ofReal (2 * A) + (c + c) :=
        add_le_add (ENNReal.ofReal_le_ofReal hsplit) le_rfl
  have htwo : ENNReal.ofReal (2 : ℝ) = 2 := by norm_num
  have hhalfTwo : ENNReal.ofReal (1 / 2 : ℝ) * 2 = 1 := by
    rw [← htwo, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    norm_num
  have hnormalize :
      ENNReal.ofReal (1 / 2 : ℝ) * ENNReal.ofReal (2 * A) +
          ENNReal.ofReal (1 / 2 : ℝ) * (c + c) = ENNReal.ofReal A + c := by
    have hfirst : ENNReal.ofReal (1 / 2 : ℝ) * ENNReal.ofReal (2 * A) =
        ENNReal.ofReal A := by
      rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      congr 1
      ring
    have hsecond : ENNReal.ofReal (1 / 2 : ℝ) * (c + c) = c := by
      rw [← two_mul, ← mul_assoc, hhalfTwo, one_mul]
    rw [hfirst, hsecond]
  calc
    ENNReal.ofReal ((1 / 2 : ℝ) * |meanGrad + meanFlux|) =
        ENNReal.ofReal (1 / 2 : ℝ) * ENNReal.ofReal |meanGrad + meanFlux| :=
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)
    _ ≤ ENNReal.ofReal (1 / 2 : ℝ) *
          (ENNReal.ofReal (2 * A) + (c + c)) :=
      mul_le_mul' le_rfl hsum
    _ = ENNReal.ofReal (1 / 2 : ℝ) * ENNReal.ofReal (2 * A) +
          ENNReal.ofReal (1 / 2 : ℝ) * (c + c) := mul_add _ _ _
    _ = ENNReal.ofReal A + c := hnormalize

end

end HCPolySupport.HighContrast.Response
