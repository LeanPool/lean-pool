/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Algebra.ScaledHomogenization
public import LeanPool.CCDN.Height.IntegerCoefficientHeight
import LeanPool.CCDN.ForMathlib.MvPolynomial

/-! The exact leading homogeneous coefficient height supplies the full
scaling gain in every dimension. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- For `h ≥ 1`, the scaled homogenization of `f` in degree `d = f.totalDegree` has coefficient
height at least `h ^ d` times the coefficient height of the top homogeneous component of `f`. -/
theorem scaledHomogenize_leading_height_lower {n : ℕ}
    (f : MvPolynomial (Fin n) ℤ) {h : ℤ} (hh : 1 ≤ h) :
    (h : ℝ) ^ f.totalDegree *
        (integerCoefficientHeight (homogeneousComponent f.totalDegree f) : ℝ) ≤
      (integerCoefficientHeight (scaledHomogenize f.totalDegree h f) : ℝ) := by
  have hhR : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hpow : (0 : ℝ) < (h : ℝ) ^ f.totalDegree := by positivity
  have hc : (integerCoefficientHeight (homogeneousComponent f.totalDegree f) : ℝ) ≤
      (integerCoefficientHeight (scaledHomogenize f.totalDegree h f) : ℝ) /
        (h : ℝ) ^ f.totalDegree := by
    apply integerCoefficientHeight_le _ (by positivity)
    intro m
    rw [coeff_homogeneousComponent]
    split_ifs with hm
    · have hm' : m.sum (fun _ e => e) = f.totalDegree := hm
      have he := coefficient_abs_le_integerCoefficientHeight (scaledHomogenize f.totalDegree h f)
        (homogenizedExponent f.totalDegree m)
      rw [scaledHomogenize_coefficient, hm', Int.cast_mul, Int.cast_pow, abs_mul,
        abs_pow, abs_of_nonneg (by linarith : (0 : ℝ) ≤ h)] at he
      exact (le_div_iff₀ hpow).mpr (by simpa only [mul_comm] using he)
    · simp only [Int.cast_zero, abs_zero]
      positivity
  have he := (le_div_iff₀ hpow).mp hc
  simpa only [mul_comm] using he

/-- The top homogeneous component of a nonzero integer polynomial has coefficient height at
least `1`. -/
lemma leading_height_one_le {n : ℕ} (f : MvPolynomial (Fin n) ℤ) (hf : f ≠ 0) :
    (1 : ℝ) ≤ integerCoefficientHeight (homogeneousComponent f.totalDegree f) := by
  exact_mod_cast integerCoefficientHeight_pos _ (homogeneousComponent_totalDegree_ne_zero hf)

end
end CCDN
