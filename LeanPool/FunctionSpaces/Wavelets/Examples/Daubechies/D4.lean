/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Wavelets.Examples.Daubechies.Mask

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# The Daubechies mask D4

The Daubechies wavelet D4 comes from the mask of order `N = 2` (`Daubechies.d4`) with the
polynomial factor

`L(z) = a + b z`,  `a = (1 + √3)/2`,  `b = (1 - √3)/2`,

whose root `z = 2 + √3` lies outside the unit disk. The conditions of a mask
(`Daubechies.Mask`) are `deg L = 1 < 2`, `L(1) = a + b = 1`, and, for `z = e^(-2πiξ)`,

`|L(z)|² = a² + b² + 2ab cos(2πξ) = 2 - cos(2πξ) = 1 + 2 sin²(πξ) = P(ξ)`,

since `a² + b² = 2` and `2ab = -1` (`Daubechies.normSq_add_mul_expFreq`,
`Daubechies.daubFun_two_eq_two_sub_cos`). The mask polynomial is

`m(z) = ((1 + z)/2)² L(z) = ((1 + √3) + (3 + √3) z + (3 - √3) z² + (1 - √3) z³)/8`

(`Daubechies.maskPoly_d4`), so the four filter coefficients are

`c_0 = (1 + √3)/4`, `c_1 = (3 + √3)/4`, `c_2 = (3 - √3)/4`, `c_3 = (1 - √3)/4`

(`Daubechies.coeff_d4`), and `c_k = 0` for every other `k ∈ ℤ` (`Daubechies.coeff_d4_eq_zero`).
They are normalised by `∑_k c_k = 2`; the orthonormal filter `h_k = c_k/√2` is the form in which
the coefficients are usually tabulated.
-/

@[expose] public section

open Polynomial
open scoped Real

namespace Daubechies

/-- **A real linear polynomial on the unit circle**: for real `a, b` and `ξ`,
`|a + b e^(-2πiξ)|² = a² + b² + 2ab cos(2πξ)`. This is `|a + b z|² = a² + b² |z|² + 2ab Re z`
with `|z| = 1` and `Re z = cos(2πξ)`. -/
theorem normSq_add_mul_expFreq (a b ξ : ℝ) :
    ‖(a : ℂ) + b * expFreq ξ‖ ^ 2 = a ^ 2 + b ^ 2 + 2 * a * b * Real.cos (2 * π * ξ) := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, expFreq_re, expFreq_im]
  linear_combination b ^ 2 * Real.sin_sq_add_cos_sq (2 * π * ξ)

/-- For `N = 2` the trigonometric Daubechies polynomial is `P(ξ) = 2 - cos(2πξ)`: by
`Daubechies.daubFun_two`, `P(ξ) = 1 + 2 sin²(πξ)`, and `cos(2πξ) = 1 - 2 sin²(πξ)`. -/
theorem daubFun_two_eq_two_sub_cos (ξ : ℝ) : daubFun 2 ξ = 2 - Real.cos (2 * π * ξ) := by
  rw [daubFun_two, show 2 * π * ξ = 2 * (π * ξ) by ring, Real.cos_two_mul', Real.cos_sq']
  ring

/-- **The Daubechies mask D4**, the mask of order `N = 2` with the polynomial factor
`L(z) = (1 + √3)/2 + ((1 - √3)/2) z` (`Daubechies.d4_L`). Its filter coefficients are
`c_0, …, c_3 = (1 + √3)/4, (3 + √3)/4, (3 - √3)/4, (1 - √3)/4` (`Daubechies.coeff_d4`). The
condition `|L(e^(-2πiξ))|² = P(ξ)` holds since both sides equal `2 - cos(2πξ)`
(`Daubechies.normSq_add_mul_expFreq`, `Daubechies.daubFun_two_eq_two_sub_cos`). -/
noncomputable def d4 : Mask 2 where
  L := C ((1 + √3) / 2) + C ((1 - √3) / 2) * X
  natDegree_L_lt := Nat.lt_succ_of_le <| natDegree_add_le_of_degree_le
    ((natDegree_C _).trans_le zero_le_one) ((natDegree_C_mul_le _ _).trans natDegree_X_le)
  eval_L_one := by
    simp only [eval_add, eval_C, eval_mul, eval_X]
    ring
  normSq_L ξ := by
    have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    rw [map_add, map_mul, aeval_C, aeval_C, aeval_X, Complex.coe_algebraMap,
      normSq_add_mul_expFreq, daubFun_two_eq_two_sub_cos]
    linear_combination (1 - Real.cos (2 * π * ξ)) / 2 * h3

/-- The polynomial factor of D4 is `L(z) = (1 + √3)/2 + ((1 - √3)/2) z`. -/
theorem d4_L : d4.L = C ((1 + √3) / 2) + C ((1 - √3) / 2) * X :=
  rfl

/-- **The mask polynomial of D4**:
`m(z) = ((1 + z)/2)² L(z) = ((1 + √3) + (3 + √3) z + (3 - √3) z² + (1 - √3) z³)/8`. Two
polynomials over `ℝ` agree once they agree at every real point (Mathlib's
`Polynomial.funext`), and pointwise this is the expansion of
`(1 + 2x + x²)(a + bx)/4` with `a = (1 + √3)/2`, `b = (1 - √3)/2`. -/
theorem maskPoly_d4 :
    maskPoly d4 = C ((1 + √3) / 8) + C ((3 + √3) / 8) * X + C ((3 - √3) / 8) * X ^ 2 +
      C ((1 - √3) / 8) * X ^ 3 := by
  refine Polynomial.funext fun x => ?_
  simp only [maskPoly, d4_L, eval_mul, eval_pow, eval_add, eval_C, eval_one, eval_X]
  ring

/-- The filter coefficient `c_0 = (1 + √3)/4` of D4. -/
@[simp]
theorem coeff_d4_zero : coeff d4 0 = (1 + √3) / 4 := by
  simp [coeff, maskPoly_d4]
  ring

/-- The filter coefficient `c_1 = (3 + √3)/4` of D4. -/
@[simp]
theorem coeff_d4_one : coeff d4 1 = (3 + √3) / 4 := by
  simp [coeff, maskPoly_d4]
  ring

/-- The filter coefficient `c_2 = (3 - √3)/4` of D4. -/
@[simp]
theorem coeff_d4_two : coeff d4 2 = (3 - √3) / 4 := by
  simp [coeff, maskPoly_d4]
  ring

/-- The filter coefficient `c_3 = (1 - √3)/4` of D4. -/
@[simp]
theorem coeff_d4_three : coeff d4 3 = (1 - √3) / 4 := by
  simp [coeff, maskPoly_d4]
  ring

/-- **The filter coefficients of D4**:
`c_0 = (1 + √3)/4`, `c_1 = (3 + √3)/4`, `c_2 = (3 - √3)/4`, `c_3 = (1 - √3)/4`. -/
theorem coeff_d4 :
    coeff d4 0 = (1 + √3) / 4 ∧ coeff d4 1 = (3 + √3) / 4 ∧ coeff d4 2 = (3 - √3) / 4 ∧
      coeff d4 3 = (1 - √3) / 4 :=
  ⟨coeff_d4_zero, coeff_d4_one, coeff_d4_two, coeff_d4_three⟩

/-- The filter coefficients of D4 vanish outside `0 ≤ k ≤ 3`: `c_k = 0` for `k < 0` and for
`k ≥ 4` (`Daubechies.coeff_eq_zero` with `2N = 4`). -/
theorem coeff_d4_eq_zero {k : ℤ} (hk : k < 0 ∨ 4 ≤ k) : coeff d4 k = 0 :=
  coeff_eq_zero d4 (by omega)

end Daubechies
