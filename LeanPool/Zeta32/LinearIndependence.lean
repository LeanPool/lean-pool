/-
Copyright (c) 2026 Qian Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qian Tang
-/
--
module

public import LeanPool.Zeta32.PiSqIrrational
public import Mathlib.NumberTheory.LSeries.HurwitzZetaValues

/-!
# From irrationality of `ζ(3) - r ζ(2)` to `ℚ`-linear independence of `1, ζ(2), ζ(3)`

Main result: `Zeta32.LinearIndependence.linearIndependent_of_irrational`.

* `riemannZeta k` (for `k ≥ 2`) is the complexification of the real series
  `∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ k` (`riemannZeta_nat_eq_ofReal_tsum`).
* `ζ(2) = π ^ 2 / 6` is irrational, by `Zeta32.irrational_pi_sq`.
* A rational relation `a + b ζ(2) + c ζ(3) = 0` with `c ≠ 0` makes
  `ζ(3) - (-b / c) ζ(2) = -a / c` rational; with `c = 0`, `b ≠ 0` it makes `ζ(2)` rational;
  with `b = c = 0` it forces `a = 0`.
-/

public section

open Real

namespace Zeta32.LinearIndependence

/-- For `k ≥ 2`, `riemannZeta k` is the complexification of `∑' n, 1 / (n + 1) ^ k` over `ℝ`. -/
theorem riemannZeta_nat_eq_ofReal_tsum {k : ℕ} (hk : 1 < k) :
    riemannZeta k = ((∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ k : ℝ) : ℂ) := by
  have hs : 1 < ((k : ℂ)).re := by
    simpa using (show (1 : ℝ) < k by exact_mod_cast hk)
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs, Complex.ofReal_tsum]
  congr 1 with n
  rw [Complex.cpow_natCast]
  push_cast
  rfl

theorem riemannZeta_two_eq_ofReal_tsum :
    riemannZeta 2 = ((∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 2 : ℝ) : ℂ) := by
  rw [show (2 : ℂ) = ((2 : ℕ) : ℂ) by norm_num]
  exact riemannZeta_nat_eq_ofReal_tsum (by norm_num)

theorem riemannZeta_three_eq_ofReal_tsum :
    riemannZeta 3 = ((∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 3 : ℝ) : ℂ) := by
  rw [show (3 : ℂ) = ((3 : ℕ) : ℂ) by norm_num]
  exact riemannZeta_nat_eq_ofReal_tsum (by norm_num)

/-- `∑' n, 1 / (n + 1) ^ 2 = π ^ 2 / 6`. -/
theorem tsum_two_eq : (∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 2) = π ^ 2 / 6 := by
  have h := riemannZeta_two_eq_ofReal_tsum.symm.trans riemannZeta_two
  exact_mod_cast h

/-- `ζ(2) = ∑' n, 1 / (n + 1) ^ 2` is irrational. -/
theorem irrational_tsum_two : Irrational (∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 2) := by
  rw [tsum_two_eq]
  have := irrational_pi_sq.div_natCast (m := 6) (by norm_num)
  simpa using this

theorem linearIndependent_of_irrational :
    (∀ r : ℚ, Irrational ((∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ 3) -
      (r : ℝ) * ∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ 2)) →
    LinearIndependent ℚ ![(1 : ℂ), riemannZeta 2, riemannZeta 3] := by
  intro hirr
  have hS2 := irrational_tsum_two
  set S2 : ℝ := ∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ 2 with hS2def
  set S3 : ℝ := ∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ 3 with hS3def
  rw [riemannZeta_two_eq_ofReal_tsum, riemannZeta_three_eq_ofReal_tsum,
    Fintype.linearIndependent_iff]
  intro g hg
  simp only [Fin.sum_univ_three, Rat.smul_def, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, mul_one] at hg
  have hreal : (g 0 : ℝ) + g 1 * S2 + g 2 * S3 = 0 := by
    have : (((g 0 : ℝ) + g 1 * S2 + g 2 * S3 : ℝ) : ℂ) = 0 := by
      push_cast
      linear_combination hg
    exact_mod_cast this
  have hc : g 2 = 0 := by
    by_contra hc
    have hcR : (g 2 : ℝ) ≠ 0 := by exact_mod_cast hc
    apply (hirr (-(g 1) / g 2)).ne_rat (-(g 0) / g 2)
    push_cast
    field_simp
    linear_combination hreal
  have hb : g 1 = 0 := by
    by_contra hb
    have hbR : (g 1 : ℝ) ≠ 0 := by exact_mod_cast hb
    apply hS2.ne_rat (-(g 0) / g 1)
    rw [hc] at hreal
    push_cast at hreal ⊢
    field_simp
    linear_combination hreal
  have ha : g 0 = 0 := by
    rw [hb, hc] at hreal
    push_cast at hreal
    exact_mod_cast (by linarith : (g 0 : ℝ) = 0)
  intro i
  fin_cases i
  · exact ha
  · exact hb
  · exact hc

end Zeta32.LinearIndependence
