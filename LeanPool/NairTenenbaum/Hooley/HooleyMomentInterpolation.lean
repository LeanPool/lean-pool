/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.Hooley.HooleyMomentComparison
import Mathlib.Tactic.Positivity

/-! # Interpolation of Hooley's integral moments

Weighted arithmetic-geometric means give the interpolation between `M₁=τ`
and `M_q`. This supplies the exponents of `τ` and `M_q` in the mixed-term
estimate used in the weighted mean proof.
-/

@[expose] public section

namespace NairTenenbaum

open Finset Real MeasureTheory

theorem moment_interpolation_pointwise {x A B a b : ℝ} {j q : ℕ}
    (hx : 0 ≤ x) (hA : 0 < A) (hB : 0 < B) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) (hexp : a + (q : ℝ) * b = j) (hj : 0 < j) :
    x ^ j ≤ A ^ a * B ^ b * (a * (x / A) + b * (x ^ q / B)) := by
  by_cases hx₀ : x = 0
  · rw [hx₀, zero_pow hj.ne']
    positivity
  have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx₀)
  have H := mul_le_mul_of_nonneg_left
    (Real.geom_mean_le_arith_mean2_weighted ha hb (div_nonneg hx hA.le)
      (div_nonneg (pow_nonneg hx q) hB.le) hab)
    (show 0 ≤ A ^ a * B ^ b by positivity)
  have hAp : A ^ a ≠ 0 := (Real.rpow_pos_of_pos hA a).ne'
  have hBp : B ^ b ≠ 0 := (Real.rpow_pos_of_pos hB b).ne'
  have Hpower : (x ^ q) ^ b = x ^ ((q : ℝ) * b) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  have Heq : A ^ a * B ^ b * ((x / A) ^ a * (x ^ q / B) ^ b) = x ^ j := by
    rw [Real.div_rpow hx hA.le, Real.div_rpow (pow_nonneg hx q) hB.le, Hpower]
    calc
      _ = x ^ a * x ^ ((q : ℝ) * b) := by field_simp
      _ = x ^ j := by rw [← Real.rpow_add hxpos, hexp, Real.rpow_natCast]
  rw [Heq] at H
  exact H

theorem hooleyMoment_interpolation (n : ℕ) {j q : ℕ}
    (hq : 1 < q) (hj : 1 ≤ j) (hjq : j ≤ q) :
    hooleyMoment j n ≤ (n.divisors.card : ℝ) ^ (((q : ℝ) - j) / ((q : ℝ) - 1)) *
      hooleyMoment q n ^ (((j : ℝ) - 1) / ((q : ℝ) - 1)) := by
  by_cases hn : n = 0
  · subst n
    rw [hooleyMoment_at_zero (by omega : 0 < j)]
    exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      (Real.rpow_nonneg (hooleyMoment_nonneg q 0) _)
  have hqR : (1 : ℝ) < q := by exact_mod_cast hq
  have hjR : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hjqR : (j : ℝ) ≤ q := by exact_mod_cast hjq
  let a : ℝ := ((q : ℝ) - j) / ((q : ℝ) - 1)
  let b : ℝ := ((j : ℝ) - 1) / ((q : ℝ) - 1)
  have ha : 0 ≤ a := div_nonneg (by linarith) (by linarith)
  have hb : 0 ≤ b := div_nonneg (by linarith) (by linarith)
  have hden : (q : ℝ) - 1 ≠ 0 := sub_ne_zero.mpr hqR.ne'
  have hab : a + b = 1 := by
    dsimp [a, b]
    rw [← add_div]
    apply (div_eq_iff hden).mpr
    ring
  have hexp : a + (q : ℝ) * b = j := by
    dsimp [a, b]
    rw [← mul_div_assoc, ← add_div]
    apply (div_eq_iff hden).mpr
    ring
  have hτ : (0 : ℝ) < n.divisors.card := by
    exact_mod_cast (card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr hn⟩ : 0 < n.divisors.card)
  have hM : 0 < hooleyMoment q n := hooleyMoment_pos hn (by omega)
  have hi₁ := ((integrable_hooleyWindow n).div_const (n.divisors.card : ℝ)).const_mul a
  have hi₂ := ((integrable_hooleyWindow_pow n (show 0 < q by omega)).div_const
    (hooleyMoment q n)).const_mul b
  have H := integral_mono (integrable_hooleyWindow_pow n (show 0 < j by omega))
    ((hi₁.add hi₂).const_mul ((n.divisors.card : ℝ) ^ a * hooleyMoment q n ^ b))
    (fun u => moment_interpolation_pointwise (hooleyWindow_nonneg n u) hτ hM ha hb hab hexp (by
      omega))
  simp only [Pi.add_apply] at H
  rw [integral_const_mul, integral_add hi₁ hi₂] at H
  simp only [integral_const_mul, integral_div, integral_hooleyWindow] at H
  change hooleyMoment j n ≤ (n.divisors.card : ℝ) ^ a * hooleyMoment q n ^ b *
    (a * ((n.divisors.card : ℝ) / n.divisors.card) + b * (hooleyMoment q n / hooleyMoment q n)) at H
  simpa only [div_self hτ.ne', div_self hM.ne', mul_one, hab, a, b] using H

/-- The product of the complementary moments has exponents independent
of the binomial index. -/
theorem hooleyMoment_mixedProduct_le (n : ℕ) {j q : ℕ}
    (hq : 1 < q) (hj : 1 ≤ j) (hjq : j < q) :
    hooleyMoment j n * hooleyMoment (q - j) n ≤
      (n.divisors.card : ℝ) ^ ((q : ℝ) / ((q : ℝ) - 1)) *
        hooleyMoment q n ^ (((q : ℝ) - 2) / ((q : ℝ) - 1)) := by
  by_cases hn : n = 0
  · subst n
    rw [hooleyMoment_at_zero (by omega : 0 < j), zero_mul]
    exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      (Real.rpow_nonneg (hooleyMoment_nonneg q 0) _)
  have hτ : (0 : ℝ) < n.divisors.card := by
    exact_mod_cast (card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr hn⟩ : 0 < n.divisors.card)
  have hM : 0 < hooleyMoment q n := hooleyMoment_pos hn (by omega)
  have H := mul_le_mul (hooleyMoment_interpolation n hq hj hjq.le)
    (hooleyMoment_interpolation n hq (by omega : 1 ≤ q - j) (Nat.sub_le _ _))
    (hooleyMoment_nonneg _ _) (mul_nonneg (Real.rpow_nonneg hτ.le _) (Real.rpow_nonneg hM.le _))
  apply H.trans_eq
  rw [mul_mul_mul_comm, ← Real.rpow_add hτ, ← Real.rpow_add hM, Nat.cast_sub hjq.le]
  congr 2 <;> ring

end NairTenenbaum
