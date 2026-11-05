/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.Hooley.HooleyShortSum

/-! # Divisor windows and moment truncation for Theorem 2 -/

@[expose] public section

namespace NairTenenbaum

open Finset Real Polynomial

/-- The number of divisors in the dyadic interval above half the cutoff. -/
noncomputable def dyadicDivisorCount (n : ℕ) (y : ℝ) : ℕ :=
  (n.divisors.filter (fun d : ℕ => y / 2 < d ∧ (d : ℝ) ≤ y)).card

/-- The sum of dyadic divisor counts over polynomial values in the short interval. -/
noncomputable def polynomialDivisorWindowSum (Q : ℤ[X]) (x y : ℝ) : ℝ :=
  ∑ n ∈ shortInterval x y, (dyadicDivisorCount (Q.eval (n : ℤ)).natAbs y : ℝ)

/-- The number of polynomial values with at least one divisor in the chosen window. -/
noncomputable def polynomialDivisorHitCount (Q : ℤ[X]) (x y : ℝ) : ℕ :=
  ((shortInterval x y).filter (fun n : ℕ => 0 < dyadicDivisorCount (Q.eval (n : ℤ)).natAbs y)).card

theorem dyadicDivisorCount_le_hooleyDelta (n : ℕ) {y : ℝ} (hy : 0 < y) :
    dyadicDivisorCount n y ≤ hooleyDelta n := by
  have H := dyadic_divisors_le_delta (n := n) (half_pos hy)
  simpa only [dyadicDivisorCount, mul_div_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using H

theorem self_le_inv_rpow_mul_rpow {w T ε : ℝ} (hT : 0 < T) (hw : T ≤ w) (hε : 0 ≤ ε) :
    w ≤ T ^ (-ε) * w ^ (1 + ε) := by
  have hw₀ : 0 < w := hT.trans_le hw
  calc
    w = w ^ (-ε) * w ^ (1 + ε) := by rw [← Real.rpow_add hw₀]; ring_nf; rw [Real.rpow_one]
    _ ≤ _ := mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_nonpos hT hw (by linarith))
      (Real.rpow_nonneg hw₀.le _)

theorem polynomialDivisorWindow_large_sum_le (Q : ℤ[X]) {x y T ε : ℝ}
    (hy : 0 < y) (hT : 0 < T) (hε : 0 ≤ ε) :
    (∑ n ∈ (shortInterval x y).filter
      (fun n : ℕ => T < (dyadicDivisorCount (Q.eval (n : ℤ)).natAbs y : ℝ)),
      (dyadicDivisorCount (Q.eval (n : ℤ)).natAbs y : ℝ)) ≤
      T ^ (-ε) * hooleyPolynomialSum Q (1 + ε) x y := by
  calc
    _ ≤ ∑ n ∈ (shortInterval x y).filter
        (fun n : ℕ => T < (dyadicDivisorCount (Q.eval (n : ℤ)).natAbs y : ℝ)),
        T ^ (-ε) * (hooleyDelta (Q.eval (n : ℤ)).natAbs : ℝ) ^ (1 + ε) := by
      apply sum_le_sum
      intro n hn
      apply (self_le_inv_rpow_mul_rpow hT (mem_filter.mp hn).2.le hε).trans
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hT.le _)
      exact Real.rpow_le_rpow (Nat.cast_nonneg _) (by
        exact_mod_cast dyadicDivisorCount_le_hooleyDelta _ hy) (by linarith)
    _ ≤ ∑ n ∈ shortInterval x y, T ^ (-ε) * (hooleyDelta (Q.eval (n : ℤ)).natAbs : ℝ) ^ (1 + ε) :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun n _ _ => by positivity)
    _ = _ := by rw [← mul_sum]; rfl

theorem polynomialDivisorWindow_small_sum_le (Q : ℤ[X]) (x y : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    (∑ n ∈ (shortInterval x y).filter
      (fun n : ℕ => (dyadicDivisorCount (Q.eval (n : ℤ)).natAbs y : ℝ) ≤ T),
      (dyadicDivisorCount (Q.eval (n : ℤ)).natAbs y : ℝ)) ≤
      T * polynomialDivisorHitCount Q x y := by
  classical
  rw [sum_filter]
  calc
    _ ≤ ∑ n ∈ shortInterval x y,
        if 0 < dyadicDivisorCount (Q.eval (n : ℤ)).natAbs y then T else 0 := by
      apply sum_le_sum
      intro n _
      split_ifs with hsmall hpos hpos
      · exact hsmall
      · have hz : dyadicDivisorCount (Q.eval (n : ℤ)).natAbs y = 0 := by omega
        simp only [hz, Nat.cast_zero, le_refl]
      · exact hT
      · rfl
    _ = _ := by rw [← sum_filter]; simp [polynomialDivisorHitCount, mul_comm]

end NairTenenbaum
