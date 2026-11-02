/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Arithmetic.CompleteResidueBlock
public import LeanPool.NairTenenbaum.DivisorSums.DivisorWindowMoments

/-! # Double counting polynomial divisors in a dyadic window -/

@[expose] public section

namespace NairTenenbaum

open Finset Real Polynomial

theorem dyadicDivisorCount_eq_congruence_filter {n : ℕ} (hn : n ≠ 0) {y : ℝ} (hy : 0 ≤ y) :
    dyadicDivisorCount n y = ((shortInterval (y / 2) (y / 2)).filter (fun d => d ∣ n)).card := by
  unfold dyadicDivisorCount
  congr 1
  ext d
  simp only [shortInterval, mem_filter, Nat.mem_divisors, mem_Ioc,
    Nat.floor_lt (div_nonneg hy (by
      norm_num : (0 : ℝ) ≤ 2)), Nat.le_floor_iff (by linarith : 0 ≤ y / 2 + y / 2)]
  rw [show y / 2 + y / 2 = y by ring]
  tauto

theorem polynomialDivisorWindowSum_eq_congruence_sum (Q : ℤ[X]) {x y : ℝ} (hy : 0 ≤ y)
    (hQ : ∀ n ∈ shortInterval x y, Q.eval (n : ℤ) ≠ 0) :
    polynomialDivisorWindowSum Q x y =
      ∑ d ∈ shortInterval (y / 2) (y / 2),
        (((shortInterval x y).filter (fun n : ℕ => d ∣ (Q.eval (n : ℤ)).natAbs)).card : ℝ) := by
  classical
  unfold polynomialDivisorWindowSum
  have H (n : ℕ) (hn : n ∈ shortInterval x y) :=
    dyadicDivisorCount_eq_congruence_filter (Int.natAbs_ne_zero.mpr (hQ n hn)) hy
  simp_rw [sum_congr rfl (fun n hn => congrArg (fun k : ℕ => (k : ℝ)) (H n hn))]
  simp_rw [card_eq_sum_ones, Nat.cast_sum, Nat.cast_one, sum_filter]
  rw [sum_comm]

theorem polynomialDivisorWindowSum_ge_rootCount_sum (Q : ℤ[X]) {x y : ℝ}
    (hx : 0 ≤ x) (hy : 0 < y) (hQ : ∀ n ∈ shortInterval x y, Q.eval (n : ℤ) ≠ 0) :
    (∑ d ∈ shortInterval (y / 2) (y / 2), (rootCount Q d : ℝ)) ≤ polynomialDivisorWindowSum Q x y
        := by
  rw [polynomialDivisorWindowSum_eq_congruence_sum Q hy.le hQ]
  apply sum_le_sum
  intro d hd
  have hd₀ : 0 < d := by have HH := (mem_Ioc.mp hd).1; omega
  have hdy : (d : ℝ) ≤ y := by
    have HH := (Nat.le_floor_iff (by linarith : 0 ≤ y / 2 + y / 2)).mp (mem_Ioc.mp hd).2
    linarith
  exact_mod_cast shortInterval_polynomial_congruence_count_ge Q hx hd₀ hdy

/-- The sum of root densities over the dyadic interval above half the cutoff. -/
noncomputable def dyadicRootDensitySum (Q : ℤ[X]) (y : ℝ) : ℝ :=
  ∑ d ∈ shortInterval (y / 2) (y / 2), (rootCount Q d : ℝ) / d

theorem polynomialDivisorWindowSum_ge_rootDensity (Q : ℤ[X]) {x y : ℝ}
    (hx : 0 ≤ x) (hy : 0 < y) (hQ : ∀ n ∈ shortInterval x y, Q.eval (n : ℤ) ≠ 0) :
    (y / 2) * dyadicRootDensitySum Q y ≤ polynomialDivisorWindowSum Q x y := by
  apply le_trans _ (polynomialDivisorWindowSum_ge_rootCount_sum Q hx hy hQ)
  unfold dyadicRootDensitySum
  rw [mul_sum]
  apply sum_le_sum
  intro d hd
  have hdy : y / 2 < (d : ℝ) := (Nat.floor_lt (half_pos hy).le).mp (mem_Ioc.mp hd).1
  have hd₀ : (0 : ℝ) < d := (half_pos hy).trans hdy
  have HH := mul_le_mul_of_nonneg_right hdy.le (div_nonneg (Nat.cast_nonneg (rootCount Q d)) hd₀.le)
  simpa only [mul_div_cancel₀ _ hd₀.ne'] using HH

theorem exists_polynomial_eval_nonzero_on_shortInterval {Q : ℤ[X]} (hQ : Q ≠ 0) :
    ∃ x₀ : ℝ, 0 ≤ x₀ ∧ ∀ x y : ℝ, x₀ < x → ∀ n ∈ shortInterval x y, Q.eval (n : ℤ) ≠ 0 := by
  obtain ⟨b, hb⟩ := Q.exists_max_root hQ
  refine ⟨max 0 (b : ℝ), le_max_left _ _, fun x y hx n hn hzero => ?_⟩
  have hx₀ : 0 ≤ x := (le_max_left _ _).trans hx.le
  have hxn : x < (n : ℝ) := (Nat.floor_lt hx₀).mp (mem_Ioc.mp hn).1
  have H := hb (n : ℤ) hzero
  have H' : (n : ℝ) ≤ (b : ℝ) := by exact_mod_cast H
  have hb₀ := le_max_right (0 : ℝ) (b : ℝ)
  linarith

end NairTenenbaum
