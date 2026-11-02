/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Polynomials.PolynomialValueBounds
public import LeanPool.NairTenenbaum.Results.TheoremTwoStatement

/-! # Fixed polynomial-value and prime-cutoff constants for Theorem 2 -/

@[expose] public section

namespace NairTenenbaum

open Polynomial Real Finset

theorem exists_theoremTwo_value_cutoff {Q : ℤ[X]} {k : ℕ} (hk : Q.natDegree < k) :
    ∃ A C : ℝ, 1 ≤ A ∧ 1 ≤ C ∧ A < C ^ k ∧
      (2 ≤ k → 2 * A < C ^ (k - 1)) ∧ ∀ x : ℝ, 1 ≤ x →
      let y : ℝ := x ^ ((Q.natDegree : ℝ) / k)
      ∀ n ∈ shortInterval x y, ((Q.eval (n : ℤ)).natAbs : ℝ) ≤ A * y ^ k := by
  let A : ℝ := max 1 ((polynomialHeight Q : ℝ) * (Q.natDegree + 1) * 2 ^ Q.natDegree)
  have hA : 1 ≤ A := le_max_left _ _
  let C : ℝ := 2 * A + 2
  have hC : 1 ≤ C := by dsimp [C]; linarith
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  refine ⟨A, C, hA, hC, ?_, ?_, fun x hx => ?_⟩
  · have H : C ≤ C ^ k := by simpa using pow_le_pow_right₀ hC (show 1 ≤ k by omega)
    exact (show A < C by dsimp [C]; linarith).trans_le H
  · intro hk2
    have H : C ≤ C ^ (k - 1) := by simpa using pow_le_pow_right₀ hC (show 1 ≤ k - 1 by omega)
    exact (show 2 * A < C by dsimp [C]; linarith).trans_le H
  · let y : ℝ := x ^ ((Q.natDegree : ℝ) / k)
    have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
    have hyx : y ≤ x := Real.rpow_le_self_of_one_le hx
      ((div_le_one hk0).mpr (by exact_mod_cast hk.le))
    have hpow : y ^ k = x ^ Q.natDegree := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le, div_mul_cancel₀ _ hk0.ne', Real.rpow_natCast]
    change ∀ n ∈ shortInterval x y, ((Q.eval (n : ℤ)).natAbs : ℝ) ≤ A * y ^ k
    intro n hn
    have hnx : (n : ℝ) ≤ 2 * x := by
      have H := (Nat.le_floor_iff (show 0 ≤ x + y by dsimp [y]; positivity)).mp (mem_Ioc.mp hn).2
      linarith
    have H := eval_natAbs_le_height_real Q hx (n := (n : ℤ)) (by
      simpa only [Int.natAbs_natCast] using hnx)
    change ((Q.eval (n : ℤ)).natAbs : ℝ) ≤ A * y ^ k
    rw [hpow]
    rw [mul_pow] at H
    have HA := mul_le_mul_of_nonneg_right (le_max_right 1
      ((polynomialHeight Q : ℝ) * (Q.natDegree + 1) * 2 ^ Q.natDegree))
      (pow_nonneg hx0.le Q.natDegree)
    apply H.trans
    convert HA using 1
    ring

end NairTenenbaum
