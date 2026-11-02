/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.NumberFields.ArithmeticLogDerivativeSupport
public import LeanPool.NairTenenbaum.NumberFields.IdealVonMangoldtLocal
public import Mathlib.NumberTheory.Chebyshev

/-! # Global bounds for the ideal von Mangoldt function

The local residue-degree formula and prime-power support compare the ideal
von Mangoldt function pointwise with the ordinary one. Chebyshev's estimate
then gives a linear bound for its summatory function.
-/

@[expose] public section

namespace NairTenenbaum

open Finset ArithmeticFunction NumberField

variable (K : Type*) [Field K] [NumberField K]

theorem idealVonMangoldt_eq_zero_of_not_primePower {n : ℕ} (hn : ¬ IsPrimePow n) :
    idealVonMangoldt K n = 0 :=
  arithmeticLogDerivative_eq_zero_of_not_primePower (idealNormArithmetic_isMultiplicative K)
    (idealNormInverse_isMultiplicative K) (idealNormArithmetic_mul_inverse K) hn

theorem idealVonMangoldt_nonneg (n : ℕ) : 0 ≤ idealVonMangoldt K n := by
  by_cases hn : IsPrimePow n
  · obtain ⟨p, k, hp, _, rfl⟩ := (isPrimePow_nat_iff n).mp hn
    exact idealVonMangoldt_prime_pow_nonneg K hp k
  · rw [idealVonMangoldt_eq_zero_of_not_primePower K hn]

theorem idealVonMangoldt_le_degree_mul (n : ℕ) :
    idealVonMangoldt K n ≤ (Module.finrank ℚ K : ℝ) * vonMangoldt n := by
  by_cases hn : IsPrimePow n
  · obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff n).mp hn
    rw [vonMangoldt_apply_pow hk.ne', vonMangoldt_apply_prime hp]
    exact idealVonMangoldt_prime_pow_le K hp hk.ne'
  · rw [idealVonMangoldt_eq_zero_of_not_primePower K hn]
    exact mul_nonneg (Nat.cast_nonneg _) vonMangoldt_nonneg

theorem idealVonMangoldt_summatory_le_psi (x : ℝ) :
    arithmeticSummatory (idealVonMangoldt K) x ≤ (Module.finrank ℚ K : ℝ) * Chebyshev.psi x := by
  rw [arithmeticSummatory, Chebyshev.psi, ← Icc_succ_left_eq_Ioc, mul_sum]
  exact sum_le_sum (fun n _ => idealVonMangoldt_le_degree_mul K n)

theorem idealVonMangoldt_summatory_le {x : ℝ} (hx : 0 ≤ x) :
    arithmeticSummatory (idealVonMangoldt K) x ≤
      ((Module.finrank ℚ K : ℝ) * (Real.log 4 + 4)) * x := by
  calc
    _ ≤ (Module.finrank ℚ K : ℝ) * Chebyshev.psi x :=
      idealVonMangoldt_summatory_le_psi K x
    _ ≤ (Module.finrank ℚ K : ℝ) * ((Real.log 4 + 4) * x) :=
      mul_le_mul_of_nonneg_left (Chebyshev.psi_le_const_mul_self hx) (Nat.cast_nonneg _)
    _ = _ := (mul_assoc _ _ _).symm

end NairTenenbaum
