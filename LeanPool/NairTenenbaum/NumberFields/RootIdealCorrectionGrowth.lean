/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.NumberFields.DirichletInverseGrowth
public import LeanPool.NairTenenbaum.NumberFields.IdealPrimePowerCountBound
public import LeanPool.NairTenenbaum.NumberFields.RootIdealCorrection
public import LeanPool.NairTenenbaum.Polynomials.PrimitiveResidueRoots

/-! # Uniform coefficient bounds for the root/ideal convolution correction -/

@[expose] public section

namespace NairTenenbaum

open Polynomial NumberField ArithmeticFunction

variable (K : Type*) [Field K] [NumberField K]

theorem idealNormArithmetic_prime_pow_exponential_bound {p : ℕ} (hp : p.Prime) (k : ℕ) :
    |idealNormArithmetic K (p ^ k)| ≤ ((2 : ℝ) ^ Module.finrank ℚ K) ^ k := by
  rw [idealNormArithmetic_apply_pos K (pow_pos hp.pos _), abs_of_nonneg (Nat.cast_nonneg _)]
  have H := idealNormCount_prime_pow_le (K := K) (k := k) hp
  have H' : (k + 1) ^ Module.finrank ℚ K ≤ (2 ^ Module.finrank ℚ K) ^ k := by
    calc
      _ ≤ (2 ^ k) ^ Module.finrank ℚ K := Nat.pow_le_pow_left Nat.lt_two_pow_self _
      _ = _ := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  exact_mod_cast H.trans H'

theorem idealNormInverse_prime_pow_exponential_bound {p : ℕ} (hp : p.Prime) (k : ℕ) :
    |idealNormInverse K (p ^ k)| ≤ (2 * (2 : ℝ) ^ Module.finrank ℚ K) ^ k :=
  inverse_prime_pow_exponential_bound (idealNormArithmetic_isMultiplicative K).1
    (idealNormArithmetic_mul_inverse K) hp (by positivity)
    (idealNormArithmetic_prime_pow_exponential_bound K hp) k

theorem squarefreeRootArithmetic_prime_pow_exponential_bound {Q : ℤ[X]}
    (hQ : Q.IsPrimitive) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    |squarefreeRootArithmetic Q (p ^ k)| ≤ (Q.natDegree + 1 : ℝ) ^ k := by
  by_cases hk0 : k = 0
  · simp [hk0, (squarefreeRootArithmetic_isMultiplicative Q).1]
  by_cases hk1 : k = 1
  · rw [hk1, pow_one, squarefreeRootArithmetic_prime Q hp, abs_of_nonneg (Nat.cast_nonneg _),
      pow_one]
    have H : (rootCount Q p : ℝ) ≤ Q.natDegree := by
      exact_mod_cast primitive_rootCount_le_degree hQ hp
    linarith
  · have H : ¬ Squarefree (p ^ k) := by simp [Nat.squarefree_pow_iff hp.ne_one hk0, hk1]
    simp only [squarefreeRootArithmetic, coe_mk, H, ↓reduceIte, abs_zero]
    positivity

/-- A uniform growth constant for the root/ideal correction coefficients. -/
noncomputable def rootIdealCorrectionGrowthConstant (Q : ℤ[X]) : ℝ :=
  2 * max (Q.natDegree + 1 : ℝ) (2 * (2 : ℝ) ^ Module.finrank ℚ K)

theorem rootIdealCorrectionGrowthConstant_pos (Q : ℤ[X]) :
    0 < rootIdealCorrectionGrowthConstant K Q := by
  unfold rootIdealCorrectionGrowthConstant
  have H : 0 < (Q.natDegree + 1 : ℝ) := by positivity
  exact mul_pos (by norm_num) (H.trans_le (le_max_left _ _))

theorem rootIdealCorrection_prime_pow_exponential_bound {Q : ℤ[X]} (hQ : Q.IsPrimitive)
    {p : ℕ} (hp : p.Prime) (k : ℕ) :
    |rootIdealCorrection K Q (p ^ k)| ≤ rootIdealCorrectionGrowthConstant K Q ^ k := by
  apply convolution_prime_pow_exponential_bound hp
    (le_trans (by positivity : (0 : ℝ) ≤ Q.natDegree + 1) (le_max_left _ _))
  · intro j
    exact (squarefreeRootArithmetic_prime_pow_exponential_bound hQ hp j).trans
      (pow_le_pow_left₀ (by positivity) (le_max_left _ _) j)
  · intro j
    exact (idealNormInverse_prime_pow_exponential_bound K hp j).trans
      (pow_le_pow_left₀ (by positivity) (le_max_right _ _) j)

end NairTenenbaum
