/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.Arithmetic.MultiplicativeCompletion
public import LeanPool.NairTenenbaum.NumberFields.IdealNormMean
public import LeanPool.NairTenenbaum.NumberFields.NumberFieldPrimeNormRoots

/-! # The squarefree-root correction to ideal norm counts

The correction is defined by Dirichlet inversion. Its convolution identity is
exact; at primes away from the conductor, the linear Euler coefficient vanishes.
Absolute summability and positivity of its total are separate analytic tasks.
-/

@[expose] public section

namespace NairTenenbaum

open Finset Polynomial NumberField ArithmeticFunction

/-- The squarefree-supported arithmetic function of polynomial root counts. -/
noncomputable def squarefreeRootArithmetic (Q : ℤ[X]) : ArithmeticFunction ℝ :=
  ⟨fun n => if Squarefree n then (rootCount Q n : ℝ) else 0, by simp⟩

theorem squarefreeRootArithmetic_nonneg (Q : ℤ[X]) (n : ℕ) :
    0 ≤ squarefreeRootArithmetic Q n := by
  simp only [squarefreeRootArithmetic, coe_mk]
  split_ifs <;> positivity

theorem squarefreeRootArithmetic_le_rootCount (Q : ℤ[X]) (n : ℕ) :
    squarefreeRootArithmetic Q n ≤ rootCount Q n := by
  simp only [squarefreeRootArithmetic, coe_mk]
  split_ifs
  · exact le_rfl
  · exact Nat.cast_nonneg _

theorem squarefreeRootArithmetic_isMultiplicative (Q : ℤ[X]) :
    (squarefreeRootArithmetic Q).IsMultiplicative := by
  constructor
  · simp [squarefreeRootArithmetic]
  · intro m n hcop
    simp only [squarefreeRootArithmetic, coe_mk, Nat.squarefree_mul hcop,
      rootCount_mul Q hcop, Nat.cast_mul]
    by_cases hm : Squarefree m <;> by_cases hn : Squarefree n <;> simp [hm, hn]

theorem squarefreeRootArithmetic_prime (Q : ℤ[X]) {p : ℕ} (hp : p.Prime) :
    squarefreeRootArithmetic Q p = rootCount Q p := by
  simp [squarefreeRootArithmetic, hp.squarefree]

theorem arithmeticFunction_mul_prime (f g : ArithmeticFunction ℝ) {p : ℕ} (hp : p.Prime) :
    (f * g) p = f 1 * g p + f p * g 1 := by
  rw [mul_apply, Nat.sum_divisorsAntidiagonal (fun d e => f d * g e)]
  rw [hp.divisors, sum_insert (by simpa using hp.ne_one.symm), sum_singleton]
  simp [Nat.div_self hp.pos]

variable (K : Type*) [Field K] [NumberField K]

/-- The Dirichlet-convolution inverse of the ideal-norm counting function. -/
noncomputable def idealNormInverse : ArithmeticFunction ℝ :=
  dirichletInverse (idealNormArithmetic K)
    (by rw [(idealNormArithmetic_isMultiplicative K).1]; exact invertibleOne)

theorem idealNormArithmetic_mul_inverse : idealNormArithmetic K * idealNormInverse K = 1 :=
  self_mul_dirichletInverse _ _

theorem idealNormInverse_isMultiplicative : (idealNormInverse K).IsMultiplicative :=
  dirichletInverse_isMultiplicative (idealNormArithmetic_isMultiplicative K) _

/-- The convolution correction between squarefree root counts and ideal-norm counts. -/
noncomputable def rootIdealCorrection (Q : ℤ[X]) : ArithmeticFunction ℝ :=
  squarefreeRootArithmetic Q * idealNormInverse K

theorem rootIdealCorrection_isMultiplicative (Q : ℤ[X]) :
    (rootIdealCorrection K Q).IsMultiplicative :=
  (squarefreeRootArithmetic_isMultiplicative Q).mul (idealNormInverse_isMultiplicative K)

theorem rootIdealCorrection_mul_idealNorm (Q : ℤ[X]) :
    rootIdealCorrection K Q * idealNormArithmetic K = squarefreeRootArithmetic Q := by
  unfold rootIdealCorrection
  rw [mul_assoc, mul_comm (idealNormInverse K), idealNormArithmetic_mul_inverse, mul_one]

theorem rootIdealCorrection_prime (Q : ℤ[X]) {p : ℕ} (hp : p.Prime) :
    rootIdealCorrection K Q p = (rootCount Q p : ℝ) - idealNormCount K p := by
  have H := congrArg (fun f : ArithmeticFunction ℝ => f p) (rootIdealCorrection_mul_idealNorm K Q)
  rw [arithmeticFunction_mul_prime _ _ hp, (rootIdealCorrection_isMultiplicative K Q).1,
    (idealNormArithmetic_isMultiplicative K).1, one_mul, mul_one,
    idealNormArithmetic_apply_pos K hp.pos, squarefreeRootArithmetic_prime Q hp] at H
  linarith

end NairTenenbaum
