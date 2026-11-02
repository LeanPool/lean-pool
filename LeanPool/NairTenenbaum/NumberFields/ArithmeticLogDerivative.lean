/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.NumberFields.IdealLocalEulerPolynomial
public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

/-! # Logarithmic weighting and Dirichlet convolution

Logarithmic weighting is a derivation for Dirichlet convolution. The ideal
von Mangoldt function is the logarithmically weighted ideal count convolved
with its proved Dirichlet inverse.
-/

@[expose] public section

namespace NairTenenbaum

open Finset ArithmeticFunction NumberField

/-- The arithmetic weight obtained by multiplying each value by the logarithm of its index. -/
noncomputable def arithmeticLogWeight (f : ArithmeticFunction ℝ) : ArithmeticFunction ℝ :=
  f.pmul ArithmeticFunction.log

@[simp] theorem arithmeticLogWeight_apply (f : ArithmeticFunction ℝ) (n : ℕ) :
    arithmeticLogWeight f n = f n * Real.log n := rfl

/-- Logarithmic differentiation of an arithmetic function under Dirichlet convolution. -/
noncomputable def arithmeticLogDerivative (f g : ArithmeticFunction ℝ) : ArithmeticFunction ℝ :=
  arithmeticLogWeight f * g

theorem arithmeticLogDerivative_convolution {f g : ArithmeticFunction ℝ} (hfg : f * g = 1) :
    f * arithmeticLogDerivative f g = arithmeticLogWeight f := by
  unfold arithmeticLogDerivative
  calc
    _ = arithmeticLogWeight f * (f * g) := by ring
    _ = _ := by rw [hfg, mul_one]

variable (K : Type*) [Field K] [NumberField K]

/-- The ideal-norm analogue of the von Mangoldt arithmetic function. -/
noncomputable def idealVonMangoldt : ArithmeticFunction ℝ :=
  arithmeticLogDerivative (idealNormArithmetic K) (idealNormInverse K)

theorem idealVonMangoldt_convolution :
    idealNormArithmetic K * idealVonMangoldt K = arithmeticLogWeight (idealNormArithmetic K) :=
  arithmeticLogDerivative_convolution (idealNormArithmetic_mul_inverse K)

theorem idealVonMangoldt_one : idealVonMangoldt K 1 = 0 := by
  simp [idealVonMangoldt, arithmeticLogDerivative]

theorem idealVonMangoldt_prime {p : ℕ} (hp : p.Prime) :
    idealVonMangoldt K p = (idealNormCount K p : ℝ) * Real.log p := by
  unfold idealVonMangoldt arithmeticLogDerivative
  rw [arithmeticFunction_mul_prime _ _ hp, arithmeticLogWeight_apply,
    arithmeticLogWeight_apply, Nat.cast_one, Real.log_one, mul_zero, zero_mul, zero_add,
    (idealNormInverse_isMultiplicative K).1, mul_one, idealNormArithmetic_apply_pos K hp.pos]

end NairTenenbaum
