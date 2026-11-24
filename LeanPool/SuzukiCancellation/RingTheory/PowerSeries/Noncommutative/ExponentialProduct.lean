/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/

/- Modified for Lean Pool: updated module paths. -/

module

public import LeanPool.SuzukiCancellation.RingTheory.PowerSeries.Noncommutative.ExponentialCurve
public import LeanPool.SuzukiCancellation.RingTheory.PowerSeries.Noncommutative.Coefficients

/-!
# Compatibility of list and exponential product coefficients

Associativity of formal series multiplication identifies the right-associated
list convention with the left-associated triple convolution in every degree.
-/

@[expose] public noncomputable section

namespace FQFP

open PowerSeries

/-- The list and pair exponential coefficient conventions agree in every degree. -/
theorem expListTerm_pair {A : Type*} [Ring A] [Algebra ℚ A] (a b : A) (n : ℕ) :
    expListTerm [a, b] n = expMulTerm a b n := by
  rw [← coeff_expListSeries]
  rw [expListSeries_cons_eq_exponentialCurve, expListSeries_cons_eq_exponentialCurve,
    expListSeries_nil, mul_one]
  simp only [coeff_mul, coeff_exponentialCurve, expMulTerm]

/-- The list and triple exponential coefficient conventions agree in every degree. -/
theorem expListTerm_triple {A : Type*} [Ring A] [Algebra ℚ A] (a b c : A) (n : ℕ) :
    expListTerm [a, b, c] n = expMulMulTerm a b c n := by
  rw [← coeff_expListSeries]
  rw [expListSeries_cons_eq_exponentialCurve, expListSeries_cons_eq_exponentialCurve,
    expListSeries_cons_eq_exponentialCurve, expListSeries_nil, mul_one, ← mul_assoc]
  simp only [coeff_mul, coeff_exponentialCurve, expMulMulTerm, expMulTerm]

end FQFP
