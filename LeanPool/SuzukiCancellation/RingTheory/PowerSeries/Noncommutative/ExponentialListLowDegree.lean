/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/

/- Modified for Lean Pool: updated module paths. -/

module

public import LeanPool.SuzukiCancellation.RingTheory.PowerSeries.Noncommutative.ExponentialListCoefficients
import Mathlib.Tactic.NormNum

/-!
# Low-degree coefficients of ordered exponential products

The sparse quadratic and cubic recursions expose lower coefficients once and
retain each whole input element as a block.

## Main results

* `FQFP.expListTerm_cons_two`: the quadratic update after prepending a factor.
* `FQFP.expListTerm_cons_three`: the cubic update after prepending a factor.
-/

@[expose] public noncomputable section

open Finset

namespace FQFP

variable {A : Type*} [Semiring A] [Algebra ℚ A]

/-- The quadratic coefficient after adding one exponential on the left. -/
lemma expListTerm_cons_two (a : A) (l : List A) :
    expListTerm (a :: l) 2 = expListTerm l 2 + a * l.sum + (1 / 2 : ℚ) • a ^ 2 := by
  rw [expListTerm, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num [sum_range_succ, expListTerm_zero, expListTerm_one, Nat.factorial]

/-- The cubic coefficient after adding one exponential on the left. -/
lemma expListTerm_cons_three (a : A) (l : List A) :
    expListTerm (a :: l) 3 = expListTerm l 3 + a * expListTerm l 2 +
      (1 / 2 : ℚ) • (a ^ 2 * l.sum) + (1 / 6 : ℚ) • a ^ 3 := by
  rw [expListTerm, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num [sum_range_succ, expListTerm_zero, expListTerm_one, smul_mul_assoc, Nat.factorial]

end FQFP
