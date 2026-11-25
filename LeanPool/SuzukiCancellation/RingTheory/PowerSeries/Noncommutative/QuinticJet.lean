/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/

/- Modified for Lean Pool: updated module paths. -/

module

public import LeanPool.SuzukiCancellation.RingTheory.PowerSeries.Noncommutative.FormalExpLog
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum

/-!
# Exponential jets with a quintic logarithm correction

The linear and quintic logarithm coefficients determine the complete
exponential product through degree six in any rational associative algebra.

## Main results

* `expListTerm_through_six_of_log_jet`: the exponential jet from its logarithm.
-/

@[expose] public noncomputable section

namespace FQFP

open Finset

variable {A : Type*} [Ring A] [Algebra ℚ A]

/-- A logarithm with only linear and quintic terms through degree six
determines the complete exponential jet through that degree. -/
theorem expListTerm_through_six_of_log_jet (l : List A) (G L : A)
    (hlog : ∀ n : Fin 7, expListLogCoeff l n =
      if n = 1 then G else if n = 5 then L else 0) (n : Fin 7) :
    expListTerm l n = (Nat.factorial n : ℚ)⁻¹ • G ^ (n : ℕ) +
      if n = 5 then L else if n = 6 then (1 / 2 : ℚ) • (G * L + L * G) else 0 := by
  rw [expListTerm_eq_sum_log_powers]
  have hc (k : ℕ) : positivePowerCoeff (expListLogCoeff l) k n =
      positivePowerCoeff
        (fun j ↦ if j = 1 then G else if j = 5 then L else 0) k n := by
    apply positivePowerCoeff_congr
    intro i _ hi
    simpa [Fin.ext_iff] using hlog ⟨i, by
      have := n.isLt
      lia⟩
  simp only [hc]
  fin_cases n <;>
    norm_num only [positivePowerCoeff, sum_range_succ, sum_range_zero, Nat.factorial,
      Nat.reduceSub, Nat.reduceAdd, ite_true, ite_false, zero_mul, mul_zero,
      zero_smul, one_smul, add_zero, zero_add, mul_one, one_mul, smul_zero, pow_succ,
      smul_add, smul_smul, mul_add, add_mul]
  all_goals norm_num [Fin.ext_iff, mul_assoc]
  all_goals module

end FQFP
