/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/

/- Modified for Lean Pool: used the gap in nonzero degrees to compute the quintic jet. -/

module

public import LeanPool.SuzukiCancellation.RingTheory.PowerSeries.Noncommutative.FormalExpLog
import Mathlib.Tactic.FinCases -- shake: keep
import Mathlib.Tactic.NormNum -- shake: keep

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

variable {A : Type*}

/-- When degrees two through four vanish, a product of positive-degree factors
has no coefficient in the three degrees immediately above its minimum. -/
private theorem positivePowerCoeff_eq_zero_of_gap [Semiring A] (u : ℕ → A)
    (hzero : ∀ i, 2 ≤ i → i ≤ 4 → u i = 0) (k n : ℕ)
    (hkn : k < n) (hgap : n < k + 4) : positivePowerCoeff u k n = 0 := by
  induction k generalizing n with
  | zero => simp [positivePowerCoeff, Nat.ne_of_gt hkn]
  | succ k ih =>
    rw [positivePowerCoeff]
    apply sum_eq_zero
    intro i hi
    have hiRange := mem_range.mp hi
    rcases Nat.eq_zero_or_pos i with rfl | hiPositive
    · rw [ih (n - (0 + 1)) (by omega) (by omega), mul_zero]
    · rw [hzero (i + 1) (by omega) (by omega), zero_mul]

variable [Ring A] [Algebra ℚ A]

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
  let u : ℕ → A := fun j ↦ if j = 1 then G else if j = 5 then L else 0
  have hzero (i : ℕ) (hl : 2 ≤ i) (hr : i ≤ 4) : u i = 0 := by
    simp [u, show i ≠ 1 by omega, show i ≠ 5 by omega]
  have hgap := positivePowerCoeff_eq_zero_of_gap u hzero
  have hconstant (j : ℕ) : positivePowerCoeff u 0 j = if j = 0 then 1 else 0 := rfl
  have hlinear : u 1 = G := by simp [u]
  have htwo : positivePowerCoeff u 2 6 = G * L + L * G := by
    rw [positivePowerCoeff_add_two u 0 6]
    norm_num [sum_range_succ, positivePowerCoeff_one, u]
  simp only [hc]
  change (∑ k ∈ range ((n : ℕ) + 1), (Nat.factorial k : ℚ)⁻¹ •
    positivePowerCoeff u k n) = _
  -- The last summand is the all-linear contribution in every degree.
  rw [sum_range_succ, positivePowerCoeff_self, hlinear, add_comm]
  congr 1
  fin_cases n <;>
    norm_num [sum_range_succ, hconstant, positivePowerCoeff_one, htwo, hgap, u, Fin.ext_iff]

end FQFP
