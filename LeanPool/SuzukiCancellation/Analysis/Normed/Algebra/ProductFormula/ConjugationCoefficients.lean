/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/

/- Modified for Lean Pool: updated module paths. -/

module

public import LeanPool.SuzukiCancellation.Analysis.Normed.Algebra.ProductFormula.SymmetricCenteredLocalError

/-!
# Low coefficients of ordered conjugations

The quadratic and cubic coefficient recursions expose only one occurrence of each
lower coefficient. They avoid repeatedly expanding the constant and linear terms.

## Main results

* `conjCoeff_two_succ`: the quadratic one-stage update.
* `conjCoeff_three_succ`: the cubic one-stage update.
-/

@[expose] public noncomputable section

open FQFP Finset

namespace TrotterError

variable {A : Type*} [Ring A] [Algebra ℝ A]

/-- An empty conjugation list has no positive-degree coefficient. -/
lemma conjCoeff_empty (Z : Fin 0 → A) (B : A) (n : ℕ) (hn : n ≠ 0) :
    conjCoeff Z B n = 0 := by
  simp [conjCoeff, finAntidiagonal_zero, hn]

/-- The quadratic coefficient after appending one outer conjugation. -/
lemma conjCoeff_two_succ {s : ℕ} (Z : Fin (s + 1) → A) (B : A) :
    conjCoeff Z B 2 = conjCoeff (fun i : Fin s ↦ Z i.castSucc) B 2 +
      ⁅Z (Fin.last s), ⁅∑ i : Fin s, Z i.castSucc, B⁆⁆ +
      (1 / 2 : ℝ) • ⁅Z (Fin.last s), ⁅Z (Fin.last s), B⁆⁆ := by
  rw [conjCoeff_succ]
  norm_num [sum_range_succ, conjCoeff_zero, conjCoeff_one, ad_pow_succ]

/-- The cubic coefficient after appending one outer conjugation. -/
lemma conjCoeff_three_succ {s : ℕ} (Z : Fin (s + 1) → A) (B : A) :
    conjCoeff Z B 3 = conjCoeff (fun i : Fin s ↦ Z i.castSucc) B 3 +
      ⁅Z (Fin.last s), conjCoeff (fun i : Fin s ↦ Z i.castSucc) B 2⁆ +
      (1 / 2 : ℝ) • ⁅Z (Fin.last s),
        ⁅Z (Fin.last s), ⁅∑ i : Fin s, Z i.castSucc, B⁆⁆⁆ +
      (1 / 6 : ℝ) • ⁅Z (Fin.last s), ⁅Z (Fin.last s), ⁅Z (Fin.last s), B⁆⁆⁆ := by
  rw [conjCoeff_succ]
  norm_num [sum_range_succ, conjCoeff_zero, conjCoeff_one, ad_pow_succ]

end TrotterError
