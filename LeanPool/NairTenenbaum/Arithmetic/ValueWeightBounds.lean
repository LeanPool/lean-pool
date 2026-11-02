/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Polynomials.PolynomialValueBounds
public import LeanPool.NairTenenbaum.Polynomials.PolynomialValueTuples

/-! # Pointwise arithmetic-weight bounds under the height hypothesis -/

@[expose] public section

namespace NairTenenbaum

theorem Admissible.extend_le_mass_rpow {k : ℕ} {A B σ : ℝ} {F : ArithmeticMap k}
    (hF : Admissible A B σ F) (hB : 0 ≤ B) (n : Fin k → ℕ) :
    extendArithmeticMap F n ≤ B * ((∏ j, n j : ℕ) : ℝ) ^ σ * F 1 := by
  unfold extendArithmeticMap
  split_ifs with hn
  · have H := (hF.le_at_one (fun j => ⟨n j, hn j⟩)).trans
      (mul_le_mul_of_nonneg_right (min_le_right _ _) (hF.nonneg 1))
    exact H
  · exact mul_nonneg (mul_nonneg hB (Real.rpow_nonneg (Nat.cast_nonneg _) _)) (hF.nonneg 1)

end NairTenenbaum
