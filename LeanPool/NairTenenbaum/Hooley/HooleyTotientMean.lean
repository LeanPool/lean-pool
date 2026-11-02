/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Arithmetic.TotientSubexponential

/-! # The sharp Hooley mean with a uniform reciprocal-totient factor -/

@[expose] public section

namespace NairTenenbaum

open Real Polynomial

theorem exists_totient_hooleyRootSum_sharp_bound {η : ℝ} (hη : Real.sqrt 2 < η) :
    ∃ x₀ C : ℝ, 1 < x₀ ∧ 0 < C ∧ ∀ x : ℝ, x₀ < x →
      ∀ n : ℕ, n ≠ 0 → (n : ℝ) ≤ x → ∀ y : ℝ, 0 ≤ y →
        ((n : ℝ) / n.totient) * (y / (Real.log x) ^ 2) * hooleyRootSum (X : ℤ[X]) 1 x ≤
          C * (y / Real.log x * hooleySubexponential η x) := by
  obtain ⟨η₁, hη₁, hη₁η⟩ := exists_between hη
  obtain ⟨x₁, C, hx₁, hC, H⟩ := exists_hooleyRootSum_X_sharp_bound hη₁
  obtain ⟨x₂, _, HT⟩ := exists_reciprocalTotient_subexponential_bound (sub_pos.mpr hη₁η)
  refine ⟨max x₁ x₂, C, hx₁.trans_le (le_max_left _ _), hC, fun x hx n hn hnx y hy => ?_⟩
  have hl : 0 < Real.log x := Real.log_pos (hx₁.trans ((le_max_left _ _).trans_lt hx))
  have hR : 0 ≤ hooleyRootSum (X : ℤ[X]) 1 x := by
    unfold hooleyRootSum
    exact Finset.sum_nonneg fun n _ => by positivity
  calc
    _ ≤ hooleySubexponential (η - η₁) x * (y / (Real.log x) ^ 2) *
        (C * (Real.log x * hooleySubexponential η₁ x)) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_right (HT x ((le_max_right _ _).trans_lt hx) n hn hnx) (by
        positivity)
      · exact H x ((le_max_left _ _).trans_lt hx)
      · exact hR
      · exact mul_nonneg (hooleySubexponential_pos _ _).le (by positivity)
    _ = C * (y / Real.log x *
        (hooleySubexponential (η - η₁) x * hooleySubexponential η₁ x)) := by field_simp
    _ = _ := by rw [hooleySubexponential_mul, sub_add_cancel]

end NairTenenbaum
