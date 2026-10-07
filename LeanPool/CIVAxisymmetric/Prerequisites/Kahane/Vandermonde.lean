/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import Mathlib.Data.Nat.Choose.Vandermonde
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Vandermonde collapse of multi-index binomial sums

The multi-index Leibniz rule for `∂^α (g h)` produces the weights
`C(α₀, a) C(α₁, b) C(α₂, c)`; summed over `a + b + c = m` they give `C(|α|, m)`. This is the
combinatorial input of the product estimates in the proof of `thm:analytic:interior`.
-/

public section


namespace CIV

/-- Vandermonde collapse of a double binomial sum. -/
theorem sum_choose_mul_choose_collapse (A B : ℕ) (F : ℕ → ℝ) :
    ∑ a ∈ Finset.range (A + 1), ∑ b ∈ Finset.range (B + 1),
        ((A.choose a * B.choose b : ℕ) : ℝ) * F (a + b) =
      ∑ m ∈ Finset.range (A + B + 1), ((A + B).choose m : ℝ) * F m := by
  rw [← Finset.sum_product']
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun p : ℕ × ℕ => p.1 + p.2)
    (t := Finset.range (A + B + 1)) (fun p hp => by
      simp only [Finset.mem_product, Finset.mem_range] at hp ⊢; omega)]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hF : ∀ p ∈ (Finset.range (A + 1) ×ˢ Finset.range (B + 1)).filter
      (fun p : ℕ × ℕ => p.1 + p.2 = m),
      ((A.choose p.1 * B.choose p.2 : ℕ) : ℝ) * F (p.1 + p.2) =
        ((A.choose p.1 * B.choose p.2 : ℕ) : ℝ) * F m := by
    intro p hp
    rw [(Finset.mem_filter.1 hp).2]
  rw [Finset.sum_congr rfl hF, ← Finset.sum_mul, Nat.add_choose_eq]
  congr 1
  push_cast
  apply Finset.sum_subset
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
    exact Finset.mem_antidiagonal.2 hp.2
  · intro p hp hnot
    have hs := Finset.mem_antidiagonal.1 hp
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range, not_and] at hnot
    by_cases h1 : p.1 < A + 1
    · have h2 : ¬ p.2 < B + 1 := fun h2 => hnot ⟨h1, h2⟩ hs
      rw [Nat.choose_eq_zero_of_lt (by omega : B < p.2)]
      simp
    · rw [Nat.choose_eq_zero_of_lt (by omega : A < p.1)]
      simp

/-- Vandermonde collapse of a triple binomial sum: the multi-index binomial weights of order `m`
sum to `(A + B + D).choose m`. -/
theorem sum_choose_mul_choose_mul_choose_collapse (A B D : ℕ) (F : ℕ → ℝ) :
    ∑ a ∈ Finset.range (A + 1), ∑ b ∈ Finset.range (B + 1), ∑ c ∈ Finset.range (D + 1),
        ((A.choose a * B.choose b * D.choose c : ℕ) : ℝ) * F (a + b + c) =
      ∑ m ∈ Finset.range (A + B + D + 1), ((A + B + D).choose m : ℝ) * F m := by
  have hinner : ∀ a, ∑ b ∈ Finset.range (B + 1), ∑ c ∈ Finset.range (D + 1),
      ((A.choose a * B.choose b * D.choose c : ℕ) : ℝ) * F (a + b + c) =
      ∑ n ∈ Finset.range (B + D + 1), ((A.choose a * (B + D).choose n : ℕ) : ℝ) * F (a + n) := by
    intro a
    have h := sum_choose_mul_choose_collapse B D (fun n => (A.choose a : ℝ) * F (a + n))
    have hl : ∀ b c, ((A.choose a * B.choose b * D.choose c : ℕ) : ℝ) * F (a + b + c) =
        ((B.choose b * D.choose c : ℕ) : ℝ) * ((A.choose a : ℝ) * F (a + (b + c))) := by
      intro b c
      rw [add_assoc]
      push_cast
      ring
    simp_rw [hl, h]
    refine Finset.sum_congr rfl fun n _ => ?_
    push_cast
    ring
  simp_rw [hinner]
  have h2 := sum_choose_mul_choose_collapse A (B + D) F
  rw [← add_assoc] at h2
  exact h2

end CIV
