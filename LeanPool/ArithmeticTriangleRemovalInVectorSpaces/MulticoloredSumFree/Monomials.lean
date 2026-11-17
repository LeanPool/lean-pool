/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Monomials of low degree

The polynomial method bounds a multicolored sum-free family in `Fin d → ZMod p` by three times the
number of monomials in `d` variables of degree at most `(p - 1) * d / 3` in which each variable has
degree less than `p`. This file defines the set of their exponent vectors and bounds its size by a
Chernoff bound.

## Main definitions

* `ArithmeticTriangleRemovalInVectorSpaces.lowDegreeExponents p d`: the exponent vectors
  `α : Fin d → ℕ` with `α t < p` for each `t` and `3 * ∑ t, α t ≤ (p - 1) * d`.

## Main statements

* `ArithmeticTriangleRemovalInVectorSpaces.card_lowDegreeExponents_le`: for `0 < x ≤ 1`, there are
  at most `(x ^ (-(p - 1) / 3) * ∑ j ∈ range p, x ^ j) ^ d` such exponent vectors.
-/

@[expose] public section

open Finset

namespace ArithmeticTriangleRemovalInVectorSpaces

/-- The exponent vectors `α : Fin d → ℕ` of the monomials in `d` variables in which each variable
has degree less than `p` and whose degree is at most `(p - 1) * d / 3`. -/
def lowDegreeExponents (p d : ℕ) : Finset (Fin d → ℕ) :=
  {α ∈ Fintype.piFinset fun _ ↦ range p | 3 * ∑ t, α t ≤ (p - 1) * d}

/-- A Chernoff bound for the number of monomials of low degree: for `0 < x ≤ 1` there are at most
`(x ^ (-(p - 1) / 3) * ∑ j ∈ range p, x ^ j) ^ d` of them. -/
lemma card_lowDegreeExponents_le {p : ℕ} (hp : 1 ≤ p) (d : ℕ) {x : ℝ} (hx₀ : 0 < x)
    (hx₁ : x ≤ 1) :
    #(lowDegreeExponents p d) ≤ (x ^ (-((p : ℝ) - 1) / 3) * ∑ j ∈ range p, x ^ j) ^ d := by
  calc (#(lowDegreeExponents p d) : ℝ)
      = ∑ α ∈ lowDegreeExponents p d, 1 := by simp
    _ ≤ ∑ α ∈ lowDegreeExponents p d, x ^ ((∑ t, α t : ℕ) - ((p : ℝ) - 1) * d / 3) := by
      gcongr with α hα
      refine Real.one_le_rpow_of_pos_of_le_one_of_nonpos hx₀ hx₁ ?_
      obtain ⟨-, h⟩ := mem_filter.1 hα
      rw [← Nat.cast_le (α := ℝ)] at h
      push_cast [Nat.cast_sub hp] at h ⊢
      linarith
    _ ≤ ∑ α ∈ Fintype.piFinset fun _ : Fin d ↦ range p,
          x ^ ((∑ t, α t : ℕ) - ((p : ℝ) - 1) * d / 3) := by
      apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
      intros
      positivity
    _ = x ^ (-(((p : ℝ) - 1) * d / 3)) * ∏ _t : Fin d, ∑ j ∈ range p, x ^ j := by
      rw [prod_univ_sum, mul_sum]
      congr with α
      rw [Real.rpow_sub hx₀, Real.rpow_natCast, ← prod_pow_eq_pow_sum, div_eq_mul_inv,
        Real.rpow_neg hx₀.le, mul_comm]
    _ = _ := by
      rw [prod_const, card_univ, Fintype.card_fin, mul_pow, ← Real.rpow_mul_natCast hx₀.le]
      ring_nf

end ArithmeticTriangleRemovalInVectorSpaces
