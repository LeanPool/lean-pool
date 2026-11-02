/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Hooley.HooleyPrimeShortSum
public import LeanPool.NairTenenbaum.Hooley.HooleyTotientMean

/-! # Corollary 8: Hooley's function at shifted primes

Both inequalities in the paper hold with constants uniform for `1≤|a|≤x`.
The asymptotic exponent is expressed by every coefficient greater than `sqrt(2)`.
-/

@[expose] public section

namespace NairTenenbaum

open Real Polynomial

/-- The statement of Corollary 8, with the scope recorded in the source alignment. -/
def CorollaryEight : Prop :=
  ∀ ε η : ℝ, 0 < ε → ε < 1 → Real.sqrt 2 < η →
    ∃ x₀ C D : ℝ, 1 < x₀ ∧ 0 < C ∧ 0 < D ∧ ∀ a : ℤ, a ≠ 0 → ∀ x y : ℝ,
      x₀ < x → (a.natAbs : ℝ) ≤ x → x ^ ε ≤ y → y ≤ x →
        hooleyPrimeSum a 1 x y ≤ C *
          (((a.natAbs : ℝ) / a.natAbs.totient) * (y / (Real.log x) ^ 2) *
            hooleyRootSum (X : ℤ[X]) 1 x) ∧
        ((a.natAbs : ℝ) / a.natAbs.totient) * (y / (Real.log x) ^ 2) *
            hooleyRootSum (X : ℤ[X]) 1 x ≤ D * (y / Real.log x * hooleySubexponential η x)

theorem corollaryEight : CorollaryEight := by
  intro ε η hε _ hη
  obtain ⟨x₁, C, _, hC, H⟩ := exists_hooleyPrimeSum_root_bound_uniform_shift hε (t := 1) zero_lt_one
  obtain ⟨x₂, D, hx₂, hD, HD⟩ := exists_totient_hooleyRootSum_sharp_bound hη
  refine ⟨max x₁ x₂, C, D, hx₂.trans_le (le_max_right _ _), hC, hD,
    fun a ha x y hx hax hy hyx => ?_⟩
  have hx₂' := (le_max_right x₁ x₂).trans_lt hx
  have hy₀ : 0 ≤ y := (Real.rpow_nonneg (by linarith : 0 ≤ x) ε).trans hy
  exact ⟨H a ha x y ((le_max_left _ _).trans_lt hx) hax hy hyx,
    HD x hx₂' a.natAbs (Int.natAbs_ne_zero.mpr ha) hax y hy₀⟩

end NairTenenbaum
