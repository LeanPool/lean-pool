/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.Polynomials.ShiftedLinearSystem
public import LeanPool.NairTenenbaum.Results.TheoremThree

/-! # Corollary 7: short sums at shifted primes

The interval range is `x^(4ε) ≤ y ≤ x`, as in Theorem 3. The display in
the source's Corollary 7 transposes `x` and `y` in this range.
-/

@[expose] public section

namespace NairTenenbaum

open Polynomial Finset

/-- The weighted sum over shifted prime arguments appearing in Corollary 7. -/
noncomputable def shiftedPrimeSum (a : ℤ) (F : ArithmeticMap 1) (x y : ℝ) : ℝ :=
  ∑ p ∈ (shortInterval x y).filter Nat.Prime,
    extendArithmeticMap F (fun _ => ((p : ℤ) + a).natAbs)

theorem shiftedLinearSystem_primeShortSum (a : ℤ) (F : ArithmeticMap 1) (x y : ℝ) :
    primeShortSum (shiftedLinearSystem a).Q F x y = shiftedPrimeSum a F x y := by
  simp only [primeShortSum, shiftedLinearSystem, eval_add, eval_X, eval_C, shiftedPrimeSum]

/-- Corollary 7. Both constants are independent of the integer shift and
the arithmetic function; the reciprocal-totient dependence is explicit. -/
def CorollarySeven : Prop :=
  ∀ (A B ε δ : ℝ), 1 ≤ A → 1 ≤ B → 0 < ε → ε < 1 / 8 → 0 < δ → δ ≤ 1 →
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (a : ℤ), a ≠ 0 → ∀ (F : ArithmeticMap 1), Admissible A B (ε * δ / 3) F →
      ∀ x y : ℝ, c₀ * (a.natAbs : ℝ) ^ δ < x → x ^ (4 * ε) ≤ y → y ≤ x →
        shiftedPrimeSum a F x y ≤ C * shiftedPrimeMainTerm a F x y

theorem corollarySeven : CorollarySeven := by
  intro A B ε δ hA hB hε hsmall hδ hδ₁
  obtain ⟨c, hc, C, hC, H⟩ := exists_primeShortSum_mainTerm_bound (g := 1) (by norm_num)
    hA hB hε (by simpa using hsmall.le) hδ hδ₁
  refine ⟨max c 2, by positivity, C 1, hC 1, ?_⟩
  intro a ha F hF x y hx hy hyx
  have ha₁ : (1 : ℝ) ≤ a.natAbs := by exact_mod_cast Int.natAbs_pos.mpr ha
  have hpow : 1 ≤ (a.natAbs : ℝ) ^ δ := Real.one_le_rpow ha₁ hδ.le
  have hx₂ : 2 < x := lt_of_le_of_lt
    ((le_max_right c 2).trans (le_mul_of_one_le_right (by positivity) hpow)) hx
  have hheight : c * (polynomialHeight (shiftedLinearSystem a).total : ℝ) ^ δ < x := by
    rw [shiftedLinearSystem_total, polynomialHeight_X_add_C_of_ne_zero ha]
    exact (mul_le_mul_of_nonneg_right (le_max_left c 2) (by positivity)).trans_lt hx
  have Hbound := H 1 1 (shiftedLinearSystem a)
    (by rw [shiftedLinearSystem_total, natDegree_X_add_C])
    (by simpa only [shiftedLinearSystem_total, eval_add, eval_X, eval_C, zero_add] using ha)
    F hF x y hheight (by simpa using hy) hyx
  rw [shiftedLinearSystem_primeShortSum, shiftedLinearSystem_badDiscriminant] at Hbound
  have hy₀ : 0 ≤ y := (Real.rpow_nonneg (by linarith : 0 ≤ x) _).trans hy
  exact Hbound.trans (mul_le_mul_of_nonneg_left
    (shiftedLinearSystem_primeMainTerm_le a hF.nonneg (by linarith) hy₀) (hC 1).le)

end NairTenenbaum
