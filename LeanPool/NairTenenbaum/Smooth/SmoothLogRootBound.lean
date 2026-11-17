/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.Contributions.ShortIntervalCongruenceUpper
public import LeanPool.NairTenenbaum.Polynomials.PolynomialLogParts

/-! # Root-density and remainder terms for the small-prime logarithmic mass -/

@[expose] public section

namespace NairTenenbaum

open Finset Polynomial Real

/-- The main term of the logarithmically weighted smooth-root count. -/
noncomputable def smoothLogRootMain (Q : ℤ[X]) (z : ℝ) (L : ℕ → ℕ) : ℝ :=
  ∑ p ∈ (range (⌊z⌋₊ + 1)).filter Nat.Prime,
    (∑ ν ∈ Icc 1 (L p), (rootCount Q (p ^ ν) : ℝ) / (p : ℝ) ^ ν) * Real.log p

/-- The remainder in the logarithmically weighted smooth-root count. -/
noncomputable def smoothLogRootError (Q : ℤ[X]) (z : ℝ) (L : ℕ → ℕ) : ℝ :=
  ∑ p ∈ (range (⌊z⌋₊ + 1)).filter Nat.Prime,
    (∑ ν ∈ Icc 1 (L p), (rootCount Q (p ^ ν) : ℝ)) * Real.log p

theorem polynomialSmoothLogMass_le_root_terms (Q : ℤ[X]) {x y z : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (hQ : ∀ n ∈ shortInterval x y, Q.eval (n : ℤ) ≠ 0) (L : ℕ → ℕ)
    (hL : ∀ p ∈ (range (⌊z⌋₊ + 1)).filter Nat.Prime, ∀ n ∈ shortInterval x y,
      ((Q.eval (n : ℤ)).natAbs).factorization p ≤ L p) :
    polynomialSmoothLogMass Q x y z ≤ (y + 1) * smoothLogRootMain Q z L + smoothLogRootError Q z L
        := by
  classical
  have hL' : ∀ p ∈ (range (⌊z⌋₊ + 1)).filter Nat.Prime, ∀ n ∈ shortInterval x y,
      (positivePolynomialValue Q n : ℕ).factorization p ≤ L p := by
    intro p hp n hn
    rw [positivePolynomialValue_eq (hQ n hn)]
    exact hL p hp n hn
  rw [polynomialSmoothLogMass_eq_primePower_counts Q x y hz L hL']
  have Hcount (p ν : ℕ) :
      ((shortInterval x y).filter (fun n => p ^ ν ∣ (positivePolynomialValue Q n : ℕ))) =
        (shortInterval x y).filter (fun n : ℕ => p ^ ν ∣ (Q.eval (n : ℤ)).natAbs) := by
    apply filter_congr
    intro n hn
    rw [positivePolynomialValue_eq (hQ n hn)]
  simp_rw [Hcount]
  calc
    _ ≤ ∑ p ∈ (range (⌊z⌋₊ + 1)).filter Nat.Prime,
        (∑ ν ∈ Icc 1 (L p), ((y + 1) * rootCount Q (p ^ ν) / (p : ℝ) ^ ν + rootCount Q (p ^ ν))) *
            Real.log p := by
      apply sum_le_sum
      intro p hp
      have hp' := (mem_filter.mp hp).2
      apply mul_le_mul_of_nonneg_right _ (Real.log_nonneg (by exact_mod_cast hp'.one_lt.le))
      apply sum_le_sum
      intro ν _
      simpa only [Nat.cast_pow] using shortInterval_polynomial_congruence_count_le Q hx hy
          (pow_pos hp'.pos ν)
    _ = _ := by
      unfold smoothLogRootMain smoothLogRootError
      rw [mul_sum, ← sum_add_distrib]
      apply sum_congr rfl
      intro p _
      rw [sum_add_distrib]
      simp only [mul_div_assoc, ← mul_sum]
      ring

end NairTenenbaum
