/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.Arithmetic.MainTermLowerBound
public import LeanPool.NairTenenbaum.Contributions.RealIntervalBounds
public import LeanPool.NairTenenbaum.Contributions.SecondContributionWeights

/-! # The small-crossing-prime contribution in the original interval -/

@[expose] public section

namespace NairTenenbaum

/-- A small prime causes the prefix mass to cross the larger threshold. -/
def PolynomialSystem.HasSmallCrossingPrime {k r : ℕ} (P : PolynomialSystem k r)
    (ε x : ℝ) (t : ℤ) : Prop :=
  ∃ (n : Tuple r) (q : ℕ), (∀ i, (n i : ℕ) = ((P.R i).eval t).natAbs) ∧ q.Prime ∧
    (q : ℝ) ≤ x ^ ((P.total.natDegree : ℝ) * ε / 2) ∧
    (weightedMass P.exponent (primeSelect n (Finset.range q)) : ℝ) ≤
      x ^ (3 * (P.total.natDegree : ℝ) ^ 2 * ε / 2) ∧
    x ^ (3 * (P.total.natDegree : ℝ) ^ 2 * ε) <
      (weightedMass P.exponent (primeSelect n (Finset.range (q + 1))) : ℝ)

theorem primePower_scale_identity (g : ℕ) (ε : ℝ) {x : ℝ} (hx : 0 ≤ x) :
    ((x ^ ((g : ℝ) * ε / 2)) ^ 3) ^ g = x ^ (3 * (g : ℝ) ^ 2 * ε / 2) := by
  rw [← pow_mul, ← Real.rpow_natCast, ← Real.rpow_mul hx]
  congr 1
  push_cast
  ring

/-- At the paper's scales the modulus of every selected prime power fits in
the rounded interval once the prime cutoff reaches two. -/
theorem secondContribution_sieve_level {g : ℕ} (hg : 0 < g) {ε x y : ℝ}
    (hε : 0 < ε) (hx : 1 ≤ x) (hz : 2 ≤ x ^ ((g : ℝ) * ε / 2))
    (hy : x ^ (4 * (g : ℝ) ^ 2 * ε) ≤ y) :
    (x ^ ((g : ℝ) * ε / 2)) ^ 4 ≤ y / 2 := by
  have hg₁ : (1 : ℝ) ≤ g := by exact_mod_cast hg
  have hz₄ : 2 ≤ (x ^ ((g : ℝ) * ε / 2)) ^ 4 := (by
    norm_num : (2 : ℝ) ≤ 2 ^ 4).trans (pow_le_pow_left₀ (by norm_num) hz 4)
  have heq : ((x ^ ((g : ℝ) * ε / 2)) ^ 4) ^ 2 = x ^ (4 * (g : ℝ) * ε) := by
    rw [← pow_mul, ← Real.rpow_natCast, ← Real.rpow_mul (zero_le_one.trans hx)]
    congr 1
    norm_num
    ring
  have H : (4 * (g : ℝ) * ε) ≤ 4 * (g : ℝ) ^ 2 * ε := by
    nlinarith [mul_nonneg hε.le (mul_nonneg (show (0 : ℝ) ≤ g by positivity) (sub_nonneg.mpr hg₁))]
  have H' := (Real.rpow_le_rpow_of_exponent_le hx H).trans hy
  rw [← heq] at H'
  nlinarith

end NairTenenbaum
