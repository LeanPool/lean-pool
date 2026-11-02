/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Arithmetic.MainTermLowerBound
public import LeanPool.NairTenenbaum.Contributions.RealIntervalBounds
public import LeanPool.NairTenenbaum.Contributions.ThirdContributionWeights

/-! # Large prefixes on a fixed finite prime support

A divisor-tuple majorant covers the third class. Its proof uses a single
smooth divisor of the radical value and does not remove any bad-prime powers.
-/

@[expose] public section

namespace NairTenenbaum

/-- A polynomial value admits a smooth divisor tuple above the lower mass cutoff. -/
def PolynomialSystem.HasLargeSmoothDivisorTuple {k r : ℕ} (P : PolynomialSystem k r)
    (s : Finset ℕ) (ε x : ℝ) (t : ℤ) : Prop :=
  ∃ m : Tuple r, (∀ i, (m i : ℤ) ∣ (P.R i).eval t) ∧
    weightedMass P.exponent m ∈ Nat.factoredNumbers s ∧
    x ^ (3 * (P.total.natDegree : ℝ) ^ 2 * ε / 2) < (weightedMass P.exponent m : ℝ) ∧
    (weightedMass P.exponent m : ℝ) ≤ x ^ (3 * (P.total.natDegree : ℝ) ^ 2 * ε)

/-- The large-divisor upper cutoff is below half the available interval. -/
theorem largeDivisor_sieve_level {g : ℕ} {ε x y : ℝ} (hx : 0 < x)
    (hgap : 2 ≤ x ^ ((g : ℝ) ^ 2 * ε)) (hy : x ^ (4 * (g : ℝ) ^ 2 * ε) ≤ y) :
    x ^ (3 * (g : ℝ) ^ 2 * ε) ≤ y / 2 := by
  have H := mul_le_mul_of_nonneg_right hgap (Real.rpow_nonneg hx.le (3 * (g : ℝ) ^ 2 * ε))
  rw [← Real.rpow_add hx] at H
  have heq : (g : ℝ) ^ 2 * ε + 3 * (g : ℝ) ^ 2 * ε = 4 * (g : ℝ) ^ 2 * ε := by ring
  rw [heq] at H
  linarith

end NairTenenbaum
