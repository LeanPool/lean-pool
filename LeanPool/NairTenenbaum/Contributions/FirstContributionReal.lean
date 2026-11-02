/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Contributions.FirstContribution
public import LeanPool.NairTenenbaum.Contributions.RealIntervalBounds

/-! # The first-contribution bound in the real short interval -/

@[expose] public section

namespace NairTenenbaum

/-- A whole-prime-power prefix with bounded real mass and a large next-prime cutoff. -/
def PolynomialSystem.HasSmallRoughPrefixReal {k r : ℕ} (P : PolynomialSystem k r)
    (T z : ℝ) (t : ℤ) : Prop :=
  ∃ (n : Tuple r) (q : ℕ), (∀ i, (n i : ℕ) = ((P.R i).eval t).natAbs) ∧
    (weightedMass P.exponent (primeSelect n (Finset.range q)) : ℝ) ≤ T ∧ z < (q : ℝ)

theorem PolynomialSystem.hasSmallRoughPrefixReal_iff {k r : ℕ} (P : PolynomialSystem k r)
    {T : ℝ} (hT : 1 ≤ T) (z : ℝ) (t : ℤ) :
    P.HasSmallRoughPrefixReal T z t ↔ P.HasSmallRoughPrefix (Nat.toPNat' ⌊T⌋₊) z t := by
  simp only [HasSmallRoughPrefixReal, HasSmallRoughPrefix,
    PNat.toPNat'_coe (Nat.floor_pos.mpr hT), Nat.le_floor_iff (zero_le_one.trans hT)]

end NairTenenbaum
