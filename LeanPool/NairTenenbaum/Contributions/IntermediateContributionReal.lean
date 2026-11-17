/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.Contributions.RealIntervalBounds
public import LeanPool.NairTenenbaum.Polynomials.PolynomialValueBounds
public import LeanPool.NairTenenbaum.Smooth.PrimeBandCover

/-! # The intermediate-prefix bound in the original real short interval -/

@[expose] public section

namespace NairTenenbaum

/-- A bounded prefix above the mass threshold with primes in the intermediate range. -/
def PolynomialSystem.HasIntermediatePrefixReal {k r : ℕ} (P : PolynomialSystem k r)
    (T X w₀ x u : ℝ) (t : ℤ) : Prop :=
  ∃ (n : Tuple r) (q : ℕ), (∀ i, (n i : ℕ) = ((P.R i).eval t).natAbs) ∧
    (weightedMass P.exponent (primeSelect n (Finset.range q)) : ℝ) ≤ T ∧
    X < (weightedMass P.exponent (primeSelect n (Finset.range q)) : ℝ) ∧
    (∀ i p, p ∈ (primeSelect n (Finset.range q) i : ℕ).primeFactors → (p : ℝ) ≤ x ^ u) ∧
    ∃ i p, p ∈ (primeSelect n (Finset.range q) i : ℕ).primeFactors ∧ w₀ < (p : ℝ)

theorem PolynomialSystem.hasIntermediatePrefixReal_iff {k r : ℕ} (P : PolynomialSystem k r)
    {T : ℝ} (hT : 1 ≤ T) (X w₀ x u : ℝ) (t : ℤ) :
    P.HasIntermediatePrefixReal T X w₀ x u t ↔
      P.HasIntermediatePrefix (Nat.toPNat' ⌊T⌋₊) X w₀ x u t := by
  simp only [HasIntermediatePrefixReal, HasIntermediatePrefix,
    PNat.toPNat'_coe (Nat.floor_pos.mpr hT), Nat.le_floor_iff (zero_le_one.trans hT)]

end NairTenenbaum
