/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Sieve.SmallDivisorSum
public import LeanPool.NairTenenbaum.Smooth.SplitSmoothTail

/-! # Reindexing the original smooth mass tail under the sieve restriction -/

@[expose] public section

namespace NairTenenbaum

/-- Small divisor tuples supported on the chosen primes with mass above the tail cutoff. -/
noncomputable def smoothTailDivisorTuples {k r : ℕ} (γ : Fin k → Fin r → ℕ)
    (N : ℕ+) (s : Finset ℕ) (X : ℝ) : Finset (Tuple r) := by
  classical
  exact (smallDivisorTuples γ N).filter (fun m =>
    (∀ i, (m i : ℕ) ∈ Nat.factoredNumbers s) ∧ X < (weightedMass γ m : ℝ))

/-- Sifted divisor sum restricted by smoothness and a lower weighted-mass cutoff. -/
noncomputable def PolynomialSystem.smoothTailSiftedSum {k r : ℕ} (P : PolynomialSystem k r)
    (F : ArithmeticMap k) (N : ℕ+) (s : Finset ℕ) (X : ℝ) (a b : ℤ) (z : ℝ) : ℝ :=
  ∑ m ∈ smoothTailDivisorTuples P.exponent N s X, pullback P.exponent F m *
    conditionalPolynomialSiftedCount P.total (sieveModulus P.total (mass m) z) P.R m a b

/-- Whole-prime-power splitting preserves the good-part smoothness and combined mass tail. -/
theorem PolynomialSystem.smoothTailDivisor_split_mem {k r : ℕ} (P : PolynomialSystem k r)
    (N : ℕ+) (s : Finset ℕ) (X : ℝ) (m : Tuple r)
    (hm : m ∈ smoothTailDivisorTuples P.exponent N s X) (n : ℤ)
    (hdiv : ∀ i, (m i : ℕ) ∣ ((P.R i).eval n).natAbs) :
    primeReject m P.discriminant.primeFactors ∈
      smoothWeightUpTo P.exponent P.discriminant s N ∧
    primeSelect m P.discriminant.primeFactors ∈
      (smallBadParts P.exponent P.badDiscriminant
        (primeReject m P.discriminant.primeFactors) N).filter
          (fun u => X < (weightedMass P.exponent
            (u * primeReject m P.discriminant.primeFactors) : ℝ)) := by
  classical
  obtain ⟨hm, hsmooth, hlarge⟩ := Finset.mem_filter.mp hm
  obtain ⟨hv, hu⟩ := P.smallDivisor_split_mem N m hm n hdiv
  refine ⟨Finset.mem_filter.mpr ⟨hv, ?_⟩, Finset.mem_filter.mpr ⟨hu, ?_⟩⟩
  · exact fun i => Nat.mem_factoredNumbers_of_dvd (hsmooth i)
      (primeReject_coordinate_dvd m _ i)
  · simpa only [primeSelect_mul_primeReject] using hlarge

/-- The combined mass tail survives full bad-prime splitting unchanged.
Only positive-count tuples require a witness for the discriminant conditions. -/
theorem PolynomialSystem.smoothTailSiftedSum_le_split {k r : ℕ} (P : PolynomialSystem k r)
    {F : ArithmeticMap k} (hF : ∀ n, 0 ≤ F n) (N : ℕ+) (s : Finset ℕ) (X : ℝ)
    (a b : ℤ) (z : ℝ) :
    P.smoothTailSiftedSum F N s X a b z ≤
      ∑ v ∈ smoothWeightUpTo P.exponent P.discriminant s N,
        ∑ u ∈ (smallBadParts P.exponent P.badDiscriminant v N).filter
            (fun u => X < (weightedMass P.exponent (u * v) : ℝ)),
          pullback P.exponent F (u * v) * P.badPrimeSiftedCount u v a b z := by
  classical
  have H := P.siftedDivisorSum_le_split hF (smoothTailDivisorTuples P.exponent N s X)
    P.total (fun m => sieveModulus P.total (mass m) z) a b
    (smoothWeightUpTo P.exponent P.discriminant s N)
    (fun v => (smallBadParts P.exponent P.badDiscriminant v N).filter
      (fun u => X < (weightedMass P.exponent (u * v) : ℝ)))
    (P.smoothTailDivisor_split_mem N s X)
  simpa only [PolynomialSystem.siftedDivisorSum, PolynomialSystem.smoothTailSiftedSum,
    PolynomialSystem.badPrimeSiftedCount, sieveModulus_badSieveModuli] using H

end NairTenenbaum
