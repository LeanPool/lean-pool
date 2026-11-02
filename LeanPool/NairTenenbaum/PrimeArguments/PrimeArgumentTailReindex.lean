/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.PrimeArguments.PrimeArgumentSmallSum
public import LeanPool.NairTenenbaum.PrimeArguments.PrimeArgumentSplitTail
public import LeanPool.NairTenenbaum.Smooth.SmoothTailSieveReindex

/-! # Reindexing the smooth prefix tail for prime arguments -/

@[expose] public section

namespace NairTenenbaum

/-- The smooth mass-tail divisor sum sifted for prime arguments. -/
noncomputable def PolynomialSystem.primeSmoothTailSiftedSum {k r : ℕ} (P : PolynomialSystem k r)
    (F : ArithmeticMap k) (g : ℕ) (N : ℕ+) (s : Finset ℕ) (X : ℝ) (a b : ℤ) (z : ℝ) : ℝ :=
  ∑ m ∈ smoothTailDivisorTuples P.exponent N s X, pullback P.exponent F m *
    conditionalPolynomialSiftedCount (P.total * Polynomial.X) (primeArgumentSieveModulus P.total g
        (mass m) z) P.R m a b

/-- The combined mass tail survives full bad-prime splitting unchanged.
Only positive-count tuples require a witness for the discriminant conditions. -/
theorem PolynomialSystem.primeSmoothTailSiftedSum_le_split {k r : ℕ} (P : PolynomialSystem k r)
    {F : ArithmeticMap k} (hF : ∀ n, 0 ≤ F n) (g : ℕ) (N : ℕ+) (s : Finset ℕ) (X : ℝ)
    (a b : ℤ) (z : ℝ) :
    P.primeSmoothTailSiftedSum F g N s X a b z ≤
      ∑ v ∈ smoothWeightUpTo P.exponent P.discriminant s N,
        ∑ u ∈ (smallBadParts P.exponent P.badDiscriminant v N).filter
            (fun u => X < (weightedMass P.exponent (u * v) : ℝ)),
          pullback P.exponent F (u * v) * P.primeArgumentBadSiftedCount g u v a b z := by
  classical
  have H := P.siftedDivisorSum_le_split hF (smoothTailDivisorTuples P.exponent N s X)
    (P.total * Polynomial.X) (fun m => primeArgumentSieveModulus P.total g (mass m) z) a b
    (smoothWeightUpTo P.exponent P.discriminant s N)
    (fun v => (smallBadParts P.exponent P.badDiscriminant v N).filter
      (fun u => X < (weightedMass P.exponent (u * v) : ℝ)))
    (P.smoothTailDivisor_split_mem N s X)
  simpa only [PolynomialSystem.siftedDivisorSum, PolynomialSystem.primeSmoothTailSiftedSum,
    PolynomialSystem.primeArgumentBadSiftedCount, primeArgumentSieveModulus_badSieveModuli] using H

end NairTenenbaum
