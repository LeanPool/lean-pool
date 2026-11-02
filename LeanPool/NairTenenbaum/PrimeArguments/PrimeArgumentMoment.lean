/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Smooth.SmoothMomentUniformity

/-! # Smooth moments with the additional prime-argument totient power

The finite envelope uses degree plus one, but the growth condition remains
that of the original polynomial family.
-/

@[expose] public section

namespace NairTenenbaum

open Polynomial Finset

/-- Coefficient-uniform smooth moment for the totient-modified weight. -/
theorem PolynomialSystem.primeArgument_smooth_moment_uniform {k r : ℕ} (P : PolynomialSystem k r)
    {A B ε κ z : ℝ} {F : ArithmeticMap k} (hF : Admissible A B ε F)
    (hA : 0 ≤ A) (hB : 1 ≤ B) (hε : 0 < ε) (hκ : 0 ≤ κ) (hz : 2 ≤ z)
    (hzκ : (4 : ℝ) ^ (((P.total.natDegree : ℝ) + 1) * κ) ≤ z)
    (hgε : (P.total.natDegree : ℝ) * ε ≤ 1 / 8) (N : ℕ+) :
    (∑ n ∈ smoothWeightUpTo P.exponent P.discriminant (Finset.Icc 0 ⌊z⌋₊) N,
      (rootTupleWeight P.exponent F P.R n * ∏ i, totientTwist (P.total.natDegree + 1) (n i)) *
        (weightedMass P.exponent n : ℝ) ^ (κ / Real.log z)) ≤
      smoothTailUniformBound A B κ (P.total.natDegree + 1) P.badDiscriminant *
        ∑ m ∈ positiveUpTo z, P.weight F m := by
  have H := totient_weight_smooth_moment_finite hF hA hB hε hκ hz P.exponent P.exponent_pos
    (fun i => (mul_le_mul_of_nonneg_right (by
      exact_mod_cast P.totalExponent_le_degree i) hε.le).trans hgε)
    P.R (fun i => max (P.R i).natDegree (P.badDiscriminant ^ 3))
    (fun i _ hp ν => P.factor_rootCount_prime_pow_uniform hp ν i)
    (P.total.natDegree + 1) (fun i => (P.totalExponent_le_degree i).trans (Nat.le_succ _))
    (by simpa only [Nat.cast_add, Nat.cast_one] using hzκ) (P.total.natDegree + 1) P.discriminant N
  apply H.trans
  apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg (fun n _ => P.weight_nonneg hF.nonneg n))
  exact (smoothTailBounds_le_uniform A B κ (P.total.natDegree + 1) P.badDiscriminant P.exponent
    (fun i => max (P.R i).natDegree (P.badDiscriminant ^ 3)) (P.factor_count_le_degree.trans
        (Nat.le_succ _))
    (fun i => (P.totalExponent_le_degree i).trans (Nat.le_succ _)) (fun i => max_le_max
      ((Polynomial.natDegree_le_of_dvd (P.factor_dvd_total i) P.total_ne_zero).trans (Nat.le_succ
          _)) le_rfl)).2

end NairTenenbaum
