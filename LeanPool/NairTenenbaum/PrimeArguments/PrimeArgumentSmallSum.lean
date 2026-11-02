/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.PrimeArguments.PrimeArgumentMajorant
public import LeanPool.NairTenenbaum.PrimeArguments.PrimeArgumentSmallSieve

/-! # The prime-argument sieve in the original divisor tuple variables -/

@[expose] public section

namespace NairTenenbaum

open Finset Nat Real Polynomial

theorem primeArgumentSieveModulus_badSieveModuli {r : ℕ} (Q : ℤ[X]) (g : ℕ)
    (u v : Tuple r) (z : ℝ) :
    primeArgumentSieveModulus Q g (mass (badSieveModuli u v)) z =
      primeArgumentSieveModulus Q g (mass (u * v)) z := by
  unfold primeArgumentSieveModulus sieveModulus
  congr 1
  ext p
  by_cases hp : p.Prime
  · simp only [sievePrimeSet, Finset.mem_filter, Finset.mem_range, hp, and_true,
      mass_badSieveModuli, mass_mul, hp.dvd_mul, prime_dvd_mass_iff_tupleLCM u hp]
  · simp [sievePrimeSet, hp]

theorem PolynomialSystem.primeSmallDivisorSiftedSum_le_split {k r : ℕ} (P : PolynomialSystem k r)
    {F : ArithmeticMap k} (hF : ∀ n, 0 ≤ F n) (g : ℕ) (N : ℕ+) (a b : ℤ) (z : ℝ) :
    P.primeSmallDivisorSiftedSum F g N a b z ≤
      ∑ v ∈ weightUpTo P.exponent P.discriminant N,
        ∑ u ∈ smallBadParts P.exponent P.badDiscriminant v N,
          pullback P.exponent F (u * v) * P.primeArgumentBadSiftedCount g u v a b z := by
  have H := P.siftedDivisorSum_le_split hF (smallDivisorTuples P.exponent N) (P.total * X)
    (fun m => primeArgumentSieveModulus P.total g (mass m) z) a b
    (weightUpTo P.exponent P.discriminant N) (fun v => smallBadParts P.exponent P.badDiscriminant
        v N)
    (P.smallDivisor_split_mem N)
  simpa only [PolynomialSystem.siftedDivisorSum, PolynomialSystem.primeSmallDivisorSiftedSum,
    PolynomialSystem.primeArgumentBadSiftedCount, primeArgumentSieveModulus_badSieveModuli] using H

/-- The corrected small-divisor sieve estimate in the original, unsplit tuple
variables. A single level condition on `N` controls every tuple in the sum. -/
theorem exists_primeSmallDivisorSiftedSum_bound {g : ℕ} (hg : 0 < g) {η δ : ℝ} (hη : 0 < η) (hδ :
    0 < δ) :
    ∃ K L : ℝ, 1 ≤ K ∧ 1 ≤ L ∧ ∀ (k r : ℕ) (P : PolynomialSystem k r), P.total.natDegree = g →
        P.total.eval 0 ≠ 0 →
      ∀ (A B ε : ℝ) (F : ArithmeticMap k), Admissible A B ε F → 0 ≤ A → 1 ≤ B → 0 < ε →
      (g : ℝ) ^ 2 * ε ≤ 1 / 8 →
      ∀ (N : ℕ+) (a b : ℤ) (z : ℝ), a ≤ b → 2 ≤ z → 16 ≤ Real.log z →
      L * (N : ℝ) * z ^ (4 * ((g : ℝ) + 1) * (1 + η) + δ) ≤ (b : ℝ) - a →
      P.primeSmallDivisorSiftedSum F g N a b z ≤
        K * primeArgumentSmallSieveCost B ε g P.badDiscriminant * ((b : ℝ) - a) * sieveProduct
            P.total z *
          (∑ n ∈ Finset.Icc 1 N, P.weight F n) * primeArgumentFactor P.total z := by
  obtain ⟨K, L, hK, hL, H⟩ := exists_primeArgument_small_sieve_sum_bound hg hη hδ
  refine ⟨K, L, hK, hL, ?_⟩
  intro k r P hdeg hzero A B ε F hF hA hB hε hsmall N a b z hab hz hzlog hlevel
  refine (P.primeSmallDivisorSiftedSum_le_split hF.nonneg g N a b z).trans ?_
  apply H k r P hdeg hzero A B ε F hF hA hB hε hsmall N
    (fun v => smallBadParts P.exponent P.badDiscriminant v N)
    (fun v _ u hu => ((mem_smallBadParts P.exponent P.exponent_pos P.badDiscriminant u v N).mp
        hu).1)
    a b z hab hz hzlog
  intro v _ u hu
  have huN := ((mem_smallBadParts P.exponent P.exponent_pos P.badDiscriminant u v N).mp hu).2
  have hmod := (mass_badSieveModuli_le_weightedMass P.exponent P.exponent_pos u v).trans huN
  have H' := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (by exact_mod_cast hmod : (mass (badSieveModuli u v) : ℝ) ≤ N)
      (zero_le_one.trans hL)) (Real.rpow_nonneg (by
        linarith : 0 ≤ z) (4 * ((g : ℝ) + 1) * (1 + η) + δ))
  apply le_trans ?_ hlevel
  simpa only [mass_badSieveModuli, Nat.cast_mul, mul_assoc] using H'

end NairTenenbaum
