/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.PrimeArguments.PrimeArgumentSieveLevel
public import LeanPool.NairTenenbaum.Sieve.BadPrimeSieve

/-! # Full bad-prime summation for the prime-argument sieve

The original radical and restricted discriminant control the bad-prime
coordinates. Adjoining the argument only adds a totient power and the explicit
constant-term/logarithm factor.
-/

@[expose] public section

namespace NairTenenbaum

open Finset Nat Real Polynomial

/-- The constant-term totient correction divided by the logarithmic sieve cutoff. -/
noncomputable def primeArgumentFactor (Q : ℤ[X]) (z : ℝ) : ℝ :=
  totientTwist 1 (Q.eval 0).natAbs / Real.log z

theorem primeArgumentFactor_nonneg (Q : ℤ[X]) {z : ℝ} (hz : 1 ≤ z) :
    0 ≤ primeArgumentFactor Q z :=
  div_nonneg (totientTwist_nonneg _ _) (Real.log_nonneg hz)

theorem primeArgumentConditionalMainTerm_eq {r : ℕ} (Q : ℤ[X]) (g : ℕ)
    (R : Fin r → ℤ[X]) (m : Tuple r) (a b : ℤ) (z : ℝ) :
    primeArgumentConditionalMainTerm Q g R m a b z =
      conditionalSieveMainTerm Q (g + 1) R m a b z * primeArgumentFactor Q z := by
  unfold primeArgumentConditionalMainTerm conditionalSieveMainTerm primeArgumentFactor
  ring

/-- The conditional prime-argument count after splitting off all bad-prime powers. -/
noncomputable def PolynomialSystem.primeArgumentBadSiftedCount {k r : ℕ} (P : PolynomialSystem k r)
    (g : ℕ) (u v : Tuple r) (a b : ℤ) (z : ℝ) : ℕ :=
  conditionalPolynomialSiftedCount (P.total * X) (primeArgumentSieveModulus P.total g (mass
      (badSieveModuli u v)) z)
    P.R (u * v) a b

theorem PolynomialSystem.primeArgumentBadSiftedCount_le {k r : ℕ} (P : PolynomialSystem k r)
    (g : ℕ) (u v : Tuple r) (a b : ℤ) (z : ℝ) :
    P.primeArgumentBadSiftedCount g u v a b z ≤
      conditionalPolynomialSiftedCount (P.total * X) (primeArgumentSieveModulus P.total g (mass
          (badSieveModuli u v)) z)
        (Fin.cons P.radical P.R) (badSieveModuli u v) a b := by
  unfold primeArgumentBadSiftedCount conditionalPolynomialSiftedCount
  apply Finset.card_le_card
  exact Finset.filter_subset_filter _ (P.congruenceSet_subset_badSieve u v a b)

/-- All bad-prime valuations stay in the original radical LCM density. -/
theorem exists_primeArgument_bad_sieve_bound (g : ℕ) {η δ : ℝ} (hη : 0 < η) (hδ : 0 < δ) :
    ∃ K L : ℝ, 1 ≤ K ∧ 1 ≤ L ∧ ∀ (k r : ℕ) (P : PolynomialSystem k r),
      P.total.natDegree ≤ g → P.total.eval 0 ≠ 0 →
      ∀ (u v : Tuple r), Dagger P.badDiscriminant v →
      (∀ i, (u i : ℕ) ∈ Nat.factoredNumbers P.badDiscriminant.primeFactors) →
      ∀ (a b : ℤ) (z : ℝ), a ≤ b → 2 ≤ z → 16 ≤ Real.log z →
      L * (tupleLCM u : ℝ) * mass v * z ^ (4 * ((g : ℝ) + 1) * (1 + η) + δ) ≤ (b : ℝ) - a →
      (P.primeArgumentBadSiftedCount g u v a b z : ℝ) ≤
        K * ((b : ℝ) - a) * sieveProduct P.total z * totientTwist (g + 1) P.badDiscriminant *
          (∏ i, totientTwist (g + 1) (v i)) * ((rootCount P.radical (tupleLCM u) : ℝ) / tupleLCM
              u) *
            (∏ i, ((rootCount (P.R i) (v i) : ℝ) / v i)) * primeArgumentFactor P.total z := by
  obtain ⟨K, L, hK, hL, H⟩ := exists_primeArgument_conditional_sieve_level_bound g hη hδ
  refine ⟨K, L, hK, hL, ?_⟩
  intro k r P hdeg hzero u v hv hu a b z hab hz hzlog hsize
  have Hcount := H P.total P.noFixedPrime hzero hdeg (r + 1) (Fin.cons P.radical P.R)
    (badSieveModuli u v) (badSieveModuli_pairwise u v hv hu) a b z hab hz hzlog
    (by simpa only [mass_badSieveModuli, Nat.cast_mul, mul_assoc] using hsize)
  rw [primeArgumentConditionalMainTerm_eq] at Hcount
  have Hle := (Nat.cast_le (α := ℝ)).mpr (P.primeArgumentBadSiftedCount_le g u v a b z)
  have Hmain := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right (P.badSieveMainTerm_le (g + 1) u v hu a b hab z)
      (primeArgumentFactor_nonneg P.total (z := z) (by linarith))) (zero_le_one.trans hK)
  exact (Hle.trans Hcount).trans (by simpa only [mul_assoc] using Hmain)

/-- The uniform cost of summing bad-prime parts in the prime-argument sieve. -/
noncomputable def primeArgumentBadSieveCost (B : ℝ) (g D : ℕ) : ℝ :=
  totientTwist (g + 1) D * badPrimeMassBound B g D

theorem exists_primeArgument_bad_sieve_sum_bound {g : ℕ} (hg : 0 < g) {η δ : ℝ} (hη : 0 < η) (hδ :
    0 < δ) :
    ∃ K L : ℝ, 1 ≤ K ∧ 1 ≤ L ∧ ∀ (k r : ℕ) (P : PolynomialSystem k r), P.total.natDegree = g →
        P.total.eval 0 ≠ 0 →
      ∀ (A B ε : ℝ) (F : ArithmeticMap k), Admissible A B ε F → 0 ≤ A → 1 ≤ B → 0 < ε →
      (g : ℝ) ^ 2 * ε ≤ 1 / 8 →
      ∀ (S : Finset (Tuple r)) (v : Tuple r), Dagger P.badDiscriminant v →
      (∀ u ∈ S, ∀ i, (u i : ℕ) ∈ Nat.factoredNumbers P.badDiscriminant.primeFactors) →
      ∀ (a b : ℤ) (z : ℝ), a ≤ b → 2 ≤ z → 16 ≤ Real.log z →
      (∀ u ∈ S, L * (tupleLCM u : ℝ) * mass v * z ^ (4 * ((g : ℝ) + 1) * (1 + η) + δ) ≤ (b : ℝ) -
          a) →
      (∑ u ∈ S, pullback P.exponent F (u * v) * P.primeArgumentBadSiftedCount g u v a b z) ≤
        K * primeArgumentBadSieveCost B g P.badDiscriminant * ((b : ℝ) - a) * sieveProduct P.total
            z *
          rootTupleWeight P.exponent F P.R v * (∏ i, totientTwist (g + 1) (v i)) *
              primeArgumentFactor P.total z := by
  obtain ⟨K, L, hK, hL, H⟩ := exists_primeArgument_bad_sieve_bound g hη hδ
  refine ⟨K, L, hK, hL, ?_⟩
  intro k r P hdeg hzero A B ε F hF hA hB hε hsmall S v hv hs a b z hab hz hzlog hsize
  let C : ℝ := K * ((b : ℝ) - a) * sieveProduct P.total z * totientTwist (g + 1) P.badDiscriminant *
    rootTupleWeight P.exponent F P.R v * (∏ i, totientTwist (g + 1) (v i)) * primeArgumentFactor
        P.total z
  have hW := rootTupleWeight_nonneg P.exponent hF.nonneg P.R v
  have hC : 0 ≤ C := mul_nonneg (
    mul_nonneg (mul_nonneg (mul_nonneg
    (mul_nonneg (mul_nonneg (zero_le_one.trans hK) (by exact_mod_cast sub_nonneg.mpr hab))
      (sieveProduct_pos P.noFixedPrime z).le) (totientTwist_nonneg (g + 1) P.badDiscriminant)) hW)
    (Finset.prod_nonneg (fun _ _ => totientTwist_nonneg _ _))) (primeArgumentFactor_nonneg P.total
        (z := z) (by
      linarith))
  have Hsum : (∑ u ∈ S, pullback P.exponent F (u * v) * P.primeArgumentBadSiftedCount g u v a b z) ≤
      C * ∑ u ∈ S, badPrimeTupleKernel A B ε (totalExponent P.exponent) P.radical u := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro u hu
    have hcross (i j : Fin r) : Nat.Coprime (u i) (v j) :=
      factoredNumbers_coprime_of_coprime (hs u hu i) (hv.2 j).symm
    have Hcount := H k r P hdeg.le hzero u v hv (hs u hu) a b z hab hz hzlog (hsize u hu)
    have H' := P.weighted_count_le_badPrimeKernel hF hA hB u v hcross
      (C := K * ((b : ℝ) - a) * sieveProduct P.total z * totientTwist (g + 1) P.badDiscriminant * (∏
        i, totientTwist (g + 1) (v i)) * primeArgumentFactor P.total z)
      (Nat.cast_nonneg (P.primeArgumentBadSiftedCount g u v a b z)) (by
        simpa only [mul_assoc, mul_comm, mul_left_comm] using Hcount)
    convert H' using 1
    dsimp only [C]
    ring
  have Hmass := P.badPrimeTupleKernel_sum_le_of_support hA hB hε
    (by simpa only [hdeg] using hg) (by simpa only [hdeg] using hsmall) S hs
  rw [hdeg] at Hmass
  calc
    _ ≤ _ := Hsum
    _ ≤ C * badPrimeMassBound B g P.badDiscriminant := mul_le_mul_of_nonneg_left Hmass hC
    _ = _ := by dsimp [C, primeArgumentBadSieveCost]; ring

end NairTenenbaum
