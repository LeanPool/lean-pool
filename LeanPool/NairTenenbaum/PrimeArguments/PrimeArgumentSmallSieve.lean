/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.Arithmetic.TotientComparisonExponents
public import LeanPool.NairTenenbaum.PrimeArguments.PrimeArgumentBadSieve

/-! # Summing the prime-argument sieve over the small good tuples -/

@[expose] public section

namespace NairTenenbaum

open Finset Nat Real Polynomial

/-- The discriminant-dependent cost of the small-divisor sieve at prime arguments. -/
noncomputable def primeArgumentSmallSieveCost (B ε : ℝ) (g D : ℕ) : ℝ :=
  primeArgumentBadSieveCost B g D * totientExponentComparisonBound B ε g (g + 1) D

/-- A finite family of bad-prime parts over all small dagger tuples is bounded
by the original weight sum. The sieve level is required only for the parts
actually present in each finite family. -/
theorem exists_primeArgument_small_sieve_sum_bound {g : ℕ} (hg : 0 < g) {η δ : ℝ} (hη : 0 < η) (hδ
    : 0 < δ) :
    ∃ K L : ℝ, 1 ≤ K ∧ 1 ≤ L ∧ ∀ (k r : ℕ) (P : PolynomialSystem k r), P.total.natDegree = g →
        P.total.eval 0 ≠ 0 →
      ∀ (A B ε : ℝ) (F : ArithmeticMap k), Admissible A B ε F → 0 ≤ A → 1 ≤ B → 0 < ε →
      (g : ℝ) ^ 2 * ε ≤ 1 / 8 →
      ∀ (N : ℕ+) (S : Tuple r → Finset (Tuple r)),
      (∀ v ∈ weightUpTo P.exponent P.discriminant N, ∀ u ∈ S v, ∀ i,
        (u i : ℕ) ∈ Nat.factoredNumbers P.badDiscriminant.primeFactors) →
      ∀ (a b : ℤ) (z : ℝ), a ≤ b → 2 ≤ z → 16 ≤ Real.log z →
      (∀ v ∈ weightUpTo P.exponent P.discriminant N, ∀ u ∈ S v,
        L * (tupleLCM u : ℝ) * mass v * z ^ (4 * ((g : ℝ) + 1) * (1 + η) + δ) ≤ (b : ℝ) - a) →
      (∑ v ∈ weightUpTo P.exponent P.discriminant N,
        ∑ u ∈ S v, pullback P.exponent F (u * v) * P.primeArgumentBadSiftedCount g u v a b z) ≤
        K * primeArgumentSmallSieveCost B ε g P.badDiscriminant * ((b : ℝ) - a) * sieveProduct
            P.total z *
          (∑ n ∈ Finset.Icc 1 N, P.weight F n) * primeArgumentFactor P.total z := by
  obtain ⟨K, L, hK, hL, H⟩ := exists_primeArgument_bad_sieve_sum_bound hg hη hδ
  refine ⟨K, L, hK, hL, ?_⟩
  intro k r P hdeg hzero A B ε F hF hA hB hε hsmall N S hs a b z hab hz hzlog hsize
  let C : ℝ := K * primeArgumentBadSieveCost B g P.badDiscriminant * ((b : ℝ) - a) * sieveProduct
      P.total z * primeArgumentFactor P.total z
  have hC : 0 ≤ C := mul_nonneg (
    mul_nonneg (mul_nonneg (mul_nonneg (zero_le_one.trans hK)
    (mul_nonneg (totientTwist_nonneg (g + 1) P.badDiscriminant)
      (badPrimeMassBound_pos (lt_of_lt_of_le zero_lt_one hB) hg P.badDiscriminant_pos).le))
    (by
      exact_mod_cast sub_nonneg.mpr hab)) (sieveProduct_pos P.noFixedPrime z).le)
          (primeArgumentFactor_nonneg P.total (z := z) (by linarith))
  have hge : (g : ℝ) * ε < 1 := by
    have hg₁ : (1 : ℝ) ≤ g := by exact_mod_cast Nat.succ_le_iff.mpr hg
    have H := mul_le_mul_of_nonneg_right (show (g : ℝ) ≤ (g : ℝ) ^ 2 by nlinarith) hε.le
    linarith
  have Hcompare := P.totient_tuple_sum_le_exponent hdeg.le hF hA hB hε hge (g + 1) N
  calc
    _ ≤ ∑ v ∈ weightUpTo P.exponent P.discriminant N,
        C * (rootTupleWeight P.exponent F P.R v * ∏ i, totientTwist (g + 1) (v i)) := by
      apply Finset.sum_le_sum
      intro v hv
      have hvD := ((mem_weightUpTo P.exponent P.exponent_pos P.discriminant N v).mp hv).2
      have H' := H k r P hdeg hzero A B ε F hF hA hB hε hsmall (S v) v
        (P.dagger_bad_of_dagger hvD) (hs v hv) a b z hab hz hzlog (hsize v hv)
      simpa only [C, mul_assoc, mul_comm, mul_left_comm] using H'
    _ = C * ∑ v ∈ weightUpTo P.exponent P.discriminant N,
        rootTupleWeight P.exponent F P.R v * ∏ i, totientTwist (g + 1) (v i) := (Finset.mul_sum _
            _ _).symm
    _ ≤ C * (totientExponentComparisonBound B ε g (g + 1) P.badDiscriminant * ∑ n ∈ Finset.Icc 1
        N, P.weight F n) :=
      mul_le_mul_of_nonneg_left Hcompare hC
    _ = _ := by dsimp [C, primeArgumentSmallSieveCost]; ring

end NairTenenbaum
