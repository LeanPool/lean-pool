/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Arithmetic.ComparisonUniformity
public import LeanPool.NairTenenbaum.Sieve.BadPrimeSieve

/-! # Summing the small-divisor sieve estimate

The full bad-prime summation and corrected multivariable totient comparison
combine into a bound by the original truncated weight, with uniform constants.
-/

@[expose] public section

namespace NairTenenbaum

open Finset Nat Real Polynomial

theorem PolynomialSystem.dagger_bad_of_dagger {k r : ℕ} (P : PolynomialSystem k r)
    {v : Tuple r} (hv : Dagger P.discriminant v) : Dagger P.badDiscriminant v := by
  refine ⟨hv.1, ?_⟩
  intro i
  apply Nat.coprime_of_dvd
  intro p hp hpv hpD
  have hpdisc := ((P.prime_dvd_badDiscriminant_iff hp).mp hpD).1
  exact hp.not_dvd_one (by simpa only [(hv.2 i).gcd_eq_one] using Nat.dvd_gcd hpv hpdisc)

theorem positiveUpTo_pnat (N : ℕ+) : positiveUpTo (N : ℝ) = Finset.Icc 1 N := by
  ext n
  rw [mem_positiveUpTo, Finset.mem_Icc]
  constructor
  · intro h
    exact ⟨one_le, by exact_mod_cast h⟩
  · intro h
    exact_mod_cast h.2

theorem PolynomialSystem.totient_tuple_sum_le {k r : ℕ} (P : PolynomialSystem k r)
    {A B ε : ℝ} {F : ArithmeticMap k} (hF : Admissible A B ε F)
    (hA : 0 ≤ A) (hB : 1 ≤ B) (hε : 0 < ε)
    (hgε : (P.total.natDegree : ℝ) * ε < 1) (N : ℕ+) :
    (∑ v ∈ weightUpTo P.exponent P.discriminant N,
      rootTupleWeight P.exponent F P.R v * ∏ i, totientTwist P.total.natDegree (v i)) ≤
      totientComparisonBound B ε P.total.natDegree P.badDiscriminant *
        ∑ n ∈ Finset.Icc 1 N, P.weight F n := by
  have H := P.totient_comparison_uniform hF hA hB hε hgε (N : ℝ)
  rw [positiveUpTo_pnat] at H
  rw [← sum_weight_twist_eq_sum_weightUpTo P.exponent P.exponent_pos]
  exact H

/-- The product of the bad-prime sieve and totient-comparison costs. -/
noncomputable def smallDivisorSieveCost (B ε : ℝ) (g D : ℕ) : ℝ :=
  badPrimeSieveCost B g D * totientComparisonBound B ε g D

/-- A finite family of bad-prime parts over all small dagger tuples is bounded
by the original weight sum. The sieve level is required only for the parts
actually present in each finite family. -/
theorem exists_smallDivisor_sieve_sum_bound {g : ℕ} (hg : 0 < g) {η δ : ℝ} (hη : 0 < η) (hδ : 0 <
    δ) :
    ∃ K L : ℝ, 1 ≤ K ∧ 1 ≤ L ∧ ∀ (k r : ℕ) (P : PolynomialSystem k r), P.total.natDegree = g →
      ∀ (A B ε : ℝ) (F : ArithmeticMap k), Admissible A B ε F → 0 ≤ A → 1 ≤ B → 0 < ε →
      (g : ℝ) ^ 2 * ε ≤ 1 / 8 →
      ∀ (N : ℕ+) (S : Tuple r → Finset (Tuple r)),
      (∀ v ∈ weightUpTo P.exponent P.discriminant N, ∀ u ∈ S v, ∀ i,
        (u i : ℕ) ∈ Nat.factoredNumbers P.badDiscriminant.primeFactors) →
      ∀ (a b : ℤ) (z : ℝ), a ≤ b → 2 ≤ z → 16 ≤ Real.log z →
      (∀ v ∈ weightUpTo P.exponent P.discriminant N, ∀ u ∈ S v,
        L * (tupleLCM u : ℝ) * mass v * z ^ (4 * (g : ℝ) * (1 + η) + δ) ≤ (b : ℝ) - a) →
      (∑ v ∈ weightUpTo P.exponent P.discriminant N,
        ∑ u ∈ S v, pullback P.exponent F (u * v) * P.badPrimeSiftedCount u v a b z) ≤
        K * smallDivisorSieveCost B ε g P.badDiscriminant * ((b : ℝ) - a) * sieveProduct P.total z *
          ∑ n ∈ Finset.Icc 1 N, P.weight F n := by
  obtain ⟨K, L, hK, hL, H⟩ := exists_badPrime_sieve_sum_bound hg hη hδ
  refine ⟨K, L, hK, hL, ?_⟩
  intro k r P hdeg A B ε F hF hA hB hε hsmall N S hs a b z hab hz hzlog hsize
  let C : ℝ := K * badPrimeSieveCost B g P.badDiscriminant * ((b : ℝ) - a) * sieveProduct P.total z
  have hC : 0 ≤ C := mul_nonneg (mul_nonneg (mul_nonneg (zero_le_one.trans hK)
    (mul_nonneg (totientTwist_nonneg g P.badDiscriminant)
      (badPrimeMassBound_pos (lt_of_lt_of_le zero_lt_one hB) hg P.badDiscriminant_pos).le))
    (by exact_mod_cast sub_nonneg.mpr hab)) (sieveProduct_pos P.noFixedPrime z).le
  have hge : (g : ℝ) * ε < 1 := by
    have hg₁ : (1 : ℝ) ≤ g := by exact_mod_cast Nat.succ_le_iff.mpr hg
    have H := mul_le_mul_of_nonneg_right (show (g : ℝ) ≤ (g : ℝ) ^ 2 by nlinarith) hε.le
    linarith
  have Hcompare := P.totient_tuple_sum_le hF hA hB hε (by simpa only [hdeg] using hge) N
  rw [hdeg] at Hcompare
  calc
    _ ≤ ∑ v ∈ weightUpTo P.exponent P.discriminant N,
        C * (rootTupleWeight P.exponent F P.R v * ∏ i, totientTwist g (v i)) := by
      apply Finset.sum_le_sum
      intro v hv
      have hvD := ((mem_weightUpTo P.exponent P.exponent_pos P.discriminant N v).mp hv).2
      have H' := H k r P hdeg A B ε F hF hA hB hε hsmall (S v) v
        (P.dagger_bad_of_dagger hvD) (hs v hv) a b z hab hz hzlog (hsize v hv)
      simpa only [C, mul_assoc] using H'
    _ = C * ∑ v ∈ weightUpTo P.exponent P.discriminant N,
        rootTupleWeight P.exponent F P.R v * ∏ i, totientTwist g (v i) := (Finset.mul_sum _ _
            _).symm
    _ ≤ C * (totientComparisonBound B ε g P.badDiscriminant * ∑ n ∈ Finset.Icc 1 N, P.weight F n) :=
      mul_le_mul_of_nonneg_left Hcompare hC
    _ = _ := by dsimp [C, smallDivisorSieveCost]; ring

end NairTenenbaum
