/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.Sieve.SiftedDivisorSplit
public import LeanPool.NairTenenbaum.Sieve.SmallDivisorSieve

/-! # Small polynomial divisor sums in the original tuple variables

Whole-prime-power splitting reindexes the original divisor tuples into good
and bad parts. Tuples with zero congruence count contribute zero; all remaining
tuples inherit the required discriminant coprimality from an actual value.
-/

@[expose] public section

namespace NairTenenbaum

open Finset Nat Real Polynomial

theorem mass_dvd_weightedMass {k r : ℕ} (γ : Fin k → Fin r → ℕ)
    (hγ : ∀ i, 0 < totalExponent γ i) (m : Tuple r) : mass m ∣ weightedMass γ m :=
  Finset.prod_dvd_prod_of_dvd _ _ (fun i _ => dvd_pow_self _ (hγ i).ne')

theorem mass_badSieveModuli_le_weightedMass {k r : ℕ} (γ : Fin k → Fin r → ℕ)
    (hγ : ∀ i, 0 < totalExponent γ i) (u v : Tuple r) :
    mass (badSieveModuli u v) ≤ weightedMass γ (u * v) := by
  apply Nat.le_of_dvd (weightedMass_pos γ (u * v))
  apply dvd_trans _ (mass_dvd_weightedMass γ hγ (u * v))
  rw [mass_badSieveModuli, mass_mul]
  exact mul_dvd_mul_right (tupleLCM_dvd_mass u) (mass v)

theorem prime_dvd_mass_iff_tupleLCM {r : ℕ} (u : Tuple r) {p : ℕ} (hp : p.Prime) :
    p ∣ mass u ↔ p ∣ tupleLCM u := by
  constructor
  · intro h
    obtain ⟨i, _, hi⟩ := (hp.prime.dvd_finsetProd_iff (fun i => (u i : ℕ))).mp h
    exact hi.trans (coordinate_dvd_tupleLCM u i)
  · exact fun h => h.trans (tupleLCM_dvd_mass u)

theorem sieveModulus_badSieveModuli {r : ℕ} (Q : ℤ[X]) (u v : Tuple r) (z : ℝ) :
    sieveModulus Q (mass (badSieveModuli u v)) z = sieveModulus Q (mass (u * v)) z := by
  unfold sieveModulus
  congr 1
  ext p
  by_cases hp : p.Prime
  · simp only [sievePrimeSet, Finset.mem_filter, Finset.mem_range, hp, and_true,
      mass_badSieveModuli, mass_mul, hp.dvd_mul, prime_dvd_mass_iff_tupleLCM u hp]
  · simp [sievePrimeSet, hp]

/-- Divisor tuples whose weighted mass is at most the cutoff. -/
noncomputable def smallDivisorTuples {k r : ℕ} (γ : Fin k → Fin r → ℕ) (N : ℕ+) : Finset (Tuple r)
    :=
  (tupleBox r N).filter (fun m => weightedMass γ m ≤ N)

/-- Bad-prime-supported tuples whose product with the good part has bounded weighted mass. -/
noncomputable def smallBadParts {k r : ℕ} (γ : Fin k → Fin r → ℕ) (D : ℕ) (v : Tuple r) (N : ℕ+) :
    Finset (Tuple r) :=
  (tupleBox r N).filter (fun u => (∀ i, (u i : ℕ) ∈ Nat.factoredNumbers D.primeFactors) ∧
      weightedMass γ (u * v) ≤ N)

theorem mem_smallBadParts {k r : ℕ} (γ : Fin k → Fin r → ℕ)
    (hγ : ∀ i, 0 < totalExponent γ i) (D : ℕ) (u v : Tuple r) (N : ℕ+) :
    u ∈ smallBadParts γ D v N ↔
      (∀ i, (u i : ℕ) ∈ Nat.factoredNumbers D.primeFactors) ∧ weightedMass γ (u * v) ≤ N := by
  classical
  simp only [smallBadParts, Finset.mem_filter]
  refine ⟨And.right, fun h => ⟨?_, h⟩⟩
  apply mem_tupleBox.mpr
  intro i
  have H : (u i : ℕ) ≤ ((u * v) i : ℕ) := by
    simpa only [Pi.mul_apply, PNat.mul_coe] using Nat.le_mul_of_pos_right (u i : ℕ) (v i).pos
  exact H.trans ((coordinate_le_weightedMass γ hγ (u * v) i).trans h.2)

/-- Weighted count of sifted polynomial values over all small divisor tuples. -/
noncomputable def PolynomialSystem.smallDivisorSiftedSum {k r : ℕ} (P : PolynomialSystem k r)
    (F : ArithmeticMap k) (N : ℕ+) (a b : ℤ) (z : ℝ) : ℝ :=
  ∑ m ∈ smallDivisorTuples P.exponent N, pullback P.exponent F m *
    conditionalPolynomialSiftedCount P.total (sieveModulus P.total (mass m) z) P.R m a b

/-- An actual polynomial divisor splits into an admissible good part and a bounded bad part. -/
theorem PolynomialSystem.smallDivisor_split_mem {k r : ℕ} (P : PolynomialSystem k r)
    (N : ℕ+) (m : Tuple r) (hm : m ∈ smallDivisorTuples P.exponent N)
    (n : ℤ) (hdiv : ∀ i, (m i : ℕ) ∣ ((P.R i).eval n).natAbs) :
    primeReject m P.discriminant.primeFactors ∈ weightUpTo P.exponent P.discriminant N ∧
    primeSelect m P.discriminant.primeFactors ∈
      smallBadParts P.exponent P.badDiscriminant
        (primeReject m P.discriminant.primeFactors) N := by
  have hmass := (Finset.mem_filter.mp hm).2
  have heprod : primeSelect m P.discriminant.primeFactors * primeReject m
      P.discriminant.primeFactors = m :=
    primeSelect_mul_primeReject _ _
  refine ⟨(mem_weightUpTo P.exponent P.exponent_pos P.discriminant N _).mpr
    ⟨?_, P.divisor_primeReject_dagger n m hdiv⟩,
    (mem_smallBadParts P.exponent P.exponent_pos P.badDiscriminant _ _ N).mpr
    ⟨P.divisor_primeSelect_bad_support n m hdiv, by simpa only [heprod] using hmass⟩⟩
  have H := Nat.le_mul_of_pos_left (weightedMass P.exponent (primeReject m
      P.discriminant.primeFactors))
    (weightedMass_pos P.exponent (primeSelect m P.discriminant.primeFactors))
  rw [← weightedMass_mul, heprod] at H
  exact H.trans hmass

theorem PolynomialSystem.smallDivisorSiftedSum_le_split {k r : ℕ} (P : PolynomialSystem k r)
    {F : ArithmeticMap k} (hF : ∀ n, 0 ≤ F n) (N : ℕ+) (a b : ℤ) (z : ℝ) :
    P.smallDivisorSiftedSum F N a b z ≤
      ∑ v ∈ weightUpTo P.exponent P.discriminant N,
        ∑ u ∈ smallBadParts P.exponent P.badDiscriminant v N,
          pullback P.exponent F (u * v) * P.badPrimeSiftedCount u v a b z := by
  have H := P.siftedDivisorSum_le_split hF (smallDivisorTuples P.exponent N) P.total
    (fun m => sieveModulus P.total (mass m) z) a b
    (weightUpTo P.exponent P.discriminant N) (fun v => smallBadParts P.exponent P.badDiscriminant
        v N)
    (P.smallDivisor_split_mem N)
  simpa only [PolynomialSystem.siftedDivisorSum, PolynomialSystem.smallDivisorSiftedSum,
    PolynomialSystem.badPrimeSiftedCount, sieveModulus_badSieveModuli] using H

/-- The corrected small-divisor sieve estimate in the original, unsplit tuple
variables. A single level condition on `N` controls every tuple in the sum. -/
theorem exists_smallDivisorSiftedSum_bound {g : ℕ} (hg : 0 < g) {η δ : ℝ} (hη : 0 < η) (hδ : 0 <
    δ) :
    ∃ K L : ℝ, 1 ≤ K ∧ 1 ≤ L ∧ ∀ (k r : ℕ) (P : PolynomialSystem k r), P.total.natDegree = g →
      ∀ (A B ε : ℝ) (F : ArithmeticMap k), Admissible A B ε F → 0 ≤ A → 1 ≤ B → 0 < ε →
      (g : ℝ) ^ 2 * ε ≤ 1 / 8 →
      ∀ (N : ℕ+) (a b : ℤ) (z : ℝ), a ≤ b → 2 ≤ z → 16 ≤ Real.log z →
      L * (N : ℝ) * z ^ (4 * (g : ℝ) * (1 + η) + δ) ≤ (b : ℝ) - a →
      P.smallDivisorSiftedSum F N a b z ≤
        K * smallDivisorSieveCost B ε g P.badDiscriminant * ((b : ℝ) - a) * sieveProduct P.total z *
          ∑ n ∈ Finset.Icc 1 N, P.weight F n := by
  obtain ⟨K, L, hK, hL, H⟩ := exists_smallDivisor_sieve_sum_bound hg hη hδ
  refine ⟨K, L, hK, hL, ?_⟩
  intro k r P hdeg A B ε F hF hA hB hε hsmall N a b z hab hz hzlog hlevel
  refine (P.smallDivisorSiftedSum_le_split hF.nonneg N a b z).trans ?_
  apply H k r P hdeg A B ε F hF hA hB hε hsmall N
    (fun v => smallBadParts P.exponent P.badDiscriminant v N)
    (fun v _ u hu => ((mem_smallBadParts P.exponent P.exponent_pos P.badDiscriminant u v N).mp
        hu).1)
    a b z hab hz hzlog
  intro v _ u hu
  have huN := ((mem_smallBadParts P.exponent P.exponent_pos P.badDiscriminant u v N).mp hu).2
  have hmod := (mass_badSieveModuli_le_weightedMass P.exponent P.exponent_pos u v).trans huN
  have H' := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (by exact_mod_cast hmod : (mass (badSieveModuli u v) : ℝ) ≤ N)
      (zero_le_one.trans hL)) (Real.rpow_nonneg (by linarith : 0 ≤ z) (4 * (g : ℝ) * (1 + η) + δ))
  apply le_trans ?_ hlevel
  simpa only [mass_badSieveModuli, Nat.cast_mul, mul_assoc] using H'

end NairTenenbaum
