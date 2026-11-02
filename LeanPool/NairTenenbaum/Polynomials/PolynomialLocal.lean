/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Polynomials.PolynomialStructure
public import LeanPool.NairTenenbaum.Sieve.BadPrimeRoots

/-! # Local properties of the irreducible polynomial factors

The prime-power bounds outside the restricted bad discriminant, and the
discriminant divisibility that controls common divisors of two distinct factors.
-/

@[expose] public section

namespace NairTenenbaum.PolynomialSystem

open Polynomial Finset

variable {k r : ℕ} (P : PolynomialSystem k r)

theorem factor_dvd_radical (h : Fin r) : P.R h ∣ P.radical :=
  Finset.dvd_prod_of_mem _ (Finset.mem_univ h)

theorem two_factors_dvd_radical {i j : Fin r} (hij : i ≠ j) :
    P.R i * P.R j ∣ P.radical := by
  have h := Finset.prod_dvd_prod_of_subset ({i, j} : Finset (Fin r)) univ P.R
    (Finset.subset_univ _)
  simpa only [Finset.prod_pair hij, radical] using h

theorem common_value_gcd_dvd_discriminant {i j : Fin r} (hij : i ≠ j) (n : ℤ) :
    Nat.gcd ((P.R i).eval n).natAbs ((P.R j).eval n).natAbs ∣ P.discriminant := by
  have hd := Polynomial.natDegree_le_of_dvd (P.two_factors_dvd_radical hij) P.radical_ne_zero
  rw [Polynomial.natDegree_mul (P.factor_ne_zero i) (P.factor_ne_zero j)] at hd
  have hdeg : 2 ≤ P.radical.natDegree := by
    have := P.factor_degree_pos i
    have := P.factor_degree_pos j
    omega
  apply Int.natCast_dvd.mp
  exact dvd_discr_of_dvd_two_factors hdeg (P.two_factors_dvd_radical hij)
    (Int.natCast_dvd.mpr (Nat.gcd_dvd_left _ _))
    (Int.natCast_dvd.mpr (Nat.gcd_dvd_right _ _))

theorem prime_dvd_badDiscriminant_iff {p : ℕ} (hp : p.Prime) :
    p ∣ P.badDiscriminant ↔ p ∣ P.discriminant ∧ rootCount P.total p ≠ 0 := by
  rw [badDiscriminant, hp.prime.dvd_finsetProd_iff]
  constructor
  · rintro ⟨q, hq, hpq⟩
    obtain ⟨hqD, hqρ⟩ := Finset.mem_filter.mp hq
    have hqprime := Nat.prime_of_mem_primeFactors hqD
    have heq : p = q := (Nat.prime_dvd_prime_iff_eq hp hqprime).mp (hp.dvd_of_dvd_pow hpq)
    subst q
    exact ⟨(Nat.mem_primeFactors.mp hqD).2.1, hqρ⟩
  · rintro ⟨hpD, hpρ⟩
    have hmem : p ∈ P.discriminant.primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hp, hpD, P.discriminant_pos.ne'⟩
    exact ⟨p, Finset.mem_filter.mpr ⟨hmem, hpρ⟩,
      dvd_pow_self _ (hp.factorization_pos_of_dvd P.discriminant_pos.ne' hpD).ne'⟩

theorem badDiscriminant_factorization (p : ℕ) :
    P.badDiscriminant.factorization p =
      if rootCount P.total p = 0 then 0 else P.discriminant.factorization p := by
  rw [badDiscriminant, Nat.factorization_prod_apply (fun q hq =>
    pow_ne_zero _ (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hq).1).ne_zero)]
  have hlocal : ∀ q ∈ P.discriminant.primeFactors.filter (fun q => rootCount P.total q ≠ 0),
      (q ^ P.discriminant.factorization q).factorization p =
        if q = p then P.discriminant.factorization q else 0 := by
    intro q hq
    rw [(Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hq).1).factorization_pow]
    simp [Finsupp.single_apply]
  rw [Finset.sum_congr rfl hlocal]
  by_cases hp : p ∈ P.discriminant.primeFactors
  · by_cases hρ : rootCount P.total p = 0 <;> simp [hp, hρ]
  · have hval : P.discriminant.factorization p = 0 := by
      apply Finsupp.notMem_support_iff.mp
      simpa only [Nat.support_factorization] using hp
    simp [hp, hval]

theorem factor_rootCount_prime_pow_le {p ν : ℕ} (hp : p.Prime) (hν : ν ≠ 0)
    (hD : ¬ p ∣ P.discriminant) (h : Fin r) :
    rootCount (P.R h) (p ^ ν) ≤ rootCount (P.R h) p :=
  rootCount_prime_pow_le_of_dvd_discr P.radical_noFixedPrime (P.factor_dvd_radical h) hp hν hD

/-- Outside the restricted bad discriminant `D`, the root counts at every
positive prime power are bounded by the number of roots modulo the prime. -/
theorem factor_rootCount_prime_pow_le_of_not_dvd_bad {p ν : ℕ} (hp : p.Prime) (hν : ν ≠ 0)
    (hD : ¬ p ∣ P.badDiscriminant) (h : Fin r) :
    rootCount (P.R h) (p ^ ν) ≤ rootCount (P.R h) p := by
  by_cases hρ : rootCount P.total p = 0
  · have hρh : rootCount (P.R h) p = 0 :=
      Nat.eq_zero_of_le_zero (hρ ▸ rootCount_le_of_dvd (P.factor_dvd_total h) hp.ne_zero)
    rw [rootCount_eq_zero_of_dvd hp.ne_zero (dvd_pow_self p hν) hρh]
    exact Nat.zero_le _
  · exact P.factor_rootCount_prime_pow_le hp hν
      (fun hpD => hD ((P.prime_dvd_badDiscriminant_iff hp).mpr ⟨hpD, hρ⟩)) h

theorem factor_rootCount_prime_pow_le_degree {p ν : ℕ} (hp : p.Prime) (hν : ν ≠ 0)
    (hD : ¬ p ∣ P.badDiscriminant) (h : Fin r) :
    rootCount (P.R h) (p ^ ν) ≤ (P.R h).natDegree :=
  (P.factor_rootCount_prime_pow_le_of_not_dvd_bad hp hν hD h).trans
    (rootCount_le_degree (P.factor_noFixedPrime h) hp)

/-- A coarse but uniform bound at every prime dividing `D`. -/
theorem radical_rootCount_prime_pow_le_bad_cube {p : ℕ} (hp : p.Prime)
    (hD : p ∣ P.badDiscriminant) (ν : ℕ) :
    rootCount P.radical (p ^ ν) ≤ P.badDiscriminant ^ 3 := by
  obtain ⟨hpD, hρ⟩ := (P.prime_dvd_badDiscriminant_iff hp).mp hD
  have hdeg : 2 ≤ P.radical.natDegree := by
    by_contra! hlt
    have heq := discr_eq_one_of_natDegree_le_one (by omega : P.radical.natDegree ≤ 1)
    have hDone : P.discriminant = 1 := by simp only [discriminant, heq, Int.natAbs_one]
    rw [hDone] at hpD
    exact hp.not_dvd_one hpD
  have he : P.badDiscriminant.factorization p = P.discriminant.factorization p := by
    rw [P.badDiscriminant_factorization, ite_eq_right hρ]
  have hbound := rootCount_prime_pow_le_factorization_bound hdeg
    (Int.natAbs_ne_zero.mp P.discriminant_pos.ne') hp ν
  change rootCount P.radical (p ^ ν) ≤ p ^ (2 * P.discriminant.factorization p + 1) at hbound
  rw [← he] at hbound
  have hpow : p ^ P.badDiscriminant.factorization p ≤ P.badDiscriminant :=
    Nat.le_of_dvd P.badDiscriminant_pos (Nat.ordProj_dvd _ _)
  have hp_le : p ≤ P.badDiscriminant := Nat.le_of_dvd P.badDiscriminant_pos hD
  calc
    rootCount P.radical (p ^ ν) ≤ p ^ (2 * P.badDiscriminant.factorization p + 1) := hbound
    _ = (p ^ P.badDiscriminant.factorization p) ^ 2 * p := by
      rw [pow_add, pow_one, Nat.mul_comm 2, pow_mul]
    _ ≤ P.badDiscriminant ^ 2 * P.badDiscriminant :=
      Nat.mul_le_mul (Nat.pow_le_pow_left hpow 2) hp_le
    _ = P.badDiscriminant ^ 3 := by ring

/-- The same bad-prime bound applies to every irreducible factor. -/
theorem factor_rootCount_prime_pow_le_bad_cube {p : ℕ} (hp : p.Prime)
    (hD : p ∣ P.badDiscriminant) (ν : ℕ) (h : Fin r) :
    rootCount (P.R h) (p ^ ν) ≤ P.badDiscriminant ^ 3 :=
  (rootCount_le_of_dvd (P.factor_dvd_radical h) (pow_ne_zero _ hp.ne_zero)).trans
    (P.radical_rootCount_prime_pow_le_bad_cube hp hD ν)

/-- A bound valid at all prime powers, with no dependence on the coefficients
other than through the specified restricted discriminant. -/
theorem factor_rootCount_prime_pow_uniform {p : ℕ} (hp : p.Prime) (ν : ℕ) (h : Fin r) :
    rootCount (P.R h) (p ^ ν) ≤ max (P.R h).natDegree (P.badDiscriminant ^ 3) := by
  by_cases hν : ν = 0
  · subst ν
    simpa only [pow_zero, rootCount_one] using
      (Nat.succ_le_of_lt (P.factor_degree_pos h)).trans
        (le_max_left (P.R h).natDegree (P.badDiscriminant ^ 3))
  · by_cases hD : p ∣ P.badDiscriminant
    · exact (P.factor_rootCount_prime_pow_le_bad_cube hp hD ν h).trans (le_max_right _ _)
    · exact (P.factor_rootCount_prime_pow_le_degree hp hν hD h).trans (le_max_left _ _)

end NairTenenbaum.PolynomialSystem
