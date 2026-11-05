/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.Arithmetic.PrimeSplitting

/-! # Splitting at the first prime beyond a mass threshold

This constructs the ordered prime-power decomposition underlying (28).
All powers of a prime are retained together, so the existing cross-coprime
splitting lemmas apply. The case where the whole mass is already small is
kept explicitly rather than assuming that a crossing prime exists.
-/

@[expose] public section

namespace NairTenenbaum

open Finset

theorem primePart_eq_one_of_not_mem {r : ℕ} (n : Tuple r) {p : ℕ}
    (hp : p ∉ (mass n).primeFactors) : primePart n p = 1 := by
  funext i
  by_cases hprime : p.Prime
  · have hpi : p ∉ (n i : ℕ).primeFactors := fun h => hp
      (Nat.primeFactors_mono (coordinate_dvd_mass n i) (mass_pos n).ne' h)
    have hν : (n i : ℕ).factorization p = 0 :=
      Finsupp.notMem_support_iff.mp (by simpa only [Nat.support_factorization] using hpi)
    simp [primePart, hprime, hν]
    rfl
  · simp [primePart, hprime]

/-- Increasing the prime cutoff by one adds precisely that whole prime part. -/
theorem primeSelect_range_succ {r : ℕ} (n : Tuple r) (q : ℕ) :
    primeSelect n (Finset.range (q + 1)) = primeSelect n (Finset.range q) * primePart n q := by
  classical
  by_cases hq : q ∈ (mass n).primeFactors
  · have heq : (mass n).primeFactors.filter (· ∈ Finset.range (q + 1)) =
        insert q ((mass n).primeFactors.filter (· ∈ Finset.range q)) := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert]
      constructor
      · rintro ⟨hp, hlt⟩
        by_cases hpq : p = q
        · exact Or.inl hpq
        · exact Or.inr ⟨hp, by omega⟩
      · rintro (rfl | ⟨hp, hlt⟩)
        · exact ⟨hq, by omega⟩
        · exact ⟨hp, by omega⟩
    rw [primeSelect, heq, Finset.prod_insert (by simp)]
    exact mul_comm _ _
  · have heq : (mass n).primeFactors.filter (· ∈ Finset.range (q + 1)) =
        (mass n).primeFactors.filter (· ∈ Finset.range q) := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_range]
      constructor
      · rintro ⟨hp, hlt⟩
        exact ⟨hp, by have : p ≠ q := fun h => hq (h ▸ hp); omega⟩
      · rintro ⟨hp, hlt⟩
        exact ⟨hp, by omega⟩
    rw [primePart_eq_one_of_not_mem n hq, mul_one, primeSelect, heq]
    rfl

theorem primeSelect_range_zero {r : ℕ} (n : Tuple r) :
    primeSelect n (Finset.range 0) = 1 := by simp [primeSelect]

theorem primeSelect_range_full {r : ℕ} (n : Tuple r) :
    primeSelect n (Finset.range (mass n + 1)) = n := by
  rw [primeSelect, Finset.filter_eq_self.mpr, prod_primePart]
  intro p hp
  exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.le_of_dvd (mass_pos n)
      (Nat.dvd_of_mem_primeFactors hp)))

/-- The prime powers in the selected part are strictly below the cutoff. -/
theorem primeSelect_range_prime_lt {r : ℕ} (n : Tuple r) (q : ℕ) (i : Fin r)
    {p : ℕ} (hp : p ∈ (primeSelect n (Finset.range q) i : ℕ).primeFactors) : p < q := by
  rw [primeFactors_primeSelect] at hp
  exact Finset.mem_range.mp (Finset.mem_inter.mp hp).2

/-- The complementary part contains no smaller prime. -/
theorem primeReject_range_prime_ge {r : ℕ} (n : Tuple r) (q : ℕ) (i : Fin r)
    {p : ℕ} (hp : p ∈ (primeReject n (Finset.range q) i : ℕ).primeFactors) : q ≤ p := by
  rw [primeFactors_primeReject] at hp
  exact Nat.le_of_not_gt (fun h => (Finset.mem_sdiff.mp hp).2 (Finset.mem_range.mpr h))

/-- A supported cutoff prime survives in the complementary mass. -/
theorem prime_mem_reject_range {r : ℕ} (n : Tuple r) {q : ℕ}
    (hq : q ∈ (mass n).primeFactors) :
    q ∈ (mass (primeReject n (Finset.range q))).primeFactors := by
  have hp := Nat.prime_of_mem_primeFactors hq
  have hd : q ∣ ∏ i, (n i : ℕ) := Nat.dvd_of_mem_primeFactors hq
  obtain ⟨i, _, hi⟩ := (hp.prime.dvd_finsetProd_iff (fun i => (n i : ℕ))).mp hd
  have himem : q ∈ (primeReject n (Finset.range q) i : ℕ).primeFactors := by
    rw [primeFactors_primeReject]
    exact Finset.mem_sdiff.mpr ⟨Nat.mem_primeFactors.mpr ⟨hp, hi, (n i).ne_zero⟩, by simp⟩
  exact Nat.primeFactors_mono (coordinate_dvd_mass _ i) (mass_pos _).ne' himem

/-- Equation (28) for arbitrary positive tuples and a real mass threshold.
The selected prime is the least prime dividing the complementary mass. -/
theorem exists_prime_threshold {k r : ℕ} (γ : Fin k → Fin r → ℕ) (n : Tuple r)
    {T : ℝ} (hT : 1 ≤ T) (hn : T < (weightedMass γ n : ℝ)) :
    ∃ q : ℕ, q.Prime ∧ q ∈ (mass n).primeFactors ∧
      (weightedMass γ (primeSelect n (Finset.range q)) : ℝ) ≤ T ∧
      T < (weightedMass γ (primeSelect n (Finset.range q)) : ℝ) *
        (q : ℝ) ^ (∑ i, totalExponent γ i * (n i : ℕ).factorization q) ∧
      q ∈ (mass (primeReject n (Finset.range q))).primeFactors ∧
      (∀ i p, p ∈ (primeSelect n (Finset.range q) i : ℕ).primeFactors → p < q) ∧
      (∀ i p, p ∈ (primeReject n (Finset.range q) i : ℕ).primeFactors → q ≤ p) := by
  classical
  have hex : ∃ q : ℕ, T < (weightedMass γ (primeSelect n (Finset.range (q + 1))) : ℝ) :=
    ⟨mass n, by simpa only [primeSelect_range_full] using hn⟩
  let q := Nat.find hex
  have hcross : T < (weightedMass γ (primeSelect n (Finset.range (q + 1))) : ℝ) := Nat.find_spec hex
  have hsmall : (weightedMass γ (primeSelect n (Finset.range q)) : ℝ) ≤ T := by
    cases hq : q with
    | zero => simpa only [hq, primeSelect_range_zero, weightedMass_one, Nat.cast_one] using hT
    | succ m =>
      have H := Nat.find_min hex (show m < Nat.find hex by change m < q; omega)
      exact le_of_not_gt H
  have hmem : q ∈ (mass n).primeFactors := by
    by_contra hq
    rw [primeSelect_range_succ, primePart_eq_one_of_not_mem n hq, mul_one] at hcross
    exact (not_lt_of_ge hsmall) hcross
  have hp := Nat.prime_of_mem_primeFactors hmem
  have hmass : weightedMass γ (primePart n q) =
      q ^ (∑ i, totalExponent γ i * (n i : ℕ).factorization q) := by
    simpa only [mass_substitute] using mass_substitute_primePart γ n hp
  rw [primeSelect_range_succ, weightedMass_mul, hmass, Nat.cast_mul, Nat.cast_pow] at hcross
  exact ⟨q, hp, hmem, hsmall, hcross, prime_mem_reject_range n hmem,
    fun i _ hp => primeSelect_range_prime_lt n q i hp,
    fun i _ hp => primeReject_range_prime_ge n q i hp⟩

/-- An exhaustive threshold dichotomy, including the small-total-mass case. -/
theorem small_mass_or_prime_threshold {k r : ℕ} (γ : Fin k → Fin r → ℕ) (n : Tuple r)
    {T : ℝ} (hT : 1 ≤ T) :
    (weightedMass γ n : ℝ) ≤ T ∨
      ∃ q : ℕ, q.Prime ∧
        (weightedMass γ (primeSelect n (Finset.range q)) : ℝ) ≤ T ∧
        T < (weightedMass γ (primeSelect n (Finset.range (q + 1))) : ℝ) := by
  by_cases hn : (weightedMass γ n : ℝ) ≤ T
  · exact Or.inl hn
  · obtain ⟨q, hp, _, hs, hc, _⟩ := exists_prime_threshold γ n hT (lt_of_not_ge hn)
    refine Or.inr ⟨q, hp, hs, ?_⟩
    have hmass : weightedMass γ (primePart n q) =
        q ^ (∑ i, totalExponent γ i * (n i : ℕ).factorization q) := by
      simpa only [mass_substitute] using mass_substitute_primePart γ n hp
    simpa only [primeSelect_range_succ, weightedMass_mul, hmass, Nat.cast_mul, Nat.cast_pow] using
        hc

end NairTenenbaum
