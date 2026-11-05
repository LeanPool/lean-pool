/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.Sieve.ConditionalPolynomialSieve
public import LeanPool.NairTenenbaum.Sieve.OmittedEulerFactors

/-! # The actual sieve prime set and restoration of omitted Euler factors -/

@[expose] public section

namespace NairTenenbaum

open Finset Nat Real Polynomial

/-- Primes below the sieve cutoff with positive root count and coprime to the modulus. -/
noncomputable def sievePrimeSet (Q : ℤ[X]) (n : ℕ) (z : ℝ) : Finset ℕ :=
  ((Finset.range (⌊z⌋₊ + 1)).filter Nat.Prime).filter (fun p => ¬p ∣ n ∧ rootCount Q p ≠ 0)

/-- The squarefree product of the selected sieve primes. -/
noncomputable def sieveModulus (Q : ℤ[X]) (n : ℕ) (z : ℝ) : ℕ := ∏ p ∈ sievePrimeSet Q n z, p

theorem sievePrimeSet_prime (Q : ℤ[X]) (n : ℕ) (z : ℝ) {p : ℕ} (hp : p ∈ sievePrimeSet Q n z) :
    p.Prime :=
  (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2

theorem sieveModulus_squarefree (Q : ℤ[X]) (n : ℕ) (z : ℝ) : Squarefree (sieveModulus Q n z) :=
  primeSet_product_squarefree _ (fun _ hp => sievePrimeSet_prime Q n z hp)

theorem sieveModulus_primeFactors (Q : ℤ[X]) (n : ℕ) (z : ℝ) :
    (sieveModulus Q n z).primeFactors = sievePrimeSet Q n z :=
  Nat.primeFactors_prod (fun _ hp => sievePrimeSet_prime Q n z hp)

theorem sieveModulus_coprime (Q : ℤ[X]) (n : ℕ) (z : ℝ) : Nat.Coprime (sieveModulus Q n z) n :=
  Nat.coprime_prod_left_iff.mpr (fun _ hp => (sievePrimeSet_prime Q n z
      hp).coprime_iff_not_dvd.mpr (Finset.mem_filter.mp hp).2.1)

theorem sieveModulus_root_pos (Q : ℤ[X]) (n : ℕ) (z : ℝ) {p : ℕ} (hp : p.Prime)
    (hd : p ∣ sieveModulus Q n z) : 0 < rootCount Q p := by
  have H := Nat.mem_primeFactors.mpr ⟨hp, hd, (sieveModulus_squarefree Q n z).ne_zero⟩
  rw [sieveModulus_primeFactors] at H
  exact Nat.pos_of_ne_zero (Finset.mem_filter.mp H).2.2

theorem sieveModulus_prime_le (Q : ℤ[X]) (n : ℕ) {z : ℝ} (hz : 0 ≤ z)
    {p : ℕ} (hp : p ∈ (sieveModulus Q n z).primeFactors) : (p : ℝ) ≤ z := by
  rw [sieveModulus_primeFactors] at hp
  exact (Nat.le_floor_iff hz).mp (Nat.le_of_lt_succ
    (Finset.mem_range.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1))

theorem sievePrimeSet_euler_eq (Q : ℤ[X]) (n : ℕ) (z : ℝ) :
    (∏ p ∈ sievePrimeSet Q n z, (1 - (rootCount Q p : ℝ) / p)) =
      ∏ p ∈ ((Finset.range (⌊z⌋₊ + 1)).filter Nat.Prime).filter (fun p => ¬p ∣ n),
        (1 - (rootCount Q p : ℝ) / p) := by
  have H := Finset.prod_filter_of_ne
    (s := ((Finset.range (⌊z⌋₊ + 1)).filter Nat.Prime).filter (fun p => ¬p ∣ n))
    (f := fun p => (1 - (rootCount Q p : ℝ) / p)) (p := fun p => rootCount Q p ≠ 0)
    (fun p _ h => by intro hzero; exact h (by simp [hzero]))
  simpa only [Finset.filter_filter, sievePrimeSet, and_assoc] using H

/-- Restoring the omitted primes gives precisely the totient correction needed
by the smooth-weight comparison. -/
theorem sievePrimeSet_euler_le {Q : ℤ[X]} (hQ : NoFixedPrimeDivisor Q)
    {g n : ℕ} (hg : Q.natDegree ≤ g) (hn : n ≠ 0) (z : ℝ) :
    (∏ p ∈ sievePrimeSet Q n z, (1 - (rootCount Q p : ℝ) / p)) ≤
      omittedEulerBound g * sieveProduct Q z * totientTwist g n := by
  let S := (Finset.range (⌊z⌋₊ + 1)).filter Nat.Prime
  let f := fun p => 1 - (rootCount Q p : ℝ) / p
  have hf : ∀ p ∈ S, 0 < f p := by
    intro p hp
    have hprime := (Finset.mem_filter.mp hp).2
    exact sub_pos.mpr ((div_lt_one (by
      exact_mod_cast hprime.pos)).mpr (by exact_mod_cast hQ p hprime))
  have hd : (∏ p ∈ S.filter (fun p => p ∣ n), f p) ≠ 0 :=
    (Finset.prod_pos (fun p hp => hf p (Finset.mem_filter.mp hp).1)).ne'
  have hpartition := Finset.prod_filter_mul_prod_filter_not S (fun p => p ∣ n) f
  have heq : (∏ p ∈ S.filter (fun p => ¬p ∣ n), f p) =
      (∏ p ∈ S, f p) * ∏ p ∈ S.filter (fun p => p ∣ n), (f p)⁻¹ := by
    rw [← hpartition, Finset.prod_inv_distrib]
    field_simp
  have hsub : S.filter (fun p => p ∣ n) ⊆ n.primeFactors := by
    intro p hp
    obtain ⟨hp, hpn⟩ := Finset.mem_filter.mp hp
    exact Nat.mem_primeFactors.mpr ⟨(Finset.mem_filter.mp hp).2, hpn, hn⟩
  rw [sievePrimeSet_euler_eq]
  change (∏ p ∈ S.filter (fun p => ¬p ∣ n), f p) ≤ _
  rw [heq]
  have H := mul_le_mul_of_nonneg_left (omittedEulerFactors_le hQ hg hn _ hsub)
    (Finset.prod_pos hf).le
  simpa only [sieveProduct, S, f, mul_assoc, mul_comm, mul_left_comm] using H

/-- The conditional sieve with the full Euler product restored. Its only
modulus-dependent correction is the standard totient twist. -/
theorem exists_restored_conditional_sieve_bound {g : ℕ} (hg : 0 < g) {η : ℝ} (hη : 0 < η) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ (Q : ℤ[X]), NoFixedPrimeDivisor Q → Q.natDegree ≤ g →
      ∀ (r : ℕ) (R : Fin r → ℤ[X]) (m : Tuple r),
      (Pairwise fun i j => Nat.Coprime (m i) (m j)) →
      ∀ (a b : ℤ) (z : ℝ), a ≤ b → 2 ≤ z → 16 ≤ Real.log z →
      (conditionalPolynomialSiftedCount Q (sieveModulus Q (mass m) z) R m a b : ℝ) ≤
        K * (((b : ℝ) - a) * sieveProduct Q z * totientTwist g (mass m) *
          (∏ i, ((rootCount (R i) (m i) : ℝ) / m i)) +
          (∏ i, (rootCount (R i) (m i) : ℝ)) * z ^ (4 * (g : ℝ) * (1 + η))) := by
  obtain ⟨K, hK, H⟩ := exists_conditional_polynomial_sieve_bound
    (g := (g : ℝ)) (by exact_mod_cast Nat.succ_le_iff.mpr hg) hη
  let C := 4 * omittedEulerBound g + K
  have hKC : K ≤ C := by dsimp [C]; linarith [omittedEulerBound_pos g]
  have hBC : 4 * omittedEulerBound g ≤ C := by dsimp [C]; linarith
  refine ⟨C, hK.trans hKC, ?_⟩
  intro Q hQ hdeg r R m hpair a b z hab hz hzlog
  let P := sieveModulus Q (mass m) z
  let D : ℝ := ∏ i, ((rootCount (R i) (m i) : ℝ) / m i)
  let E : ℝ := (∏ i, (rootCount (R i) (m i) : ℝ)) * z ^ (4 * (g : ℝ) * (1 + η))
  let M : ℝ := ((b : ℝ) - a) * sieveProduct Q z * totientTwist g (mass m) * D
  have hD : 0 ≤ D := Finset.prod_nonneg (fun _ _ => div_nonneg (Nat.cast_nonneg _)
      (Nat.cast_nonneg _))
  have hL : 0 ≤ (b : ℝ) - a := by exact_mod_cast sub_nonneg.mpr hab
  have hE : 0 ≤ E := mul_nonneg (Finset.prod_nonneg (fun _ _ => Nat.cast_nonneg _))
      (Real.rpow_nonneg (by
    linarith) _)
  have hM : 0 ≤ M := mul_nonneg
    (mul_nonneg (mul_nonneg hL (sieveProduct_pos hQ z).le) (totientTwist_nonneg g (mass m))) hD
  have Hcount := H Q hQ (by exact_mod_cast hdeg) P (sieveModulus_squarefree Q (mass m) z)
    (fun p hp hd => sieveModulus_root_pos Q (mass m) z hp hd) r R m hpair
    (sieveModulus_coprime Q (mass m) z) a b z hab hz hzlog
    (fun p hp => sieveModulus_prime_le Q (mass m) (by linarith) hp)
  have Heuler : (∏ p ∈ P.primeFactors, (1 - (rootCount Q p : ℝ) / p)) ≤
      omittedEulerBound g * sieveProduct Q z * totientTwist g (mass m) := by
    rw [sieveModulus_primeFactors]
    exact sievePrimeSet_euler_le hQ hdeg (mass_pos m).ne' z
  calc
    _ ≤ 4 * ((b : ℝ) - a) * D *
        (∏ p ∈ P.primeFactors, (1 - (rootCount Q p : ℝ) / p)) + K * E := by
      simpa only [P, D, E, mul_assoc] using Hcount
    _ ≤ 4 * ((b : ℝ) - a) * D *
        (omittedEulerBound g * sieveProduct Q z * totientTwist g (mass m)) + K * E :=
      add_le_add (mul_le_mul_of_nonneg_left Heuler (mul_nonneg (mul_nonneg (by
        norm_num : (0 : ℝ) ≤ 4) hL) hD)) le_rfl
    _ = (4 * omittedEulerBound g) * M + K * E := by dsimp [M]; ring
    _ ≤ C * M + C * E := add_le_add (mul_le_mul_of_nonneg_right hBC hM)
        (mul_le_mul_of_nonneg_right hKC hE)
    _ = _ := by dsimp [M, E, D]; ring

end NairTenenbaum
