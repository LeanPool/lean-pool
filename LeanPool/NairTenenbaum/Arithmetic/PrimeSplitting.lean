/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Arithmetic.AuxiliaryFunctions

/-! # Coprime splitting by prime support

The decompositions used in Lemmas 1 and 2 and in (28)–(30) of the main proof.
The same set of primes is used in every coordinate, so the two parts are coprime
even across different coordinates. This property survives exponent substitution.
-/

@[expose] public section

namespace NairTenenbaum

open Finset

/-- Retain the full prime-power parts at the primes in `s`. -/
def primeSelect {k : ℕ} (n : Tuple k) (s : Finset ℕ) : Tuple k :=
  ∏ p ∈ (mass n).primeFactors.filter (· ∈ s), primePart n p

/-- Retain the full prime-power parts at the primes outside `s`. -/
def primeReject {k : ℕ} (n : Tuple k) (s : Finset ℕ) : Tuple k :=
  ∏ p ∈ (mass n).primeFactors.filter (· ∉ s), primePart n p

theorem primeSelect_mul_primeReject {k : ℕ} (n : Tuple k) (s : Finset ℕ) :
    primeSelect n s * primeReject n s = n := by
  rw [primeSelect, primeReject, Finset.prod_filter_mul_prod_filter_not, prod_primePart]

/-- Coprimality holds across all pairs of coordinates, not just matching ones. -/
theorem primeSelect_primeReject_coprime {k : ℕ} (n : Tuple k) (s : Finset ℕ)
    (i j : Fin k) : Nat.Coprime (primeSelect n s i) (primeReject n s j) := by
  simp only [primeSelect, primeReject, Finset.prod_apply, PNat.coe_prod,
    Nat.coprime_prod_left_iff, Nat.coprime_prod_right_iff]
  intro q hq p hp
  obtain ⟨hp₀, hps⟩ := Finset.mem_filter.mp hp
  obtain ⟨hq₀, hqs⟩ := Finset.mem_filter.mp hq
  have hpp := Nat.prime_of_mem_primeFactors hp₀
  have hqq := Nat.prime_of_mem_primeFactors hq₀
  rw [primePart_coe n hpp i, primePart_coe n hqq j]
  exact Nat.coprime_pow_primes _ _ hpp hqq (by rintro rfl; exact hqs hps)

theorem factorization_prod_primePart {k : ℕ} (n : Tuple k) (T : Finset ℕ)
    (hT : ∀ q ∈ T, q.Prime) (j : Fin k) (p : ℕ) :
    ((∏ q ∈ T, primePart n q) j : ℕ).factorization p =
      if p ∈ T then (n j : ℕ).factorization p else 0 := by
  classical
  simp only [Finset.prod_apply, PNat.coe_prod]
  rw [Nat.factorization_prod (fun q _ => (primePart n q j).ne_zero), Finset.sum_apply']
  calc
    ∑ q ∈ T, (primePart n q j : ℕ).factorization p =
        ∑ q ∈ T, if q = p then (n j : ℕ).factorization q else 0 := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [primePart_coe n (hT q hq) j, (hT q hq).factorization_pow]
      simp [Finsupp.single_apply]
    _ = _ := by simp

theorem factorization_primeSelect {k : ℕ} (n : Tuple k) (s : Finset ℕ) (j : Fin k) (p : ℕ) :
    (primeSelect n s j : ℕ).factorization p =
      if p ∈ s then (n j : ℕ).factorization p else 0 := by
  rw [primeSelect, factorization_prod_primePart n _
    (fun q hq => Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hq).1)]
  by_cases hν : (n j : ℕ).factorization p = 0
  · simp [hν]
  · have hpj : p ∈ (n j : ℕ).primeFactors := by
      simpa only [Nat.support_factorization] using Finsupp.mem_support_iff.mpr hν
    have hp : p ∈ (mass n).primeFactors :=
      Nat.primeFactors_mono (coordinate_dvd_mass n j) (mass_pos n).ne' hpj
    simp [hp]

theorem factorization_primeReject {k : ℕ} (n : Tuple k) (s : Finset ℕ) (j : Fin k) (p : ℕ) :
    (primeReject n s j : ℕ).factorization p =
      if p ∈ s then 0 else (n j : ℕ).factorization p := by
  rw [primeReject, factorization_prod_primePart n _
    (fun q hq => Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hq).1)]
  by_cases hν : (n j : ℕ).factorization p = 0
  · simp [hν]
  · have hpj : p ∈ (n j : ℕ).primeFactors := by
      simpa only [Nat.support_factorization] using Finsupp.mem_support_iff.mpr hν
    have hp : p ∈ (mass n).primeFactors :=
      Nat.primeFactors_mono (coordinate_dvd_mass n j) (mass_pos n).ne' hpj
    by_cases hs : p ∈ s <;> simp [hp, hs]

theorem primeFactors_primeSelect {k : ℕ} (n : Tuple k) (s : Finset ℕ) (j : Fin k) :
    (primeSelect n s j : ℕ).primeFactors = (n j : ℕ).primeFactors ∩ s := by
  ext p
  simp only [← Nat.support_factorization, Finsupp.mem_support_iff, factorization_primeSelect,
    Finset.mem_inter]
  by_cases hp : p ∈ s <;> simp [hp]

theorem primeFactors_primeReject {k : ℕ} (n : Tuple k) (s : Finset ℕ) (j : Fin k) :
    (primeReject n s j : ℕ).primeFactors = (n j : ℕ).primeFactors \ s := by
  ext p
  simp only [← Nat.support_factorization, Finsupp.mem_support_iff, factorization_primeReject,
    Finset.mem_sdiff]
  by_cases hp : p ∈ s <;> simp [hp]

/-- Equation (29) for a split at an arbitrary set of primes. -/
theorem Admissible.pullback_primeSplit_le {k r : ℕ} {A B ε : ℝ} {F : ArithmeticMap k}
    (hF : Admissible A B ε F) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (γ : Fin k → Fin r → ℕ) (n : Tuple r) (s : Finset ℕ) :
    pullback γ F n ≤ pullback γ F (primeSelect n s) *
      pullback γ (minimalMajorant F) (primeReject n s) := by
  have hcop := substitute_coprime γ (primeSelect_primeReject_coprime n s)
  have hbound := hF.le_minimalMajorant_mul hA hB
    (substitute γ (primeReject n s)) (substitute γ (primeSelect n s)) hcop.symm
  rw [← substitute_mul, mul_comm (primeReject n s), primeSelect_mul_primeReject] at hbound
  simpa only [pullback, mul_comm] using hbound

/-- Equation (30), stated for any positive input tuple. -/
theorem Admissible.pullback_minimalMajorant_le_growth {k r : ℕ} {A B ε : ℝ}
    {F : ArithmeticMap k} (hF : Admissible A B ε F) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (γ : Fin k → Fin r → ℕ) (n : Tuple r) :
    pullback γ (minimalMajorant F) n ≤
      min (A ^ bigOmega (weightedMass γ n)) (B * (weightedMass γ n : ℝ) ^ ε) := by
  simpa only [growthBound, mass_substitute, pullback] using hF.minimalMajorant_le hA hB
      (substitute γ n)

end NairTenenbaum
