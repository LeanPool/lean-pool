/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Arithmetic.PrimeMajorant
public import LeanPool.NairTenenbaum.Arithmetic.Weights
import Mathlib.Tactic.Positivity

/-! # The multiplicative auxiliary functions of §2

The functions `f_h` immediately preceding equation (17). The local value at
exponent zero is one, including for primes below the cutoff.
-/

@[expose] public section

namespace NairTenenbaum

open Finset

/-- The prescribed prime-power values of `f_h`, with `γ = γ_h`. -/
noncomputable def auxiliaryLocal (A B ε : ℝ) (γ p ν : ℕ) : ℝ :=
  if ν = 0 then 1 else
    if A ^ (1 / ε) < (p : ℝ) then A ^ (γ * ν)
    else B * (p : ℝ) ^ ((γ * ν : ℕ) * ε)

/-- The multiplicative extension of the prescribed prime-power values. -/
noncomputable def auxiliary (A B ε : ℝ) (γ n : ℕ) : ℝ :=
  ∏ p ∈ n.primeFactors, auxiliaryLocal A B ε γ p (n.factorization p)

@[simp] theorem auxiliaryLocal_zero (A B ε : ℝ) (γ p : ℕ) :
    auxiliaryLocal A B ε γ p 0 = 1 := by simp [auxiliaryLocal]

@[simp] theorem auxiliary_one (A B ε : ℝ) (γ : ℕ) : auxiliary A B ε γ 1 = 1 := by
  simp [auxiliary]

theorem auxiliaryLocal_nonneg {A B ε : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (γ p ν : ℕ) :
    0 ≤ auxiliaryLocal A B ε γ p ν := by
  unfold auxiliaryLocal
  split_ifs <;> positivity

theorem auxiliary_nonneg {A B ε : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (γ n : ℕ) :
    0 ≤ auxiliary A B ε γ n :=
  Finset.prod_nonneg fun _ _ => auxiliaryLocal_nonneg hA hB _ _ _

/-- The extension is multiplicative on coprime arguments. -/
theorem auxiliary_mul {A B ε : ℝ} (γ : ℕ) {m n : ℕ} (hmn : m.Coprime n) :
    auxiliary A B ε γ (m * n) = auxiliary A B ε γ m * auxiliary A B ε γ n := by
  simp only [auxiliary]
  rw [hmn.primeFactors_mul, Finset.prod_union hmn.disjoint_primeFactors]
  congr 1
  · apply Finset.prod_congr rfl
    intro p hp
    rw [Nat.factorization_eq_of_coprime_left hmn
      (Nat.mem_primeFactors_iff_mem_primeFactorsList.mp hp)]
  · apply Finset.prod_congr rfl
    intro p hp
    rw [Nat.factorization_eq_of_coprime_right hmn
      (Nat.mem_primeFactors_iff_mem_primeFactorsList.mp hp)]

/-- The multiplicative extension has precisely the prescribed prime-power values. -/
theorem auxiliary_prime_pow (A B ε : ℝ) (γ : ℕ) {p : ℕ} (hp : p.Prime) (ν : ℕ) :
    auxiliary A B ε γ (p ^ ν) = auxiliaryLocal A B ε γ p ν := by
  by_cases hν : ν = 0
  · subst ν; simp
  · rw [auxiliary, Nat.primeFactors_prime_pow hν hp, Finset.prod_singleton,
      Nat.factorization_pow_self hp]

theorem auxiliaryLocal_large {A B ε : ℝ} {p : ℕ} (hp : A ^ (1 / ε) < (p : ℝ))
    (γ ν : ℕ) : auxiliaryLocal A B ε γ p ν = A ^ (γ * ν) := by
  by_cases hν : ν = 0
  · subst ν; simp
  · rw [auxiliaryLocal, ite_eq_right hν, ite_eq_left hp]

theorem auxiliaryLocal_small {A B ε : ℝ} {p : ℕ} (hp : ¬ A ^ (1 / ε) < (p : ℝ))
    (γ ν : ℕ) : auxiliaryLocal A B ε γ p ν =
      (if ν = 0 then 1 else B) * ((p : ℝ) ^ ε) ^ (γ * ν) := by
  by_cases hν : ν = 0
  · simp [auxiliaryLocal, hν]
  · simp only [auxiliaryLocal, hν, ↓reduceIte, hp]
    rw [Real.rpow_natCast_mul (by positivity), ← Real.rpow_pow_comm (by positivity)]

/-- Geometric control of the local factors, as used in Lemmas 1 and 2. -/
theorem auxiliaryLocal_le_geometric {A B ε : ℝ} (hA : 0 ≤ A) (hB : 1 ≤ B)
    (hε : 0 < ε) (γ p ν : ℕ) :
    auxiliaryLocal A B ε γ p ν ≤ B * (min A ((p : ℝ) ^ ε)) ^ (γ * ν) := by
  by_cases hν : ν = 0
  · simpa [hν] using hB
  · by_cases hp : A ^ (1 / ε) < (p : ℝ)
    · have hAp : A ≤ (p : ℝ) ^ ε :=
        (Real.rpow_inv_le_iff_of_pos hA (by positivity) hε).mp (by simpa using hp.le)
      rw [auxiliaryLocal_large hp, min_eq_left hAp]
      exact le_mul_of_one_le_left (pow_nonneg hA _) hB
    · have hpA : (p : ℝ) ^ ε ≤ A :=
        (Real.le_rpow_inv_iff_of_pos (by positivity) hA hε).mp (by simpa using le_of_not_gt hp)
      rw [auxiliaryLocal_small hp, ite_eq_right hν, min_eq_right hpA]

/-- The local inequality used to deduce (17) from (14). -/
theorem local_min_le_prod_auxiliary {r : ℕ} {A B ε : ℝ}
    (hB : 1 ≤ B) (γ ν : Fin r → ℕ) (p : ℕ) :
    min (A ^ ∑ h, γ h * ν h) (B * (p : ℝ) ^ ((∑ h, γ h * ν h : ℕ) * ε)) ≤
      ∏ h, auxiliaryLocal A B ε (γ h) p (ν h) := by
  classical
  by_cases hp : A ^ (1 / ε) < (p : ℝ)
  · simp_rw [auxiliaryLocal_large hp]
    rw [Finset.prod_pow_eq_pow_sum]
    exact min_le_left _ _
  · simp_rw [auxiliaryLocal_small hp]
    rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
    by_cases hν : ∀ h, ν h = 0
    · simp [hν]
    · have hcard : 1 ≤ (Finset.univ.filter fun h => ν h ≠ 0).card := by
        apply Finset.one_le_card.mpr
        obtain ⟨h, hh⟩ := not_forall.mp hν
        exact ⟨h, by simp [hh]⟩
      have hprod : B ≤ ∏ h, if ν h = 0 then (1 : ℝ) else B := by
        simpa [Finset.prod_ite] using
          (pow_le_pow_right₀ hB hcard : B ^ 1 ≤ B ^ (Finset.univ.filter fun h => ν h ≠ 0).card)
      apply (min_le_right _ _).trans
      rw [Real.rpow_natCast_mul (by positivity), ← Real.rpow_pow_comm (by positivity)]
      exact mul_le_mul_of_nonneg_right hprod (by positivity)

/-- Substitution commutes with a finite product. -/
theorem substitute_prod {k r : ℕ} (γ : Fin k → Fin r → ℕ) {ι : Type*}
    (s : Finset ι) (a : ι → Tuple r) :
    substitute γ (∏ i ∈ s, a i) = ∏ i ∈ s, substitute γ (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp only [Finset.prod_insert hi, substitute_mul, ih]

/-- Distinct prime parts remain coordinatewise coprime after substitution. -/
theorem substitute_primePart_coprime {k r : ℕ} (γ : Fin k → Fin r → ℕ) (n : Tuple r)
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    Coprime (substitute γ (primePart n p)) (substitute γ (primePart n q)) := by
  apply substitute_coprime
  intro i j
  rw [primePart_coe n hp i, primePart_coe n hq j]
  exact Nat.coprime_pow_primes _ _ hp hq hpq

theorem mass_substitute_primePart {k r : ℕ} (γ : Fin k → Fin r → ℕ) (n : Tuple r)
    {p : ℕ} (hp : p.Prime) :
    mass (substitute γ (primePart n p)) =
      p ^ ∑ h, totalExponent γ h * (n h : ℕ).factorization p := by
  rw [mass_substitute]
  simp only [weightedMass, primePart_coe n hp, ← pow_mul]
  simp_rw [mul_comm ((n _ : ℕ).factorization p)]
  exact Finset.prod_pow_eq_pow_sum _ _ _

/-- Enlarging the prime support of an auxiliary function inserts only factors one. -/
theorem auxiliary_eq_prod_mass {r : ℕ} (A B ε : ℝ) (γ : ℕ) (n : Tuple r) (h : Fin r) :
    auxiliary A B ε γ (n h) =
      ∏ p ∈ (mass n).primeFactors, auxiliaryLocal A B ε γ p ((n h : ℕ).factorization p) := by
  classical
  apply Finset.prod_subset
  · intro p hp
    exact Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hp,
      (Nat.dvd_of_mem_primeFactors hp).trans (coordinate_dvd_mass n h), (mass_pos n).ne'⟩
  · intro p _ hp
    have hz : (n h : ℕ).factorization p = 0 :=
      Finsupp.notMem_support_iff.mp (by simpa only [Nat.support_factorization] using hp)
    simp [hz]

/-- Equation (17), without a coprimality restriction on the input tuple. -/
theorem Admissible.pullback_minimalMajorant_le_auxiliary {k r : ℕ} {A B ε : ℝ}
    {F : ArithmeticMap k} (hF : Admissible A B ε F) (hA : 0 ≤ A) (hB : 1 ≤ B)
    (γ : Fin k → Fin r → ℕ) (n : Tuple r) :
    pullback γ (minimalMajorant F) n ≤
      ∏ h, auxiliary A B ε (totalExponent γ h) (n h) := by
  have hB₀ := zero_le_one.trans hB
  calc
    pullback γ (minimalMajorant F) n =
        minimalMajorant F (∏ p ∈ (mass n).primeFactors, substitute γ (primePart n p)) := by
      rw [← substitute_prod, prod_primePart]
      rfl
    _ ≤ ∏ p ∈ (mass n).primeFactors, minimalMajorant F (substitute γ (primePart n p)) :=
      hF.minimalMajorant_prod_le hA hB₀ _ _ (fun p hp q hq hpq =>
        substitute_primePart_coprime γ n (Nat.prime_of_mem_primeFactors hp)
          (Nat.prime_of_mem_primeFactors hq) hpq)
    _ ≤ ∏ p ∈ (mass n).primeFactors,
        ∏ h, auxiliaryLocal A B ε (totalExponent γ h) p ((n h : ℕ).factorization p) := by
      apply Finset.prod_le_prod₀ (fun p _ => hF.minimalMajorant_nonneg hA hB₀ _)
      intro p hp
      apply (hF.minimalMajorant_le hA hB₀ _).trans
      have hp' := Nat.prime_of_mem_primeFactors hp
      rw [growthBound, mass_substitute_primePart γ n hp']
      have hΩ : bigOmega (p ^ ∑ h, totalExponent γ h * (n h : ℕ).factorization p) =
          ∑ h, totalExponent γ h * (n h : ℕ).factorization p :=
        ArithmeticFunction.cardFactors_apply_prime_pow hp'
      rw [hΩ, Nat.cast_pow, ← Real.rpow_natCast_mul (by positivity)]
      exact local_min_le_prod_auxiliary hB _ _ _
    _ = ∏ h, auxiliary A B ε (totalExponent γ h) (n h) := by
      rw [Finset.prod_comm]
      apply Finset.prod_congr rfl
      intro h _
      exact (auxiliary_eq_prod_mass A B ε _ n h).symm

end NairTenenbaum
