/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Sieve.BadPrimeMass

/-! # Reciprocal-density tails on fixed prime support -/

@[expose] public section

namespace NairTenenbaum

/-- A geometric Euler-product bound for the reciprocal square roots of
integers supported by finitely many primes. -/
theorem smooth_reciprocal_half_sum_le (s : Finset ℕ) (S : Finset ℕ+)
    (hS : ∀ n ∈ S, (n : ℕ) ∈ Nat.factoredNumbers s) :
    (∑ n ∈ S, (n : ℝ) ^ (-(1 / 2 : ℝ))) ≤
      (1 / (1 - (2 : ℝ) ^ (-(1 / 2 : ℝ)))) ^ (s.filter Nat.Prime).card := by
  have H := fractionalAuxiliary_sum_le (A := 1) (B := 1) (ε := 1) (α := 1 / 2)
    (σ := -(1 / 2)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) 0 (by norm_num) s S hS
  simpa [fractionalAuxiliary, auxiliary, auxiliaryLocal, Real.rpow_neg, one_div] using H

/-- A large supported modulus supplies a square-root saving in its reciprocal
root density. No pairwise coprimality assumption on the original divisors is needed. -/
theorem smooth_root_density_tail_le (Q : Polynomial ℤ) (s : Finset ℕ) (M : ℕ) (hM : 1 ≤ M)
    (hρ : ∀ p ∈ s, p.Prime → ∀ ν, rootCount Q (p ^ ν) ≤ M)
    (S : Finset ℕ+) (hS : ∀ n ∈ S, (n : ℕ) ∈ Nat.factoredNumbers s)
    {T : ℝ} (hT : 0 < T) (hlarge : ∀ n ∈ S, T ≤ (n : ℝ)) :
    (∑ n ∈ S, (rootCount Q n : ℝ) / n) ≤
      (M ^ (s.filter Nat.Prime).card : ℕ) *
        (1 / (1 - (2 : ℝ) ^ (-(1 / 2 : ℝ)))) ^ (s.filter Nat.Prime).card * T ^ (-(1 / 2 : ℝ)) := by
  let C : ℝ := (M ^ (s.filter Nat.Prime).card : ℕ)
  have hlocal (n : ℕ+) (hn : n ∈ S) : (rootCount Q n : ℝ) / n ≤
      (C * T ^ (-(1 / 2 : ℝ))) * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
    have hn₀ : (0 : ℝ) < n := by exact_mod_cast n.pos
    have hroot : (rootCount Q n : ℝ) ≤ C := by
      dsimp only [C]
      exact_mod_cast rootCount_factored_le Q s M hM hρ (hS n hn)
    have hpower : (n : ℝ) ^ (-(1 / 2 : ℝ)) ≤ T ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hT (hlarge n hn) (by norm_num)
    calc
      _ ≤ C / n := div_le_div_of_nonneg_right hroot hn₀.le
      _ = C * ((n : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ) ^ (-(1 / 2 : ℝ))) := by
        rw [← Real.rpow_add hn₀]
        norm_num [div_eq_mul_inv, Real.rpow_neg_one]
      _ ≤ _ := by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hpower (Real.rpow_nonneg hn₀.le _)) (by positivity : 0 ≤ C)
  calc
    _ ≤ ∑ n ∈ S, (C * T ^ (-(1 / 2 : ℝ))) * (n : ℝ) ^ (-(1 / 2 : ℝ)) := Finset.sum_le_sum hlocal
    _ = (C * T ^ (-(1 / 2 : ℝ))) * ∑ n ∈ S, (n : ℝ) ^ (-(1 / 2 : ℝ)) := (Finset.mul_sum _ _ _).symm
    _ ≤ (C * T ^ (-(1 / 2 : ℝ))) *
        (1 / (1 - (2 : ℝ) ^ (-(1 / 2 : ℝ)))) ^ (s.filter Nat.Prime).card :=
      mul_le_mul_of_nonneg_left (smooth_reciprocal_half_sum_le s S hS) (by positivity)
    _ = _ := by dsimp [C]; ring

/-- Uniform radical root counts at every prime power, including root-free
primes and the restricted bad primes. -/
theorem PolynomialSystem.radical_rootCount_prime_pow_uniform {k r : ℕ}
    (P : PolynomialSystem k r) {p : ℕ} (hp : p.Prime) (ν : ℕ) :
    rootCount P.radical (p ^ ν) ≤ max P.total.natDegree (P.badDiscriminant ^ 3) := by
  by_cases hν : ν = 0
  · subst ν
    simpa only [pow_zero, rootCount_one] using
      (Nat.one_le_pow _ _ P.badDiscriminant_pos).trans (le_max_right P.total.natDegree _)
  by_cases hD : p ∣ P.badDiscriminant
  · exact (P.radical_rootCount_prime_pow_le_bad_cube hp hD ν).trans (le_max_right _ _)
  by_cases hρ : rootCount P.total p = 0
  · have hρ' : rootCount P.radical p = 0 := by rwa [P.rootCount_total_eq_radical hp] at hρ
    rw [rootCount_eq_zero_of_dvd hp.ne_zero (dvd_pow_self p hν) hρ']
    exact Nat.zero_le _
  have hdisc : ¬p ∣ P.discriminant := fun h => hD ((P.prime_dvd_badDiscriminant_iff hp).mpr ⟨h, hρ⟩)
  exact (rootCount_prime_pow_le_of_dvd_discr P.radical_noFixedPrime (dvd_refl P.radical) hp hν
      hdisc).trans
    (((rootCount_le_degree P.radical_noFixedPrime hp).trans P.radical_degree_le_total).trans
        (le_max_left _ _))

end NairTenenbaum
