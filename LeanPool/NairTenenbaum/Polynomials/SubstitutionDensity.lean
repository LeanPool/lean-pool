/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Arithmetic.DivisorTupleDisjointness
public import LeanPool.NairTenenbaum.Sieve.JointDensityComparison

/-! # Root-density aggregation over exponent-substitution fibers -/

@[expose] public section

namespace NairTenenbaum

open Finset

/-- A factor with a positive exponent divides the corresponding polynomial. -/
theorem PolynomialSystem.factor_dvd_polynomial {k r : ℕ} (P : PolynomialSystem k r)
    (j : Fin k) (i : Fin r) (hi : 0 < P.exponent j i) : P.R i ∣ P.Q j := by
  rw [P.factorization j]
  apply dvd_mul_of_dvd_right
  exact (dvd_pow_self _ hi.ne').trans (Finset.dvd_prod_of_mem _ (Finset.mem_univ i))

/-- Pairwise coprime original polynomials have disjoint exponent supports. -/
theorem PolynomialSystem.exponent_disjoint {k r : ℕ} (P : PolynomialSystem k r)
    (hcop : ∀ i j, i ≠ j → IsCoprime ((P.Q i).map (Int.castRingHom ℚ)) ((P.Q j).map
        (Int.castRingHom ℚ)))
    {i j : Fin k} (hij : i ≠ j) (h : Fin r) : P.exponent i h = 0 ∨ P.exponent j h = 0 := by
  by_contra H
  push Not at H
  have hi := Polynomial.map_dvd (Int.castRingHom ℚ) (P.factor_dvd_polynomial i h
      (Nat.pos_of_ne_zero H.1))
  have hj := Polynomial.map_dvd (Int.castRingHom ℚ) (P.factor_dvd_polynomial j h
      (Nat.pos_of_ne_zero H.2))
  exact (P.irreducible h).not_isUnit ((hcop i j hij).isUnit_of_dvd' hi hj)

/-- Dagger tuples remain pairwise coprime after substitution into pairwise
coprime original polynomials. -/
theorem PolynomialSystem.substitute_pairwise_coprime {k r : ℕ} (P : PolynomialSystem k r)
    (hcop : ∀ i j, i ≠ j → IsCoprime ((P.Q i).map (Int.castRingHom ℚ)) ((P.Q j).map
        (Int.castRingHom ℚ)))
    (n : Tuple r) (hn : Pairwise fun i j => Nat.Coprime (n i) (n j)) :
    Pairwise fun i j => Nat.Coprime (substitute P.exponent n i) (substitute P.exponent n j) := by
  intro i j hij
  simp only [substitute, PNat.coe_prod, PNat.pow_coe, Nat.coprime_prod_left_iff,
      Nat.coprime_prod_right_iff]
  intro h _ l _
  by_cases hhl : h = l
  · subst l
    rcases P.exponent_disjoint hcop hij h with H | H
    · rw [H, pow_zero]
      exact Nat.coprime_one_left _
    · rw [H, pow_zero]
      exact Nat.coprime_one_right _
  · exact ((hn (Ne.symm hhl)).pow_left _).pow_right _

/-- Factor-value divisibility gives all the original polynomial congruences
at the substituted moduli. -/
theorem PolynomialSystem.substitute_dvd_eval {k r : ℕ} (P : PolynomialSystem k r)
    (n : Tuple r) (t : ℤ) (hn : ∀ i, (n i : ℤ) ∣ (P.R i).eval t) (j : Fin k) :
    (substitute P.exponent n j : ℤ) ∣ (P.Q j).eval t := by
  rw [P.factorization j, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod]
  apply dvd_mul_of_dvd_right
  simp only [substitute, PNat.coe_prod, PNat.pow_coe, Nat.cast_prod, Nat.cast_pow,
      Polynomial.eval_pow]
  exact Finset.prod_dvd_prod_of_dvd _ _ (fun i _ => pow_dvd_pow_of_dvd (hn i) _)

/-- Aggregate all dagger tuples with the same substituted arguments before
comparing with the joint root density of the original polynomials. -/
theorem PolynomialSystem.sum_substitutionFiber_rootDensity_le {k r : ℕ} (P : PolynomialSystem k r)
    (S : Finset (Tuple r)) (hS : ∀ n ∈ S, Dagger P.discriminant n) (m : Tuple k)
    (hm : Pairwise fun i j => Nat.Coprime (m i) (m j))
    (hsubst : ∀ n ∈ S, substitute P.exponent n = m) :
    (∑ n ∈ S, ∏ i, (rootCount (P.R i) (n i) : ℝ) / (n i : ℝ)) ≤
      ∏ j, (rootCount (P.Q j) (m j) : ℝ) / (m j : ℝ) := by
  apply sum_jointRootDensity_le S (fun _ => P.R) (fun n i => (n i : ℕ))
    (fun n _ i => (n i).pos) (fun n hn => (hS n hn).1) P.Q (fun j => (m j : ℕ))
    (fun j => (m j).pos) hm
  · intro n hn n' hn' hne t hdiv hdiv'
    apply hne
    apply P.divisor_tuple_eq_of_weightedMass_eq t n n' hdiv hdiv' (hS n hn)
    rw [← mass_substitute, ← mass_substitute, hsubst n hn, hsubst n' hn']
  · intro n hn t hdiv j
    simpa only [hsubst n hn] using P.substitute_dvd_eval n t hdiv j

end NairTenenbaum
