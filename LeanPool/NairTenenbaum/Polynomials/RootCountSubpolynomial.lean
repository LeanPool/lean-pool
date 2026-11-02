/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Arithmetic.PrimeFactorBounds
public import LeanPool.NairTenenbaum.Polynomials.IrreducibleSystem
public import LeanPool.NairTenenbaum.Polynomials.PolynomialLocal

/-! # Subpolynomial root counts for a fixed irreducible polynomial

The discriminant bound is uniform in prime-power exponents. Multiplicativity
then bounds the root count by a fixed exponential in the number of distinct
prime factors, and hence by every positive power of the modulus.
-/

@[expose] public section

namespace NairTenenbaum

open Finset Polynomial Real

theorem exists_rootCount_prime_pow_uniform {Q : ℤ[X]} (hQ : NoFixedPrimeDivisor Q)
    (hirr : Irreducible (Q.map (Int.castRingHom ℚ))) :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ p : ℕ, p.Prime → ∀ ν : ℕ, rootCount Q (p ^ ν) ≤ C := by
  let P := PolynomialSystem.ofIrreducible (fun _ : Fin 1 => Q) (fun _ => hirr)
    (by intro i j hij; exact (hij (Subsingleton.elim _ _)).elim) (by simpa using hQ)
  refine ⟨max Q.natDegree (P.badDiscriminant ^ 3), ?_, fun p hp ν => ?_⟩
  · exact (show 1 ≤ Q.natDegree from P.factor_degree_pos 0).trans (le_max_left _ _)
  · exact P.factor_rootCount_prime_pow_uniform hp ν 0

theorem rootCount_le_primeFactorPower {Q : ℤ[X]} {C : ℕ}
    (hC : ∀ p : ℕ, p.Prime → ∀ ν : ℕ, rootCount Q (p ^ ν) ≤ C) :
    ∀ n : ℕ, n ≠ 0 → rootCount Q n ≤ C ^ n.primeFactors.card := by
  classical
  apply Nat.recOnPrimePow
  · intro h; exact (h rfl).elim
  · simp
  · intro a p ν hp hpa hν ih _
    have ha : a ≠ 0 := by intro h; exact hpa (h ▸ dvd_zero p)
    have hcop : (p ^ ν).Coprime a := (hp.coprime_iff_not_dvd.mpr hpa).pow_left ν
    have hnot : p ∉ a.primeFactors := fun h => hpa (Nat.dvd_of_mem_primeFactors h)
    rw [rootCount_mul Q hcop, Nat.primeFactors_mul (pow_ne_zero _ hp.ne_zero) ha,
      Nat.primeFactors_pow p hν.ne', hp.primeFactors, singleton_union, card_insert_of_notMem hnot,
          pow_succ]
    exact (Nat.mul_le_mul (hC p hp ν) (ih ha)).trans_eq (Nat.mul_comm _ _)

theorem exists_rootCount_le_rpow {Q : ℤ[X]} (hQ : NoFixedPrimeDivisor Q)
    (hirr : Irreducible (Q.map (Int.castRingHom ℚ))) {ε : ℝ} (hε : 0 < ε) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ n : ℕ, n ≠ 0 → (rootCount Q n : ℝ) ≤ B * (n : ℝ) ^ ε := by
  obtain ⟨C, hC, HC⟩ := exists_rootCount_prime_pow_uniform hQ hirr
  obtain ⟨B, hB, HB⟩ := exists_primeFactorPower_le_rpow (by exact_mod_cast hC : (1 : ℝ) ≤ C) hε
  refine ⟨B, hB, fun n hn => ?_⟩
  exact (show (rootCount Q n : ℝ) ≤ (C : ℝ) ^ n.primeFactors.card by
    exact_mod_cast rootCount_le_primeFactorPower HC n hn).trans (HB n hn)

end NairTenenbaum
