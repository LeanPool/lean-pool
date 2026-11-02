/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Arithmetic.RoughMass

/-! # Positive tuples of polynomial values and their small-prime divisors -/

@[expose] public section

namespace NairTenenbaum

open Polynomial Finset

theorem PolynomialSystem.substitute_valueTuple {k r : ℕ} (P : PolynomialSystem k r)
    {a : ℤ} {n : Tuple r} (hn : ∀ i, (n i : ℕ) = ((P.R i).eval a).natAbs) (j : Fin k) :
    (substitute P.exponent n j : ℕ) = ((P.Q j).eval a).natAbs := by
  rw [P.abs_eval_factorization]
  simp only [substitute, PNat.coe_prod, PNat.pow_coe, hn]

theorem PolynomialSystem.weightedMass_valueTuple {k r : ℕ} (P : PolynomialSystem k r)
    {a : ℤ} {n : Tuple r} (hn : ∀ i, (n i : ℕ) = ((P.R i).eval a).natAbs) :
    weightedMass P.exponent n = (P.total.eval a).natAbs := by
  rw [← mass_substitute]
  simp only [mass, P.substitute_valueTuple hn, PolynomialSystem.total, Polynomial.eval_prod]
  exact (map_prod Int.natAbsHom _ _).symm

theorem PolynomialSystem.pullback_valueTuple {k r : ℕ} (P : PolynomialSystem k r)
    (F : ArithmeticMap k) {a : ℤ} {n : Tuple r}
    (hn : ∀ i, (n i : ℕ) = ((P.R i).eval a).natAbs) :
    pullback P.exponent F n = extendArithmeticMap F (fun j => ((P.Q j).eval a).natAbs) := by
  rw [← funext (P.substitute_valueTuple hn), extendArithmeticMap_coe]
  rfl

/-- Nonzero total values supply positive tuples of all irreducible values. -/
theorem PolynomialSystem.exists_valueTuple {k r : ℕ} (P : PolynomialSystem k r)
    {a : ℤ} (ha : P.total.eval a ≠ 0) :
    ∃ n : Tuple r, ∀ i, (n i : ℕ) = ((P.R i).eval a).natAbs := by
  have hpos (i : Fin r) : 0 < ((P.R i).eval a).natAbs := by
    apply Int.natAbs_pos.mpr
    exact ne_zero_of_dvd_ne_zero ha (Polynomial.eval_dvd (P.factor_dvd_total i))
  exact ⟨fun i => ⟨_, hpos i⟩, fun _ => rfl⟩

/-- A selected prefix satisfies the actual sieve condition whenever its cutoff
is larger than the sifting bound. -/
theorem PolynomialSystem.primeSelect_sieve_coprime {k r : ℕ} (P : PolynomialSystem k r)
    {a : ℤ} {n : Tuple r} (hn : ∀ i, (n i : ℕ) = ((P.R i).eval a).natAbs)
    {q : ℕ} {z : ℝ} (hz : 0 ≤ z) (hq : z < (q : ℝ)) :
    Nat.Coprime (sieveModulus P.total (mass (primeSelect n (Finset.range q))) z)
      (P.total.eval a).natAbs := by
  apply Nat.coprime_of_dvd
  intro p hp hps hpv
  have hpmem := Nat.mem_primeFactors.mpr
    ⟨hp, hps, (sieveModulus_squarefree P.total _ z).ne_zero⟩
  have hpz := sieveModulus_prime_le P.total _ hz hpmem
  have hpq : p < q := by exact_mod_cast hpz.trans_lt hq
  rw [sieveModulus_primeFactors] at hpmem
  have hnot := (Finset.mem_filter.mp hpmem).2.1
  apply hnot
  have hd := (prime_dvd_weightedMass_iff P.exponent P.exponent_pos n hp).mp
    (by simpa only [P.weightedMass_valueTuple hn] using hpv)
  obtain ⟨i, _, hi⟩ := (hp.prime.dvd_finsetProd_iff (fun i => (n i : ℕ))).mp hd
  apply dvd_trans _ (coordinate_dvd_mass _ i)
  apply Nat.dvd_of_mem_primeFactors
  rw [primeFactors_primeSelect]
  exact Finset.mem_inter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hp, hi, (n i).ne_zero⟩,
    Finset.mem_range.mpr hpq⟩

/-- Remove rough remainders from a finite sum once the selected-prefix sum is bounded. -/
theorem PolynomialSystem.sum_roughPrefix_le_of_selected_sum {k r : ℕ} (P : PolynomialSystem k r)
    {A B σ : ℝ} {F : ArithmeticMap k} (hF : Admissible A B σ F) (hA : 1 ≤ A) (hB : 0 ≤ B)
    (T : Finset ℤ) (n : ℤ → Tuple r) (q : ℤ → ℕ)
    (hn : ∀ t ∈ T, ∀ i, (n t i : ℕ) = ((P.R i).eval t).natAbs)
    {x α c S : ℝ} (hx : 1 < x) (hα : 0 < α)
    (hq : ∀ t ∈ T, x ^ α < (q t : ℝ))
    (hvalue : ∀ t ∈ T, ((P.total.eval t).natAbs : ℝ) ≤ x ^ c)
    (hselected : (∑ t ∈ T,
      pullback P.exponent F (primeSelect (n t) (Finset.range (q t)))) ≤ S) :
    (∑ t ∈ T, extendArithmeticMap F (fun j => ((P.Q j).eval t).natAbs)) ≤
      A ^ (c / α) * S := by
  calc
    _ ≤ ∑ t ∈ T, A ^ (c / α) *
        pullback P.exponent F (primeSelect (n t) (Finset.range (q t))) := by
      apply Finset.sum_le_sum
      intro t ht
      rw [← P.pullback_valueTuple F (hn t ht)]
      exact hF.pullback_primeSplit_le_of_rough hA hB P.exponent P.exponent_pos (n t) (q t)
        hx hα (hq t ht).le (by simpa only [P.weightedMass_valueTuple (hn t ht)] using hvalue t ht)
    _ = A ^ (c / α) * ∑ t ∈ T,
        pullback P.exponent F (primeSelect (n t) (Finset.range (q t))) := (Finset.mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hselected (Real.rpow_nonneg (by linarith) _)

end NairTenenbaum
