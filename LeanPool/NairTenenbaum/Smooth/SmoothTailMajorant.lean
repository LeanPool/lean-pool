/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Polynomials.PolynomialValueTuples
public import LeanPool.NairTenenbaum.Smooth.SmoothTailSieve

/-! # Selected smooth prefixes with a lower mass cutoff -/

@[expose] public section

namespace NairTenenbaum

open Finset

/-- Grouping selected divisors preserves both smoothness and the lower mass
cutoff. Distinct integers can have the same selected tuple. -/
theorem PolynomialSystem.sum_selectedSmoothTailDivisors_le {k r : ℕ} (P : PolynomialSystem k r)
    {F : ArithmeticMap k} (hF : ∀ n, 0 ≤ F n) (N : ℕ+) (s : Finset ℕ) (X : ℝ) (a b : ℤ) (z : ℝ)
    (T : Finset ℤ) (m : ℤ → Tuple r) (hT : T ⊆ Finset.Ioc a b)
    (hm : ∀ t ∈ T, weightedMass P.exponent (m t) ≤ N)
    (hdiv : ∀ t ∈ T, ∀ i, (m t i : ℤ) ∣ (P.R i).eval t)
    (hsmooth : ∀ t ∈ T, ∀ i, (m t i : ℕ) ∈ Nat.factoredNumbers s)
    (hlarge : ∀ t ∈ T, X < (weightedMass P.exponent (m t) : ℝ))
    (hsift : ∀ t ∈ T, Nat.Coprime (sieveModulus P.total (mass (m t)) z) (P.total.eval t).natAbs) :
    (∑ t ∈ T, pullback P.exponent F (m t)) ≤ P.smoothTailSiftedSum F N s X a b z := by
  classical
  have hmap : ∀ t ∈ T, m t ∈ smoothTailDivisorTuples P.exponent N s X := by
    intro t ht
    apply Finset.mem_filter.mpr
    refine ⟨?_, hsmooth t ht, hlarge t ht⟩
    exact Finset.mem_filter.mpr ⟨mem_tupleBox.mpr (fun i =>
      (coordinate_le_weightedMass P.exponent P.exponent_pos (m t) i).trans (hm t ht)), hm t ht⟩
  exact P.sum_selected_le_siftedDivisorSum hF (smoothTailDivisorTuples P.exponent N s X)
    P.total (fun m => sieveModulus P.total (mass m) z) a b T m hT hmap hdiv
    hsift

/-- Rough remainders can be removed while retaining the smooth mass tail of
the selected prefix. The sifting cutoff is `x^α`; its relation to the smoothness
support is unrestricted. -/
theorem PolynomialSystem.sum_roughSmoothTailPrefix_le {k r : ℕ} (P : PolynomialSystem k r)
    {A B σ : ℝ} {F : ArithmeticMap k} (hF : Admissible A B σ F) (hA : 1 ≤ A) (hB : 0 ≤ B)
    (N : ℕ+) (s : Finset ℕ) (X : ℝ) (a b : ℤ) (T : Finset ℤ) (n : ℤ → Tuple r) (q : ℤ → ℕ)
    (hT : T ⊆ Finset.Ioc a b) (hn : ∀ t ∈ T, ∀ i, (n t i : ℕ) = ((P.R i).eval t).natAbs)
    {x α c : ℝ} (hx : 1 < x) (hα : 0 < α)
    (hq : ∀ t ∈ T, x ^ α < (q t : ℝ))
    (hsmall : ∀ t ∈ T, weightedMass P.exponent (primeSelect (n t) (Finset.range (q t))) ≤ N)
    (hsmooth : ∀ t ∈ T, ∀ i,
      (primeSelect (n t) (Finset.range (q t)) i : ℕ) ∈ Nat.factoredNumbers s)
    (hlarge : ∀ t ∈ T, X < (weightedMass P.exponent
      (primeSelect (n t) (Finset.range (q t))) : ℝ))
    (hvalue : ∀ t ∈ T, ((P.total.eval t).natAbs : ℝ) ≤ x ^ c) :
    (∑ t ∈ T, extendArithmeticMap F (fun j => ((P.Q j).eval t).natAbs)) ≤
      A ^ (c / α) * P.smoothTailSiftedSum F N s X a b (x ^ α) := by
  let m := fun t => primeSelect (n t) (Finset.range (q t))
  have H := P.sum_selectedSmoothTailDivisors_le hF.nonneg N s X a b (x ^ α) T m hT hsmall
    (fun t ht i => Int.natCast_dvd.mpr (by
      simpa only [hn t ht i] using primeSelect_coordinate_dvd (n t) (Finset.range (q t)) i))
    hsmooth hlarge
    (fun t ht => P.primeSelect_sieve_coprime (hn t ht) (Real.rpow_nonneg (by linarith) _) (hq t ht))
  exact P.sum_roughPrefix_le_of_selected_sum hF hA hB T n q hn hx hα hq hvalue H

end NairTenenbaum
