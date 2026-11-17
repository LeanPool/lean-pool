/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.Polynomials.PolynomialValueTuples

/-! # From selected polynomial divisors to the sifted tuple sum -/

@[expose] public section

namespace NairTenenbaum

open Finset

/-- Grouping a selected divisor for each integer by its tuple gives the sifted
small-divisor majorant. Distinct integers can have the same selected tuple. -/
theorem PolynomialSystem.sum_selectedDivisors_le {k r : ℕ} (P : PolynomialSystem k r)
    {F : ArithmeticMap k} (hF : ∀ n, 0 ≤ F n) (N : ℕ+) (a b : ℤ) (z : ℝ)
    (T : Finset ℤ) (m : ℤ → Tuple r) (hT : T ⊆ Finset.Ioc a b)
    (hm : ∀ t ∈ T, weightedMass P.exponent (m t) ≤ N)
    (hdiv : ∀ t ∈ T, ∀ i, (m t i : ℤ) ∣ (P.R i).eval t)
    (hsift : ∀ t ∈ T, Nat.Coprime (sieveModulus P.total (mass (m t)) z) (P.total.eval t).natAbs) :
    (∑ t ∈ T, pullback P.exponent F (m t)) ≤ P.smallDivisorSiftedSum F N a b z := by
  classical
  have hmap : ∀ t ∈ T, m t ∈ smallDivisorTuples P.exponent N := by
    intro t ht
    exact Finset.mem_filter.mpr ⟨mem_tupleBox.mpr (fun i =>
      (coordinate_le_weightedMass P.exponent P.exponent_pos (m t) i).trans (hm t ht)), hm t ht⟩
  exact P.sum_selected_le_siftedDivisorSum hF (smallDivisorTuples P.exponent N)
    P.total (fun m => sieveModulus P.total (mass m) z) a b T m hT hmap hdiv
    hsift

/-- Equation (31), with explicit growth constant and a proven sieve condition.
The finite set can be any part of the interval whose selected prefixes are small
and whose next-prime cutoffs exceed `x^α`. -/
theorem PolynomialSystem.sum_roughPrefix_le {k r : ℕ} (P : PolynomialSystem k r)
    {A B σ : ℝ} {F : ArithmeticMap k} (hF : Admissible A B σ F) (hA : 1 ≤ A) (hB : 0 ≤ B)
    (N : ℕ+) (a b : ℤ) (T : Finset ℤ) (n : ℤ → Tuple r) (q : ℤ → ℕ)
    (hT : T ⊆ Finset.Ioc a b) (hn : ∀ t ∈ T, ∀ i, (n t i : ℕ) = ((P.R i).eval t).natAbs)
    {x α c : ℝ} (hx : 1 < x) (hα : 0 < α)
    (hq : ∀ t ∈ T, x ^ α < (q t : ℝ))
    (hsmall : ∀ t ∈ T, weightedMass P.exponent (primeSelect (n t) (Finset.range (q t))) ≤ N)
    (hvalue : ∀ t ∈ T, ((P.total.eval t).natAbs : ℝ) ≤ x ^ c) :
    (∑ t ∈ T, extendArithmeticMap F (fun j => ((P.Q j).eval t).natAbs)) ≤
      A ^ (c / α) * P.smallDivisorSiftedSum F N a b (x ^ α) := by
  let m := fun t => primeSelect (n t) (Finset.range (q t))
  have H := P.sum_selectedDivisors_le hF.nonneg N a b (x ^ α) T m hT hsmall
    (fun t ht i => Int.natCast_dvd.mpr (by
      simpa only [hn t ht i] using primeSelect_coordinate_dvd (n t) (Finset.range (q t)) i))
    (fun t ht => P.primeSelect_sieve_coprime (hn t ht) (Real.rpow_nonneg (by linarith) _) (hq t ht))
  exact P.sum_roughPrefix_le_of_selected_sum hF hA hB T n q hn hx hα hq hvalue H

end NairTenenbaum
