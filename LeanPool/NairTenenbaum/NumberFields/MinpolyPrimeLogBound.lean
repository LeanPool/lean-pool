/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Arithmetic.PrimeProductLogBound
public import LeanPool.NairTenenbaum.Hooley.HooleyDivisorEulerBound
public import LeanPool.NairTenenbaum.NumberFields.ConductorNonzero

/-! # Sharp logarithmic upper bound for minimal-polynomial prime roots

For an integral primitive generator of a number field, the prime root series
is bounded by `−log(σ−1)+O(1)` as `σ` decreases to one. The coefficient of
the logarithm is one. The finite conductor-prime contribution is explicit.
-/

@[expose] public section

namespace NairTenenbaum

open Finset Real Polynomial NumberField

variable {K : Type*} [Field K] [NumberField K]

theorem minpoly_goodPrimeSum_le_log_idealNormDirichlet (θ : 𝓞 K)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    (hgood : ∀ p ∈ S, ¬p ∣ RingOfIntegers.exponent θ) {σ : ℝ} (hσ : 1 < σ) :
    (∑ p ∈ S, (rootCount (minpoly ℤ θ) p : ℝ) * (p : ℝ) ^ (-σ)) ≤
      Real.log (idealNormDirichlet K σ) +
      ((minpoly ℤ θ).natDegree : ℝ) ^ 2 * ∑' n : ℕ, (n : ℝ) ^ (-2 : ℝ) := by
  apply (monic_primeRoot_sum_le_log_product (minpoly.monic θ.isIntegral) S hS hσ.le).trans
  apply add_le_add_left
  apply Real.log_le_log _ (minpoly_goodPrimeProduct_le_idealNormDirichlet θ S hS hgood hσ)
  apply prod_pos
  intro p _
  have := mul_nonneg (Nat.cast_nonneg (rootCount (minpoly ℤ θ) p))
    (Real.rpow_nonneg (Nat.cast_nonneg p) (-σ))
  linarith

theorem monic_primeRoot_sum_le_degree_mul_card {Q : ℤ[X]} (hQ : Q.Monic)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) {σ : ℝ} (hσ : 1 ≤ σ) :
    (∑ p ∈ S, (rootCount Q p : ℝ) * (p : ℝ) ^ (-σ)) ≤
      (Q.natDegree : ℝ) * S.card := by
  calc
    _ ≤ ∑ _p ∈ S, (Q.natDegree : ℝ) := by
      apply sum_le_sum
      intro p hp
      apply (monic_rootPrimePowerWeight_le_degree_div hQ (hS p hp) hσ).trans
      exact div_le_self (Nat.cast_nonneg _) (by exact_mod_cast (hS p hp).one_le)
    _ = _ := by simp [mul_comm]

theorem minpoly_primeSum_le_log_idealNormDirichlet (θ : 𝓞 K) (B : PowerBasis ℚ K)
    (hB : B.gen = (θ : K)) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {σ : ℝ} (hσ : 1 < σ) :
    (∑ p ∈ S, (rootCount (minpoly ℤ θ) p : ℝ) * (p : ℝ) ^ (-σ)) ≤
      Real.log (idealNormDirichlet K σ) +
      ((minpoly ℤ θ).natDegree : ℝ) ^ 2 * ∑' n : ℕ, (n : ℝ) ^ (-2 : ℝ) +
      (minpoly ℤ θ).natDegree * (RingOfIntegers.exponent θ).primeFactors.card := by
  classical
  have hbad : S.filter (fun p => p ∣ RingOfIntegers.exponent θ) ⊆
      (RingOfIntegers.exponent θ).primeFactors := by
    intro p hp
    exact Nat.mem_primeFactors.mpr ⟨hS p (mem_filter.mp hp).1,
      (mem_filter.mp hp).2, conductor_exponent_ne_zero θ B hB⟩
  have Hbad := (monic_primeRoot_sum_le_degree_mul_card (minpoly.monic θ.isIntegral)
    (S.filter (fun p => p ∣ RingOfIntegers.exponent θ))
    (fun p hp => hS p (mem_filter.mp hp).1) hσ.le).trans
      (mul_le_mul_of_nonneg_left (show ((S.filter (fun p => p ∣ RingOfIntegers.exponent θ)).card :
          ℝ) ≤
        ((RingOfIntegers.exponent θ).primeFactors.card : ℝ) by
          exact_mod_cast card_le_card hbad) (Nat.cast_nonneg _))
  have Hgood := minpoly_goodPrimeSum_le_log_idealNormDirichlet θ
    (S.filter (fun p => ¬p ∣ RingOfIntegers.exponent θ))
    (fun p hp => hS p (mem_filter.mp hp).1) (fun _ hp => (mem_filter.mp hp).2) hσ
  have Hsplit := sum_filter_add_sum_filter_not S (fun p => p ∣ RingOfIntegers.exponent θ)
    (fun p => (rootCount (minpoly ℤ θ) p : ℝ) * (p : ℝ) ^ (-σ))
  linarith

theorem exists_minpoly_primeSum_log_bound (θ : 𝓞 K) (B : PowerBasis ℚ K)
    (hB : B.gen = (θ : K)) :
    ∃ C b : ℝ, 0 ≤ C ∧ 1 < b ∧ ∀ σ : ℝ, 1 < σ → σ < b →
      ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime) →
        (∑ p ∈ S, (rootCount (minpoly ℤ θ) p : ℝ) * (p : ℝ) ^ (-σ)) ≤
          C - Real.log (σ - 1) := by
  obtain ⟨C, b, hC, hb, hbound⟩ := exists_idealNormDirichlet_pole_bound K
  let E : ℝ := ((minpoly ℤ θ).natDegree : ℝ) ^ 2 * ∑' n : ℕ, (n : ℝ) ^ (-2 : ℝ) +
    (minpoly ℤ θ).natDegree * (RingOfIntegers.exponent θ).primeFactors.card
  refine ⟨max 0 (Real.log C + E), b, le_max_left _ _, hb, fun σ hσ hσb S hS => ?_⟩
  have hpos : 0 < idealNormDirichlet K σ := by
    have H := minpoly_goodPrimeProduct_le_idealNormDirichlet θ ∅ (by simp) (by simp) hσ
    simp only [prod_empty] at H
    linarith
  have Hlog := Real.log_le_log hpos (hbound σ hσ hσb)
  rw [Real.log_div hC.ne' (by linarith : σ - 1 ≠ 0)] at Hlog
  have H := minpoly_primeSum_le_log_idealNormDirichlet θ B hB S hS hσ
  have HE := le_max_right 0 (Real.log C + E)
  dsimp only [E] at HE
  linarith

end NairTenenbaum
