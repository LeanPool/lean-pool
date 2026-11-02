/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Arithmetic.PrimeReciprocalLogBound
public import LeanPool.NairTenenbaum.Arithmetic.RoughMass

/-! # A uniform iterated-logarithm bound for the reciprocal totient -/

@[expose] public section

namespace NairTenenbaum

open Real Polynomial Finset

theorem primeFactors_card_le_log {n : ℕ} (hn : n ≠ 0) :
    (n.primeFactors.card : ℝ) ≤ Real.log n / Real.log 2 := by
  have hc : n.primeFactors.card ≤ bigOmega n := List.toFinset_card_le _
  exact (by exact_mod_cast hc : (n.primeFactors.card : ℝ) ≤ bigOmega n).trans
    (rough_bigOmega_le hn (by norm_num : (1 : ℝ) < 2)
      (fun p hp => by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le))

theorem largePrimeReciprocal_le {n : ℕ} (hn : n ≠ 0) {x : ℝ} (hx : 1 < x)
    (hnx : (n : ℝ) ≤ x) :
    (∑ p ∈ n.primeFactors.filter (fun p : ℕ => Real.log x < (p : ℝ)), 1 / (p : ℝ)) ≤
      1 / Real.log 2 := by
  have hl : 0 < Real.log x := Real.log_pos hx
  have hl₂ : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc : (n.primeFactors.card : ℝ) ≤ Real.log x / Real.log 2 :=
    (primeFactors_card_le_log hn).trans (div_le_div_of_nonneg_right
      (Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hn) hnx) hl₂.le)
  calc
    _ ≤ ∑ p ∈ n.primeFactors.filter (fun p : ℕ => Real.log x < (p : ℝ)), 1 / Real.log x := by
      apply sum_le_sum
      intro p hp
      exact one_div_le_one_div_of_le hl (mem_filter.mp hp).2.le
    _ ≤ ∑ _p ∈ n.primeFactors, 1 / Real.log x :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => (one_div_pos.mpr hl).le)
    _ = (n.primeFactors.card : ℝ) / Real.log x := by simp [div_eq_mul_inv]
    _ ≤ (Real.log x / Real.log 2) / Real.log x := div_le_div_of_nonneg_right hc hl.le
    _ = 1 / Real.log 2 := by field_simp

theorem reciprocalTotient_le_exp_primeSum {n : ℕ} (hn : n ≠ 0) :
    (n : ℝ) / n.totient ≤ Real.exp (2 * ∑ p ∈ n.primeFactors, 1 / (p : ℝ)) := by
  have H := totientTwist_eq_prod 1 hn
  simp only [totientTwist, pow_one] at H
  rw [H, mul_sum, Real.exp_sum]
  apply Finset.prod_le_prod₀ (fun p _ => by positivity)
  intro p hp
  have hp' := Nat.prime_of_mem_primeFactors hp
  have HE : (p : ℝ) / p.totient = (1 - 1 / (p : ℝ))⁻¹ := by
    rw [Nat.totient_prime hp']
    have hp₀ : (p : ℝ) ≠ 0 := by exact_mod_cast hp'.ne_zero
    have hp₁ : (p : ℝ) - 1 ≠ 0 := by
      have HH : (1 : ℝ) < p := by exact_mod_cast hp'.one_lt
      linarith
    rw [Nat.cast_sub hp'.one_le, Nat.cast_one]
    field_simp
  rw [HE]
  have HS := sieveFactor_inv_le_exp noFixedPrimeDivisor_X
    (g := 1) (by simp) hp' (by simpa using hp'.two_le)
  simpa only [rootCount_X, Nat.cast_one, mul_one, mul_one_div] using HS

theorem exists_reciprocalTotient_logLog_bound :
    ∃ A B x₀ : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ 1 < x₀ ∧ ∀ x : ℝ, x₀ < x →
      ∀ n : ℕ, n ≠ 0 → (n : ℝ) ≤ x →
        (n : ℝ) / n.totient ≤ Real.exp (A + B * Real.log (Real.log (Real.log x))) := by
  obtain ⟨C, z₀, hC, hz₀, H⟩ := exists_primeReciprocal_log_bound
  refine ⟨2 * (Real.exp 1 * C + 1 / Real.log 2), 2 * Real.exp 1, Real.exp z₀,
    by positivity, by positivity, Real.one_lt_exp_iff.mpr (by linarith), fun x hx n hn hnx => ?_⟩
  have hz : z₀ < Real.log x := by
    have HH := Real.log_lt_log (Real.exp_pos z₀) hx
    simpa only [Real.log_exp] using HH
  have hx₁ : 1 < x := (Real.one_lt_exp_iff.mpr (by linarith : 0 < z₀)).trans hx
  have HS := H (Real.log x) hz (n.primeFactors.filter (fun p => (p : ℝ) ≤ Real.log x))
    (fun p hp => ⟨Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1, (mem_filter.mp hp).2⟩)
  have HL := largePrimeReciprocal_le hn hx₁ hnx
  have HE := sum_filter_add_sum_filter_not n.primeFactors (fun p => (p : ℝ) ≤ Real.log x)
    (fun p => 1 / (p : ℝ))
  simp only [not_le] at HE
  apply (reciprocalTotient_le_exp_primeSum hn).trans
  apply Real.exp_le_exp.mpr
  nlinarith

end NairTenenbaum
