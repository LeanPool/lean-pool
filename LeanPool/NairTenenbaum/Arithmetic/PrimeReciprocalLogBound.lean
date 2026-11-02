/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Hooley.HooleySquarefreeRankin

/-! # A logarithmic upper bound for finite sums of prime reciprocals -/

@[expose] public section

namespace NairTenenbaum

open Real Polynomial Finset

theorem exists_primeReciprocal_log_bound :
    ∃ C z₀ : ℝ, 0 ≤ C ∧ 1 < z₀ ∧ ∀ z : ℝ, z₀ < z →
      ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime ∧ (p : ℝ) ≤ z) →
        (∑ p ∈ S, 1 / (p : ℝ)) ≤ Real.exp 1 * (C + Real.log (Real.log z)) := by
  have HI : Irreducible ((X : ℤ[X]).map (Int.castRingHom ℚ)) := by
    simpa only [Polynomial.map_X] using (Polynomial.irreducible_X : Irreducible (X : ℚ[X]))
  obtain ⟨C, b, hC, hb, H⟩ := exists_irreducible_primeSum_log_bound HI
  let z₀ := Real.exp (1 / (b - 1) + 1)
  have hd : 0 < b - 1 := by linarith
  have hz₀ : 1 < z₀ := Real.one_lt_exp_iff.mpr (by positivity)
  refine ⟨C, z₀, hC, hz₀, fun z hz S hS => ?_⟩
  have hz₁ : 1 < z := hz₀.trans hz
  have hl : 0 < Real.log z := Real.log_pos hz₁
  have hlbig : 1 / (b - 1) + 1 < Real.log z := by
    have HH := Real.log_lt_log (Real.exp_pos (1 / (b - 1) + 1)) hz
    rwa [Real.log_exp] at HH
  have hσ : 1 < 1 + 1 / Real.log z := by linarith [one_div_pos.mpr hl]
  have hσb : 1 + 1 / Real.log z < b := by
    have H₁ : 1 / (b - 1) < Real.log z := by linarith
    have H₂ := (div_lt_iff₀ hd).mp H₁
    have H₃ := (div_lt_iff₀ hl).mpr (show 1 < (b - 1) * Real.log z by nlinarith)
    linarith
  have HE : z ^ ((1 + 1 / Real.log z) - 1) = Real.exp 1 := by
    rw [Real.rpow_def_of_pos (by linarith), add_sub_cancel_left]
    congr 1
    field_simp
  have HB := H (1 + 1 / Real.log z) hσ hσb S (fun p hp => (hS p hp).1)
  simp only [rootCount_X, Nat.cast_one, one_mul, add_sub_cancel_left,
    one_div, Real.log_inv, sub_neg_eq_add] at HB
  calc
    _ ≤ ∑ p ∈ S, Real.exp 1 * (p : ℝ) ^ (-(1 + 1 / Real.log z)) := by
      apply sum_le_sum
      intro p hp
      have HR := reciprocal_le_rankin_weight hσ.le (hS p hp).1.pos (hS p hp).2
      rw [HE] at HR
      simpa only [one_div] using HR
    _ = Real.exp 1 * ∑ p ∈ S, (p : ℝ) ^ (-(1 + 1 / Real.log z)) := by rw [mul_sum]
    _ ≤ _ := by simpa only [one_div] using mul_le_mul_of_nonneg_left HB (Real.exp_pos 1).le

end NairTenenbaum
