/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Hooley.HooleyLogarithmicSaving

/-! # Absorbing the subexponential factor into a logarithmic margin -/

@[expose] public section

namespace NairTenenbaum

open Real Filter Polynomial

theorem hooley_short_exponent_nonneg {t : ℝ} (ht : 1 ≤ t) :
    0 ≤ (2 : ℝ) ^ t - t - 1 := by
  have H := one_add_mul_self_le_rpow_one_add (s := 1) (by norm_num) ht
  norm_num at H
  linarith

theorem exists_hooleyPolynomialSum_log_margin {Q : ℤ[X]} (hQ : NoFixedPrimeDivisor Q)
    (hirr : Irreducible (Q.map (Int.castRingHom ℚ))) {t α δ : ℝ}
    (ht : 1 ≤ t) (hα : 0 < α) (hδ : 0 < δ) :
    ∃ x₀ C : ℝ, 1 < x₀ ∧ 0 < C ∧ ∀ x y : ℝ,
      x₀ < x → x ^ α ≤ y → y ≤ x →
        hooleyPolynomialSum Q t x y ≤ C * y * (Real.log x) ^ ((2 : ℝ) ^ t - t - 1 + δ) := by
  let η := Real.sqrt (2 * t) + 1
  obtain ⟨x₁, C, hx₁, hC, H⟩ := exists_hooleyPolynomialSum_sharp_bound hQ hirr ht hα
    (show Real.sqrt (2 * t) < η by dsimp [η]; linarith)
  obtain ⟨x₂, H₂⟩ := eventually_atTop.mp (eventually_hooleySubexponential_le_log_rpow η hδ)
  refine ⟨max x₁ x₂, C, hx₁.trans_le (le_max_left _ _), hC, fun x y hx hy hyx => ?_⟩
  have hx₁' := (le_max_left _ _).trans_lt hx
  have hxpos : 0 < x := by linarith [hx₁.trans hx₁']
  have hl : 0 < Real.log x := Real.log_pos (hx₁.trans hx₁')
  have hy₀ : 0 ≤ y := (Real.rpow_nonneg hxpos.le α).trans hy
  calc
    _ ≤ C * (y * (Real.log x) ^ ((2 : ℝ) ^ t - t - 1) * hooleySubexponential η x) := H x y hx₁' hy
        hyx
    _ ≤ C * (y * (Real.log x) ^ ((2 : ℝ) ^ t - t - 1) * (Real.log x) ^ δ) := by
      apply mul_le_mul_of_nonneg_left _ hC.le
      exact mul_le_mul_of_nonneg_left (H₂ x ((le_max_right _ _).trans hx.le)) (by positivity)
    _ = _ := by
      rw [Real.rpow_add (Real.log_pos (hx₁.trans hx₁'))]
      ring

end NairTenenbaum
