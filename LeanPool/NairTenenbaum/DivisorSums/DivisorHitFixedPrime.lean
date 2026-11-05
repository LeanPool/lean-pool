/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.DivisorSums.PolynomialDivisorWindowCount
public import LeanPool.NairTenenbaum.Hooley.HooleyFixedPrimeTail

/-! # Divisor hits without a restriction on fixed prime divisors

The analytic tail estimate covers fixed prime divisors. The final implication keeps
its numerical root-density lower bound explicit; that arithmetic estimate
is a separate remaining input to Theorem 2.
-/

@[expose] public section

namespace NairTenenbaum

open Real Polynomial

theorem exists_divisorWindow_rootDensity_le_hits_add_small_unrestricted {Q : ℤ[X]}
    (hirr : Irreducible (Q.map (Int.castRingHom ℚ))) {α η c : ℝ} (hα : 0 < α)
    (hη : Real.log 4 - 1 < η) (hc : 0 < c) :
    ∃ x₀ : ℝ, 1 < x₀ ∧ ∀ x y : ℝ, x₀ < x → x ^ α ≤ y → y ≤ x / 2 →
      (y / 2) * dyadicRootDensitySum Q y ≤
        (Real.log x) ^ η * polynomialDivisorHitCount Q x y + c * y := by
  have hQ₀ : Q ≠ 0 := by intro h; simp [h] at hirr
  obtain ⟨x₁, _, H₁⟩ := exists_polynomial_eval_nonzero_on_shortInterval hQ₀
  obtain ⟨x₂, hx₂, H₂⟩ := exists_polynomialDivisorWindowSum_le_hits_add_small_unrestricted hirr hα
      hη hc
  refine ⟨max x₁ x₂, hx₂.trans_le (le_max_right _ _), fun x y hx hy hyx => ?_⟩
  have hx₂' : x₂ < x := (le_max_right _ _).trans_lt hx
  have hxpos : 0 < x := by linarith [hx₂.trans hx₂']
  have hypos : 0 < y := (Real.rpow_pos_of_pos hxpos α).trans_le hy
  exact (polynomialDivisorWindowSum_ge_rootDensity Q hxpos.le hypos
    (H₁ x y ((le_max_left _ _).trans_lt hx))).trans (H₂ x y hx₂' hy hyx)

theorem exists_polynomialDivisorHitCount_density_bound_unrestricted {Q : ℤ[X]}
    (hirr : Irreducible (Q.map (Int.castRingHom ℚ))) {α η c : ℝ} (hα : 0 < α)
    (hη : Real.log 4 - 1 < η) (hc : 0 < c) :
    ∃ x₀ : ℝ, 1 < x₀ ∧ ∀ x y : ℝ, x₀ < x → x ^ α ≤ y → y ≤ x / 2 →
      4 * c ≤ dyadicRootDensitySum Q y →
        c * y / (Real.log x) ^ η ≤ polynomialDivisorHitCount Q x y := by
  obtain ⟨x₀, hx₀, H⟩ := exists_divisorWindow_rootDensity_le_hits_add_small_unrestricted hirr hα
      hη hc
  refine ⟨x₀, hx₀, fun x y hx hy hyx hρ => ?_⟩
  have hxpos : 0 < x := by linarith [hx₀.trans hx]
  have hypos : 0 < y := (Real.rpow_pos_of_pos hxpos α).trans_le hy
  have hL : 0 < (Real.log x) ^ η := Real.rpow_pos_of_pos (Real.log_pos (hx₀.trans hx)) η
  have HE := H x y hx hy hyx
  have HD := mul_le_mul_of_nonneg_left hρ (show 0 ≤ y / 2 by positivity)
  apply (div_le_iff₀ hL).mpr
  nlinarith

end NairTenenbaum
