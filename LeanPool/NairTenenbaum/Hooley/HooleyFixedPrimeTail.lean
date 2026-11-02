/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Hooley.HooleyDivisorTail
public import LeanPool.NairTenenbaum.Hooley.HooleyFixedPrimeBound

/-! # Divisor-window tail saving in the presence of fixed prime divisors -/

@[expose] public section

namespace NairTenenbaum

open Real Filter Polynomial
open scoped Topology

theorem exists_polynomialDivisorLargeSum_power_saving_unrestricted {Q : ℤ[X]}
    (hirr : Irreducible (Q.map (Int.castRingHom ℚ))) {α η : ℝ}
    (hα : 0 < α) (hη : Real.log 4 - 1 < η) :
    ∃ δ x₀ C : ℝ, 0 < δ ∧ 1 < x₀ ∧ 0 < C ∧ ∀ x y : ℝ,
      x₀ < x → x ^ α ≤ y → y ≤ x / 2 →
        polynomialDivisorLargeSum Q η x y ≤ C * y * (Real.log x) ^ (-δ) := by
  obtain ⟨ε, hε, he⟩ := exists_hooley_tail_exponent hη
  let e : ℝ := (2 : ℝ) ^ (1 + ε) - (1 + ε) - 1
  let δ := -(e - ε * η) / 2
  have hδ : 0 < δ := by dsimp [δ, e]; linarith
  obtain ⟨x₀, C, hx₀, hC, H⟩ := exists_hooleyPolynomialSum_log_margin_unrestricted hirr
    (t := 1 + ε) (by linarith) hα hδ
  refine ⟨δ, x₀, C, hδ, hx₀, hC, fun x y hx hy hyx => ?_⟩
  have hxpos : 0 < x := by linarith [hx₀.trans hx]
  have hl : 0 < Real.log x := Real.log_pos (hx₀.trans hx)
  have hypos : 0 < y := (Real.rpow_pos_of_pos hxpos α).trans_le hy
  have hT : 0 < (Real.log x) ^ η := Real.rpow_pos_of_pos hl η
  have HE : ((Real.log x) ^ η) ^ (-ε) * (C * y * (Real.log x) ^ (e + δ)) =
      C * y * (Real.log x) ^ (-δ) := by
    rw [← Real.rpow_mul hl.le]
    calc
      _ = C * y * ((Real.log x) ^ (η * -ε) * (Real.log x) ^ (e + δ)) := by ring
      _ = C * y * (Real.log x) ^ (η * -ε + (e + δ)) := by rw [← Real.rpow_add hl]
      _ = _ := by congr 2; dsimp [δ]; ring
  calc
    _ ≤ ((Real.log x) ^ η) ^ (-ε) * hooleyPolynomialSum Q (1 + ε) x y :=
      polynomialDivisorWindow_large_sum_le Q hypos hT hε.le
    _ ≤ ((Real.log x) ^ η) ^ (-ε) * (C * y * (Real.log x) ^ (e + δ)) :=
      mul_le_mul_of_nonneg_left (H x y hx hy hyx) (Real.rpow_nonneg hT.le _)
    _ = _ := HE

theorem exists_polynomialDivisorLargeSum_small_unrestricted {Q : ℤ[X]}
    (hirr : Irreducible (Q.map (Int.castRingHom ℚ))) {α η c : ℝ} (hα : 0 < α)
    (hη : Real.log 4 - 1 < η) (hc : 0 < c) :
    ∃ x₀ : ℝ, 1 < x₀ ∧ ∀ x y : ℝ, x₀ < x → x ^ α ≤ y → y ≤ x / 2 →
      polynomialDivisorLargeSum Q η x y ≤ c * y := by
  obtain ⟨δ, x₁, C, hδ, hx₁, _, H⟩ := exists_polynomialDivisorLargeSum_power_saving_unrestricted
      hirr hα hη
  have HL : Tendsto (fun x : ℝ => C * (Real.log x) ^ (-δ)) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, mul_zero] using ((tendsto_rpow_neg_atTop hδ).comp
        Real.tendsto_log_atTop).const_mul C
  obtain ⟨x₂, hx₂⟩ := eventually_atTop.mp (HL.eventually (gt_mem_nhds hc))
  refine ⟨max x₁ x₂, hx₁.trans_le (le_max_left _ _), fun x y hx hy hyx => ?_⟩
  have hx₁' : x₁ < x := (le_max_left _ _).trans_lt hx
  have hy₀ : 0 ≤ y := (Real.rpow_nonneg (by linarith [hx₁.trans hx₁'] : 0 ≤ x) α).trans hy
  apply (H x y hx₁' hy hyx).trans
  have HB := mul_le_mul_of_nonneg_right (hx₂ x ((le_max_right _ _).trans hx.le)).le hy₀
  simpa only [mul_assoc, mul_right_comm C y] using HB

theorem exists_polynomialDivisorWindowSum_le_hits_add_small_unrestricted {Q : ℤ[X]}
    (hirr : Irreducible (Q.map (Int.castRingHom ℚ))) {α η c : ℝ} (hα : 0 < α)
    (hη : Real.log 4 - 1 < η) (hc : 0 < c) :
    ∃ x₀ : ℝ, 1 < x₀ ∧ ∀ x y : ℝ, x₀ < x → x ^ α ≤ y → y ≤ x / 2 →
      polynomialDivisorWindowSum Q x y ≤ (Real.log x) ^ η * polynomialDivisorHitCount Q x y + c *
          y := by
  classical
  obtain ⟨x₀, hx₀, H⟩ := exists_polynomialDivisorLargeSum_small_unrestricted hirr hα hη hc
  refine ⟨x₀, hx₀, fun x y hx hy hyx => ?_⟩
  have HS := polynomialDivisorWindow_small_sum_le Q x y
    (Real.rpow_nonneg (Real.log_pos (hx₀.trans hx)).le η)
  have HL := H x y hx hy hyx
  have HE := Finset.sum_filter_add_sum_filter_not (shortInterval x y)
    (fun n : ℕ => (dyadicDivisorCount (Q.eval (n : ℤ)).natAbs y : ℝ) ≤ (Real.log x) ^ η)
    (fun n : ℕ => (dyadicDivisorCount (Q.eval (n : ℤ)).natAbs y : ℝ))
  simp only [not_le] at HE
  change _ + polynomialDivisorLargeSum Q η x y = polynomialDivisorWindowSum Q x y at HE
  linarith

end NairTenenbaum
