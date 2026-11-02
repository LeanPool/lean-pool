/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.DivisorSums.PolynomialDivisorWindowCount
public import LeanPool.NairTenenbaum.NumberFields.ConvolutionMean

/-! # Positive linear means give lower bounds in dyadic divisor windows -/

@[expose] public section

namespace NairTenenbaum

open Finset Filter Real Polynomial
open scoped Topology

theorem sum_shortInterval_half_eq_summatory_sub (a : ℕ → ℝ) {y : ℝ} (hy : 0 ≤ y) :
    (∑ n ∈ shortInterval (y / 2) (y / 2), a n) =
      arithmeticSummatory a y - arithmeticSummatory a (y / 2) := by
  have H := sum_Ioc_consecutive a (Nat.zero_le ⌊y / 2⌋₊)
    (Nat.floor_mono (show y / 2 ≤ y by linarith))
  change (∑ n ∈ Ioc ⌊y / 2⌋₊ ⌊y / 2 + y / 2⌋₊, a n) = _
  rw [show y / 2 + y / 2 = y by ring]
  unfold arithmeticSummatory
  simp only [← Icc_succ_left_eq_Ioc, Order.succ_eq_add_one, zero_add] at H ⊢
  linarith

theorem tendsto_dyadic_mean {a : ℕ → ℝ} {L : ℝ}
    (h : Tendsto (fun x : ℝ => arithmeticSummatory a x / x) atTop (𝓝 L)) :
    Tendsto (fun y : ℝ => (∑ n ∈ shortInterval (y / 2) (y / 2), a n) / y)
      atTop (𝓝 (L / 2)) := by
  have Hhalf := (h.comp (tendsto_id.atTop_div_const (by norm_num : (0 : ℝ) < 2))).div_const 2
  have H := h.sub Hhalf
  rw [show L - L / 2 = L / 2 by ring] at H
  apply H.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with y hy
  rw [sum_shortInterval_half_eq_summatory_sub a hy]
  dsimp only [Function.comp_apply, id_eq]
  ring

theorem eventually_dyadic_weighted_sum_ge_of_mean {a : ℕ → ℝ} {L : ℝ}
    (ha : ∀ n, 0 ≤ a n) (hL : 0 < L)
    (h : Tendsto (fun x : ℝ => arithmeticSummatory a x / x) atTop (𝓝 L)) :
    ∀ᶠ y : ℝ in atTop, L / 4 ≤ ∑ n ∈ shortInterval (y / 2) (y / 2), a n / n := by
  have H := (tendsto_dyadic_mean h).eventually_const_lt (show L / 4 < L / 2 by linarith)
  filter_upwards [H, eventually_gt_atTop (0 : ℝ)] with y hy hy0
  apply hy.le.trans
  rw [sum_div]
  apply sum_le_sum
  intro n hn
  have hnlo : y / 2 < (n : ℝ) :=
    (Nat.floor_lt (half_pos hy0).le).mp (mem_Ioc.mp hn).1
  have hnhi : (n : ℝ) ≤ y := by
    have HH := (Nat.le_floor_iff (show 0 ≤ y / 2 + y / 2 by positivity)).mp (mem_Ioc.mp hn).2
    linarith
  exact div_le_div_of_nonneg_left (ha n) (by linarith) hnhi

theorem eventually_dyadicRootDensity_ge_of_minorant_mean {Q : ℤ[X]} {a : ℕ → ℝ} {L : ℝ}
    (ha : ∀ n, 0 ≤ a n) (hroot : ∀ n, a n ≤ rootCount Q n) (hL : 0 < L)
    (h : Tendsto (fun x : ℝ => arithmeticSummatory a x / x) atTop (𝓝 L)) :
    ∀ᶠ y : ℝ in atTop, L / 4 ≤ dyadicRootDensitySum Q y := by
  filter_upwards [eventually_dyadic_weighted_sum_ge_of_mean ha hL h] with y hy
  apply hy.trans
  apply sum_le_sum
  intro n _
  exact div_le_div_of_nonneg_right (hroot n) (Nat.cast_nonneg n)

end NairTenenbaum
