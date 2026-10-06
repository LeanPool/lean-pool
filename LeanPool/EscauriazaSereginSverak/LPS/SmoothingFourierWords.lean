/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedR12FinalField

/-!
# Ordered Fourier coordinate symbols

A spatial word corresponds to a product of coordinate frequency
multipliers. Its growth is bounded by the word length, which is the
input for the all-order Bessel-to-classical derivative bridge.
-/

public section

open CKN

open MeasureTheory FourierTransform Complex
open scoped ENNReal FourierTransform Real


noncomputable section

namespace ESS

open CKN.Foundation.Parabolic

/-- Fourier multiplier of an ordered spatial derivative word. -/
@[expose] def lps_fourierWordSymbol (α : List (Fin 3))
    (ξ : L2Vec3) : ℂ :=
  (α.map fun j => CKN.Leray.regR12CoordSymbol j ξ).prod

/-- Appending one derivative multiplies by its coordinate symbol. -/
theorem lps_fourierWordSymbol_append (α : List (Fin 3))
    (j : Fin 3) (ξ : L2Vec3) :
    lps_fourierWordSymbol (α ++ [j]) ξ =
      CKN.Leray.regR12CoordSymbol j ξ * lps_fourierWordSymbol α ξ := by
  simp only [lps_fourierWordSymbol, List.map_append, List.prod_append,
    List.map_singleton, List.prod_singleton]
  ring

/-- An ordered word of length `r` has at most polynomial Fourier
growth of order `r` (`prop:lps-smoothing`). -/
theorem lps_fourierWordSymbol_norm_le (α : List (Fin 3))
    (ξ : L2Vec3) :
    ‖lps_fourierWordSymbol α ξ‖ ≤
      (2 * π) ^ α.length * ‖ξ‖ ^ α.length := by
  induction α with
  | nil => simp [lps_fourierWordSymbol]
  | cons j α ih =>
      have hj := CKN.Leray.regR12CoordSymbol_norm_le j ξ
      simp only [lps_fourierWordSymbol, List.map_cons, List.prod_cons,
        norm_mul, List.length_cons, pow_succ]
      calc
        ‖CKN.Leray.regR12CoordSymbol j ξ‖ *
            ‖(α.map fun k => CKN.Leray.regR12CoordSymbol k ξ).prod‖
          ≤ (2 * π * ‖ξ‖) *
              ((2 * π) ^ α.length * ‖ξ‖ ^ α.length) :=
            mul_le_mul hj ih (by positivity) (by positivity)
        _ = (2 * π) ^ (α.length + 1) *
            ‖ξ‖ ^ (α.length + 1) := by ring

/-- A Bessel weight of order `2k` absorbs a polynomial of degree at
most `2k` (`prop:lps-smoothing`). -/
theorem lps_power_le_bessel_even
    (r k : ℕ) (hr : r ≤ 2 * k) (x : ℝ) (hx : 0 ≤ x) :
    x ^ r ≤ (1 + x ^ 2) ^ k := by
  by_cases hsmall : x ≤ 1
  · exact (pow_le_one₀ hx hsmall).trans
      (one_le_pow₀ (by nlinarith only [sq_nonneg x]))
  · have hlarge : 1 ≤ x := le_of_not_ge hsmall
    calc
      x ^ r ≤ x ^ (2 * k) := pow_le_pow_right₀ hlarge hr
      _ = (x ^ 2) ^ k := by rw [pow_mul]
      _ ≤ (1 + x ^ 2) ^ k := by gcongr; linarith only

/-- A Fourier word of length at most `2k` is bounded by the
order-`2k` Bessel weight (`prop:lps-smoothing`). -/
theorem lps_fourierWordSymbol_bessel_bound
    (k : ℕ) (α : List (Fin 3)) (hα : α.length ≤ 2 * k)
    (ξ : L2Vec3) :
    ‖lps_fourierWordSymbol α ξ‖ ≤
      (2 * π) ^ α.length * (1 + ‖ξ‖ ^ 2) ^ k := by
  calc
    ‖lps_fourierWordSymbol α ξ‖ ≤
        (2 * π) ^ α.length * ‖ξ‖ ^ α.length :=
      lps_fourierWordSymbol_norm_le α ξ
    _ ≤ (2 * π) ^ α.length * (1 + ‖ξ‖ ^ 2) ^ k :=
      mul_le_mul_of_nonneg_left
        (lps_power_le_bessel_even α.length k hα ‖ξ‖ (norm_nonneg ξ))
        (by positivity)

end ESS
