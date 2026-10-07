/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingFourierWords

/-!
# Damped high-order Fourier multipliers

A higher Bessel lift can be fed into the order-four inverse Fourier
field after the excess Bessel weight is moved into the multiplier.
-/

public section

open MeasureTheory FourierTransform Complex
open scoped ENNReal FourierTransform Real


noncomputable section

namespace ESS

open CKN.Foundation.Parabolic

/-- A coordinate word multiplier damped by an additional Bessel
weight of order `2n`. -/
@[expose] def lpsDampedFourierWordSymbol (n : ℕ) (α : List (Fin 3))
    (ξ : L2Vec3) : ℂ :=
  lpsFourierWordSymbol α ξ *
    (((1 + ‖ξ‖ ^ 2) ^ (-(n : ℝ)) : ℝ) : ℂ)

/-- Damping by an even Bessel power leaves at most quadratic growth
for every polynomial power below the available order
(`prop:lps-smoothing`). -/
theorem lps_damped_power_bound
    (n r : ℕ) (hr : r ≤ 2 * (n + 1))
    (x : ℝ) (hx : 0 ≤ x) :
    x ^ r * (1 + x ^ 2) ^ (-(n : ℝ)) ≤ 1 + x ^ 2 := by
  let b : ℝ := 1 + x ^ 2
  have hb : 0 < b := by dsimp [b]; positivity
  have hpow := lps_power_le_bessel_even r (n + 1) hr x hx
  have hfactor : 0 ≤ b ^ (-(n : ℝ)) := Real.rpow_nonneg hb.le _
  have hweighted := mul_le_mul_of_nonneg_right hpow hfactor
  have hident : b ^ (n + 1) * b ^ (-(n : ℝ)) = b := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hb]
    have he : ((n + 1 : ℕ) : ℝ) + -(n : ℝ) = 1 := by
      push_cast
      ring
    rw [he, Real.rpow_one]
  dsimp [b] at hweighted ⊢
  rw [hident] at hweighted
  exact hweighted

/-- The damped word multiplier has at most quadratic growth when
its word length fits under the higher Bessel order
(`prop:lps-smoothing`). -/
theorem lps_dampedFourierWordSymbol_norm_le
    (n : ℕ) (α : List (Fin 3))
    (hα : α.length ≤ 2 * (n + 1)) (ξ : L2Vec3) :
    ‖lpsDampedFourierWordSymbol n α ξ‖ ≤
      (2 * π) ^ α.length * (1 + ‖ξ‖ ^ 2) := by
  have hb : 0 ≤ (1 + ‖ξ‖ ^ 2) ^ (-(n : ℝ)) := by positivity
  unfold lpsDampedFourierWordSymbol
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hb]
  calc
    ‖lpsFourierWordSymbol α ξ‖ *
        (1 + ‖ξ‖ ^ 2) ^ (-(n : ℝ)) ≤
      ((2 * π) ^ α.length * ‖ξ‖ ^ α.length) *
        (1 + ‖ξ‖ ^ 2) ^ (-(n : ℝ)) :=
      mul_le_mul_of_nonneg_right
        (lps_fourierWordSymbol_norm_le α ξ) hb
    _ = (2 * π) ^ α.length *
        (‖ξ‖ ^ α.length * (1 + ‖ξ‖ ^ 2) ^ (-(n : ℝ))) := by ring
    _ ≤ (2 * π) ^ α.length * (1 + ‖ξ‖ ^ 2) :=
      mul_le_mul_of_nonneg_left
        (lps_damped_power_bound n α.length hα ‖ξ‖ (norm_nonneg ξ))
        (by positivity)

/-- One additional coordinate derivative still has quadratic growth
when the higher Bessel order has one spare degree
(`prop:lps-smoothing`). -/
theorem lps_dampedFourierWordSymbol_first_moment_le
    (n : ℕ) (α : List (Fin 3))
    (hα : α.length + 1 ≤ 2 * (n + 1)) (ξ : L2Vec3) :
    ‖ξ‖ * ‖lpsDampedFourierWordSymbol n α ξ‖ ≤
      (2 * π) ^ α.length * (1 + ‖ξ‖ ^ 2) := by
  have hb : 0 ≤ (1 + ‖ξ‖ ^ 2) ^ (-(n : ℝ)) := by positivity
  unfold lpsDampedFourierWordSymbol
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hb]
  calc
    ‖ξ‖ * (‖lpsFourierWordSymbol α ξ‖ *
        (1 + ‖ξ‖ ^ 2) ^ (-(n : ℝ))) ≤
      ‖ξ‖ * (((2 * π) ^ α.length * ‖ξ‖ ^ α.length) *
        (1 + ‖ξ‖ ^ 2) ^ (-(n : ℝ))) := by
      gcongr
      exact lps_fourierWordSymbol_norm_le α ξ
    _ = (2 * π) ^ α.length *
        (‖ξ‖ ^ (α.length + 1) *
          (1 + ‖ξ‖ ^ 2) ^ (-(n : ℝ))) := by
      rw [pow_succ]
      ring
    _ ≤ (2 * π) ^ α.length * (1 + ‖ξ‖ ^ 2) :=
      mul_le_mul_of_nonneg_left
        (lps_damped_power_bound n (α.length + 1) hα
          ‖ξ‖ (norm_nonneg ξ)) (by positivity)

/-- After multiplication by the order-four inverse Bessel weight,
the damped coordinate multiplier is bounded at every frequency
(`prop:lps-smoothing`). -/
theorem lps_dampedFourierWordSymbol_weighted_norm_le
    (n : ℕ) (α : List (Fin 3))
    (hα : α.length ≤ 2 * (n + 1)) (ξ : L2Vec3) :
    ‖lpsDampedFourierWordSymbol n α ξ *
      (((1 + ‖ξ‖ ^ 2) ^ (-2 : ℝ) : ℝ) : ℂ)‖ ≤
      (2 * π) ^ α.length := by
  let b : ℝ := 1 + ‖ξ‖ ^ 2
  have hb : 1 ≤ b := by dsimp [b]; nlinarith only [sq_nonneg ‖ξ‖]
  have hbpos : 0 < b := lt_of_lt_of_le zero_lt_one hb
  have hw : 0 ≤ b ^ (-2 : ℝ) := Real.rpow_nonneg hbpos.le _
  have hbw : b * b ^ (-2 : ℝ) ≤ 1 := by
    have hid : b * b ^ (-2 : ℝ) = b ^ (-1 : ℝ) := by
      conv_lhs => lhs; rw [← Real.rpow_one b]
      rw [← Real.rpow_add hbpos]
      norm_num
    rw [hid]
    exact Real.rpow_le_one_of_one_le_of_nonpos hb (by norm_num)
  have hM := lps_dampedFourierWordSymbol_norm_le n α hα ξ
  change ‖lpsDampedFourierWordSymbol n α ξ‖ ≤
    (2 * π) ^ α.length * b at hM
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw]
  calc
    ‖lpsDampedFourierWordSymbol n α ξ‖ * b ^ (-2 : ℝ) ≤
      ((2 * π) ^ α.length * b) * b ^ (-2 : ℝ) :=
      mul_le_mul_of_nonneg_right hM hw
    _ = (2 * π) ^ α.length * (b * b ^ (-2 : ℝ)) := by ring
    _ ≤ (2 * π) ^ α.length * 1 :=
      mul_le_mul_of_nonneg_left hbw (by positivity)
    _ = (2 * π) ^ α.length := by ring

end ESS
