/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Core.Iteration.Arithmetic
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Topology
public import LeanPool.CIVAxisymmetric.Statements.UnitCylinder

/-!
# One-step contraction of the scale-invariant quantity

The one-step contraction of the scale-invariant quantity in the iteration of the CKN
manuscript's iteration proposition (with its convention for κ, η, ε_* and the force
coefficient C₂₉), stated for abstract
real numbers.
-/

public section

open MeasureTheory Set
open CKN.Foundation.Parabolic CKN


noncomputable section

namespace CIV



theorem theta_contraction_of_beta_small {C₂₇ C₂₈ T Tnext b L : ℝ}
    (hC₂₇ : 0 < C₂₇) (hC₂₈ : 0 < C₂₈) (hT : 0 ≤ T) (hL : 0 ≤ L) (hb : 0 ≤ b)
    (hbsmall : b ≤ iterationEpsilonStar C₂₇)
    (hdec : Tnext ≤ C₂₇ * iterationKappa C₂₇ ^ (2 / 3 : ℝ) * T +
        C₂₇ * iterationKappa C₂₇ ^ (-5 : ℝ) * (b ^ (1 / 2 : ℝ) + b) * T +
        C₂₈ * iterationKappa C₂₇ ^ (-1 / 2 : ℝ) * T ^ (1 / 2 : ℝ) * L ^ (1 / 2 : ℝ) +
        C₂₈ * iterationKappa C₂₇ ^ (-3 : ℝ) * L) :
    Tnext ≤ (3 / 8 : ℝ) * T + iterationC₂₉ C₂₇ C₂₈ * L := by
  set κ := iterationKappa C₂₇ with hκdef
  have hκ : 0 < κ := iterationKappa_pos hC₂₇
  have hκle1 : κ ≤ 1 := by
    have h := iterationKappa_le_half C₂₇
    linarith only [h]
  have hεpos : 0 < iterationEpsilon := by
    unfold iterationEpsilon
    norm_num
  have hεpos' : 0 ≤ iterationEpsilon := hεpos.le
  -- (1) first term bound: C₂₇ * κ^(2/3) * T ≤ (1/8) * T
  have h_first : C₂₇ * κ ^ (2 / 3 : ℝ) * T ≤ (1 / 8 : ℝ) * T := by
    have h_rpow : κ ^ (2 / 3 : ℝ) ≤ κ ^ (2 / 3 - iterationEpsilon) :=
      Real.rpow_le_rpow_of_exponent_ge hκ hκle1 (by
        linarith only [hεpos'])
    have h_prop := iterationKappa_prop₁ hC₂₇
    calc
      C₂₇ * κ ^ (2 / 3 : ℝ) * T ≤ C₂₇ * κ ^ (2 / 3 - iterationEpsilon) * T :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h_rpow hC₂₇.le) hT
      _ ≤ (1 / 8 : ℝ) * T := mul_le_mul_of_nonneg_right h_prop hT
  -- (2) second term bound: C₂₇ * κ^(-5) * (b^(1/2) + b) * T ≤ (1/8) * T
  have h_second : C₂₇ * κ ^ (-5 : ℝ) * (b ^ (1 / 2 : ℝ) + b) * T ≤ (1 / 8 : ℝ) * T := by
    have hb_sqrt : b ^ (1 / 2 : ℝ) ≤ (iterationEpsilonStar C₂₇) ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow hb hbsmall (by norm_num)
    have hb_sum : b ^ (1 / 2 : ℝ) + b ≤
        (iterationEpsilonStar C₂₇) ^ (1 / 2 : ℝ) + iterationEpsilonStar C₂₇ :=
      add_le_add hb_sqrt hbsmall
    have h_rpow : κ ^ (-5 : ℝ) ≤ κ ^ (-5 - iterationEpsilon) :=
      Real.rpow_le_rpow_of_exponent_ge hκ hκle1 (by linarith only [hεpos'])
    have h_prop := iterationKappa_prop₃ hC₂₇
    set s := (iterationEpsilonStar C₂₇) ^ (1 / 2 : ℝ) + iterationEpsilonStar C₂₇ with hsdef
    have hs_nonneg : 0 ≤ s := by
      have hεs_nonneg : 0 ≤ (iterationEpsilonStar C₂₇) ^ (1 / 2 : ℝ) :=
        Real.rpow_nonneg (iterationEpsilonStar_pos hC₂₇).le _
      have hεs_le : 0 ≤ iterationEpsilonStar C₂₇ :=
        (iterationEpsilonStar_pos hC₂₇).le
      positivity
    have hpos_factor : 0 ≤ C₂₇ * κ ^ (-5 : ℝ) * T := by positivity
    -- C₂₇ * κ^(-5) * (b^(1/2)+b) * T ≤ C₂₇ * κ^(-5) * s * T
    have hstep1 : C₂₇ * κ ^ (-5 : ℝ) * (b ^ (1 / 2 : ℝ) + b) * T ≤
        C₂₇ * κ ^ (-5 : ℝ) * s * T := by
      have h := mul_le_mul_of_nonneg_right hb_sum hpos_factor
      simpa [mul_comm, mul_left_comm, mul_assoc] using h
    -- C₂₇ * κ^(-5) * s * T ≤ C₂₇ * κ^(-5-ε) * s * T
    have hstep2 : C₂₇ * κ ^ (-5 : ℝ) * s * T ≤
        C₂₇ * κ ^ (-5 - iterationEpsilon) * s * T := by
      have hpos_sT : 0 ≤ C₂₇ * s * T := by positivity
      have h := mul_le_mul_of_nonneg_left h_rpow hpos_sT
      simpa [mul_comm, mul_left_comm, mul_assoc] using h
    -- C₂₇ * κ^(-5-ε) * s * T = (2 * C₂₇ * κ^(-5-ε) * s) * T / 2
    have hstep3 : C₂₇ * κ ^ (-5 - iterationEpsilon) * s * T =
        (2 * C₂₇ * κ ^ (-5 - iterationEpsilon) * s) * T / 2 := by ring
    calc
      C₂₇ * κ ^ (-5 : ℝ) * (b ^ (1 / 2 : ℝ) + b) * T ≤
          C₂₇ * κ ^ (-5 : ℝ) * s * T := hstep1
      _ ≤ C₂₇ * κ ^ (-5 - iterationEpsilon) * s * T := hstep2
      _ = (2 * C₂₇ * κ ^ (-5 - iterationEpsilon) * s) * T / 2 := by ring
      _ ≤ ((1 / 8 : ℝ) / 2) * T := by
        have htemp := h_prop
        have hposT : 0 ≤ T := hT
        nlinarith only [htemp, hposT]
      _ ≤ (1 / 8 : ℝ) * T := by nlinarith only [hT]
  -- (3) third term bound: C₂₈ * κ^(-1/2) * T^(1/2) * L^(1/2) ≤ (1/8) * T + 2 * C₂₈^2 *
  -- κ^(-1-2ε) * L
  have h_third : C₂₈ * κ ^ (-1 / 2 : ℝ) * T ^ (1 / 2 : ℝ) * L ^ (1 / 2 : ℝ) ≤
      (1 / 8 : ℝ) * T + 2 * C₂₈ ^ 2 * κ ^ (-1 - 2 * iterationEpsilon) * L := by
    set x := T ^ (1 / 2 : ℝ) with hxdef
    set y := C₂₈ * κ ^ (-1 / 2 : ℝ) * L ^ (1 / 2 : ℝ) with hydef
    have hx_nonneg : 0 ≤ x := Real.rpow_nonneg hT _
    have hy_nonneg : 0 ≤ y := by
      have h1 : 0 ≤ C₂₈ := hC₂₈.le
      have h2 : 0 ≤ κ ^ (-1 / 2 : ℝ) := Real.rpow_nonneg hκ.le _
      have h3 : 0 ≤ L ^ (1 / 2 : ℝ) := Real.rpow_nonneg hL _
      positivity
    have h_young : 2 * x * y ≤ x ^ 2 + y ^ 2 := two_mul_le_add_sq _ _
    have h_goal : x * y ≤ (1 / 8 : ℝ) * x ^ 2 + 2 * y ^ 2 := by
      have h_sq : (x - 4 * y) ^ 2 ≥ 0 := sq_nonneg _
      nlinarith only [h_sq]
    have hx_sq : x ^ 2 = T :=
      CKN.Foundation.Euclidean.rpow_half_sq_of_nonneg hT
    have hy_sq_eq : y ^ 2 = C₂₈ ^ 2 * κ ^ (-1 : ℝ) * L := by
      dsimp [y]
      calc
        (C₂₈ * κ ^ (-1 / 2 : ℝ) * L ^ (1 / 2 : ℝ)) ^ 2 =
            C₂₈ ^ 2 * (κ ^ (-1 / 2 : ℝ)) ^ 2 * (L ^ (1 / 2 : ℝ)) ^ 2 := by ring
        _ = C₂₈ ^ 2 * κ ^ (-1 : ℝ) * (L ^ (1 / 2 : ℝ)) ^ 2 := by
          have h : (κ ^ (-1 / 2 : ℝ)) ^ 2 = κ ^ (-1 : ℝ) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hκ.le]
            norm_num
          rw [h]
        _ = C₂₈ ^ 2 * κ ^ (-1 : ℝ) * L :=
          by rw [CKN.Foundation.Euclidean.rpow_half_sq_of_nonneg hL]
    have h_rpow' : κ ^ (-1 : ℝ) ≤ κ ^ (-1 - 2 * iterationEpsilon) :=
      Real.rpow_le_rpow_of_exponent_ge hκ hκle1 (by linarith only [hεpos'])
    calc
      C₂₈ * κ ^ (-1 / 2 : ℝ) * T ^ (1 / 2 : ℝ) * L ^ (1 / 2 : ℝ) =
          x * y := by dsimp [x, y]; ring
      _ ≤ (1 / 8 : ℝ) * x ^ 2 + 2 * y ^ 2 := h_goal
      _ = (1 / 8 : ℝ) * T + 2 * y ^ 2 := by rw [hx_sq]
      _ = (1 / 8 : ℝ) * T + 2 * (C₂₈ ^ 2 * κ ^ (-1 : ℝ) * L) := by rw [hy_sq_eq]
      _ = (1 / 8 : ℝ) * T + 2 * C₂₈ ^ 2 * κ ^ (-1 : ℝ) * L := by ring
      _ ≤ (1 / 8 : ℝ) * T + 2 * C₂₈ ^ 2 * κ ^ (-1 - 2 * iterationEpsilon) * L := by
        have hpos : 0 ≤ 2 * C₂₈ ^ 2 * L := by positivity
        nlinarith only [h_rpow', hC₂₈.le, hpos]
  -- (4) fourth term bound: C₂₈ * κ^(-3) * L ≤ C₂₈ * κ^(-3-ε) * L
  have h_fourth : C₂₈ * κ ^ (-3 : ℝ) * L ≤ C₂₈ * κ ^ (-3 - iterationEpsilon) * L := by
    have h_rpow : κ ^ (-3 : ℝ) ≤ κ ^ (-3 - iterationEpsilon) :=
      Real.rpow_le_rpow_of_exponent_ge hκ hκle1 (by linarith only [hεpos'])
    have hpos : 0 ≤ C₂₈ * L := by positivity
    have h := mul_le_mul_of_nonneg_left h_rpow hpos
    simpa [mul_comm, mul_left_comm, mul_assoc] using h
  -- sum the four bounds
  calc
    Tnext ≤ C₂₇ * κ ^ (2 / 3 : ℝ) * T +
        C₂₇ * κ ^ (-5 : ℝ) * (b ^ (1 / 2 : ℝ) + b) * T +
        C₂₈ * κ ^ (-1 / 2 : ℝ) * T ^ (1 / 2 : ℝ) * L ^ (1 / 2 : ℝ) +
        C₂₈ * κ ^ (-3 : ℝ) * L := hdec
    _ ≤ (1 / 8 : ℝ) * T + (1 / 8 : ℝ) * T +
        ((1 / 8 : ℝ) * T + 2 * C₂₈ ^ 2 * κ ^ (-1 - 2 * iterationEpsilon) * L) +
        C₂₈ * κ ^ (-3 : ℝ) * L := by
      have h12 := add_le_add h_first h_second
      have h123 := add_le_add h12 h_third
      have h1234 := add_le_add h123 (le_refl (C₂₈ * κ ^ (-3 : ℝ) * L))
      simpa [add_comm, add_left_comm, add_assoc] using h1234
    _ = (3 / 8 : ℝ) * T + (2 * C₂₈ ^ 2 * κ ^ (-1 - 2 * iterationEpsilon) * L +
        C₂₈ * κ ^ (-3 : ℝ) * L) := by ring
    _ ≤ (3 / 8 : ℝ) * T + (2 * C₂₈ ^ 2 * κ ^ (-1 - 2 * iterationEpsilon) * L +
        C₂₈ * κ ^ (-3 - iterationEpsilon) * L) := by
      have h_inner : 2 * C₂₈ ^ 2 * κ ^ (-1 - 2 * iterationEpsilon) * L +
          C₂₈ * κ ^ (-3 : ℝ) * L ≤
          2 * C₂₈ ^ 2 * κ ^ (-1 - 2 * iterationEpsilon) * L +
          C₂₈ * κ ^ (-3 - iterationEpsilon) * L := by
        simpa [add_comm] using
          add_le_add_right h_fourth (2 * C₂₈ ^ 2 * κ ^ (-1 - 2 * iterationEpsilon) * L)
      exact add_le_add (le_refl _) h_inner
    _ = (3 / 8 : ℝ) * T + iterationC₂₉ C₂₇ C₂₈ * L := by
      unfold iterationC₂₉
      ring

end CIV
