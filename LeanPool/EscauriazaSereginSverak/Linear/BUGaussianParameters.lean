/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Parameters for Gaussian average decay

The Carleman absorption choice and the rescaled collar geometry in
lem:bu-gaussian.
-/

public section


noncomputable section

namespace ESS

/-- A small time threshold satisfying the absorption conditions in
lem:bu-gaussian#parameter-choice. -/
theorem buGaussian_parameter_choice (c₁ C_G β H : ℝ)
    (hc₁ : 0 < c₁) (hCG : 0 < C_G) (hβ : 0 < β) (hH : 0 < H) :
    ∃ γ : ℝ, 0 < γ ∧ γ < 1 / 12 ∧ γ ≤ 1 / 24 ∧
      γ ≤ β / (3 * H) ∧ 3 * C_G * c₁ ^ 2 * γ ≤ 1 / 2 := by
  let γ := min (1 / 24 : ℝ)
    (min (β / (3 * H)) (1 / (6 * C_G * c₁ ^ 2)))
  have hγpos : 0 < γ := by
    dsimp [γ]
    positivity
  have hγ24 : γ ≤ 1 / 24 := by
    dsimp [γ]
    exact min_le_left _ _
  have hγβ : γ ≤ β / (3 * H) := by
    dsimp [γ]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hγabsorb : γ ≤ 1 / (6 * C_G * c₁ ^ 2) := by
    dsimp [γ]
    exact (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨γ, hγpos, ?_, hγ24, hγβ, ?_⟩
  · exact lt_of_le_of_lt hγ24 (by norm_num)
  · calc
      3 * C_G * c₁ ^ 2 * γ ≤
          3 * C_G * c₁ ^ 2 * (1 / (6 * C_G * c₁ ^ 2)) :=
        mul_le_mul_of_nonneg_left hγabsorb (by positivity)
      _ = 1 / 2 := by field_simp; norm_num

/-- The source parameter choice makes the rescaled shell radius large, the
Carleman exponent greater than one, and the covering radius at most 1/16.
The product rho times r is independent of the point and time. -/
theorem buGaussian_parameter_geometry
    (β H γ x₃ t : ℝ) (hβ : 0 < β) (hH : 0 < H)
    (hHβ : 16 * β < H)
    (hγβ : γ ≤ β / (3 * H)) (hx₃ : 2 < x₃)
    (ht : 0 < t) (htγ : t < γ) :
    let ρ := (x₃ - 1) / Real.sqrt (3 * t)
    let a := β * ρ ^ 2 / H
    let r := 1 / (16 * Real.sqrt a)
    4 < ρ ∧ 1 < a ∧ 0 < r ∧ r < 1 / 16 ∧
      ρ * r = Real.sqrt (H / β) / 16 := by
  let ρ := (x₃ - 1) / Real.sqrt (3 * t)
  let a := β * ρ ^ 2 / H
  let r := 1 / (16 * Real.sqrt a)
  have h3tβ : 3 * t < β / H := by
    have hγscaled : 3 * γ ≤ β / H := by
      calc
        3 * γ ≤ 3 * (β / (3 * H)) :=
          mul_le_mul_of_nonneg_left hγβ (by norm_num)
        _ = β / H := by field_simp
    nlinarith only [htγ, hγscaled]
  have h3tH : 3 * t * H < β := by
    calc
      3 * t * H < (β / H) * H :=
        mul_lt_mul_of_pos_right h3tβ hH
      _ = β := by field_simp
  have hβH : β / H < 1 / 16 := by
    apply (div_lt_iff₀ hH).2
    nlinarith only [hHβ]
  have hsqrtDen : Real.sqrt (3 * t) < 1 / 4 := by
    calc
      Real.sqrt (3 * t) < Real.sqrt (1 / 16) :=
        Real.sqrt_lt_sqrt (by positivity) (lt_trans h3tβ hβH)
      _ = 1 / 4 := by
        rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1)]
        have hsqrt16 : Real.sqrt (16 : ℝ) = 4 :=
          (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).2 (by norm_num)
        rw [hsqrt16]
        norm_num
  have hxNumer : 1 < x₃ - 1 := by linarith only [hx₃]
  have hρpos : 0 < ρ := by
    dsimp [ρ]
    exact div_pos (by linarith only [hx₃]) (Real.sqrt_pos.mpr (by positivity))
  have hρlarge : 4 < ρ := by
    dsimp [ρ]
    apply (lt_div_iff₀ (Real.sqrt_pos.mpr (by positivity))).2
    have hden4 : 4 * Real.sqrt (3 * t) < 1 := by
      nlinarith only [hsqrtDen]
    nlinarith only [hxNumer, hden4]
  have hInv : H / β < 1 / (3 * t) := by
    apply (div_lt_iff₀ hβ).2
    have hcancel : (1 / (3 * t)) * β = β / (3 * t) := by ring
    rw [hcancel]
    apply (lt_div_iff₀ (by positivity : 0 < 3 * t)).2
    nlinarith only [h3tH]
  have hdenPos : 0 < 3 * t := by positivity
  have hpointSq : 1 < (x₃ - 1) ^ 2 := by nlinarith only [hxNumer]
  have hquot : 1 / (3 * t) <
      (x₃ - 1) ^ 2 / (3 * t) := by
    exact (div_lt_div_iff_of_pos_right hdenPos).2 hpointSq
  have hρsq : H / β < ρ ^ 2 := by
    dsimp [ρ]
    rw [div_pow, Real.sq_sqrt (by positivity)]
    exact lt_trans hInv hquot
  have hβρsq : H < β * ρ ^ 2 := by
    have hmul := mul_lt_mul_of_pos_left hρsq hβ
    have hcancel : β * (H / β) = H := by field_simp
    rw [hcancel] at hmul
    exact hmul
  have ha : 1 < a := by
    dsimp [a]
    exact (lt_div_iff₀ hH).2 (by nlinarith only [hβρsq])
  have hroot : 1 < Real.sqrt a := by
    simpa using Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1) ha
  have hrpos : 0 < r := by
    dsimp [r]
    exact one_div_pos.mpr (by positivity)
  have hrsmall : r < 1 / 16 := by
    dsimp [r]
    apply (div_lt_div_iff₀ (by positivity : 0 < 16 * Real.sqrt a)
      (by norm_num : (0 : ℝ) < 16)).2
    nlinarith only [hroot]
  have haeq : a = (β / H) * ρ ^ 2 := by
    dsimp [a]
    ring
  have hsqrtA : Real.sqrt a = ρ * Real.sqrt (β / H) := by
    rw [haeq, Real.sqrt_mul (by positivity : 0 ≤ β / H),
      Real.sqrt_sq_eq_abs, abs_of_pos hρpos]
    ring
  have hsqrts : Real.sqrt (β / H) * Real.sqrt (H / β) = 1 := by
    have hprod : (β / H) * (H / β) = 1 := by field_simp
    have hsqrtprod := congrArg Real.sqrt hprod
    rw [Real.sqrt_mul (by positivity : 0 ≤ β / H)] at hsqrtprod
    simpa using hsqrtprod
  have hrhoR : ρ * r = Real.sqrt (H / β) / 16 := by
    dsimp [r]
    rw [hsqrtA]
    calc
      ρ * (1 / (16 * (ρ * Real.sqrt (β / H)))) =
          1 / (16 * Real.sqrt (β / H)) := by
            field_simp [ne_of_gt hρpos, ne_of_gt (Real.sqrt_pos.mpr (div_pos hβ hH))]
      _ = Real.sqrt (H / β) / 16 := by
        have hsqrtβ : 0 < Real.sqrt (β / H) :=
          Real.sqrt_pos.mpr (div_pos hβ hH)
        field_simp [ne_of_gt hsqrtβ]
        rw [hsqrts]
  exact ⟨hρlarge, ha, hrpos, hrsmall, hrhoR⟩

/-- The rescaled collar radius gives the source height-decay exponent
(lem:bu-gaussian#change-back). -/
theorem buGaussian_scaled_height_lower {x₃ t : ℝ}
    (hx₃ : 2 < x₃) (ht : 0 < t) :
    ((x₃ - 1) / Real.sqrt (3 * t)) ^ 2 ≥ x₃ ^ 2 / (12 * t) := by
  have hxhalf : x₃ / 2 ≤ x₃ - 1 := by linarith only [hx₃]
  have hxhalfNonneg : 0 ≤ x₃ / 2 := by linarith only [hx₃]
  have hxminusNonneg : 0 ≤ x₃ - 1 := by linarith only [hx₃]
  have hsq :
      (x₃ / 2) * (x₃ / 2) ≤ (x₃ - 1) * (x₃ - 1) := by
    calc
      (x₃ / 2) * (x₃ / 2) ≤ (x₃ - 1) * (x₃ / 2) :=
        mul_le_mul_of_nonneg_right hxhalf hxhalfNonneg
      _ = (x₃ / 2) * (x₃ - 1) := by ring
      _ = (x₃ - 1) * (x₃ / 2) := by ring
      _ ≤ (x₃ - 1) * (x₃ - 1) :=
        mul_le_mul_of_nonneg_left hxhalf hxminusNonneg
  have hnum : x₃ ^ 2 / 4 ≤ (x₃ - 1) ^ 2 := by
    nlinarith only [hsq]
  have hden : 0 < 3 * t := by positivity
  calc
    x₃ ^ 2 / (12 * t) = (x₃ ^ 2 / 4) / (3 * t) := by field_simp; norm_num
    _ ≤ (x₃ - 1) ^ 2 / (3 * t) :=
      div_le_div_of_nonneg_right hnum hden.le
    _ = ((x₃ - 1) / Real.sqrt (3 * t)) ^ 2 := by
      rw [div_pow, Real.sq_sqrt (le_of_lt hden)]

end ESS
