/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Statements.SpatialPartial
public import LeanPool.CaffarelliKohnNirenberg.Statements.TimePartial
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpatialSecondPartial
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Algebra

Supporting results for the Constantin–Ignatova–Vicol axisymmetric regularity theorem.
-/


public section

open Set
open CKN.Foundation.Parabolic CKN

noncomputable section
namespace CIV

/-- If `|R * S| ≤ D` with `ε > 0` and `ε ≤ R`, then `(S / R)^2 ≤ D^2 / ε^4`. -/
theorem sq_div_le_of_abs_mul_le {S R D ε : ℝ} (hε : 0 < ε) (hR : ε ≤ R)
    (h : |R * S| ≤ D) : (S / R) ^ 2 ≤ D ^ 2 / ε ^ 4 := by
  have hRpos : 0 < R := by linarith only [hε, hR]
  have h_abs_range : -D ≤ R * S ∧ R * S ≤ D := abs_le.mp h
  have h_sq : (R * S) ^ 2 ≤ D ^ 2 := by
    rcases h_abs_range with ⟨h_low, h_high⟩
    nlinarith only [h_low, h_high]
  have h_sq' : R ^ 2 * S ^ 2 ≤ D ^ 2 := by nlinarith only [h_sq]
  have h_eps_four_le_R_four : ε ^ 4 ≤ R ^ 4 := by
    have h_eps_sq_le_R_sq : ε ^ 2 ≤ R ^ 2 := by nlinarith only [hε, hR]
    nlinarith only [h_eps_sq_le_R_sq]
  have h_main : S ^ 2 * ε ^ 4 ≤ D ^ 2 * R ^ 2 := by
    have h_nonneg_S_sq : 0 ≤ S ^ 2 := by positivity
    have h1 : S ^ 2 * ε ^ 4 ≤ S ^ 2 * R ^ 4 := by nlinarith only [h_eps_four_le_R_four,
      h_nonneg_S_sq]
    have h2 : S ^ 2 * R ^ 4 ≤ D ^ 2 * R ^ 2 := by nlinarith only [h_sq']
    nlinarith only [h1, h2]
  field_simp [hRpos.ne', (by positivity : 0 < ε ^ 4).ne']
  -- goal: S ^ 2 * ε ^ 4 ≤ R ^ 2 * D ^ 2
  -- h_main: S ^ 2 * ε ^ 4 ≤ D ^ 2 * R ^ 2
  nlinarith only [h_main]

/-- If `|S| ≤ C * R` with `R > 0`, then `(S / R)^2 ≤ C^2`. -/
theorem sq_div_le_of_abs_le_mul {S R C : ℝ} (hR : 0 < R) (h : |S| ≤ C * R) : (S / R) ^ 2 ≤ C ^ 2
    := by
  have h_abs_range : -(C * R) ≤ S ∧ S ≤ C * R := abs_le.mp h
  have h_sq : S ^ 2 ≤ C ^ 2 * R ^ 2 := by
    rcases h_abs_range with ⟨h_low, h_high⟩
    nlinarith only [h_low, h_high]
  field_simp [hR.ne']
  nlinarith only [h_sq]

/-- For `τ ≤ -1` and `e ≤ 0`, we have `(-τ)^e ≤ 1`. -/
theorem neg_rpow_le_one_of_le_neg_one {τ e : ℝ} (hτ : τ ≤ -1) (he : e ≤ 0) : (-τ) ^ e ≤ 1 := by
  have h_base : 1 ≤ -τ := by linarith only [hτ]
  calc
    (-τ) ^ e ≤ (-τ) ^ (0 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le h_base he
    _ = 1 := by rw [Real.rpow_zero (-τ)]

/-- Finite axis bound: for `C ≥ 0`, `0 ≤ δ ≤ 1`, `τ ≤ -1`, `0 < h < 1/2`,
`C * (δ^2 * (-τ)^(-3/2 + h) + (-τ)^(-3/2 - h)) ≤ 2 * C`. -/
theorem finite_axis_bound_le {δ τ h C : ℝ} (hC : 0 ≤ C) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hτ : τ ≤ -1) (hh : 0 < h ∧ h < 1 / 2) :
    C * (δ ^ 2 * (-τ) ^ (-(3 / 2 : ℝ) + h) + (-τ) ^ (-(3 / 2 : ℝ) - h)) ≤ 2 * C := by
  rcases hh with ⟨hh_left, hh_right⟩
  have h_neg_tau_ge_one : 1 ≤ -τ := by linarith only [hτ]
  have ha_neg : -(3 / 2 : ℝ) + h ≤ 0 := by linarith only [hh_right]
  have hb_neg : -(3 / 2 : ℝ) - h ≤ 0 := by linarith only [hh_left, hh_right]
  have ha_rpow_le_one : (-τ) ^ (-(3 / 2 : ℝ) + h) ≤ 1 := by
    calc
      (-τ) ^ (-(3 / 2 : ℝ) + h) ≤ (-τ) ^ (0 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le h_neg_tau_ge_one ha_neg
      _ = 1 := by rw [Real.rpow_zero (-τ)]
  have hb_rpow_le_one : (-τ) ^ (-(3 / 2 : ℝ) - h) ≤ 1 := by
    calc
      (-τ) ^ (-(3 / 2 : ℝ) - h) ≤ (-τ) ^ (0 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le h_neg_tau_ge_one hb_neg
      _ = 1 := by rw [Real.rpow_zero (-τ)]
  have hδ_sq_le_one : δ ^ 2 ≤ 1 := by nlinarith only [hδ, hδ1]
  have h_sum : δ ^ 2 * (-τ) ^ (-(3 / 2 : ℝ) + h) + (-τ) ^ (-(3 / 2 : ℝ) - h) ≤ 2 := by
    nlinarith only [hδ_sq_le_one, ha_rpow_le_one, hb_rpow_le_one]
  nlinarith only [hC, h_sum]

/-- `(-t) * (-t)^(-1/2) = (-t)^(1/2)` for `t < 0`. -/
theorem neg_t_mul_rpow_neg_half {t : ℝ} (ht : t < 0) : (-t) * (-t) ^ (-(1 / 2 : ℝ)) = (-t) ^ (1
    / 2 : ℝ) := by
  have hpos : 0 < -t := by linarith only [ht]
  calc
    (-t) * (-t) ^ (-(1 / 2 : ℝ)) = (-t) ^ (1 : ℝ) * (-t) ^ (-(1 / 2 : ℝ)) := by rw [Real.rpow_one]
    _ = (-t) ^ ((1 : ℝ) + (-(1 / 2 : ℝ))) := by rw [Real.rpow_add hpos (1 : ℝ) (-(1 / 2 : ℝ))]
    _ = (-t) ^ (1 / 2 : ℝ) := by ring_nf

/-- `(-t) * (-t)^(-1 + h) = (-t)^h` for `t < 0`. -/
theorem neg_t_mul_rpow_neg_one_add {t h : ℝ} (ht : t < 0) : (-t) * (-t) ^ (-(1 : ℝ) + h) = (-t)
    ^ h := by
  have hpos : 0 < -t := by linarith only [ht]
  calc
    (-t) * (-t) ^ (-(1 : ℝ) + h) = (-t) ^ (1 : ℝ) * (-t) ^ (-(1 : ℝ) + h) := by rw [Real.rpow_one]
    _ = (-t) ^ ((1 : ℝ) + (-(1 : ℝ) + h)) := by rw [Real.rpow_add hpos (1 : ℝ) (-(1 : ℝ) + h)]
    _ = (-t) ^ h := by ring_nf

end CIV
