/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Zoom.RescaledBounds

/-! ### Normalizer for the second-derivative exponent -/

public section

open Set
open CKN.Foundation.Parabolic CKN

noncomputable section

namespace CIV



private theorem mul_rpow_le_mul_rpow_neg_half' {C τ e : ℝ} (hC : 0 ≤ C) (hτ : τ ≤ -1)
    (he : e ≤ -(1 / 2 : ℝ)) : C * (-τ) ^ e ≤ C * (-τ) ^ (-(1 / 2 : ℝ)) := by
  have hbase : 1 ≤ -τ := by linarith only [hτ]
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hbase he) hC

/-! ### The uniform second-derivative half of `eq:aniso:zoom:derivatives` for `W_n` -/

/-- Uniform bound for `∂_R∂_R W_n` (`eq:aniso:zoom:derivatives`, exponent `-3/2 - h`).
The raw combined bound `abs_drdr_zoomW_add_abs_drdr_zoomS_le` contains a swirl summand
`|dr(dr(zoomS))|`; dropping it by nonnegativity and normalizing the remaining
`W_n` bound to the standard `τ ≤ -1` form gives the uniform estimate. -/
theorem abs_drdr_zoomW_le_rpow_neg_half {C h lam zc : ℝ} (hlam : 0 < lam)
    {u : ParabolicPoint → Vec3} (hb : AnisotropicBounds C h u)
    (hu : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder) {p : (ℝ × ℝ) × ℝ}
    (hp : zoomPoint lam h zc p ∈ unitCylinder) (hC : 0 ≤ C) (hh0 : 0 ≤ h) (hτ : p.2 ≤ -1) :
    |dr (dr (zoomW lam h zc u)) p| ≤ C * (-p.2) ^ (-(1 / 2 : ℝ)) := by
  have hdrop : |dr (dr (zoomW lam h zc u)) p|
      ≤ |dr (dr (zoomW lam h zc u)) p| + |dr (dr (zoomS lam h zc u)) p| :=
    le_add_of_nonneg_right (abs_nonneg _)
  refine le_trans
    (le_trans hdrop (abs_drdr_zoomW_add_abs_drdr_zoomS_le C h lam zc hlam u hb hu p hp)) ?_
  exact mul_rpow_le_mul_rpow_neg_half' hC hτ (by
    have : -(1 / 2 : ℝ) - h - 2 / 2 - (1 / 2 - h) * 0 = -(3 / 2 : ℝ) - h := by ring
    rw [this]
    linarith only [hh0])

/-- Uniform bound for `∂_R∂_Z W_n` (`eq:aniso:zoom:derivatives`, exponent `-3/2`).
The raw combined bound `abs_drdz_zoomW_add_abs_drdz_zoomS_le` contains a swirl summand
`|dr(dz(zoomS))|`; dropping it by nonnegativity and normalizing the remaining
`W_n` bound to the standard `τ ≤ -1` form gives the uniform estimate. -/
theorem abs_drdz_zoomW_le_rpow_neg_half {C h lam zc : ℝ} (hlam : 0 < lam)
    {u : ParabolicPoint → Vec3} (hb : AnisotropicBounds C h u)
    (hu : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder) {p : (ℝ × ℝ) × ℝ}
    (hp : zoomPoint lam h zc p ∈ unitCylinder) (hC : 0 ≤ C) (hτ : p.2 ≤ -1) :
    |dr (dz (zoomW lam h zc u)) p| ≤ C * (-p.2) ^ (-(1 / 2 : ℝ)) := by
  have hdrop : |dr (dz (zoomW lam h zc u)) p|
      ≤ |dr (dz (zoomW lam h zc u)) p| + |dr (dz (zoomS lam h zc u)) p| :=
    le_add_of_nonneg_right (abs_nonneg _)
  refine le_trans
    (le_trans hdrop (abs_drdz_zoomW_add_abs_drdz_zoomS_le C h lam zc hlam u hb hu p hp)) ?_
  exact mul_rpow_le_mul_rpow_neg_half' hC hτ (by norm_num)

/-- Uniform bound for `∂_Z∂_Z W_n` (`eq:aniso:zoom:derivatives`, exponent `-3/2 + h`).
The raw combined bound `abs_dzdz_zoomW_add_abs_dzdz_zoomS_le` contains a swirl summand
`|dz(dz(zoomS))|`; dropping it by nonnegativity and normalizing the remaining
`W_n` bound to the standard `τ ≤ -1` form gives the uniform estimate. -/
theorem abs_dzdz_zoomW_le_rpow_neg_half {C h lam zc : ℝ} (hlam : 0 < lam)
    {u : ParabolicPoint → Vec3} (hb : AnisotropicBounds C h u)
    (hu : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder) {p : (ℝ × ℝ) × ℝ}
    (hp : zoomPoint lam h zc p ∈ unitCylinder) (hC : 0 ≤ C) (hh1 : h ≤ 1 / 2) (hτ : p.2 ≤ -1) :
    |dz (dz (zoomW lam h zc u)) p| ≤ C * (-p.2) ^ (-(1 / 2 : ℝ)) := by
  have hdrop : |dz (dz (zoomW lam h zc u)) p|
      ≤ |dz (dz (zoomW lam h zc u)) p| + |dz (dz (zoomS lam h zc u)) p| :=
    le_add_of_nonneg_right (abs_nonneg _)
  refine le_trans
    (le_trans hdrop (abs_dzdz_zoomW_add_abs_dzdz_zoomS_le C h lam zc hlam u hb hu p hp)) ?_
  exact mul_rpow_le_mul_rpow_neg_half' hC hτ (by
    have : -(1 / 2 : ℝ) - h - 0 / 2 - (1 / 2 - h) * 2 = -(3 / 2 : ℝ) + h := by ring
    rw [this]
    linarith only [hh1])

end CIV
