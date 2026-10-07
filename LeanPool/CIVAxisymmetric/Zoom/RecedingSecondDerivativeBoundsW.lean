/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Zoom.Receding

/-!
# Receding Second Derivative Bounds W

Supporting results for the Constantin–Ignatova–Vicol axisymmetric regularity theorem.
-/


public section

open Set
open CKN.Foundation.Parabolic CKN

noncomputable section

namespace CIV

private theorem mul_rpow_le_mul_rpow_neg_half' {C τ e : ℝ} (hC : 0 ≤ C) (hτ : τ ≤ -1)
    (he : e ≤ -(1 / 2 : ℝ)) : C * (-τ) ^ e ≤ C * (-τ) ^ (-(1 / 2 : ℝ)) :=
  mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (by linarith only [hτ]) he) hC

/-- Uniform second-derivative bound `eq:aniso:zoom:derivatives` for `∂_R∂_R W_n` in the
receding-axis recentred rescaled variables, the receding-axis analogue of
`CIV.abs_dr_zoomW_le_rpow_neg_half` one derivative order further: the raw combined bound
`abs_drdr_zoomWRec_add_abs_drdr_zoomSRec_le` supplies `|∂_R∂_R W_n| + |∂_R∂_R S_n| ≤ C
(-τ)^{-3/2 - h}`,
and dropping the `S_n` summand and normalizing the exponent to `-1/2` for `τ ≤ -1` gives the
uniform estimate needed by the corresponding statement. -/
theorem abs_drdr_zoomWRec_le_rpow_neg_half {C h lam rc zc : ℝ} (hlam : 0 < lam)
    {u : ParabolicPoint → Vec3} (hb : AnisotropicBounds C h u)
    (hu : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder) {p : (ℝ × ℝ) × ℝ}
    (hp : zoomPointRec lam h rc zc p ∈ unitCylinder) (hC : 0 ≤ C) (hh0 : 0 ≤ h)
    (hτ : p.2 ≤ -1) :
    |dr (dr (zoomWRec lam h rc zc u)) p| ≤ C * (-p.2) ^ (-(1 / 2 : ℝ)) := by
  have hdrop : |dr (dr (zoomWRec lam h rc zc u)) p|
      ≤ |dr (dr (zoomWRec lam h rc zc u)) p| + |dr (dr (zoomSRec lam h rc zc u)) p| :=
    le_add_of_nonneg_right (abs_nonneg _)
  refine le_trans
    (le_trans hdrop
      (abs_drdr_zoomWRec_add_abs_drdr_zoomSRec_le C h lam rc zc hlam u hb hu p hp))
    (mul_rpow_le_mul_rpow_neg_half' hC hτ (by linarith only [hh0]))

/-- Uniform second-derivative bound `eq:aniso:zoom:derivatives` for `∂_R∂_Z W_n` in the
receding-axis recentred rescaled variables, the receding-axis analogue of
`CIV.abs_dz_zoomW_le_rpow_neg_half` one derivative order further: the raw combined bound
`abs_drdz_zoomWRec_add_abs_drdz_zoomSRec_le` supplies `|∂_R∂_Z W_n| + |∂_R∂_Z S_n| ≤ C (-τ)^{-3/2}`,
the `h` terms cancelling, and dropping the `S_n` summand and normalizing the exponent to `-1/2`
for `τ ≤ -1` gives the uniform estimate. -/
theorem abs_drdz_zoomWRec_le_rpow_neg_half {C h lam rc zc : ℝ} (hlam : 0 < lam)
    {u : ParabolicPoint → Vec3} (hb : AnisotropicBounds C h u)
    (hu : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder) {p : (ℝ × ℝ) × ℝ}
    (hp : zoomPointRec lam h rc zc p ∈ unitCylinder) (hC : 0 ≤ C) (hτ : p.2 ≤ -1) :
    |dr (dz (zoomWRec lam h rc zc u)) p| ≤ C * (-p.2) ^ (-(1 / 2 : ℝ)) := by
  have hdrop : |dr (dz (zoomWRec lam h rc zc u)) p|
      ≤ |dr (dz (zoomWRec lam h rc zc u)) p| + |dr (dz (zoomSRec lam h rc zc u)) p| :=
    le_add_of_nonneg_right (abs_nonneg _)
  refine le_trans
    (le_trans hdrop
      (abs_drdz_zoomWRec_add_abs_drdz_zoomSRec_le C h lam rc zc hlam u hb hu p hp))
    (mul_rpow_le_mul_rpow_neg_half' hC hτ (by norm_num))

/-- Uniform second-derivative bound `eq:aniso:zoom:derivatives` for `∂_Z∂_Z W_n` in the
receding-axis recentred rescaled variables, the receding-axis analogue of
`CIV.abs_dz_zoomW_le_rpow_neg_half` one derivative order further: the raw combined bound
`abs_dzdz_zoomWRec_add_abs_dzdz_zoomSRec_le` supplies `|∂_Z∂_Z W_n| + |∂_Z∂_Z S_n| ≤ C
(-τ)^{-3/2 + h}`,
and dropping the `S_n` summand and normalizing the exponent to `-1/2` for `τ ≤ -1` with
`h ≤ 1/2` gives the uniform estimate. -/
theorem abs_dzdz_zoomWRec_le_rpow_neg_half {C h lam rc zc : ℝ} (hlam : 0 < lam)
    {u : ParabolicPoint → Vec3} (hb : AnisotropicBounds C h u)
    (hu : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder) {p : (ℝ × ℝ) × ℝ}
    (hp : zoomPointRec lam h rc zc p ∈ unitCylinder) (hC : 0 ≤ C) (hh1 : h ≤ 1 / 2)
    (hτ : p.2 ≤ -1) :
    |dz (dz (zoomWRec lam h rc zc u)) p| ≤ C * (-p.2) ^ (-(1 / 2 : ℝ)) := by
  have hdrop : |dz (dz (zoomWRec lam h rc zc u)) p|
      ≤ |dz (dz (zoomWRec lam h rc zc u)) p| + |dz (dz (zoomSRec lam h rc zc u)) p| :=
    le_add_of_nonneg_right (abs_nonneg _)
  refine le_trans
    (le_trans hdrop
      (abs_dzdz_zoomWRec_add_abs_dzdz_zoomSRec_le C h lam rc zc hlam u hb hu p hp))
    (mul_rpow_le_mul_rpow_neg_half' hC hτ (by linarith only [hh1]))

end CIV
