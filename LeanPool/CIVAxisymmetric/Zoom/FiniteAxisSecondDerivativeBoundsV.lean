/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Zoom.RescaledBounds

/-! ### The Step 2 second-derivative bounds -/

public section

open Set
open CKN.Foundation.Parabolic CKN

noncomputable section

namespace CIV



/-- For `τ ≤ -1` a nonpositive shift of the exponent only decreases the power of `-τ`. -/
private theorem mul_rpow_le_mul_rpow_neg_half' {C τ e : ℝ} (hC : 0 ≤ C) (hτ : τ ≤ -1)
    (he : e ≤ -(1 / 2 : ℝ)) : C * (-τ) ^ e ≤ C * (-τ) ^ (-(1 / 2 : ℝ)) :=
  mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (by linarith only [hτ]) he) hC

/-- Second-derivative bound for `∂_R∂_R V_n` (`eq:aniso:zoom:derivatives`, exponent `-1/2`). -/
theorem abs_drdr_zoomV_le_rpow_neg_half {C h lam zc : ℝ} (hlam : 0 < lam)
    {u : ParabolicPoint → Vec3} (hb : AnisotropicBounds C h u)
    (hu : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder) {p : (ℝ × ℝ) × ℝ}
    (hp : zoomPoint lam h zc p ∈ unitCylinder) (hC : 0 ≤ C) (hτ : p.2 ≤ -1) :
    |dr (dr (zoomV lam h zc u)) p| ≤ C * (-p.2) ^ (-(1 / 2 : ℝ)) := by
  refine le_trans (abs_drdr_zoomV_le C h lam zc hlam u hb hu p hp) ?_
  exact mul_rpow_le_mul_rpow_neg_half' hC hτ (by norm_num)

/-- Second-derivative bound for `∂_R∂_Z V_n` (`eq:aniso:zoom:derivatives`, exponent `-1`). -/
theorem abs_drdz_zoomV_le_rpow_neg_half {C h lam zc : ℝ} (hlam : 0 < lam)
    {u : ParabolicPoint → Vec3} (hb : AnisotropicBounds C h u)
    (hu : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder) {p : (ℝ × ℝ) × ℝ}
    (hp : zoomPoint lam h zc p ∈ unitCylinder) (hC : 0 ≤ C) (hh1 : h ≤ 1 / 2)
    (hτ : p.2 ≤ -1) :
    |dr (dz (zoomV lam h zc u)) p| ≤ C * (-p.2) ^ (-(1 / 2 : ℝ)) := by
  refine le_trans (abs_drdz_zoomV_le C h lam zc hlam u hb hu p hp) ?_
  exact mul_rpow_le_mul_rpow_neg_half' hC hτ (by linarith only [hh1])

/-- Second-derivative bound for `∂_Z∂_Z V_n` (`eq:aniso:zoom:derivatives`, exponent `-1 + 2h`). -/
theorem abs_dzdz_zoomV_le_rpow_neg_half {C h lam zc : ℝ} (hlam : 0 < lam)
    {u : ParabolicPoint → Vec3} (hb : AnisotropicBounds C h u)
    (hu : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder) {p : (ℝ × ℝ) × ℝ}
    (hp : zoomPoint lam h zc p ∈ unitCylinder) (hC : 0 ≤ C) (hh1 : h ≤ 1 / 2)
    (hτ : p.2 ≤ -1) :
    |dz (dz (zoomV lam h zc u)) p| ≤ C * (-p.2) ^ (-(1 / 2 : ℝ)) := by
  refine le_trans (abs_dzdz_zoomV_le C h lam zc hlam u hb hu p hp) ?_
  exact mul_rpow_le_mul_rpow_neg_half' hC hτ (by linarith only [hh1])

end CIV
