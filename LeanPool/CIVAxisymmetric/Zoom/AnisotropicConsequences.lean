/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Statements.AnisotropicBounds
public import LeanPool.CIVAxisymmetric.Statements.MeridionalSmallness

/-!
# Immediate consequences of the anisotropic Type II bounds

Each of the four lemmas below extracts a pointwise estimate from
`AnisotropicBounds C h u` (eq:aniso:bounds) by specialising the derivative
orders `(a, b)` and simplifying the exponent.
-/

public section

open Set
open CKN.Foundation.Parabolic CKN

noncomputable section

namespace CIV



/-- `∂_z u_r` bound from the anisotropic Type II bounds.
Corresponds to the `b = 1` term in `eq:aniso:bounds`. -/
theorem abs_dz_ur_le_of_anisotropicBounds {C h : ℝ} {u : ParabolicPoint → Vec3}
    (hb : AnisotropicBounds C h u) {x₁ x₃ t : ℝ} (hz : (meridional x₁ x₃, t) ∈ unitCylinder) :
    |spatialPartial (fun w => u w 0) 2 (meridional x₁ x₃, t)| ≤
      C * (-t) ^ (-(1 / 2 : ℝ) - (1 / 2 - h)) := by
  have hside : (0 : ℕ) + 1 ≤ 2 := by norm_num
  rcases hb 0 1 hside x₁ x₃ t hz with ⟨hfirst, _⟩
  simpa [meridionalPartial] using hfirst

/-- `(-t) * |∂_z u_r|` bound from the anisotropic Type II bounds, via
`mul_le_mul_of_nonneg_left` and the `Real.rpow` identity `s * s ^ α = s ^ (1 + α)`. -/
theorem neg_t_mul_abs_dz_ur_le {C h : ℝ} {u : ParabolicPoint → Vec3}
    (hb : AnisotropicBounds C h u) {x₁ x₃ t : ℝ}
    (hz : (meridional x₁ x₃, t) ∈ unitCylinder) :
    (-t) * |spatialPartial (fun w => u w 0) 2 (meridional x₁ x₃, t)| ≤ C * (-t) ^ h := by
  have hpos : 0 < -t := by
    rcases hz with ⟨_, ht⟩
    exact neg_pos.mpr ht.2
  have hbound := abs_dz_ur_le_of_anisotropicBounds hb hz
  have h_mul : (-t) * (C * (-t) ^ (-(1 / 2 : ℝ) - (1 / 2 - h))) =
      C * (-t) ^ h := by
    calc
      (-t) * (C * (-t) ^ (-(1 / 2 : ℝ) - (1 / 2 - h))) =
          C * ((-t) * (-t) ^ (-(1 / 2 : ℝ) - (1 / 2 - h))) := by ring_nf
      _ = C * ((-t) ^ (1 : ℝ) * (-t) ^ (-(1 / 2 : ℝ) - (1 / 2 - h))) := by rw [Real.rpow_one]
      _ = C * (-t) ^ ((1 : ℝ) + (-(1 / 2 : ℝ) - (1 / 2 - h))) := by
        rw [Real.rpow_add hpos (1 : ℝ) (-(1 / 2 : ℝ) - (1 / 2 - h))]
      _ = C * (-t) ^ h := by ring_nf
  have h_nonneg : 0 ≤ -t := by linarith only [hpos]
  exact le_trans (mul_le_mul_of_nonneg_left hbound h_nonneg) (by rw [h_mul])

/-- `u_r` bound from the anisotropic Type II bounds at `(a, b) = (0, 0)`.
Corresponds to the first term in `eq:aniso:bounds` with no derivatives. -/
theorem abs_ur_le_of_anisotropicBounds {C h : ℝ} {u : ParabolicPoint → Vec3}
    (hb : AnisotropicBounds C h u) {x₁ x₃ t : ℝ} (hz : (meridional x₁ x₃, t) ∈ unitCylinder) :
    |u (meridional x₁ x₃, t) 0| ≤ C * (-t) ^ (-(1 / 2 : ℝ)) := by
  have hside : (0 : ℕ) + 0 ≤ 2 := by norm_num
  rcases hb 0 0 hside x₁ x₃ t hz with ⟨hfirst, _⟩
  simpa [meridionalPartial] using hfirst

/-- `|u_z| + |u_θ|` bound from the anisotropic Type II bounds at `(a, b) = (0, 0)`.
Corresponds to the second term in `eq:aniso:bounds` with no derivatives. -/
theorem abs_uz_add_abs_utheta_le_of_anisotropicBounds {C h : ℝ} {u : ParabolicPoint → Vec3}
    (hb : AnisotropicBounds C h u) {x₁ x₃ t : ℝ} (hz : (meridional x₁ x₃, t) ∈ unitCylinder) :
    |u (meridional x₁ x₃, t) 2| + |u (meridional x₁ x₃, t) 1| ≤
      C * (-t) ^ (-(1 / 2 : ℝ) - h) := by
  have hside : (0 : ℕ) + 0 ≤ 2 := by norm_num
  rcases hb 0 0 hside x₁ x₃ t hz with ⟨_, hsecond⟩
  simpa [meridionalPartial] using hsecond

end CIV
