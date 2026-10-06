/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Statements.Meridional
public import LeanPool.CIVAxisymmetric.Statements.UnitCylinder
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Ambient.Basis
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# The meridional segment through the axis

The continuity statements for `u_r / r` and for `ω_θ / r` across the axis are all proved the
same way: the quotient at `(x₁, 0, x₃)` is an average of a radial derivative along the segment
`s ↦ (s x₁, 0, x₃)`, `s ∈ [0, 1]`, which stays inside the unit ball. This module collects the
elementary facts about that segment and about the clamp `s ↦ max 0 (min s 1)` used to extend
the segment parameter to all of `ℝ`, so that the several quotient modules share one copy.
-/

public section

open Set
open CKN.Foundation.Parabolic CKN


noncomputable section

namespace CIV

/-- A point of the axis at height `|x₃| < 1` lies in the unit cylinder at every time of
`(-1, 0)`. -/
theorem mem_unitCylinder_meridional (x₃ : ℝ) (hx : |x₃| < 1) (t : ℝ)
    (ht : t ∈ Set.Ioo (-1 : ℝ) 0) :
    ((meridional 0 x₃, t) : ParabolicPoint) ∈ unitCylinder := by
  unfold unitCylinder spaceTimeSet
  refine ⟨?_, ht⟩
  rw [mem_vec3Ball, sub_zero]
  unfold vec3EuclideanNorm
  simp [meridional, Fin.sum_univ_three]
  have hsq : x₃ ^ 2 < 1 := by
    have habs := abs_lt.mp hx
    nlinarith only [habs.1, habs.2]
  have hpos : 0 ≤ x₃ ^ 2 := pow_two_nonneg x₃
  have hpos_one : (0 : ℝ) ≤ 1 := by norm_num
  rw [Real.sqrt_lt hpos hpos_one]
  nlinarith only [hsq]

/-- The first coordinate of a meridional point is its axis distance. -/
theorem meridional_apply_zero (x₁ x₃ : ℝ) : meridional x₁ x₃ 0 = x₁ := by
  simp [meridional]

/-- The meridional point `(a, 0, x₃)` written in the standard basis. -/
theorem meridional_eq (a x₃ : ℝ) :
    meridional a x₃ = a • basisVec 0 + x₃ • basisVec 2 := by
  funext i
  fin_cases i <;> simp [meridional, basisVec_apply]

/-- The segment `s ↦ (s x₁, 0, x₃)` from the axis to `(x₁, 0, x₃)` is affine in `s`, with
constant velocity `x₁ e₁`. -/
theorem hasDerivAt_meridional_scale (x₁ x₃ s : ℝ) :
    HasDerivAt (fun s : ℝ => meridional (s * x₁) x₃) (x₁ • basisVec 0) s := by
  have heq : (fun s : ℝ => meridional (s * x₁) x₃)
      = fun s : ℝ => s • (x₁ • basisVec 0) + x₃ • basisVec 2 := by
    funext s
    rw [meridional_eq, mul_smul]
  rw [heq]
  simpa using (hasDerivAt_id s).smul_const (x₁ • basisVec 0) |>.add_const (x₃ • basisVec 2)

/-- The segment from the axis to a meridional point of the open unit ball stays in the open
unit ball, and so does its extension by any parameter of size at most one. -/
theorem meridional_scale_mem_vec3Ball {x₁ x₃ s : ℝ} (hx : x₁ ^ 2 + x₃ ^ 2 < 1)
    (hs : |s| ≤ 1) : meridional (s * x₁) x₃ ∈ vec3Ball (0 : Vec3) 1 := by
  rw [mem_vec3Ball, sub_zero]
  unfold vec3EuclideanNorm
  simp [meridional, Fin.sum_univ_three]
  have hb := abs_le.mp hs
  have hs2 : s ^ 2 ≤ 1 := by
    nlinarith only [mul_nonneg (by linarith only [hb.1] : (0:ℝ) ≤ s + 1)
      (by linarith only [hb.2] : (0:ℝ) ≤ 1 - s)]
  have hkey : (s * x₁) ^ 2 ≤ x₁ ^ 2 := by
    nlinarith only [mul_le_mul_of_nonneg_right hs2 (sq_nonneg x₁)]
  have hpos : (0:ℝ) ≤ (s * x₁) ^ 2 + x₃ ^ 2 := by positivity
  rw [Real.sqrt_lt hpos (by norm_num)]
  nlinarith only [hkey, hx]

/-- The clamp `max 0 (min s 1)` of a real number lands in `[0, 1]`. -/
theorem clamp_mem_Icc (s : ℝ) : max 0 (min s 1) ∈ Set.Icc (0:ℝ) 1 :=
  ⟨le_max_left _ _, max_le (by norm_num) (min_le_right s 1)⟩

/-- The clamp of a real number has size at most one. -/
theorem abs_clamp_le_one (s : ℝ) : |max 0 (min s 1)| ≤ 1 := by
  have h := clamp_mem_Icc s
  exact abs_le.mpr ⟨by linarith only [h.1], h.2⟩

/-- The clamp fixes every point of `[0, 1]`. -/
theorem clamp_eq_self {s : ℝ} (hs : s ∈ Set.Icc (0:ℝ) 1) : max 0 (min s 1) = s := by
  rw [min_eq_left hs.2, max_eq_right hs.1]

end CIV
