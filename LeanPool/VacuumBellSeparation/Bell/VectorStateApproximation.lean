/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Bell.OperationalReehSchliederDefs

/-! Uniform bounded-operator estimates for actual unit vectors in the original Hilbert space. -/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation.Bipartite

open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Reeh–Schlieder unit vector. -/
def reehSchliederUnitVector (x : H) : H := (‖x‖ : ℂ)⁻¹ • x

omit [CompleteSpace H] in
theorem reehSchliederUnitVector_norm {x : H} (hx : x ≠ 0) :
    ‖reehSchliederUnitVector x‖ = 1 := by
  rw [reehSchliederUnitVector, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg x), inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]

omit [CompleteSpace H] in
theorem norm_smul_reehSchliederUnitVector {x : H} (hx : x ≠ 0) :
    (‖x‖ : ℂ) • reehSchliederUnitVector x = x := by
  rw [reehSchliederUnitVector, smul_smul,
    mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hx)), one_smul]

omit [CompleteSpace H] in
theorem unitVector_distance_le {x χ : H} (hx : x ≠ 0) (hχ : ‖χ‖ = 1) :
    ‖χ - reehSchliederUnitVector x‖ ≤ 2 * ‖χ - x‖ := by
  have hunit := reehSchliederUnitVector_norm hx
  have he : reehSchliederUnitVector x - x =
      ((1 - ‖x‖ : ℝ) : ℂ) • reehSchliederUnitVector x := by
    rw [Complex.ofReal_sub, Complex.ofReal_one, sub_smul, one_smul,
      norm_smul_reehSchliederUnitVector hx]
  have hd : ‖reehSchliederUnitVector x - x‖ = |1 - ‖x‖| := by
    rw [he, norm_smul, Complex.norm_real, Real.norm_eq_abs, hunit, mul_one]
  have hr : |1 - ‖x‖| ≤ ‖χ - x‖ := by
    simpa only [hχ] using abs_norm_sub_norm_le χ x
  calc
    ‖χ - reehSchliederUnitVector x‖ ≤ ‖χ - x‖ + ‖x - reehSchliederUnitVector x‖ :=
      norm_sub_le_norm_sub_add_norm_sub χ x (reehSchliederUnitVector x)
    _ = ‖χ - x‖ + |1 - ‖x‖| := by rw [norm_sub_rev x, hd]
    _ ≤ 2 * ‖χ - x‖ := by linarith

omit [CompleteSpace H] in
theorem vectorState_uniform_difference_bound (x y : H) (R : H →L[ℂ] H) :
    ‖⟪x, R x⟫_ℂ - ⟪y, R y⟫_ℂ‖ ≤ (‖x‖ + ‖y‖) * ‖x - y‖ * ‖R‖ := by
  have he : ⟪x, R x⟫_ℂ - ⟪y, R y⟫_ℂ =
      ⟪x - y, R x⟫_ℂ + ⟪y, R (x - y)⟫_ℂ := by
    rw [map_sub, inner_sub_left, inner_sub_right]
    ring
  rw [he]
  calc
    _ ≤ ‖⟪x - y, R x⟫_ℂ‖ + ‖⟪y, R (x - y)⟫_ℂ‖ := norm_add_le _ _
    _ ≤ ‖x - y‖ * ‖R x‖ + ‖y‖ * ‖R (x - y)‖ :=
      add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _)
    _ ≤ ‖x - y‖ * (‖R‖ * ‖x‖) + ‖y‖ * (‖R‖ * ‖x - y‖) :=
      add_le_add (mul_le_mul_of_nonneg_left (R.le_opNorm x) (norm_nonneg _))
        (mul_le_mul_of_nonneg_left (R.le_opNorm (x - y)) (norm_nonneg _))
    _ = (‖x‖ + ‖y‖) * ‖x - y‖ * ‖R‖ := by ring

end VacuumBellSeparation.Bipartite
