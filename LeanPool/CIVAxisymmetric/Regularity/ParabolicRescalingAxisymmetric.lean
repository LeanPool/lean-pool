/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Statements.IsAxisymmetricOn
public import LeanPool.CIVAxisymmetric.Statements.UnitCylinder
public import LeanPool.CIVAxisymmetric.Regularity.ParabolicRescaling
public import LeanPool.CIVAxisymmetric.Setting.RotationLemmas

/-!
# Parabolic Rescaling Axisymmetric

Supporting results for the Constantin–Ignatova–Vicol axisymmetric regularity theorem.
-/


public section

open Set MeasureTheory
open CKN.Foundation.Parabolic CKN

noncomputable section

namespace CIV

/-- The rotation of a rescaled field equals the rescaling of the rotated field:
`rotField φ (R·, R²·) (c u) = c · rotField φ u` at the rescaled point. -/
theorem rotField_smul_comp (φ c R : ℝ) (u : ParabolicPoint → Vec3) (z : ParabolicPoint) :
    rotField φ (fun w : ParabolicPoint => c • u (R • w.1, R ^ 2 * w.2)) z =
      c • rotField φ u ((R • z.1 : Vec3), R ^ 2 * z.2) := by
  dsimp [rotField]
  rw [← rotZ_smul (-φ) R z.1, rotZ_smul φ c]

/-- The angular mean commutes with the parabolic rescaling:
`𝒫(c u(R·, R²·)) = c · 𝒫u` at the rescaled point. -/
theorem angularMean_smul_comp (c R : ℝ) (u : ParabolicPoint → Vec3) (z : ParabolicPoint) :
    angularMean (fun w : ParabolicPoint => c • u (R • w.1, R ^ 2 * w.2)) z =
      c • angularMean u ((R • z.1 : Vec3), R ^ 2 * z.2) := by
  unfold angularMean
  have h_eq : (fun (φ : ℝ) => rotField φ (fun w : ParabolicPoint => c • u (R • w.1, R ^ 2 *
    w.2)) z) =
      (fun (φ : ℝ) => c • rotField φ u ((R • z.1 : Vec3), R ^ 2 * z.2)) := by
    funext φ; exact rotField_smul_comp φ c R u z
  rw [h_eq]
  have h_int : ∫ (φ : ℝ) in (0 : ℝ)..(2 * Real.pi), c • rotField φ u ((R • z.1 : Vec3), R ^ 2 *
    z.2) =
      c • ∫ (φ : ℝ) in (0 : ℝ)..(2 * Real.pi), rotField φ u ((R • z.1 : Vec3), R ^ 2 * z.2) := by
    calc
      ∫ (φ : ℝ) in (0 : ℝ)..(2 * Real.pi), c • rotField φ u ((R • z.1 : Vec3), R ^ 2 * z.2)
          = (∫ (φ : ℝ) in Ioc (0 : ℝ) (2 * Real.pi), c • rotField φ u ((R • z.1 : Vec3), R ^ 2 *
            z.2) ∂ volume) -
            (∫ (φ : ℝ) in Ioc (2 * Real.pi) (0 : ℝ), c • rotField φ u ((R • z.1 : Vec3), R ^ 2 *
              z.2) ∂ volume) := rfl
      _ = (c • ∫ (φ : ℝ) in Ioc (0 : ℝ) (2 * Real.pi), rotField φ u ((R • z.1 : Vec3), R ^ 2 *
        z.2) ∂ volume) -
          (c • ∫ (φ : ℝ) in Ioc (2 * Real.pi) (0 : ℝ), rotField φ u ((R • z.1 : Vec3), R ^ 2 *
            z.2) ∂ volume) := by
        rw [MeasureTheory.integral_smul c, MeasureTheory.integral_smul c]
      _ = c • ((∫ (φ : ℝ) in Ioc (0 : ℝ) (2 * Real.pi), rotField φ u ((R • z.1 : Vec3), R ^ 2 *
        z.2) ∂ volume) -
               (∫ (φ : ℝ) in Ioc (2 * Real.pi) (0 : ℝ), rotField φ u ((R • z.1 : Vec3), R ^ 2 *
                 z.2) ∂ volume)) := by
        rw [smul_sub]
      _ = c • ∫ (φ : ℝ) in (0 : ℝ)..(2 * Real.pi), rotField φ u ((R • z.1 : Vec3), R ^ 2 * z.2)
        := rfl
  rw [h_int]
  rw [smul_comm]

/-- If `u` is axisymmetric on the unit cylinder, then the parabolically rescaled field
`R u(R·, R²·)` is also axisymmetric on the unit cylinder, for `0 < R ≤ 1`. -/
theorem isAxisymmetricOn_smul_comp_of_isAxisymmetricOn {u : ParabolicPoint → Vec3}
    {R : ℝ} (hR0 : 0 < R) (hR1 : R ≤ 1)
    (haxi : IsAxisymmetricOn u unitCylinder) :
    IsAxisymmetricOn (fun w : ParabolicPoint => R • u (R • w.1, R ^ 2 * w.2)) unitCylinder := by
  intro z hz
  rw [angularMean_smul_comp R R u z]
  have hz_ball : vec3EuclideanNorm z.1 < 1 := by
    have := hz.1
    simpa [unitCylinder, spaceTimeSet, vec3Ball, sub_zero] using this
  have hz_time : z.2 ∈ Ioo (-1 : ℝ) 0 := by
    have := hz.2
    simpa [unitCylinder, spaceTimeSet] using this
  have hmem_ball : (R • z.1 : Vec3) ∈ vec3Ball 0 1 := by
    rw [vec3Ball]
    simp [sub_zero]
    rw [vec3EuclideanNorm_smul, abs_of_pos hR0]
    have hpos : 0 ≤ vec3EuclideanNorm z.1 := vec3EuclideanNorm_nonneg _
    nlinarith only [hz_ball, hR1, hpos]
  have hmem_time : R ^ 2 * z.2 ∈ Ioo (-1 : ℝ) 0 := by
    rcases hz_time with ⟨hzl, hzr⟩
    have hR2pos : 0 < R ^ 2 := pow_pos hR0 2
    have hR2le1 : R ^ 2 ≤ 1 := pow_le_one₀ hR0.le hR1 (n := 2)
    have h_lower : -1 < R ^ 2 * z.2 := by
      have hz2_nonpos : z.2 ≤ 0 := by linarith only [hzr]
      have h_mul_ge : z.2 ≤ R ^ 2 * z.2 := by
        nlinarith only [hR2le1, hz2_nonpos]
      linarith only [hzl, h_mul_ge]
    have h_upper : R ^ 2 * z.2 < 0 := by
      nlinarith only [hzr, hR2pos]
    exact ⟨h_lower, h_upper⟩
  have hmem : ((R • z.1 : Vec3), R ^ 2 * z.2) ∈ unitCylinder := by
    unfold unitCylinder spaceTimeSet
    exact Set.mem_prod.mpr ⟨hmem_ball, hmem_time⟩
  rw [haxi ((R • z.1 : Vec3), R ^ 2 * z.2) hmem]

end CIV
