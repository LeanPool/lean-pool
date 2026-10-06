/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Statements.AnisotropicBounds
public import LeanPool.CIVAxisymmetric.Reduction.ParabolicRescaleSolution
public import LeanPool.CIVAxisymmetric.Analysis.ScalingRadialExponent
public import LeanPool.CIVAxisymmetric.Analysis.ScalingSwirlVerticalExponent
public import LeanPool.CIVAxisymmetric.Regularity.ParabolicRescalingAxisymmetric

/-!
# Anisotropic Bounds Rescale

Supporting results for the Constantin–Ignatova–Vicol axisymmetric regularity theorem.
-/


public section

open Set
open CKN.Foundation.Parabolic CKN

noncomputable section
namespace CIV

private theorem meridional_smul (c x₁ x₃ : ℝ) :
    c • meridional x₁ x₃ = meridional (c * x₁) (c * x₃) := by
  ext i
  fin_cases i <;> simp [meridional]

private theorem scalingParabolic_meridional (R x₁ x₃ t : ℝ) :
    scalingParabolic R ((0 : Vec3), (0 : ℝ)) (meridional x₁ x₃, t) =
      (meridional (R * x₁) (R * x₃), R ^ 2 * t) := by
  show ((0 : Vec3) + R • meridional x₁ x₃, (0 : ℝ) + R ^ 2 * t) =
      (meridional (R * x₁) (R * x₃), R ^ 2 * t)
  rw [zero_add, zero_add, meridional_smul]

private theorem mem_unitCylinder_of_mem_meridional {x₁ x₃ t R : ℝ} (hR0 : 0 < R) (hR1 : R ≤ 1)
    (hmem : (meridional x₁ x₃, t) ∈ unitCylinder) :
    (meridional (R * x₁) (R * x₃), R ^ 2 * t) ∈ unitCylinder := by
  have hball : vec3EuclideanNorm (meridional x₁ x₃) < 1 := by
    have := hmem.1
    simpa [unitCylinder, spaceTimeSet, vec3Ball, sub_zero] using this
  have htime : t ∈ Ioo (-1 : ℝ) 0 := by
    have := hmem.2
    simpa [unitCylinder, spaceTimeSet] using this
  have hmem_ball : meridional (R * x₁) (R * x₃) ∈ vec3Ball 0 1 := by
    show vec3EuclideanNorm (meridional (R * x₁) (R * x₃) - 0) < 1
    rw [sub_zero, ← meridional_smul, vec3EuclideanNorm_smul, abs_of_pos hR0]
    have hpos : 0 ≤ vec3EuclideanNorm (meridional x₁ x₃) := vec3EuclideanNorm_nonneg _
    nlinarith only [hball, hR1, hpos]
  have hmem_time : R ^ 2 * t ∈ Ioo (-1 : ℝ) 0 := by
    rcases htime with ⟨htl, htr⟩
    have hR2pos : 0 < R ^ 2 := pow_pos hR0 2
    have hR2le1 : R ^ 2 ≤ 1 := pow_le_one₀ hR0.le hR1 (n := 2)
    have h_lower : -1 < R ^ 2 * t := by
      have ht_nonpos : t ≤ 0 := by linarith only [htr]
      have h_mul_ge : t ≤ R ^ 2 * t := by nlinarith only [hR2le1, ht_nonpos]
      linarith only [htl, h_mul_ge]
    have h_upper : R ^ 2 * t < 0 := by nlinarith only [htr, hR2pos]
    exact ⟨h_lower, h_upper⟩
  exact ⟨hmem_ball, hmem_time⟩

theorem anisotropicBounds_rescale {C h R : ℝ} (hC : 0 ≤ C) (hh0 : 0 ≤ h)
    (hR0 : 0 < R) (hR1 : R ≤ 1) {v : ParabolicPoint → Vec3}
    (hv : AnisotropicBounds C h v) :
    AnisotropicBounds (R ^ (-(2 * h)) * C) h (rescaleVelocity R ((0 : Vec3), (0 : ℝ)) v) := by
  intro a b hab x₁ x₃ t hmem
  have ht : t < 0 := by
    have := hmem.2
    simpa [unitCylinder, spaceTimeSet] using this.2
  have hdilate_mem : (meridional (R * x₁) (R * x₃), R ^ 2 * t) ∈ unitCylinder :=
    mem_unitCylinder_of_mem_meridional hR0 hR1 hmem
  obtain ⟨hbound0, hbound12⟩ := hv a b hab (R * x₁) (R * x₃) (R ^ 2 * t) hdilate_mem
  have hRpow_nonneg : (0 : ℝ) ≤ R ^ (1 + a + b) := by positivity
  constructor
  · have hmp := meridionalPartial_rescaleVelocity R ((0 : Vec3), (0 : ℝ)) v 0 a b
      (meridional x₁ x₃, t)
    rw [scalingParabolic_meridional] at hmp
    rw [hmp, abs_mul, abs_of_nonneg hRpow_nonneg]
    calc
      R ^ (1 + a + b) * |meridionalPartial (fun w => v w 0) a b (meridional (R * x₁) (R * x₃), R
        ^ 2 * t)|
          ≤ R ^ (1 + a + b) * (C * (-(R ^ 2 * t)) ^ (-(1 / 2 : ℝ) - (a : ℝ) / 2 - (1 / 2 - h) *
            b)) := by
        gcongr
      _ = R ^ (1 + a + b) * C * (-(R ^ 2 * t)) ^ (-(1 / 2 : ℝ) - (a : ℝ) / 2 - (1 / 2 - h) * b)
        := by
        ring
      _ ≤ C * (-t) ^ (-(1 / 2 : ℝ) - (a : ℝ) / 2 - (1 / 2 - h) * b) :=
        rpow_scaled_le_of_radialAnisoBound hC hh0 ht hR0 hR1 a b
      _ ≤ R ^ (-(2 * h)) * C * (-t) ^ (-(1 / 2 : ℝ) - (a : ℝ) / 2 - (1 / 2 - h) * b) := by
        have h1 : (1 : ℝ) ≤ R ^ (-(2 * h)) := by
          have h0 : R ^ (0 : ℝ) ≤ R ^ (-(2 * h)) :=
            Real.rpow_le_rpow_of_exponent_ge hR0 hR1 (by linarith only [hh0])
          simpa using h0
        have hnn : (0 : ℝ) ≤ (-t) ^ (-(1 / 2 : ℝ) - (a : ℝ) / 2 - (1 / 2 - h) * b) :=
          Real.rpow_nonneg (by linarith only [ht]) _
        have hm := mul_le_mul_of_nonneg_right h1 (mul_nonneg hC hnn)
        linarith only [hm]
  · have hmp2 := meridionalPartial_rescaleVelocity R ((0 : Vec3), (0 : ℝ)) v 2 a b
      (meridional x₁ x₃, t)
    have hmp1 := meridionalPartial_rescaleVelocity R ((0 : Vec3), (0 : ℝ)) v 1 a b
      (meridional x₁ x₃, t)
    rw [scalingParabolic_meridional] at hmp2 hmp1
    rw [hmp2, hmp1, abs_mul, abs_mul, abs_of_nonneg hRpow_nonneg]
    calc
      R ^ (1 + a + b) * |meridionalPartial (fun w => v w 2) a b (meridional (R * x₁) (R * x₃), R
        ^ 2 * t)|
          + R ^ (1 + a + b) * |meridionalPartial (fun w => v w 1) a b (meridional (R * x₁) (R *
            x₃), R ^ 2 * t)|
          = R ^ (1 + a + b) *
              (|meridionalPartial (fun w => v w 2) a b (meridional (R * x₁) (R * x₃), R ^ 2 * t)|
                + |meridionalPartial (fun w => v w 1) a b (meridional (R * x₁) (R * x₃), R ^ 2 *
                  t)|) := by
        ring
      _ ≤ R ^ (1 + a + b) *
            (C * (-(R ^ 2 * t)) ^ (-(1 / 2 : ℝ) - h - (a : ℝ) / 2 - (1 / 2 - h) * b)) := by
        gcongr
      _ = R ^ (1 + a + b) * C * (-(R ^ 2 * t)) ^ (-(1 / 2 : ℝ) - h - (a : ℝ) / 2 - (1 / 2 - h) *
        b) := by
        ring
      _ ≤ R ^ (-(2 * h)) * C * (-t) ^ (-(1 / 2 : ℝ) - h - (a : ℝ) / 2 - (1 / 2 - h) * b) :=
        rpow_scaled_le_of_swirlVerticalAnisoBound hC hh0 ht hR0 hR1 a b

private theorem rescaleVelocity_eq_smul_comp (R : ℝ) (u : ParabolicPoint → Vec3) :
    rescaleVelocity R ((0 : Vec3), (0 : ℝ)) u =
      fun w : ParabolicPoint => R • u ((R • w.1 : Vec3), R ^ 2 * w.2) := by
  funext w
  show R • u ((0 : Vec3) + R • w.1, (0 : ℝ) + R ^ 2 * w.2) = R • u ((R • w.1 : Vec3), R ^ 2 * w.2)
  rw [zero_add, zero_add]

theorem anisotropicBounds_angularMean_rescale {C h R : ℝ} (hC : 0 ≤ C) (hh0 : 0 ≤ h)
    (hR0 : 0 < R) (hR1 : R ≤ 1) {u : ParabolicPoint → Vec3}
    (hu : AnisotropicBounds C h (angularMean u)) :
    AnisotropicBounds (R ^ (-(2 * h)) * C) h
      (angularMean (rescaleVelocity R ((0 : Vec3), (0 : ℝ)) u)) := by
  have heq : angularMean (rescaleVelocity R ((0 : Vec3), (0 : ℝ)) u) =
      rescaleVelocity R ((0 : Vec3), (0 : ℝ)) (angularMean u) := by
    rw [rescaleVelocity_eq_smul_comp, rescaleVelocity_eq_smul_comp]
    funext z
    exact angularMean_smul_comp R R u z
  rw [heq]
  exact anisotropicBounds_rescale hC hh0 hR0 hR1 hu

end CIV
