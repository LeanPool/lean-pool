/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Analytic.SkewGauge
public import LeanPool.HighContrastHomogenization.Analytic.TestNorms
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.NormalizedRootCoefficient

/-!
# High-contrast homogenization: Provider.Regularity.RoundedCoefficientWeightedNormGauge

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Scalar and skew-gauge cancellation for the rounded coefficient

The R3-A rounded coefficient is built from a positive scalar multiple of the
physical coefficient after subtraction of the constant comparison skew part.
This module records the exact effect of those two operations on the normalized
weighted gradient norm, so estimates can be returned to the original physical
coefficient without adding a hypothesis.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- Positive scalar multiplication of the coefficient multiplies the weighted
gradient norm by the square root of that scalar. -/
theorem weightedGradNorm_smul_coefficient
    {U : Set (Vec d)} (b : CoeffField d) (F : Vec d → Vec d)
    {mu : ℝ} (hmu : 0 ≤ mu) :
    weightedGradNorm (fun x ↦ mu • b x) U F =
      (ENNReal.ofReal mu) ^ (1 / 2 : ℝ) * weightedGradNorm b U F := by
  have hpoint : (fun x ↦ ENNReal.ofReal
      (vecDot (F x) (matVecMul (symmPart (mu • b x)) (F x)))) =
      fun x ↦ ENNReal.ofReal mu * ENNReal.ofReal
        (vecDot (F x) (matVecMul (symmPart (b x)) (F x))) := by
    funext x
    rw [symmPart_smul, smul_matVecMul, vecDot_smul_right,
      ENNReal.ofReal_mul hmu]
  unfold weightedGradNorm
  rw [hpoint, eVolumeAverage_const_mul U _ ENNReal.ofReal_ne_top,
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2)]

/-- The exact scalar-normalized skew gauge used by the rounded map differs
from the original physical weighted norm only by its positive scalar factor. -/
theorem weightedGradNorm_normalizedSkewGauge
    [NeZero d] (abar : Mat d) (hS : (symmPart abar).PosDef)
    (a : CoeffField d) (U : Set (Vec d)) (F : Vec d → Vec d) :
    weightedGradNorm
        (fun x ↦ specBound ((symmPart abar)⁻¹) •
          (a x - skewPart abar)) U F =
      (ENNReal.ofReal (specBound ((symmPart abar)⁻¹))) ^ (1 / 2 : ℝ) *
        weightedGradNorm a U F := by
  let b : CoeffField d := fun x ↦ a x - skewPart abar
  let mu : ℝ := specBound ((symmPart abar)⁻¹)
  have hmu : 0 ≤ mu := (normalizedRootScale_pos hS).le
  have hk : IsSkewMat (skewPart abar) := matTranspose_skewPart abar
  have hfield : (fun x ↦ b x + skewPart abar) = a := by
    funext x
    simp only [b, sub_add_cancel]
  have hgauge := weightedGradNorm_add_constSkew b U F (skewPart abar) hk
  rw [hfield] at hgauge
  calc
    weightedGradNorm
        (fun x ↦ specBound ((symmPart abar)⁻¹) •
          (a x - skewPart abar)) U F =
        weightedGradNorm (fun x ↦ mu • b x) U F := by rfl
    _ = (ENNReal.ofReal mu) ^ (1 / 2 : ℝ) *
        weightedGradNorm b U F := weightedGradNorm_smul_coefficient b F hmu
    _ = (ENNReal.ofReal (specBound ((symmPart abar)⁻¹))) ^ (1 / 2 : ℝ) *
        weightedGradNorm a U F := by rw [hgauge]

/-- A weighted-norm comparison in the scalar-normalized skew gauge cancels
back to the same comparison for the original coefficient. -/
theorem weightedGradNorm_le_of_normalizedSkewGauge_le
    [NeZero d] (abar : Mat d) (hS : (symmPart abar).PosDef)
    (a : CoeffField d) (U V : Set (Vec d)) (F : Vec d → Vec d)
    (C : ℝ≥0∞)
    (hbound : weightedGradNorm
        (fun x ↦ specBound ((symmPart abar)⁻¹) •
          (a x - skewPart abar)) U F ≤
      C * weightedGradNorm
        (fun x ↦ specBound ((symmPart abar)⁻¹) •
          (a x - skewPart abar)) V F) :
    weightedGradNorm a U F ≤ C * weightedGradNorm a V F := by
  let scale : ℝ≥0∞ :=
    (ENNReal.ofReal (specBound ((symmPart abar)⁻¹))) ^ (1 / 2 : ℝ)
  have hscalePos : 0 < scale := by
    exact ENNReal.rpow_pos
      (ENNReal.ofReal_pos.mpr (normalizedRootScale_pos hS))
      ENNReal.ofReal_ne_top
  have hscaleTop : scale ≠ ⊤ := by
    exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top
  rw [weightedGradNorm_normalizedSkewGauge abar hS a U F,
    weightedGradNorm_normalizedSkewGauge abar hS a V F] at hbound
  have hbound' : scale * weightedGradNorm a U F ≤
      scale * (C * weightedGradNorm a V F) := by
    simpa only [scale, mul_assoc, mul_left_comm, mul_comm] using hbound
  exact (ENNReal.mul_le_mul_iff_right hscalePos.ne' hscaleTop).mp hbound'

end

end HighContrast
end HCPolySupport
