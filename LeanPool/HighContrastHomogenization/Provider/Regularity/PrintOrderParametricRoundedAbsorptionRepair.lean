/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.PrintOrderNearIdentityDualAbsorption
public import LeanPool.HighContrastHomogenization.Provider.Regularity.RoundedAffineMap

/-!
# High-contrast homogenization: Provider.Regularity.PrintOrderParametricRoundedAbsorptionRepair

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Parametric rounded-reference repair for perturbative absorption

The rounded grid is defined at every generation above `kZero d`.  This file
states the exact constructor strengthening needed to select that generation
after the identity-regularity constant is known.  No claim is made that the
canonical generation already satisfies the strengthened tolerance.
-/

namespace HCPolySupport
namespace HighContrast
open MeasureTheory Set
open scoped Matrix.Norms.L2Operator

noncomputable section

/-- The constant rounded reference obtained from an arbitrary admissible
rounding generation. -/
@[expose]
def roundedReferenceMatrixAtGeneration {d : ℕ} [NeZero d]
    (l : ℤ) (abar : Mat d) (_hS : (symmPart abar).PosDef) : Mat d :=
  (roundedGrid l (symmPart abar))⁻¹ *
      (specBound ((symmPart abar)⁻¹) • symmPart abar) *
    matTranspose (roundedGrid l (symmPart abar))⁻¹

/-- The identity constant enlarged by the component-sum matrix-action cost.
The lower bound by one makes the tightened tolerance positive even when the
identity estimate has zero constant. -/
@[expose]
def printOrderAbsorptionEffectiveIdentityConstant
    (d : ℕ) (Cid : ℝ) : ℝ :=
  max 1 (Cid * (d : ℝ) ^ 2)

/-- The constructor tolerance selected after the effective identity constant
is known. -/
@[expose]
def printOrderAbsorptionTolerance (d : ℕ) (Cid : ℝ) : ℝ :=
  1 / (2 * printOrderAbsorptionEffectiveIdentityConstant d Cid)

theorem printOrderAbsorptionEffectiveIdentityConstant_pos
    (d : ℕ) (Cid : ℝ) :
    0 < printOrderAbsorptionEffectiveIdentityConstant d Cid := by
  have hone : (1 : ℝ) ≤
      printOrderAbsorptionEffectiveIdentityConstant d Cid := by
    exact le_max_left _ _
  linarith only [hone]

theorem printOrderAbsorptionTolerance_pos (d : ℕ) (Cid : ℝ) :
    0 < printOrderAbsorptionTolerance d Cid := by
  have hCeff :
      0 < printOrderAbsorptionEffectiveIdentityConstant d Cid :=
    printOrderAbsorptionEffectiveIdentityConstant_pos d Cid
  rw [printOrderAbsorptionTolerance]
  exact one_div_pos.mpr (mul_pos (by norm_num) hCeff)

theorem printOrderAbsorptionTolerance_le_half (d : ℕ) (Cid : ℝ) :
    printOrderAbsorptionTolerance d Cid ≤ 1 / 2 := by
  have hCeff : (1 : ℝ) ≤
      printOrderAbsorptionEffectiveIdentityConstant d Cid :=
    le_max_left _ _
  have hden : (2 : ℝ) ≤
      2 * printOrderAbsorptionEffectiveIdentityConstant d Cid :=
    by simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hCeff (show (0 : ℝ) ≤ 2 by norm_num)
  rw [printOrderAbsorptionTolerance]
  exact one_div_le_one_div_of_le (by norm_num) hden

/-- The tightened tolerance gives precisely the absorption coefficient needed
by the component-sum full-dual norm. -/
theorem printOrderAbsorptionTolerance_smallness
    (d : ℕ) (Cid : ℝ) :
    Cid * ((d : ℝ) ^ 2 * printOrderAbsorptionTolerance d Cid) ≤
      1 / 2 := by
  let Ceff : ℝ := printOrderAbsorptionEffectiveIdentityConstant d Cid
  have hCeff : 0 < Ceff := by
    simpa only [Ceff] using
      printOrderAbsorptionEffectiveIdentityConstant_pos d Cid
  have hproduct : Cid * (d : ℝ) ^ 2 ≤ Ceff := by
    simpa only [Ceff, printOrderAbsorptionEffectiveIdentityConstant] using
      (le_max_right (1 : ℝ) (Cid * (d : ℝ) ^ 2))
  have hden : 0 < 2 * Ceff := mul_pos (by norm_num) hCeff
  calc
    Cid * ((d : ℝ) ^ 2 * printOrderAbsorptionTolerance d Cid) =
        (Cid * (d : ℝ) ^ 2) / (2 * Ceff) := by
          rw [printOrderAbsorptionTolerance]
          change Cid * ((d : ℝ) ^ 2 *
            (1 / (2 * Ceff))) = (Cid * (d : ℝ) ^ 2) / (2 * Ceff)
          rw [div_eq_mul_inv]
          ring
    _ ≤ Ceff / (2 * Ceff) :=
      (div_le_div_iff_of_pos_right hden).2 hproduct
    _ = 1 / 2 := by
      field_simp [ne_of_gt hCeff]

/-- Exact constructor-side repair: select a rounded generation after the
desired defect tolerance is known, retaining a uniform ellipticity window.
The first conjunct records the symmetric positive reference required by the
constant-coefficient carrier. -/
@[expose]
def PrintOrderRoundedReferenceConstructorAtTolerance
    (d : ℕ) [NeZero d] (eps : ℝ) : Prop :=
  ∃ l : ℤ, (kZero d : ℤ) ≤ l ∧
    ∀ (abar : Mat d) (hS : (symmPart abar).PosDef),
      (roundedReferenceMatrixAtGeneration l abar hS).PosDef ∧
      IsEllipticMatrix (1 - eps) (1 + eps)
        (roundedReferenceMatrixAtGeneration l abar hS) ∧
      ‖roundedReferenceMatrixAtGeneration l abar hS - 1‖ ≤ eps

/-- Consumer surface for a rounded reference whose generation is selected
after the identity constant. -/
@[expose]
def PrintOrderRoundedReferenceDualRegularityAtGeneration
    (d : ℕ) [NeZero d] (g : ℝ) (l : ℤ) : Prop :=
  ∃ Cdual : ℝ, 0 ≤ Cdual ∧
    ∀ (abar : Mat d) (hS : (symmPart abar).PosDef) (m : ℤ)
      {w F : Vec d → Vec d},
      MemVectorL2 (cubeSet (originCube d m)) F →
      IsPotentialZeroTraceOn (cubeSet (originCube d m)) w →
      IsSolenoidalOn (cubeSet (originCube d m)) (fun x ↦
        matVecMul (roundedReferenceMatrixAtGeneration l abar hS) (w x) + F x) →
      cubeScaleNormalizedDualNegativeBesovVectorNormTwo
          (originCube d m) (printCertificateOrder g) (fun x ↦
            matVecMul (roundedReferenceMatrixAtGeneration l abar hS) (w x)) ≤
        Cdual * cubeScaleNormalizedDualNegativeBesovVectorNormTwo
          (originCube d m) (printCertificateOrder g) F ∧
      cubeScaleNormalizedDualNegativeBesovVectorNormTwo
          (originCube d m) (printCertificateOrder g) (fun x ↦
            matVecMul (roundedReferenceMatrixAtGeneration l abar hS) (w x) + F x) ≤
        Cdual * cubeScaleNormalizedDualNegativeBesovVectorNormTwo
          (originCube d m) (printCertificateOrder g) F

end

end HighContrast
end HCPolySupport
