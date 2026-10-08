/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.PrintOrderRoundedGenerationData
public import LeanPool.HighContrastHomogenization.Provider.Regularity.PrintOrderRoundedGenerationResponseRows

/-!
# High-contrast homogenization: Provider.Regularity.PrintOrderParametricRoundedApplication

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Printed-order application at a tolerance-selected rounded generation

The rounded generation is chosen after the identity regularity constant.  The
same generation is then used for the near-identity reference, the physical
coefficient family, and every response row.
-/

namespace HCPolySupport
namespace HighContrast
open MeasureTheory Set
open scoped Matrix Matrix.Norms.L2Operator MatrixOrder

noncomputable section

/-- The private spine keeps the original one-percent geometric window and,
when necessary, refines it further to the absorption tolerance. -/
@[expose]
def printOrderSpineRoundingTolerance (d : ℕ) (Cid : ℝ) : ℝ :=
  min (1 / 100 : ℝ) (printOrderAbsorptionTolerance d Cid)

theorem printOrderSpineRoundingTolerance_pos (d : ℕ) (Cid : ℝ) :
    0 < printOrderSpineRoundingTolerance d Cid := by
  exact lt_min (by norm_num) (printOrderAbsorptionTolerance_pos d Cid)

theorem printOrderSpineRoundingTolerance_le_absorption
    (d : ℕ) (Cid : ℝ) :
    printOrderSpineRoundingTolerance d Cid ≤
      printOrderAbsorptionTolerance d Cid :=
  min_le_right _ _

theorem printOrderSpineRoundingTolerance_le_one_percent
    (d : ℕ) (Cid : ℝ) :
    printOrderSpineRoundingTolerance d Cid ≤ (1 / 100 : ℝ) :=
  min_le_left _ _

theorem printOrderSpineRoundingTolerance_le_half
    (d : ℕ) (Cid : ℝ) :
    printOrderSpineRoundingTolerance d Cid ≤ (1 / 2 : ℝ) :=
  (printOrderSpineRoundingTolerance_le_one_percent d Cid).trans (by norm_num)

theorem printOrderRoundedReferenceDualRegularityAtGeneration_of_absorption
    (d : ℕ) (g Cid : ℝ) (hg : g ∈ Ico (0 : ℝ) 1)
    (hidentity : PrintOrderIdentityCubeDualRegularityWithConstant d g Cid)
    {generation : ℤ}
    (hmatrix : ∀ (abar : Mat d) (hS : (symmPart abar).PosDef),
      (roundedReferenceMatrixAtGeneration generation abar hS).PosDef ∧
      IsEllipticMatrix
        (1 - printOrderAbsorptionTolerance d Cid)
        (1 + printOrderAbsorptionTolerance d Cid)
        (roundedReferenceMatrixAtGeneration generation abar hS) ∧
      ‖roundedReferenceMatrixAtGeneration generation abar hS - 1‖ ≤
        printOrderAbsorptionTolerance d Cid) :
    PrintOrderRoundedReferenceDualRegularityAtGeneration d g generation := by
  let B : ℝ := (d : ℝ) ^ 2 * 2
  let Cgrad : ℝ := B * (2 * Cid)
  let Cflux : ℝ := 2 * Cid
  let Cdual : ℝ := max Cgrad Cflux
  have hCid : 0 ≤ Cid := hidentity.1
  have hB : 0 ≤ B := mul_nonneg (sq_nonneg _) (by norm_num)
  have hCflux : 0 ≤ Cflux := by
    dsimp only [Cflux]
    positivity
  refine ⟨Cdual, hCflux.trans (le_max_right Cgrad Cflux), ?_⟩
  intro abar hS m w F hF hw hsol
  let A : Mat d := roundedReferenceMatrixAtGeneration generation abar hS
  have hproperties := hmatrix abar hS
  have heps : printOrderAbsorptionTolerance d Cid ≤ 1 / 2 :=
    printOrderAbsorptionTolerance_le_half d Cid
  have hAexact : IsEllipticMatrix
      (1 - printOrderAbsorptionTolerance d Cid)
      (1 + printOrderAbsorptionTolerance d Cid) A := by
    simpa only [A] using hproperties.2.1
  have hAell : IsEllipticMatrix (1 / 2 : ℝ) 2 A := by
    exact hAexact.mono (by norm_num)
      (by linarith only [heps]) (by linarith only [heps])
  have hAaction : dualBesovMatrixActionSize A ≤ B := by
    simpa only [A, B] using
      dualBesovMatrixActionSize_le_dim_sq_mul_ellipticity hAell
  have hdefect : ‖A - 1‖ ≤ printOrderAbsorptionTolerance d Cid := by
    simpa only [A] using hproperties.2.2
  have hsmall :
      Cid * dualBesovMatrixActionSize (A - 1) ≤ 1 / 2 := by
    exact identityActionSmallness_of_opNorm_defect hCid
      (printOrderAbsorptionTolerance_smallness d Cid) hdefect
  have hb := printOrder_dual_bounds_of_identity_of_action_absorption
    hg hidentity hAaction hB hsmall (originCube d m) hF hw (by
      simpa only [A] using hsol)
  constructor
  · calc
      cubeScaleNormalizedDualNegativeBesovVectorNormTwo
          (originCube d m) (printCertificateOrder g) (fun x ↦
            matVecMul
              (roundedReferenceMatrixAtGeneration generation abar hS)
              (w x)) ≤
        Cgrad * cubeScaleNormalizedDualNegativeBesovVectorNormTwo
          (originCube d m) (printCertificateOrder g) F := by
            simpa only [A, Cgrad] using hb.1
      _ ≤ Cdual * cubeScaleNormalizedDualNegativeBesovVectorNormTwo
          (originCube d m) (printCertificateOrder g) F :=
        mul_le_mul_of_nonneg_right (le_max_left Cgrad Cflux)
          (cubeScaleNormalizedDualNegativeBesovVectorNormTwo_nonneg
            (originCube d m) (printCertificateOrder g) F)
  · calc
      cubeScaleNormalizedDualNegativeBesovVectorNormTwo
          (originCube d m) (printCertificateOrder g) (fun x ↦
            matVecMul
              (roundedReferenceMatrixAtGeneration generation abar hS)
              (w x) + F x) ≤
        Cflux * cubeScaleNormalizedDualNegativeBesovVectorNormTwo
          (originCube d m) (printCertificateOrder g) F := by
            simpa only [A, Cflux] using hb.2
      _ ≤ Cdual * cubeScaleNormalizedDualNegativeBesovVectorNormTwo
          (originCube d m) (printCertificateOrder g) F :=
        mul_le_mul_of_nonneg_right (le_max_right Cgrad Cflux)
          (cubeScaleNormalizedDualNegativeBesovVectorNormTwo_nonneg
            (originCube d m) (printCertificateOrder g) F)

/-- The complete rounded application at the generation selected by the
absorption tolerance. -/
structure PrintOrderParametricRoundedCoefficientApplication
    (d : ℕ) [NeZero d] (g : ℝ) (a : CoeffSpace d) (abar : Mat d)
    (sourceAmplitude target kappa Cid : ℝ) (X : CoeffSpace d → ℝ) where
  /-- Admissible rounding generation selected for the prescribed absorption tolerance. -/
  generation : ℤ
  generation_admissible : (kZero d : ℤ) ≤ generation
  hS : (symmPart abar).PosDef
  reference_posDef :
    (roundedReferenceMatrixAtGeneration generation abar hS).PosDef
  reference_posDef_all :
    ∀ (abar' : Mat d) (hS' : (symmPart abar').PosDef),
      (roundedReferenceMatrixAtGeneration generation abar' hS').PosDef
  reference_sharp_elliptic_all :
    ∀ (abar' : Mat d) (hS' : (symmPart abar').PosDef),
      IsEllipticMatrix (99 / 100 : ℝ) (101 / 100 : ℝ)
        (roundedReferenceMatrixAtGeneration generation abar' hS')
  reference_lower_all :
    ∀ (abar' : Mat d) (hS' : (symmPart abar').PosDef),
      (99 / 100 : ℝ) • (1 : Mat d) ≤
        roundedReferenceMatrixAtGeneration generation abar' hS'
  reference_upper_all :
    ∀ (abar' : Mat d) (hS' : (symmPart abar').PosDef),
      roundedReferenceMatrixAtGeneration generation abar' hS' ≤
        (101 / 100 : ℝ) • (1 : Mat d)
  reference_elliptic :
    IsEllipticMatrix (1 / 2 : ℝ) 2
      (roundedReferenceMatrixAtGeneration generation abar hS)
  reference_defect :
    ‖roundedReferenceMatrixAtGeneration generation abar hS - 1‖ ≤
      printOrderAbsorptionTolerance d Cid
  dualRegularity :
    PrintOrderRoundedReferenceDualRegularityAtGeneration d g generation
  commonCertificate :
    PrintOrderQuantitativeNormalizedReferenceCertificate abar g target kappa
      (printOrderCommonQuantitativeAffineScale
        d g sourceAmplitude target kappa abar X a) a
  goodMax :
    ∀ m : ℤ,
      (Quenched.triadicCeilingIndex
        (printOrderCommonQuantitativeAffineScale
          d g sourceAmplitude target kappa abar X a) : ℤ) ≤ m →
      RoundedGenerationSpatialGoodMaxOnInterval generation a abar hS
        (printCertificateOrder g)
        (target / (1 - (3 : ℝ) ^ (-kappa)))
        (Quenched.triadicCeilingIndex
          (printOrderCommonQuantitativeAffineScale
            d g sourceAmplitude target kappa abar X a) : ℤ) m
  goodTail :
    RoundedGenerationSpatialGoodTail generation a abar hS
      (printCertificateOrder g)
      (target / (1 - (3 : ℝ) ^ (-kappa)))
      (Quenched.triadicCeilingIndex
        (printOrderCommonQuantitativeAffineScale
          d g sourceAmplitude target kappa abar X a) : ℤ)
  /-- Triadic coefficient family realizing the centered coefficient rounded at `generation`. -/
  aRounded : Book.Ch03.CoeffFamily d
  aRounded_eq :
    ∀ Q : TriadicCube d,
      (aRounded.coeffOn Q).toCoeffField =
        (⇑(roundedCenteredCoeffSpaceAtGeneration
          generation generation_admissible abar hS a).1 : CoeffField d)
  aRounded_ae :
    ∀ Q : TriadicCube d,
      (aRounded.coeffOn Q).toCoeffField =ᵐ[volume]
        roundedCenteredCoefficientAtGeneration
          generation generation_admissible abar hS (⇑a.1)

end

end HighContrast
end HCPolySupport
