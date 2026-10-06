/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.PrintOrderParametricFiniteRecurrence

/-!
# High-contrast homogenization: Provider.Regularity.PrintOrderToleranceSelectedRoundedSpine

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# One rounded generation selected from the absorption tolerance

The generation is selected after the identity estimate and before any
coefficient sample or target amplitude.  All later applications therefore
use the same deterministic geometry.
-/

namespace HCPolySupport
namespace HighContrast
open MeasureTheory Set
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

noncomputable section

theorem sharp_order_bounds_of_selected_defect
    {d : ℕ} {A : Mat d} (hA : A.PosDef)
    (hdefect : ‖A - 1‖ ≤ (1 / 100 : ℝ)) :
    (99 / 100 : ℝ) • (1 : Mat d) ≤ A ∧
      A ≤ (101 / 100 : ℝ) • (1 : Mat d) := by
  have hherm : (A - 1)ᴴ = A - 1 :=
    Matrix.IsHermitian.eq
      (hA.isHermitian.sub Matrix.PosSemidef.one.isHermitian)
  obtain ⟨hupper, hlower⟩ := PortableHistory.sandwich_of_norm_le hherm hdefect
  constructor
  · calc
      (99 / 100 : ℝ) • (1 : Mat d) =
          (-(1 / 100 : ℝ)) • (1 : Mat d) + 1 := by module
      _ ≤ (A - 1) + 1 := by
        simpa only [add_comm] using add_le_add_right hlower 1
      _ = A := by abel
  · calc
      A = (A - 1) + 1 := by abel
      _ ≤ (1 / 100 : ℝ) • (1 : Mat d) + 1 := by
        simpa only [add_comm] using add_le_add_right hupper 1
      _ = (101 / 100 : ℝ) • (1 : Mat d) := by module

/-- Uniform data of the generation chosen at the private spine tolerance. -/
structure PrintOrderToleranceSelectedRoundedSpine
    (d : ℕ) [NeZero d] (Cid : ℝ) where
  generation : ℤ
  admissible : (kZero d : ℤ) ≤ generation
  fine : ∀ (abar : Mat d) (hS : (symmPart abar).PosDef),
    (roundedReferenceMatrixAtGeneration generation abar hS).PosDef ∧
      IsEllipticMatrix
        (1 - printOrderSpineRoundingTolerance d Cid)
        (1 + printOrderSpineRoundingTolerance d Cid)
        (roundedReferenceMatrixAtGeneration generation abar hS) ∧
      ‖roundedReferenceMatrixAtGeneration generation abar hS - 1‖ ≤
        printOrderSpineRoundingTolerance d Cid

namespace PrintOrderToleranceSelectedRoundedSpine

variable {d : ℕ} [NeZero d] {Cid : ℝ}

/-- The selected matrices satisfy the exact absorption window. -/
theorem absorptionProperties
    (spine : PrintOrderToleranceSelectedRoundedSpine d Cid) :
    ∀ (abar : Mat d) (hS : (symmPart abar).PosDef),
      (roundedReferenceMatrixAtGeneration spine.generation abar hS).PosDef ∧
      IsEllipticMatrix
        (1 - printOrderAbsorptionTolerance d Cid)
        (1 + printOrderAbsorptionTolerance d Cid)
        (roundedReferenceMatrixAtGeneration spine.generation abar hS) ∧
      ‖roundedReferenceMatrixAtGeneration spine.generation abar hS - 1‖ ≤
        printOrderAbsorptionTolerance d Cid := by
  intro abar hS
  have hfine := spine.fine abar hS
  have hle := printOrderSpineRoundingTolerance_le_absorption d Cid
  refine ⟨hfine.1, ?_, hfine.2.2.trans hle⟩
  exact hfine.2.1.mono
    (by
      have hhalf := printOrderAbsorptionTolerance_le_half d Cid
      linarith only [hhalf])
    (by linarith only [hle]) (by linarith only [hle])

/-- The selected generation as the common deterministic geometry. -/
@[expose]
def geometry
    (spine : PrintOrderToleranceSelectedRoundedSpine d Cid) :
    RoundedGenerationAnalyticGeometry d where
  generation := spine.generation
  admissible := spine.admissible
  reference_posDef := fun abar hS ↦ (spine.fine abar hS).1
  reference_elliptic := fun abar hS ↦ by
    have hfine := spine.fine abar hS
    have hle := printOrderSpineRoundingTolerance_le_one_percent d Cid
    exact hfine.2.1.mono (by norm_num)
      (by linarith only [hle]) (by linarith only [hle])
  reference_lower := fun abar hS ↦
    (sharp_order_bounds_of_selected_defect (spine.fine abar hS).1
      ((spine.fine abar hS).2.2.trans
        (printOrderSpineRoundingTolerance_le_one_percent d Cid))).1
  reference_upper := fun abar hS ↦
    (sharp_order_bounds_of_selected_defect (spine.fine abar hS).1
      ((spine.fine abar hS).2.2.trans
        (printOrderSpineRoundingTolerance_le_one_percent d Cid))).2

end PrintOrderToleranceSelectedRoundedSpine

/-- The tolerance constructor supplies one uniform selected generation. -/
theorem nonempty_printOrderToleranceSelectedRoundedSpine
    (d : ℕ) [NeZero d] (Cid : ℝ) :
    Nonempty (PrintOrderToleranceSelectedRoundedSpine d Cid) := by
  obtain ⟨generation, admissible, fine⟩ :=
    exists_printOrderRoundedReferenceConstructorAtTolerance d
      (printOrderSpineRoundingTolerance_pos d Cid)
      (printOrderSpineRoundingTolerance_le_half d Cid)
  exact ⟨⟨generation, admissible, fine⟩⟩

/-- A certificate is applied at a previously selected rounded generation,
with the generation equality retained for downstream consumers. -/
theorem PrintOrderQuantitativeNormalizedReferenceCertificate.exists_applicationAtSelectedSpine
    {d : ℕ} [NeZero d] {g : ℝ} {a : CoeffSpace d} {abar : Mat d}
    {sourceAmplitude target kappa Cid : ℝ} {X : CoeffSpace d → ℝ}
    (h : PrintOrderQuantitativeNormalizedReferenceCertificate
      abar g sourceAmplitude kappa (X a) a)
    (spine : PrintOrderToleranceSelectedRoundedSpine d Cid)
    (hg : g ∈ Ico (0 : ℝ) 1) (hTarget : 0 < target)
    (hidentity : PrintOrderIdentityCubeDualRegularityWithConstant d g Cid) :
    ∃ application : PrintOrderParametricRoundedCoefficientApplication
        d g a abar sourceAmplitude target kappa Cid X,
      application.generation = spine.generation := by
  let geom := spine.geometry
  have hmatrix := spine.absorptionProperties
  obtain ⟨hS, hTail⟩ :=
    h.exists_roundedGenerationSpatialGoodTail spine.admissible hg hTarget
  have hGood : ∀ m : ℤ,
      (Quenched.triadicCeilingIndex
        (printOrderCommonQuantitativeAffineScale
          d g sourceAmplitude target kappa abar X a) : ℤ) ≤ m →
      RoundedGenerationSpatialGoodMaxOnInterval spine.generation a abar hS
        (printCertificateOrder g)
        (target / (1 - (3 : ℝ) ^ (-kappa)))
        (Quenched.triadicCeilingIndex
          (printOrderCommonQuantitativeAffineScale
            d g sourceAmplitude target kappa abar X a) : ℤ) m := by
    intro m hm
    exact hTail.goodMaxOnInterval hm
  have hproperties := hmatrix abar hS
  have heps : printOrderAbsorptionTolerance d Cid ≤ 1 / 2 :=
    printOrderAbsorptionTolerance_le_half d Cid
  have hEll : IsEllipticMatrix (1 / 2 : ℝ) 2
      (roundedReferenceMatrixAtGeneration spine.generation abar hS) := by
    exact hproperties.2.1.mono (by norm_num)
      (by linarith only [heps]) (by linarith only [heps])
  have hdual : PrintOrderRoundedReferenceDualRegularityAtGeneration
      d g spine.generation :=
    printOrderRoundedReferenceDualRegularityAtGeneration_of_absorption
      d g Cid hg hidentity hmatrix
  have hCommon : PrintOrderQuantitativeNormalizedReferenceCertificate
      abar g target kappa
        (printOrderCommonQuantitativeAffineScale
          d g sourceAmplitude target kappa abar X a) a := by
    simpa only [printOrderCommonQuantitativeAffineScale] using
      (h.commonAffineScale
        (Caff := printOrderRoundedResponseAffineConstant d g)
        (overlinePi :=
          specBound (symmPart abar) * specBound (symmPart abar)⁻¹)
        (kappaCube := kappa) hTarget)
  obtain ⟨aRounded, hRounded, hRoundedAE⟩ :=
    exists_roundedCenteredCoeffFamilyAtGeneration
      spine.generation spine.admissible abar hS a
  refine ⟨⟨spine.generation, spine.admissible, hS, hproperties.1,
    (fun abar' hS' ↦ (hmatrix abar' hS').1),
    geom.reference_elliptic, geom.reference_lower, geom.reference_upper,
    hEll, hproperties.2.2, hdual, hCommon, hGood, hTail,
    aRounded, hRounded, hRoundedAE⟩, rfl⟩

/-- Generation-preserving selected join for terminal assembly. -/
theorem PrintOrderQuantitativeNormalizedReferenceCertificate.exists_joinAtSelectedSpine
    {d : ℕ} [NeZero d] {g : ℝ} {a : CoeffSpace d} {abar : Mat d}
    {sourceAmplitude target kappa Cid : ℝ} {X : CoeffSpace d → ℝ}
    (h : PrintOrderQuantitativeNormalizedReferenceCertificate
      abar g sourceAmplitude kappa (X a) a)
    (spine : PrintOrderToleranceSelectedRoundedSpine d Cid)
    (hg : g ∈ Ico (0 : ℝ) 1) (hTarget : 0 < target)
    (hidentity : PrintOrderIdentityCubeDualRegularityWithConstant d g Cid) :
    ∃ join : PrintOrderParametricRoundedResponseJoin
        d g a abar sourceAmplitude target kappa Cid X,
      join.application.generation = spine.generation := by
  obtain ⟨application, hgeneration⟩ :=
    h.exists_applicationAtSelectedSpine spine hg hTarget hidentity
  exact ⟨⟨application, privateRoundedPhysicalDirichletSpine d, rfl,
    privateRoundedOrder_lt_printCertificateOrder d hg⟩, hgeneration⟩

end

end HighContrast
end HCPolySupport
