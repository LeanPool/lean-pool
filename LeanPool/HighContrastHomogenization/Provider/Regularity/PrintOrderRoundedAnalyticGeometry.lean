/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.PrintOrderParametricRoundedApplication

/-!
# High-contrast homogenization: Provider.Regularity.PrintOrderRoundedAnalyticGeometry

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Analytic geometry of a selected rounded generation

This carrier exposes the same constant-matrix and harmonic-replacement API
used by the finite regularity proof, with the rounded generation explicit.
-/

namespace HCPolySupport
namespace HighContrast
open MeasureTheory
open scoped Matrix.Norms.L2Operator MatrixOrder

noncomputable section

/-- Uniform deterministic geometry attached to one admissible rounded
generation. -/
structure RoundedGenerationAnalyticGeometry (d : ℕ) [NeZero d] where
  /-- Admissible generation at which the reference matrices and deterministic geometry are
  rounded. -/
  generation : ℤ
  admissible : (kZero d : ℤ) ≤ generation
  reference_posDef :
    ∀ (abar : Mat d) (hS : (symmPart abar).PosDef),
      (roundedReferenceMatrixAtGeneration generation abar hS).PosDef
  reference_elliptic :
    ∀ (abar : Mat d) (hS : (symmPart abar).PosDef),
      IsEllipticMatrix (99 / 100 : ℝ) (101 / 100 : ℝ)
        (roundedReferenceMatrixAtGeneration generation abar hS)
  reference_lower :
    ∀ (abar : Mat d) (hS : (symmPart abar).PosDef),
      (99 / 100 : ℝ) • (1 : Mat d) ≤
        roundedReferenceMatrixAtGeneration generation abar hS
  reference_upper :
    ∀ (abar : Mat d) (hS : (symmPart abar).PosDef),
      roundedReferenceMatrixAtGeneration generation abar hS ≤
        (101 / 100 : ℝ) • (1 : Mat d)

namespace RoundedGenerationAnalyticGeometry

variable {d : ℕ} [NeZero d]

/-- The selected rounded coordinate matrix. -/
@[expose]
def grid (geom : RoundedGenerationAnalyticGeometry d) (m : Mat d) : Mat d :=
  roundedGrid geom.generation m

theorem grid_posDef (geom : RoundedGenerationAnalyticGeometry d)
    {m : Mat d} (hm : m.PosDef) : (geom.grid m).PosDef := by
  exact Recurrence.posDef_roundedGrid geom.admissible hm

theorem grid_transpose (geom : RoundedGenerationAnalyticGeometry d)
    {m : Mat d} (hm : m.PosDef) :
    matTranspose (geom.grid m) = geom.grid m := by
  ext i j
  exact Recurrence.roundedGrid_symm geom.generation hm.posSemidef i j

theorem grid_det_isUnit (geom : RoundedGenerationAnalyticGeometry d)
    {m : Mat d} (hm : m.PosDef) : IsUnit (geom.grid m).det :=
  isUnit_det_of_posDef (geom.grid_posDef hm)

/-- The constant selected-generation reference matrix. -/
@[expose]
def referenceMatrix (geom : RoundedGenerationAnalyticGeometry d)
    (abar : Mat d) (hS : (symmPart abar).PosDef) : Mat d :=
  roundedReferenceMatrixAtGeneration geom.generation abar hS

/-- The selected normalized coefficient carrier. -/
@[expose]
def centeredCoeffSpace (geom : RoundedGenerationAnalyticGeometry d)
    (abar : Mat d) (hS : (symmPart abar).PosDef) (a : CoeffSpace d) :
    CoeffSpace d :=
  roundedCenteredCoeffSpaceAtGeneration
    geom.generation geom.admissible abar hS a

/-- The selected physical response maximum. -/
@[expose]
def responseMax (geom : RoundedGenerationAnalyticGeometry d)
    (a : CoeffSpace d) (abar : Mat d) (hS : (symmPart abar).PosDef)
    (k : ℤ) (w : Fin d → ℤ) : ℝ :=
  roundedNormalizedDoubledResponseMaxAtGeneration
    geom.generation a abar hS k w

/-- The selected full weak-error row. -/
@[expose]
def spatialWeakError (geom : RoundedGenerationAnalyticGeometry d)
    (a : CoeffSpace d) (abar : Mat d) (hS : (symmPart abar).PosDef)
    (s : ℝ) (m : ℤ) : ℝ :=
  roundedGenerationSpatialWeakError geom.generation a abar hS s m

theorem spatialWeakError_nonneg (geom : RoundedGenerationAnalyticGeometry d)
    (a : CoeffSpace d) (abar : Mat d) (hS : (symmPart abar).PosDef)
    (s : ℝ) (m : ℤ) : 0 ≤ geom.spatialWeakError a abar hS s m := by
  exact roundedGenerationSpatialWeakError_nonneg
    geom.generation a abar hS s m

theorem reference_coarse_elliptic
    (geom : RoundedGenerationAnalyticGeometry d)
    (abar : Mat d) (hS : (symmPart abar).PosDef) :
    IsEllipticMatrix (1 / 2 : ℝ) 2 (geom.referenceMatrix abar hS) := by
  exact (geom.reference_elliptic abar hS).mono
    (by norm_num) (by norm_num) (by norm_num)

/-- The selected reference in the Chapter 3 constant-matrix carrier. -/
@[expose]
def referenceConstantCoeffMatrix
    (geom : RoundedGenerationAnalyticGeometry d)
    (abar : Mat d) (hS : (symmPart abar).PosDef) :
    Book.Ch03.ConstantCoeffMatrix d :=
  roundedReferenceConstantCoeffMatrixAtGeneration geom.generation abar hS
    (geom.reference_posDef abar hS) (geom.reference_coarse_elliptic abar hS)

@[simp] theorem referenceConstantCoeffMatrix_matrix
    (geom : RoundedGenerationAnalyticGeometry d)
    (abar : Mat d) (hS : (symmPart abar).PosDef) :
    (geom.referenceConstantCoeffMatrix abar hS).matrix =
      geom.referenceMatrix abar hS :=
  rfl

/-- The same-trace harmonic replacement for the selected reference. -/
@[expose]
def harmonicReplacementDatum (geom : RoundedGenerationAnalyticGeometry d)
    (abar : Mat d) (hS : (symmPart abar).PosDef)
    (a : Book.Ch03.CoeffFamily d) (m : ℤ)
    (u : H1Function (Book.Ch02.cubeDomain (originCube d m) : Set (Vec d)))
    (hu : IsWeakSolutionOn (a.coeffOn (originCube d m)).toCoeffField
      (Book.Ch02.cubeDomain (originCube d m) : Set (Vec d)) u.grad) :=
  roundedHarmonicReplacementDatumAtGeneration geom.generation abar hS
    (geom.reference_posDef abar hS) (geom.reference_coarse_elliptic abar hS)
    a m u hu

@[simp] theorem harmonicReplacementDatum_u
    (geom : RoundedGenerationAnalyticGeometry d)
    (abar : Mat d) (hS : (symmPart abar).PosDef)
    (a : Book.Ch03.CoeffFamily d) (m : ℤ)
    (u : H1Function (Book.Ch02.cubeDomain (originCube d m) : Set (Vec d)))
    (hu : IsWeakSolutionOn (a.coeffOn (originCube d m)).toCoeffField
      (Book.Ch02.cubeDomain (originCube d m) : Set (Vec d)) u.grad) :
    (geom.harmonicReplacementDatum abar hS a m u hu).u = u := by
  exact roundedHarmonicReplacementDatumAtGeneration_u geom.generation abar hS
    (geom.reference_posDef abar hS) (geom.reference_coarse_elliptic abar hS)
    a m u hu

/-- The geometry extracted from a parametric rounded application. -/
@[expose]
def ofApplication
    {g : ℝ} {a : CoeffSpace d} {abar : Mat d}
    {sourceAmplitude target kappa Cid : ℝ} {X : CoeffSpace d → ℝ}
    (application : PrintOrderParametricRoundedCoefficientApplication
      d g a abar sourceAmplitude target kappa Cid X) :
    RoundedGenerationAnalyticGeometry d where
  generation := application.generation
  admissible := application.generation_admissible
  reference_posDef := application.reference_posDef_all
  reference_elliptic := application.reference_sharp_elliptic_all
  reference_lower := application.reference_lower_all
  reference_upper := application.reference_upper_all

end RoundedGenerationAnalyticGeometry

end

end HighContrast
end HCPolySupport
