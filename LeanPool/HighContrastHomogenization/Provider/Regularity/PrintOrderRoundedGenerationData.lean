/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.PrintOrderParametricRoundedConstructor
public import LeanPool.HighContrastHomogenization.Provider.Regularity.RoundedCenteredCoeffFamily
public import LeanPool.HighContrastHomogenization.Provider.Regularity.RoundedHarmonicReplacement

/-!
# High-contrast homogenization: Provider.Regularity.PrintOrderRoundedGenerationData

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Coefficient data at a selected rounded generation

The affine coefficient, its constant symmetric reference, and the Chapter 3
coefficient family are packaged using one common admissible generation.
-/

namespace HCPolySupport
namespace HighContrast
open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- The centered physical coefficient pulled back by a selected rounded grid. -/
@[expose]
def roundedCenteredCoefficientAtGeneration [NeZero d]
    (l : ℤ) (hl : (kZero d : ℤ) ≤ l) (abar : Mat d)
    (hS : (symmPart abar).PosDef) (a : CoeffField d) : CoeffField d :=
  affineCoefficient (roundedGrid l (symmPart abar))
    ((Matrix.isUnit_iff_isUnit_det _).mp
      (Recurrence.posDef_roundedGrid hl hS).isUnit)
    (fun x ↦ specBound ((symmPart abar)⁻¹) •
      (a x - skewPart abar))

@[simp] theorem roundedCenteredCoefficientAtGeneration_apply [NeZero d]
    (l : ℤ) (hl : (kZero d : ℤ) ≤ l) (abar : Mat d)
    (hS : (symmPart abar).PosDef) (a : CoeffField d) (y : Vec d) :
    roundedCenteredCoefficientAtGeneration l hl abar hS a y =
      (roundedGrid l (symmPart abar))⁻¹ *
        (specBound ((symmPart abar)⁻¹) •
          (a (matVecMul (roundedGrid l (symmPart abar)) y) -
            skewPart abar)) *
        matTranspose (roundedGrid l (symmPart abar))⁻¹ := by
  rfl

/-- The selected-grid pullback on the qualitative coefficient carrier. -/
@[expose]
def roundedCenteredCoeffSpaceAtGeneration [NeZero d]
    (l : ℤ) (hl : (kZero d : ℤ) ≤ l) (abar : Mat d)
    (hS : (symmPart abar).PosDef) (a : CoeffSpace d) : CoeffSpace d :=
  affinePullbackCoeffSpace (roundedGrid l (symmPart abar))
    ((Matrix.isUnit_iff_isUnit_det _).mp
      (Recurrence.posDef_roundedGrid hl hS).isUnit)
    (normalizedCenteredCoeff a abar hS)

/-- The selected-grid pullback has the literal transformed representative
almost everywhere. -/
theorem roundedCenteredCoeffSpaceAtGeneration_ae [NeZero d]
    (l : ℤ) (hl : (kZero d : ℤ) ≤ l) (abar : Mat d)
    (hS : (symmPart abar).PosDef) (a : CoeffSpace d) :
    (⇑(roundedCenteredCoeffSpaceAtGeneration l hl abar hS a).1 :
        CoeffField d) =ᵐ[volume]
      roundedCenteredCoefficientAtGeneration l hl abar hS (⇑a.1) := by
  let q : Mat d := roundedGrid l (symmPart abar)
  let hQ : IsUnit q.det :=
    (Matrix.isUnit_iff_isUnit_det q).mp (Recurrence.posDef_roundedGrid hl hS).isUnit
  have hpull := affinePullbackCoeffSpace_ae q hQ
    (normalizedCenteredCoeff a abar hS)
  have hcongr := affineCoefficient_congr_ae q hQ
    (normalizedCenteredCoeff_ae a abar hS)
  exact hpull.trans (by
    simpa only [q, hQ, roundedCenteredCoefficientAtGeneration] using hcongr)

/-- The selected rounded sample admits a compatible Chapter 3 family. -/
theorem exists_roundedCenteredCoeffFamilyAtGeneration [NeZero d]
    (l : ℤ) (hl : (kZero d : ℤ) ≤ l) (abar : Mat d)
    (hS : (symmPart abar).PosDef) (a : CoeffSpace d) :
    ∃ aRounded : Book.Ch03.CoeffFamily d,
      (∀ Q : TriadicCube d,
        (aRounded.coeffOn Q).toCoeffField =
          (⇑(roundedCenteredCoeffSpaceAtGeneration l hl abar hS a).1 :
            CoeffField d)) ∧
      ∀ Q : TriadicCube d,
        (aRounded.coeffOn Q).toCoeffField =ᵐ[volume]
          roundedCenteredCoefficientAtGeneration l hl abar hS (⇑a.1) := by
  obtain ⟨aRounded, hRounded⟩ :=
    exists_coeffFamily_of_coeffSpace
      (roundedCenteredCoeffSpaceAtGeneration l hl abar hS a)
  refine ⟨aRounded, hRounded, ?_⟩
  intro Q
  rw [hRounded Q]
  exact roundedCenteredCoeffSpaceAtGeneration_ae l hl abar hS a

/-- A selected near-identity matrix in the Chapter 3 constant-coefficient
carrier, using the uniform one-half/two ellipticity window. -/
@[expose]
def roundedReferenceConstantCoeffMatrixAtGeneration [NeZero d]
    (l : ℤ) (abar : Mat d) (hS : (symmPart abar).PosDef)
    (hPos : (roundedReferenceMatrixAtGeneration l abar hS).PosDef)
    (hEll : IsEllipticMatrix (1 / 2 : ℝ) 2
      (roundedReferenceMatrixAtGeneration l abar hS)) :
    Book.Ch03.ConstantCoeffMatrix d where
  matrix := roundedReferenceMatrixAtGeneration l abar hS
  isSymm := isSymm_of_isHermitian hPos.isHermitian
  lam := 1 / 2
  Lam := 2
  lam_pos := by norm_num
  lam_le_Lam := by norm_num
  elliptic := hEll

/-- The chosen same-trace comparison for any selected rounded reference. -/
@[expose]
def roundedHarmonicReplacementDatumAtGeneration [NeZero d]
    (l : ℤ) (abar : Mat d) (hS : (symmPart abar).PosDef)
    (hPos : (roundedReferenceMatrixAtGeneration l abar hS).PosDef)
    (hEll : IsEllipticMatrix (1 / 2 : ℝ) 2
      (roundedReferenceMatrixAtGeneration l abar hS))
    (a : Book.Ch03.CoeffFamily d) (m : ℤ)
    (u : H1Function (Book.Ch02.cubeDomain (originCube d m) : Set (Vec d)))
    (hu : IsWeakSolutionOn (a.coeffOn (originCube d m)).toCoeffField
      (Book.Ch02.cubeDomain (originCube d m) : Set (Vec d)) u.grad) :
    Book.Ch03.CoarseGrainingComparisonDatum (originCube d m) a
      (roundedReferenceConstantCoeffMatrixAtGeneration
        l abar hS hPos hEll) (0 : Vec d → Vec d) :=
  Classical.choose
    (exists_constantCoeffCoarseGrainingComparisonDatum_of_hcWeakSolution
      (roundedReferenceConstantCoeffMatrixAtGeneration
        l abar hS hPos hEll) u hu)

@[simp] theorem roundedHarmonicReplacementDatumAtGeneration_u [NeZero d]
    (l : ℤ) (abar : Mat d) (hS : (symmPart abar).PosDef)
    (hPos : (roundedReferenceMatrixAtGeneration l abar hS).PosDef)
    (hEll : IsEllipticMatrix (1 / 2 : ℝ) 2
      (roundedReferenceMatrixAtGeneration l abar hS))
    (a : Book.Ch03.CoeffFamily d) (m : ℤ)
    (u : H1Function (Book.Ch02.cubeDomain (originCube d m) : Set (Vec d)))
    (hu : IsWeakSolutionOn (a.coeffOn (originCube d m)).toCoeffField
      (Book.Ch02.cubeDomain (originCube d m) : Set (Vec d)) u.grad) :
    (roundedHarmonicReplacementDatumAtGeneration
      l abar hS hPos hEll a m u hu).u = u :=
  Classical.choose_spec
    (exists_constantCoeffCoarseGrainingComparisonDatum_of_hcWeakSolution
      (roundedReferenceConstantCoeffMatrixAtGeneration
        l abar hS hPos hEll) u hu)

end

end HighContrast
end HCPolySupport
