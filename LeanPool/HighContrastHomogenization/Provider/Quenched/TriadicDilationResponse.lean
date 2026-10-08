/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Annealed.Measurability
public import LeanPool.HighContrastHomogenization.Geometry.CoarseSchurBridge
public import LeanPool.HighContrastHomogenization.Provider.Quenched.TriadicRebasedLaw
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.Dilation

/-!
# High-contrast homogenization: Provider.Quenched.TriadicDilationResponse

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Coarse-response covariance under triadic dilation

The coarse response of a dilated coefficient sample on a reference cube is the
response of the original sample on the corresponding larger cube.  Passing
this identity through the pushed-forward law gives exact covariance of the
annealed block and its intrinsic contrast.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory

noncomputable section

variable {d : ℕ}

private theorem dilatedCoeffOn_triadicDilation_aeeq (n : ℕ)
    (Q : TriadicCube d) (a : CoeffSpace d) :
    Book.Ch02.CoeffOn.AEEq
      (Book.Ch02.CoeffOn.dilate (n : ℤ)
        ((CoeffSpace.triadicDilation n a).coeffOn (Book.Ch02.cubeDomain Q)))
      (a.coeffOn (Book.Ch02.cubeDomain (Book.Ch02.dilateCube (n : ℤ) Q))) := by
  let r : ℝ := (3 : ℝ) ^ n
  have hr : 0 < r := by positivity
  have hpull :=
    (Measure.quasiMeasurePreserving_smul (volume : Measure (Vec d))
      (inv_ne_zero hr.ne')).tendsto_ae (CoeffSpace.triadicDilation_ae n a)
  have hglobal :
      Book.Ch02.dilateCoeffField (n : ℤ)
          ((CoeffSpace.triadicDilation n a).coeffOn
            (Book.Ch02.cubeDomain Q)).toCoeffField
        =ᵐ[volume]
      (a.coeffOn
        (Book.Ch02.cubeDomain (Book.Ch02.dilateCube (n : ℤ) Q))).toCoeffField := by
    filter_upwards [hpull] with x hx
    change (CoeffSpace.triadicDilation n a).1 (r⁻¹ • x) =
      a.1 (triadicDilateVec n (r⁻¹ • x)) at hx
    change (CoeffSpace.triadicDilation n a).1
      (Book.Ch02.undilateVec (n : ℤ) x) = a.1 x
    have hund : Book.Ch02.undilateVec (n : ℤ) x = r⁻¹ • x := by
      simp [Book.Ch02.undilateVec, Book.Ch02.triadicDilationFactor, r]
    rw [hund, hx]
    congr 1
    change r • (r⁻¹ • x) = x
    rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
  exact
    (Book.Ch02.CoeffOn.dilate_isCubeDilation (n : ℤ)
      ((CoeffSpace.triadicDilation n a).coeffOn
        (Book.Ch02.cubeDomain Q))).coeff_ae_eq.trans
      (ae_restrict_of_ae hglobal)

/-- Pathwise coarse responses commute with triadic dilation of a cube. -/
theorem coarseBlock_triadicDilation (n : ℕ) (Q : TriadicCube d)
    (a : CoeffSpace d) :
    coarseBlock (openCubeSet Q) (CoeffSpace.triadicDilation n a) =
      coarseBlock (openCubeSet (Book.Ch02.dilateCube (n : ℤ) Q)) a := by
  let c := (CoeffSpace.triadicDilation n a).coeffOn (Book.Ch02.cubeDomain Q)
  let b := Book.Ch02.CoeffOn.dilate (n : ℤ) c
  have hCoeff : Book.Ch02.CoeffOn.IsCubeDilation (n : ℤ) c b :=
    Book.Ch02.CoeffOn.dilate_isCubeDilation (n : ℤ) c
  have hba : Book.Ch02.CoeffOn.AEEq b
      (a.coeffOn (Book.Ch02.cubeDomain (Book.Ch02.dilateCube (n : ℤ) Q))) := by
    simpa only [b, c] using dilatedCoeffOn_triadicDilation_aeeq n Q a
  calc
    coarseBlock (openCubeSet Q) (CoeffSpace.triadicDilation n a) =
        Book.Ch02.coarseBlockMatrix (Book.Ch02.cubeDomain Q) c :=
      coarseBlock_eq_coarseBlockMatrix (CoeffSpace.triadicDilation n a)
        (Book.Ch02.cubeDomain Q)
    _ = Book.Ch02.coarseBlockMatrix
        (Book.Ch02.cubeDomain (Book.Ch02.dilateCube (n : ℤ) Q)) b :=
      (Book.Ch02.coarseBlockMatrix_dilate hCoeff).symm
    _ = Book.Ch02.coarseBlockMatrix
        (Book.Ch02.cubeDomain (Book.Ch02.dilateCube (n : ℤ) Q))
          (a.coeffOn
            (Book.Ch02.cubeDomain (Book.Ch02.dilateCube (n : ℤ) Q))) :=
      Book.Ch02.coarseBlockMatrix_eq_ofAEEq hba
    _ = coarseBlock (openCubeSet (Book.Ch02.dilateCube (n : ℤ) Q)) a :=
      (coarseBlock_eq_coarseBlockMatrix a
        (Book.Ch02.cubeDomain (Book.Ch02.dilateCube (n : ℤ) Q))).symm

/-- On standard aligned cells, dilation shifts the integer generation and
preserves the cell label. -/
theorem coarseBlock_standardCell_triadicDilation (n : ℕ) (k : ℤ)
    (w : Fin d → ℤ) (a : CoeffSpace d) :
    coarseBlock (standardCell d k w) (CoeffSpace.triadicDilation n a) =
      coarseBlock (standardCell d ((n : ℤ) + k) w) a := by
  simpa [standardCell, Book.Ch02.dilateCube, translateCube, originCube,
    add_comm] using
    coarseBlock_triadicDilation n (translateCube w (originCube d k)) a

/-- On centered cubes, dilation shifts the integer generation. -/
theorem coarseBlock_centeredCube_triadicDilation (n : ℕ) (k : ℤ)
    (a : CoeffSpace d) :
    coarseBlock (centeredCube d k) (CoeffSpace.triadicDilation n a) =
      coarseBlock (centeredCube d ((n : ℤ) + k)) a := by
  simpa [centeredCube, Book.Ch02.dilateCube, originCube, add_comm] using
    coarseBlock_triadicDilation n (originCube d k) a

/-- Annealed blocks of the rebased law are the original annealed blocks at the
shifted generation. -/
theorem annealedBlock_triadicRebasedLaw (n : ℕ)
    (P : Measure (CoeffSpace d)) (k : ℤ) :
    annealedBlock (triadicRebasedLaw n P) (centeredCube d k) =
      annealedBlock P (centeredCube d ((n : ℤ) + k)) := by
  have hentry : ∀ α β : BlockCoord d,
      blockMatEntry (annealedBlock (triadicRebasedLaw n P) (centeredCube d k)) α β =
        blockMatEntry (annealedBlock P (centeredCube d ((n : ℤ) + k))) α β := by
    intro α β
    rw [blockMatEntry_annealedBlock, blockMatEntry_annealedBlock]
    change (∫ a, blockMatEntry (coarseBlock (centeredCube d k) a) α β
        ∂Measure.map (CoeffSpace.triadicDilation n) P) = _
    rw [integral_map (CoeffSpace.measurable_triadicDilation n).aemeasurable
      (measurable_blockMatEntry_coarseBlock k α β).aestronglyMeasurable]
    exact integral_congr_ae (Filter.Eventually.of_forall fun a =>
      congrArg (fun A => blockMatEntry A α β)
        (coarseBlock_centeredCube_triadicDilation n k a))
  refine blockMat_ext ?_ ?_ ?_ ?_ <;> funext i j
  · exact hentry (Sum.inl i) (Sum.inl j)
  · exact hentry (Sum.inl i) (Sum.inr j)
  · exact hentry (Sum.inr i) (Sum.inl j)
  · exact hentry (Sum.inr i) (Sum.inr j)

/-- The intrinsic annealed contrast has the same generation-shift covariance. -/
theorem annealedContrast_triadicRebasedLaw (n : ℕ)
    (P : Measure (CoeffSpace d)) (k : ℤ) :
    annealedContrast (triadicRebasedLaw n P) k =
      annealedContrast P ((n : ℤ) + k) := by
  rw [annealedContrast, annealedContrast, annealedBlock_triadicRebasedLaw]

end

end HighContrast
end HCPolySupport
