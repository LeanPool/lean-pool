/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.NormalizedResponseExcess
public import LeanPool.HighContrastHomogenization.Provider.PortableHistory.MajorizationSize
public import LeanPool.HighContrastHomogenization.Provider.Quenched.StoppingRadiusCellExcess
public import LeanPool.HighContrastHomogenization.Provider.Response.CoefficientBridge
public import LeanPool.HighContrastHomogenization.Provider.Response.ReferenceWeakBridge
public import LeanPool.HighContrastHomogenization.Support.CoarseGraining.CoarseBounds.Sandwich

/-!
# High-contrast homogenization: Provider.PolynomialHomogenization.BlockExcessHomogenizationError

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# HCPolySupport error controlled by a row of block excesses

The normalized response on a cube is bounded by the excess of its coarse block
over a fixed constant comparison block.  Descendants of an origin cube are
reindexed by standard-cell labels.  A coefficient-space sample also has a
single finite excess bound valid on every standard cell inside a prescribed
bounded window; later weighted-row arguments may therefore establish genuine
summability without choosing samplewise ellipticity constants as public data.
The window is supplied by the containment of a standard cell of scale at most
`M`, centred in the centered cube of scale `M`, in the centered cube of scale
`M + 1`.
-/

namespace HCPolySupport
namespace HighContrast

open Book.Ch02
open scoped MatrixOrder

noncomputable section

variable {d : ℕ}

/-- Descendants of an origin cube at a fixed depth are exactly the standard
cells whose centres lie in that origin cube. -/
theorem maxDescendantNormalizedBlockResponseAtScale_originCube_eq_alignedIndex
    [NeZero d] (m : ℤ) (n : ℕ) (aL : TriadicCoeffFamily d) (abar : Mat d) :
    Book.Ch02.maxDescendantNormalizedBlockResponseAtScale
        (originCube d m) (m - (n : ℤ)) aL abar =
      Book.Ch02.finsetSupReal (Response.alignedIndex (1 : Mat d) (m - (n : ℤ)) m)
        (fun w ↦ Book.Ch02.normalizedBlockResponseMax
          (translateCube w (originCube d (m - (n : ℤ)))) aL abar) := by
  classical
  have hscale : m - (n : ℤ) ≤ m := by omega
  unfold Book.Ch02.maxDescendantNormalizedBlockResponseAtScale
  rw [descendantsAtScale_eq_descendantsAtDepth (originCube d m) hscale]
  have hdepth :
      Int.toNat ((originCube d m).scale - (m - (n : ℤ))) = n := by
    simp only [originCube]
    omega
  rw [hdepth, ← Response.image_translateCube_alignedIndex_one_eq_descendantsAtDepth d m n]
  exact Book.Ch02.finsetSupReal_image _ _ _ _ (fun _ _ ↦ rfl)

private theorem isSymmetricBlockMat_blockDiag_smul_one
    (c₁ c₂ : ℝ) :
    IsSymmetricBlockMat
      (blockDiag (c₁ • (1 : Mat d)) (c₂ • (1 : Mat d))) := by
  intro α β
  cases α <;> cases β <;>
    simp [blockMatEntry, blockDiag, Matrix.one_apply, eq_comm]

/-- The constant competitor bounds doubled `mu` on every Chapter 2 domain by
the pointwise ellipticity upper form. -/
private theorem doubledMu_le_plainUpper_of_isEllipticFieldOn
    [NeZero d] (U : Domain d) (b : CoeffOn U) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (U : Set (Vec d)) b.toCoeffField)
    (P : BlockVec d) :
    doubledMu U b P ≤
      (1 / 2 : ℝ) *
        ((Lam + 2 * lam⁻¹ * Lam ^ 2) * vecNormSq P.1 +
          (2 * lam⁻¹) * vecNormSq P.2) := by
  classical
  rw [doubledMu_eq_Mu]
  let X₀ : BlockState d :=
    { potential := fun _ ↦ P.1
      flux := fun _ ↦ P.2 }
  have hAdm : IsBlockMuAdmissible (U : Set (Vec d)) P X₀ := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · have hz : (fun x ↦ X₀.potential x - P.1) = (0 : Vec d → Vec d) := by
        funext x
        simp [X₀]
      rw [hz]
      exact MeasureTheory.MemLp.zero
    · have hz : (fun x ↦ X₀.potential x - P.1) = (0 : Vec d → Vec d) := by
        funext x
        simp [X₀]
      rw [hz]
      exact isPotentialZeroTraceOn_zero
    · have hz : (fun x ↦ X₀.flux x - P.2) = (0 : Vec d → Vec d) := by
        funext x
        simp [X₀]
      rw [hz]
      exact MeasureTheory.MemLp.zero
    · have hz : (fun x ↦ X₀.flux x - P.2) = (0 : Vec d → Vec d) := by
        funext x
        simp [X₀]
      rw [hz]
      exact isSolenoidalZeroNormalTraceOn_zero
  have hBddBelow : BddBelow
      (muValueSet (U : Set (Vec d)) P b.toCoeffField) := by
    refine ⟨0, ?_⟩
    intro r hr
    rcases hr with ⟨Y, _hY, rfl⟩
    refine volumeAverage_nonneg_of_nonneg_on U.measurableSet ?_
    intro x hx
    have hquad :=
      blockMatrixOfCoeff_quadratic_nonneg (hEll.2 x hx) (Y.eval x)
    change 0 ≤ (1 / 2 : ℝ) *
      blockVecDot (Y.eval x)
        (blockMatVecMul (blockMatrixOfCoeff (b.toCoeffField x)) (Y.eval x))
    exact mul_nonneg (by norm_num) hquad
  have hMuLe :
      Mu (U : Set (Vec d)) P b.toCoeffField ≤
        volumeAverage (U : Set (Vec d)) (blockEnergyDensity b.toCoeffField X₀) := by
    unfold Mu
    exact csInf_le hBddBelow (muValueSet_mem hAdm)
  have hEnergyInt :
      MeasureTheory.IntegrableOn (blockEnergyDensity b.toCoeffField X₀)
        (U : Set (Vec d)) :=
    (hAdm.toBlockMuIntegrabilityDataOfIsEllipticFieldOn
      (a := b.toCoeffField) hEll).energyIntegrable
  have hAvgLe :
      volumeAverage (U : Set (Vec d)) (blockEnergyDensity b.toCoeffField X₀) ≤
        (1 / 2 : ℝ) *
          ((Lam + 2 * lam⁻¹ * Lam ^ 2) * vecNormSq P.1 +
            (2 * lam⁻¹) * vecNormSq P.2) := by
    refine volumeAverage_le_of_le_on U.measurableSet hEnergyInt
      (Internal.Ch02.BookCh02.domain_volume_pos U).ne' ?_
    intro x hx
    have hquad :=
      blockMatrixOfCoeff_quadratic_plainUpperBound_of_isEllipticMatrix
        (hEll.2 x hx) P.1 P.2
    have hhalf := mul_le_mul_of_nonneg_left hquad (by norm_num : (0 : ℝ) ≤ 1 / 2)
    simpa [blockEnergyDensity, blockCoeffField, BlockState.eval, X₀] using hhalf
  exact hMuLe.trans hAvgLe

/-- The coarse block is bounded in doubled Loewner order by the same diagonal
form as the constant competitor estimate. -/
private theorem coarseBlockMatrix_blockMatLoewnerLE_plainUpper
    [NeZero d] (U : Domain d) (b : CoeffOn U) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (U : Set (Vec d)) b.toCoeffField) :
    BlockMatLoewnerLE (Book.Ch02.coarseBlockMatrix U b)
      (blockDiag
        ((Lam + 2 * lam⁻¹ * Lam ^ 2) • (1 : Mat d))
        ((2 * lam⁻¹) • (1 : Mat d))) := by
  intro P
  have h := doubledMu_le_plainUpper_of_isEllipticFieldOn U b hEll P
  rw [(doubledMuTheory U b).mu_quadratic] at h
  rw [blockVecDot_blockMatVecMul_blockDiag_smul_one]
  exact h

/-- Every centered triadic cube is bounded. -/
theorem isBounded_centeredCube (d : ℕ) (M : ℤ) :
    Bornology.IsBounded (centeredCube d M) :=
  (isOpenBoundedConvexDomain_openCubeSet
    (originCube d M)).isBoundedDomain.isBounded

/-- A standard cell of scale at most `M` whose centre lies in the centered cube
of scale `M` lies in the centered cube of scale `M + 1`: the cell reaches at most
its own half-width beyond its centre. -/
theorem standardCell_subset_centeredCube_succ {k M : ℤ} {w : Fin d → ℤ}
    (hw : standardCellCenter k w ∈ centeredCube d M) (hkM : k ≤ M) :
    standardCell d k w ⊆ centeredCube d (M + 1) := by
  have hpow : (3 : ℝ) ^ k ≤ (3 : ℝ) ^ M := zpow_le_zpow_right₀ (by norm_num) hkM
  have hM0 : (0 : ℝ) < (3 : ℝ) ^ M := by positivity
  have hsucc : (3 : ℝ) ^ (M + 1) = 3 * (3 : ℝ) ^ M := by
    rw [zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_one]
    ring
  rw [Recurrence.mem_centeredCube_iff] at hw
  intro x hx
  rw [Recurrence.mem_standardCell_iff] at hx
  rw [Recurrence.mem_centeredCube_iff, hsucc]
  intro i
  have hci : standardCellCenter k w i = (3 : ℝ) ^ k * (w i : ℝ) := rfl
  have hlo := (hw i).1
  have hhi := (hw i).2
  rw [hci] at hlo hhi
  exact ⟨by linarith only [hpow, hM0, hlo, (hx i).1],
    by linarith only [hpow, hM0, hhi, (hx i).2]⟩

/-- Every standard-cell excess over a symmetric positive definite comparison
block is nonnegative: the coarse block of a cell is positive semidefinite. -/
theorem standardCell_blockExcess_nonneg [NeZero d] (a : CoeffSpace d)
    {F : BlockMat d} (hF : IsSymmetricBlockMat F) (hFpd : BlockPosDef F)
    (k : ℤ) (w : Fin d → ℤ) :
    0 ≤ blockExcess (coarseBlock (standardCell d k w) a) F := by
  have hU : IsOpenBoundedConvexDomain (standardCell d k w) :=
    isOpenBoundedConvexDomain_openCubeSet _
  have hvol : 0 < (MeasureTheory.volume (standardCell d k w)).toReal := by
    change 0 <
      (MeasureTheory.volume
        (openCubeSet (translateCube w (originCube d k)))).toReal
    rw [volume_openCubeSet_toReal]
    exact cubeVolume_pos _
  have hvol0 : MeasureTheory.volume (standardCell d k w) ≠ 0 := by
    intro hz
    rw [hz] at hvol
    simp at hvol
  exact Response.blockExcess_nonneg (isSymmetricBlockMat_coarseBlock _ a)
    (Transport.posSemidef_toFullBlockMat_coarseBlock hU hvol0 a) hF hFpd

/-- Every standard cell inside one bounded window admits one nonnegative finite
upper bound on its excess.  The bound may depend on the sample, the comparison
matrix and the window, but not on the cell scale or label. -/
theorem exists_uniform_standardCell_blockExcess_bound [NeZero d]
    (a : CoeffSpace d) (abar : Mat d) (habar : (symmPart abar).PosDef)
    {S : Set (Vec d)} (hS : Bornology.IsBounded S) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : ℤ) (w : Fin d → ℤ),
      standardCell d k w ⊆ S →
        blockExcess (coarseBlock (standardCell d k w) a)
          (Book.Ch02.constantBlockMatrix abar) ≤ C := by
  classical
  obtain ⟨f, lam, Lam, hlam, hle, hfm, hell, hblock⟩ :=
    Response.exists_representative a hS
  let c₁ : ℝ := Lam + 2 * lam⁻¹ * Lam ^ 2
  let c₂ : ℝ := 2 * lam⁻¹
  let E : BlockMat d := blockDiag (c₁ • (1 : Mat d)) (c₂ • (1 : Mat d))
  let F : BlockMat d := Book.Ch02.constantBlockMatrix abar
  let C : ℝ := blockSize E F
  have hFsym : IsSymmetricBlockMat F := by
    simpa only [F, Book.Ch02.constantBlockMatrix, blockMatrixOfCoeff] using
      isSymmetricBlockMat_blockMatrixOfCoeff abar
  have hFpd : BlockPosDef F := by
    simpa only [F] using
      blockPosDef_constantBlockMatrix_of_posDef_symmPart habar
  have hEsym : IsSymmetricBlockMat E := by
    exact isSymmetricBlockMat_blockDiag_smul_one c₁ c₂
  have hC : 0 ≤ C := PortableHistory.blockSize_nonneg hEsym hFsym hFpd
  have hEF : BlockMatLoewnerLE E (blockScale C F) := by
    apply blockMatLoewnerLE_of_le
    rw [toFullBlockMat_blockScale]
    exact PortableHistory.blockSize_sandwich hEsym hFsym hFpd |>.1
  refine ⟨C, hC, ?_⟩
  intro k w hsub
  let R : TriadicCube d := translateCube w (originCube d k)
  obtain ⟨b, hf, hlam', hLam', hEll⟩ :=
    Response.exists_coeffOn_of_measurable hlam hle hfm (cubeDomain R)
      fun x hx => hell x (hsub hx)
  have hEllb :
      IsEllipticFieldOn b.lam b.Lam
        (cubeDomain R : Set (Vec d)) b.toCoeffField := by
    simpa [hf, hlam', hLam'] using hEll
  have hcoarse :
      Book.Ch02.coarseBlockMatrix (cubeDomain R) b =
        coarseBlock (standardCell d k w) a := by
    calc
      Book.Ch02.coarseBlockMatrix (cubeDomain R) b =
          coarseBlockMatrix (openCubeSet R) b.toCoeffField :=
        Response.coarseBlockMatrix_eq_of_isEllipticFieldOn (cubeDomain R) b hEllb
      _ = coarseBlockMatrix (openCubeSet R) f := by rw [hf]
      _ = coarseBlock (openCubeSet R) a := (hblock _).symm
      _ = coarseBlock (standardCell d k w) a := by simp [R, standardCell]
  have hupperBook :=
    coarseBlockMatrix_blockMatLoewnerLE_plainUpper (cubeDomain R) b hEllb
  have hupper : BlockMatLoewnerLE
      (coarseBlock (standardCell d k w) a) (blockScale 1 E) := by
    rw [blockScale_one, ← hcoarse]
    simpa [E, c₁, c₂, hlam', hLam'] using hupperBook
  have hU : IsOpenBoundedConvexDomain (standardCell d k w) := by
    simpa [R, standardCell] using isOpenBoundedConvexDomain_openCubeSet R
  have hvol : 0 < (MeasureTheory.volume (standardCell d k w)).toReal := by
    change 0 < (MeasureTheory.volume (openCubeSet R)).toReal
    rw [volume_openCubeSet_toReal]
    exact cubeVolume_pos R
  have hvol0 : MeasureTheory.volume (standardCell d k w) ≠ 0 := by
    intro hz
    rw [hz] at hvol
    simp at hvol
  have hpsd :
      (toFullBlockMat (coarseBlock (standardCell d k w) a)).PosSemidef :=
    Transport.posSemidef_toFullBlockMat_coarseBlock hU hvol0 a
  have hbound := Quenched.blockExcess_le_of_blockMatLoewnerLE
    (isSymmetricBlockMat_coarseBlock _ a) hpsd hFsym hFpd
    (s := 1) (c := C) (by norm_num) hC hupper hEF
  simpa only [F, one_mul] using hbound

end

end HighContrast
end HCPolySupport
