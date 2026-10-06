/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.PreYoungRowPartialDischarge
public import LeanPool.HighContrastHomogenization.Provider.Response.SubcellDoubledResponse

/-!
# High-contrast homogenization: Provider.Response.PreYoungRecentDefectPointwise

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Pointwise recent-defect pairings

The average of the child--parent optimizer difference is controlled by its
half doubled-energy and the appropriate Schur load of the cell response.
-/

namespace HCPolySupport.HighContrast.Response

open Book.Ch02 MeasureTheory

noncomputable section

variable {d : ℕ}

private theorem upper_left_pos_semidef {H : BlockMat d}
    (hsymm : IsSymmetricBlockMat H) (hpos : BlockPosDef H) :
    H.upperLeft.PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · ext i j
    simpa only [Matrix.conjTranspose, RCLike.star_def, Matrix.map_apply,
      Matrix.transpose_apply, conj_trivial, blockMatEntry] using
        hsymm (Sum.inl j) (Sum.inl i)
  · intro x
    by_cases hx : x = 0
    · subst hx
      simp only [Matrix.mulVec_zero, dotProduct_zero, le_rfl]
    · have hX : ((x, 0) : BlockVec d) ≠ 0 := by
        intro hzero
        exact hx (congrArg Prod.fst hzero)
      have hquad := (hpos ((x, 0) : BlockVec d) hX).le
      simpa only [star_trivial, ge_iff_le, blockVecDot, blockMatVecMul,
        matVecMul_zero, add_zero, vecDot_zero_left] using! hquad

/-- The two coordinate pairings of a recent child--parent difference are
controlled by its half doubled-energy and the cell Schur loads. -/
theorem abs_vec_dot_recent_difference_le [NeZero d]
    {q : Mat d} (hq : q.PosDef) {s t : ℤ} (hst : s ≤ t)
    {w : Fin d → ℤ} (hw : w ∈ alignedIndex q s t)
    (a : CoeffSpace d) (p r Pcen Qcen : Vec d) :
    let energy := (1 / 2 : ℝ) * average (adaptedDomainAt hq s w) (fun x ↦
      blockVecDot
        (diagonalWeakChildState hq s w a p r x -
          diagonalWeakState hq t a p r x)
        (blockMatVecMul (blockMatrixOfCoeff ((⇑a.1 : CoeffField d) x))
          (diagonalWeakChildState hq s w a p r x -
            diagonalWeakState hq t a p r x)))
    |vecDot Qcen (blockCellAverage (adaptedCellAt q s w) (fun x ↦
        diagonalWeakChildState hq s w a p r x -
          diagonalWeakState hq t a p r x)).1| ≤
        Real.sqrt (2 * energy) *
          profileSchurLoadFlux (coarseBlock (adaptedCellAt q s w) a) Qcen ∧
      |vecDot Pcen (blockCellAverage (adaptedCellAt q s w) (fun x ↦
        diagonalWeakChildState hq s w a p r x -
          diagonalWeakState hq t a p r x)).2| ≤
        Real.sqrt (2 * energy) *
          profileSchurLoadGradient (coarseBlock (adaptedCellAt q s w) a) Pcen := by
  dsimp only
  let U := adaptedDomainAt hq s w
  let Y : DoubledField d :=
    { potential := fun x ↦
        (diagonalWeakState hq t a p r x -
          diagonalWeakChildState hq s w a p r x).1
      flux := fun x ↦
        (diagonalWeakState hq t a p r x -
          diagonalWeakChildState hq s w a p r x).2 }
  have hY : IsDoubledResponseField U (a.coeffOn U) Y :=
    isDoubledResponseField_diagonalWeakState_sub_childState hq hst hw a p r
  have hsymm := Book.Ch02.isSymmetricBlockMat_coarseBlockMatrix U (a.coeffOn U)
  have hpos := (Book.Ch02.blockCoarseMatrixTheory U
    (a.coeffOn U)).block_matrix_posDef
  have hpot := abs_vecDot_averageVec_potential_coeffSpace_le U a
    (posSemidef_lowerRight hsymm hpos) (isUnit_det_lowerRight hpos) hY Qcen
  have hflux := abs_vecDot_averageVec_flux_coeffSpace_le U a
    (upper_left_pos_semidef hsymm hpos) hY Pcen
  have hpotAverage : Book.Ch02.averageVec U Y.potential =
      -(blockCellAverage (adaptedCellAt q s w) (fun x ↦
        diagonalWeakChildState hq s w a p r x -
          diagonalWeakState hq t a p r x)).1 := by
    funext i
    change average U (fun x ↦
        (diagonalWeakState hq t a p r x -
          diagonalWeakChildState hq s w a p r x).1 i) =
      -average U (fun x ↦
        (diagonalWeakChildState hq s w a p r x -
          diagonalWeakState hq t a p r x).1 i)
    unfold Book.Ch02.average
    rw [show (fun x ↦
        (diagonalWeakState hq t a p r x -
          diagonalWeakChildState hq s w a p r x).1 i) =
        -(fun x ↦
          (diagonalWeakChildState hq s w a p r x -
            diagonalWeakState hq t a p r x).1 i) by
      funext x
      simp]
    rw [MeasureTheory.integral_neg']
    ring
  have hfluxAverage : Book.Ch02.averageVec U Y.flux =
      -(blockCellAverage (adaptedCellAt q s w) (fun x ↦
        diagonalWeakChildState hq s w a p r x -
          diagonalWeakState hq t a p r x)).2 := by
    funext i
    change average U (fun x ↦
        (diagonalWeakState hq t a p r x -
          diagonalWeakChildState hq s w a p r x).2 i) =
      -average U (fun x ↦
        (diagonalWeakChildState hq s w a p r x -
          diagonalWeakState hq t a p r x).2 i)
    unfold Book.Ch02.average
    rw [show (fun x ↦
        (diagonalWeakState hq t a p r x -
          diagonalWeakChildState hq s w a p r x).2 i) =
        -(fun x ↦
          (diagonalWeakChildState hq s w a p r x -
            diagonalWeakState hq t a p r x).2 i) by
      funext x
      simp]
    rw [MeasureTheory.integral_neg']
    ring
  have henergy : Book.Ch02.average U (fun x ↦
      blockVecDot (Y.eval x)
        (blockMatVecMul (blockMatrixField (a.coeffOn U) x) (Y.eval x))) =
      2 * ((1 / 2 : ℝ) * average U (fun x ↦
        blockVecDot
          (diagonalWeakChildState hq s w a p r x -
            diagonalWeakState hq t a p r x)
          (blockMatVecMul (blockMatrixOfCoeff ((⇑a.1 : CoeffField d) x))
            (diagonalWeakChildState hq s w a p r x -
              diagonalWeakState hq t a p r x)))) := by
    obtain ⟨f, hae, hfamily⟩ :=
      CoeffSpace.exists_pointwise_coeffOn_family_aeeq a
    obtain ⟨c, _clam, _cLam, hcf, _hclam, _hcLam, _hcEll, hca⟩ := hfamily U
    have hpoint : Book.Ch02.average U (fun x ↦ blockVecDot (Y.eval x)
        (blockMatVecMul (blockMatrixField (a.coeffOn U) x) (Y.eval x))) =
        Book.Ch02.average U (fun x ↦ blockVecDot
          (diagonalWeakChildState hq s w a p r x -
            diagonalWeakState hq t a p r x)
          (blockMatVecMul (blockMatrixOfCoeff ((⇑a.1 : CoeffField d) x))
            (diagonalWeakChildState hq s w a p r x -
              diagonalWeakState hq t a p r x))) := by
      apply Book.Ch02.average_eq_of_ae_eq
      filter_upwards [hca, ae_restrict_of_ae hae] with x hxca hx
      change blockVecDot (Y.eval x)
          (blockMatVecMul
            (blockMatrixOfCoeff ((a.coeffOn U).toCoeffField x)) (Y.eval x)) = _
      rw [hxca, hcf, hx]
      let D : BlockVec d := diagonalWeakChildState hq s w a p r x -
        diagonalWeakState hq t a p r x
      have hYeval : Y.eval x = -D := by
        ext i <;> simp [Y, D, DoubledField.eval]
      rw [hYeval]
      change blockVecDot (-D) (blockMatVecMul (blockMatrixOfCoeff (f x)) (-D)) =
        blockVecDot D (blockMatVecMul (blockMatrixOfCoeff (f x)) D)
      rw [show (-D) = (-1 : ℝ) • D by simp,
        blockMatVecMul_smul, blockVecDot_smul_left,
        blockVecDot_smul_right]
      ring
    rw [hpoint]
    ring
  rw [hpotAverage, henergy, ← coarseBlock_eq_coarseBlockMatrix] at hpot
  rw [hfluxAverage, henergy, ← coarseBlock_eq_coarseBlockMatrix] at hflux
  have hpot' := hpot
  have hflux' := hflux
  rw [vecDot_neg_right, abs_neg] at hpot'
  rw [vecDot_neg_right, abs_neg] at hflux'
  simpa only [U] using! And.intro hpot' hflux'

end

end HCPolySupport.HighContrast.Response
