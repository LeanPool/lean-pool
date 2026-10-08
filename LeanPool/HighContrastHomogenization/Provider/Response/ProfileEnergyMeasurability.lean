/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.ProfileRecentMeasurability
public import LeanPool.HighContrastHomogenization.Provider.Response.ProfileEnergyPointwise

/-!
# High-contrast homogenization: Provider.Response.ProfileEnergyMeasurability

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Measurability of terminal optimizer energies

The squared canonical optimizer energy is a fixed quadratic reading of the
terminal coarse block.  Entrywise coarse-block measurability therefore gives
measurability of both the primal and coefficient-transpose energies.
-/

namespace HCPolySupport.HighContrast.Response

open Book.Ch02 MeasureTheory

noncomputable section

variable {d : ℕ}

/-- A fixed quadratic reading of a random coarse block is almost everywhere
measurable. -/
theorem aemeasurable_blockQuadratic_coarseBlock
    {P : Measure (CoeffSpace d)} {U : Set (Vec d)}
    (hU : HasMeasurableCoarseBlock P U) (X : BlockVec d) :
    AEMeasurable (fun a ↦
      blockVecDot X (blockMatVecMul (coarseBlock U a) X)) P := by
  have hfun : (fun a ↦
      blockVecDot X (blockMatVecMul (coarseBlock U a) X)) =
      fun a ↦ ∑ α : BlockCoord d, ∑ β : BlockCoord d,
        toFullBlockVec X α *
          toFullBlockMat (coarseBlock U a) α β *
            toFullBlockVec X β := by
    funext a
    rw [blockVecDot_blockMatVecMul_eq_dotProduct]
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    exact Finset.sum_congr rfl fun α _ ↦
      Finset.sum_congr rfl fun β _ ↦ by ring
  rw [hfun]
  exact Finset.aemeasurable_fun_sum Finset.univ fun α _ ↦
    Finset.aemeasurable_fun_sum Finset.univ fun β _ ↦
      (((hU α β).aemeasurable.const_mul _).mul_const _)

/-- The primal optimizer energy squared is its terminal block quadratic form
minus the load product. -/
theorem sq_diagonalWeakEnergy_eq_coarseBlock
    {q : Mat d} (hq : q.PosDef) (t : ℤ) (a : CoeffSpace d)
    (p r : Vec d) :
    diagonalWeakEnergy hq t a p r ^ 2 =
      blockVecDot ((-p, r) : BlockVec d)
          (blockMatVecMul (coarseBlock (adaptedCell q t) a)
            ((-p, r) : BlockVec d)) -
        2 * vecDot p r := by
  have hJenergy := responseJ_eq_sq_diagonalWeakEnergy hq t a p r
  have hJblock := responseJ_eq_coarseBlock (adaptedDomain hq t) a p r
  rw [hJenergy] at hJblock
  change (1 / 2 : ℝ) * diagonalWeakEnergy hq t a p r ^ 2 =
    (1 / 2 : ℝ) * blockVecDot ((-p, r) : BlockVec d)
      (blockMatVecMul (coarseBlock (adaptedCell q t) a)
        ((-p, r) : BlockVec d)) - vecDot p r at hJblock
  linarith only [hJblock]

/-- The adjoint optimizer energy squared is the plus-load quadratic reading
of the original terminal block. -/
theorem sq_diagonalWeakAdjointEnergy_eq_coarseBlock
    {q : Mat d} (hq : q.PosDef) (t : ℤ) (a : CoeffSpace d)
    (p r : Vec d) :
    diagonalWeakAdjointEnergy hq t a p r ^ 2 =
      blockVecDot ((p, r) : BlockVec d)
          (blockMatVecMul (coarseBlock (adaptedCell q t) a)
            ((p, r) : BlockVec d)) -
        2 * vecDot p r := by
  have hmain := sq_diagonalWeakEnergy_eq_coarseBlock
    hq t a.transpose p r
  have htrans : coarseBlock (adaptedCell q t) a.transpose =
      blockMatMul (blockDiag 1 (-1))
        (blockMatMul (coarseBlock (adaptedCell q t) a)
          (blockDiag 1 (-1))) := by
    simpa only [adaptedDomain_carrier] using
      coarseBlock_transpose a (adaptedDomain hq t)
  rw [htrans, blockQuadratic_adjointSign_congr,
    adjointSign_mulVec] at hmain
  change diagonalWeakAdjointEnergy hq t a p r ^ 2 = _
  calc
    diagonalWeakAdjointEnergy hq t a p r ^ 2 =
        blockVecDot ((-p, -r) : BlockVec d)
            (blockMatVecMul (coarseBlock (adaptedCell q t) a)
              ((-p, -r) : BlockVec d)) -
          2 * vecDot p r := hmain
    _ = blockVecDot ((p, r) : BlockVec d)
            (blockMatVecMul (coarseBlock (adaptedCell q t) a)
              ((p, r) : BlockVec d)) -
          2 * vecDot p r := by
      have hneg : ((-p, -r) : BlockVec d) = -((p, r) : BlockVec d) := rfl
      rw [hneg, ← neg_one_smul ℝ ((p, r) : BlockVec d),
        blockMatVecMul_smul, blockVecDot_smul_left,
        blockVecDot_smul_right]
      norm_num

/-- The primal terminal optimizer energy is almost everywhere measurable. -/
theorem aemeasurable_diagonalWeakEnergy
    {P : Measure (CoeffSpace d)} {q : Mat d} (hq : q.PosDef)
    (t : ℤ) (p r : Vec d) :
    AEMeasurable (fun a ↦ diagonalWeakEnergy hq t a p r) P := by
  have hquad := aemeasurable_blockQuadratic_coarseBlock
    (Recurrence.hasMeasurableCoarseBlock_adaptedCell P hq t)
    ((-p, r) : BlockVec d)
  have heq : (fun a ↦ diagonalWeakEnergy hq t a p r) =
      fun a ↦ Real.sqrt
        (blockVecDot ((-p, r) : BlockVec d)
            (blockMatVecMul (coarseBlock (adaptedCell q t) a)
              ((-p, r) : BlockVec d)) -
          2 * vecDot p r) := by
    funext a
    rw [← sq_diagonalWeakEnergy_eq_coarseBlock hq t a p r,
      Real.sqrt_sq (diagonalWeakEnergy_nonneg hq t a p r)]
  rw [heq]
  exact (hquad.sub aemeasurable_const).sqrt

/-- The adjoint terminal optimizer energy is almost everywhere measurable. -/
theorem aemeasurable_diagonalWeakAdjointEnergy
    {P : Measure (CoeffSpace d)} {q : Mat d} (hq : q.PosDef)
    (t : ℤ) (p r : Vec d) :
    AEMeasurable (fun a ↦ diagonalWeakAdjointEnergy hq t a p r) P := by
  have hquad := aemeasurable_blockQuadratic_coarseBlock
    (Recurrence.hasMeasurableCoarseBlock_adaptedCell P hq t)
    ((p, r) : BlockVec d)
  have heq : (fun a ↦ diagonalWeakAdjointEnergy hq t a p r) =
      fun a ↦ Real.sqrt
        (blockVecDot ((p, r) : BlockVec d)
            (blockMatVecMul (coarseBlock (adaptedCell q t) a)
              ((p, r) : BlockVec d)) -
          2 * vecDot p r) := by
    funext a
    rw [← sq_diagonalWeakAdjointEnergy_eq_coarseBlock hq t a p r]
    simpa only [diagonalWeakAdjointEnergy_eq] using
      (Real.sqrt_sq (diagonalWeakEnergy_nonneg hq t a.transpose p r)).symm
  rw [heq]
  exact (hquad.sub aemeasurable_const).sqrt

end

end HCPolySupport.HighContrast.Response
