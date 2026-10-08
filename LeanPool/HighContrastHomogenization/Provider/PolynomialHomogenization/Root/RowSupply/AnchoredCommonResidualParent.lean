/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.RowSupply.CommonResidualObservationParent
public import LeanPool.HighContrastHomogenization.Provider.Regularity.AffineTransfer

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.RowSupply.AnchoredCommonResidualParent

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Anchored common residual parent

The ellipsoid premise anchors the gauge domain at the origin.  After dividing
by the normalized-root scale, the residual affine image lies in the fixed
generation-one adapted cell.  Hence the common parent can be selected with an
explicit upper generation rather than by an arbitrary bounded-domain radius.
-/

namespace HCPolySupport
namespace HighContrast
namespace RowSupply

open scoped Matrix

noncomputable section

variable {d : ℕ}

/-- A normalized gauge domain is contained in the fixed generation-one
normalized-root cell after the residual dilation in `[1,3]`. -/
theorem matImage_epsilonAffineGrid_subset_normalizedRoot_cell_one
    [NeZero d] {U : Set (Vec d)} {lambda : ℝ}
    (hlambda : lambda ∈ Set.Icc (1 : ℝ) 3)
    {abar : Mat d} (hS : (symmPart abar).PosDef)
    (hGauge : U ⊆ {z : Vec d |
      vecNormSq z ≤ specBound (symmPart abar)⁻¹}) :
    matImage (epsilonAffineGrid lambda abar) U ⊆
      adaptedCell (Selection.normalizedRoot (symmPart abar)) 1 := by
  let alpha : ℝ := Real.sqrt (specBound (symmPart abar)⁻¹)
  have halpha : 0 < alpha := by
    exact Real.sqrt_pos.mpr (normalizedRootScale_pos hS)
  have hlambdaPos : 0 < lambda := zero_lt_one.trans_le hlambda.1
  rintro y ⟨z, hz, rfl⟩
  let beta : ℝ := (lambda * alpha)⁻¹
  let w : Vec d := beta • z
  have hbeta : 0 < beta := inv_pos.mpr (mul_pos hlambdaPos halpha)
  have hzNorm : ‖z‖ ≤ alpha := by
    calc
      ‖z‖ ≤ Real.sqrt (vecNormSq z) := norm_le_sqrt_vecNormSq z
      _ ≤ Real.sqrt (specBound (symmPart abar)⁻¹) :=
        Real.sqrt_le_sqrt (hGauge hz)
      _ = alpha := rfl
  have hwNorm : ‖w‖ ≤ 1 := by
    calc
      ‖w‖ = beta * ‖z‖ := by
        dsimp only [w]
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hbeta]
      _ ≤ beta * alpha := mul_le_mul_of_nonneg_left hzNorm hbeta.le
      _ = lambda⁻¹ := by
        dsimp only [beta]
        field_simp [hlambdaPos.ne', halpha.ne']
      _ ≤ 1 := (inv_le_one₀ hlambdaPos).2 hlambda.1
  have hw : w ∈ centeredCube d (1 : ℤ) := by
    rw [Recurrence.mem_centeredCube_iff]
    intro i
    have hi : |w i| ≤ 1 := by
      calc
        |w i| = ‖w i‖ := (Real.norm_eq_abs (w i)).symm
        _ ≤ ‖w‖ := norm_le_pi_norm w i
        _ ≤ 1 := hwNorm
    rw [abs_le] at hi
    norm_num
    constructor <;> linarith only [hi.1, hi.2]
  refine ⟨w, hw, ?_⟩
  dsimp only [w, beta, Selection.normalizedRoot, epsilonAffineGrid, alpha]
  simp only [smul_matVecMul, matVecMul_smul, smul_smul]
  congr 1
  field_simp [hlambdaPos.ne', halpha.ne']
  exact div_self halpha.ne'

/-- The anchored selector chooses the explicit common generation `max n 1`.
It therefore publishes both containment and its exact deterministic upper
generation relative to the requested activation generation. -/
theorem exists_anchored_common_matImage_enclosingParent
    [NeZero d] {U : Set (Vec d)} {lambda : ℝ}
    (hlambda : lambda ∈ Set.Icc (1 : ℝ) 3)
    {abar : Mat d} (hS : (symmPart abar).PosDef)
    (hGauge : U ⊆ {z : Vec d |
      vecNormSq z ≤ specBound (symmPart abar)⁻¹})
    (n : ℤ) :
    ∃ M : ℤ, M = max n 1 ∧ n ≤ M ∧
      matImage (epsilonAffineGrid lambda abar) U ⊆
        adaptedCell (Selection.normalizedRoot (symmPart abar)) M := by
  let M : ℤ := max n 1
  refine ⟨M, rfl, le_max_left _ _, ?_⟩
  refine (matImage_epsilonAffineGrid_subset_normalizedRoot_cell_one
    hlambda hS hGauge).trans ?_
  rintro y ⟨z, hz, rfl⟩
  exact ⟨z, Initialization.centeredCube_subset_centeredCube
    (le_max_right n 1) hz, rfl⟩

end

end RowSupply
end HighContrast
end HCPolySupport
