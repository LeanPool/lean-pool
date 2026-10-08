/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.AdaptedCellExcessBoundary
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.BlockRowGoodTail
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.BoundaryRowShift
public import LeanPool.HighContrastHomogenization.Provider.Response.WeakNorm

/-!
# High-contrast homogenization: Provider.PolynomialHomogenization.AdaptedCellExcessQuenchedRow

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Adapted-cell excesses from a shifted quenched row

An aligned adapted child is first filled by standard cells.  If its parent
adapted cell lies in an enlarged centered cube, the resulting boundary
convolution is controlled by the quenched block row at that enlarged scale.
-/

namespace HCPolySupport
namespace HighContrast

open Book.Ch02

open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-- A standard-cell quenched row on a centered enlargement controls the
excess of every aligned adapted child.  The shift records both the depth of
the child and the fixed enlargement of its parent. -/
theorem blockExcess_coarseBlock_adaptedCellAt_le_quenched_block_row
    [NeZero d] {q : Mat d} (hq : q.PosDef)
    (t n G : ℕ) (a : CoeffSpace d)
    (abar : Mat d) (habar : (symmPart abar).PosDef)
    (rho sourceScale : ℝ) (hrho : 0 < rho) (hrho1 : rho ≤ 1)
    (henclose : adaptedCell q (t : ℤ) ⊆
      centeredCube d ((t + G : ℕ) : ℤ))
    (hactive : sourceScale ≤ (3 : ℝ) ^ (t + G))
    (w : Fin d → ℤ)
    (hw : w ∈ Response.alignedIndex q ((t : ℤ) - (n : ℤ)) (t : ℤ)) :
    blockExcess
        (coarseBlock (adaptedCellAt q ((t : ℤ) - (n : ℤ)) w) a)
        (Book.Ch02.constantBlockMatrix abar) ≤
      max 1 (6 * (d : ℝ) * Real.sqrt d * ‖q⁻¹‖) *
        (3 : ℝ) ^ (rho * ((n + G : ℕ) : ℝ)) *
          Quenched.quenchedBlockRow rho
            (Book.Ch02.constantBlockMatrix abar) sourceScale a (t + G) := by
  classical
  let F : BlockMat d := Book.Ch02.constantBlockMatrix abar
  let B : ℤ → ℝ := fun r ↦
    sSup {x : ℝ | ∃ z : Fin d → ℤ,
      standardCellCenter r z ∈ centeredCube d ((t + G : ℕ) : ℤ) ∧
      x = blockExcess (coarseBlock (standardCell d r z) a) F}
  obtain ⟨C, hC, hcellBound⟩ :=
    exists_uniform_standardCell_blockExcess_bound a abar habar
      (isBounded_centeredCube d (((t + G : ℕ) : ℤ) + 1))
  have hFsym : IsSymmetricBlockMat F := by
    simpa only [F, Book.Ch02.constantBlockMatrix, blockMatrixOfCoeff] using
      isSymmetricBlockMat_blockMatrixOfCoeff abar
  have hFpd : Book.Ch02.BlockPosDef F := by
    simpa only [F] using
      blockPosDef_constantBlockMatrix_of_posDef_symmPart habar
  have hB0 : ∀ r : ℤ, 0 ≤ B r := by
    intro r
    dsimp only [B]
    refine Real.sSup_nonneg ?_
    rintro x ⟨z, -, rfl⟩
    exact standardCell_blockExcess_nonneg a hFsym hFpd r z
  have hbdd : ∀ r : ℤ, r ≤ ((t + G : ℕ) : ℤ) →
      BddAbove {x : ℝ | ∃ z : Fin d → ℤ,
        standardCellCenter r z ∈ centeredCube d ((t + G : ℕ) : ℤ) ∧
        x = blockExcess (coarseBlock (standardCell d r z) a) F} := by
    intro r hr
    refine ⟨C, ?_⟩
    rintro x ⟨z, hz, rfl⟩
    simpa only [F] using
      hcellBound r z (standardCell_subset_centeredCube_succ hz hr)
  have hrowOuter : Summable (fun j : ℕ ↦
      (3 : ℝ) ^ (-rho * (j : ℝ)) *
        B (((t + G : ℕ) : ℤ) - (j : ℤ))) := by
    simpa only [B, F] using
      summable_weighted_standardCell_blockExcess_sSup
        (t + G) rho a abar habar hrho
  let H : ℕ := n + G
  have hindex : (t : ℤ) - (n : ℤ) + (H : ℤ) =
      ((t + G : ℕ) : ℤ) := by
    dsimp only [H]
    omega
  have hrowShift : Summable (fun j : ℕ ↦
      (3 : ℝ) ^ (-rho * (j : ℝ)) *
        B ((t : ℤ) - (n : ℤ) + (H : ℤ) - (j : ℤ))) := by
    simpa only [hindex] using hrowOuter
  obtain ⟨hboundarySummable, hboundaryLe⟩ :=
    summable_boundary_row_and_tsum_le_shifted_row
      hrho1 H ((t : ℤ) - (n : ℤ)) B hB0 hrowShift
  have hchild :
      adaptedCellAt q ((t : ℤ) - (n : ℤ)) w ⊆ adaptedCell q (t : ℤ) :=
    Response.adaptedCellAt_subset_of_mem_alignedIndex hq (by omega) hw
  have hlocal :
      blockExcess
          (coarseBlock (adaptedCellAt q ((t : ℤ) - (n : ℤ)) w) a) F ≤
        max 1 (6 * (d : ℝ) * Real.sqrt d * ‖q⁻¹‖) *
          ∑' j : ℕ, (3 : ℝ) ^ (-(j : ℤ)) *
            B ((t : ℤ) - (n : ℤ) - (j : ℤ)) := by
    apply blockExcess_coarseBlock_adaptedCellAt_le_boundary_tsum
      hq ((t : ℤ) - (n : ℤ)) w a hFsym hFpd B hB0 hboundarySummable
    intro r z hrk hz
    have hzCenter :
        standardCellCenter r z ∈ centeredCube d ((t + G : ℕ) : ℤ) :=
      henclose (hchild (hz (Recurrence.standardCellCenter_mem_standardCell r z)))
    exact le_csSup (hbdd r (by omega)) ⟨z, hzCenter, rfl⟩
  have hrowEq :
      (∑' j : ℕ, (3 : ℝ) ^ (-rho * (j : ℝ)) *
          B (((t + G : ℕ) : ℤ) - (j : ℤ))) =
        Quenched.quenchedBlockRow rho F sourceScale a (t + G) := by
    unfold Quenched.quenchedBlockRow
    rw [ite_eq_left hactive]
  have hfactor0 :
      0 ≤ max 1 (6 * (d : ℝ) * Real.sqrt d * ‖q⁻¹‖) :=
    le_trans zero_le_one (le_max_left _ _)
  calc
    blockExcess
        (coarseBlock (adaptedCellAt q ((t : ℤ) - (n : ℤ)) w) a) F ≤
        max 1 (6 * (d : ℝ) * Real.sqrt d * ‖q⁻¹‖) *
          ∑' j : ℕ, (3 : ℝ) ^ (-(j : ℤ)) *
            B ((t : ℤ) - (n : ℤ) - (j : ℤ)) := hlocal
    _ ≤ max 1 (6 * (d : ℝ) * Real.sqrt d * ‖q⁻¹‖) *
          ((3 : ℝ) ^ (rho * (H : ℝ)) *
            ∑' j : ℕ, (3 : ℝ) ^ (-rho * (j : ℝ)) *
              B ((t : ℤ) - (n : ℤ) + (H : ℤ) - (j : ℤ))) :=
      mul_le_mul_of_nonneg_left hboundaryLe hfactor0
    _ = max 1 (6 * (d : ℝ) * Real.sqrt d * ‖q⁻¹‖) *
          (3 : ℝ) ^ (rho * ((n + G : ℕ) : ℝ)) *
            Quenched.quenchedBlockRow rho F sourceScale a (t + G) := by
      rw [show (∑' j : ℕ, (3 : ℝ) ^ (-rho * (j : ℝ)) *
          B ((t : ℤ) - (n : ℤ) + (H : ℤ) - (j : ℤ))) =
          ∑' j : ℕ, (3 : ℝ) ^ (-rho * (j : ℝ)) *
            B (((t + G : ℕ) : ℤ) - (j : ℤ)) by
        congr 1
        funext j
        rw [hindex]]
      rw [hrowEq]
      simp only [H, mul_assoc]

end

end HighContrast
end HCPolySupport
