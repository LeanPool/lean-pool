/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.BlockExcessHomogenizationError
public import LeanPool.HighContrastHomogenization.Provider.Quenched.CoupledPhysicalBlockDecay
public import LeanPool.HighContrastHomogenization.Provider.Regularity.GoodTail
public import LeanPool.HighContrastHomogenization.Provider.Transport.DiscreteConvolution

/-!
# High-contrast homogenization: Provider.PolynomialHomogenization.BlockRowGoodTail

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Weak-error tails from a quenched block row

The spatial supremum in the quenched block row is genuinely summable for each
coefficient-space sample.  On the active source branch, the squared endpoint
homogenization error is bounded by that row.  Power decay of every later row
then gives the finite `l¹` weak-error certificate used by large-scale
regularity.
-/

namespace HCPolySupport
namespace HighContrast

open Book.Ch02

noncomputable section

variable {d : ℕ}

/-- Excess values over the standard cells at relative generation `m - n` whose centers lie in
the centered cube of generation `m`. -/
@[expose]
public def rowCellExcessSet (m n : ℕ) (a : CoeffSpace d)
    (F : BlockMat d) : Set ℝ :=
  {r : ℝ | ∃ w : Fin d → ℤ,
    standardCellCenter ((m : ℤ) - (n : ℤ)) w ∈ centeredCube d (m : ℤ) ∧
    r = blockExcess
      (coarseBlock (standardCell d ((m : ℤ) - (n : ℤ)) w) a) F}

/-- Supremum of the cell excess values in `rowCellExcessSet m n a F`. -/
@[expose]
public def rowCellExcessSup (m n : ℕ) (a : CoeffSpace d)
    (F : BlockMat d) : ℝ :=
  sSup (rowCellExcessSet m n a F)

private theorem rowCellExcessSup_data [NeZero d]
    (m : ℕ) (a : CoeffSpace d) (abar : Mat d)
    (habar : (symmPart abar).PosDef) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
      (rowCellExcessSet m n a (Book.Ch02.constantBlockMatrix abar)).Nonempty ∧
      BddAbove (rowCellExcessSet m n a (Book.Ch02.constantBlockMatrix abar)) ∧
      0 ≤ rowCellExcessSup m n a (Book.Ch02.constantBlockMatrix abar) ∧
      rowCellExcessSup m n a (Book.Ch02.constantBlockMatrix abar) ≤ C := by
  have hFsym : IsSymmetricBlockMat (Book.Ch02.constantBlockMatrix abar) := by
    simpa only [Book.Ch02.constantBlockMatrix, blockMatrixOfCoeff] using
      isSymmetricBlockMat_blockMatrixOfCoeff abar
  have hFpd : BlockPosDef (Book.Ch02.constantBlockMatrix abar) :=
    blockPosDef_constantBlockMatrix_of_posDef_symmPart habar
  obtain ⟨C, hC, hcell⟩ :=
    exists_uniform_standardCell_blockExcess_bound a abar habar
      (isBounded_centeredCube d ((m : ℤ) + 1))
  refine ⟨C, hC, ?_⟩
  intro n
  have hwindow : ∀ w : Fin d → ℤ,
      standardCellCenter ((m : ℤ) - (n : ℤ)) w ∈ centeredCube d (m : ℤ) →
        blockExcess
            (coarseBlock (standardCell d ((m : ℤ) - (n : ℤ)) w) a)
            (Book.Ch02.constantBlockMatrix abar) ≤ C := by
    intro w hw
    exact hcell _ w (standardCell_subset_centeredCube_succ hw (by omega))
  have hne :
      (rowCellExcessSet m n a (Book.Ch02.constantBlockMatrix abar)).Nonempty := by
    refine ⟨blockExcess
      (coarseBlock (standardCell d ((m : ℤ) - (n : ℤ)) 0) a)
        (Book.Ch02.constantBlockMatrix abar), 0, ?_, rfl⟩
    exact standardCellCenter_zero_mem_centeredCube _ _
  have hbdd :
      BddAbove (rowCellExcessSet m n a (Book.Ch02.constantBlockMatrix abar)) := by
    refine ⟨C, ?_⟩
    rintro r ⟨w, hw, rfl⟩
    exact hwindow w hw
  have hnonneg :
      0 ≤ rowCellExcessSup m n a (Book.Ch02.constantBlockMatrix abar) := by
    unfold rowCellExcessSup
    refine Real.sSup_nonneg ?_
    rintro r ⟨w, -, rfl⟩
    exact standardCell_blockExcess_nonneg a hFsym hFpd _ w
  have hle :
      rowCellExcessSup m n a (Book.Ch02.constantBlockMatrix abar) ≤ C := by
    unfold rowCellExcessSup
    exact csSup_le hne (by
      rintro r ⟨w, hw, rfl⟩
      exact hwindow w hw)
  exact ⟨hne, hbdd, hnonneg, hle⟩

/-- The exact weighted spatial-supremum sequence occurring on the active
branch of `quenched_block_row` is summable. -/
theorem summable_weighted_standardCell_blockExcess_sSup [NeZero d]
    (m : ℕ) (rho : ℝ) (a : CoeffSpace d) (abar : Mat d)
    (habar : (symmPart abar).PosDef) (hrho : 0 < rho) :
    Summable (fun n : ℕ ↦ (3 : ℝ) ^ (-rho * (n : ℝ)) *
      sSup {r : ℝ | ∃ w : Fin d → ℤ,
        standardCellCenter ((m : ℤ) - (n : ℤ)) w ∈ centeredCube d (m : ℤ) ∧
        r = blockExcess
          (coarseBlock (standardCell d ((m : ℤ) - (n : ℤ)) w) a)
          (Book.Ch02.constantBlockMatrix abar)}) := by
  obtain ⟨C, hC, hdata⟩ := rowCellExcessSup_data m a abar habar
  let ratio : ℝ := (3 : ℝ) ^ (-rho)
  have hratio0 : 0 ≤ ratio := Real.rpow_nonneg (by norm_num) _
  have hratio1 : ratio < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_iff_pos.mpr hrho)
  have hfactor : ∀ n : ℕ,
      (3 : ℝ) ^ (-rho * (n : ℝ)) = ratio ^ n := by
    intro n
    dsimp [ratio]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
  have hmajorant : Summable (fun n : ℕ ↦ C * ratio ^ n) :=
    (summable_geometric_of_lt_one hratio0 hratio1).mul_left C
  have hsum : Summable (fun n : ℕ ↦
      (3 : ℝ) ^ (-rho * (n : ℝ)) *
        rowCellExcessSup m n a (Book.Ch02.constantBlockMatrix abar)) := by
    refine Summable.of_nonneg_of_le
      (f := fun n : ℕ ↦ C * ratio ^ n) ?_ ?_ hmajorant
    · intro n
      exact mul_nonneg (Real.rpow_nonneg (by norm_num) _) (hdata n).2.2.1
    · intro n
      have hfactor0 : 0 ≤ (3 : ℝ) ^ (-rho * (n : ℝ)) :=
        Real.rpow_nonneg (by norm_num) _
      have hmul := mul_le_mul_of_nonneg_left (hdata n).2.2.2 hfactor0
      calc
        (3 : ℝ) ^ (-rho * (n : ℝ)) *
            rowCellExcessSup m n a (Book.Ch02.constantBlockMatrix abar) ≤
            (3 : ℝ) ^ (-rho * (n : ℝ)) * C := hmul
        _ = C * ratio ^ n := by rw [hfactor n]; ring
  simpa [rowCellExcessSup, rowCellExcessSet] using hsum

private theorem physical_ratio_rpow_le_geometric_gap
    {x kappa : ℝ} {n k : ℤ} (hx : 0 < x)
    (hxn : x ≤ (3 : ℝ) ^ n) (hkappa : 0 < kappa) :
    (((3 : ℝ) ^ k) / x) ^ (-kappa) ≤
      (3 : ℝ) ^ (-kappa * ((k : ℝ) - (n : ℝ))) := by
  have hkpow : 0 < (3 : ℝ) ^ k := by positivity
  have hratio : 0 < ((3 : ℝ) ^ k) / x := div_pos hkpow hx
  have hgap : 0 < (3 : ℝ) ^ ((k : ℝ) - (n : ℝ)) := by positivity
  have hbase :
      (3 : ℝ) ^ ((k : ℝ) - (n : ℝ)) ≤ ((3 : ℝ) ^ k) / x := by
    rw [Real.rpow_sub (by norm_num : (0 : ℝ) < 3),
      Real.rpow_intCast, Real.rpow_intCast]
    exact div_le_div_of_nonneg_left hkpow.le hx hxn
  calc
    (((3 : ℝ) ^ k) / x) ^ (-kappa) ≤
        ((3 : ℝ) ^ ((k : ℝ) - (n : ℝ))) ^ (-kappa) :=
      (Real.rpow_le_rpow_iff_of_neg hratio hgap (neg_neg_of_pos hkappa)).2 hbase
    _ = (3 : ℝ) ^
        (((k : ℝ) - (n : ℝ)) * (-kappa)) :=
      (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3) _ _).symm
    _ = (3 : ℝ) ^ (-kappa * ((k : ℝ) - (n : ℝ))) := by
      congr 1
      ring

end

end HighContrast
end HCPolySupport
