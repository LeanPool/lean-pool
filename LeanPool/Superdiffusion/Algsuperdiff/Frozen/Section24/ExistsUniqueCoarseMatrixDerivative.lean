/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section24.CoarseMatrixDerivative.Existence

/-!
# ExistsUniqueCoarseMatrixDerivative

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

open HCPolySupport HCPolySupport.Book.Ch02 MeasureTheory
open scoped ENNReal

-- FROZEN-STATEMENT-BEGIN
theorem Algsuperdiff.Frozen.Section24.existsUnique_coarseMatrixDerivative
    {d : ℕ} (U : Domain d) (a : CoeffOn U)
    (h : Algsuperdiff.Frozen.Section24.LInfMatrixFieldOn U) :
    ∃! D : BlockMat d,
      IsSymmetricBlockMat D ∧
      ∀ p q : Vec d, ∀ vAdj : Solution U a.transpose, ∀ v : Solution U a,
        IsResponseMaximizer U a.transpose p q vAdj →
        IsResponseMaximizer U a p (-q) v →
        blockVecDot (p, q) (blockMatVecMul D (p, q)) =
          average U (fun x =>
            vecDot (vAdj.toH1.grad x)
              (matVecMul (h.1 x) (v.toH1.grad x)))
-- FROZEN-STATEMENT-END
    := by
  exact
    Algsuperdiff.Section24.CoarseMatrixDerivative.Internal.existsUnique_coarseMatrixDerivative
      U a h
