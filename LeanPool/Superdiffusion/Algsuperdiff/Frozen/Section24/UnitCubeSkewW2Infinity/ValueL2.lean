/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Frozen.Section24.MatrixDerivativeNorm
public import LeanPool.Superdiffusion.Algsuperdiff.Frozen.Section24.UnitCubeSkewW2Infinity
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# ValueL2

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

open HCPolySupport HCPolySupport.Book.Ch02 MeasureTheory
open scoped ENNReal

-- FROZEN-STATEMENT-BEGIN
/-- The matrix-value L² norm on the unit cube. -/
noncomputable def Algsuperdiff.Frozen.Section24.UnitCubeSkewW2Infinity.valueL2
    {d : ℕ} (h : Algsuperdiff.Frozen.Section24.UnitCubeSkewW2Infinity d) : ℝ :=
  ENNReal.toReal
    (eLpNorm (fun x => matrixNorm (h.toLInfSkewMatrixFieldOn.1.1 x)) 2
      (volumeMeasureOn ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d))))
-- FROZEN-STATEMENT-END
