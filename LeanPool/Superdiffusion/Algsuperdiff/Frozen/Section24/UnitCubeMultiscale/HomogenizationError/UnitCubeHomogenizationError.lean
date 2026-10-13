/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Frozen.Section24.UnitCubeMultiscale.HomogenizationError.ExistsUniqueUnitCubeHomogenizationError

/-!
# UnitCubeHomogenizationError

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

open HCPolySupport HCPolySupport.Book.Ch02 MeasureTheory

-- FROZEN-STATEMENT-BEGIN
/-- The multiscale homogenization error on the origin unit cube. -/
noncomputable def Algsuperdiff.Frozen.Section24.unitCubeHomogenizationError
    {d : ℕ} (s : ℝ) (p q : Book.Ch02.MultiscaleExponent)
    (a : CoeffOn (cubeDomain (originCube d 0))) (a0 : Mat d) : ℝ :=
  Classical.choose
    (Algsuperdiff.Frozen.Section24.existsUnique_unitCubeHomogenizationError
      s p q a a0)
-- FROZEN-STATEMENT-END
