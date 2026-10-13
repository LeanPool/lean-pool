/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section24.UnitCubeMultiscale.HomogenizationError.Characterization

/-!
# UnitCubeHomogenizationErrorCharacterization

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

open HCPolySupport HCPolySupport.Book.Ch02 MeasureTheory

-- FROZEN-STATEMENT-BEGIN
theorem Algsuperdiff.Frozen.Section24.unitCubeHomogenizationError_characterization
    {d : ℕ} [NeZero d] (s : ℝ) (p q : Book.Ch02.MultiscaleExponent)
    (a : CoeffOn (cubeDomain (originCube d 0))) (a0 : Mat d) :
    ∀ F : TriadicCoeffFamily d,
      CoeffOn.AEEq (F.coeffOn (originCube d 0)) a →
        Algsuperdiff.Frozen.Section24.unitCubeHomogenizationError
          s p q a a0 =
          Book.Ch02.HomogenizationErrorOnCube
            (originCube d 0) s p q F a0
-- FROZEN-STATEMENT-END
    := by
  exact Algsuperdiff.Section24.UnitCubeMultiscale.HomogenizationError.characterization
    s p q a a0
