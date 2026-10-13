/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Frozen.Section24.UnitCubeMultiscale.HomogenizationError.UnitCubeHomogenizationError

/-!
# Characterization

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-! # Characterization of the origin-cube homogenization error -/

namespace Algsuperdiff.Section24.UnitCubeMultiscale.HomogenizationError

open HCPolySupport HCPolySupport.Book.Ch02 MeasureTheory

variable {d : ℕ}

/-- The unique-choice characterization used by the corresponding frozen
theorem. -/
theorem characterization [NeZero d]
    (s : ℝ) (p q : Book.Ch02.MultiscaleExponent)
    (a : CoeffOn (cubeDomain (originCube d 0))) (a0 : Mat d) :
    ∀ F : TriadicCoeffFamily d,
      CoeffOn.AEEq (F.coeffOn (originCube d 0)) a →
        Algsuperdiff.Frozen.Section24.unitCubeHomogenizationError
          s p q a a0 =
          Book.Ch02.HomogenizationErrorOnCube
            (originCube d 0) s p q F a0 :=
  (Classical.choose_spec
    (Algsuperdiff.Frozen.Section24.existsUnique_unitCubeHomogenizationError
      s p q a a0)).1

end Algsuperdiff.Section24.UnitCubeMultiscale.HomogenizationError
