/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Frozen.Section24.UnitCubeMultiscale.Lambda.UnitCubeLambda

/-!
# Characterization

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-! # Characterization of origin-cube lower multiscale ellipticity -/

namespace Algsuperdiff.Section24.UnitCubeMultiscale.Lambda

open HCPolySupport HCPolySupport.Book.Ch02 MeasureTheory

variable {d : ℕ}

/-- The unique-choice characterization used by the corresponding frozen
theorem. -/
theorem characterization
    (s : ℝ) (q : Book.Ch02.MultiscaleExponent)
    (a : CoeffOn (cubeDomain (originCube d 0))) :
    ∀ F : TriadicCoeffFamily d,
      CoeffOn.AEEq (F.coeffOn (originCube d 0)) a →
        Algsuperdiff.Frozen.Section24.unitCubeLambda s q a =
          Book.Ch02.lambdaSq (originCube d 0) s q F :=
  (Classical.choose_spec
    (Algsuperdiff.Frozen.Section24.existsUnique_unitCubeLambda s q a)).1

end Algsuperdiff.Section24.UnitCubeMultiscale.Lambda
