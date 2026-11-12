/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.BandCircleEnclosureDichotomy
public import LeanPool.ApollonianSuperharmonic.CircleMatrixEnclosureCriterion
public import LeanPool.ApollonianSuperharmonic.SymmetricMatrixCoordinates

-- [TABLET NODE: PositiveTracePackingDichotomy]

/-!
# PositiveTracePackingDichotomy

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem PositiveTracePackingDichotomy
    (A : Matrix (Fin 2) (Fin 2) Real) (hA : A.IsSymm)
    (htrace : 0 < Matrix.trace A) :
    (∃ C : BandCircle, (CircleMatrix C - A).PosSemidef) ∨
      (∃ C : BandCircle, (A - CircleMatrix C).PosDef) := by
-- BODY
  let E : EuclideanCircleData :=
    { center := (SymmetricMatrixCoordinates A).1
      radius := (SymmetricMatrixCoordinates A).2
      radius_pos := by
        simpa [SymmetricMatrixCoordinates] using htrace }
  rcases BandCircleEnclosureDichotomy E with h | h
  · left
    rcases h with ⟨C, hC⟩
    refine ⟨C, (CircleMatrixEnclosureCriterion A hA C).1.mpr ?_⟩
    simpa [E] using hC
  · right
    rcases h with ⟨C, hC⟩
    refine ⟨C, (CircleMatrixEnclosureCriterion A hA C).2.mpr ?_⟩
    simpa [E] using hC

end ApollonianSuperharmonic

end
