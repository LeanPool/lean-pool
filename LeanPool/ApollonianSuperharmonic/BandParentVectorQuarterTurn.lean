/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.BandVectors
public import LeanPool.ApollonianSuperharmonic.GaussianQuarterTurn
public import Mathlib.Init



/-!
# BandParentVectorQuarterTurn

Shared facts adapted from Wesley Pegden's Apache-2.0 Trellis formalization of
Levine–Pegden–Smart, replacing repeated implementations at their common dependency level.
-/

@[expose] public section

namespace ApollonianSuperharmonic
namespace BandParentVectorQuarterTurn

/-- The phase relation turns each incoming parent vector into its outgoing vector. -/
theorem turn (q : Fin 4 → CircleCoordinates)
    (phase : ∀ s : Fin 3, BandVectors.1 (q 0) (q s.succ) =
      (⟨0, 1⟩ : GaussianInt) * BandVectors.1 (q s.succ) (q 0)) (s : Fin 3) :
    GaussianQuarterTurn (BandVectors.1 (q s.succ) (q 0)) =
      BandVectors.1 (q 0) (q s.succ) := by
  rw [phase s]
  rcases BandVectors.1 (q s.succ) (q 0) with ⟨a, b⟩
  apply Zsqrtd.ext <;> simp [GaussianQuarterTurn]

end BandParentVectorQuarterTurn
end ApollonianSuperharmonic

end
