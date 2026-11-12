/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.GaussianQuarterTurn
public import Mathlib.Init


/-!
# GaussianQuarterTurnProperties

Shared facts adapted from Wesley Pegden's Apache-2.0 Trellis formalization of
Levine–Pegden–Smart, replacing repeated implementations at their common dependency level.
-/

@[expose] public section

namespace ApollonianSuperharmonic
namespace GaussianQuarterTurnProperties

/-- Shared negation identity for GaussianQuarterTurnProperties. -/
theorem negation :
    (by
      classical
      exact
        ∀ (z : GaussianInt), GaussianQuarterTurn (-z) = -GaussianQuarterTurn z ) := by
  classical
  intro z
  rcases z with ⟨a, b⟩
  apply Zsqrtd.ext <;> simp [GaussianQuarterTurn]

/-- Shared twice identity for GaussianQuarterTurnProperties. -/
theorem twice :
    (by
      classical
      exact
        ∀ (z : GaussianInt), GaussianQuarterTurn (GaussianQuarterTurn z) = -z ) := by
  classical
  intro z
  rcases z with ⟨a, b⟩
  apply Zsqrtd.ext <;> simp [GaussianQuarterTurn]

end GaussianQuarterTurnProperties
end ApollonianSuperharmonic

end
