/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.TileTouching
public import Mathlib.Init


/-!
# TileTouchingDisjoint

Shared facts adapted from Wesley Pegden's Apache-2.0 Trellis formalization of
Levine–Pegden–Smart, replacing repeated implementations at their common dependency level.
-/

@[expose] public section

namespace ApollonianSuperharmonic
namespace TileTouchingDisjoint

/-- Shared cells identity for TileTouchingDisjoint. -/
theorem cells :
    (by
      classical
      exact
        ∀ (X : ProtoTile), ∀ (Y : ProtoTile), (X.cells.Nonempty) → ((Y.cells.Nonempty) →
            ((TileTouching X Y) → (Disjoint X.cells Y.cells))) ) := by
  classical
  intro X Y hX hY hxy
  rcases hxy with ⟨_, _, hd, _⟩ | ⟨he, _⟩ | ⟨he, _⟩
  · exact hd
  · simp [he] at hX
  · simp [he] at hY

end TileTouchingDisjoint
end ApollonianSuperharmonic

end
