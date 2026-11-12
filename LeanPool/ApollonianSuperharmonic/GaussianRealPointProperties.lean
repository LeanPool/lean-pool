/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.GaussianRealPoint
public import Mathlib.Init


/-!
# GaussianRealPointProperties

Shared facts adapted from Wesley Pegden's Apache-2.0 Trellis formalization of
Levine–Pegden–Smart, replacing repeated implementations at their common dependency level.
-/

@[expose] public section

namespace ApollonianSuperharmonic
namespace GaussianRealPointProperties

/-- Shared add identity for GaussianRealPointProperties. -/
theorem add :
    (by
      classical
      exact
        ∀ (x : GaussianInt), ∀ (y : GaussianInt), GaussianRealPoint (x + y) = GaussianRealPoint x
            + GaussianRealPoint y ) := by
  classical
  intro x y
  ext <;> simp [GaussianRealPoint]

/-- Shared negation identity for GaussianRealPointProperties. -/
theorem negation :
    (by
      classical
      exact
        ∀ (z : GaussianInt), GaussianRealPoint (-z) = -GaussianRealPoint z ) := by
  classical
  intro z
  ext <;> simp [GaussianRealPoint]

/-- Shared injective identity for GaussianRealPointProperties. -/
theorem injective :
    (by
      classical
      exact
        Function.Injective GaussianRealPoint ) := by
  classical
  intro x y hxy
  apply Zsqrtd.ext
  · have h := congrArg Prod.fst hxy
    dsimp [GaussianRealPoint] at h
    exact_mod_cast h
  · have h := congrArg Prod.snd hxy
    dsimp [GaussianRealPoint] at h
    exact_mod_cast h

end GaussianRealPointProperties
end ApollonianSuperharmonic

end
