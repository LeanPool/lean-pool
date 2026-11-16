/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Init
public import Mathlib.LinearAlgebra.AffineSpace.AffineMap
public import Mathlib.Tactic.Module


/-!
# AffineLineMapProperties

Shared facts adapted from Wesley Pegden's Apache-2.0 Trellis formalization of
Levine–Pegden–Smart, replacing repeated implementations at their common dependency level.
-/

@[expose] public section

namespace ApollonianSuperharmonic
namespace AffineLineMapProperties

/-- Shared coordinates identity for AffineLineMapProperties. -/
theorem coordinates :
    (by
      classical
      exact
        ∀ x y : Real × Real, ∀ t : Real, AffineMap.lineMap x y t = x + t • (y - x) ) := by
  classical
  intro x y t
  rw [AffineMap.lineMap_apply_module]
  module

end AffineLineMapProperties
end ApollonianSuperharmonic

end
