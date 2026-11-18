/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P3723T1EdgeContact
public import Mathlib.Init


/-!
# PeriodicEdgeContactSymmetry

Shared facts adapted from Wesley Pegden's Apache-2.0 Trellis formalization of
Levine–Pegden–Smart, replacing repeated implementations at their common dependency level.
-/

@[expose] public section

namespace ApollonianSuperharmonic
namespace PeriodicEdgeContactSymmetry

/-- Shared symmetric identity for PeriodicEdgeContactSymmetry. -/
theorem symmetric :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (a : ι), ∀ (b : ι), P3723T1EdgeContact P
            a b ↔ P3723T1EdgeContact P b a ) := by
  classical
  intro ι P a b
  simp only [P3723T1EdgeContact, ne_comm, Set.inter_comm]

end PeriodicEdgeContactSymmetry
end ApollonianSuperharmonic

end
