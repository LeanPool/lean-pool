/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Data.Finset.Max
public import LeanPool.GoldbergSeymour.Degree

/-!
# Maximum Degree

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

/-- The largest vertex degree, with zero included to handle an empty vertex type. -/
noncomputable def MaximumDegree {V E : Type*} [Fintype V] [Fintype E] (G : LooplessMultigraph V E) :
    ℕ := by classical exact (insert 0 (Finset.univ.image fun v => Degree G v)).max' (by simp)

end GoldbergSeymour

end
