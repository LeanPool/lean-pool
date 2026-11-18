/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.Incident

/-!
# Degree

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

/-- The number of edges incident to a vertex, counting parallel edges separately. -/
noncomputable def Degree {V E : Type*} [Fintype E] (G : LooplessMultigraph V E) (v : V) : ℕ := by
  classical
  exact (Finset.univ.filter fun e => Incident G v e).card

end GoldbergSeymour

end
