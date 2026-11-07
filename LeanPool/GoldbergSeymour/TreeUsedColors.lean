/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TreeSequence
public import LeanPool.GoldbergSeymour.PartialEdgeColoring
public import Mathlib.Data.Fintype.Basic

/-!
# Tree Used Colors

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

/-- Colors assigned to noninitial tree edges. -/
noncomputable def TreeUsedColors {V E : Type*} {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0) : Finset (Fin k) := by
  classical
  exact Finset.univ.filter fun alpha =>
    ∃ j : Fin T.length, 1 ≤ j.val ∧ phi (T.edge j) = some alpha

end GoldbergSeymour

end
