/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Data.Finset.Max

public import LeanPool.GoldbergSeymour.MissingColors
public import LeanPool.GoldbergSeymour.TreeSequence

/-!
# Hierarchy First Missing Position

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

/-- The first vertex position missing a color, defaulting to the final position when none exists. -/
noncomputable def HierarchyFirstMissingPosition {V E : Type*} [Fintype E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} (phi : PartialEdgeColoring E k)
    (T : TreeSequence G e0) (eta : Fin k) : Fin (T.length + 1) := by
  classical
  let candidates : Finset (Fin (T.length + 1)) :=
    Finset.univ.filter fun i => eta ∈ MissingColors G phi (T.vertex i)
  exact if h : candidates.Nonempty then candidates.min' h else Fin.last T.length

end GoldbergSeymour

end
