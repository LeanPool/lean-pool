/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TashkinovSeriesData
public import LeanPool.GoldbergSeymour.TreeMissingColors

/-!
# Tashkinov Stored Colors

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

/-- Accumulated stored colors up to a stage, excluding colors missing on its tree. -/
noncomputable def TashkinovStoredColors {V E : Type*} [Fintype E]
    {G : LooplessMultigraph V E} {k rounds : ℕ} {e0 : E} (data : TashkinovSeriesData G k rounds e0)
    (i : Fin (rounds + 1)) : Finset (Fin k) := by
  classical
  exact if i.val = 0 then ∅ else
    (Finset.univ.biUnion fun h : Fin (rounds + 1) =>
      if h.val ≤ i.val then data.stored h else ∅) \
      TreeMissingColors (data.coloring i) (data.tree i.castSucc)

end GoldbergSeymour

end
