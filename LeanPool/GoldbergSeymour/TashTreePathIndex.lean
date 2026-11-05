/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Data.Nat.Find

public import LeanPool.GoldbergSeymour.TashTreeSuffixPath

/-!
# Tash Tree Path Index

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

/-- The least positive position after which the remaining tree sequence is a path. -/
noncomputable def TashTreePathIndex {V E : Type*} (G : LooplessMultigraph V E) {e0 : E}
    (T : TreeSequence G e0) : ℕ := by
  classical
  exact Nat.find (show ∃ q, TashTreeSuffixPath G T q by
    refine ⟨T.length, T.positive, le_rfl, ?_⟩
    intro i hi
    exact (Nat.not_lt_of_ge hi i.isLt).elim)

end GoldbergSeymour

end
