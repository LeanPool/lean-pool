/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ExtendedTashkinovTree

/-!
# Extension Base Case One Indices

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

/-- Slots selected from the indexed list strictly before the specified position. -/
noncomputable def ExtensionBaseCaseOneIndices {V E : Type*} [Fintype V] [Fintype E] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input : PartialEdgeColoring E k}
    {T : TreeSequence G e0} {generating : PartialEdgeColoring E k}
    (ett : ExtendedTashkinovTree G k e0 input T generating) (p : ℕ)
    (indices : Fin (p + 1) → Fin ett.rounds) (b : Fin (p + 1)) : Finset (Fin ett.rounds) :=
  (Finset.univ.filter fun a : Fin (p + 1) => a.val < b.val).image indices

end GoldbergSeymour

end
