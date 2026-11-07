/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ETTFirstAppearanceIndex

/-!
# Extension Base Active Indices

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

/-- Parallel-extension indices at or after the terminal support's first appearance whose supports
appeared no later.
-/
noncomputable def ExtensionBaseActiveIndices {V E : Type*} [Fintype V] [Fintype E] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input : PartialEdgeColoring E k}
    {T : TreeSequence G e0} {generating : PartialEdgeColoring E k}
    (ett : ExtendedTashkinovTree G k e0 input T generating) (terminalSupport : V)
    (hterminalSupport : terminalSupport ∈ TreeSequenceVertexSet T) : Finset (Fin ett.rounds) := by
  classical
  let j := ETTFirstAppearanceIndex ett terminalSupport hterminalSupport
  exact Finset.univ.filter fun s =>
    j ≤ s.val + 1 ∧
      ett.series.data.kind s.succ = some TashkinovExtensionKind.PE ∧
      ∃ v : V, ∃ hv : v ∈ TreeSequenceVertexSet T,
        ett.series.data.chosenVertex s.succ = some v ∧
          ETTFirstAppearanceIndex ett v hv ≤ j

end GoldbergSeymour

end
