/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.HierarchySituationOnePenultimateCommonMissing
public import LeanPool.GoldbergSeymour.HierarchySituationOneShorteningContradiction

/-!
# Hierarchy Situation One Impossible

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem HierarchySituationOneImpossible {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi)
    (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext
      G k e0 input T phi ett base C)
    (hsituation : HierarchyPathNumber C.hierarchy = 1)
    (hvertexMissing : ∀ (mu : PartialEdgeColoring E k),
      IsProperEdgeColoring G mu → IsOneEdgeUncolored mu e0 →
        ∀ v : V, (MissingColors G mu v).Nonempty) : False := by
  have hnonempty := HierarchyClaimNine G k e0 input T phi ett base C ctx
    hsituation hvertexMissing
  have hlast := HierarchySituationOnePenultimateCommonMissing G k e0 input T phi
    ett base C ctx hsituation hvertexMissing hnonempty
  exact HierarchySituationOneShorteningContradiction G k e0 input T phi ett base C
    ctx hsituation hlast

end GoldbergSeymour

end
