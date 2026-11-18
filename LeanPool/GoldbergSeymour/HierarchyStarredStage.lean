/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TashkinovHierarchy

/-!
# Hierarchy Starred Stage

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

/-- The base core at index zero and the ordinary preceding stage at later indices. -/
def HierarchyStarredStage {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input : PartialEdgeColoring E k}
    {T : TreeSequence G e0} {generating phi : PartialEdgeColoring E k}
    {ett : ExtendedTashkinovTree G k e0 input T generating} {base : HierarchyBase ett phi}
    (H : TashkinovHierarchy ett base) (j : Fin (H.dividerCount + 1)) : TreeSequence G e0 :=
  Fin.cases base.core (fun i : Fin H.dividerCount => H.stage i.succ.castSucc) j

end GoldbergSeymour

end
