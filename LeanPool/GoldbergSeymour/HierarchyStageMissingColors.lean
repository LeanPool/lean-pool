/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TashkinovHierarchy

/-!
# Hierarchy Stage Missing Colors

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

/-- Missing colors at the ladder base or the corresponding ordinary hierarchy stage. -/
noncomputable def HierarchyStageMissingColors {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    [DecidableEq E] {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input : PartialEdgeColoring E k}
    {T : TreeSequence G e0} {generating phi : PartialEdgeColoring E k}
    {ett : ExtendedTashkinovTree G k e0 input T generating} {base : HierarchyBase ett phi}
    (H : TashkinovHierarchy ett base) (j : Fin (H.dividerCount + 1)) : Finset (Fin k) := by
  classical
  let Tn := ett.series.data.tree (Fin.last ett.rounds).castSucc
  exact Fin.cases (TreeMissingColors phi Tn)
    (fun i : Fin H.dividerCount =>
      TreeMissingColors phi (H.stage i.succ.castSucc)) j

end GoldbergSeymour

end
