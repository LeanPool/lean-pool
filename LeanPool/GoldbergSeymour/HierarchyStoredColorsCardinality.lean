/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.HierarchyStoredColorsAt
public import LeanPool.GoldbergSeymour.TashkinovStoredColorsCardinality

/-!
# Hierarchy Stored Colors Cardinality

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem HierarchyStoredColorsCardinality {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {generating phi : PartialEdgeColoring E k}
    {ett : ExtendedTashkinovTree G k e0 input T generating}
    {base : HierarchyBase ett phi} (H : TashkinovHierarchy ett base)
    (j : Fin (H.dividerCount + 1)) :
    (HierarchyStoredColorsAt H j).card ≤ ett.rounds := by
  classical
  let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
  have hsub : HierarchyStoredColorsAt H j ⊆
      TashkinovStoredColors ett.series.data n := by
    intro c hc
    unfold HierarchyStoredColorsAt at hc
    exact (Finset.mem_sdiff.mp hc).1
  calc
    (HierarchyStoredColorsAt H j).card ≤
        (TashkinovStoredColors ett.series.data n).card :=
      Finset.card_le_card hsub
    _ ≤ n.val := TashkinovStoredColorsCardinality G k ett.rounds e0 input
      ett.series n
    _ = ett.rounds := by simp [n]

end GoldbergSeymour

end
