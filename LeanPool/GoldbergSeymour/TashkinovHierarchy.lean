/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.HierarchyBase

/-!
# Tashkinov Hierarchy

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

/-- A strictly nested sequence of stages with ordered divider positions above a hierarchy base. -/
structure TashkinovHierarchy {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input : PartialEdgeColoring E k}
    {T : TreeSequence G e0} {generating phi : PartialEdgeColoring E k}
    (ett : ExtendedTashkinovTree G k e0 input T generating) (base : HierarchyBase ett phi) where
  /-- The number of internal divider positions in the hierarchy. -/
  dividerCount : ℕ
  /-- The ordered hierarchy stages, including the initial and final stages. -/
  stage : Fin (dividerCount + 2) → TreeSequence G e0
  baseStage : stage 0 = ett.series.data.tree (Fin.last ett.rounds).castSucc
  terminalStage : stage (Fin.last (dividerCount + 1)) = T
  nested :
    ∀ j : Fin (dividerCount + 1), TreeSequenceInitialSegment (stage j.castSucc) (stage j.succ)
  strict : ∀ j : Fin (dividerCount + 1), (stage j.castSucc).length < (stage j.succ).length
  /-- The increasing tree-vertex position of each internal divider. -/
  dividerPosition : Fin dividerCount → Fin (T.length + 1)
  dividerPositive : ∀ i, 1 ≤ (dividerPosition i).val
  dividerIncreasing : ∀ i j, i.val < j.val → (dividerPosition i).val < (dividerPosition j).val
  dividerStage :
    ∀ i : Fin dividerCount,
      stage ⟨i.val + 1, by omega⟩ =
        TreeSequencePrefix T (dividerPosition i).val (dividerPositive i)
          (Nat.le_of_lt_succ (dividerPosition i).isLt)
  coreInsideFirst : TreeSequenceInitialSegment base.core (stage ⟨1, by omega⟩)

end GoldbergSeymour

end
