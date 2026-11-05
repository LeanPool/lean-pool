/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.HierarchyCounterexampleLess
public import LeanPool.GoldbergSeymour.LowerRoundProperties
public import LeanPool.GoldbergSeymour.HierarchyCounterexampleMeasure

/-!
# Hierarchy Minimum Counterexample Context

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

/-- Induction hypotheses and minimality conditions for a non-elementary good hierarchy. -/
structure HierarchyMinimumCounterexampleContext {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
    (C : HierarchyCounterexample base) where
  proper : IsProperEdgeColoring G phi
  oneEdgeUncolored : IsOneEdgeUncolored phi e0
  lowerRung :
    ∀ {input' : PartialEdgeColoring E k} {T' : TreeSequence G e0}
        {generating' : PartialEdgeColoring E k} (lower : ExtendedTashkinovTree G k e0 input' T'
        generating'), 0 < lower.rounds → lower.rounds < ett.rounds → MaximumProperty lower → (open
        scoped Classical in LowerRoundProperties lower)
  fewerDividers :
    ∀ {input' : PartialEdgeColoring E k} {T' : TreeSequence G e0}
        {generating' : PartialEdgeColoring E k} (other : ExtendedTashkinovTree G k e0 input' T'
        generating'), other.rounds = ett.rounds → MaximumProperty other →
    ∀ (base' : HierarchyBase other generating') (K : TashkinovHierarchy other base'),
        GoodHierarchy K → K.dividerCount < C.hierarchy.dividerCount → ColoredVertexSetElementary G
        generating' (TreeSequenceVertexSet T')
  lexicographicMinimality :
    ∀ {input' : PartialEdgeColoring E k} {T' : TreeSequence G e0}
      {generating' : PartialEdgeColoring E k}
      {other : ExtendedTashkinovTree G k e0 input' T' generating'}
      {base' : HierarchyBase other generating'} (C' : HierarchyCounterexample base'),
      other.rounds = ett.rounds →
        C'.hierarchy.dividerCount = C.hierarchy.dividerCount →
          ¬HierarchyCounterexampleLess (HierarchyCounterexampleMeasure C')
              (HierarchyCounterexampleMeasure C)
  largeMissingSet :
    let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
    let Tn := ett.series.data.tree n.castSucc
    2 * ett.rounds + 11 ≤ (TreeMissingColors phi Tn).card

end GoldbergSeymour

end
