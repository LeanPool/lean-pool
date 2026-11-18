/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ETTStrongInterchangeable
public import LeanPool.GoldbergSeymour.ExtensionBaseRestorationTrace

public import LeanPool.GoldbergSeymour.TwoColorNontrivialPathComponent

/-!
# Extension Base Restoration Invariant

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

/-- The coloring and component conditions preserved while restoring other support classes. -/
def ExtensionBaseRestorationInvariant {V E : Type*} [Fintype V] [Fintype E] [DecidableEq E]
  {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input : PartialEdgeColoring E k}
  {T : TreeSequence G e0} {generating : PartialEdgeColoring E k}
  (ett : ExtendedTashkinovTree G k e0 input T generating) (terminalSupport : V)
  (hterminalSupport : terminalSupport ∈ TreeSequenceVertexSet T) (jSlot q : Fin ett.rounds)
  (sigmaN : PartialEdgeColoring E k)
  (trace : ExtensionBaseRestorationTrace ett terminalSupport hterminalSupport sigmaN) : Prop :=
 (∀ a : Fin (trace.steps + 1),
   IsProperEdgeColoring G (trace.coloring a) ∧ IsOneEdgeUncolored (trace.coloring a) e0) ∧
  (∀ a : Fin trace.steps,
    trace.slot a ∈ ExtensionBaseRestorationIndices ett terminalSupport hterminalSupport ∧
     TreeVertexOrder T terminalSupport (trace.support a) ∧
      TreeSequenceInitialSegment (ett.series.data.tree jSlot.succ.castSucc)
        (ett.series.data.tree (trace.slot a).succ.castSucc) ∧
       trace.support a ∈ TreeSequenceVertexSet (ett.series.data.tree (trace.slot a).succ.castSucc) ∧
        trace.delta a ∈ MissingColors G (trace.coloring a.castSucc) (trace.support a) ∧
         TwoColorNontrivialPathComponent G (trace.coloring a.castSucc) (trace.gamma a)
           (trace.delta a) (Sum.inl (trace.support a)) ∧
          (∀ w : V,
            w ∈ TreeSequenceVertexSet (ett.series.data.tree (trace.slot a).succ.castSucc) →
             (Sum.inl w ∈
               TwoColorComponent G (trace.coloring a.castSucc) (trace.gamma a) (trace.delta a)
                (Sum.inl (trace.support a)) ↔
              w = trace.support a)) ∧
           ∀ (s : Fin ett.rounds) (vs : V) (gammaS deltaS : Fin k),
            s ∈ ExtensionBaseActiveIndices ett terminalSupport hterminalSupport →
             s ≠ q →
              (∀ b : Fin trace.steps, b.val ≤ a.val → trace.slot b ≠ s) →
               ett.series.data.chosenVertex s.succ = some vs →
                ett.series.data.gamma s.succ = some gammaS →
                 ett.series.data.delta s.succ = some deltaS →
                  ETTStrongInterchangeable ett s vs (trace.coloring a.succ) gammaS deltaS) ∧
   ∀ (s : Fin ett.rounds) (vs : V) (gammaS deltaS : Fin k),
    s ∈ ExtensionBaseActiveIndices ett terminalSupport hterminalSupport →
     s ≠ q →
      (∀ a : Fin trace.steps, trace.slot a ≠ s) →
       ett.series.data.chosenVertex s.succ = some vs →
        ett.series.data.gamma s.succ = some gammaS →
         ett.series.data.delta s.succ = some deltaS →
          ETTStrongInterchangeable ett s vs (trace.coloring (Fin.last trace.steps)) gammaS deltaS

end GoldbergSeymour

end
