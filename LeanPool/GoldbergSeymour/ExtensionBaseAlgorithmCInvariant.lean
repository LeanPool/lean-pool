/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ETTStrongInterchangeable
public import LeanPool.GoldbergSeymour.ExtensionBaseAlgorithmCTrace

public import LeanPool.GoldbergSeymour.TwoColorNontrivialPathComponent

/-!
# Extension Base Algorithm CInvariant

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

/--
Properness, path-component and preservation conditions along Algorithm C's support-class swaps. -/
def ExtensionBaseAlgorithmCInvariant {V E : Type*} [Fintype V] [Fintype E] [DecidableEq E]
  {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input : PartialEdgeColoring E k}
  {T : TreeSequence G e0} {generating : PartialEdgeColoring E k}
  (ett : ExtendedTashkinovTree G k e0 input T generating) (terminalSupport : V)
  (hterminalSupport : terminalSupport ∈ TreeSequenceVertexSet T)
  (terminalSlot jSlot : Fin ett.rounds) (mu0 : PartialEdgeColoring E k) (u : V)
  (trace : ExtensionBaseAlgorithmCTrace ett terminalSupport hterminalSupport terminalSlot mu0 u) :
  Prop :=
 (∀ a : Fin (trace.steps + 1),
   IsProperEdgeColoring G (trace.coloring a) ∧ IsOneEdgeUncolored (trace.coloring a) e0) ∧
  (∀ a : Fin trace.steps,
    TreeSequenceInitialSegment (ett.series.data.tree jSlot.succ.castSucc)
      (ett.series.data.tree (trace.slot a).succ.castSucc) ∧
     trace.delta a ∈ MissingColors G (trace.coloring a.castSucc) u ∧
      TwoColorNontrivialPathComponent G (trace.coloring a.castSucc) (trace.gamma a) (trace.delta a)
        (Sum.inl u) ∧
       (∀ w : V,
         w ∈ TreeSequenceVertexSet (ett.series.data.tree (trace.slot a).succ.castSucc) →
          Sum.inl w ∈
            TwoColorComponent G (trace.coloring a.castSucc) (trace.gamma a) (trace.delta a)
             (Sum.inl u) →
           w = terminalSupport) ∧
        (Sum.inl terminalSupport ∈
           TwoColorComponent G (trace.coloring a.castSucc) (trace.gamma a) (trace.delta a)
            (Sum.inl u) →
          ¬Set.Subsingleton
            ((TwoColorIncidenceGraph G (trace.coloring a.castSucc) (trace.gamma a)
               (trace.delta a)).neighborSet
             (Sum.inl terminalSupport))) ∧
         ∀ (s : Fin ett.rounds) (gammaS deltaS : Fin k),
          s ∈
            (ExtensionBaseSupportClass ett terminalSupport hterminalSupport terminalSupport).erase
             terminalSlot →
           (∀ b : Fin trace.steps, b.val ≤ a.val → trace.slot b ≠ s) →
            ett.series.data.chosenVertex s.succ = some terminalSupport →
             ett.series.data.gamma s.succ = some gammaS →
              ett.series.data.delta s.succ = some deltaS →
               ETTStrongInterchangeable ett s terminalSupport (trace.coloring a.succ) gammaS
                deltaS) ∧
   ∀ (s : Fin ett.rounds) (gammaS deltaS : Fin k),
    s ∈
      (ExtensionBaseSupportClass ett terminalSupport hterminalSupport terminalSupport).erase
       terminalSlot →
     (∀ a : Fin trace.steps, trace.slot a ≠ s) →
      ett.series.data.chosenVertex s.succ = some terminalSupport →
       ett.series.data.gamma s.succ = some gammaS →
        ett.series.data.delta s.succ = some deltaS →
         ETTStrongInterchangeable ett s terminalSupport (trace.coloring (Fin.last trace.steps))
          gammaS deltaS

end GoldbergSeymour

end
