/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TashkinovSeriesTerminalRoute

public import LeanPool.GoldbergSeymour.HierarchyPrefixData
public import LeanPool.GoldbergSeymour.HierarchyMinimumCounterexampleContext
public import LeanPool.GoldbergSeymour.TashkinovAugmentationSequenceColoringTransport
public import LeanPool.GoldbergSeymour.Td

/-!
# P2752_T2_Full Certificate

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem P2752_T2_FullCertificate {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi sigma : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
    (Bplus : TreeSequence G e0) (F : HierarchyPrefixData C Bplus sigma)
    (hfixed : ∀ t : Fin T.length, sigma (T.edge t) = phi (T.edge t))
    (hstable : StableColoring
      (ett.series.data.tree (Fin.last ett.rounds).castSucc)
      (TashkinovStoredColors ett.series.data (Fin.last ett.rounds)) phi sigma) :
    ∃ corr : CorrespondingExtendedTashkinovTree G k e0 ett sigma T,
      MaximumProperty corr.replacementETT := by
  classical
  let n := Fin.last ett.rounds
  let Tn := ett.series.data.tree n.castSucc
  have hNT : TreeSequenceInitialSegment Tn T := by
    convert ett.abovePenultimate using 1
    congr 1
  have hstrict : Tn.length < T.length := by
    convert ett.strictAbovePenultimate using 1
    congr 1
  have eligible :
      (ett.series.data.kind n = some TashkinovExtensionKind.PE ∧
        TashkinovAugmentationSequence sigma Tn T) ∨
      ((ett.series.data.kind n = some TashkinovExtensionKind.SE ∨
          ett.series.data.kind n = some TashkinovExtensionKind.RE) ∧
        ∃ (f : E) (seed : TreeSequence G e0),
          ett.series.data.connectingEdges n = {f} ∧
            TreeSequenceAdjoinEdge Tn f seed ∧
            TashkinovAugmentationSequence sigma seed T) := by
    exact ett.series.terminalRouteColoringTransport C.positive phi ett.generatingColoring
      T hNT hstrict ett.belowFinal sigma Bplus F.belowFull F.penultimateLength
      (fun t _ => hfixed t) F.invariant.2
  have hmod := Td G k e0 input T phi ett C.maximum C.positive
    ctx.lowerRung sigma F.proper F.oneUncolored
    (by simpa [← ett.generatingColoring] using hstable)
  obtain ⟨corr⟩ := hmod.2.2 T hNT hstrict eligible
  exact ⟨corr, MaximumPropertyTransport G k e0 ett sigma hmod T corr C.maximum⟩

end GoldbergSeymour

end
