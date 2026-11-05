/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ParallelTerminalFacts
public import LeanPool.GoldbergSeymour.ColoredVertexSetElementary

public import LeanPool.GoldbergSeymour.TashkinovClosureVertexSetUnique
public import LeanPool.GoldbergSeymour.TreeSequenceInitialSegmentVertexSetSubset

/-!
# P2634_T1_Closed Core Elementary

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem P2634_T1_ClosedCoreElementary
    {V E : Type*} [Fintype V] [Fintype E]
     [DecidableEq E]
    {G : LooplessMultigraph V E} {k : Nat} {e0 : E}
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {phi : PartialEdgeColoring E k}
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (hPE : ett.series.data.kind (Fin.last ett.rounds) =
      some TashkinovExtensionKind.PE)
    (core : TreeSequence G e0)
    (hroute : TashkinovAugmentationSequence phi
      (ett.series.data.tree (Fin.last ett.rounds).castSucc) core)
    (helem : ColoredVertexSetElementary G phi (TreeSequenceVertexSet core))
    (hclosed : ColoredVertexSetClosed G phi (TreeSequenceVertexSet core)) :
    ColoredVertexSetElementary G phi (TreeSequenceVertexSet T) := by
  classical
  have hfinal := (P2634_T1_PETerminalFacts ett hPE).2.2
  have hvertices := TashkinovClosureVertexSetUnique phi
    (ett.series.data.tree (Fin.last ett.rounds).castSucc) core
    (ett.series.data.tree (Fin.last (ett.rounds + 1)))
    ⟨hroute, hclosed⟩ hfinal
  have hsubset := TreeSequenceInitialSegmentVertexSetSubset ett.belowFinal
  rw [← hvertices] at hsubset
  intro u hu v hv hne
  exact helem (hsubset hu) (hsubset hv) hne

end GoldbergSeymour

end
