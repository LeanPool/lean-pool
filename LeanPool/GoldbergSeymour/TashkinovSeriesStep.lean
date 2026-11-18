/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ColoredVertexSetStronglyClosed
public import LeanPool.GoldbergSeymour.KTriple
public import LeanPool.GoldbergSeymour.MaximumDefectiveChoice
public import LeanPool.GoldbergSeymour.ParallelExtensionColor
public import LeanPool.GoldbergSeymour.RevisitingExtensionCertificate
public import LeanPool.GoldbergSeymour.TashkinovClosure
public import LeanPool.GoldbergSeymour.TashkinovStoredColors
public import LeanPool.GoldbergSeymour.TreeExit
public import LeanPool.GoldbergSeymour.TreeSequenceAdjoinEdge
public import LeanPool.GoldbergSeymour.TwoColorComponentSwap

/-!
# Tashkinov Series Step

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

/-- The initial and extension rules certifying a stage of a Tashkinov series. -/
inductive TashkinovSeriesStep {V E : Type*} [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k rounds : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
    (data : TashkinovSeriesData G k rounds e0) : Fin (rounds + 1) → Prop where
  |
  initial (triple : KTriple G k e0 input) (seedLength : (data.tree 0).length = 1)
    (initialColoring : data.coloring 0 = input) (initialStored : data.stored 0 = ∅)
    (initialEdges : data.connectingEdges 0 = ∅) (initialKind : data.kind 0 = none)
    (initialVertex : data.chosenVertex 0 = none) (initialOutside : data.outsideVertex 0 = none)
    (initialDelta : data.delta 0 = none) (initialGamma : data.gamma 0 = none)
    (initialClosure : TashkinovClosure (data.coloring 0) (data.tree 0) (data.tree 1)) :
    TashkinovSeriesStep G k rounds e0 input data 0
  |
  SE (i : Fin rounds) (previousProper : IsProperEdgeColoring G (data.coloring i.castSucc))
    (previousOneUncolored : IsOneEdgeUncolored (data.coloring i.castSucc) e0)
    (previousClosed :
      ColoredVertexSetClosed G (data.coloring i.castSucc)
        (TreeSequenceVertexSet (data.tree i.succ.castSucc)))
    (previousNotStronglyClosed :
      ¬ColoredVertexSetStronglyClosed G (data.coloring i.castSucc)
          (TreeSequenceVertexSet (data.tree i.succ.castSucc)))
    (noRevisiting : ¬Nonempty (RevisitingExtensionCertificate data i.castSucc))
    (choice :
      MaximumDefectiveChoice G e0 (data.tree i.succ.castSucc)
        (TashkinovStoredColors data i.castSucc) (data.coloring i.castSucc))
    (seriesAlternative :
      ∀ pi : PartialEdgeColoring E k,
        IsProperEdgeColoring G pi →
          IsOneEdgeUncolored pi e0 →
            StableColoring (data.tree i.succ.castSucc)
                (insert choice.color (TashkinovStoredColors data i.castSucc)) choice.selected pi →
              Disjoint (MissingColors G pi choice.otherEndpoint)
                (TreeMissingColors pi (data.tree i.succ.castSucc)))
    (currentColoring : data.coloring i.succ = choice.selected)
    (currentStored : data.stored i.succ = { choice.color })
    (currentEdges : data.connectingEdges i.succ = { choice.edge })
    (currentKind : data.kind i.succ = some TashkinovExtensionKind.SE)
    (currentVertex : data.chosenVertex i.succ = some choice.vertex)
    (currentOutside : data.outsideVertex i.succ = some choice.otherEndpoint)
    (currentDelta : data.delta i.succ = some choice.color) (currentGamma : data.gamma i.succ = none)
    (adjoined : TreeSequence G e0)
    (adjoinedExactly : TreeSequenceAdjoinEdge (data.tree i.succ.castSucc) choice.edge adjoined)
    (closedExtension : TashkinovClosure (data.coloring i.succ) adjoined (data.tree i.succ.succ))
    (orderedExtension :
      TreeSequenceInitialSegment (data.tree i.succ.castSucc) (data.tree i.succ.succ))
    (strictExtension : (data.tree i.succ.castSucc).length < (data.tree i.succ.succ).length) :
    TashkinovSeriesStep G k rounds e0 input data i.succ
  |
  PE (i : Fin rounds) (previousProper : IsProperEdgeColoring G (data.coloring i.castSucc))
    (previousOneUncolored : IsOneEdgeUncolored (data.coloring i.castSucc) e0)
    (previousClosed :
      ColoredVertexSetClosed G (data.coloring i.castSucc)
        (TreeSequenceVertexSet (data.tree i.succ.castSucc)))
    (previousNotStronglyClosed :
      ¬ColoredVertexSetStronglyClosed G (data.coloring i.castSucc)
          (TreeSequenceVertexSet (data.tree i.succ.castSucc)))
    (noRevisiting : ¬Nonempty (RevisitingExtensionCertificate data i.castSucc))
    (choice :
      MaximumDefectiveChoice G e0 (data.tree i.succ.castSucc)
        (TashkinovStoredColors data i.castSucc) (data.coloring i.castSucc))
    (seriesAlternativeFails :
      ∃ rho : PartialEdgeColoring E k,
        IsProperEdgeColoring G rho ∧
          IsOneEdgeUncolored rho e0 ∧
            StableColoring (data.tree i.succ.castSucc)
                (insert choice.color (TashkinovStoredColors data i.castSucc)) choice.selected rho ∧
              ¬Disjoint (MissingColors G rho choice.otherEndpoint)
                  (TreeMissingColors rho (data.tree i.succ.castSucc)))
    (gamma : Fin k)
    (gammaRule : ParallelExtensionColor data i.castSucc choice.selected choice.vertex gamma)
    (secondStable : PartialEdgeColoring E k)
    (secondStableProper : IsProperEdgeColoring G secondStable)
    (secondStableOneUncolored : IsOneEdgeUncolored secondStable e0)
    (secondStableRelation :
      StableColoring (data.tree i.succ.castSucc)
        (insert choice.color (TashkinovStoredColors data i.castSucc)) choice.selected secondStable)
    (exitWitness :
      TreeExit (data.tree i.succ.castSucc) secondStable gamma choice.color choice.vertex)
    (currentColoring :
      data.coloring i.succ =
        TwoColorComponentSwap G secondStable gamma choice.color (Sum.inl choice.vertex))
    (currentProper : IsProperEdgeColoring G (data.coloring i.succ))
    (currentOneUncolored : IsOneEdgeUncolored (data.coloring i.succ) e0)
    (currentStored : data.stored i.succ = { choice.color, gamma })
    (currentEdges : data.connectingEdges i.succ = { choice.edge })
    (currentKind : data.kind i.succ = some TashkinovExtensionKind.PE)
    (currentVertex : data.chosenVertex i.succ = some choice.vertex)
    (currentOutside : data.outsideVertex i.succ = some choice.otherEndpoint)
    (currentDelta : data.delta i.succ = some choice.color)
    (currentGamma : data.gamma i.succ = some gamma)
    (closedExtension :
      TashkinovClosure (data.coloring i.succ) (data.tree i.succ.castSucc) (data.tree i.succ.succ))
    (orderedExtension :
      TreeSequenceInitialSegment (data.tree i.succ.castSucc) (data.tree i.succ.succ))
    (strictExtension : (data.tree i.succ.castSucc).length < (data.tree i.succ.succ).length) :
    TashkinovSeriesStep G k rounds e0 input data i.succ
  |
  RE (i : Fin rounds) (previousProper : IsProperEdgeColoring G (data.coloring i.castSucc))
    (previousOneUncolored : IsOneEdgeUncolored (data.coloring i.castSucc) e0)
    (previousClosed :
      ColoredVertexSetClosed G (data.coloring i.castSucc)
        (TreeSequenceVertexSet (data.tree i.succ.castSucc)))
    (previousNotStronglyClosed :
      ¬ColoredVertexSetStronglyClosed G (data.coloring i.castSucc)
          (TreeSequenceVertexSet (data.tree i.succ.castSucc)))
    (available : RevisitingExtensionCertificate data i.castSucc)
    (currentColoring : data.coloring i.succ = data.coloring i.castSucc)
    (currentStored : data.stored i.succ = { available.delta, available.gamma })
    (currentEdges : data.connectingEdges i.succ = { available.edge })
    (currentKind : data.kind i.succ = some TashkinovExtensionKind.RE)
    (currentVertex : data.chosenVertex i.succ = some available.insideEndpoint)
    (currentOutside : data.outsideVertex i.succ = some available.outsideEndpoint)
    (currentDelta : data.delta i.succ = some available.delta)
    (currentGamma : data.gamma i.succ = some available.gamma) (adjoined : TreeSequence G e0)
    (adjoinedExactly : TreeSequenceAdjoinEdge (data.tree i.succ.castSucc) available.edge adjoined)
    (closedExtension : TashkinovClosure (data.coloring i.succ) adjoined (data.tree i.succ.succ))
    (orderedExtension :
      TreeSequenceInitialSegment (data.tree i.succ.castSucc) (data.tree i.succ.succ))
    (strictExtension : (data.tree i.succ.castSucc).length < (data.tree i.succ.succ).length) :
    TashkinovSeriesStep G k rounds e0 input data i.succ

end GoldbergSeymour

end
