/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ColoredVertexSetElementary

public import LeanPool.GoldbergSeymour.TashkinovClosure
public import LeanPool.GoldbergSeymour.TchangeCounterexample

public import LeanPool.GoldbergSeymour.TwoColorComponentSwap

/-!
# Tchange Kempe Closure Data

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

/-- The swapped coloring, successive augmentations and transported exit paths used in the color-
change argument.
-/
structure TchangeKempeClosureData {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    [DecidableEq E] {G : LooplessMultigraph V E} {k : Nat} {e0 : E}
    (C : TchangeCounterexample G k e0) where
  /-- The replacement coloring constrained by this certificate. -/
  sigma : PartialEdgeColoring E k
  /-- The initial tree prefix before the component-swap augmentations. -/
  baseTree : TreeSequence G e0
  /-- The tree after the first augmentation. -/
  oneTree : TreeSequence G e0
  /-- The tree after the second augmentation. -/
  twoTree : TreeSequence G e0
  /-- The closed tree reached by the subsequent augmentation sequence. -/
  closedTree : TreeSequence G e0
  sigmaEq : sigma = TwoColorComponentSwap G C.phi C.a C.b (Sum.inl C.b3)
  baseInitial : TreeSequenceInitialSegment baseTree C.T
  baseLast : baseTree.vertex (Fin.last baseTree.length) = C.b3
  b1InBase : C.b1 ∈ TreeSequenceVertexSet baseTree
  b2InBase : C.b2 ∈ TreeSequenceVertexSet baseTree
  baseIsTree : TashkinovTree G e0 sigma baseTree
  firstAugmentation : TashkinovAugmentation sigma baseTree oneTree
  secondAugmentation : TashkinovAugmentation sigma oneTree twoTree
  closureRoute : TashkinovClosure sigma twoTree closedTree
  triple : KTriple G k e0 sigma
  closureTree : TashkinovTree G e0 sigma closedTree
  closureClosed : ColoredVertexSetClosed G sigma (TreeSequenceVertexSet closedTree)
  closureElementary : ColoredVertexSetElementary G sigma (TreeSequenceVertexSet closedTree)
  betaMissing : C.b ∈ MissingColors G sigma C.b3
  b1InClosure : C.b1 ∈ TreeSequenceVertexSet closedTree
  b2InClosure : C.b2 ∈ TreeSequenceVertexSet closedTree
  b3InClosure : C.b3 ∈ TreeSequenceVertexSet closedTree
  a1Outside : C.a1 ∉ TreeSequenceVertexSet closedTree
  a2Outside : C.a2 ∉ TreeSequenceVertexSet closedTree
  a3Outside : C.a3 ∉ TreeSequenceVertexSet closedTree
  f1EndsInside : ∀ v, Incident G v C.f1 → v ∈ TreeSequenceVertexSet closedTree
  /-- The first two-color exit walk. -/
  Q1 : (TwoColorIncidenceGraph G sigma C.a C.b).Walk (Sum.inl C.a1) (Sum.inl C.b1)
  /-- The second two-color exit walk. -/
  Q2 : (TwoColorIncidenceGraph G sigma C.a C.b).Walk (Sum.inl C.a2) (Sum.inl C.b2)
  /-- The third two-color exit walk. -/
  Q3 : (TwoColorIncidenceGraph G sigma C.a C.b).Walk (Sum.inl C.a3) (Sum.inl C.b3)
  exit1 : TreeExitPath C.T sigma C.a C.b C.a1 C.b1 Q1
  exit2 : TreeExitPath C.T sigma C.a C.b C.a2 C.b2 Q2
  exit3 : TreeExitPath C.T sigma C.a C.b C.a3 C.b3 Q3
  support1 : Q1.support = C.P1.support
  support2 : Q2.support = C.P2.support
  support3 : Q3.support = C.P3.support
  length1 : Q1.length = C.P1.length
  length2 : Q2.length = C.P2.length
  length3 : Q3.length = C.P3.length

end GoldbergSeymour

end
