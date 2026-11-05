/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.HierarchyFullTailPrefix

public import LeanPool.GoldbergSeymour.HierarchyReplacementPresentation

public import LeanPool.GoldbergSeymour.HierarchyWeaklyStable

/-!
# P2880_T1_Split Swap Data

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

/-- The component-swap, missing-color, invariant-prefix and suffix-route certificates for a
hierarchy split.
-/
structure P2880_T1_SplitSwapData {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    [DecidableEq E] (G : LooplessMultigraph V E) (k : Nat) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
    (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
    (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (alpha beta : Fin k)
    (sigma : PartialEdgeColoring E k) where
  swapped :
    sigma = TwoColorComponentSwap G P.coloring alpha beta (Sum.inl (T.vertex (Fin.last T.length)))
  distinct : alpha ≠ beta
  path : TwoColorPathComponent G P.coloring alpha beta (Sum.inl (T.vertex (Fin.last T.length)))
  splitOutside :
    ∀ v ∈ TreeSequenceVertexSet (HierarchyFullTailPrefix C (HierarchyPathNumber C.hierarchy - 1)),
      Sum.inl v ∉ TwoColorComponent G P.coloring alpha beta (Sum.inl (T.vertex (Fin.last T.length)))
  twoBeforeInSplit :
    TreeSequenceInitialSegment (HierarchyFullTailPrefix C (HierarchyPathNumber C.hierarchy - 2))
      (HierarchyFullTailPrefix C (HierarchyPathNumber C.hierarchy - 1))
  splitInFull :
    TreeSequenceInitialSegment (HierarchyFullTailPrefix C (HierarchyPathNumber C.hierarchy - 1)) T
  splitAboveStar :
    let H := P.counterexample.hierarchy
    let A := HierarchyStarredStage H (Fin.last H.dividerCount)
    let X := HierarchyFullTailPrefix C (HierarchyPathNumber C.hierarchy - 1)
    TreeSequenceInitialSegment A X ∧ A.length < X.length
  splitInPenultimate :
    TreeSequenceInitialSegment (HierarchyFullTailPrefix C (HierarchyPathNumber C.hierarchy - 1))
      (HierarchyFullTailPrefix P.counterexample (HierarchyFullTailLength P.counterexample - 1))
  coreInSplit :
    TreeSequenceInitialSegment P.replacementBase.core
      (HierarchyFullTailPrefix C (HierarchyPathNumber C.hierarchy - 1))
  penultimateElementary :
    ColoredVertexSetElementary G P.coloring
      (TreeSequenceVertexSet
        (HierarchyFullTailPrefix P.counterexample (HierarchyFullTailLength P.counterexample - 1)))
  proper : IsProperEdgeColoring G sigma
  oneEdgeUncolored : IsOneEdgeUncolored sigma e0
  invariant :
    TreeColoringInvariant (HierarchyFullTailPrefix C (HierarchyPathNumber C.hierarchy - 1))
      P.coloring sigma
  incidentFixed :
    ∀ v ∈ TreeSequenceVertexSet (HierarchyFullTailPrefix C (HierarchyPathNumber C.hierarchy - 1)),
      ∀ f : E, Incident G v f → sigma f = P.coloring f
  fixedOnSplit :
    ∀ r : Fin T.length,
      r.val < (HierarchyFullTailPrefix C (HierarchyPathNumber C.hierarchy - 1)).length →
        sigma (T.edge r) = P.coloring (T.edge r)
  fixedThroughJ :
    let H := P.counterexample.hierarchy
    let A := HierarchyStarredStage H (Fin.last H.dividerCount)
    let j := HierarchyPathNumber C.hierarchy
    ∀ r : Fin T.length,
      A.length ≤ r.val → r.val < A.length + j → sigma (T.edge r) = P.coloring (T.edge r)
  missingTwoBefore :
    let B := HierarchyFullTailPrefix C (HierarchyPathNumber C.hierarchy - 2)
    alpha ∈ TreeMissingColors sigma B ∧ beta ∈ TreeMissingColors sigma B
  missingOnSplit :
    let X := HierarchyFullTailPrefix C (HierarchyPathNumber C.hierarchy - 1)
    alpha ∈ TreeMissingColors sigma X ∧ beta ∈ TreeMissingColors sigma X
  oldMissingOnPenultimate :
    let B := HierarchyFullTailPrefix P.counterexample (HierarchyFullTailLength P.counterexample - 1)
    alpha ∈ TreeMissingColors P.coloring B ∧ beta ∈ TreeMissingColors P.coloring B
  missingTerminal : beta ∈ MissingColors G sigma (T.vertex (Fin.last T.length))
  penultimateMissing :
    ∀
      v ∈
        TreeSequenceVertexSet
          (HierarchyFullTailPrefix P.counterexample (HierarchyFullTailLength P.counterexample - 1)),
      MissingColors G sigma v = MissingColors G P.coloring v
  storedFirst :
    let H := P.counterexample.hierarchy
    let q := Fin.last H.dividerCount
    ∀ eta ∈ HierarchyStoredColorsAt H q,
      HierarchyFirstMissingPosition sigma T eta = HierarchyFirstMissingPosition P.coloring T eta
  gammaCutoff :
    let H := P.counterexample.hierarchy
    let q := Fin.last H.dividerCount
    let X := HierarchyFullTailPrefix C (HierarchyPathNumber C.hierarchy - 1)
    ∀ eta ∈ HierarchyStoredColorsAt H q,
      (alpha ∈ P.counterexample.good.gamma q eta ∨ beta ∈ P.counterexample.good.gamma q eta) →
        (HierarchyFirstMissingPosition P.coloring T eta).val ≤ X.length
  separatedAlpha :
    Disjoint (TwoColorComponent G P.coloring alpha beta (Sum.inl (T.vertex (Fin.last T.length))))
      (TwoColorComponent G P.coloring alpha beta
        (Sum.inl (T.vertex (HierarchyFirstMissingPosition P.coloring T alpha))))
  separatedBeta :
    Disjoint (TwoColorComponent G P.coloring alpha beta (Sum.inl (T.vertex (Fin.last T.length))))
      (TwoColorComponent G P.coloring alpha beta
        (Sum.inl (T.vertex (HierarchyFirstMissingPosition P.coloring T beta))))
  prefixRoute :
    let m := P.corresponding.replacementETT
    let n := Fin.last m.rounds
    let Tn := m.series.data.tree n.castSucc
    let X := HierarchyFullTailPrefix C (HierarchyPathNumber C.hierarchy - 1)
    (m.series.data.kind n = some TashkinovExtensionKind.PE ∧
        TashkinovAugmentationSequence sigma Tn X) ∨
      ((m.series.data.kind n = some TashkinovExtensionKind.SE ∨
          m.series.data.kind n = some TashkinovExtensionKind.RE) ∧
        ∃ (f : E) (seed : TreeSequence G e0),
          m.series.data.connectingEdges n = { f } ∧
            TreeSequenceAdjoinEdge Tn f seed ∧ TashkinovAugmentationSequence sigma seed X)
  oldSuffix :
    TashkinovAugmentationSequence P.coloring
      (HierarchyFullTailPrefix C (HierarchyPathNumber C.hierarchy - 1)) T
  newSuffix :
    TashkinovAugmentationSequence sigma
      (HierarchyFullTailPrefix C (HierarchyPathNumber C.hierarchy - 1)) T

end GoldbergSeymour

end
