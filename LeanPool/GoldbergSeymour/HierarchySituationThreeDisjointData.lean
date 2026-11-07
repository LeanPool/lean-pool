/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.HierarchyFullTailPrefix

public import LeanPool.GoldbergSeymour.HierarchyReplacementPresentation

public import LeanPool.GoldbergSeymour.TreeColoringInvariant

/-!
# Hierarchy Situation Three Disjoint Data

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

/-- A switched replacement presentation and missing-color witnesses for the disjoint-component case
of situation three.
-/
structure HierarchySituationThreeDisjointData {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    [DecidableEq E] (G : LooplessMultigraph V E) (k : Nat) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
    (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
    (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
    (alpha beta : Fin k) where
  /-- The replacement presentation after the designated component swap. -/
  switched : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx
  switchedColoring :
    switched.coloring =
      TwoColorComponentSwap G P.coloring alpha beta (Sum.inl (T.vertex (Fin.last T.length)))
  proper : IsProperEdgeColoring G switched.coloring
  oneEdgeUncolored : IsOneEdgeUncolored switched.coloring e0
  invariantOnSplit :
    let j := HierarchyPathNumber C.hierarchy
    let X := HierarchyFullTailPrefix C (j - 1)
    TreeColoringInvariant X P.coloring switched.coloring
  affectedMissingOnSplit :
    let j := HierarchyPathNumber C.hierarchy
    let X := HierarchyFullTailPrefix C (j - 1)
    alpha ∈ TreeMissingColors switched.coloring X ∧ beta ∈ TreeMissingColors switched.coloring X
  transportedSuffix :
    let j := HierarchyPathNumber C.hierarchy
    let X := HierarchyFullTailPrefix C (j - 1)
    TashkinovAugmentationSequence switched.coloring X T
  betaMissingTerminal : beta ∈ MissingColors G switched.coloring (T.vertex (Fin.last T.length))
  betaMissingTwoBeforeWitness :
    let j := HierarchyPathNumber C.hierarchy
    let B := HierarchyFullTailPrefix C (j - 2)
    ∃ v ∈ TreeSequenceVertexSet B, beta ∈ MissingColors G switched.coloring v
  betaOutsideGamma :
    let H := switched.counterexample.hierarchy
    let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
    let D := HierarchyStoredColorsAt H q
    let Gamma := D.biUnion (switched.counterexample.good.gamma q)
    beta ∉ Gamma
  conditionNine :
    let H := switched.counterexample.hierarchy
    let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
    let A := HierarchyStarredStage H q
    let j := HierarchyPathNumber C.hierarchy
    let B := HierarchyFullTailPrefix C (j - 2)
    let n : Fin (switched.corresponding.replacementETT.rounds + 1) :=
      Fin.last switched.corresponding.replacementETT.rounds
    let Tn := switched.corresponding.replacementETT.series.data.tree n.castSucc
    let D := HierarchyStoredColorsAt H q
    let Gamma := D.biUnion (switched.counterexample.good.gamma q)
    let baseExtraMissing :=
      ((TreeSequenceVertexSet switched.replacementBase.core \ TreeSequenceVertexSet Tn).biUnion
        fun v => MissingColors G switched.coloring v)
    let tailUsedThroughJ :=
      (Finset.univ : Finset (Fin k)).filter fun c =>
        ∃ r : Fin T.length,
          A.length ≤ r.val ∧ r.val < A.length + j ∧ switched.coloring (T.edge r) = some c
    (beta ∉ baseExtraMissing ∧ beta ∉ tailUsedThroughJ ∧ beta ∉ Gamma ∧ beta ∉ D) ∨
      (beta ∈ D ∧
        beta ∈ TreeMissingColors switched.coloring B ∧
          Disjoint (switched.counterexample.good.gamma q beta ∪ { beta }) tailUsedThroughJ)
  /-- The auxiliary color with the missing-color conditions recorded below. -/
  theta : Fin k
  thetaMissingAtJ :
    let j := HierarchyPathNumber C.hierarchy
    let Y := HierarchyFullTailPrefix C j
    theta ∈ MissingColors G switched.coloring (Y.vertex (Fin.last Y.length))
  thetaOutsideGamma :
    let H := switched.counterexample.hierarchy
    let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
    let D := HierarchyStoredColorsAt H q
    let Gamma := D.biUnion (switched.counterexample.good.gamma q)
    theta ∉ Gamma

namespace HierarchySituationThreeDisjointData

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  {G : LooplessMultigraph V E} {k : Nat} {e0 : E} {input : PartialEdgeColoring E k}
  {T : TreeSequence G e0} {phi : PartialEdgeColoring E k}
  {ett : ExtendedTashkinovTree G k e0 input T phi} {base : HierarchyBase ett phi}
  {C : HierarchyCounterexample base}
  {ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C}
  {P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx} {alpha beta : Fin k}

/-- Recover the union-of-missing-colors interface from the explicit vertex witness. -/
theorem betaMissingTwoBefore
    (data : HierarchySituationThreeDisjointData
      G k e0 input T phi ett base C ctx P alpha beta) :
    let j := HierarchyPathNumber C.hierarchy
    let B := HierarchyFullTailPrefix C (j - 2)
    beta ∈ TreeMissingColors data.switched.coloring B := by
  simpa only [TreeMissingColors, Finset.mem_biUnion] using data.betaMissingTwoBeforeWitness

end HierarchySituationThreeDisjointData

end GoldbergSeymour

end
