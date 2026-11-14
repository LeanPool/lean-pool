/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.HierarchySituationTwoSubcaseThreeOne.Preparation2
public import LeanPool.GoldbergSeymour.HierarchySituationTwoCaseThreeOneData

/-!
# Hierarchy Situation Two Subcase Three One

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

open HierarchySituationTwoSubcaseThreeOnePreparation

theorem HierarchySituationTwoSubcaseThreeOne {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi)
    (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext
      G k e0 input T phi ett base C)
    (D : HierarchySituationTwoCaseThreeOneData
      G k e0 input T phi ett base C ctx) :
    False := by
  classical
  let alpha : Fin k := D.alpha
  let theta : Fin k := D.theta
  let lastIndex : Fin T.length := D.lastEdgeIndex
  let penIndex : Fin (T.length + 1) := D.penultimateVertexIndex
  let endIndex : Fin (T.length + 1) := D.terminalVertexIndex
  let H := C.hierarchy
  let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
  let A := HierarchyStarredStage H q
  let ell := HierarchyFullTailLength C
  let B := HierarchyFullTailPrefix C (ell - 2)
  let Bplus := HierarchyFullTailPrefix C (ell - 1)
  let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
  let Tn := ett.series.data.tree n.castSucc
  have lastColor : phi (T.edge lastIndex) = some theta := D.thetaOnLastEdge
  have alphaTerminal : alpha ∈ MissingColors G phi (T.vertex endIndex) := D.alphaMissingTerminal
  have alphaBefore : alpha ∈ TreeMissingColors phi B := D.alphaMissingTwoBefore
  have alphaUnused : ∀ t : Fin T.length, A.length ≤ t.val → phi (T.edge t) ≠ some alpha :=
    D.alphaUnusedOnFullTail
  have lastPosition : lastIndex.val + 1 = T.length := D.lastEdgePosition
  have penPosition : penIndex.val + 1 = T.length := D.penultimateVertexPosition
  have endPosition : endIndex.val = T.length := D.terminalVertexPosition
  have thetaPresent : theta ∉ MissingColors G phi (T.vertex penIndex) := D.thetaPresentPenultimate
  have oldRoute := P2813_T1_TerminalRoute G k e0 input T phi ett
  have h_exception := helper_h_exception_6390 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base)
      (@C) (@ctx) (@D) (@lastColor) (@alphaTerminal) (@alphaBefore) (@lastPosition) (@penPosition)
      (@endPosition) (@thetaPresent)
  exact helper_continuation_3712 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx)
      (@D)
      (@lastColor) (@alphaTerminal) (@alphaBefore) (@alphaUnused) (@lastPosition) (@penPosition)
      (@endPosition) (@oldRoute) (@h_exception)
end GoldbergSeymour

end
