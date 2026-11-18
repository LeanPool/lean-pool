/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.HierarchyFullTailPrefix
public import LeanPool.GoldbergSeymour.HierarchySituationTwoCaseThreeData

/-!
# Hierarchy Situation Two Case Three Normalized Data

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

/-- The missing-color, unused-tail and normalized-alternative conditions for situation two, case
three.
-/
structure HierarchySituationTwoCaseThreeNormalizedData {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
    (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) extends
    HierarchySituationTwoCaseThreeData G k e0 input T phi ett base C ctx where
  alphaMissingTwoBefore :
    alpha ∈ TreeMissingColors phi (HierarchyFullTailPrefix C (HierarchyFullTailLength C - 2))
  alphaUnusedOnFullTail :
    let H := C.hierarchy
    let A := HierarchyStarredStage H (Fin.last H.dividerCount)
    ∀ t : Fin T.length, A.length ≤ t.val → phi (T.edge t) ≠ some alpha
  normalizedAlternative :
    let H := C.hierarchy
    let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
    let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
    let Dn := TashkinovStoredColors ett.series.data n
    let Dnq := HierarchyStoredColorsAt H q
    let Gamma := Dnq.biUnion (C.good.gamma q)
    let A := HierarchyStarredStage H q
    let tailUsed :=
      (Finset.univ : Finset (Fin k)).filter fun c =>
        ∃ t : Fin T.length, A.length ≤ t.val ∧ phi (T.edge t) = some c
    (0 < H.dividerCount ∧ alpha ∉ Dnq ∧ alpha ∉ Gamma) ∨
      (H.dividerCount = 0 ∧ alpha ∉ Dn ∧ alpha ∉ Gamma) ∨
        (alpha ∈ Dnq ∧ Disjoint (C.good.gamma q alpha) tailUsed)

end GoldbergSeymour

end
