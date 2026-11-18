/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.HierarchySituationTwoSubcaseTwoOneNonexceptional
public import LeanPool.GoldbergSeymour.HierarchySituationTwoSubcaseTwoOneStoredException

/-!
# Hierarchy Situation Two Subcase Two One

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem HierarchySituationTwoSubcaseTwoOne {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi)
    (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext
      G k e0 input T phi ett base C)
    (D : HierarchySituationTwoCaseTwoData
      G k e0 input T phi ett base C ctx) :
    False := by
  classical
  let H := C.hierarchy
  let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
  by_cases hexceptional : ∃ eta,
      eta ∈ HierarchyStoredColorsAt H q ∧
        eta ∈ MissingColors G phi (T.vertex D.penultimateVertexIndex) ∧
        D.theta ∈ C.good.gamma q eta
  · rcases hexceptional with ⟨eta, hetaStored, hetaMissing, hthetaPair⟩
    exact HierarchySituationTwoSubcaseTwoOneStoredException
      G k e0 input T phi ett base C ctx D eta
      (by simpa [q, H] using hetaStored) hetaMissing
      (by simpa [q, H] using hthetaPair)
  · exact HierarchySituationTwoSubcaseTwoOneNonexceptional
      G k e0 input T phi ett base C ctx D
      (by simpa [q, H] using hexceptional)

end GoldbergSeymour

end
