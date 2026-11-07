/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.HierarchySituationTwoTailData

/-!
# Hierarchy Situation Two Case One Data

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

/-- A stored color missing at both final vertices and its two distinct auxiliary colors in situation
two, case one.
-/
structure HierarchySituationTwoCaseOneData {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
    (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
    (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) extends
    HierarchySituationTwoTailData G k e0 input T phi ett base C ctx where
  /-- The distinguished color constrained by the accompanying missing-color conditions. -/
  alpha : Fin k
  /-- The first auxiliary color in the stored color pair. -/
  gammaOne : Fin k
  /-- The second auxiliary color in the stored color pair. -/
  gammaTwo : Fin k
  alphaMissingPenultimate : alpha ∈ MissingColors G phi (T.vertex penultimateVertexIndex)
  alphaMissingTerminal : alpha ∈ MissingColors G phi (T.vertex terminalVertexIndex)
  alphaStored : alpha ∈ HierarchyStoredColorsAt C.hierarchy (Fin.last C.hierarchy.dividerCount)
  gammaPair : C.good.gamma (Fin.last C.hierarchy.dividerCount) alpha = { gammaOne, gammaTwo }
  gammaDistinct : gammaOne ≠ gammaTwo

end GoldbergSeymour

end
