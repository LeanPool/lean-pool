/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.CriticalCoreExists
public import LeanPool.GoldbergSeymour.ElementaryTransfer

public import
    LeanPool.GoldbergSeymour.HierarchySituationThreeDisjointThetaUnstoredBetaStoredImpossible

public import LeanPool.GoldbergSeymour.MaximumDegreeRestrict
public import LeanPool.GoldbergSeymour.ThmGS2

/-!
# General High Index Elementary

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem GeneralHighIndexElementary {V E : Type*} [Fintype V] [Fintype E]
    (G : LooplessMultigraph V E)
    (hG : MaximumDegree G + 2 ≤ ChromaticIndex G) : Elementary G := by
  classical
  obtain ⟨F, hχ, hcrit⟩ := CriticalCoreExists G
  apply ElementaryTransfer G F hχ
  refine ThmGS2 (RestrictEdges G F) ?_ hcrit
  have hdeg := MaximumDegreeRestrict G F
  omega

end GoldbergSeymour

end
