/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ScheideOriginalDefectiveConfinement
public import LeanPool.GoldbergSeymour.ScheideOriginalNondefectiveConfinement
public import LeanPool.GoldbergSeymour.ScheideReplacementConfinement
public import LeanPool.GoldbergSeymour.ScheideTwoColorLastExitPath

/-!
# Scheide Single Boundary Crossing

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem ScheideSingleBoundaryCrossing {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (C : ScheideReducedConfiguration G k e0 phi T)
    (D : ScheideDefectiveSetup G k e0 phi T C)
    (R : ∀ d : {delta // delta ∈ DefectiveColors G phi
      (TreeSequenceVertexSet T)}, ScheideReplacementData G k e0 phi T C D d) :
    ∀ alpha : Fin k,
      (∀ v ∈ ScheideEnlargedVertexSet R, alpha ∈ PresentColors G phi v) →
      ∃! f : E, f ∈ BoundaryEdges G (ScheideEnlargedVertexSet R) ∧
        Sum.inr f ∈ TwoColorComponent G phi D.alpha0 alpha
          (Sum.inl (C.y ⟨0, lt_of_lt_of_le Nat.zero_lt_two C.p_ge_two⟩)) := by
  classical
  intro alpha hpresent
  let L : ScheideLastExitPath G k e0 phi T C D R alpha :=
    Classical.choice
      (ScheideTwoColorLastExitPath G k e0 phi T C D R alpha hpresent)
  refine ⟨L.crossing, ⟨L.crossingBoundary, L.crossingComponent⟩, ?_⟩
  intro f hf
  by_cases hlast : L.lastInside ∈ TreeSequenceVertexSet T
  · by_cases hdef : alpha ∈ DefectiveColors G phi (TreeSequenceVertexSet T)
    · exact (ScheideOriginalDefectiveConfinement G k e0 phi T C D R
        alpha L hlast hdef).2.2.2 f hf
    · exact (ScheideOriginalNondefectiveConfinement G k e0 phi T C D R
        alpha L hlast hdef).2 f hf
  · obtain ⟨d, _, _, _, _, _, _, hunique⟩ :=
      ScheideReplacementConfinement G k e0 phi T C D R alpha L hlast
    exact hunique f hf

end GoldbergSeymour

end
