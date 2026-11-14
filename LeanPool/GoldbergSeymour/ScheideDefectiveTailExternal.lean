/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ScheideDefectiveLastReturnExists
public import LeanPool.GoldbergSeymour.ScheideDefectiveReturnContradiction

/-!
# Scheide Defective Tail External

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem ScheideDefectiveTailExternal {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (C : ScheideReducedConfiguration G k e0 phi T)
    (D : ScheideDefectiveSetup G k e0 phi T C) :
    ∀ d : {delta // delta ∈ DefectiveColors G phi (TreeSequenceVertexSet T)},
    ∀ w ∈ TreeSequenceVertexSet T, Sum.inl w ∈ TwoColorComponent G phi (C.gamma (D.gammaIndex d))
        d.1 (Sum.inl (D.v0 d)) → w = D.v0 d := by
  classical
  intro d w hw hcomponent
  by_contra hne
  obtain ⟨R⟩ := ScheideDefectiveLastReturnExists
    G k e0 phi T C D d w hw hcomponent hne
  exact ScheideDefectiveReturnContradiction G k e0 phi T C D d R

end GoldbergSeymour

end
