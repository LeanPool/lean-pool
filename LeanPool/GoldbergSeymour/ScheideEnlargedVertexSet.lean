/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ScheideReplacementData

/-!
# Scheide Enlarged Vertex Set

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

/-- The original tree vertices together with the two outside endpoints supplied by each defective-
color replacement.
-/
noncomputable def ScheideEnlargedVertexSet {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    [DecidableEq E] {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {phi : PartialEdgeColoring E k}
    {T : TreeSequence G e0} {C : ScheideReducedConfiguration G k e0 phi T}
    {D : ScheideDefectiveSetup G k e0 phi T C}
    (R :
      ∀ d : { delta // delta ∈ DefectiveColors G phi (TreeSequenceVertexSet T) },
        ScheideReplacementData G k e0 phi T C D d) :
    Finset V := by
  classical
  exact TreeSequenceVertexSet T ∪ Finset.univ.biUnion (fun d => {R d |>.u1, R d |>.u2})

end GoldbergSeymour

end
