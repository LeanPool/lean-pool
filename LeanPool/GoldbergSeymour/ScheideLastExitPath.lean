/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ScheideEnlargedVertexSet

/-!
# Scheide Last Exit Path

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

/-- A two-color path with a recorded last departure from the enlarged vertex set. -/
structure ScheideLastExitPath {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k)
    (T : TreeSequence G e0) (C : ScheideReducedConfiguration G k e0 phi T)
    (D : ScheideDefectiveSetup G k e0 phi T C)
    (R :
      ∀ d : { delta // delta ∈ DefectiveColors G phi (TreeSequenceVertexSet T) },
        ScheideReplacementData G k e0 phi T C D d)
    (alpha : Fin k) where
  /-- The terminal vertex of the path, lying outside the enlarged vertex set. -/
  terminal : V
  /-- The last vertex of the path belonging to the enlarged vertex set. -/
  lastInside : V
  /-- The vertex immediately after the last departure from the enlarged set. -/
  firstOutside : V
  /-- The boundary edge at the recorded last departure. -/
  crossing : E
  /-- The two-color path witnessing the last departure. -/
  path :
    (TwoColorIncidenceGraph G phi D.alpha0 alpha).Walk
      (Sum.inl (C.y ⟨0, lt_of_lt_of_le Nat.zero_lt_two C.p_ge_two⟩)) (Sum.inl terminal)
  /-- The index of the distinguished final trunk or departure vertex. -/
  lastIndex : Fin (path.length + 1)
  pathSimple : path.IsPath
  pathSpans :
    {z | z ∈ path.support} =
      TwoColorComponent G phi D.alpha0 alpha
        (Sum.inl (C.y ⟨0, lt_of_lt_of_le Nat.zero_lt_two C.p_ge_two⟩))
  terminalOutside : terminal ∉ ScheideEnlargedVertexSet R
  lastInsideAt : path.getVert lastIndex.val = Sum.inl lastInside
  lastInsideMem : lastInside ∈ ScheideEnlargedVertexSet R
  followingVertex : lastIndex.val + 2 ≤ path.length
  crossingAt : path.getVert (lastIndex.val + 1) = Sum.inr crossing
  firstOutsideAt : path.getVert (lastIndex.val + 2) = Sum.inl firstOutside
  firstOutsideNotMem : firstOutside ∉ ScheideEnlargedVertexSet R
  afterLastOutside :
    ∀ (j : Fin (path.length + 1)),
      lastIndex.val < j.val →
        ∀ x : V, path.getVert j.val = Sum.inl x → x ∉ ScheideEnlargedVertexSet R
  crossingBoundary : crossing ∈ BoundaryEdges G (ScheideEnlargedVertexSet R)
  crossingColor : phi crossing = some alpha
  crossingComponent :
    Sum.inr crossing ∈
      TwoColorComponent G phi D.alpha0 alpha
        (Sum.inl (C.y ⟨0, lt_of_lt_of_le Nat.zero_lt_two C.p_ge_two⟩))

end GoldbergSeymour

end
