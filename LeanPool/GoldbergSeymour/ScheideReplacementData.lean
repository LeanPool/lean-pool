/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ScheideDefectiveSetup

/-!
# Scheide Replacement Data

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

open scoped Sym2

/-- Two defective boundary edges and a replacement tree with the prescribed retained and final
positions.
-/
structure ScheideReplacementData {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k)
    (T : TreeSequence G e0) (C : ScheideReducedConfiguration G k e0 phi T)
    (D : ScheideDefectiveSetup G k e0 phi T C)
    (d : { delta // delta ∈ DefectiveColors G phi (TreeSequenceVertexSet T) }) where
  /-- The first selected boundary edge. -/
  f1 : E
  /-- The second selected boundary edge. -/
  f2 : E
  /-- The first selected vertex inside the tree. -/
  v1 : V
  /-- The second selected vertex inside the tree. -/
  v2 : V
  /-- The first selected outside vertex. -/
  u1 : V
  /-- The second selected outside vertex. -/
  u2 : V
  f0_ne_f1 : D.f0 d ≠ f1
  f0_ne_f2 : D.f0 d ≠ f2
  f1_ne_f2 : f1 ≠ f2
  v1_in_remainder :
    v1 ∈
      TreeSequenceVertexSet T \ {C.blockVertex (D.gammaIndex d) 0, C.blockVertex (D.gammaIndex d) 1}
  v2_in_remainder :
    v2 ∈
      TreeSequenceVertexSet T \ {C.blockVertex (D.gammaIndex d) 0, C.blockVertex (D.gammaIndex d) 1}
  u1_outside : u1 ∉ TreeSequenceVertexSet T
  u2_outside : u2 ∉ TreeSequenceVertexSet T
  f1_ends : G.ends f1 = s(v1, u1)
  f2_ends : G.ends f2 = s(v2, u2)
  f1_color : phi f1 = some d.1
  f2_color : phi f2 = some d.1
  exact_three :
    ∀ f : E, (f ∈ BoundaryColorEdges G phi (TreeSequenceVertexSet T \
        {C.blockVertex (D.gammaIndex d) 0, C.blockVertex (D.gammaIndex d) 1}) d.1 ∧
    ∃ w, w ∉ TreeSequenceVertexSet T ∧ Incident G w f) ↔ f = D.f0 d ∨ f = f1 ∨ f = f2
  /-- The reordered tree retaining the prescribed vertices and edges. -/
  replacementTree : TreeSequence G e0
  replacement_length : replacementTree.length = T.length
  retained_edges_before :
    ∀ q : ℕ,
      q < C.p - 1 + 2 * (D.gammaIndex d).val →
        ∀ hq : q < T.length, replacementTree.edge ⟨q, by omega⟩ = T.edge ⟨q, hq⟩
  retained_vertices_before :
    ∀ q : ℕ,
      q ≤ C.p - 1 + 2 * (D.gammaIndex d).val →
        ∀ hq : q < T.length + 1, replacementTree.vertex ⟨q, by omega⟩ = T.vertex ⟨q, hq⟩
  retained_edges_after :
    ∀ q : ℕ,
      C.p - 1 + 2 * (D.gammaIndex d).val ≤ q →
        ∀ hq : q + 2 < T.length, replacementTree.edge ⟨q, by omega⟩ = T.edge ⟨q + 2, hq⟩
  retained_vertices_after :
    ∀ q : ℕ,
      C.p - 1 + 2 * (D.gammaIndex d).val < q →
        ∀ hq : q + 2 < T.length + 1, replacementTree.vertex ⟨q, by omega⟩ = T.vertex ⟨q + 2, hq⟩
  replacement_last_edges :
    replacementTree.edge
          ⟨T.length - 2, by
            have hi := (D.gammaIndex d).isLt
            have hp := C.p_ge_two
            have hc := C.length_eq
            have _ := replacement_length
            omega⟩ =
        f1 ∧
      replacementTree.edge
          ⟨T.length - 1, by
            have hi := (D.gammaIndex d).isLt
            have hp := C.p_ge_two
            have hc := C.length_eq
            have _ := replacement_length
            omega⟩ =
        f2
  replacement_last_vertices :
    replacementTree.vertex
          ⟨T.length - 1, by
            have _ := (D.gammaIndex d).isLt
            have _ := C.p_ge_two
            have hc := C.length_eq
            have _ := replacement_length
            omega⟩ =
        u1 ∧
      replacementTree.vertex
          ⟨T.length, by
            have _ := replacement_length
            omega⟩ =
        u2
  replacement_vertices :
    TreeSequenceVertexSet replacementTree =
      (TreeSequenceVertexSet T \
          {C.blockVertex (D.gammaIndex d) 0, C.blockVertex (D.gammaIndex d) 1}) ∪
        { u1, u2 }
  replacement_edges :
    Finset.univ.image replacementTree.edge =
      (((Finset.univ.image T.edge).erase (C.blockEdge (D.gammaIndex d) 0)).erase
          (C.blockEdge (D.gammaIndex d) 1)) ∪
        { f1, f2 }

end GoldbergSeymour

end
