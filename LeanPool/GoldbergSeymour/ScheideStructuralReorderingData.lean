/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ScheideStructuralSelectionData

/-!
# Scheide Structural Reordering Data

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

/--
Position and set-equality certificates for reordering absorbed and retained structural blocks. -/
structure ScheideStructuralReorderingData {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k)
    (T : TreeSequence G e0) (C : ScheideStructuralConfiguration G k e0 phi T)
    (D : ScheideStructuralSelectionData G k e0 phi T C) (T' : TreeSequence G e0) where
  length_eq : T'.length = T.length
  base_vertex_position :
    ∀ q : Fin C.p,
      T'.vertex
          ⟨q.val, by
            have hq := q.isLt
            have hc := C.length_eq
            rw [length_eq]
            omega⟩ =
        C.y q
  absorbed_vertex_position :
    ∀ (h : Fin D.absorbedCount) (j : Fin 2),
      T'.vertex
          ⟨C.p + 2 * h.val + j.val, by
            have hh := h.isLt
            have hj := j.isLt
            have hc := C.length_eq
            have hd := D.count_eq
            rw [length_eq]
            omega⟩ =
        C.blockVertex (D.absorbedEquiv h).1 j
  retained_vertex_position :
    ∀ (t : Fin D.retainedCount) (j : Fin 2),
      T'.vertex
          ⟨C.p + 2 * D.absorbedCount + 2 * t.val + j.val,
            by
            have ht := t.isLt
            have hj := j.isLt
            have hc := C.length_eq
            have hd := D.count_eq
            rw [length_eq]
            omega⟩ =
        C.blockVertex (D.retained t) j
  base_edge_position :
    ∀ q : Fin (C.p - 1),
      T'.edge
          ⟨q.val, by
            have hq := q.isLt
            have hp := C.p_ge_two
            have hc := C.length_eq
            rw [length_eq]
            omega⟩ =
        C.baseEdge q
  absorbed_edge_position :
    ∀ (h : Fin D.absorbedCount) (j : Fin 2),
      T'.edge
          ⟨C.p - 1 + 2 * h.val + j.val, by
            have hh := h.isLt
            have hj := j.isLt
            have hp := C.p_ge_two
            have hc := C.length_eq
            have hd := D.count_eq
            rw [length_eq]
            omega⟩ =
        C.blockEdge (D.absorbedEquiv h).1 j
  retained_edge_position :
    ∀ (t : Fin D.retainedCount) (j : Fin 2),
      T'.edge
          ⟨C.p - 1 + 2 * D.absorbedCount + 2 * t.val + j.val,
            by
            have ht := t.isLt
            have hj := j.isLt
            have hp := C.p_ge_two
            have hc := C.length_eq
            have hd := D.count_eq
            rw [length_eq]
            omega⟩ =
        C.blockEdge (D.retained t) j
  tashkinov : TashkinovTree G e0 phi T'
  vertex_set_eq : TreeSequenceVertexSet T' = TreeSequenceVertexSet T
  exit_set_eq : ScheideExitVertices T' phi = ScheideExitVertices T phi

end GoldbergSeymour

end
