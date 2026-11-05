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

/-- Nonfirst initial edges of the reordered configuration avoid all retained block colors. -/
theorem ScheideStructuralReorderingData.initialNonfirstAvoidsRetainedColor.{u_1, u_2} :
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (C : ScheideStructuralConfiguration G k e0 phi T)
      (D : ScheideStructuralSelectionData G k e0 phi T C) (T' : TreeSequence G e0)
      (Q : ScheideStructuralReorderingData G k e0 phi T C D T'),
    ∀ (n : Fin (C.p - (1 : ℕ) + (2 : ℕ) * D.absorbedCount)),
    (1 : ℕ) ≤ (↑n : ℕ) →
    ∀ (d : Fin k),
    phi
          (T'.edge
            (⟨(↑n : ℕ),
                have hn : (↑n : ℕ) < C.p - (1 : ℕ) + (2 : ℕ) * D.absorbedCount := n.isLt;
                have hp : (2 : ℕ) ≤ C.p := C.p_ge_two;
                have hl : T.length + (1 : ℕ) = C.p + (2 : ℕ) * C.s := C.length_eq;
                have hd : C.s = D.absorbedCount + D.retainedCount := D.count_eq;
                Eq.mpr (id (congrArg (fun (_a : ℕ) => (↑n : ℕ) < _a) Q.length_eq))
                  (Decidable.byContradiction fun (a : ¬(↑n : ℕ) < T.length) => by omega)⟩ :
              Fin T'.length)) =
        some d →
    ∀ (r : Fin D.retainedCount),
    d ≠ C.gamma (D.retained r) := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D T' Q n hn d hdedge rr
  refine Fin.addCases ?_ ?_ n hn d hdedge rr
  · intro u hn d hdedge rr
    have hold := Q.base_edge_position u
    change 1 ≤ u.val at hn
    apply C.initial_nonfirst_avoids_blocks u hn d (by
      rw [← hold]
      exact hdedge) (D.retained rr)
  · intro u hn d hdedge rr
    let paired : Fin (D.absorbedCount * 2) :=
      Fin.cast (Nat.mul_comm 2 D.absorbedCount) u
    let h := paired.divNat
    let j := paired.modNat
    have huv : u.val = 2 * h.val + j.val := by
      dsimp [h, j, paired, Fin.divNat, Fin.modNat]
      omega
    have hedge := Q.absorbed_edge_position h j
    have hblock : phi (C.blockEdge (D.absorbedEquiv h).1 j) = some d := by
      rw [← hedge]
      simpa [huv, Nat.add_assoc] using hdedge
    have hcolor := C.block_color (D.absorbedEquiv h).1 j
    have heq : d = C.gamma (D.absorbedEquiv h).1 := by
      rw [hcolor] at hblock
      simpa using hblock.symm
    intro hbad
    apply (D.absorbedEquiv h).2
    refine ⟨rr, ?_⟩
    apply C.gamma_injective
    rw [← heq, hbad]

end GoldbergSeymour

end
