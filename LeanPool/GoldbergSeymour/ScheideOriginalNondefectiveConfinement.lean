/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TwoColorWalkConfinement

public import LeanPool.GoldbergSeymour.ScheideGlobalMaximumOrder
public import LeanPool.GoldbergSeymour.ScheideLastExitPath

/-!
# Scheide Original Nondefective Confinement

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private theorem ScheideOriginalNondefectiveConfinement_hnoDeparture_103.{u_1, u_2} :
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (R : (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))) →
        ScheideReplacementData G k e0 phi T C D d) (alpha : Fin k) (L : ScheideLastExitPath G k e0
        phi T C D R alpha), alpha ∉ DefectiveColors G phi (TreeSequenceVertexSet T) →
    let VT := TreeSequenceVertexSet T;
    let y0 := C.y ⟨0, lt_of_lt_of_le Nat.zero_lt_two C.p_ge_two⟩; y0 ∈ VT → ColoredVertexSetClosed
        G phi VT → L.crossing ∈ BoundaryColorEdges G phi VT alpha →
    ∀ (n : ℕ) (y x : V) (e : E), n + 2 ≤ (↑L.lastIndex : ℕ) → L.path.getVert n = Sum.inl y → y ∈
        VT → L.path.getVert (n + 1) = Sum.inr e → L.path.getVert (n + 2) = Sum.inl x → x ∉ VT →
        False := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D R alpha L hnondef VT y0 hy0VT hVTclosed hcrossBC n y x e hnl
      hny hy hne hexc hx
  obtain ⟨hedge, edgeColor⟩ := TwoColorWalk.boundaryAtTwoStep L.path L.pathSimple
    VT n y x e (by have := L.followingVertex; omega) hny hy hne hexc hx
  have hnotzero : phi e ≠ some D.alpha0 := by
    intro hezero
    exact (hVTclosed hedge hy0VT hezero) D.alpha0_missing_at_y0
  have hecolor : phi e = some alpha := by
    rcases edgeColor with hezero | healpha
    · exact False.elim (hnotzero hezero)
    · exact healpha
  have hcrossne : e ≠ L.crossing := by
    intro heq
    have hinj := L.pathSimple.getVert_injOn
      (show n + 1 ≤ L.path.length by
        have h := L.followingVertex
        omega)
      (show L.lastIndex.val + 1 ≤ L.path.length by
        have h := L.followingVertex
        omega)
      (by rw [hne, L.crossingAt, heq])
    omega
  have hmem : alpha ∈ DefectiveColors G phi VT := by
    simp only [DefectiveColors, Finset.mem_filter, Finset.mem_univ, true_and]
    change 2 ≤ (BoundaryColorEdges G phi VT alpha).card
    have hsub : ({L.crossing, e} : Finset E) ⊆ BoundaryColorEdges G phi VT alpha := by
      intro q hq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with rfl | rfl
      · exact hcrossBC
      · simp only [BoundaryColorEdges, Finset.mem_filter]
        exact ⟨hedge, hecolor⟩
    have hcard := Finset.card_le_card hsub
    have hpairs : ({L.crossing, e} : Finset E).card = 2 := by
      exact Finset.card_pair hcrossne.symm
    rw [hpairs] at hcard
    exact hcard
  exact hnondef (by simpa [VT] using hmem)

theorem ScheideOriginalNondefectiveConfinement {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (C : ScheideReducedConfiguration G k e0 phi T)
    (D : ScheideDefectiveSetup G k e0 phi T C)
    (R : ∀ d : {delta // delta ∈ DefectiveColors G phi
      (TreeSequenceVertexSet T)}, ScheideReplacementData G k e0 phi T C D d)
    (alpha : Fin k)
    (L : ScheideLastExitPath G k e0 phi T C D R alpha)
    (hlast : L.lastInside ∈ TreeSequenceVertexSet T)
    (hnondef : alpha ∉ DefectiveColors G phi (TreeSequenceVertexSet T)) :
    (∀ (j : Fin (L.path.length + 1)),
        j.val ≤ L.lastIndex.val →
          ∀ x : V, L.path.getVert j.val = Sum.inl x → x ∈ TreeSequenceVertexSet T) ∧
      ∀ f : E,
        f ∈ BoundaryEdges G (ScheideEnlargedVertexSet R) ∧
            Sum.inr f ∈
              TwoColorComponent G phi D.alpha0 alpha
                (Sum.inl (C.y ⟨0, lt_of_lt_of_le Nat.zero_lt_two C.p_ge_two⟩)) →
          f = L.crossing := by
  classical
  let VT := TreeSequenceVertexSet T
  let X := ScheideEnlargedVertexSet R
  let y0 : V := C.y ⟨0, lt_of_lt_of_le Nat.zero_lt_two C.p_ge_two⟩
  have hy0VT : y0 ∈ VT := by
    have hpos : (0 : ℕ) < T.length + 1 := by omega
    have hv := C.base_vertex_position
      ⟨0, lt_of_lt_of_le Nat.zero_lt_two C.p_ge_two⟩
    simpa [y0, VT, TreeSequenceVertexSet] using
      (show ∃ i : Fin (T.length + 1), T.vertex i = y0 from
        ⟨⟨0, hpos⟩, by simpa [y0] using hv⟩)
  have hVTclosed : ColoredVertexSetClosed G phi VT := by
    unfold ColoredVertexSetClosed
    intro f c v hf hv hc
    exact (ScheideGlobalMaximumOrder G k e0 phi T C.globally_maximum).2.2.2.2
      hf hv hc
  have hVTsubX : VT ⊆ X := by
    intro v hv
    simp [X, ScheideEnlargedVertexSet, VT, hv]
  have hy0X : y0 ∈ X := hVTsubX hy0VT
  have hcrossVT : L.crossing ∈ BoundaryEdges G VT := by
    unfold BoundaryEdges
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨L.lastInside, hlast, L.firstOutside, ?_, ?_⟩
    · intro h
      exact L.firstOutsideNotMem (hVTsubX h)
    · have hadj0 := L.path.adj_getVert_succ
          (i := L.lastIndex.val) (by
            have hfollow := L.followingVertex
            omega)
      have hadj := L.path.adj_getVert_succ
          (i := L.lastIndex.val + 1) (by
            have hfollow := L.followingVertex
            omega)
      rw [L.lastInsideAt, L.crossingAt] at hadj0
      rw [L.crossingAt, L.firstOutsideAt] at hadj
      simp only [TwoColorIncidenceGraph, Incident] at hadj0 hadj
      have hne : L.lastInside ≠ L.firstOutside := by
        intro heq
        have hidx := L.pathSimple.getVert_injOn
          (show L.lastIndex.val ≤ L.path.length by omega)
          (show L.lastIndex.val + 2 ≤ L.path.length by exact L.followingVertex)
          (by rw [L.lastInsideAt, L.firstOutsideAt, heq])
        omega
      exact (Sym2.mem_and_mem_iff hne).mp ⟨hadj0.1, hadj.1⟩
  have hcrossBC : L.crossing ∈ BoundaryColorEdges G phi VT alpha := by
    simp only [BoundaryColorEdges, Finset.mem_filter]
    exact ⟨hcrossVT, L.crossingColor⟩
  have hnoDeparture :
    ∀ (n : ℕ) (y x : V) (e : E), n + 2 ≤ L.lastIndex.val → L.path.getVert n = Sum.inl y → y ∈ VT →
        L.path.getVert (n + 1) = Sum.inr e → L.path.getVert (n + 2) = Sum.inl x → x ∉ VT → False
  := by
    exact @ScheideOriginalNondefectiveConfinement_hnoDeparture_103 V E inferInstance
        inferInstance inferInstance inferInstance G k e0 phi T C D R alpha L hnondef hy0VT
        hVTclosed hcrossBC
  have hconf : ∀ n : ℕ, n ≤ L.lastIndex.val →
      ∀ x : V, L.path.getVert n = Sum.inl x → x ∈ VT := by
    exact TwoColorWalk.confinedBefore L.path VT L.lastIndex.val
      (by have := L.followingVertex; omega) hy0VT hnoDeparture
  constructor
  · intro j hj x hx
    exact hconf j.val hj x hx
  · intro f hf
    exact TwoColorWalk.lastBoundaryEdgeUnique L.path L.pathSimple X VT hVTsubX
      L.lastIndex L.lastInside L.lastInsideAt L.crossing L.crossingAt
      L.afterLastOutside hconf f hf.1 (by
        have member := hf.2
        rw [← L.pathSpans] at member
        exact member)
end GoldbergSeymour

end
