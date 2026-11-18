/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.AdjacentEdges
public import LeanPool.GoldbergSeymour.TwoColorWalkConfinement

public import LeanPool.GoldbergSeymour.ScheideLastExitPath
public import LeanPool.GoldbergSeymour.ScheideReplacementUnionClosed

/-!
# Scheide Original Defective Confinement

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private theorem helper_hunique_159.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (R : (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))) →
        ScheideReplacementData G k e0 phi T C D d) (alpha : Fin k) (hdef : alpha ∈ DefectiveColors
        G phi (TreeSequenceVertexSet T)),
    let d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T)) := (⟨alpha, hdef⟩ :
        ↥(DefectiveColors G phi (TreeSequenceVertexSet T)));
    let VT : Finset V := TreeSequenceVertexSet T;
    let XA : Finset V := VT ∪ {(R d).u1, (R d).u2}; IsProperEdgeColoring G phi → VT ⊆ XA →
    ∀ (fBlock : E), phi fBlock = some (↑d : Fin k) → G.ends fBlock = s(C.blockVertex (D.gammaIndex
        d) (0 : Fin (2 : ℕ)), C.blockVertex (D.gammaIndex d) (1 : Fin (2 : ℕ))) → C.blockVertex
        (D.gammaIndex d) (0 : Fin (2 : ℕ)) ∈ VT → C.blockVertex (D.gammaIndex d) (1 : Fin (2 : ℕ))
        ∈ VT →
    ∀ f ∈ BoundaryColorEdges G phi XA alpha, f = D.f0 d := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D R alpha hdef d VT XA hproper hVTsubXA fBlock hfBlockColor
      hfBlockEnds hblock0VT hblock1VT f hf
  have hfBoundary : f ∈ BoundaryEdges G XA :=
    (Finset.mem_filter.mp hf).1
  have hfColor : phi f = some alpha :=
    (Finset.mem_filter.mp hf).2
  obtain ⟨a, ha, b, hb, hends⟩ :
      ∃ a ∈ XA, ∃ b ∉ XA, G.ends f = s(a, b) := by
    simpa [BoundaryEdges] using hfBoundary
  have hfa : Incident G a f := by
    unfold Incident
    rw [hends]
    simp
  have hfb : Incident G b f := by
    unfold Incident
    rw [hends]
    simp
  have hneInternal : ∀ (g : E) (r s : V), G.ends g = s(r, s) →
      r ∈ XA → s ∈ XA → f ≠ g := by
    intro g r s hg hr hs heq
    have hbmem : b ∈ G.ends g := by
      rw [← heq]
      exact hfb
    rw [hg] at hbmem
    rcases Sym2.mem_iff.mp hbmem with hbr | hbs
    · exact hb (hbr.symm ▸ hr)
    · exact hb (hbs.symm ▸ hs)
  have haVT : a ∈ VT := by
    simp only [XA, Finset.mem_union, Finset.mem_insert,
      Finset.mem_singleton] at ha
    rcases ha with ha | ha | ha
    · exact ha
    · subst a
      have hne := hneInternal (R d).f1 (R d).v1 (R d).u1
        (R d).f1_ends
        (hVTsubXA (Finset.mem_sdiff.mp (R d).v1_in_remainder).1)
        (by simp [XA])
      have hadj : AdjacentEdges G f (R d).f1 := by
        exact ⟨(R d).u1, hfa, by
          unfold Incident
          rw [(R d).f1_ends]
          simp⟩
      exact False.elim ((hproper hne hadj hfColor) (R d).f1_color)
    · subst a
      have hne := hneInternal (R d).f2 (R d).v2 (R d).u2
        (R d).f2_ends
        (hVTsubXA (Finset.mem_sdiff.mp (R d).v2_in_remainder).1)
        (by simp [XA])
      have hadj : AdjacentEdges G f (R d).f2 := by
        exact ⟨(R d).u2, hfa, by
          unfold Incident
          rw [(R d).f2_ends]
          simp⟩
      exact False.elim ((hproper hne hadj hfColor) (R d).f2_color)
  have haNeBlock0 : a ≠ C.blockVertex (D.gammaIndex d) 0 := by
    intro heq
    have hne := hneInternal fBlock
      (C.blockVertex (D.gammaIndex d) 0)
      (C.blockVertex (D.gammaIndex d) 1) hfBlockEnds
      (hVTsubXA hblock0VT) (hVTsubXA hblock1VT)
    have hadj : AdjacentEdges G f fBlock := by
      refine ⟨a, hfa, ?_⟩
      unfold Incident
      rw [hfBlockEnds, heq]
      simp
    exact (hproper hne hadj hfColor) hfBlockColor
  have haNeBlock1 : a ≠ C.blockVertex (D.gammaIndex d) 1 := by
    intro heq
    have hne := hneInternal fBlock
      (C.blockVertex (D.gammaIndex d) 0)
      (C.blockVertex (D.gammaIndex d) 1) hfBlockEnds
      (hVTsubXA hblock0VT) (hVTsubXA hblock1VT)
    have hadj : AdjacentEdges G f fBlock := by
      refine ⟨a, hfa, ?_⟩
      unfold Incident
      rw [hfBlockEnds, heq]
      simp
    exact (hproper hne hadj hfColor) hfBlockColor
  have hbVT : b ∉ VT := by
    intro hbVT
    exact hb (hVTsubXA hbVT)
  have hfRemainder : f ∈ BoundaryColorEdges G phi
      (VT \ {C.blockVertex (D.gammaIndex d) 0,
        C.blockVertex (D.gammaIndex d) 1}) alpha := by
    simp only [BoundaryColorEdges, Finset.mem_filter]
    constructor
    · unfold BoundaryEdges
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨a, ?_, b, ?_, hends⟩
      · simp [haVT, haNeBlock0, haNeBlock1]
      · simp [hbVT]
    · exact hfColor
  have hfOutside : ∃ w, w ∉ VT ∧ Incident G w f :=
    ⟨b, hbVT, hfb⟩
  rcases ((R d).exact_three f).mp ⟨by simpa [VT] using hfRemainder,
      by simpa [VT] using hfOutside⟩ with heq | heq | heq
  · exact heq
  · exact False.elim ((hneInternal (R d).f1 (R d).v1 (R d).u1
      (R d).f1_ends
      (hVTsubXA (Finset.mem_sdiff.mp (R d).v1_in_remainder).1)
      (by simp [XA])) heq)
  · exact False.elim ((hneInternal (R d).f2 (R d).v2 (R d).u2
      (R d).f2_ends
      (hVTsubXA (Finset.mem_sdiff.mp (R d).v2_in_remainder).1)
      (by simp [XA])) heq)

private theorem helper_hnoDeparture_298.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (R : (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))) →
        ScheideReplacementData G k e0 phi T C D d) (alpha : Fin k) (L : ScheideLastExitPath G k e0
        phi T C D R alpha) (hdef : alpha ∈ DefectiveColors G phi (TreeSequenceVertexSet T)),
    let d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T)) := (⟨alpha, hdef⟩ :
        ↥(DefectiveColors G phi (TreeSequenceVertexSet T)));
    let VT : Finset V := TreeSequenceVertexSet T;
    let XA : Finset V := VT ∪ {(R d).u1, (R d).u2};
    let y0 : V := C.y (⟨(0 : ℕ), lt_of_lt_of_le Nat.zero_lt_two C.p_ge_two⟩ : Fin C.p); y0 ∈ XA →
        (
    ∀ f ∈ BoundaryColorEdges G phi XA alpha, f = D.f0 d) → ColoredVertexSetClosed G phi XA →
        L.crossing = D.f0 d →
    ∀ (n : ℕ) (y x : V) (e : E), n + (2 : ℕ) ≤ (↑L.lastIndex : ℕ) → L.path.getVert n = Sum.inl y →
        y ∈ XA → L.path.getVert (n + (1 : ℕ)) = Sum.inr e → L.path.getVert (n + (2 : ℕ)) = Sum.inl
        x → x ∉ XA → False := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D R alpha L hdef d VT XA y0 hy0XA hunique hXAclosed hcrossEq n
      y x e hnl hny hy hne hexc hx
  obtain ⟨hedge, edgeColor⟩ := TwoColorWalk.boundaryAtTwoStep L.path L.pathSimple
    XA n y x e (by have := L.followingVertex; omega) hny hy hne hexc hx
  have hnotzero : phi e ≠ some D.alpha0 := by
    intro hezero
    exact (hXAclosed hedge hy0XA hezero) D.alpha0_missing_at_y0
  have hecolor : phi e = some alpha := by
    rcases edgeColor with hezero | healpha
    · exact False.elim (hnotzero hezero)
    · exact healpha
  have heq : e = D.f0 d := hunique e (by
    simp only [BoundaryColorEdges, Finset.mem_filter]
    exact ⟨hedge, hecolor⟩)
  have hpathEq : e = L.crossing := heq.trans hcrossEq.symm
  have hinj := L.pathSimple.getVert_injOn
    (show n + 1 ≤ L.path.length by
      have h := L.followingVertex
      omega)
    (show L.lastIndex.val + 1 ≤ L.path.length by
      have h := L.followingVertex
      omega)
    (by rw [hne, L.crossingAt, hpathEq])
  omega

theorem ScheideOriginalDefectiveConfinement {V E : Type*}
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
    (hdef : alpha ∈ DefectiveColors G phi (TreeSequenceVertexSet T)) :
    let d : {delta // delta ∈ DefectiveColors G phi
      (TreeSequenceVertexSet T)} := ⟨alpha, hdef⟩
    D.f0 d ∈ BoundaryColorEdges G phi
        (TreeSequenceVertexSet T ∪ {(R d).u1, (R d).u2}) alpha ∧
    (∀ f : E, f ∈ BoundaryColorEdges G phi
        (TreeSequenceVertexSet T ∪ {(R d).u1, (R d).u2}) alpha →
      f = D.f0 d) ∧
    (∀ (j : Fin (L.path.length + 1)), j.val ≤ L.lastIndex.val →
      ∀ x : V, L.path.getVert j.val = Sum.inl x →
        x ∈ TreeSequenceVertexSet T ∪ {(R d).u1, (R d).u2}) ∧
    ∀ f : E, f ∈ BoundaryEdges G (ScheideEnlargedVertexSet R) ∧
      Sum.inr f ∈ TwoColorComponent G phi D.alpha0 alpha
        (Sum.inl (C.y ⟨0, lt_of_lt_of_le Nat.zero_lt_two C.p_ge_two⟩)) →
      f = L.crossing := by
  classical
  let d : {delta // delta ∈ DefectiveColors G phi
      (TreeSequenceVertexSet T)} := ⟨alpha, hdef⟩
  let VT := TreeSequenceVertexSet T
  let XA := VT ∪ {(R d).u1, (R d).u2}
  let X := ScheideEnlargedVertexSet R
  let y0 : V := C.y ⟨0, lt_of_lt_of_le Nat.zero_lt_two C.p_ge_two⟩
  change D.f0 d ∈ BoundaryColorEdges G phi XA alpha ∧
    (∀ f : E, f ∈ BoundaryColorEdges G phi XA alpha → f = D.f0 d) ∧
    (∀ (j : Fin (L.path.length + 1)), j.val ≤ L.lastIndex.val →
      ∀ x : V, L.path.getVert j.val = Sum.inl x → x ∈ XA) ∧
    ∀ f : E, f ∈ BoundaryEdges G X ∧
      Sum.inr f ∈ TwoColorComponent G phi D.alpha0 alpha (Sum.inl y0) →
      f = L.crossing
  have hproper : IsProperEdgeColoring G phi :=
    C.globally_maximum.1.2.2.2.1
  have hVTsubXA : VT ⊆ XA := by
    intro v hv
    simp [XA, hv]
  have hXAsubX : XA ⊆ X := by
    intro v hv
    simp only [XA, Finset.mem_union, Finset.mem_insert,
      Finset.mem_singleton] at hv
    rcases hv with hv | hv | hv
    · simp [X, ScheideEnlargedVertexSet, VT, hv]
    · subst v
      simp only [X, ScheideEnlargedVertexSet, Finset.mem_union]
      right
      apply Finset.mem_biUnion.mpr
      exact ⟨d, Finset.mem_univ d, by simp⟩
    · subst v
      simp only [X, ScheideEnlargedVertexSet, Finset.mem_union]
      right
      apply Finset.mem_biUnion.mpr
      exact ⟨d, Finset.mem_univ d, by simp⟩
  have hy0VT : y0 ∈ VT := by
    have hpos : (0 : ℕ) < T.length + 1 := by omega
    have hv := C.base_vertex_position
      ⟨0, lt_of_lt_of_le Nat.zero_lt_two C.p_ge_two⟩
    simpa [y0, VT, TreeSequenceVertexSet] using
      (show ∃ i : Fin (T.length + 1), T.vertex i = y0 from
        ⟨⟨0, hpos⟩, by simpa [y0] using hv⟩)
  have hy0XA : y0 ∈ XA := hVTsubXA hy0VT
  have hv0VT : D.v0 d ∈ VT := by
    have hmem := D.v0_is_exit d
    change D.v0 d ∈
      Finset.univ.filter (fun v => ScheideExitVertex T phi v) at hmem
    have hexit : ScheideExitVertex T phi (D.v0 d) :=
      (Finset.mem_filter.mp hmem).2
    unfold ScheideExitVertex at hexit
    rcases hexit with
      ⟨u, gamma, delta, hu, hgamma, hdelta, z, p, hp, i, hi, hv, hafter⟩
    simpa only [VT] using hv
  have hu0ne1 : D.u0 d ≠ (R d).u1 := by
    intro heq
    have hadj : AdjacentEdges G (D.f0 d) (R d).f1 :=
      AdjacentEdges.of_endpoint_pairs (by simpa only [heq] using D.f0_ends d)
        ((R d).f1_ends.trans Sym2.eq_swap)
    exact (hproper (R d).f0_ne_f1 hadj (D.f0_color d)) (R d).f1_color
  have hu0ne2 : D.u0 d ≠ (R d).u2 := by
    intro heq
    have hadj : AdjacentEdges G (D.f0 d) (R d).f2 :=
      AdjacentEdges.of_endpoint_pairs (by simpa only [heq] using D.f0_ends d)
        ((R d).f2_ends.trans Sym2.eq_swap)
    exact (hproper (R d).f0_ne_f2 hadj (D.f0_color d)) (R d).f2_color
  have hu0NotXA : D.u0 d ∉ XA := by
    simp only [XA, Finset.mem_union, Finset.mem_insert,
      Finset.mem_singleton, not_or]
    exact ⟨D.u0_outside d, hu0ne1, hu0ne2⟩
  have hf0Boundary : D.f0 d ∈ BoundaryEdges G XA := by
    unfold BoundaryEdges
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨D.v0 d, hVTsubXA hv0VT, D.u0 d, hu0NotXA, D.f0_ends d⟩
  have hf0BC : D.f0 d ∈ BoundaryColorEdges G phi XA alpha := by
    simp only [BoundaryColorEdges, Finset.mem_filter]
    exact ⟨hf0Boundary, D.f0_color d⟩
  obtain ⟨fBlock, hfBlockColor, hfBlockEnds⟩ :=
    (ScheideSymmetricDefectiveInternal G k e0 phi T C D d (R d)).1
  have hblock0VT : C.blockVertex (D.gammaIndex d) 0 ∈ VT := by
    change C.blockVertex (D.gammaIndex d) 0 ∈ TreeSequenceVertexSet T
    rw [← C.block_vertex_position (D.gammaIndex d) (0 : Fin 2)]
    simp [TreeSequenceVertexSet]
  have hblock1VT : C.blockVertex (D.gammaIndex d) 1 ∈ VT := by
    change C.blockVertex (D.gammaIndex d) 1 ∈ TreeSequenceVertexSet T
    rw [← C.block_vertex_position (D.gammaIndex d) (1 : Fin 2)]
    simp [TreeSequenceVertexSet]
  have hunique := @helper_hunique_159 V E inferInstance inferInstance inferInstance inferInstance G
      k e0 phi T C D R alpha hdef hproper hVTsubXA fBlock hfBlockColor hfBlockEnds hblock0VT
      hblock1VT
  have hXAclosed : ColoredVertexSetClosed G phi XA := by
    change ColoredVertexSetClosed G phi
      (TreeSequenceVertexSet T ∪ {(R d).u1, (R d).u2})
    exact ScheideReplacementUnionClosed G k e0 phi T C D d (R d)
  have hcrossXA : L.crossing ∈ BoundaryEdges G XA := by
    unfold BoundaryEdges
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨L.lastInside, hVTsubXA hlast, L.firstOutside, ?_, ?_⟩
    · intro h
      exact L.firstOutsideNotMem (hXAsubX h)
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
  have hcrossEq : L.crossing = D.f0 d := by
    apply hunique
    simp only [BoundaryColorEdges, Finset.mem_filter]
    exact ⟨hcrossXA, L.crossingColor⟩
  have hnoDeparture := @helper_hnoDeparture_298 V E inferInstance inferInstance inferInstance
      inferInstance G k e0 phi T C D R alpha L hdef hy0XA hunique hXAclosed hcrossEq
  have hconf := TwoColorWalk.confinedBefore L.path XA L.lastIndex.val
    (by have := L.followingVertex; omega) hy0XA hnoDeparture
  refine ⟨hf0BC, hunique, ?_, ?_⟩
  · intro j hj x hx
    exact hconf j.val hj x hx
  · intro f hf
    exact TwoColorWalk.lastBoundaryEdgeUnique L.path L.pathSimple X XA hXAsubX
      L.lastIndex L.lastInside L.lastInsideAt L.crossing L.crossingAt
      L.afterLastOutside hconf f hf.1 (by
        have member := hf.2
        rw [← L.pathSpans] at member
        exact member)
end GoldbergSeymour

end
