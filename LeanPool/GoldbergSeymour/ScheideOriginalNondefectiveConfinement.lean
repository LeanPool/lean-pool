/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

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
  have ha1 := L.path.adj_getVert_succ (i := n) (by
    have h := L.followingVertex
    omega)
  have ha2 := L.path.adj_getVert_succ (i := n + 1) (by
    have h := L.followingVertex
    omega)
  rw [show n + 1 + 1 = n + 2 by omega] at ha2
  rw [hny, hne] at ha1
  rw [hne, hexc] at ha2
  simp only [TwoColorIncidenceGraph, Incident] at ha1 ha2
  have hvne : y ≠ x := by
    intro heq
    have hinj := L.pathSimple.getVert_injOn
      (show n ≤ L.path.length by
        have h := L.followingVertex
        omega)
      (show n + 2 ≤ L.path.length by
        have h := L.followingVertex
        omega)
      (by rw [hny, hexc, heq])
    omega
  have hedge : e ∈ BoundaryEdges G VT := by
    unfold BoundaryEdges
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨y, hy, x, hx, ?_⟩
    exact (Sym2.mem_and_mem_iff hvne).mp ⟨ha1.1, ha2.1⟩
  have hnotzero : phi e ≠ some D.alpha0 := by
    intro hezero
    exact (hVTclosed hedge hy0VT hezero) D.alpha0_missing_at_y0
  have hecolor : phi e = some alpha := by
    rcases ha1.2 with hezero | healpha
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

private theorem ScheideOriginalNondefectiveConfinement_hconf_169.{u_1, u_2} :
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (R : (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))) →
        ScheideReplacementData G k e0 phi T C D d) (alpha : Fin k) (L : ScheideLastExitPath G k e0
        phi T C D R alpha),
    let VT := TreeSequenceVertexSet T;
    let y0 := C.y ⟨0, lt_of_lt_of_le Nat.zero_lt_two C.p_ge_two⟩; y0 ∈ VT → (
    ∀ (n : ℕ) (y x : V) (e : E), n + 2 ≤ (↑L.lastIndex : ℕ) → L.path.getVert n = Sum.inl y → y ∈
        VT → L.path.getVert (n + 1) = Sum.inr e → L.path.getVert (n + 2) = Sum.inl x → x ∉ VT →
        False) →
    ∀ n ≤ (↑L.lastIndex : ℕ),
    ∀ (x : V), L.path.getVert n = Sum.inl x → x ∈ VT := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D R alpha L VT y0 hy0VT hnoDeparture n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro hn x hx
      by_cases hn0 : n = 0
      · subst n
        rw [L.path.getVert_zero] at hx
        injection hx with hxe
        subst x
        exact hy0VT
      by_cases hn1 : n = 1
      · have ha := L.path.adj_getVert_succ (i := 0) (by
          have h := L.followingVertex
          omega)
        subst n
        rw [L.path.getVert_zero, hx] at ha
        simp [TwoColorIncidenceGraph] at ha
      · have hprev := L.path.adj_getVert_succ (i := n - 1) (by
          have h := L.followingVertex
          omega)
        rw [show n - 1 + 1 = n by omega, hx] at hprev
        cases hmid : L.path.getVert (n - 1) with
        | inl z =>
            rw [hmid] at hprev
            simp [TwoColorIncidenceGraph] at hprev
        | inr e =>
            have hbefore := L.path.adj_getVert_succ (i := n - 2) (by
              have h := L.followingVertex
              omega)
            rw [show n - 2 + 1 = n - 1 by omega, hmid] at hbefore
            cases hleft : L.path.getVert (n - 2) with
            | inl y =>
                rw [hleft] at hbefore
                simp only [TwoColorIncidenceGraph] at hbefore
                have hy := ih (n - 2) (by omega) (by omega) y hleft
                by_cases hxVT : x ∈ VT
                · exact hxVT
                · exfalso
                  apply hnoDeparture (n - 2) y x e (by omega)
                    hleft hy (by simpa [show n - 2 + 1 = n - 1 by omega] using hmid)
                      (by simpa [show n - 2 + 2 = n by omega] using hx) hxVT
            | inr q =>
                rw [hleft] at hbefore
                simp [TwoColorIncidenceGraph] at hbefore

private theorem ScheideOriginalNondefectiveConfinement_branch_218.{u_1, u_2} :
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (R : (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))) →
        ScheideReplacementData G k e0 phi T C D d) (alpha : Fin k) (L : ScheideLastExitPath G k e0
        phi T C D R alpha),
    let VT := TreeSequenceVertexSet T;
    let X := ScheideEnlargedVertexSet R; VT ⊆ X → (
    ∀ n ≤ (↑L.lastIndex : ℕ),
    ∀ (x : V), L.path.getVert n = Sum.inl x → x ∈ VT) →
    ∀ (f : E), f ∈ BoundaryEdges G (ScheideEnlargedVertexSet R) ∧ Sum.inr f ∈ TwoColorComponent G
        phi D.alpha0 alpha (Sum.inl (C.y ⟨0, lt_of_lt_of_le Nat.zero_lt_two C.p_ge_two⟩)) → f =
        L.crossing := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D R alpha L VT X hVTsubX hconf f hf
  obtain ⟨u, hu, w, hw, hends⟩ : ∃ u ∈ X, ∃ w ∉ X, G.ends f = s(u, w) := by
    simpa [X, BoundaryEdges] using hf.1
  have hneuw : u ≠ w := by
    intro h
    exact G.loopless f u (h ▸ hends)
  have hfsupport : Sum.inr f ∈ L.path.support := by
    have hcomponent := hf.2
    rw [← L.pathSpans] at hcomponent
    exact hcomponent
  obtain ⟨n, hnget, hnle⟩ :=
    SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hfsupport
  have hnpos : 0 < n := by
    by_cases hnzero : n = 0
    · subst n
      rw [L.path.getVert_zero] at hnget
      cases hnget
    · omega
  have hnlt : n < L.path.length := by
    by_contra hnl
    have heq : n = L.path.length := by omega
    subst n
    rw [L.path.getVert_length] at hnget
    cases hnget
  have hprev := L.path.adj_getVert_succ (i := n - 1) (by omega)
  have hnext := L.path.adj_getVert_succ (i := n) hnlt
  rw [show n - 1 + 1 = n by omega, hnget] at hprev
  have hprevExists : ∃ vprev : V, L.path.getVert (n - 1) = Sum.inl vprev := by
    cases hprevVert : L.path.getVert (n - 1) with
    | inl vprev => exact ⟨vprev, rfl⟩
    | inr q =>
        rw [hprevVert] at hprev
        simp [TwoColorIncidenceGraph] at hprev
  obtain ⟨vprev, hprevVert⟩ := hprevExists
  rw [hprevVert] at hprev
  simp only [TwoColorIncidenceGraph, Incident] at hprev
  rw [hnget] at hnext
  have hnextExists : ∃ vnext : V, L.path.getVert (n + 1) = Sum.inl vnext := by
    cases hnextVert : L.path.getVert (n + 1) with
    | inl vnext => exact ⟨vnext, rfl⟩
    | inr q =>
        rw [hnextVert] at hnext
        simp [TwoColorIncidenceGraph] at hnext
  obtain ⟨vnext, hnextVert⟩ := hnextExists
  rw [hnextVert] at hnext
  simp only [TwoColorIncidenceGraph, Incident] at hnext
  have hprevEnds : vprev = u ∨ vprev = w := by
    rw [hends] at hprev
    simpa [Sym2.mem_iff] using hprev.1
  have hnextEnds : vnext = u ∨ vnext = w := by
    rw [hends] at hnext
    simpa [Sym2.mem_iff] using hnext.1
  have hvne : vprev ≠ vnext := by
    intro heq
    have hidx := L.pathSimple.getVert_injOn
      (show n - 1 ≤ L.path.length by omega)
      (show n + 1 ≤ L.path.length by omega)
      (by rw [hprevVert, hnextVert, heq])
    omega
  have hprevXor : (vprev ∈ X ∧ vnext ∉ X) ∨
      (vprev ∉ X ∧ vnext ∈ X) := by
    rcases hprevEnds with hpu | hpw <;> rcases hnextEnds with hnu | hnw
    · exfalso
      apply hvne
      exact hpu.trans hnu.symm
    · left
      constructor
      · simpa [hpu] using hu
      · simpa [hnw] using hw
    · right
      constructor
      · simpa [hpw] using hw
      · simpa [hnu] using hu
    · exfalso
      apply hvne
      exact hpw.trans hnw.symm
  have hprevIn : n - 1 ≤ L.lastIndex.val := by
    rcases hprevXor with hcase | hcase
    · by_contra hnot
      have hout := L.afterLastOutside ⟨n - 1, by
        have h := hnlt
        omega⟩ (by
          change L.lastIndex.val < n - 1
          omega)
        vprev hprevVert
      exact hout hcase.1
    · have hnextIn : n + 1 ≤ L.lastIndex.val := by
        by_contra hbad
        have hout := L.afterLastOutside ⟨n + 1, by
          have h := hnlt
          omega⟩ (by
            change L.lastIndex.val < n + 1
            omega)
          vnext hnextVert
        exact hout hcase.2
      exact False.elim (hcase.1 (hVTsubX (hconf (n - 1) (by omega)
        vprev hprevVert)))
  have hnextOut : ¬ n + 1 ≤ L.lastIndex.val := by
    by_contra hnext
    have hvnextX := hVTsubX (hconf (n + 1) hnext vnext hnextVert)
    rcases hprevXor with hcase | hcase
    · exact hcase.2 hvnextX
    · exact hcase.1 (hVTsubX (hconf (n - 1) hprevIn vprev hprevVert))
  have hidx : n = L.lastIndex.val + 1 := by
    have hsub : n - 1 + 1 ≤ L.lastIndex.val + 1 :=
      Nat.succ_le_succ hprevIn
    have hle : n ≤ L.lastIndex.val + 1 := by
      simpa [Nat.sub_add_cancel (by omega : 1 ≤ n)] using hsub
    have hneq : n ≠ L.lastIndex.val := by
      intro heq
      have hbad := hnget
      rw [heq, L.lastInsideAt] at hbad
      cases hbad
    have hgt : L.lastIndex.val < n := by
      by_contra hnot
      have hnle : n ≤ L.lastIndex.val := by omega
      have hsucc : n + 1 ≤ L.lastIndex.val := by omega
      exact hnextOut hsucc
    have hge : L.lastIndex.val + 1 ≤ n := by omega
    omega
  have heq : (Sum.inr f : Sum V E) = Sum.inr L.crossing := by
    rw [← hnget, hidx, L.crossingAt]
  injection heq

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
    exact @ScheideOriginalNondefectiveConfinement_hconf_169 V E inferInstance inferInstance
        inferInstance inferInstance G k e0 phi T C D R alpha L hy0VT hnoDeparture
  constructor
  · intro j hj x hx
    exact hconf j.val hj x hx
  · exact @ScheideOriginalNondefectiveConfinement_branch_218 V E inferInstance inferInstance
      inferInstance inferInstance G k e0 phi T C D R alpha L hVTsubX hconf
end GoldbergSeymour

end
