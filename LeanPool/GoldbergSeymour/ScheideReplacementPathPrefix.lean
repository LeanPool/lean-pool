/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ColoredVertexSetClosed
public import LeanPool.GoldbergSeymour.DefectiveColors
public import LeanPool.GoldbergSeymour.MissingColors
public import LeanPool.GoldbergSeymour.ScheideDefectiveSwitchEffect
public import LeanPool.GoldbergSeymour.ScheideGlobalMaximumOrder
public import LeanPool.GoldbergSeymour.ScheideLastExitPath
public import LeanPool.GoldbergSeymour.ScheideReplacementData
public import LeanPool.GoldbergSeymour.ScheideReplacementMaximum
public import LeanPool.GoldbergSeymour.TreeSequenceVertexSet
public import LeanPool.GoldbergSeymour.TwoColorComponentSwap

/-!
# Scheide Replacement Path Prefix

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private theorem ScheideReplacementPathPrefix_hnoDeparture_193.{u_1, u_2} :
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (R : (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))) →
        ScheideReplacementData G k e0 phi T C D d) (alpha : Fin k) (L : ScheideLastExitPath G k e0
        phi T C D R alpha) (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))),
        TwoColorIncidenceGraph G (TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d)) (↑d : Fin
        k) (Sum.inl (D.v0 d))) D.alpha0 alpha = TwoColorIncidenceGraph G phi D.alpha0 alpha →
        alpha ∉ DefectiveColors G (TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d)) (↑d :
        Fin k) (Sum.inl (D.v0 d))) (TreeSequenceVertexSet (R d).replacementTree) →
    let phiD := TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d)) (↑d : Fin k) (Sum.inl (D.v0
        d));
    let VT := TreeSequenceVertexSet (R d).replacementTree;
    let y0 := C.y ⟨0, lt_of_lt_of_le Nat.zero_lt_two C.p_ge_two⟩; y0 ∈ VT → ColoredVertexSetClosed
        G phiD VT → D.alpha0 ∈ MissingColors G phiD y0 → L.crossing ∈ BoundaryEdges G VT → phiD
        L.crossing = some alpha →
    ∀ (n : ℕ) (y x : V) (e : E), n + 2 ≤ (↑L.lastIndex : ℕ) → L.path.getVert n = Sum.inl y → y ∈
        VT → L.path.getVert (n + 1) = Sum.inr e → L.path.getVert (n + 2) = Sum.inl x → x ∉ VT →
        False := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D R alpha L d hgraph hnondef phiD VT y0 hy0VT hclosed
      hy0Missing hcross hcrossColor n y x e hnl hny hy hne hexc hx
  have ha := L.path.adj_getVert_succ (i := n) (by
    have h := L.followingVertex
    omega)
  have hb := L.path.adj_getVert_succ (i := n + 1) (by
    have h := L.followingVertex
    omega)
  rw [hny, hne] at ha
  rw [hne, hexc] at hb
  rw [← hgraph] at ha hb
  simp only [TwoColorIncidenceGraph, Incident] at ha hb
  have hneYX : y ≠ x := by
    intro heq
    have hi := L.pathSimple.getVert_injOn
      (show n ≤ L.path.length by omega)
      (show n + 2 ≤ L.path.length by omega)
      (by rw [hny, hexc, heq])
    omega
  have hedge : e ∈ BoundaryEdges G VT := by
    unfold BoundaryEdges
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨y, hy, x, hx, (Sym2.mem_and_mem_iff hneYX).mp ⟨ha.1, hb.1⟩⟩
  have hnot0 : phiD e ≠ some D.alpha0 := by
    intro he0
    exact (hclosed hedge hy0VT he0) hy0Missing
  have healpha : phiD e = some alpha := by
    rcases ha.2 with he0 | hea
    · exact False.elim (hnot0 he0)
    · exact hea
  have hene : e ≠ L.crossing := by
    intro heq
    have hi := L.pathSimple.getVert_injOn
      (show n + 1 ≤ L.path.length by omega)
      (show L.lastIndex.val + 1 ≤ L.path.length by
        have hfollow := L.followingVertex
        omega)
      (by rw [hne, L.crossingAt, heq])
    omega
  have hmem : alpha ∈ DefectiveColors G phiD VT := by
    simp only [DefectiveColors, Finset.mem_filter, Finset.mem_univ, true_and]
    change 2 ≤ (BoundaryColorEdges G phiD VT alpha).card
    have hs : ({L.crossing, e} : Finset E) ⊆ BoundaryColorEdges G phiD VT alpha := by
      intro q hq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with rfl | rfl
      · simp only [BoundaryColorEdges, Finset.mem_filter]
        exact ⟨hcross, hcrossColor⟩
      · simp only [BoundaryColorEdges, Finset.mem_filter]
        exact ⟨hedge, healpha⟩
    have hc := Finset.card_le_card hs
    rw [Finset.card_pair hene.symm] at hc
    exact hc
  exact hnondef hmem

private theorem ScheideReplacementPathPrefix_hconf_251.{u_1, u_2} :
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (R : (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))) →
        ScheideReplacementData G k e0 phi T C D d) (alpha : Fin k) (L : ScheideLastExitPath G k e0
        phi T C D R alpha) (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))),
        TwoColorIncidenceGraph G (TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d)) (↑d : Fin
        k) (Sum.inl (D.v0 d))) D.alpha0 alpha = TwoColorIncidenceGraph G phi D.alpha0 alpha →
    let VT := TreeSequenceVertexSet (R d).replacementTree;
    let y0 := C.y ⟨0, lt_of_lt_of_le Nat.zero_lt_two C.p_ge_two⟩; y0 ∈ VT → (
    ∀ (n : ℕ) (y x : V) (e : E), n + 2 ≤ (↑L.lastIndex : ℕ) → L.path.getVert n = Sum.inl y → y ∈
        VT → L.path.getVert (n + 1) = Sum.inr e → L.path.getVert (n + 2) = Sum.inl x → x ∉ VT →
        False) →
    ∀ n ≤ (↑L.lastIndex : ℕ),
    ∀ (x : V), L.path.getVert n = Sum.inl x → x ∈ VT := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D R alpha L d hgraph VT y0 hy0VT hnoDeparture n
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
      rw [L.path.getVert_zero, hx, ← hgraph] at ha
      simp [TwoColorIncidenceGraph] at ha
    · have hprev := L.path.adj_getVert_succ (i := n - 1) (by
        have h := L.followingVertex
        omega)
      rw [show n - 1 + 1 = n by omega, hx] at hprev
      cases hmid : L.path.getVert (n - 1) with
      | inl z =>
          rw [hmid, ← hgraph] at hprev
          simp [TwoColorIncidenceGraph] at hprev
      | inr e =>
          have hbefore := L.path.adj_getVert_succ (i := n - 2) (by
            have h := L.followingVertex
            omega)
          rw [show n - 2 + 1 = n - 1 by omega, hmid] at hbefore
          cases hleft : L.path.getVert (n - 2) with
          | inl y =>
              rw [hleft, ← hgraph] at hbefore
              simp only [TwoColorIncidenceGraph] at hbefore
              have hy := ih (n - 2) (by omega) (by omega) y hleft
              by_cases hxVT : x ∈ VT
              · exact hxVT
              · exfalso
                apply hnoDeparture (n - 2) y x e (by omega)
                  hleft hy (by simpa [show n - 2 + 1 = n - 1 by omega] using hmid)
                  (by simpa [show n - 2 + 2 = n by omega] using hx) hxVT
          | inr q =>
              rw [hleft, ← hgraph] at hbefore
              simp [TwoColorIncidenceGraph] at hbefore

theorem ScheideReplacementPathPrefix {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (C : ScheideReducedConfiguration G k e0 phi T)
    (D : ScheideDefectiveSetup G k e0 phi T C)
    (R : ∀ d : {delta // delta ∈ DefectiveColors G phi
      (TreeSequenceVertexSet T)}, ScheideReplacementData G k e0 phi T C D d)
    (alpha : Fin k)
    (L : ScheideLastExitPath G k e0 phi T C D R alpha)
    (d : {delta // delta ∈ DefectiveColors G phi
      (TreeSequenceVertexSet T)})
    (hpair : L.lastInside ∈ ({(R d).u1, (R d).u2} : Finset V))
    (hgraph : TwoColorIncidenceGraph G
        (TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d)) d.1
          (Sum.inl (D.v0 d))) D.alpha0 alpha =
      TwoColorIncidenceGraph G phi D.alpha0 alpha)
    (hnondef : alpha ∉ DefectiveColors G
      (TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d)) d.1
        (Sum.inl (D.v0 d)))
      (TreeSequenceVertexSet (R d).replacementTree)) :
    ∀ (j : Fin (L.path.length + 1)), j.val ≤ L.lastIndex.val →
    ∀ x : V, L.path.getVert j.val = Sum.inl x → x ∈ TreeSequenceVertexSet (R d).replacementTree
  := by
  classical
  let phiD := TwoColorComponentSwap G phi
    (C.gamma (D.gammaIndex d)) d.1 (Sum.inl (D.v0 d))
  let VT := TreeSequenceVertexSet (R d).replacementTree
  let X := ScheideEnlargedVertexSet R
  let y0 : V := C.y ⟨0, lt_of_lt_of_le Nat.zero_lt_two C.p_ge_two⟩
  have hVTsubX : VT ⊆ X := by
    intro v hv
    change v ∈ TreeSequenceVertexSet (R d).replacementTree at hv
    rw [(R d).replacement_vertices] at hv
    rcases Finset.mem_union.mp hv with hvT | hvPair
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mp hvT).1
    · unfold X ScheideEnlargedVertexSet
      apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      exact ⟨d, Finset.mem_univ _, hvPair⟩
  have hy0VT : y0 ∈ VT := by
    have hposOld : (0 : ℕ) < T.length + 1 := by omega
    have hposNew : (0 : ℕ) < (R d).replacementTree.length + 1 := by omega
    have hzero : (0 : ℕ) ≤ C.p - 1 + 2 * (D.gammaIndex d).val := by omega
    have hv : (R d).replacementTree.vertex ⟨0, hposNew⟩ = y0 := by
      calc
        (R d).replacementTree.vertex ⟨0, hposNew⟩ = T.vertex ⟨0, hposOld⟩ :=
          (R d).retained_vertices_before 0 hzero hposOld
        _ = y0 := by
          simpa [y0] using C.base_vertex_position
            ⟨0, lt_of_lt_of_le Nat.zero_lt_two C.p_ge_two⟩
    simpa [VT, TreeSequenceVertexSet] using
      (show ∃ i : Fin ((R d).replacementTree.length + 1),
        (R d).replacementTree.vertex i = y0 from ⟨⟨0, hposNew⟩, hv⟩)
  have hy0T : y0 ∈ TreeSequenceVertexSet T := by
    have hpos : (0 : ℕ) < T.length + 1 := by omega
    have hv := C.base_vertex_position
      ⟨0, lt_of_lt_of_le Nat.zero_lt_two C.p_ge_two⟩
    simpa [y0, TreeSequenceVertexSet] using
      (show ∃ i : Fin (T.length + 1), T.vertex i = y0 from
        ⟨⟨0, hpos⟩, by simpa [y0] using hv⟩)
  have hclosed : ColoredVertexSetClosed G phiD VT := by
    have hm := ScheideReplacementMaximum G k e0 phi T C D d (R d)
    dsimp at hm
    change ColoredVertexSetClosed G phiD
      (TreeSequenceVertexSet (R d).replacementTree)
    exact (ScheideGlobalMaximumOrder G k e0 phiD (R d).replacementTree
      hm.2.2).2.2.2.2
  have hTclosed : ColoredVertexSetClosed G phi (TreeSequenceVertexSet T) := by
    exact (ScheideGlobalMaximumOrder G k e0 phi T C.globally_maximum).2.2.2.2
  have halpha0NeDelta : D.alpha0 ≠ d.1 := by
    intro heq
    have hf : (R d).f1 ∈ BoundaryEdges G (TreeSequenceVertexSet T) := by
      unfold BoundaryEdges
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨(R d).v1, (Finset.mem_sdiff.mp (R d).v1_in_remainder).1,
        (R d).u1, (R d).u1_outside, (R d).f1_ends⟩
    have hm := D.alpha0_missing_at_y0
    have hc := heq ▸ (R d).f1_color
    exact (hTclosed hf hy0T hc) hm
  have halpha0NeGamma : D.alpha0 ≠ C.gamma (D.gammaIndex d) :=
    D.alpha0_not_block (D.gammaIndex d)
  have hfirstFixed : ∀ e : E,
      phiD e = some D.alpha0 ↔ phi e = some D.alpha0 := by
    intro e
    have hgamma : C.gamma (D.gammaIndex d) ≠ d.1 := by
      intro heq
      have hm : C.gamma (D.gammaIndex d) ∉ PresentColors G phi (D.v0 d) := by
        simpa [MissingColors] using D.gamma_missing_at_v0 d
      apply hm
      unfold PresentColors
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨D.f0 d, by unfold Incident; rw [D.f0_ends]; simp,
        heq.symm ▸ D.f0_color d⟩
    have hother : ∀ c : Fin k, c ≠ C.gamma (D.gammaIndex d) → c ≠ d.1 →
        (phiD e = some c ↔ phi e = some c) := by
      intro c hc hd
      by_cases he : Sum.inr e ∈ TwoColorComponent G phi
          (C.gamma (D.gammaIndex d)) d.1 (Sum.inl (D.v0 d))
      · by_cases hg : phi e = some (C.gamma (D.gammaIndex d))
        · have hv : phiD e = some d.1 := by
            simp [phiD, TwoColorComponentSwap, he, hg]
          rw [hv, hg]
          simp [hc.symm, hd.symm]
        · by_cases hdel : phi e = some d.1
          · have hv : phiD e = some (C.gamma (D.gammaIndex d)) := by
              simp [phiD, TwoColorComponentSwap, he, hdel, hgamma.symm]
            rw [hv, hdel]
            simp [hc.symm, hd.symm]
          · simp [phiD, TwoColorComponentSwap, he, hg, hdel]
      · simp [phiD, TwoColorComponentSwap, he]
    exact hother D.alpha0 halpha0NeGamma halpha0NeDelta
  have hy0Missing : D.alpha0 ∈ MissingColors G phiD y0 := by
    have hnot : D.alpha0 ∉ PresentColors G phiD y0 := by
      intro hm
      simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and] at hm
      obtain ⟨e, he, hec⟩ := hm
      have hec' : phi e = some D.alpha0 := (hfirstFixed e).mp hec
      have hmold : D.alpha0 ∉ PresentColors G phi y0 := by
        simpa [MissingColors] using D.alpha0_missing_at_y0
      apply hmold
      simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨e, he, hec'⟩
    simpa [MissingColors] using hnot
  have hcross : L.crossing ∈ BoundaryEdges G VT := by
    unfold BoundaryEdges
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨L.lastInside, ?_, L.firstOutside, ?_, ?_⟩
    · change L.lastInside ∈ TreeSequenceVertexSet (R d).replacementTree
      rw [(R d).replacement_vertices]
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      exact Or.inr (by simpa using hpair)
    · intro h
      exact L.firstOutsideNotMem (hVTsubX h)
    · have ha := L.path.adj_getVert_succ (i := L.lastIndex.val) (by
        have h := L.followingVertex
        omega)
      have hb := L.path.adj_getVert_succ (i := L.lastIndex.val + 1) (by
        have h := L.followingVertex
        omega)
      rw [L.lastInsideAt, L.crossingAt] at ha
      rw [L.crossingAt, L.firstOutsideAt] at hb
      simp only [TwoColorIncidenceGraph, Incident] at ha hb
      have hne : L.lastInside ≠ L.firstOutside := by
        intro heq
        have hi := L.pathSimple.getVert_injOn
          (show L.lastIndex.val ≤ L.path.length by omega)
          (show L.lastIndex.val + 2 ≤ L.path.length by exact L.followingVertex)
          (by rw [L.lastInsideAt, L.firstOutsideAt, heq])
        omega
      exact (Sym2.mem_and_mem_iff hne).mp ⟨ha.1, hb.1⟩
  have hcrossColor : phiD L.crossing = some alpha := by
    have ha := L.path.adj_getVert_succ (i := L.lastIndex.val) (by
      have h := L.followingVertex
      omega)
    rw [L.lastInsideAt, L.crossingAt, ← hgraph] at ha
    simp only [TwoColorIncidenceGraph, Incident] at ha
    have hnot0 : phiD L.crossing ≠ some D.alpha0 := by
      intro he0
      exact (hclosed hcross hy0VT he0) hy0Missing
    rcases ha.2 with he0 | hea
    · exact False.elim (hnot0 he0)
    · exact hea
  have hnoDeparture :
    ∀ (n : ℕ) (y x : V) (e : E), n + 2 ≤ L.lastIndex.val → L.path.getVert n = Sum.inl y → y ∈ VT →
        L.path.getVert (n + 1) = Sum.inr e → L.path.getVert (n + 2) = Sum.inl x → x ∉ VT → False
  := by
    exact @ScheideReplacementPathPrefix_hnoDeparture_193 V E inferInstance inferInstance
        inferInstance inferInstance G k e0 phi T C D R alpha L d hgraph hnondef hy0VT hclosed
        hy0Missing hcross hcrossColor
  have hconf : ∀ n : ℕ, n ≤ L.lastIndex.val →
      ∀ x : V, L.path.getVert n = Sum.inl x → x ∈ VT := by
    exact @ScheideReplacementPathPrefix_hconf_251 V E inferInstance inferInstance inferInstance
        inferInstance G k e0 phi T C D R alpha L d hgraph hy0VT hnoDeparture
  intro j hj x hx
  exact hconf j.val hj x hx

end GoldbergSeymour

end
