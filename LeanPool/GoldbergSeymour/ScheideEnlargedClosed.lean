/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ColoredVertexSetClosed
public import LeanPool.GoldbergSeymour.ScheideEnlargedElementary
public import LeanPool.GoldbergSeymour.ScheideEnlargedVertexSet
public import LeanPool.GoldbergSeymour.ScheideReplacementPairsLaminar
public import LeanPool.GoldbergSeymour.ScheideReplacementUnionClosed

/-!
# Scheide Enlarged Closed

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private theorem helper_branch_69.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (R : (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))) →
        ScheideReplacementData G k e0 phi T C D d),
    let VT : Finset V := TreeSequenceVertexSet T;
    let X : Finset V := ScheideEnlargedVertexSet R;
    let Def : Finset (Fin k) := DefectiveColors G phi VT;
    ∀ u ∈ X, u ∉ VT →
    ∃ (d : ↥Def), u ∈ VT ∪ (insert (R d).u1 ({(R d).u2} : Finset V) : Finset V) := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D R VT X Def u huX huT
  have huPairs : u ∈ Finset.univ.biUnion
      (fun d : {delta // delta ∈ Def} => {(R d).u1, (R d).u2}) := by
    simpa [X, VT, Def, ScheideEnlargedVertexSet, huT] using huX
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and] at huPairs
  obtain ⟨d, hud⟩ := huPairs
  exact ⟨d, Finset.mem_union_right _ hud⟩

private theorem helper_hXdSub_76.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (R : (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))) →
        ScheideReplacementData G k e0 phi T C D d),
    let VT : Finset V := TreeSequenceVertexSet T;
    let X : Finset V := ScheideEnlargedVertexSet R;
    let Def : Finset (Fin k) := DefectiveColors G phi VT;
    ∀ (d : ↥Def),
    let Xd : Finset V := VT ∪ (insert (R d).u1 ({(R d).u2} : Finset V) : Finset V); Xd ⊆ X := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D R VT X Def d Xd v hv
  simp only [Xd, Finset.mem_union, Finset.mem_insert,
    Finset.mem_singleton] at hv
  rcases hv with hvT | hv1 | hv2
  · exact Finset.mem_union_left _ hvT
  · unfold X ScheideEnlargedVertexSet
    apply Finset.mem_union_right
    apply Finset.mem_biUnion.mpr
    exact ⟨d, Finset.mem_univ _, by simp [hv1]⟩
  · unfold X ScheideEnlargedVertexSet
    apply Finset.mem_union_right
    apply Finset.mem_biUnion.mpr
    exact ⟨d, Finset.mem_univ _, by simp [hv2]⟩

private theorem helper_hclosedD_95.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (R : (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))) →
        ScheideReplacementData G k e0 phi T C D d),
    let VT : Finset V := TreeSequenceVertexSet T;
    let Def : Finset (Fin k) := DefectiveColors G phi VT;
    ∀ (d : ↥Def),
    let Xd : Finset V := VT ∪ (insert (R d).u1 ({(R d).u2} : Finset V) : Finset V);
        ColoredVertexSetClosed G phi Xd := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D R VT Def d Xd
  unfold ColoredVertexSetClosed
  intro g c v hg hv hgc
  exact ScheideReplacementUnionClosed G k e0 phi T C D d (R d)
    (by simpa only [Xd, VT] using hg)
    (by simpa only [Xd, VT] using hv) hgc

private theorem helper_hpairsDisjoint_112.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (R : (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))) →
        ScheideReplacementData G k e0 phi T C D d),
    let VT : Finset V := TreeSequenceVertexSet T;
    let Def : Finset (Fin k) := DefectiveColors G phi VT;
    ∀ {x : V} (d : ↥Def),
    let Xd : Finset V := VT ∪ (insert (R d).u1 ({(R d).u2} : Finset V) : Finset V); x ∉ Xd →
    ∀ (d' : ↥Def), x ∈ (insert (R d').u1 ({(R d').u2} : Finset V) : Finset V) → Disjoint (insert
        (R d).u1 ({(R d).u2} : Finset V) : Finset V) (insert (R d').u1 ({(R d').u2} : Finset V) :
        Finset V) := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D R VT Def x d Xd hxNotXd d' hxd'
  rcases ScheideReplacementPairsLaminar G k e0 phi T C D R d d' with
    heq | hdisj
  · exfalso
    apply hxNotXd
    apply Finset.mem_union_right
    rw [heq]
    exact hxd'
  · exact hdisj

private theorem helper_hXd'Sub_123.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (R : (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))) →
        ScheideReplacementData G k e0 phi T C D d),
    let VT : Finset V := TreeSequenceVertexSet T;
    let X : Finset V := ScheideEnlargedVertexSet R;
    let Def : Finset (Fin k) := DefectiveColors G phi VT;
    ∀ (d' : ↥Def),
    let Xd' : Finset V := VT ∪ (insert (R d').u1 ({(R d').u2} : Finset V) : Finset V); Xd' ⊆ X := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D R VT X Def d' Xd' v hv
  simp only [Xd', Finset.mem_union, Finset.mem_insert,
    Finset.mem_singleton] at hv
  rcases hv with hvT | hv1 | hv2
  · exact Finset.mem_union_left _ hvT
  · unfold X ScheideEnlargedVertexSet
    apply Finset.mem_union_right
    apply Finset.mem_biUnion.mpr
    exact ⟨d', Finset.mem_univ _, by simp [hv1]⟩
  · unfold X ScheideEnlargedVertexSet
    apply Finset.mem_union_right
    apply Finset.mem_biUnion.mpr
    exact ⟨d', Finset.mem_univ _, by simp [hv2]⟩

private theorem helper_hclosedD_138.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (R : (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))) →
        ScheideReplacementData G k e0 phi T C D d),
    let VT : Finset V := TreeSequenceVertexSet T;
    let Def : Finset (Fin k) := DefectiveColors G phi VT;
    ∀ (d' : ↥Def),
    let Xd' : Finset V := VT ∪ (insert (R d').u1 ({(R d').u2} : Finset V) : Finset V);
        ColoredVertexSetClosed G phi Xd' := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D R VT Def d' Xd'
  unfold ColoredVertexSetClosed
  intro g c v hg hv hgc
  exact ScheideReplacementUnionClosed G k e0 phi T C D d' (R d')
    (by simpa only [Xd', VT] using hg)
    (by simpa only [Xd', VT] using hv) hgc

private theorem helper_huNotT_145.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (R : (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))) →
        ScheideReplacementData G k e0 phi T C D d),
    let VT : Finset V := TreeSequenceVertexSet T;
    let Def : Finset (Fin k) := DefectiveColors G phi VT;
    ∀ {f : E} {alpha : Fin k} {x : V}, phi f = some alpha → alpha ∈ MissingColors G phi x →
    ∀ (u w : V), G.ends f = s(u, w) →
    ∀ (d' : ↥Def),
    let Xd' : Finset V := VT ∪ (insert (R d').u1 ({(R d').u2} : Finset V) : Finset V); w ∉ Xd' →
        ColoredVertexSetClosed G phi Xd' → x ∈ Xd' → u ∉ VT := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D R VT Def f alpha x hfalpha hmiss u w hfends d' Xd' hwXd'
      hclosedD' hxXd' huT
  have hfXd' : f ∈ BoundaryEdges G Xd' := by
    unfold BoundaryEdges
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨u, Finset.mem_union_left _ huT, w, hwXd', hfends⟩
  exact (hclosedD' hfXd' hxXd' hfalpha) hmiss

private theorem helper_alphaNotBlock_189.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (R : (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))) →
        ScheideReplacementData G k e0 phi T C D d),
    let VT : Finset V := TreeSequenceVertexSet T;
    let X : Finset V := ScheideEnlargedVertexSet R;
    let Def : Finset (Fin k) := DefectiveColors G phi VT;
    ∀ {alpha : Fin k} {x : V}, x ∈ ScheideEnlargedVertexSet R → alpha ∈ MissingColors G phi x →
    ∀ (d : ↥Def),
    let Xd : Finset V := VT ∪ (insert (R d).u1 ({(R d).u2} : Finset V) : Finset V); Xd ⊆ X → x ∉
        VT →
    ∀ (i : Fin C.s), alpha ≠ C.gamma i := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D R VT X Def alpha x hx hmiss d Xd hXdSub hxNotT i h
  obtain ⟨q, hq⟩ := C.block_color_missing_on_base i
  have hyqT : C.y q ∈ VT := by
    have hlen := C.length_eq
    have hpos : q.val < T.length + 1 := by omega
    have hv := C.base_vertex_position q
    simpa [VT, TreeSequenceVertexSet] using
      (show ∃ j : Fin (T.length + 1), T.vertex j = C.y q from
        ⟨⟨q.val, hpos⟩, by simpa using hv⟩)
  have hyqX : C.y q ∈ X := hXdSub (Finset.mem_union_left _ hyqT)
  have hyqne : C.y q ≠ x := by
    intro heq
    exact hxNotT (heq ▸ hyqT)
  have hdisj := ScheideEnlargedElementary G k e0 phi T C D R
    hyqX hx hyqne
  exact (Finset.disjoint_left.mp hdisj) hq (h.symm ▸ hmiss)

private theorem helper_pairDOutsideD_206.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (R : (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))) →
        ScheideReplacementData G k e0 phi T C D d),
    let VT : Finset V := TreeSequenceVertexSet T;
    let Def : Finset (Fin k) := DefectiveColors G phi VT;
    ∀ (d d' : ↥Def), Disjoint (insert (R d).u1 ({(R d).u2} : Finset V) : Finset V) (insert (R
        d').u1 ({(R d').u2} : Finset V) : Finset V) →
    let Xd' : Finset V := VT ∪ (insert (R d').u1 ({(R d').u2} : Finset V) : Finset V);
    ∀ v ∈ (insert (R d).u1 ({(R d).u2} : Finset V) : Finset V), v ∉ Xd' := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D R VT Def d d' hpairsDisjoint Xd' v hvD hvD'
  simp only [Xd', Finset.mem_union] at hvD'
  rcases hvD' with hvT | hvPair
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hvD
    rcases hvD with rfl | rfl
    · exact (R d).u1_outside hvT
    · exact (R d).u2_outside hvT
  · exact (Finset.disjoint_left.mp hpairsDisjoint) hvD hvPair

private theorem helper_hf1Boundary_216.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (R : (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))) →
        ScheideReplacementData G k e0 phi T C D d),
    let VT : Finset V := TreeSequenceVertexSet T;
    let Def : Finset (Fin k) := DefectiveColors G phi VT;
    ∀ (d d' : ↥Def),
    let Xd' : Finset V := VT ∪ (insert (R d').u1 ({(R d').u2} : Finset V) : Finset V); (
    ∀ v ∈ (insert (R d).u1 ({(R d).u2} : Finset V) : Finset V), v ∉ Xd') → (R d).f1 ∈
        BoundaryEdges G Xd' := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D R VT Def d d' Xd' pairDOutsideD'
  unfold BoundaryEdges
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨(R d).v1, Finset.mem_union_left _
      (Finset.mem_sdiff.mp (R d).v1_in_remainder).1,
    (R d).u1, ?_, (R d).f1_ends⟩
  exact pairDOutsideD' (R d).u1 (by simp)

private theorem helper_gammaNeDelta_230.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C),
    let VT : Finset V := TreeSequenceVertexSet T;
    let Def : Finset (Fin k) := DefectiveColors G phi VT;
    ∀ (d : ↥Def), C.gamma (D.gammaIndex d) ≠ (↑d : Fin k) := by
  classical
  intro V E _ _ _ G k e0 phi T C D VT Def d h
  have hnotPresent : C.gamma (D.gammaIndex d) ∉
      PresentColors G phi (D.v0 d) := by
    simpa [MissingColors] using D.gamma_missing_at_v0 d
  apply hnotPresent
  unfold PresentColors
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨D.f0 d, ?_, ?_⟩
  · unfold Incident
    rw [D.f0_ends]
    simp
  · exact h.symm ▸ D.f0_color d

private theorem helper_hfirstOther_253.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T :
          TreeSequence G e0)
      (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi T C),
      let VT : Finset V := TreeSequenceVertexSet T;
      let Def : Finset (Fin k) := DefectiveColors G phi VT;
      ∀ (d : ↥Def),
        C.gamma (D.gammaIndex d) ≠ (↑d : Fin k) →
          let phiD : PartialEdgeColoring E k :=
            TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d)) (↑d : Fin k) (Sum.inl (D.v0 d));
          ∀ (e : E) (c : Fin k), c ≠ C.gamma (D.gammaIndex d) → c ≠ (↑d : Fin k) → (phiD e = some
              c ↔ phi e = some c) := by
  classical
  intro V E _ _ _ G k e0 phi T C D VT Def d gammaNeDelta phiD e c hcGamma hcDelta
  by_cases he : Sum.inr e ∈ TwoColorComponent G phi
      (C.gamma (D.gammaIndex d)) d.1 (Sum.inl (D.v0 d))
  · by_cases heGamma : phi e = some (C.gamma (D.gammaIndex d))
    · have hvalue : phiD e = some d.1 := by
        simp [phiD, TwoColorComponentSwap, he, heGamma]
      rw [hvalue, heGamma]
      simp [hcGamma.symm, hcDelta.symm]
    · by_cases heDelta : phi e = some d.1
      · have hvalue : phiD e = some (C.gamma (D.gammaIndex d)) := by
          simp [phiD, TwoColorComponentSwap, he, heDelta,
            gammaNeDelta.symm]
        rw [hvalue, heDelta]
        simp [hcGamma.symm, hcDelta.symm]
      · simp [phiD, TwoColorComponentSwap, he, heGamma, heDelta]
  · simp [phiD, TwoColorComponentSwap, he]

private theorem helper_hgraph_278.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C),
    let VT : Finset V := TreeSequenceVertexSet T;
    let Def : Finset (Fin k) := DefectiveColors G phi VT;
    ∀ {alpha : Fin k} (_ : V) (d : ↥Def),
    let phiD : PartialEdgeColoring E k := TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d))
        (↑d : Fin k) (Sum.inl (D.v0 d)); (
    ∀ (e : E), (phiD e = some D.alpha0 ↔ phi e = some D.alpha0) ∧ (phiD e = some alpha ↔ phi e =
        some alpha)) → TwoColorIncidenceGraph G phiD D.alpha0 alpha = TwoColorIncidenceGraph G phi
        D.alpha0 alpha := by
  classical
  intro V E _ _ _ G k e0 phi T C D VT Def alpha w d phiD hfirstFixed
  ext z z'
  cases z with
  | inl v =>
      cases z' with
      | inl w => simp [TwoColorIncidenceGraph]
      | inr e =>
          simp only [TwoColorIncidenceGraph]
          rw [(hfirstFixed e).1, (hfirstFixed e).2]
  | inr e =>
      cases z' with
      | inl v =>
          simp only [TwoColorIncidenceGraph]
          rw [(hfirstFixed e).1, (hfirstFixed e).2]
      | inr g => simp [TwoColorIncidenceGraph]

private theorem helper_hcomponent_294.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C),
    let VT : Finset V := TreeSequenceVertexSet T;
    let Def : Finset (Fin k) := DefectiveColors G phi VT;
    ∀ {alpha : Fin k} (u : V) (d : ↥Def),
    let K : Set (V ⊕ E) := TwoColorComponent G phi D.alpha0 alpha (Sum.inl u);
    let phiD : PartialEdgeColoring E k := TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d))
        (↑d : Fin k) (Sum.inl (D.v0 d)); TwoColorIncidenceGraph G phiD D.alpha0 alpha =
        TwoColorIncidenceGraph G phi D.alpha0 alpha → TwoColorComponent G phiD D.alpha0 alpha
        (Sum.inl u) = K := by
  classical
  intro V E _ _ _ G k e0 phi T C D VT Def alpha u d K phiD hgraph
  change ((TwoColorIncidenceGraph G phiD D.alpha0 alpha).connectedComponentMk
      (Sum.inl u)).supp =
    ((TwoColorIncidenceGraph G phi D.alpha0 alpha).connectedComponentMk
      (Sum.inl u)).supp
  rw [hgraph]

private theorem helper_hrepEdgeAvoid_300.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (R : (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))) →
        ScheideReplacementData G k e0 phi T C D d),
    let VT : Finset V := TreeSequenceVertexSet T;
    let Def : Finset (Fin k) := DefectiveColors G phi VT;
    ∀ {alpha : Fin k} (u : V) (d d' : ↥Def),
    let Xd' : Finset V := VT ∪ (insert (R d').u1 ({(R d').u2} : Finset V) : Finset V);
    let K : Set (V ⊕ E) := TwoColorComponent G phi D.alpha0 alpha (Sum.inl u); (
    ∀ (e : E), (
    ∃ v ∈ Xd', Incident G v e) → Sum.inr e ∉ K) →
    ∀ (r : Fin (R d).replacementTree.length), Sum.inr ((R d).replacementTree.edge r) ∉ K := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D R VT Def alpha u d d' Xd' K hKavoidE r
  apply hKavoidE ((R d).replacementTree.edge r)
  have hmem : (R d).replacementTree.edge r ∈
      Finset.univ.image (R d).replacementTree.edge := by simp
  rw [(R d).replacement_edges] at hmem
  rcases Finset.mem_union.mp hmem with hold | hnew
  · have hold' : (R d).replacementTree.edge r ∈
        Finset.univ.image T.edge :=
      (Finset.mem_erase.mp (Finset.mem_erase.mp hold).2).2
    obtain ⟨q, _, hq⟩ := Finset.mem_image.mp hold'
    obtain ⟨i, hi⟩ := T.attaches q
    refine ⟨T.vertex q.succ, Finset.mem_union_left _ ?_, ?_⟩
    · simp [VT, TreeSequenceVertexSet]
    · unfold Incident
      rw [← hq, hi]
      simp
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hnew
    rcases hnew with hnew | hnew
    · refine ⟨(R d).v1, Finset.mem_union_left _
          (Finset.mem_sdiff.mp (R d).v1_in_remainder).1, ?_⟩
      unfold Incident
      rw [hnew, (R d).f1_ends]
      simp
    · refine ⟨(R d).v2, Finset.mem_union_left _
          (Finset.mem_sdiff.mp (R d).v2_in_remainder).1, ?_⟩
      unfold Incident
      rw [hnew, (R d).f2_ends]
      simp

private theorem helper_pairMissingFixed_380.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (R : (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))) →
        ScheideReplacementData G k e0 phi T C D d),
    let VT : Finset V := TreeSequenceVertexSet T;
    let Def : Finset (Fin k) := DefectiveColors G phi VT;
    ∀ {alpha : Fin k} (u : V) (d : ↥Def),
    let K : Set (V ⊕ E) := TwoColorComponent G phi D.alpha0 alpha (Sum.inl u);
    let phiD : PartialEdgeColoring E k := TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d))
        (↑d : Fin k) (Sum.inl (D.v0 d)); TwoColorComponent G phiD D.alpha0 alpha (Sum.inl u) = K →
        (
    ∀ q ∈ (insert (R d).u1 ({(R d).u2} : Finset V) : Finset V), D.alpha0 ∉ MissingColors G phiD q
        ∧ alpha ∉ MissingColors G phiD q) →
    let psi : PartialEdgeColoring E k := TwoColorComponentSwap G phiD D.alpha0 alpha (Sum.inl u);
        ((
    ∀ (v : V), Sum.inl v ∉ TwoColorComponent G phiD D.alpha0 alpha (Sum.inl u) → MissingColors G
        (TwoColorComponentSwap G phiD D.alpha0 alpha (Sum.inl u)) v = MissingColors G phiD v) ∧ (
    ∀ (v : V), Sum.inl v ∈ TwoColorComponent G phiD D.alpha0 alpha (Sum.inl u) → D.alpha0 ∈
        MissingColors G phiD v → alpha ∈ MissingColors G (TwoColorComponentSwap G phiD D.alpha0
        alpha (Sum.inl u)) v) ∧ (
    ∀ (v : V), Sum.inl v ∈ TwoColorComponent G phiD D.alpha0 alpha (Sum.inl u) → alpha ∈
        MissingColors G phiD v → D.alpha0 ∈ MissingColors G (TwoColorComponentSwap G phiD D.alpha0
        alpha (Sum.inl u)) v) ∧
    ∀ (v : V) (c : Fin k), c ≠ D.alpha0 → c ≠ alpha → (c ∈ MissingColors G (TwoColorComponentSwap
        G phiD D.alpha0 alpha (Sum.inl u)) v ↔ c ∈ MissingColors G phiD v)) →
    ∀ q ∈ (insert (R d).u1 ({(R d).u2} : Finset V) : Finset V), MissingColors G psi q =
        MissingColors G phiD q := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D R VT Def alpha u d K phiD hcomponent pairNotMissing psi
      hbehaviorPsi q hq
  by_cases hqK : Sum.inl q ∈ K
  · have hqKD : Sum.inl q ∈
        TwoColorComponent G phiD D.alpha0 alpha (Sum.inl u) := by
      rw [hcomponent]
      exact hqK
    have hnotOld := pairNotMissing q hq
    have alphaPresent : alpha ∈ PresentColors G phiD q := by
      simpa [MissingColors] using hnotOld.2
    obtain ⟨ea, heaInc, heaColor⟩ := by
      simpa [PresentColors] using alphaPresent
    have heaK : Sum.inr ea ∈
        TwoColorComponent G phiD D.alpha0 alpha (Sum.inl u) := by
      change (TwoColorIncidenceGraph G phiD D.alpha0 alpha).connectedComponentMk
          (Sum.inr ea) =
        (TwoColorIncidenceGraph G phiD D.alpha0 alpha).connectedComponentMk
          (Sum.inl u)
      have hadj : (TwoColorIncidenceGraph G phiD D.alpha0 alpha).Adj
          (Sum.inr ea) (Sum.inl q) := by
        simp [TwoColorIncidenceGraph, heaInc, heaColor]
      exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj).trans
        hqKD
    have alpha0PresentNew : D.alpha0 ∈ PresentColors G psi q := by
      unfold PresentColors
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨ea, heaInc, ?_⟩
      simp [psi, TwoColorComponentSwap, heaK, heaColor]
    have alpha0NotNew : D.alpha0 ∉ MissingColors G psi q := by
      simpa [MissingColors] using alpha0PresentNew
    have alpha0Present : D.alpha0 ∈ PresentColors G phiD q := by
      simpa [MissingColors] using hnotOld.1
    obtain ⟨e0, he0Inc, he0Color⟩ := by
      simpa [PresentColors] using alpha0Present
    have he0K : Sum.inr e0 ∈
        TwoColorComponent G phiD D.alpha0 alpha (Sum.inl u) := by
      change (TwoColorIncidenceGraph G phiD D.alpha0 alpha).connectedComponentMk
          (Sum.inr e0) =
        (TwoColorIncidenceGraph G phiD D.alpha0 alpha).connectedComponentMk
          (Sum.inl u)
      have hadj : (TwoColorIncidenceGraph G phiD D.alpha0 alpha).Adj
          (Sum.inr e0) (Sum.inl q) := by
        simp [TwoColorIncidenceGraph, he0Inc, he0Color]
      exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj).trans
        hqKD
    have alphaPresentNew : alpha ∈ PresentColors G psi q := by
      unfold PresentColors
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨e0, he0Inc, ?_⟩
      simp [psi, TwoColorComponentSwap, he0K, he0Color]
    have alphaNotNew : alpha ∉ MissingColors G psi q := by
      simpa [MissingColors] using alphaPresentNew
    apply Finset.ext
    intro c
    by_cases hc0 : c = D.alpha0
    · subst c
      simp [hnotOld.1, alpha0NotNew]
    · by_cases hca : c = alpha
      · subst c
        simp [hnotOld.2, alphaNotNew]
      · exact hbehaviorPsi.2.2.2 q c hc0 hca
  · apply hbehaviorPsi.1
    rw [hcomponent]
    exact hqK

private theorem helper_hrepMissingFixed_445.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (R : (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))) →
        ScheideReplacementData G k e0 phi T C D d),
    let VT : Finset V := TreeSequenceVertexSet T;
    let Def : Finset (Fin k) := DefectiveColors G phi VT;
    ∀ {alpha : Fin k} (u : V) (d d' : ↥Def),
    let Xd' : Finset V := VT ∪ (insert (R d').u1 ({(R d').u2} : Finset V) : Finset V);
    let K : Set (V ⊕ E) := TwoColorComponent G phi D.alpha0 alpha (Sum.inl u); (
    ∀ v ∈ Xd', Sum.inl v ∉ K) →
    let phiD : PartialEdgeColoring E k := TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d))
        (↑d : Fin k) (Sum.inl (D.v0 d)); TwoColorComponent G phiD D.alpha0 alpha (Sum.inl u) = K →
    let psi : PartialEdgeColoring E k := TwoColorComponentSwap G phiD D.alpha0 alpha (Sum.inl u);
        ((
    ∀ (v : V), Sum.inl v ∉ TwoColorComponent G phiD D.alpha0 alpha (Sum.inl u) → MissingColors G
        (TwoColorComponentSwap G phiD D.alpha0 alpha (Sum.inl u)) v = MissingColors G phiD v) ∧ (
    ∀ (v : V), Sum.inl v ∈ TwoColorComponent G phiD D.alpha0 alpha (Sum.inl u) → D.alpha0 ∈
        MissingColors G phiD v → alpha ∈ MissingColors G (TwoColorComponentSwap G phiD D.alpha0
        alpha (Sum.inl u)) v) ∧ (
    ∀ (v : V), Sum.inl v ∈ TwoColorComponent G phiD D.alpha0 alpha (Sum.inl u) → alpha ∈
        MissingColors G phiD v → D.alpha0 ∈ MissingColors G (TwoColorComponentSwap G phiD D.alpha0
        alpha (Sum.inl u)) v) ∧
    ∀ (v : V) (c : Fin k), c ≠ D.alpha0 → c ≠ alpha → (c ∈ MissingColors G (TwoColorComponentSwap
        G phiD D.alpha0 alpha (Sum.inl u)) v ↔ c ∈ MissingColors G phiD v)) → (
    ∀ q ∈ (insert (R d).u1 ({(R d).u2} : Finset V) : Finset V), MissingColors G psi q =
        MissingColors G phiD q) →
    ∀ q ∈ TreeSequenceVertexSet (R d).replacementTree, MissingColors G psi q = MissingColors G
        phiD q := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D R VT Def alpha u d d' Xd' K hKavoidV phiD hcomponent psi
      hbehaviorPsi pairMissingFixed q hq
  rw [(R d).replacement_vertices] at hq
  rcases Finset.mem_union.mp hq with hqOld | hqPair
  · apply hbehaviorPsi.1
    rw [hcomponent]
    apply hKavoidV q
    exact Finset.mem_union_left _ (Finset.mem_sdiff.mp hqOld).1
  · exact pairMissingFixed q hqPair

private theorem helper_hTashPsi_460.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (R : (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))) →
        ScheideReplacementData G k e0 phi T C D d),
    let VT : Finset V := TreeSequenceVertexSet T;
    let Def : Finset (Fin k) := DefectiveColors G phi VT;
    ∀ {alpha : Fin k} (u : V) (d : ↥Def),
    let phiD : PartialEdgeColoring E k := TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d))
        (↑d : Fin k) (Sum.inl (D.v0 d)); IsProperEdgeColoring G phiD ∧ IsOneEdgeUncolored phiD e0
        ∧ GlobalMaximumTriple G k e0 phiD (R d).replacementTree →
    let psi : PartialEdgeColoring E k := TwoColorComponentSwap G phiD D.alpha0 alpha (Sum.inl u);
        (
    ∀ q ∈ TreeSequenceVertexSet (R d).replacementTree, MissingColors G psi q = MissingColors G
        phiD q) → (
    ∀ (r : Fin (R d).replacementTree.length), psi ((R d).replacementTree.edge r) = phiD ((R
        d).replacementTree.edge r)) → TashkinovTree G e0 psi (R d).replacementTree := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D R VT Def alpha u d phiD hmaximum psi hrepMissingFixed
      hrepEdgeFixed r hr
  obtain ⟨i, c, hc, hm⟩ := hmaximum.2.2.2.1 r hr
  refine ⟨i, c, (hrepEdgeFixed r).trans hc, ?_⟩
  rw [hrepMissingFixed]
  · exact hm
  · simp [TreeSequenceVertexSet]

private theorem helper_honePsi_470.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (R : (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))) →
        ScheideReplacementData G k e0 phi T C D d),
    let VT : Finset V := TreeSequenceVertexSet T;
    let Def : Finset (Fin k) := DefectiveColors G phi VT;
    ∀ {alpha : Fin k} (u : V) (d : ↥Def),
    let phiD : PartialEdgeColoring E k := TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d))
        (↑d : Fin k) (Sum.inl (D.v0 d)); IsProperEdgeColoring G phiD ∧ IsOneEdgeUncolored phiD e0
        ∧ GlobalMaximumTriple G k e0 phiD (R d).replacementTree →
    let psi : PartialEdgeColoring E k := TwoColorComponentSwap G phiD D.alpha0 alpha (Sum.inl u);
        IsOneEdgeUncolored psi e0 := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D R VT Def alpha u d phiD hmaximum psi
  constructor
  · by_cases heK : Sum.inr e0 ∈
        TwoColorComponent G phiD D.alpha0 alpha (Sum.inl u)
    · have he0none : phiD e0 = none := hmaximum.2.1.1
      simp [psi, TwoColorComponentSwap, heK, he0none]
    · have he0none : phiD e0 = none := hmaximum.2.1.1
      simp [psi, TwoColorComponentSwap, heK, he0none]
  · intro e he0
    obtain ⟨c, hc⟩ := hmaximum.2.1.2 e he0
    change phiD e = some c at hc
    by_cases heK : Sum.inr e ∈
        TwoColorComponent G phiD D.alpha0 alpha (Sum.inl u)
    · by_cases hc0 : c = D.alpha0
      · refine ⟨alpha, ?_⟩
        simp only [psi, TwoColorComponentSwap, heK, ite_eq_left]
        rw [hc0] at hc
        rw [hc]
        simp []
      · by_cases hca : c = alpha
        · refine ⟨D.alpha0, ?_⟩
          simp only [psi, TwoColorComponentSwap, heK, ite_eq_left]
          rw [hca] at hc
          rw [hc]
          simp
        · refine ⟨c, ?_⟩
          simp only [psi, TwoColorComponentSwap, heK, ite_eq_left]
          rw [hc]
          simp [hc0, hca]
    · refine ⟨c, ?_⟩
      simp only [psi, TwoColorComponentSwap, heK]
      exact hc

private theorem helper_hrepSubX_524.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (R : (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))) →
        ScheideReplacementData G k e0 phi T C D d),
    let VT : Finset V := TreeSequenceVertexSet T;
    let X : Finset V := ScheideEnlargedVertexSet R;
    let Def : Finset (Fin k) := DefectiveColors G phi VT;
    ∀ (d : ↥Def),
    let Xd : Finset V := VT ∪ (insert (R d).u1 ({(R d).u2} : Finset V) : Finset V); Xd ⊆ X →
        TreeSequenceVertexSet (R d).replacementTree ⊆ X := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D R VT X Def d Xd hXdSub v hv
  rw [(R d).replacement_vertices] at hv
  rcases Finset.mem_union.mp hv with hvOld | hvPair
  · exact hXdSub (Finset.mem_union_left _ (Finset.mem_sdiff.mp hvOld).1)
  · exact hXdSub (Finset.mem_union_right _ hvPair)

private theorem helper_hfK_545.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) {f : E} {alpha : Fin k}, phi f = some alpha →
    ∀ (u w : V), G.ends f = s(u, w) →
    let K : Set (V ⊕ E) := TwoColorComponent G phi D.alpha0 alpha (Sum.inl u); Sum.inr f ∈ K := by
  classical
  intro V E _ _ _ G k e0 phi T C D f alpha hfalpha u w hfends K
  change (TwoColorIncidenceGraph G phi D.alpha0 alpha).connectedComponentMk
      (Sum.inr f) =
    (TwoColorIncidenceGraph G phi D.alpha0 alpha).connectedComponentMk
      (Sum.inl u)
  apply SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
  simp [TwoColorIncidenceGraph, Incident, hfends, hfalpha]

private theorem helper_continuation_878.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (R : (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))) →
        ScheideReplacementData G k e0 phi T C D d),
    let VT : Finset V := TreeSequenceVertexSet T;
    let X : Finset V := ScheideEnlargedVertexSet R;
    let Def : Finset (Fin k) := DefectiveColors G phi VT;
    ∀ {f : E} {alpha : Fin k} (_ : phi f = some alpha) (u w : V) (_ : w ∉ X) (_ : G.ends f = s(u,
        w)) (d : ↥Def),
    let Xd : Finset V := VT ∪ (insert (R d).u1 ({(R d).u2} : Finset V) : Finset V);
    ∀ (_ : Xd ⊆ X) (d' : ↥Def),
    let Xd' : Finset V := VT ∪ (insert (R d').u1 ({(R d').u2} : Finset V) : Finset V);
    ∀ (_ : u ∈ (insert (R d).u1 ({(R d).u2} : Finset V) : Finset V)),
    let _ : V := C.y (⟨(0 : ℕ), lt_of_lt_of_le Nat.zero_lt_two C.p_ge_two⟩ : Fin C.p);
    ∀ (_ : D.alpha0 ≠ alpha),
    let K : Set (V ⊕ E) := TwoColorComponent G phi D.alpha0 alpha (Sum.inl u);
    ∀ (_ :
    ∀ v ∈ Xd', Sum.inl v ∉ K) (_ : D.alpha0 ≠ (↑d : Fin k)) (_ : D.alpha0 ≠ C.gamma (D.gammaIndex
        d)),
    let phiD : PartialEdgeColoring E k := TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d))
        (↑d : Fin k) (Sum.inl (D.v0 d));
    ∀ (_ : IsProperEdgeColoring G phiD ∧ IsOneEdgeUncolored phiD e0 ∧ GlobalMaximumTriple G k e0
        phiD (R d).replacementTree) (_ :
    ∀ (e : E), (phiD e = some D.alpha0 ↔ phi e = some D.alpha0) ∧ (phiD e = some alpha ↔ phi e =
        some alpha)) (_ : TwoColorComponent G phiD D.alpha0 alpha (Sum.inl u) = K) (_ :
    ∀ (r : Fin (R d).replacementTree.length), Sum.inr ((R d).replacementTree.edge r) ∉
        TwoColorComponent G phiD D.alpha0 alpha (Sum.inl u)) (_ : (
    ∀ (v : V), Sum.inl v ∉ TwoColorComponent G phi (C.gamma (D.gammaIndex d)) (↑d : Fin k)
        (Sum.inl (D.v0 d)) → MissingColors G (TwoColorComponentSwap G phi (C.gamma (D.gammaIndex
        d)) (↑d : Fin k) (Sum.inl (D.v0 d))) v = MissingColors G phi v) ∧ (
    ∀ (v : V), Sum.inl v ∈ TwoColorComponent G phi (C.gamma (D.gammaIndex d)) (↑d : Fin k)
        (Sum.inl (D.v0 d)) → C.gamma (D.gammaIndex d) ∈ MissingColors G phi v → (↑d : Fin k) ∈
        MissingColors G (TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d)) (↑d : Fin k)
        (Sum.inl (D.v0 d))) v) ∧ (
    ∀ (v : V), Sum.inl v ∈ TwoColorComponent G phi (C.gamma (D.gammaIndex d)) (↑d : Fin k)
        (Sum.inl (D.v0 d)) → (↑d : Fin k) ∈ MissingColors G phi v → C.gamma (D.gammaIndex d) ∈
        MissingColors G (TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d)) (↑d : Fin k)
        (Sum.inl (D.v0 d))) v) ∧
    ∀ (v : V) (c : Fin k), c ≠ C.gamma (D.gammaIndex d) → c ≠ (↑d : Fin k) → (c ∈ MissingColors G
        (TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d)) (↑d : Fin k) (Sum.inl (D.v0 d))) v
        ↔ c ∈ MissingColors G phi v)) (_ :
    ∀ q ∈ (insert (R d).u1 ({(R d).u2} : Finset V) : Finset V), D.alpha0 ∉ MissingColors G phiD q
        ∧ alpha ∉ MissingColors G phiD q), False := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D R VT X Def f alpha hfalpha u w hwX hfends d Xd hXdSub d' Xd'
      hud y0 ha0alpha K hKavoidV alpha0NeDelta alpha0NeGamma phiD hmaximum hfirstFixed hcomponent
      hrepEdgeAvoidD hbehaviorD pairNotMissing
  let psi := TwoColorComponentSwap G phiD D.alpha0 alpha (Sum.inl u)
  have hbehaviorPsi := TwoColorComponentSwapMissingBehavior G phiD
    D.alpha0 alpha ha0alpha hmaximum.1 (Sum.inl u)
  dsimp only at hbehaviorPsi
  have pairMissingFixed : ∀ q ∈ ({(R d).u1, (R d).u2} : Finset V),
      MissingColors G psi q = MissingColors G phiD q := by
    exact @helper_pairMissingFixed_380 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@phi) (@T) (@C) (@D) (@R) (@alpha) (@u) (@d) (@hcomponent)
        (@pairNotMissing) (@hbehaviorPsi)
  have hrepMissingFixed : ∀ q ∈ TreeSequenceVertexSet (R d).replacementTree,
      MissingColors G psi q = MissingColors G phiD q := by
    exact @helper_hrepMissingFixed_445 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@phi) (@T) (@C) (@D) (@R) (@alpha) (@u) (@d) (@d')
        (@hKavoidV) (@hcomponent) (@hbehaviorPsi) (@pairMissingFixed)
  have hrepEdgeFixed : ∀ r : Fin (R d).replacementTree.length,
      psi ((R d).replacementTree.edge r) =
        phiD ((R d).replacementTree.edge r) := by
    intro r
    simp [psi, TwoColorComponentSwap, hrepEdgeAvoidD r]
  have hTashPsi : TashkinovTree G e0 psi (R d).replacementTree := by
    exact @helper_hTashPsi_460 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@phi) (@T) (@C) (@D) (@R) (@alpha) (@u) (@d) (@hmaximum)
        (@hrepMissingFixed) (@hrepEdgeFixed)
  have hproperPsi : IsProperEdgeColoring G psi :=
    TwoColorComponentSwapProper G phiD D.alpha0 alpha ha0alpha
      hmaximum.1 (Sum.inl u)
  have honePsi : IsOneEdgeUncolored psi e0 := by
    exact @helper_honePsi_470 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@phi) (@T) (@C) (@D) (@R) (@alpha) (@u) (@d) (@hmaximum)
  have hglobalPsi : GlobalMaximumTriple G k e0 psi (R d).replacementTree := by
    refine ⟨?_, hTashPsi, hmaximum.2.2.2.2⟩
    exact ⟨hmaximum.2.2.1.1, hmaximum.2.2.1.2.1,
      hmaximum.2.2.1.2.2.1, hproperPsi, honePsi⟩
  have hy0Rep : y0 ∈ TreeSequenceVertexSet (R d).replacementTree := by
    have hposOld : (0 : ℕ) < T.length + 1 := by omega
    have hposNew : (0 : ℕ) < (R d).replacementTree.length + 1 := by omega
    have hzeroBound : (0 : ℕ) ≤ C.p - 1 + 2 * (D.gammaIndex d).val := by
      have hp := C.p_ge_two
      omega
    have hvertex : (R d).replacementTree.vertex ⟨0, hposNew⟩ = y0 := by
      calc
        (R d).replacementTree.vertex ⟨0, hposNew⟩ =
            T.vertex ⟨0, hposOld⟩ :=
          (R d).retained_vertices_before 0 hzeroBound hposOld
        _ = y0 := by
          simpa [y0] using C.base_vertex_position
            ⟨0, lt_of_lt_of_le Nat.zero_lt_two C.p_ge_two⟩
    simpa [TreeSequenceVertexSet] using
      (show ∃ i : Fin ((R d).replacementTree.length + 1),
          (R d).replacementTree.vertex i = y0 from
        ⟨⟨0, hposNew⟩, hvertex⟩)
  have hrepSubX : TreeSequenceVertexSet (R d).replacementTree ⊆ X := by
    exact @helper_hrepSubX_524 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@phi) (@T) (@C) (@D) (@R) (@d) (@hXdSub)
  have huRep : u ∈ TreeSequenceVertexSet (R d).replacementTree := by
    rw [(R d).replacement_vertices]
    exact Finset.mem_union_right _ hud
  have hwRep : w ∉ TreeSequenceVertexSet (R d).replacementTree :=
    fun hw => hwX (hrepSubX hw)
  have hfRep : f ∈ BoundaryEdges G (TreeSequenceVertexSet (R d).replacementTree) := by
    unfold BoundaryEdges
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨u, huRep, w, hwRep, hfends⟩
  have hy0MissingD : D.alpha0 ∈ MissingColors G phiD y0 :=
    (hbehaviorD.2.2.2 y0 D.alpha0 alpha0NeGamma alpha0NeDelta).2
      D.alpha0_missing_at_y0
  have hy0MissingPsi : D.alpha0 ∈ MissingColors G psi y0 := by
    rw [hrepMissingFixed y0 hy0Rep]
    exact hy0MissingD
  have hfK : Sum.inr f ∈ K := by
    exact @helper_hfK_545 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k) (@e0)
        (@phi) (@T) (@C) (@D) (@f) (@alpha) (@hfalpha) (@u) (@w) (@hfends)
  have hfKD : Sum.inr f ∈
      TwoColorComponent G phiD D.alpha0 alpha (Sum.inl u) := by
    rw [hcomponent]
    exact hfK
  have hfalphaD : phiD f = some alpha := (hfirstFixed f).2.2 hfalpha
  have hfalpha0Psi : psi f = some D.alpha0 := by
    simp [psi, TwoColorComponentSwap, hfKD, hfalphaD]
  have hfinalClosed : ColoredVertexSetClosed G psi
      (TreeSequenceVertexSet (R d).replacementTree) :=
    (ScheideGlobalMaximumOrder G k e0 psi (R d).replacementTree
      hglobalPsi).2.2.2.2
  exact (hfinalClosed hfRep hy0Rep hfalpha0Psi) hy0MissingPsi

private abbrev helperBranch62Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (R : (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))) →
        ScheideReplacementData G k e0 phi T C D d),
    let VT : Finset V := TreeSequenceVertexSet T;
    let _ : Finset V := ScheideEnlargedVertexSet R;
    let Def : Finset (Fin k) := DefectiveColors G phi VT;
    ∀ {f : E} {alpha : Fin k} {x : V}, f ∈ BoundaryEdges G (ScheideEnlargedVertexSet R) → x ∈
        ScheideEnlargedVertexSet R → phi f = some alpha → alpha ∈ MissingColors G phi x →
        Def.Nonempty → False

private theorem helper_branch_62.{u_1, u_2} :
    helperBranch62Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D R VT X Def f alpha x hf hx hfalpha hmiss hdef
  have hfEnds : ∃ u ∈ X, ∃ w ∉ X, G.ends f = s(u, w) := by
    simpa [X, BoundaryEdges, Sym2.mem_iff] using hf
  obtain ⟨u, huX, w, hwX, hfends⟩ := hfEnds
  obtain ⟨d, huXd⟩ : ∃ d : {delta // delta ∈ Def},
      u ∈ VT ∪ {(R d).u1, (R d).u2} := by
    by_cases huT : u ∈ VT
    · obtain ⟨delta, hdelta⟩ := hdef
      exact ⟨⟨delta, hdelta⟩, Finset.mem_union_left _ huT⟩
    · exact @helper_branch_69 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@phi) (@T) (@C) (@D) (@R) (@u) (@huX) (@huT)
  let Xd : Finset V := VT ∪ {(R d).u1, (R d).u2}
  have hXdSub : Xd ⊆ X := by
    exact @helper_hXdSub_76 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@phi) (@T) (@C) (@D) (@R) (@d)
  have hwXd : w ∉ Xd := fun hw => hwX (hXdSub hw)
  have hfXd : f ∈ BoundaryEdges G Xd := by
    unfold BoundaryEdges
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨u, huXd, w, hwXd, hfends⟩
  have hclosedD : ColoredVertexSetClosed G phi Xd := by
    exact @helper_hclosedD_95 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@phi) (@T) (@C) (@D) (@R) (@d)
  have hxNotXd : x ∉ Xd := by
    intro hxXd
    exact (hclosedD hfXd hxXd hfalpha) hmiss
  have hxNotT : x ∉ VT := by
    intro hxT
    exact hxNotXd (Finset.mem_union_left _ hxT)
  have hxPairs : x ∈ Finset.univ.biUnion
      (fun d : {delta // delta ∈ Def} => {(R d).u1, (R d).u2}) := by
    simpa [X, VT, Def, ScheideEnlargedVertexSet, hxNotT] using hx
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and] at hxPairs
  obtain ⟨d', hxd'⟩ := hxPairs
  have hpairsDisjoint : Disjoint ({(R d).u1, (R d).u2} : Finset V)
      ({(R d').u1, (R d').u2} : Finset V) := by
    exact @helper_hpairsDisjoint_112 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@phi) (@T) (@C) (@D) (@R) (@x) (@d) (@hxNotXd) (@d') (@hxd')
  let Xd' : Finset V := VT ∪ {(R d').u1, (R d').u2}
  have hXd'Sub : Xd' ⊆ X := by
    exact @helper_hXd'Sub_123 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@phi) (@T) (@C) (@D) (@R) (@d')
  have hwXd' : w ∉ Xd' := fun hw => hwX (hXd'Sub hw)
  have hclosedD' : ColoredVertexSetClosed G phi Xd' := by
    exact @helper_hclosedD_138 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@phi) (@T) (@C) (@D) (@R) (@d')
  have hxXd' : x ∈ Xd' := Finset.mem_union_right _ hxd'
  have huNotT : u ∉ VT := by
    exact @helper_huNotT_145 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@phi) (@T) (@C) (@D) (@R) (@f) (@alpha) (@x) (@hfalpha) (@hmiss) (@u)
        (@w) (@hfends) (@d') (@hwXd') (@hclosedD') (@hxXd')
  have hud : u ∈ ({(R d).u1, (R d).u2} : Finset V) := by
    simpa [Xd, huNotT] using huXd
  have huNotPairD' : u ∉ ({(R d').u1, (R d').u2} : Finset V) :=
    fun hu' => Finset.disjoint_left.mp hpairsDisjoint hud hu'
  have huNotXd' : u ∉ Xd' := by
    intro hu
    rcases Finset.mem_union.mp hu with huT | huPair
    · exact huNotT huT
    · exact huNotPairD' huPair
  let y0 : V := C.y ⟨0, lt_of_lt_of_le Nat.zero_lt_two C.p_ge_two⟩
  have hy0T : y0 ∈ VT := by
    have hpos : (0 : ℕ) < T.length + 1 := by omega
    have hv := C.base_vertex_position
      ⟨0, lt_of_lt_of_le Nat.zero_lt_two C.p_ge_two⟩
    simpa [y0, VT, TreeSequenceVertexSet] using
      (show ∃ i : Fin (T.length + 1), T.vertex i = y0 from
        ⟨⟨0, hpos⟩, by simpa [y0] using hv⟩)
  have hy0X : y0 ∈ X := hXdSub (Finset.mem_union_left _ hy0T)
  have hy0Xd' : y0 ∈ Xd' := Finset.mem_union_left _ hy0T
  have hy0neX : y0 ≠ x := by
    intro h
    exact hxNotT (h ▸ hy0T)
  have ha0alpha : D.alpha0 ≠ alpha := by
    intro h
    have hdisj := ScheideEnlargedElementary G k e0 phi T C D R
      hy0X hx hy0neX
    exact (Finset.disjoint_left.mp hdisj) D.alpha0_missing_at_y0
      (h ▸ hmiss)
  let K := TwoColorComponent G phi D.alpha0 alpha (Sum.inl u)
  have havoid := ClosedSetTwoColorComponentAvoidance G phi D.alpha0 alpha
    Xd' u y0 x hclosedD' huNotXd' hy0Xd' hxXd'
    D.alpha0_missing_at_y0 hmiss
  have hKavoidV : ∀ v ∈ Xd', Sum.inl v ∉ K := by
    simpa [K] using havoid.1
  have hKavoidE : ∀ e : E, (∃ v ∈ Xd', Incident G v e) →
      Sum.inr e ∉ K := by
    simpa [K] using havoid.2
  have alphaNotBlock : ∀ i : Fin C.s, alpha ≠ C.gamma i := by
    exact @helper_alphaNotBlock_189 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@phi) (@T) (@C) (@D) (@R) (@alpha) (@x) (@hx) (@hmiss)
        (@d) (@hXdSub) (@hxNotT)
  have pairDOutsideD' : ∀ v ∈ ({(R d).u1, (R d).u2} : Finset V),
      v ∉ Xd' := by
    exact @helper_pairDOutsideD_206 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@phi) (@T) (@C) (@D) (@R) (@d) (@d') (@hpairsDisjoint)
  have hf1Boundary : (R d).f1 ∈ BoundaryEdges G Xd' := by
    exact @helper_hf1Boundary_216 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@phi) (@T) (@C) (@D) (@R) (@d) (@d') (@pairDOutsideD')
  have alphaNeDelta : alpha ≠ d.1 := by
    intro h
    exact (hclosedD' hf1Boundary hxXd' (h.symm ▸ (R d).f1_color)) hmiss
  have alpha0NeDelta : D.alpha0 ≠ d.1 := by
    intro h
    exact (hclosedD' hf1Boundary hy0Xd'
      (h.symm ▸ (R d).f1_color)) D.alpha0_missing_at_y0
  have gammaNeDelta : C.gamma (D.gammaIndex d) ≠ d.1 := by
    exact @helper_gammaNeDelta_230 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
        (@e0) (@phi) (@T) (@C) (@D) (@d)
  have alpha0NeGamma : D.alpha0 ≠ C.gamma (D.gammaIndex d) :=
    D.alpha0_not_block (D.gammaIndex d)
  have alphaNeGamma : alpha ≠ C.gamma (D.gammaIndex d) :=
    alphaNotBlock (D.gammaIndex d)
  let phiD := TwoColorComponentSwap G phi
    (C.gamma (D.gammaIndex d)) d.1 (Sum.inl (D.v0 d))
  have hmaximum := ScheideReplacementMaximum G k e0 phi T C D d (R d)
  dsimp only at hmaximum
  change IsProperEdgeColoring G phiD ∧ IsOneEdgeUncolored phiD e0 ∧
    GlobalMaximumTriple G k e0 phiD (R d).replacementTree at hmaximum
  have hfirstOther : ∀ (e : E) (c : Fin k),
      c ≠ C.gamma (D.gammaIndex d) → c ≠ d.1 →
      (phiD e = some c ↔ phi e = some c) := by
    exact @helper_hfirstOther_253 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
        (@e0) (@phi) (@T) (@C) (@D) (@d) (@gammaNeDelta)
  have hfirstFixed : ∀ e : E,
      (phiD e = some D.alpha0 ↔ phi e = some D.alpha0) ∧
        (phiD e = some alpha ↔ phi e = some alpha) := by
    intro e
    exact ⟨hfirstOther e D.alpha0 alpha0NeGamma alpha0NeDelta,
      hfirstOther e alpha alphaNeGamma alphaNeDelta⟩
  have hgraph : TwoColorIncidenceGraph G phiD D.alpha0 alpha =
      TwoColorIncidenceGraph G phi D.alpha0 alpha := by
    exact @helper_hgraph_278 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k) (@e0)
        (@phi) (@T) (@C) (@D) (@alpha) (@w) (@d) (@hfirstFixed)
  have hcomponent : TwoColorComponent G phiD D.alpha0 alpha (Sum.inl u) = K := by
    exact @helper_hcomponent_294 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
        (@e0) (@phi) (@T) (@C) (@D) (@alpha) (@u) (@d) (@hgraph)
  have hrepEdgeAvoid : ∀ r : Fin (R d).replacementTree.length,
      Sum.inr ((R d).replacementTree.edge r) ∉ K := by
    exact @helper_hrepEdgeAvoid_300 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@phi) (@T) (@C) (@D) (@R) (@alpha) (@u) (@d) (@d')
        (@hKavoidE)
  have hrepEdgeAvoidD : ∀ r : Fin (R d).replacementTree.length,
      Sum.inr ((R d).replacementTree.edge r) ∉
        TwoColorComponent G phiD D.alpha0 alpha (Sum.inl u) := by
    intro r hr
    apply hrepEdgeAvoid r
    rw [← hcomponent]
    exact hr
  have hproper : IsProperEdgeColoring G phi :=
    C.globally_maximum.1.2.2.2.1
  have hbehaviorD := TwoColorComponentSwapMissingBehavior G phi
    (C.gamma (D.gammaIndex d)) d.1 gammaNeDelta hproper
    (Sum.inl (D.v0 d))
  dsimp only at hbehaviorD
  have pairNotMissing : ∀ q ∈ ({(R d).u1, (R d).u2} : Finset V),
      D.alpha0 ∉ MissingColors G phiD q ∧
        alpha ∉ MissingColors G phiD q := by
    intro q hq
    have hqT : q ∉ VT := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with rfl | rfl
      · exact (R d).u1_outside
      · exact (R d).u2_outside
    have hqX : q ∈ X := hXdSub (Finset.mem_union_right _ hq)
    have hy0q : y0 ≠ q := by
      intro h
      exact hqT (h ▸ hy0T)
    have hxq : x ≠ q := by
      intro h
      exact pairDOutsideD' q hq (h ▸ hxXd')
    have ha0Old : D.alpha0 ∉ MissingColors G phi q := by
      intro hqmiss
      have hdisj := ScheideEnlargedElementary G k e0 phi T C D R
        hy0X hqX hy0q
      exact (Finset.disjoint_left.mp hdisj) D.alpha0_missing_at_y0 hqmiss
    have halphaOld : alpha ∉ MissingColors G phi q := by
      intro hqmiss
      have hdisj := ScheideEnlargedElementary G k e0 phi T C D R
        hx hqX hxq
      exact (Finset.disjoint_left.mp hdisj) hmiss hqmiss
    constructor
    · intro hnew
      exact ha0Old ((hbehaviorD.2.2.2 q D.alpha0 alpha0NeGamma
        alpha0NeDelta).mp hnew)
    · intro hnew
      exact halphaOld ((hbehaviorD.2.2.2 q alpha alphaNeGamma
        alphaNeDelta).mp hnew)
  exact @helper_continuation_878 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@phi) (@T) (@C) (@D) (@R) (@f) (@alpha) (@hfalpha) (@u) (@w)
      (@hwX) (@hfends) (@d) (@hXdSub) (@d') (@hud) (@ha0alpha) (@hKavoidV) (@alpha0NeDelta)
      (@alpha0NeGamma) (@hmaximum) (@hfirstFixed) (@hcomponent) (@hrepEdgeAvoidD) (@hbehaviorD)
      (@pairNotMissing)
theorem ScheideEnlargedClosed {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (C : ScheideReducedConfiguration G k e0 phi T)
    (D : ScheideDefectiveSetup G k e0 phi T C)
    (R : ∀ d : {delta // delta ∈ DefectiveColors G phi
      (TreeSequenceVertexSet T)}, ScheideReplacementData G k e0 phi T C D d) :
    ColoredVertexSetClosed G phi (ScheideEnlargedVertexSet R) := by
  classical
  let VT := TreeSequenceVertexSet T
  let X := ScheideEnlargedVertexSet R
  let Def := DefectiveColors G phi VT
  have htreeClosed : ColoredVertexSetClosed G phi VT :=
    (ScheideGlobalMaximumOrder G k e0 phi T C.globally_maximum).2.2.2.2
  unfold ColoredVertexSetClosed at htreeClosed ⊢
  intro f alpha x hf hx hfalpha hmiss
  by_cases hdef : Def.Nonempty
  · exact @helper_branch_62 V E inferInstance inferInstance inferInstance inferInstance G k e0
      phi T C D R f alpha x hf hx hfalpha hmiss hdef
  · let : IsEmpty {delta // delta ∈
        DefectiveColors G phi (TreeSequenceVertexSet T)} :=
      ⟨fun d => hdef ⟨d.1, by simp [Def, VT]⟩⟩
    have hXeq : X = VT := by
      unfold X ScheideEnlargedVertexSet
      simp [VT]
    exact htreeClosed (by simpa [X, hXeq] using hf)
      (by simpa [X, hXeq] using hx) hfalpha hmiss

end GoldbergSeymour

end
