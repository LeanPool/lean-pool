/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ScheideSingleBoundaryCrossing

/-!
# Scheide Enlarged Boundary Selection

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

open scoped Sym2

private theorem helper_hDefUnique_410.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V]
      [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k)
      (T : TreeSequence G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D :
          ScheideDefectiveSetup G k e0 phi T C)
      (R : (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))) → ScheideReplacementData G k
          e0 phi T C D d),
      let VT : Finset V := TreeSequenceVertexSet T;
      let Def : Finset (Fin k) := DefectiveColors G phi VT;
      let Pair : ↥Def → Finset V := fun (d : ↥Def) ↦ {(R d).u1, (R d).u2};
      IsProperEdgeColoring G phi →
        (∀ (a : ↥Def) (j : Fin (2 : ℕ)), C.blockVertex (D.gammaIndex a) j ∈ VT) →
          ∀ (a : ↥Def), ∀ e ∈ BoundaryColorEdges G phi (VT ∪ Pair a) (↑a : Fin k), e = D.f0 a := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D R VT Def Pair hproper hblockVT a e he
  let XA := VT ∪ Pair a
  let Z := VT \ {C.blockVertex (D.gammaIndex a) 0,
    C.blockVertex (D.gammaIndex a) 1}
  have heBoundary : e ∈ BoundaryEdges G XA :=
    (Finset.mem_filter.mp he).1
  have heColor : phi e = some a.1 :=
    (Finset.mem_filter.mp he).2
  obtain ⟨x, hxXA, z, hzXA, hexz⟩ := by
    simpa [BoundaryEdges] using heBoundary
  obtain ⟨g, hgColor, hgEnds⟩ :=
    (ScheideSymmetricDefectiveInternal G k e0 phi T C D a (R a)).1
  have hblock0XA : C.blockVertex (D.gammaIndex a) 0 ∈ XA :=
    Finset.mem_union_left _ (hblockVT a 0)
  have hblock1XA : C.blockVertex (D.gammaIndex a) 1 ∈ XA :=
    Finset.mem_union_left _ (hblockVT a 1)
  have heg : e ≠ g := by
    intro heg
    have hzEnds : z ∈ G.ends g := by
      rw [← heg, hexz]
      simp
    rw [hgEnds] at hzEnds
    simp only [Sym2.mem_iff] at hzEnds
    rcases hzEnds with hz0 | hz1
    · exact hzXA (hz0 ▸ hblock0XA)
    · exact hzXA (hz1 ▸ hblock1XA)
  by_cases hxVT : x ∈ VT
  · have hx0 : x ≠ C.blockVertex (D.gammaIndex a) 0 := by
      intro hx0
      exact (hproper heg
        ⟨x, by change x ∈ G.ends e; rw [hexz]; simp,
          by change x ∈ G.ends g; rw [hgEnds, hx0]; simp⟩ heColor) hgColor
    have hx1 : x ≠ C.blockVertex (D.gammaIndex a) 1 := by
      intro hx1
      exact (hproper heg
        ⟨x, by change x ∈ G.ends e; rw [hexz]; simp,
          by change x ∈ G.ends g; rw [hgEnds, hx1]; simp⟩ heColor) hgColor
    have hxZ : x ∈ Z := by
      exact Finset.mem_sdiff.mpr ⟨hxVT, by simp [hx0, hx1]⟩
    have hzVT : z ∉ VT := by
      intro hz
      exact hzXA (Finset.mem_union_left _ hz)
    have heZ : e ∈ BoundaryColorEdges G phi Z a.1 := by
      apply Finset.mem_filter.mpr
      refine ⟨?_, heColor⟩
      simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨x, hxZ, z, fun hz => hzVT (Finset.mem_sdiff.mp hz).1, hexz⟩
    have heOutside : ∃ w, w ∉ VT ∧ Incident G w e := by
      exact ⟨z, hzVT, by change z ∈ G.ends e; rw [hexz]; simp⟩
    rcases ((R a).exact_three e).mp ⟨by simpa [Z] using heZ, heOutside⟩ with
      he0 | he1 | he2
    · exact he0
    · exfalso
      have hzEnds : z ∈ G.ends (R a).f1 := by
        rw [← he1, hexz]
        simp
      rw [(R a).f1_ends] at hzEnds
      simp only [Sym2.mem_iff] at hzEnds
      rcases hzEnds with hzv | hzu
      · exact hzXA (hzv ▸ Finset.mem_union_left _
          (Finset.mem_sdiff.mp (R a).v1_in_remainder).1)
      · exact hzXA (hzu ▸ Finset.mem_union_right _ (by simp [Pair]))
    · exfalso
      have hzEnds : z ∈ G.ends (R a).f2 := by
        rw [← he2, hexz]
        simp
      rw [(R a).f2_ends] at hzEnds
      simp only [Sym2.mem_iff] at hzEnds
      rcases hzEnds with hzv | hzu
      · exact hzXA (hzv ▸ Finset.mem_union_left _
          (Finset.mem_sdiff.mp (R a).v2_in_remainder).1)
      · exact hzXA (hzu ▸ Finset.mem_union_right _ (by simp [Pair]))
  · have hxPair : x ∈ Pair a := by
      exact (Finset.mem_union.mp hxXA).resolve_left hxVT
    simp only [Pair, Finset.mem_insert, Finset.mem_singleton] at hxPair
    rcases hxPair with hx1 | hx2
    · have hef : e ≠ (R a).f1 := by
        intro hef
        have hzEnds : z ∈ G.ends (R a).f1 := by
          rw [← hef, hexz]
          simp
        rw [(R a).f1_ends] at hzEnds
        simp only [Sym2.mem_iff] at hzEnds
        rcases hzEnds with hzv | hzu
        · exact hzXA (hzv ▸ Finset.mem_union_left _
            (Finset.mem_sdiff.mp (R a).v1_in_remainder).1)
        · exact hzXA (hzu ▸ Finset.mem_union_right _ (by simp [Pair]))
      exfalso
      exact (hproper hef
        ⟨x, by change x ∈ G.ends e; rw [hexz]; simp,
          by change x ∈ G.ends (R a).f1; rw [(R a).f1_ends, hx1]; simp⟩
        heColor) (R a).f1_color
    · have hef : e ≠ (R a).f2 := by
        intro hef
        have hzEnds : z ∈ G.ends (R a).f2 := by
          rw [← hef, hexz]
          simp
        rw [(R a).f2_ends] at hzEnds
        simp only [Sym2.mem_iff] at hzEnds
        rcases hzEnds with hzv | hzu
        · exact hzXA (hzv ▸ Finset.mem_union_left _
            (Finset.mem_sdiff.mp (R a).v2_in_remainder).1)
        · exact hzXA (hzu ▸ Finset.mem_union_right _ (by simp [Pair]))
      exfalso
      exact (hproper hef
        ⟨x, by change x ∈ G.ends e; rw [hexz]; simp,
          by change x ∈ G.ends (R a).f2; rw [(R a).f2_ends, hx2]; simp⟩
        heColor) (R a).f2_color

private theorem helper_hBaseBone_523.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V]
      [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k)
      (T : TreeSequence G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D :
          ScheideDefectiveSetup G k e0 phi T C)
      (R : (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))) → ScheideReplacementData G k
          e0 phi T C D d),
      let VT : Finset V := TreeSequenceVertexSet T;
      let X : Finset V := ScheideEnlargedVertexSet R;
      let Def : Finset (Fin k) := DefectiveColors G phi VT;
      let Pair : ↥Def → Finset V := fun (d : ↥Def) ↦ {(R d).u1, (R d).u2};
      VT ⊆ X →
        ∀ (alpha : Fin k),
          let B : Finset E := BoundaryColorEdges G phi X alpha;
          (∀ (a : ↥Def), Pair a ⊆ X) →
            (∀ S ⊆ X, ∀ e ∈ BoundaryEdges G X, (∃ v ∈ S, Incident G v e) → e ∈ BoundaryEdges G S) →
              (∀ (a : ↥Def), ∀ e ∈ BoundaryColorEdges G phi (VT ∪ Pair a) (↑a : Fin k), e = D.f0
                  a) →
                let BaseB : Finset E := {e ∈ B | ∃ v ∈ VT, Incident G v e};
                BaseB.card ≤ (1 : ℕ) := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D R VT X Def Pair hVTsubX alpha B hPairSubX
      boundaryOfIncidentSubset hDefUnique BaseB
  apply Finset.card_le_one.mpr
  intro e he f hf
  have heB := (Finset.mem_filter.mp he).1
  have hfB := (Finset.mem_filter.mp hf).1
  have heInc := (Finset.mem_filter.mp he).2
  have hfInc := (Finset.mem_filter.mp hf).2
  by_cases hdef : alpha ∈ Def
  · let a : {delta // delta ∈ Def} := ⟨alpha, hdef⟩
    have hSsub : VT ∪ Pair a ⊆ X :=
      Finset.union_subset hVTsubX (hPairSubX a)
    have heXA : e ∈ BoundaryColorEdges G phi (VT ∪ Pair a) a.1 := by
      apply Finset.mem_filter.mpr
      refine ⟨boundaryOfIncidentSubset (VT ∪ Pair a) hSsub e
        (Finset.mem_filter.mp heB).1 ?_, ?_⟩
      · obtain ⟨v, hv, hve⟩ := heInc
        exact ⟨v, Finset.mem_union_left _ hv, hve⟩
      · exact (Finset.mem_filter.mp heB).2
    have hfXA : f ∈ BoundaryColorEdges G phi (VT ∪ Pair a) a.1 := by
      apply Finset.mem_filter.mpr
      refine ⟨boundaryOfIncidentSubset (VT ∪ Pair a) hSsub f
        (Finset.mem_filter.mp hfB).1 ?_, ?_⟩
      · obtain ⟨v, hv, hvf⟩ := hfInc
        exact ⟨v, Finset.mem_union_left _ hv, hvf⟩
      · exact (Finset.mem_filter.mp hfB).2
    exact (hDefUnique a e heXA).trans (hDefUnique a f hfXA).symm
  · by_contra hef
    have heVT : e ∈ BoundaryColorEdges G phi VT alpha := by
      apply Finset.mem_filter.mpr
      exact ⟨boundaryOfIncidentSubset VT hVTsubX e
        (Finset.mem_filter.mp heB).1 heInc, (Finset.mem_filter.mp heB).2⟩
    have hfVT : f ∈ BoundaryColorEdges G phi VT alpha := by
      apply Finset.mem_filter.mpr
      exact ⟨boundaryOfIncidentSubset VT hVTsubX f
        (Finset.mem_filter.mp hfB).1 hfInc, (Finset.mem_filter.mp hfB).2⟩
    have htwo : 2 ≤ (BoundaryColorEdges G phi VT alpha).card := by
      have hp : ({e, f} : Finset E).card = 2 := by simp [hef]
      rw [← hp]
      apply Finset.card_le_card
      intro g hg
      simp only [Finset.mem_insert, Finset.mem_singleton] at hg
      rcases hg with rfl | rfl
      · exact heVT
      · exact hfVT
    apply hdef
    dsimp [Def]
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    change 2 ≤ (BoundaryColorEdges G phi VT alpha).card
    exact htwo

private theorem helper_avoidComponent_658.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (R : (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))) →
        ScheideReplacementData G k e0 phi T C D d),
    let X : Finset V := ScheideEnlargedVertexSet R;
    let y0 : V := C.y (⟨(0 : ℕ), lt_of_lt_of_le Nat.zero_lt_two C.p_ge_two⟩ : Fin C.p);
    ∀ (alpha : Fin k),
    let _ : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G phi D.alpha0 alpha;
    let P : Set (V ⊕ E) := TwoColorComponent G phi D.alpha0 alpha (Sum.inl y0);
    ∀ (_ : E),
    ∀ u ∉ X,
    let Q : Set (V ⊕ E) := TwoColorComponent G phi D.alpha0 alpha (Sum.inl u); (
    ∀ z ∈ P, z ∉ Q) →
    ∀ S ⊆ X, ColoredVertexSetClosed G phi S → y0 ∈ S →
    ∀ (g : E), (
    ∀ e ∈ BoundaryColorEdges G phi S alpha, e = g) → Sum.inr g ∈ P →
    ∀ v ∈ S, Sum.inl v ∉ Q := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D R X y0 alpha H P f u huX Q hPQ S hSX hclosed hy0S g hunique hgP
  have hgQ : Sum.inr g ∉ Q := hPQ (Sum.inr g) hgP
  let Outside : Sum V E → Prop
    | Sum.inl v => v ∉ S
    | Sum.inr e => ∀ v ∈ S, ¬ Incident G v e
  have step : ∀ {z z' : Sum V E}, H.Adj z z' →
      Outside z → z ∈ Q → Outside z' := by
    intro z z' hzz' hz hzQ
    cases z with
    | inl v =>
        cases z' with
        | inl x => simp [H, TwoColorIncidenceGraph] at hzz'
        | inr e =>
            simp only [H, TwoColorIncidenceGraph] at hzz'
            intro x hxS hxe
            have hvx : x ≠ v := by
              intro hvx
              exact hz (hvx ▸ hxS)
            have hends : G.ends e = s(x, v) :=
              (Sym2.mem_and_mem_iff hvx).mp ⟨hxe, hzz'.1⟩
            have heBoundary : e ∈ BoundaryEdges G S := by
              simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ,
                true_and]
              exact ⟨x, hxS, v, hz, hends⟩
            rcases hzz'.2 with he0 | hea
            · exact (hclosed heBoundary hy0S he0)
                D.alpha0_missing_at_y0
            · have heg : e = g := hunique e
                (Finset.mem_filter.mpr ⟨heBoundary, hea⟩)
              apply hgQ
              rw [← heg]
              change H.connectedComponentMk (Sum.inr e) =
                H.connectedComponentMk (Sum.inl u)
              change H.connectedComponentMk (Sum.inl v) =
                H.connectedComponentMk (Sum.inl u) at hzQ
              exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
                hzz').symm.trans hzQ
    | inr e =>
        cases z' with
        | inl v =>
            simp only [H, TwoColorIncidenceGraph] at hzz'
            intro hvS
            exact hz v hvS hzz'.1
        | inr f => simp [H, TwoColorIncidenceGraph] at hzz'
  have componentOutside : ∀ z, z ∈ Q → Outside z := by
    intro z hzQ
    have hreach : H.Reachable (Sum.inl u) z := by
      apply SimpleGraph.ConnectedComponent.exact
      change H.connectedComponentMk z = H.connectedComponentMk (Sum.inl u) at hzQ
      exact hzQ.symm
    clear hzQ
    rw [SimpleGraph.reachable_iff_reflTransGen] at hreach
    induction hreach with
    | refl => exact fun huS => huX (hSX huS)
    | @tail z z' hreach hlast ih =>
        have hzQ : z ∈ Q := by
          change H.connectedComponentMk z = H.connectedComponentMk (Sum.inl u)
          exact (SimpleGraph.ConnectedComponent.sound
            (by simpa [SimpleGraph.reachable_iff_reflTransGen] using hreach)).symm
        exact step hlast ih hzQ
  intro v hvS hvQ
  exact (componentOutside (Sum.inl v) hvQ) hvS

private theorem helper_hQavoidVT_727.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (R : (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))) →
        ScheideReplacementData G k e0 phi T C D d),
    let VT : Finset V := TreeSequenceVertexSet T;
    let X : Finset V := ScheideEnlargedVertexSet R;
    let Def : Finset (Fin k) := DefectiveColors G phi VT;
    let Pair : ↥Def → Finset V := fun (d : ↥Def) ↦ {(R d).u1, (R d).u2}; ColoredVertexSetClosed G
        phi VT →
    let y0 : V := C.y (⟨(0 : ℕ), lt_of_lt_of_le Nat.zero_lt_two C.p_ge_two⟩ : Fin C.p); y0 ∈ VT →
        VT ⊆ X →
    ∀ (alpha : Fin k), (
    ∀ (a : ↥Def), Pair a ⊆ X) → (
    ∀ (a : ↥Def),
    ∀ e ∈ BoundaryColorEdges G phi (VT ∪ Pair a) (↑a : Fin k), e = D.f0 a) →
    let _ : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G phi D.alpha0 alpha;
    let P : Set (V ⊕ E) := TwoColorComponent G phi D.alpha0 alpha (Sum.inl y0);
    ∀ p ∈ BoundaryEdges G X, Sum.inr p ∈ P → phi p = some alpha →
    ∀ (_ : E) (u : V),
    let Q : Set (V ⊕ E) := TwoColorComponent G phi D.alpha0 alpha (Sum.inl u); (
    ∀ S ⊆ X, ColoredVertexSetClosed G phi S → y0 ∈ S →
    ∀ (g : E), (
    ∀ e ∈ BoundaryColorEdges G phi S alpha, e = g) → Sum.inr g ∈ P →
    ∀ v ∈ S, Sum.inl v ∉ Q) →
    ∀ v ∈ VT, Sum.inl v ∉ Q := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D R VT X Def Pair hVTclosed y0 hy0VT hVTsubX alpha hPairSubX
      hDefUnique H P p hpBoundary hpP hpColor f u Q avoidComponent
  by_cases hdef : alpha ∈ Def
  · let a : {delta // delta ∈ Def} := ⟨alpha, hdef⟩
    let XA := VT ∪ Pair a
    have hXAsub : XA ⊆ X :=
      Finset.union_subset hVTsubX (hPairSubX a)
    have hXAclosed : ColoredVertexSetClosed G phi XA := by
      change ColoredVertexSetClosed G phi
        (TreeSequenceVertexSet T ∪ {(R a).u1, (R a).u2})
      exact ScheideReplacementUnionClosed G k e0 phi T C D a (R a)
    have hy0XA : y0 ∈ XA := Finset.mem_union_left _ hy0VT
    have havoid := avoidComponent XA hXAsub hXAclosed hy0XA (D.f0 a)
      (by
        intro e he
        exact hDefUnique a e (by simpa [XA] using he))
      (by simpa [P, y0, a] using D.f0_on_initial_component a)
    intro v hv
    exact havoid v (Finset.mem_union_left _ hv)
  · let BaseColor := BoundaryColorEdges G phi VT alpha
    have hBaseColorOne : BaseColor.card ≤ 1 := by
      by_contra hnotOne
      have htwo : 2 ≤ BaseColor.card := by omega
      apply hdef
      dsimp [Def]
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      change 2 ≤ (BoundaryColorEdges G phi VT alpha).card
      simpa [BaseColor] using htwo
    have hBaseP : ∃ g : E, g ∈ BaseColor ∧ Sum.inr g ∈ P := by
      by_contra hnone
      push Not at hnone
      let Inside : Sum V E → Prop
        | Sum.inl v => v ∈ VT
        | Sum.inr e => ∃ v ∈ VT, Incident G v e
      have stepInside : ∀ {z z' : Sum V E}, H.Adj z z' →
          Inside z → z ∈ P → Inside z' := by
        intro z z' hzz' hz hzP
        cases z with
        | inl v =>
            cases z' with
            | inl x => simp [H, TwoColorIncidenceGraph] at hzz'
            | inr e =>
                simp only [H, TwoColorIncidenceGraph] at hzz'
                exact ⟨v, hz, hzz'.1⟩
        | inr e =>
            cases z' with
            | inl v =>
                simp only [H, TwoColorIncidenceGraph] at hzz'
                by_cases hvVT : v ∈ VT
                · exact hvVT
                · obtain ⟨x, hxVT, hxe⟩ := hz
                  have hxv : x ≠ v := by
                    intro hxv
                    exact hvVT (hxv ▸ hxVT)
                  have hends : G.ends e = s(x, v) :=
                    (Sym2.mem_and_mem_iff hxv).mp ⟨hxe, hzz'.1⟩
                  have heBoundary : e ∈ BoundaryEdges G VT := by
                    simp only [BoundaryEdges, Finset.mem_filter,
                      Finset.mem_univ, true_and]
                    exact ⟨x, hxVT, v, hvVT, hends⟩
                  rcases hzz'.2 with he0 | hea
                  · exact False.elim ((hVTclosed heBoundary hy0VT he0)
                      D.alpha0_missing_at_y0)
                  · exact False.elim (hnone e
                      (Finset.mem_filter.mpr ⟨heBoundary, hea⟩) hzP)
            | inr f => simp [H, TwoColorIncidenceGraph] at hzz'
      have componentInside : ∀ z, z ∈ P → Inside z := by
        intro z hzP
        have hreach : H.Reachable (Sum.inl y0) z := by
          apply SimpleGraph.ConnectedComponent.exact
          change H.connectedComponentMk z = H.connectedComponentMk (Sum.inl y0) at hzP
          exact hzP.symm
        clear hzP
        rw [SimpleGraph.reachable_iff_reflTransGen] at hreach
        induction hreach with
        | refl => exact hy0VT
        | @tail z z' hreach hlast ih =>
            have hzP : z ∈ P := by
              change H.connectedComponentMk z = H.connectedComponentMk (Sum.inl y0)
              exact (SimpleGraph.ConnectedComponent.sound
                (by simpa [SimpleGraph.reachable_iff_reflTransGen] using hreach)).symm
            exact stepInside hlast ih hzP
      obtain ⟨x, hxX, z, hzX, hpEnds⟩ := by
        simpa [BoundaryEdges] using hpBoundary
      have hzVT : z ∉ VT := fun hz => hzX (hVTsubX hz)
      have hzP : Sum.inl z ∈ P := by
        change H.connectedComponentMk (Sum.inl z) =
          H.connectedComponentMk (Sum.inl y0)
        change H.connectedComponentMk (Sum.inr p) =
          H.connectedComponentMk (Sum.inl y0) at hpP
        exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
          (by simp [H, TwoColorIncidenceGraph, Incident, hpEnds, hpColor])).trans hpP
      exact hzVT (componentInside (Sum.inl z) hzP)
    obtain ⟨g, hgBase, hgP⟩ := hBaseP
    have hunique : ∀ e : E, e ∈ BoundaryColorEdges G phi VT alpha →
        e = g := by
      intro e he
      exact Finset.card_le_one.mp hBaseColorOne e (by simpa [BaseColor] using he)
        g hgBase
    exact avoidComponent VT hVTsubX hVTclosed hy0VT g hunique hgP

private theorem helper_hUeven_520.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V]
      [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k)
      (T : TreeSequence G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D :
          ScheideDefectiveSetup G k e0 phi T C)
      (R : (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))) → ScheideReplacementData G k
          e0 phi T C D d),
      let VT : Finset V := TreeSequenceVertexSet T;
      let Def : Finset (Fin k) := DefectiveColors G phi VT;
      let Pair : ↥Def → Finset V := fun (d : ↥Def) ↦ {(R d).u1, (R d).u2};
      let U : Finset V := Finset.univ.biUnion Pair;
      (∀ (d : ↥Def), (Pair d).card = (2 : ℕ)) → Even U.card := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D R VT Def Pair U hPairCard
  have aux : ∀ s : Finset {delta // delta ∈ Def},
      Even (s.biUnion Pair).card := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert d s hds ih =>
        rw [Finset.biUnion_insert]
        by_cases heq : ∃ q ∈ s, Pair d = Pair q
        · obtain ⟨q, hqs, hdq⟩ := heq
          have hsub : Pair d ⊆ s.biUnion Pair := by
            intro v hv
            exact Finset.mem_biUnion.mpr ⟨q, hqs, by simpa [hdq] using hv⟩
          rw [Finset.union_eq_right.mpr hsub]
          exact ih
        · have hdisj : Disjoint (Pair d) (s.biUnion Pair) := by
            rw [Finset.disjoint_left]
            intro v hvd hvU
            obtain ⟨q, hqs, hvq⟩ := Finset.mem_biUnion.mp hvU
            rcases ScheideReplacementPairsLaminar G k e0 phi T C D R d q with
              hdq | hdq
            · exact heq ⟨q, hqs, by simpa [Pair, Def] using hdq⟩
            · exact (Finset.disjoint_left.mp
                (by simpa [Pair, Def] using hdq)) hvd hvq
          rw [Finset.card_union_of_disjoint hdisj, hPairCard d]
          rcases ih with ⟨q, hq⟩
          refine ⟨q + 1, ?_⟩
          omega
  simpa [U] using aux Finset.univ

private theorem helper_hinternalUnion_636.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V]
      [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k)
      (T : TreeSequence G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D :
          ScheideDefectiveSetup G k e0 phi T C)
      (R : (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))) → ScheideReplacementData G k
          e0 phi T C D d),
      let X : Finset V := ScheideEnlargedVertexSet R;
      ∀ (alpha : Fin k),
        let edges : Finset E := {e : E | phi e = some alpha};
        let internal : Finset E := {e ∈ edges | ∀ (v : V), Incident G v e → v ∈ X};
        (∀ (e : E), (G.ends e).toFinset.card = (2 : ℕ)) →
          (∀ ⦃e : E⦄, e ∈ internal → ∀ ⦃f : E⦄, f ∈ internal → e ≠ f → Disjoint (G.ends
              e).toFinset (G.ends f).toFinset) →
            (internal.biUnion fun (e : E) ↦ (G.ends e).toFinset).card = (2 : ℕ) * internal.card
               := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D R X alpha edges internal hendcard hinternalDisjoint
  have aux : ∀ s : Finset E, s ⊆ internal →
      (s.biUnion fun e => (G.ends e).toFinset).card = 2 * s.card := by
    intro s hs
    induction s using Finset.induction_on with
    | empty => simp
    | @insert e s hes ih =>
        rw [Finset.biUnion_insert]
        have hd : Disjoint (G.ends e).toFinset
            (s.biUnion fun f => (G.ends f).toFinset) := by
          rw [Finset.disjoint_left]
          intro v hev hvs
          obtain ⟨f, hf, hvf⟩ := Finset.mem_biUnion.mp hvs
          have hh := hinternalDisjoint
            (hs (Finset.mem_insert_self e s))
            (hs (Finset.mem_insert_of_mem hf)) (by
              intro heq
              exact hes (by simpa [heq] using hf))
          exact (Finset.disjoint_left.mp hh) hev hvf
        rw [Finset.card_union_of_disjoint hd, hendcard]
        rw [ih (fun x hx => hs (Finset.mem_insert_of_mem hx))]
        rw [Finset.card_insert_of_notMem hes]
        omega
  exact aux internal (by intro e he; exact he)

private theorem helper_hcover_662.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V]
      [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k)
      (T : TreeSequence G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D :
          ScheideDefectiveSetup G k e0 phi T C)
      (R : (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))) → ScheideReplacementData G k
          e0 phi T C D d),
      let X : Finset V := ScheideEnlargedVertexSet R;
      ∀ (alpha : Fin k),
        let B : Finset E := BoundaryColorEdges G phi X alpha;
        (∀ v ∈ X, alpha ∈ PresentColors G phi v) →
          let edges : Finset E := {e : E | phi e = some alpha};
          let internal : Finset E := {e ∈ edges | ∀ (v : V), Incident G v e → v ∈ X};
          (∀ (e : E), e ∈ edges ↔ phi e = some alpha) →
            (∀ (e : E), e ∈ internal ↔ e ∈ edges ∧ ∀ (v : V), Incident G v e → v ∈ X) →
              ∀ v ∈ X,
                (v ∈ internal.biUnion fun (e : E) ↦ (G.ends e).toFinset) ∨
                  v ∈ B.biUnion fun (e : E) ↦ {w ∈ X | Incident G w e} := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D R X alpha B hpresent edges internal hedge_mem hinternal v hv
  obtain ⟨e, hve, hecolor⟩ := by
    simpa [PresentColors] using hpresent v hv
  by_cases hall : ∀ w, Incident G w e → w ∈ X
  · left
    exact Finset.mem_biUnion.mpr
      ⟨e, (hinternal e).mpr ⟨(hedge_mem e).mpr hecolor, hall⟩,
        Sym2.mem_toFinset.mpr hve⟩
  · right
    push Not at hall
    obtain ⟨w, hwe, hwX⟩ := hall
    obtain ⟨z, hze⟩ := Sym2.mem_iff_exists.mp hwe
    have heq : G.ends e = s(w, z) := hze
    have hzv : z = v := by
      have hvEnds : v = w ∨ v = z := by
        have : v ∈ s(w, z) := by rw [← heq]; exact hve
        simpa using this
      rcases hvEnds with hvw | hvz
      · exact False.elim (hwX (hvw ▸ hv))
      · exact hvz.symm
    have heboundary : e ∈ BoundaryEdges G X := by
      simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨v, hv, w, hwX, by simpa [hzv] using heq.trans Sym2.eq_swap⟩
    have heB : e ∈ B := by
      exact Finset.mem_filter.mpr ⟨heboundary, hecolor⟩
    exact Finset.mem_biUnion.mpr ⟨e, heB,
      Finset.mem_filter.mpr ⟨hv, hve⟩⟩

private theorem helper_hBunion_721.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V]
      [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k)
      (T : TreeSequence G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D :
          ScheideDefectiveSetup G k e0 phi T C)
      (R : (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))) → ScheideReplacementData G k
          e0 phi T C D d),
      let X : Finset V := ScheideEnlargedVertexSet R;
      ∀ (alpha : Fin k),
        let B : Finset E := BoundaryColorEdges G phi X alpha;
        (∀ e ∈ B, {v ∈ X | Incident G v e}.card = (1 : ℕ)) →
          (∀ ⦃e : E⦄, e ∈ B → ∀ ⦃f : E⦄, f ∈ B → e ≠ f → Disjoint ({v ∈ X | Incident G v e}) ({v
              ∈ X | Incident G v f})) →
            (B.biUnion fun (e : E) ↦ {v ∈ X | Incident G v e}).card = B.card := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D R X alpha B hBfiber hBdisjoint
  have aux :
    ∀ s : Finset E, s ⊆ B → (s.biUnion fun e => X.filter (fun v => Incident G v e)).card = s.card
  := by
    intro s hs
    induction s using Finset.induction_on with
    | empty => simp
    | @insert e s hes ih =>
        rw [Finset.biUnion_insert]
        have hd : Disjoint (X.filter (fun v => Incident G v e))
            (s.biUnion fun f => X.filter (fun v => Incident G v f)) := by
          rw [Finset.disjoint_left]
          intro v hev hvs
          obtain ⟨f, hf, hvf⟩ := Finset.mem_biUnion.mp hvs
          exact (Finset.disjoint_left.mp
            (hBdisjoint (hs (Finset.mem_insert_self e s))
              (hs (Finset.mem_insert_of_mem hf)) (by
                intro heq
                exact hes (by simpa [heq] using hf)))) hev hvf
        rw [Finset.card_union_of_disjoint hd,
          hBfiber e (hs (Finset.mem_insert_self e s))]
        rw [ih (fun x hx => hs (Finset.mem_insert_of_mem hx))]
        rw [Finset.card_insert_of_notMem hes]
        exact Nat.add_comm 1 s.card
  exact aux B (by intro e he; exact he)

private theorem helper_hBfiber_785.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V]
      [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k)
      (T : TreeSequence G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D :
          ScheideDefectiveSetup G k e0 phi T C)
      (R : (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))) → ScheideReplacementData G k
          e0 phi T C D d),
      let X : Finset V := ScheideEnlargedVertexSet R;
      ∀ (alpha : Fin k),
        let B : Finset E := BoundaryColorEdges G phi X alpha;
        ∀ e ∈ B, {v ∈ X | Incident G v e}.card = (1 : ℕ) := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D R X alpha B e he
  have heboundary : e ∈ BoundaryEdges G X :=
    (Finset.mem_filter.mp he).1
  obtain ⟨u, hu, v, hv, huv⟩ := by
    simpa [BoundaryEdges] using heboundary
  have hs : X.filter (fun x => Incident G x e) = {u} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_singleton, Incident,
      huv, Sym2.mem_iff]
    constructor
    · rintro ⟨hx, rfl | hxe⟩
      · exact rfl
      · exact False.elim (hv (hxe ▸ hx))
    · intro hxu
      subst hxu
      exact ⟨hu, Or.inl rfl⟩
  rw [hs]
  simp

private theorem helper_hAW_828.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V]
      [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k)
      (T : TreeSequence G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D :
          ScheideDefectiveSetup G k e0 phi T C)
      (R : (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))) → ScheideReplacementData G k
          e0 phi T C D d),
      let X : Finset V := ScheideEnlargedVertexSet R;
      IsProperEdgeColoring G phi →
        ∀ (alpha : Fin k),
          let B : Finset E := BoundaryColorEdges G phi X alpha;
          let edges : Finset E := {e : E | phi e = some alpha};
          let internal : Finset E := {e ∈ edges | ∀ (v : V), Incident G v e → v ∈ X};
          (∀ (e : E), e ∈ edges ↔ phi e = some alpha) →
            (∀ (e : E), e ∈ internal ↔ e ∈ edges ∧ ∀ (v : V), Incident G v e → v ∈ X) →
              let A : Finset V := internal.biUnion fun (e : E) ↦ (G.ends e).toFinset;
              let W : Finset V := B.biUnion fun (e : E) ↦ {v ∈ X | Incident G v e};
              Disjoint A W := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D R X hproper alpha B edges internal hedge_mem hinternal A W
  rw [Finset.disjoint_left]
  intro v hvA hvW
  obtain ⟨e, he, hve⟩ := Finset.mem_biUnion.mp hvA
  obtain ⟨f, hf, hvf⟩ := Finset.mem_biUnion.mp hvW
  have hef : e ≠ f := by
    intro hef
    have hfboundary : f ∈ BoundaryEdges G X :=
      (Finset.mem_filter.mp hf).1
    obtain ⟨u, hu, w, hw, huw⟩ := by
      simpa [BoundaryEdges] using hfboundary
    have : w ∈ X := ((hinternal e).mp he).2 w (by
      change w ∈ G.ends e
      rw [hef, huw]
      simp)
    exact hw this
  exact (hproper hef ⟨v, Sym2.mem_toFinset.mp hve,
    (Finset.mem_filter.mp hvf).2⟩
    (hedge_mem e |>.mp (hinternal e |>.mp he).1))
    (Finset.mem_filter.mp hf).2

private theorem helper_boundaryOfIncidentSubset_877.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V]
      [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k)
      (T : TreeSequence G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D :
          ScheideDefectiveSetup G k e0 phi T C)
      (R : (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))) → ScheideReplacementData G k
          e0 phi T C D d),
      let X : Finset V := ScheideEnlargedVertexSet R;
      ∀ S ⊆ X, ∀ e ∈ BoundaryEdges G X, (∃ v ∈ S, Incident G v e) → e ∈ BoundaryEdges G S := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D R X S hSX e heX heInc
  obtain ⟨x, hxX, z, hzX, hexz⟩ := by
    simpa [BoundaryEdges] using heX
  obtain ⟨v, hvS, hve⟩ := heInc
  have hvEnds : v = x ∨ v = z := by
    have : v ∈ s(x, z) := by rw [← hexz]; exact hve
    simpa using this
  have hvx : v = x := by
    rcases hvEnds with hvx | hvz
    · exact hvx
    · exact False.elim (hzX (hSX (hvz ▸ hvS)))
  simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨v, hvS, z, fun hzS => hzX (hSX hzS), by simpa [hvx] using hexz⟩

private theorem helper_continuation_896.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (R : (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))) →
        ScheideReplacementData G k e0 phi T C D d),
    let VT : Finset V := TreeSequenceVertexSet T;
    let X : Finset V := ScheideEnlargedVertexSet R;
    let Def : Finset (Fin k) := DefectiveColors G phi VT;
    let Pair : ↥Def → Finset V := fun (d : ↥Def) ↦ {(R d).u1, (R d).u2};
    let U : Finset V := Finset.univ.biUnion Pair; ColoredVertexSetClosed G phi VT →
        ColoredVertexSetClosed G phi X → X = VT ∪ U →
    let y0 : V := C.y (⟨(0 : ℕ), lt_of_lt_of_le Nat.zero_lt_two C.p_ge_two⟩ : Fin C.p); y0 ∈ VT →
        VT ⊆ X → y0 ∈ X →
    ∀ (alpha : Fin k),
    let B : Finset E := BoundaryColorEdges G phi X alpha; (
    ∀ v ∈ X, alpha ∈ PresentColors G phi v) → alpha ≠ D.alpha0 →
    let edges : Finset E := {e : E | phi e = some alpha};
    let internal : Finset E := {e ∈ edges |
    ∀ (v : V), Incident G v e → v ∈ X}; (B.biUnion fun (e : E) ↦ {v ∈ X | Incident G v e}).card =
        B.card → X.card = (2 : ℕ) * internal.card + B.card → (3 : ℕ) ≤ B.card → (
    ∀ (a : ↥Def), Pair a ⊆ X) → (
    ∀ (a : ↥Def),
    ∀ e ∈ BoundaryColorEdges G phi (VT ∪ Pair a) (↑a : Fin k), e = D.f0 a) →
    let BaseB : Finset E := {e ∈ B |
    ∃ v ∈ VT, Incident G v e}; BaseB.card ≤ (1 : ℕ) →
    let OutB : Finset E := {e ∈ B | ¬
    ∃ v ∈ VT, Incident G v e}; BaseB.card + OutB.card = B.card →
    ∃ (alpha : Fin k) (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))) (f : E) (w : V) (u
        : V), alpha ≠ D.alpha0 ∧ phi f = some alpha ∧ G.ends f = s(w, u) ∧ w ∈
        ScheideEnlargedVertexSet R ∧ w ∉ TreeSequenceVertexSet T ∧ u ∉ ScheideEnlargedVertexSet R
        ∧ (w = (R d).u1 ∨ w = (R d).u2) ∧ Sum.inr f ∈ TwoColorComponent G phi D.alpha0 alpha
        (Sum.inl u) ∧
    ∀ v ∈ TreeSequenceVertexSet T, Sum.inl v ∉ TwoColorComponent G phi D.alpha0 alpha (Sum.inl u)
  := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D R VT X Def Pair U hVTclosed hXclosed hXeq y0 hy0VT hVTsubX
      hy0X alpha B hpresent halpha edges internal hBunion hcardeq hBthree hPairSubX hDefUnique
      BaseB hBaseBone OutB hpartition
  have hOutBtwo : 2 ≤ OutB.card := by omega
  let H := TwoColorIncidenceGraph G phi D.alpha0 alpha
  let P := TwoColorComponent G phi D.alpha0 alpha (Sum.inl y0)
  obtain ⟨p, hp, hpUnique⟩ :=
    ScheideSingleBoundaryCrossing G k e0 phi T C D R alpha
      (by simpa [X] using hpresent)
  have hpBoundary : p ∈ BoundaryEdges G X := by simpa [X] using hp.1
  have hpP : Sum.inr p ∈ P := by simpa [P, y0] using hp.2
  have edgeColorOfP : ∀ e : E, Sum.inr e ∈ P →
      phi e = some D.alpha0 ∨ phi e = some alpha := by
    exact (fun _ member => TwoColorComponent.edge_colors member)
  have hpColor : phi p = some alpha := by
    rcases edgeColorOfP p hpP with hp0 | hpa
    · exact False.elim ((hXclosed hpBoundary hy0X hp0)
        D.alpha0_missing_at_y0)
    · exact hpa
  have hpB : p ∈ B := Finset.mem_filter.mpr ⟨hpBoundary, hpColor⟩
  have hchoose : ∃ f : E, f ∈ OutB ∧ f ≠ p := by
    by_contra hnone
    push Not at hnone
    have hle : OutB.card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro e he f hf
      exact (hnone e he).trans (hnone f hf).symm
    omega
  obtain ⟨f, hfOut, hfp⟩ := hchoose
  have hfB : f ∈ B := (Finset.mem_filter.mp hfOut).1
  have hfNoBase : ¬ ∃ v ∈ VT, Incident G v f :=
    (Finset.mem_filter.mp hfOut).2
  have hfBoundary : f ∈ BoundaryEdges G X :=
    (Finset.mem_filter.mp hfB).1
  have hfColor : phi f = some alpha :=
    (Finset.mem_filter.mp hfB).2
  obtain ⟨w, hwX, u, huX, hfEnds⟩ := by
    simpa [BoundaryEdges] using hfBoundary
  have hwVT : w ∉ VT := by
    intro hw
    exact hfNoBase ⟨w, hw, by change w ∈ G.ends f; rw [hfEnds]; simp⟩
  have hwU : w ∈ U := by
    rw [hXeq] at hwX
    exact (Finset.mem_union.mp hwX).resolve_left hwVT
  obtain ⟨d, _, hwd⟩ := Finset.mem_biUnion.mp hwU
  have hwPair : w = (R d).u1 ∨ w = (R d).u2 := by
    simpa [Pair] using hwd
  let Q := TwoColorComponent G phi D.alpha0 alpha (Sum.inl u)
  have hfQ : Sum.inr f ∈ Q := by
    change H.connectedComponentMk (Sum.inr f) =
      H.connectedComponentMk (Sum.inl u)
    apply SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
    simp [H, TwoColorIncidenceGraph, Incident, hfEnds, hfColor]
  have hfNotP : Sum.inr f ∉ P := by
    intro hfP
    have hpf : f = p := hpUnique f ⟨by simpa [X] using hfBoundary,
      by simpa [P, y0] using hfP⟩
    exact hfp hpf
  have hPQ : ∀ z, z ∈ P → z ∉ Q := by
    intro z hzP hzQ
    apply hfNotP
    change H.connectedComponentMk (Sum.inr f) =
      H.connectedComponentMk (Sum.inl y0)
    change H.connectedComponentMk (Sum.inr f) =
      H.connectedComponentMk (Sum.inl u) at hfQ
    change H.connectedComponentMk z = H.connectedComponentMk (Sum.inl u) at hzQ
    change H.connectedComponentMk z = H.connectedComponentMk (Sum.inl y0) at hzP
    exact hfQ.trans (hzQ.symm.trans hzP)
  have avoidComponent :
    ∀ (S : Finset V), S ⊆ X → ColoredVertexSetClosed G phi S → y0 ∈ S →
    ∀ (g : E), (
    ∀ e : E, e ∈ BoundaryColorEdges G phi S alpha → e = g) → Sum.inr g ∈ P →
    ∀ v ∈ S, Sum.inl v ∉ Q := by
    exact @helper_avoidComponent_658 V E inferInstance inferInstance inferInstance inferInstance
        G k e0 phi T C D R alpha f u huX hPQ
  have hQavoidVT : ∀ v ∈ VT, Sum.inl v ∉ Q := by
    exact @helper_hQavoidVT_727 V E inferInstance inferInstance inferInstance inferInstance G k
        e0 phi T C D R hVTclosed hy0VT hVTsubX alpha hPairSubX hDefUnique p hpBoundary hpP
        hpColor f u avoidComponent
  refine ⟨alpha, d, f, w, u, halpha, hfColor, hfEnds, ?_, hwVT, huX,
    hwPair, hfQ, ?_⟩
  · simpa [X] using hwX
  · intro v hv
    exact hQavoidVT v hv

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
    let Pair : ↥Def → Finset V := fun (d : ↥Def) ↦ {(R d).u1, (R d).u2};
    let U : Finset V := Finset.univ.biUnion Pair; IsProperEdgeColoring G phi →
        ColoredVertexSetClosed G phi VT → ColoredVertexSetClosed G phi X → X = VT ∪ U → Odd X.card
        →
    let y0 : V := C.y (⟨(0 : ℕ), lt_of_lt_of_le Nat.zero_lt_two C.p_ge_two⟩ : Fin C.p); y0 ∈ VT →
        VT ⊆ X → y0 ∈ X →
    ∀ (alpha : Fin k),
    let B : Finset E := BoundaryColorEdges G phi X alpha; (2 : ℕ) ≤ B.card → (
    ∀ v ∈ X, alpha ∈ PresentColors G phi v) → alpha ≠ D.alpha0 →
    let edges : Finset E := {e : E | phi e = some alpha};
    let _ : Finset E := {e ∈ edges |
    ∀ (v : V), Incident G v e → v ∈ X}; (
    ∀ (e : E), e ∈ edges ↔ phi e = some alpha) →
    ∃ (alpha : Fin k) (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))) (f : E) (w : V) (u
        : V), alpha ≠ D.alpha0 ∧ phi f = some alpha ∧ G.ends f = s(w, u) ∧ w ∈
        ScheideEnlargedVertexSet R ∧ w ∉ TreeSequenceVertexSet T ∧ u ∉ ScheideEnlargedVertexSet R
        ∧ (w = (R d).u1 ∨ w = (R d).u2) ∧ Sum.inr f ∈ TwoColorComponent G phi D.alpha0 alpha
        (Sum.inl u) ∧
    ∀ v ∈ TreeSequenceVertexSet T, Sum.inl v ∉ TwoColorComponent G phi D.alpha0 alpha (Sum.inl u)
  := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D R VT X Def Pair U hproper hVTclosed hXclosed hXeq hXodd y0
      hy0VT hVTsubX hy0X alpha B hBtwo hpresent halpha edges internal hedge_mem
  have hinternal : ∀ e, e ∈ internal ↔
      e ∈ edges ∧ ∀ v, Incident G v e → v ∈ X := by
    intro e
    simp [internal]
  have hendcard : ∀ e : E, (G.ends e).toFinset.card = 2 := by
    intro e
    apply Sym2.card_toFinset_of_not_isDiag
    intro hd
    exact G.loopless e ((G.ends e).diagElem hd)
      (Sym2.diag_diagElem hd).symm
  have hinternalDisjoint : ∀ ⦃e⦄, e ∈ internal → ∀ ⦃f⦄,
      f ∈ internal → e ≠ f →
        Disjoint (G.ends e).toFinset (G.ends f).toFinset := by
    intro e he f hf hef
    rw [Finset.disjoint_left]
    intro v hev hvf
    exact (hproper hef
      ⟨v, Sym2.mem_toFinset.mp hev, Sym2.mem_toFinset.mp hvf⟩
      (hedge_mem e |>.mp (hinternal e |>.mp he).1))
      (hedge_mem f |>.mp (hinternal f |>.mp hf).1)
  have hinternalUnion :
      (internal.biUnion fun e => (G.ends e).toFinset).card =
        2 * internal.card := by
    exact @helper_hinternalUnion_636 V E inferInstance inferInstance inferInstance inferInstance
        G k e0 phi T C D R alpha hendcard hinternalDisjoint
  have hcover : ∀ v, v ∈ X →
      v ∈ internal.biUnion (fun e => (G.ends e).toFinset) ∨
        v ∈ B.biUnion (fun e => X.filter (fun w => Incident G w e)) := by
    exact @helper_hcover_662 V E inferInstance inferInstance inferInstance inferInstance G k e0
        phi T C D R alpha hpresent hedge_mem hinternal
  have hBfiber : ∀ e, e ∈ B →
      (X.filter (fun v => Incident G v e)).card = 1 := by
    exact @helper_hBfiber_785 V E inferInstance inferInstance inferInstance inferInstance G k e0
        phi T C D R alpha
  have hBdisjoint : ∀ ⦃e⦄, e ∈ B → ∀ ⦃f⦄, f ∈ B → e ≠ f →
      Disjoint (X.filter (fun v => Incident G v e))
        (X.filter (fun v => Incident G v f)) := by
    intro e he f hf hef
    rw [Finset.disjoint_left]
    intro v hev hvf
    exact (hproper hef ⟨v, (Finset.mem_filter.mp hev).2,
      (Finset.mem_filter.mp hvf).2⟩
      (Finset.mem_filter.mp he).2) (Finset.mem_filter.mp hf).2
  have hBunion :
      (B.biUnion fun e => X.filter (fun v => Incident G v e)).card =
        B.card := by
    exact @helper_hBunion_721 V E inferInstance inferInstance inferInstance inferInstance G k e0
        phi T C D R alpha hBfiber hBdisjoint
  let A := internal.biUnion (fun e => (G.ends e).toFinset)
  let W := B.biUnion (fun e => X.filter (fun v => Incident G v e))
  have hA : A ⊆ X := by
    intro v hv
    obtain ⟨e, he, hve⟩ := Finset.mem_biUnion.mp hv
    exact ((hinternal e).mp he).2 v (Sym2.mem_toFinset.mp hve)
  have hW : W ⊆ X := by
    intro v hv
    obtain ⟨e, _, hve⟩ := Finset.mem_biUnion.mp hv
    exact (Finset.mem_filter.mp hve).1
  have hAW : Disjoint A W := by
    exact @helper_hAW_828 V E inferInstance inferInstance inferInstance inferInstance G k e0 phi
        T C D R hproper alpha hedge_mem hinternal
  have hAX : A ∪ W = X := by
    apply Finset.Subset.antisymm
    · exact Finset.union_subset hA hW
    · intro v hv
      rcases hcover v hv with hvA | hvW
      · exact Finset.mem_union.mpr (Or.inl hvA)
      · exact Finset.mem_union.mpr (Or.inr hvW)
  have hcardeq : X.card = 2 * internal.card + B.card := by
    rw [← hAX, Finset.card_union_of_disjoint hAW,
      hinternalUnion, hBunion]
  have hBodd : Odd B.card := by
    rcases hXodd with ⟨q, hq⟩
    have hile : internal.card ≤ q := by omega
    refine ⟨q - internal.card, ?_⟩
    omega
  have hBthree : 3 ≤ B.card := by
    rcases hBodd with ⟨q, hq⟩
    omega
  have hblockVT : ∀ (a : {delta // delta ∈ Def}) (j : Fin 2),
      C.blockVertex (D.gammaIndex a) j ∈ VT := by
    intro a j
    rw [← C.block_vertex_position (D.gammaIndex a) j]
    simp [VT, TreeSequenceVertexSet]
  have hPairSubX : ∀ a : {delta // delta ∈ Def}, Pair a ⊆ X := by
    intro a v hv
    rw [hXeq]
    apply Finset.mem_union_right
    exact Finset.mem_biUnion.mpr ⟨a, Finset.mem_univ _, hv⟩
  have boundaryOfIncidentSubset : ∀ (S : Finset V), S ⊆ X →
      ∀ (e : E), e ∈ BoundaryEdges G X →
        (∃ v ∈ S, Incident G v e) → e ∈ BoundaryEdges G S := by
    exact @helper_boundaryOfIncidentSubset_877 V E inferInstance inferInstance inferInstance
        inferInstance G k e0 phi T C D R
  have hDefUnique : ∀ a : {delta // delta ∈ Def},
      ∀ e : E, e ∈ BoundaryColorEdges G phi (VT ∪ Pair a) a.1 →
        e = D.f0 a := by
    exact @helper_hDefUnique_410 V E inferInstance inferInstance inferInstance inferInstance G k
        e0 phi T C D R hproper hblockVT
  let BaseB := B.filter (fun e => ∃ v ∈ VT, Incident G v e)
  have hBaseBone : BaseB.card ≤ 1 := by
    exact @helper_hBaseBone_523 V E inferInstance inferInstance inferInstance inferInstance G k
        e0 phi T C D R hVTsubX alpha hPairSubX boundaryOfIncidentSubset hDefUnique
  let OutB := B.filter (fun e => ¬ ∃ v ∈ VT, Incident G v e)
  have hpartition : BaseB.card + OutB.card = B.card := by
    simpa [BaseB, OutB] using
      (Finset.card_filter_add_card_filter_not
        (s := B) (fun e => ∃ v ∈ VT, Incident G v e))
  exact @helper_continuation_896 V E inferInstance inferInstance inferInstance inferInstance G k
      e0 phi T C D R hVTclosed hXclosed hXeq hy0VT hVTsubX hy0X alpha hpresent halpha hBunion
      hcardeq hBthree hPairSubX hDefUnique hBaseBone hpartition
theorem ScheideEnlargedBoundarySelection {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (C : ScheideReducedConfiguration G k e0 phi T)
    (D : ScheideDefectiveSetup G k e0 phi T C)
    (R : ∀ d : {delta // delta ∈ DefectiveColors G phi
      (TreeSequenceVertexSet T)}, ScheideReplacementData G k e0 phi T C D d)
    (hnot : ¬ ColoredVertexSetStronglyClosed G phi
      (ScheideEnlargedVertexSet R)) :
    ∃ (alpha : Fin k)
      (d : {delta // delta ∈ DefectiveColors G phi (TreeSequenceVertexSet T)})
      (f : E) (w u : V),
      alpha ≠ D.alpha0 ∧
      phi f = some alpha ∧
      G.ends f = s(w, u) ∧
      w ∈ ScheideEnlargedVertexSet R ∧
      w ∉ TreeSequenceVertexSet T ∧
      u ∉ ScheideEnlargedVertexSet R ∧
      (w = (R d).u1 ∨ w = (R d).u2) ∧
      Sum.inr f ∈ TwoColorComponent G phi D.alpha0 alpha (Sum.inl u) ∧
      ∀ v ∈ TreeSequenceVertexSet T,
        Sum.inl v ∉ TwoColorComponent G phi D.alpha0 alpha (Sum.inl u) := by
  classical
  let VT := TreeSequenceVertexSet T
  let X := ScheideEnlargedVertexSet R
  let Def := DefectiveColors G phi VT
  let Pair : {delta // delta ∈ Def} → Finset V :=
    fun d => {(R d).u1, (R d).u2}
  let U := Finset.univ.biUnion Pair
  have hproper : IsProperEdgeColoring G phi :=
    C.globally_maximum.1.2.2.2.1
  have hVTclosed : ColoredVertexSetClosed G phi VT :=
    (ScheideGlobalMaximumOrder G k e0 phi T C.globally_maximum).2.2.2.2
  have hVTodd : Odd VT.card :=
    (ScheideGlobalMaximumOrder G k e0 phi T C.globally_maximum).2.2.1
  have hXclosed : ColoredVertexSetClosed G phi X := by
    change ColoredVertexSetClosed G phi (ScheideEnlargedVertexSet R)
    exact ScheideEnlargedClosed G k e0 phi T C D R
  have hPairCard : ∀ d : {delta // delta ∈ Def}, (Pair d).card = 2 := by
    intro d
    obtain ⟨g, _, hg⟩ :=
      (ScheideSymmetricDefectiveInternal G k e0 phi T C D d (R d)).2
    have hne : (R d).u1 ≠ (R d).u2 := by
      intro h
      exact G.loopless g (R d).u1 (by simpa [h] using hg)
    simp [Pair, hne]
  have hPairOutside : ∀ d : {delta // delta ∈ Def},
      Disjoint VT (Pair d) := by
    intro d
    rw [Finset.disjoint_left]
    intro v hvT hvPair
    simp only [Pair, Finset.mem_insert, Finset.mem_singleton] at hvPair
    rcases hvPair with rfl | rfl
    · exact (R d).u1_outside hvT
    · exact (R d).u2_outside hvT
  have hUeven : Even U.card := by
    exact @helper_hUeven_520 V E inferInstance inferInstance inferInstance inferInstance G k e0
        phi T C D R hPairCard
  have hVTU : Disjoint VT U := by
    rw [Finset.disjoint_left]
    intro v hvT hvU
    obtain ⟨d, _, hvd⟩ := Finset.mem_biUnion.mp hvU
    exact (Finset.disjoint_left.mp (hPairOutside d)) hvT hvd
  have hXeq : X = VT ∪ U := by
    simp [X, VT, U, Pair, Def, ScheideEnlargedVertexSet]
  have hXodd : Odd X.card := by
    rw [hXeq, Finset.card_union_of_disjoint hVTU]
    rcases hVTodd with ⟨a, ha⟩
    rcases hUeven with ⟨b, hb⟩
    refine ⟨a + b, ?_⟩
    omega
  let y0 : V := C.y ⟨0, lt_of_lt_of_le Nat.zero_lt_two C.p_ge_two⟩
  have hy0VT : y0 ∈ VT := by
    have hpos : (0 : ℕ) < T.length + 1 := by omega
    have hv := C.base_vertex_position
      ⟨0, lt_of_lt_of_le Nat.zero_lt_two C.p_ge_two⟩
    simpa [y0, VT, TreeSequenceVertexSet] using
      (show ∃ i : Fin (T.length + 1), T.vertex i = y0 from
        ⟨⟨0, hpos⟩, by simpa [y0] using hv⟩)
  have hVTsubX : VT ⊆ X := by
    intro v hv
    rw [hXeq]
    exact Finset.mem_union_left _ hv
  have hy0X : y0 ∈ X := hVTsubX hy0VT
  have hnotSep : ¬ ∀ {f g c}, f ∈ BoundaryEdges G X →
      g ∈ BoundaryEdges G X → f ≠ g → phi f = some c →
        phi g ≠ some c := by
    intro hsep
    exact hnot ⟨hXclosed, hsep⟩
  push Not at hnotSep
  obtain ⟨b0, b1, alpha, hb0Boundary, hb1Boundary, hb01,
      hb0Color, hb1Color⟩ := hnotSep
  let B := BoundaryColorEdges G phi X alpha
  have hb0B : b0 ∈ B := by
    exact Finset.mem_filter.mpr ⟨hb0Boundary, hb0Color⟩
  have hb1B : b1 ∈ B := by
    exact Finset.mem_filter.mpr ⟨hb1Boundary, hb1Color⟩
  have hBtwo : 2 ≤ B.card := by
    have hpair : ({b0, b1} : Finset E).card = 2 := by simp [hb01]
    rw [← hpair]
    apply Finset.card_le_card
    intro f hf
    simp only [Finset.mem_insert, Finset.mem_singleton] at hf
    rcases hf with rfl | rfl
    · exact hb0B
    · exact hb1B
  have hpresent : ∀ v, v ∈ X → alpha ∈ PresentColors G phi v := by
    intro v hv
    have hn : alpha ∉ MissingColors G phi v := by
      intro hm
      exact (hXclosed hb0Boundary hv hb0Color) hm
    simpa [MissingColors] using hn
  have halpha : alpha ≠ D.alpha0 := by
    intro h
    have hp := hpresent y0 hy0X
    have hn : D.alpha0 ∉ PresentColors G phi y0 := by
      simpa [MissingColors] using D.alpha0_missing_at_y0
    exact hn (h ▸ hp)
  let edges := (Finset.univ : Finset E).filter (fun e => phi e = some alpha)
  let internal := edges.filter (fun e => ∀ v, Incident G v e → v ∈ X)
  have hedge_mem : ∀ e, e ∈ edges ↔ phi e = some alpha := by
    intro e
    simp [edges]
  exact @helper_continuation_878 V E inferInstance inferInstance inferInstance inferInstance G k
      e0 phi T C D R hproper hVTclosed hXclosed hXeq hXodd hy0VT hVTsubX hy0X alpha hBtwo
      hpresent halpha hedge_mem
end GoldbergSeymour

end
