/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ScheideSymmetricMissingInternal

/-!
# Scheide Replacement Union Closed

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private theorem ScheideReplacementUnionClosed_branch_104.{u_1, u_2} :
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))) (R : ScheideReplacementData
        G k e0 phi T C D d) {f : E} {c : Fin k} {v : V}, phi f = some c → c ∈ MissingColors G phi
        v → ColoredVertexSetClosed G phi (TreeSequenceVertexSet T) →
    let phiD := TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d)) (↑d : Fin k) (Sum.inl (D.v0
        d)); (
    ∀ {a : Fin k}, a ∈ MissingColors G phi (C.blockVertex (D.gammaIndex d) 0) ∨ a ∈ MissingColors
        G phi (C.blockVertex (D.gammaIndex d) 1) →
    ∃ (g : E), phi g = some a ∧ G.ends g = s(R.u1, R.u2)) → (
    ∃ (g : E), phi g = some c ∧ (G.ends g = s(R.u1, R.u2) ∨ G.ends g = s(C.blockVertex
        (D.gammaIndex d) 0, C.blockVertex (D.gammaIndex d) 1))) →
    ∀ (u w : V), w ∉ TreeSequenceVertexSet T ∪ { R.u1, R.u2 } → G.ends f = s(u, w) →
        IsProperEdgeColoring G phi → (u ∈ TreeSequenceVertexSet T → f ≠ D.f0 d → phiD f = phi f) →
        u ∈ TreeSequenceVertexSet T ∨ u = R.u1 ∨ u = R.u2 → v ∈ TreeSequenceVertexSet T → False
  := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D d R f c v hfc hmiss htreeClosed phiD pairInternal
      pairOrBlock u w hw hends proper switchOnTree hu hvTree
  have pairEdge : ∃ g : E, phi g = some c ∧
      G.ends g = s(R.u1, R.u2) := by
    by_cases hv0 : v = C.blockVertex (D.gammaIndex d) 0
    · exact pairInternal (Or.inl (hv0 ▸ hmiss))
    · by_cases hv3 : v = C.blockVertex (D.gammaIndex d) 1
      · exact pairInternal (Or.inr (hv3 ▸ hmiss))
      · have hvrem : v ∈ (TreeSequenceVertexSet T \
          {C.blockVertex (D.gammaIndex d) 0,
            C.blockVertex (D.gammaIndex d) 1}) := by
          simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
          exact ⟨hvTree, by simp [hv0, hv3]⟩
        by_cases hc : c = C.gamma (D.gammaIndex d)
        · subst c
          obtain ⟨g, hgc, hge⟩ :=
            ScheideSymmetricDefectiveInternal G k e0 phi T C D d R |>.2
          exact ⟨g, hgc, hge⟩
        · exact ScheideReplacementInternalMissing G k e0 phi T C D d R c hc
            ⟨v, hvrem, hmiss⟩
  rcases pairEdge with ⟨g, hgc, hge⟩
  by_cases huTree : u ∈ TreeSequenceVertexSet T
  · have hb : f ∈ BoundaryEdges G (TreeSequenceVertexSet T) := by
      unfold BoundaryEdges
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨u, huTree, w, ?_, hends⟩
      intro hwT
      exact hw (by simp [hwT])
    exact (htreeClosed hb hvTree hfc) hmiss
  · have hpair : u = R.u1 ∨ u = R.u2 := by simpa [huTree] using hu
    have hadj : AdjacentEdges G f g := by
      rcases hpair with rfl | rfl
      · refine ⟨R.u1, ?_, ?_⟩ <;> unfold Incident
        · rw [hends]; simp
        · rw [hge]; simp
      · refine ⟨R.u2, ?_, ?_⟩ <;> unfold Incident
        · rw [hends]; simp
        · rw [hge]; simp
    exact (proper (by
      intro he
      apply hw
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      right
      rcases Sym2.eq_iff.mp (hends.symm.trans (he ▸ hge)) with h | h
      · exact Or.inr h.2
      · exact Or.inl h.2) hadj hfc) hgc

private theorem ScheideReplacementUnionClosed_branch_148.{u_1, u_2} :
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))) (R : ScheideReplacementData
        G k e0 phi T C D d) {f : E} {c : Fin k} {v : V}, phi f = some c → c ∈ MissingColors G phi
        v →
    let phiD := TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d)) (↑d : Fin k) (Sum.inl (D.v0
        d)); ColoredVertexSetClosed G phiD (TreeSequenceVertexSet R.replacementTree) → (
    ∀ {a : Fin k}, a ∈ MissingColors G phi R.u1 ∨ a ∈ MissingColors G phi R.u2 →
    ∃ (g : E), phi g = some a ∧ G.ends g = s(C.blockVertex (D.gammaIndex d) 0, C.blockVertex
        (D.gammaIndex d) 1)) → (
    ∃ (g : E), phi g = some c ∧ (G.ends g = s(R.u1, R.u2) ∨ G.ends g = s(C.blockVertex
        (D.gammaIndex d) 0, C.blockVertex (D.gammaIndex d) 1))) →
    ∀ (u w : V), w ∉ TreeSequenceVertexSet T ∪ { R.u1, R.u2 } → G.ends f = s(u, w) →
        IsProperEdgeColoring G phi → (u ∈ TreeSequenceVertexSet T → f ≠ D.f0 d → phiD f = phi f) →
        u ∈ TreeSequenceVertexSet T ∨ u = R.u1 ∨ u = R.u2 → v = R.u1 → False := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D d R f c v hfc hmiss phiD hrepClosed blockInternal
      pairOrBlock u w hw hends proper switchOnTree hu hv1
  have notDelta : c ≠ d.1 := by
    intro hc
    subst c
    have hm : d.1 ∈ MissingColors G phi R.u1 := hv1 ▸ hmiss
    have hn : d.1 ∉ PresentColors G phi R.u1 := by
      simpa [MissingColors] using hm
    have hp : d.1 ∈ PresentColors G phi R.u1 := by
      classical
      rw [PresentColors]
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      exact ⟨R.f1, by change R.u1 ∈ G.ends R.f1; rw [R.f1_ends]; simp,
        R.f1_color⟩
    exact hn hp
  obtain ⟨g, hgc, hge⟩ := blockInternal (Or.inl (hv1 ▸ hmiss))
  have blockMem0 : C.blockVertex (D.gammaIndex d) 0 ∈
      TreeSequenceVertexSet T := by
    let : DecidableEq V := Classical.decEq V
    unfold TreeSequenceVertexSet
    apply Finset.mem_image.mpr
    refine ⟨⟨C.p + 2 * (D.gammaIndex d).val, by
      have hh := C.length_eq
      omega⟩, by simp, ?_⟩
    simpa using C.block_vertex_position (D.gammaIndex d) 0
  have blockMem1 : C.blockVertex (D.gammaIndex d) 1 ∈
      TreeSequenceVertexSet T := by
    let : DecidableEq V := Classical.decEq V
    unfold TreeSequenceVertexSet
    apply Finset.mem_image.mpr
    refine ⟨⟨C.p + 2 * (D.gammaIndex d).val + 1, by
      have hh := C.length_eq
      omega⟩, by simp, ?_⟩
    simpa using C.block_vertex_position (D.gammaIndex d) 1
  have hmissD : c ∈ MissingColors G phiD v := by
    have hn : ¬ ∃ e, Incident G v e ∧ phi e = some c := by
      simpa [MissingColors, PresentColors] using hmiss
    have hnD : ¬ ∃ e, Incident G v e ∧ phiD e = some c := by
      intro hp
      rcases hp with ⟨e, he, hec⟩
      apply hn
      refine ⟨e, he, ?_⟩
      rw [← ScheideReplacementPairFixed G k e0 phi T C D d R e]
      · exact hec
      · exact Or.inl (hv1 ▸ he)
    simpa [MissingColors, PresentColors] using hnD
  have huRep : u ∈ TreeSequenceVertexSet R.replacementTree := by
    rw [R.replacement_vertices]
    simp only [Finset.mem_union]
    by_cases hu1 : u = R.u1 ∨ u = R.u2
    · exact Or.inr (by simpa using hu1)
    · have hut : u ∈ TreeSequenceVertexSet T := by
        simpa [hu1] using hu
      by_cases hb0 : u = C.blockVertex (D.gammaIndex d) 0
      · have hfg : f ≠ g := by
          intro he
          apply hw
          have hwg : w ∈ G.ends g := by
            rw [← he, hends]
            simp
          rw [hge] at hwg
          rcases Sym2.mem_iff.mp hwg with h | h
          · simp [h, blockMem0]
          · simp [h, blockMem1]
        have hadj' : AdjacentEdges G f g := by
          refine ⟨u, ?_, ?_⟩
          · change u ∈ G.ends f
            rw [hends]
            simp [hb0]
          · change u ∈ G.ends g
            rw [hge]
            simp [hb0]
        exact False.elim ((proper hfg hadj' hfc) hgc)
      · by_cases hb1 : u = C.blockVertex (D.gammaIndex d) 1
        · have hfg : f ≠ g := by
            intro he
            apply hw
            have hwg : w ∈ G.ends g := by
              rw [← he, hends]
              simp
            rw [hge] at hwg
            rcases Sym2.mem_iff.mp hwg with h | h
            · simp [h, blockMem0]
            · simp [h, blockMem1]
          have hadj' : AdjacentEdges G f g := by
            refine ⟨u, ?_, ?_⟩
            · change u ∈ G.ends f
              rw [hends]
              simp [hb1]
            · change u ∈ G.ends g
              rw [hge]
              simp [hb1]
          exact False.elim ((proper hfg hadj' hfc) hgc)
        · exact Or.inl (by
            simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
            exact ⟨hut, by simp [hb0, hb1]⟩)
  have hwRep : w ∉ TreeSequenceVertexSet R.replacementTree := by
    intro hwR
    rw [R.replacement_vertices] at hwR
    simp only [Finset.mem_union] at hwR
    apply hw
    apply Finset.mem_union.mpr
    rcases hwR with hwR | hwR
    · exact Or.inl (Finset.mem_sdiff.mp hwR).1
    · exact Or.inr (by simpa using hwR)
  have hfb : f ∈ BoundaryEdges G (TreeSequenceVertexSet R.replacementTree) := by
    unfold BoundaryEdges
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨u, huRep, w, hwRep, hends⟩
  have hne : f ≠ D.f0 d := by
    intro he
    have := hfc
    rw [he, D.f0_color d] at this
    exact notDelta (by simpa using this.symm)
  have hfd : phiD f = some c := by
    by_cases huPair : u = R.u1 ∨ u = R.u2
    · change TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d)) d.1
        (Sum.inl (D.v0 d)) f = some c
      rw [ScheideReplacementPairFixed G k e0 phi T C D d R f]
      · exact hfc
      · rcases huPair with huPair | huPair
        · exact Or.inl (by change R.u1 ∈ G.ends f; rw [hends]; simp [huPair])
        · exact Or.inr (by change R.u2 ∈ G.ends f; rw [hends]; simp [huPair])
    · have hut : u ∈ TreeSequenceVertexSet T := by simpa [huPair] using hu
      exact (switchOnTree hut hne).trans hfc
  apply (hrepClosed (v := v) hfb (by
    rw [R.replacement_vertices]
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    exact Or.inr (Or.inl hv1)) hfd)
  exact hmissD

private theorem ScheideReplacementUnionClosed_branch_276.{u_1, u_2} :
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))) (R : ScheideReplacementData
        G k e0 phi T C D d) {f : E} {c : Fin k} {v : V}, phi f = some c → c ∈ MissingColors G phi
        v →
    let phiD := TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d)) (↑d : Fin k) (Sum.inl (D.v0
        d)); ColoredVertexSetClosed G phiD (TreeSequenceVertexSet R.replacementTree) → (
    ∀ {a : Fin k}, a ∈ MissingColors G phi R.u1 ∨ a ∈ MissingColors G phi R.u2 →
    ∃ (g : E), phi g = some a ∧ G.ends g = s(C.blockVertex (D.gammaIndex d) 0, C.blockVertex
        (D.gammaIndex d) 1)) → (
    ∃ (g : E), phi g = some c ∧ (G.ends g = s(R.u1, R.u2) ∨ G.ends g = s(C.blockVertex
        (D.gammaIndex d) 0, C.blockVertex (D.gammaIndex d) 1))) →
    ∀ (u w : V), w ∉ TreeSequenceVertexSet T ∪ { R.u1, R.u2 } → G.ends f = s(u, w) →
        IsProperEdgeColoring G phi → (u ∈ TreeSequenceVertexSet T → f ≠ D.f0 d → phiD f = phi f) →
        u ∈ TreeSequenceVertexSet T ∨ u = R.u1 ∨ u = R.u2 → v = R.u2 → False := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D d R f c v hfc hmiss phiD hrepClosed blockInternal
      pairOrBlock u w hw hends proper switchOnTree hu hv2
  have notDelta : c ≠ d.1 := by
    intro hc
    subst c
    have hm : d.1 ∈ MissingColors G phi R.u2 := hv2 ▸ hmiss
    have hn : d.1 ∉ PresentColors G phi R.u2 := by simpa [MissingColors] using hm
    have hp : d.1 ∈ PresentColors G phi R.u2 := by
      classical
      rw [PresentColors]
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      exact ⟨R.f2, by change R.u2 ∈ G.ends R.f2; rw [R.f2_ends]; simp,
        R.f2_color⟩
    exact hn hp
  obtain ⟨g, hgc, hge⟩ := blockInternal (Or.inr (hv2 ▸ hmiss))
  have blockMem0 : C.blockVertex (D.gammaIndex d) 0 ∈
      TreeSequenceVertexSet T := by
    let : DecidableEq V := Classical.decEq V
    unfold TreeSequenceVertexSet
    apply Finset.mem_image.mpr
    refine ⟨⟨C.p + 2 * (D.gammaIndex d).val, by
      have hh := C.length_eq
      omega⟩, by simp, ?_⟩
    simpa using C.block_vertex_position (D.gammaIndex d) 0
  have blockMem1 : C.blockVertex (D.gammaIndex d) 1 ∈
      TreeSequenceVertexSet T := by
    let : DecidableEq V := Classical.decEq V
    unfold TreeSequenceVertexSet
    apply Finset.mem_image.mpr
    refine ⟨⟨C.p + 2 * (D.gammaIndex d).val + 1, by
      have hh := C.length_eq
      omega⟩, by simp, ?_⟩
    simpa using C.block_vertex_position (D.gammaIndex d) 1
  have hmissD : c ∈ MissingColors G phiD v := by
    have hn : ¬ ∃ e, Incident G v e ∧ phi e = some c := by
      simpa [MissingColors, PresentColors] using hmiss
    have hnD : ¬ ∃ e, Incident G v e ∧ phiD e = some c := by
      intro hp
      rcases hp with ⟨e, he, hec⟩
      apply hn
      refine ⟨e, he, ?_⟩
      rw [← ScheideReplacementPairFixed G k e0 phi T C D d R e]
      · exact hec
      · exact Or.inr (hv2 ▸ he)
    simpa [MissingColors, PresentColors] using hnD
  have huRep : u ∈ TreeSequenceVertexSet R.replacementTree := by
    rw [R.replacement_vertices]
    simp only [Finset.mem_union]
    by_cases hu1 : u = R.u1 ∨ u = R.u2
    · exact Or.inr (by simpa using hu1)
    · have hut : u ∈ TreeSequenceVertexSet T := by simpa [hu1] using hu
      by_cases hb0 : u = C.blockVertex (D.gammaIndex d) 0
      · have hfg : f ≠ g := by
          intro he
          apply hw
          have hwg : w ∈ G.ends g := by rw [← he, hends]; simp
          rw [hge] at hwg
          rcases Sym2.mem_iff.mp hwg with h | h
          · simp [h, blockMem0]
          · simp [h, blockMem1]
        have hadj' : AdjacentEdges G f g := by
          refine ⟨u, ?_, ?_⟩
          · change u ∈ G.ends f; rw [hends]; simp [hb0]
          · change u ∈ G.ends g; rw [hge]; simp [hb0]
        exact False.elim ((proper hfg hadj' hfc) hgc)
      · by_cases hb1 : u = C.blockVertex (D.gammaIndex d) 1
        · have hfg : f ≠ g := by
            intro he
            apply hw
            have hwg : w ∈ G.ends g := by rw [← he, hends]; simp
            rw [hge] at hwg
            rcases Sym2.mem_iff.mp hwg with h | h
            · simp [h, blockMem0]
            · simp [h, blockMem1]
          have hadj' : AdjacentEdges G f g := by
            refine ⟨u, ?_, ?_⟩
            · change u ∈ G.ends f; rw [hends]; simp [hb1]
            · change u ∈ G.ends g; rw [hge]; simp [hb1]
          exact False.elim ((proper hfg hadj' hfc) hgc)
        · exact Or.inl (by
            simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
            exact ⟨hut, by simp [hb0, hb1]⟩)
  have hwRep : w ∉ TreeSequenceVertexSet R.replacementTree := by
    intro hwR
    rw [R.replacement_vertices] at hwR
    simp only [Finset.mem_union] at hwR
    apply hw
    apply Finset.mem_union.mpr
    rcases hwR with hwR | hwR
    · exact Or.inl (Finset.mem_sdiff.mp hwR).1
    · exact Or.inr (by simpa using hwR)
  have hfb : f ∈ BoundaryEdges G (TreeSequenceVertexSet R.replacementTree) := by
    unfold BoundaryEdges
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨u, huRep, w, hwRep, hends⟩
  have hne : f ≠ D.f0 d := by
    intro he
    have hh := hfc
    rw [he, D.f0_color d] at hh
    exact notDelta (by simpa using hh.symm)
  have hfd : phiD f = some c := by
    by_cases huPair : u = R.u1 ∨ u = R.u2
    · change TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d)) d.1
        (Sum.inl (D.v0 d)) f = some c
      rw [ScheideReplacementPairFixed G k e0 phi T C D d R f]
      · exact hfc
      · rcases huPair with huPair | huPair
        · exact Or.inl (by change R.u1 ∈ G.ends f; rw [hends]; simp [huPair])
        · exact Or.inr (by change R.u2 ∈ G.ends f; rw [hends]; simp [huPair])
    · have hut : u ∈ TreeSequenceVertexSet T := by simpa [huPair] using hu
      exact (switchOnTree hut hne).trans hfc
  apply (hrepClosed (v := v) hfb (by
    rw [R.replacement_vertices]
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    exact Or.inr (Or.inr hv2)) hfd)
  exact hmissD

theorem ScheideReplacementUnionClosed {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (C : ScheideReducedConfiguration G k e0 phi T)
    (D : ScheideDefectiveSetup G k e0 phi T C)
    (d : {delta // delta ∈ DefectiveColors G phi (TreeSequenceVertexSet T)})
    (R : ScheideReplacementData G k e0 phi T C D d) :
    ColoredVertexSetClosed G phi (TreeSequenceVertexSet T ∪ { R.u1, R.u2 }) := by
  unfold ColoredVertexSetClosed
  intro f c v hf hv hfc
  by_contra hmiss
  have htree := ScheideGlobalMaximumOrder G k e0 phi T
    C.globally_maximum
  have htreeClosed : ColoredVertexSetClosed G phi (TreeSequenceVertexSet T) :=
    htree.2.2.2.2
  let phiD := TwoColorComponentSwap G phi
      (C.gamma (D.gammaIndex d)) d.1 (Sum.inl (D.v0 d))
  have hmaximum := ScheideReplacementMaximum G k e0 phi T C D d R
  dsimp [phiD] at hmaximum
  have hrep := ScheideGlobalMaximumOrder G k e0 phiD R.replacementTree
    hmaximum.2.2
  have hrepClosed : ColoredVertexSetClosed G phiD
      (TreeSequenceVertexSet R.replacementTree) := hrep.2.2.2.2
  have pairInternal : ∀ {a : Fin k},
      a ∈ MissingColors G phi (C.blockVertex (D.gammaIndex d) 0) ∨
        a ∈ MissingColors G phi (C.blockVertex (D.gammaIndex d) 1) →
      ∃ g : E, phi g = some a ∧ G.ends g = s(R.u1, R.u2) := by
    intro a ha
    exact (ScheideSymmetricMissingInternal G k e0 phi T C D d R).2 a ha
  have blockInternal :
    ∀ {a : Fin k}, a ∈ MissingColors G phi R.u1 ∨ a ∈ MissingColors G phi R.u2 →
    ∃ g : E, phi g = some a ∧ G.ends g = s(C.blockVertex (D.gammaIndex d) 0, C.blockVertex
        (D.gammaIndex d) 1) := by
    intro a ha
    exact (ScheideSymmetricMissingInternal G k e0 phi T C D d R).1 a ha
  have pairOrBlock : ∃ g : E, phi g = some c ∧
      (G.ends g = s(R.u1, R.u2) ∨
        G.ends g = s(C.blockVertex (D.gammaIndex d) 0,
          C.blockVertex (D.gammaIndex d) 1)) := by
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with hvTree | hv1 | hv2
    · by_cases hv0 : v = C.blockVertex (D.gammaIndex d) 0
      · refine ⟨(pairInternal (Or.inl (hv0 ▸ hmiss))).choose, ?_, ?_⟩
        · exact (pairInternal (Or.inl (hv0 ▸ hmiss))).choose_spec.1
        · exact Or.inl (pairInternal (Or.inl (hv0 ▸ hmiss))).choose_spec.2
      by_cases hv3 : v = C.blockVertex (D.gammaIndex d) 1
      · refine ⟨(pairInternal (Or.inr (hv3 ▸ hmiss))).choose, ?_, ?_⟩
        · exact (pairInternal (Or.inr (hv3 ▸ hmiss))).choose_spec.1
        · exact Or.inl (pairInternal (Or.inr (hv3 ▸ hmiss))).choose_spec.2
      have hvrem : v ∈ (TreeSequenceVertexSet T \
        {C.blockVertex (D.gammaIndex d) 0,
          C.blockVertex (D.gammaIndex d) 1}) := by
        simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
        exact ⟨hvTree, by simp [hv0, hv3]⟩
      by_cases hc : c = C.gamma (D.gammaIndex d)
      · subst c
        obtain ⟨g, hgc, hge⟩ :=
          ScheideSymmetricDefectiveInternal G k e0 phi T C D d R |>.2
        exact ⟨g, hgc, Or.inl hge⟩
      · obtain ⟨g, hgc, hge⟩ := ScheideReplacementInternalMissing G k e0 phi T C D d R c
          hc ⟨v, hvrem, hmiss⟩
        exact ⟨g, hgc, Or.inl hge⟩
    · obtain ⟨g, hgc, hge⟩ := blockInternal (Or.inl (hv1 ▸ hmiss))
      exact ⟨g, hgc, Or.inr hge⟩
    · obtain ⟨g, hgc, hge⟩ := blockInternal (Or.inr (hv2 ▸ hmiss))
      exact ⟨g, hgc, Or.inr hge⟩
  simp only [BoundaryEdges, Finset.union_insert, Finset.union_singleton, Finset.mem_insert, not_or,
    exists_eq_or_imp, Finset.mem_filter, Finset.mem_univ, true_and] at hf
  rcases (show ∃ u ∈ (TreeSequenceVertexSet T ∪ {R.u1, R.u2}),
      ∃ w ∉ (TreeSequenceVertexSet T ∪ {R.u1, R.u2}),
        G.ends f = s(u, w) by simpa [Sym2.mem_iff] using hf) with
    ⟨u, hu, w, hw, hends⟩
  have proper := C.globally_maximum.1.2.2.2.1
  have switchOnTree (hq : u ∈ TreeSequenceVertexSet T)
      (hne : f ≠ D.f0 d) :
      phiD f = phi f := by
    apply (ScheideDefectiveSwitchEffect G k e0 phi T C D d).2.2.2.2.1 f
    · exact ⟨u, hq, by change u ∈ G.ends f; rw [hends]; simp⟩
    · exact hne
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hv hu
  rcases hv with hvTree | hv1 | hv2
  · exact @ScheideReplacementUnionClosed_branch_104 V E inferInstance inferInstance inferInstance
      inferInstance G k e0 phi T C D d R f c v hfc hmiss htreeClosed pairInternal pairOrBlock u w
      hw hends proper switchOnTree hu hvTree
  · exact @ScheideReplacementUnionClosed_branch_148 V E inferInstance inferInstance inferInstance
      inferInstance G k e0 phi T C D d R f c v hfc hmiss hrepClosed blockInternal pairOrBlock u w
      hw hends proper switchOnTree hu hv1
  · exact @ScheideReplacementUnionClosed_branch_276 V E inferInstance inferInstance inferInstance
      inferInstance G k e0 phi T C D d R f c v hfc hmiss hrepClosed blockInternal pairOrBlock u w
      hw hends proper switchOnTree hu hv2
end GoldbergSeymour

end
