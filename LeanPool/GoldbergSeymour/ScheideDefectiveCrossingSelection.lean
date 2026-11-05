/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ScheideDefectiveSetup
public import LeanPool.GoldbergSeymour.ScheideStructuralInternalPair

/-!
# Scheide Defective Crossing Selection

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

open scoped Sym2

private theorem ScheideDefectiveCrossingSelection_hg3_279.{u_1, u_2} :
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))),
    let i := D.gammaIndex d;
    let X := TreeSequenceVertexSet T;
    let U := {C.blockVertex i 0, C.blockVertex i 1};
    let Z := X \ U; (
    ∀ (e f : E), e ∈ BoundaryColorEdges G phi X (↑d : Fin k) → f ∈ BoundaryColorEdges G phi X (↑d
        : Fin k) → e ≠ f → ¬((
    ∃ a ∈ U, Incident G a e) ∧
    ∃ a ∈ U, Incident G a f)) →
    ∀ (a b c : E), a ∈ BoundaryColorEdges G phi X (↑d : Fin k) → b ∈ BoundaryColorEdges G phi X
        (↑d : Fin k) → c ∈ BoundaryColorEdges G phi X (↑d : Fin k) → a ≠ b → a ≠ c → b ≠ c → (
    ∀ e ∈ BoundaryColorEdges G phi X (↑d : Fin k), e = D.f0 d ∨ (
    ∃ z ∈ Z,
    ∃ w ∉ X, G.ends e = s(z, w)) ∨
    ∃ a ∈ U, Incident G a e) →
    ∃ g3 ∈ BoundaryColorEdges G phi X (↑d : Fin k), g3 ≠ D.f0 d ∧
    ∃ z3 ∈ Z,
    ∃ w3 ∉ X, G.ends g3 = s(z3, w3) := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D d i X U Z hu_unique a b c ha hb hc hab hac hbc split_edge
  have finish : ∀ e, e ∈ BoundaryColorEdges G phi X d.1 → e ≠ D.f0 d →
      (∃ z ∈ Z, ∃ w ∉ X, G.ends e = s(z,w)) →
      ∃ g3, g3 ∈ BoundaryColorEdges G phi X d.1 ∧ g3 ≠ D.f0 d ∧
        ∃ z ∈ Z, ∃ w ∉ X, G.ends g3 = s(z,w) := by
    intro e he hne hext
    exact ⟨e, he, hne, hext⟩
  have choose : ∀ e, e ∈ BoundaryColorEdges G phi X d.1 →
      e = D.f0 d ∨
        (∃ z ∈ Z, ∃ w ∉ X, G.ends e = s(z,w)) ∨
        ∃ a ∈ U, Incident G a e := split_edge
  rcases choose a ha with hae | hae | hau
  · rcases choose b hb with hbe | hbe | hbu
    · exact False.elim (hab (hae.trans hbe.symm))
    · exact finish b hb (by intro h; exact hab (h ▸ hae)) hbe
    · rcases choose c hc with hce | hce | hcu
      · exact False.elim (hac (hae.trans hce.symm))
      · exact finish c hc (by intro h; exact hac (h ▸ hae)) hce
      · exact False.elim (hu_unique b c hb hc hbc ⟨hbu, hcu⟩)
  · by_cases hane : a = D.f0 d
    · rcases choose b hb with hbe | hbe | hbu
      · exact False.elim (hab (hane.trans hbe.symm))
      · exact finish b hb (by intro h; exact hab (h ▸ hane)) hbe
      · rcases choose c hc with hce | hce | hcu
        · exact False.elim (hac (hane.trans hce.symm))
        · exact finish c hc (by intro h; exact hac (h ▸ hane)) hce
        · exact False.elim (hu_unique b c hb hc hbc ⟨hbu, hcu⟩)
    · exact finish a ha hane hae
  · rcases choose b hb with hbe | hbe | hbu
    · rcases choose c hc with hce | hce | hcu
      · exact False.elim (hbc (hbe.trans hce.symm))
      · exact finish c hc (by intro h; exact hbc (h ▸ hbe)) hce
      · exact False.elim (hu_unique a c ha hc hac ⟨hau, hcu⟩)
    · by_cases hbne : b = D.f0 d
      · rcases choose c hc with hce | hce | hcu
        · exact False.elim (hbc (hbne.trans hce.symm))
        · exact finish c hc (by intro h; exact hbc (h ▸ hbne)) hce
        · exact False.elim (hu_unique a c ha hc hac ⟨hau, hcu⟩)
      · exact finish b hb hbne hbe
    · exact False.elim (hu_unique a b ha hb hab ⟨hau, hbu⟩)

private theorem helper_hu01_145.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))),
    let i : Fin C.s := D.gammaIndex d; T.length + (1 : ℕ) = C.p + (2 : ℕ) * C.s → C.blockVertex i
        (0 : Fin (2 : ℕ)) ≠ C.blockVertex i (1 : Fin (2 : ℕ)) := by
  classical
  intro V E _ _ _ G k e0 phi T C D d i hlen h
  have hv := C.block_vertex_position i 0
  have hw := C.block_vertex_position i 1
  have hi := i.isLt
  have hp := C.p_ge_two
  have heq : T.vertex ⟨C.p + 2 * i.val,
      by omega⟩ = T.vertex ⟨C.p + 2 * i.val + 1, by omega⟩ := by
    have hv' : T.vertex ⟨C.p + 2 * i.val, by omega⟩ = C.blockVertex i 0 := by
      simpa using hv
    have hw' : T.vertex ⟨C.p + 2 * i.val + 1, by omega⟩ = C.blockVertex i 1 := by
      simpa using hw
    rw [hv', hw', h]
  have hi' := T.vertex_injective heq
  have hval : C.p + 2 * i.val ≠ C.p + 2 * i.val + 1 := by omega
  exact hval (congrArg Fin.val hi')

private theorem helper_hv0X_192.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))),
    let X : Finset V := TreeSequenceVertexSet T; D.v0 d ∈ X := by
  classical
  intro V E _ _ _ G k e0 phi T C D d X
  have hv := D.v0_is_exit d
  have hv'' : D.v0 d ∈ (Finset.univ.filter fun v => ScheideExitVertex T phi v) := by
    simpa [ScheideExitVertices] using hv
  have hv' : ScheideExitVertex T phi (D.v0 d) := (Finset.mem_filter.mp hv'').2
  rcases hv' with ⟨u, gamma, delta, hu, hgamma, hdelta, z, path, hpath, r, hr, hrv, htail⟩
  exact hrv

private theorem helper_hv0base_201.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))),
    let i : Fin C.s := D.gammaIndex d;
    let X : Finset V := TreeSequenceVertexSet T; T.length + (1 : ℕ) = C.p + (2 : ℕ) * C.s →
        ColoredVertexSetElementary G phi X → D.v0 d ∈ X → C.gamma i ∈ MissingColors G phi (D.v0 d)
        →
    ∃ (q : Fin C.p), D.v0 d = C.y q := by
  classical
  intro V E _ _ _ G k e0 phi T C D d i X hlen helem hv0X hv0gamma
  obtain ⟨r, hr⟩ := C.exit_covered (D.v0 d) (D.v0_is_exit d)
  obtain ⟨q, hq⟩ := C.block_color_missing_on_base i
  have hsame : r = i :=
    (C.exit_exactly_one (D.v0 d) (D.v0_is_exit d)).unique hr hv0gamma
  have hmq : C.gamma i ∈ MissingColors G phi (C.y q) := by simpa [hsame] using hq
  by_cases heq : D.v0 d = C.y q
  · exact ⟨q, heq⟩
  · exfalso
    have hqX : C.y q ∈ X := by
      simp only [X, TreeSequenceVertexSet, Finset.mem_image]
      exact ⟨⟨q.val, by have hp := C.p_ge_two; omega⟩, Finset.mem_univ _,
          C.base_vertex_position q⟩
    exact Finset.disjoint_left.mp (helem hv0X hqX heq)
      hv0gamma hmq

private theorem helper_base_block_ne_222.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))),
    let i : Fin C.s := D.gammaIndex d;
    ∀ (q : Fin C.p) (j : Fin (2 : ℕ)), C.y q ≠ C.blockVertex i j := by
  classical
  intro V E _ _ _ G k e0 phi T C D d i q j heq
  have hq := q.isLt
  have hi := i.isLt
  have hj := j.isLt
  have he := C.base_vertex_position q
  have hb := C.block_vertex_position i j
  have hpos := T.vertex_injective (he.trans (heq ▸ hb.symm))
  have hp := C.p_ge_two
  have hpos' := congrArg Fin.val hpos
  simp at hpos'
  omega

private theorem helper_hv0Z_235.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))),
    let i : Fin C.s := D.gammaIndex d;
    let X : Finset V := TreeSequenceVertexSet T;
    let U : Finset V := (insert (C.blockVertex i (0 : Fin (2 : ℕ)))
        ({C.blockVertex i (1 : Fin (2 : ℕ))} : Finset V) : Finset V);
    let Z : Finset V := X \ U; D.v0 d ∈ X → (
    ∃ (q : Fin C.p), D.v0 d = C.y q) → (
    ∀ (q : Fin C.p) (j : Fin (2 : ℕ)), C.y q ≠ C.blockVertex i j) → D.v0 d ∈ Z := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D d i X U Z hv0X hv0base base_block_ne
  apply Finset.mem_sdiff.mpr
  refine ⟨hv0X, ?_⟩
  intro hv
  simp only [U, Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with hv | hv
  · exact base_block_ne _ _ (hv0base.choose_spec.symm.trans hv)
  · exact base_block_ne _ _ (hv0base.choose_spec.symm.trans hv)

private theorem helper_hu2_251.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))),
    ∀ x ∈ (insert (C.blockVertex (D.gammaIndex d) (0 : Fin (2 : ℕ)))
        ({C.blockVertex (D.gammaIndex d) (1 : Fin (2 : ℕ))} : Finset V) : Finset V),
    let i : Fin C.s := D.gammaIndex d;
    let U : Finset V := (insert (C.blockVertex i (0 : Fin (2 : ℕ)))
        ({C.blockVertex i (1 : Fin (2 : ℕ))} : Finset V) : Finset V);
    ∃ (u2 : V), (insert x ({ u2 } : Finset V) : Finset V) = U := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D d x hx i U
  have hxU : x ∈ U := by simpa [U, i] using hx
  rcases Finset.mem_insert.mp hxU with hxeq | hxeq
  · refine ⟨C.blockVertex i 1, ?_⟩
    simp [U, hxeq]
  · have hxeq' : x = C.blockVertex i 1 := by simpa using hxeq
    refine ⟨C.blockVertex i 0, ?_⟩
    simp [U, hxeq', Finset.pair_comm]

private theorem helper_hu12_262.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))) (x : V),
    let i : Fin C.s := D.gammaIndex d;
    let U : Finset V := (insert (C.blockVertex i (0 : Fin (2 : ℕ)))
        ({C.blockVertex i (1 : Fin (2 : ℕ))} : Finset V) : Finset V); U.card = (2 : ℕ) →
    ∀ (u2 : V), (insert x ({ u2 } : Finset V) : Finset V) = U → u2 ∈ U → x ≠ u2 := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D d x i U hu_card u2 hpair hu2U h
  subst u2
  have := hu_card
  rw [← hpair] at this
  simp at this

private theorem helper_hbad_291.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))) (g1 : E),
    ∀ x ∈ (insert (C.blockVertex (D.gammaIndex d) (0 : Fin (2 : ℕ)))
        ({C.blockVertex (D.gammaIndex d) (1 : Fin (2 : ℕ))} : Finset V) : Finset V), Incident G x
        g1 →
    ∀ z1 ∈ TreeSequenceVertexSet T \ (insert (C.blockVertex (D.gammaIndex d) (0 : Fin (2 : ℕ)))
        ({C.blockVertex (D.gammaIndex d) (1 : Fin (2 : ℕ))} : Finset V) : Finset V), Incident G z1
        g1 →
    let i : Fin C.s := D.gammaIndex d;
    let X : Finset V := TreeSequenceVertexSet T;
    let U : Finset V := (insert (C.blockVertex i (0 : Fin (2 : ℕ)))
        ({C.blockVertex i (1 : Fin (2 : ℕ))} : Finset V) : Finset V); x ∈ X → G.ends g1 = s(x, z1)
        →
    ∀ (u2 : V), (insert x ({ u2 } : Finset V) : Finset V) = U → x ∈ U → x ≠ u2 → g1 ∉
        BoundaryColorEdges G phi X (↑d : Fin k) := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D d g1 x hx hxg1 z1 hz1 hz1g1 i X U hxX hg1ends u2 hpair hu1U
      hu12 h
  have hb := (Finset.mem_filter.mp h).1
  simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and] at hb
  rcases hb with ⟨a, ha, b, hb, he⟩
  have hmem : b ∈ s(x,z1) := by
    rw [← hg1ends, he]
    simp
  have : b = x ∨ b = z1 := by simpa using hmem
  rcases this with rfl | rfl
  · exact hb hxX
  · exact hb (Finset.mem_sdiff.mp hz1).1

private theorem helper_hu_endpoint_309.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))) (g1 : E), phi g1 = some (↑d
        : Fin k) →
    ∀ (x : V), Incident G x g1 →
    let i : Fin C.s := D.gammaIndex d;
    let X : Finset V := TreeSequenceVertexSet T;
    let U : Finset V := (insert (C.blockVertex i (0 : Fin (2 : ℕ)))
        ({C.blockVertex i (1 : Fin (2 : ℕ))} : Finset V) : Finset V); IsProperEdgeColoring G phi →
        g1 ∉ BoundaryColorEdges G phi X (↑d : Fin k) →
    ∀ e ∈ BoundaryColorEdges G phi X (↑d : Fin k),
    ∀ a ∈ U, Incident G a e → a ≠ x := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D d g1 hg1 x hxg1 i X U hproper hbad e he a ha hae hax
  have heg : e ≠ g1 := by
    intro heq
    exact hbad (by simpa [heq] using he)
  have hadj : AdjacentEdges G e g1 := by
    unfold AdjacentEdges
    exact ⟨a, hae, by simpa [hax] using hxg1⟩
  have hce := (Finset.mem_filter.mp he).2
  exact (hproper heg hadj hce) hg1

private theorem helper_hu_unique_320.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))) (x : V),
    let i : Fin C.s := D.gammaIndex d;
    let X : Finset V := TreeSequenceVertexSet T;
    let U : Finset V := (insert (C.blockVertex i (0 : Fin (2 : ℕ)))
        ({C.blockVertex i (1 : Fin (2 : ℕ))} : Finset V) : Finset V); IsProperEdgeColoring G phi →
    ∀ (u2 : V), (insert x ({ u2 } : Finset V) : Finset V) = U → (
    ∀ e ∈ BoundaryColorEdges G phi X (↑d : Fin k),
    ∀ a ∈ U, Incident G a e → a ≠ x) →
    ∀ (e f : E), e ∈ BoundaryColorEdges G phi X (↑d : Fin k) → f ∈ BoundaryColorEdges G phi X (↑d
        : Fin k) → e ≠ f → ¬((
    ∃ a ∈ U, Incident G a e) ∧
    ∃ a ∈ U, Incident G a f) := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D d x i X U hproper u2 hpair hu_endpoint e f he hf hef hn
  rcases hn with ⟨⟨ae, hae, heae⟩, ⟨af, haf, hafinc⟩⟩
  have heax : ae ≠ x := hu_endpoint e he ae hae heae
  have hafx : af ≠ x := hu_endpoint f hf af haf hafinc
  have hae2 : ae = u2 := by
    rw [← hpair] at hae
    simpa [Finset.mem_insert, heax] using hae
  have haf2 : af = u2 := by
    rw [← hpair] at haf
    simpa [Finset.mem_insert, hafx] using haf
  subst ae
  subst af
  have hadj : AdjacentEdges G e f := ⟨u2, heae, hafinc⟩
  exact (hproper hef hadj (Finset.mem_filter.mp he).2) (Finset.mem_filter.mp hf).2

private theorem helper_split_edge_339.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
      [DecidableEq V] [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (C : ScheideReducedConfiguration G k e0 phi T)
      (D : ScheideDefectiveSetup G k e0 phi T C)
      (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))),
    let i : Fin C.s := D.gammaIndex d;
    let X : Finset V := TreeSequenceVertexSet T;
    let U : Finset V :=
      (insert (C.blockVertex i (0 : Fin (2 : ℕ)))
          ({C.blockVertex i (1 : Fin (2 : ℕ))} : Finset V) :
        Finset V);
    let Z : Finset V := X \ U;
    (∀ e ∈ BoundaryColorEdges G phi X (↑d : Fin k), ∃ a ∈ X, ∃ b ∉ X, G.ends e = s(a, b)) →
    ∀ e ∈ BoundaryColorEdges G phi X (↑d : Fin k),
    e = D.f0 d ∨ (∃ z ∈ Z, ∃ w ∉ X, G.ends e = s(z, w)) ∨ ∃ a ∈ U, Incident G a e := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D d i X U Z hparts e he
  obtain ⟨v, hv, w, hw, hev⟩ := hparts e he
  by_cases hvU : v ∈ U
  · exact Or.inr (Or.inr ⟨v, hvU, by simp [Incident, hev]⟩)
  · exact Or.inr (Or.inl ⟨v, Finset.mem_sdiff.mpr ⟨hv, hvU⟩, w, hw, hev⟩)

theorem ScheideDefectiveCrossingSelection {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (C : ScheideReducedConfiguration G k e0 phi T)
    (D : ScheideDefectiveSetup G k e0 phi T C)
    (d : {delta // delta ∈ DefectiveColors G phi (TreeSequenceVertexSet T)})
    (g1 : E) (hg1 : phi g1 = some d.1)
    (x : V) (hx : x ∈ ({C.blockVertex (D.gammaIndex d) 0,
      C.blockVertex (D.gammaIndex d) 1} : Finset V))
    (hxg1 : Incident G x g1)
    (z1 : V) (hz1 : z1 ∈ TreeSequenceVertexSet T \
      {C.blockVertex (D.gammaIndex d) 0,
        C.blockVertex (D.gammaIndex d) 1})
    (hz1g1 : Incident G z1 g1) :
    let i := D.gammaIndex d
    let X := TreeSequenceVertexSet T
    let U := ({C.blockVertex i 0, C.blockVertex i 1} : Finset V)
    let Z := X \ U
    ∃ u1 u2 : V, ∃ g2 g3 : E, ∃ z3 w3 : V,
      ({u1, u2} : Finset V) = U ∧ x = u1 ∧
      u1 ≠ u2 ∧ u1 ∈ U ∧ u2 ∈ U ∧ u1 ∈ X ∧ u2 ∈ X ∧
      D.v0 d ∈ Z ∧
      C.y ⟨0, lt_of_lt_of_le Nat.zero_lt_two C.p_ge_two⟩ ∈ Z ∧
      D.alpha0 ≠ C.gamma i ∧ D.alpha0 ≠ d.1 ∧ C.gamma i ≠ d.1 ∧
      G.ends g1 = s(u1, z1) ∧
      phi g2 = some D.alpha0 ∧ G.ends g2 = s(u1, u2) ∧
      g3 ∈ BoundaryColorEdges G phi X d.1 ∧ g3 ≠ D.f0 d ∧
      z3 ∈ Z ∧ w3 ∉ X ∧ G.ends g3 = s(z3, w3) ∧
      g1 ≠ g2 ∧ g1 ≠ g3 ∧ g2 ≠ g3 := by
  classical
  dsimp
  let i := D.gammaIndex d
  let X := TreeSequenceVertexSet T
  let U := ({C.blockVertex i 0, C.blockVertex i 1} : Finset V)
  let Z := X \ U
  have hlen := C.length_eq
  have hu01 : C.blockVertex i 0 ≠ C.blockVertex i 1 := by
    exact @helper_hu01_145 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k) (@e0)
        (@phi) (@T) (@C) (@D) (@d) (@hlen)
  have hu0X : C.blockVertex i 0 ∈ X := by
    simp only [X, TreeSequenceVertexSet, Finset.mem_image]
    have hp := C.p_ge_two
    exact ⟨⟨C.p + 2 * i.val, by omega⟩,
      Finset.mem_univ _, C.block_vertex_position i 0⟩
  have hu1X : C.blockVertex i 1 ∈ X := by
    simp only [X, TreeSequenceVertexSet, Finset.mem_image]
    have hp := C.p_ge_two
    exact ⟨⟨C.p + 2 * i.val + 1, by omega⟩,
      Finset.mem_univ _, C.block_vertex_position i 1⟩
  have hxX : x ∈ X := by
    rcases (show x = C.blockVertex i 0 ∨ x = C.blockVertex i 1 by simpa [i] using hx) with rfl | rfl
    · exact hu0X
    · exact hu1X
  have hu_card : U.card = 2 := by simp [U, hu01]
  have hpair_mem : ∀ {a b : V} {e : E}, a ∈ G.ends e → b ∈ G.ends e →
      a ≠ b → G.ends e = s(a,b) := by
    intro a b e ha hb hab
    change a ∈ G.ends e at ha
    change b ∈ G.ends e at hb
    exact (Sym2.mem_and_mem_iff hab).mp ⟨ha, hb⟩
  have hg1ends : G.ends g1 = s(x,z1) := by
    apply hpair_mem hxg1 hz1g1
    intro h
    exact (Finset.mem_sdiff.mp hz1).2 (by simpa [h] using hx)
  have horder := ScheideGlobalMaximumOrder G k e0 phi T C.globally_maximum
  have helem : ColoredVertexSetElementary G phi X := by
    exact horder.2.2.2.1
  have hclosed : ColoredVertexSetClosed G phi X := by
    exact horder.2.2.2.2
  have hproper : IsProperEdgeColoring G phi := C.globally_maximum.1.2.2.2.1
  have hv0X : D.v0 d ∈ X := by
    exact @helper_hv0X_192 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k) (@e0)
        (@phi) (@T) (@C) (@D) (@d)
  have hv0gamma : C.gamma i ∈ MissingColors G phi (D.v0 d) :=
    D.gamma_missing_at_v0 d
  have hv0base : ∃ q : Fin C.p, D.v0 d = C.y q := by
    exact @helper_hv0base_201 (@V) (@E) inferInstance inferInstance  inferInstance
        (@G) (@k) (@e0) (@phi) (@T) (@C) (@D) (@d) (@hlen) (@helem) (@hv0X) (@hv0gamma)
  have hy0X : C.y ⟨0, lt_of_lt_of_le Nat.zero_lt_two C.p_ge_two⟩ ∈ X := by
    simp only [X, TreeSequenceVertexSet, Finset.mem_image]
    have hp := C.p_ge_two
    exact ⟨⟨0, by omega⟩, Finset.mem_univ _, C.base_vertex_position ⟨0, by omega⟩⟩
  have hy0base : ∃ q : Fin C.p, C.y ⟨0, lt_of_lt_of_le Nat.zero_lt_two C.p_ge_two⟩ = C.y q :=
    ⟨⟨0, by have hp := C.p_ge_two; omega⟩, rfl⟩
  have base_block_ne : ∀ q : Fin C.p, ∀ j : Fin 2,
      C.y q ≠ C.blockVertex i j := by
    exact @helper_base_block_ne_222 (@V) (@E) inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@phi) (@T) (@C) (@D) (@d)
  have hv0Z : D.v0 d ∈ Z := by
    exact @helper_hv0Z_235 (@V) (@E) inferInstance inferInstance inferInstance inferInstance (@G)
        (@k) (@e0) (@phi) (@T) (@C) (@D) (@d) (@hv0X) (@hv0base) (@base_block_ne)
  have hy0Z : C.y ⟨0, lt_of_lt_of_le Nat.zero_lt_two C.p_ge_two⟩ ∈ Z := by
    apply Finset.mem_sdiff.mpr
    refine ⟨hy0X, ?_⟩
    simp only [U, Finset.mem_insert, Finset.mem_singleton]
    intro hv
    rcases hv with hv | hv
    · exact base_block_ne _ _ hv
    · exact base_block_ne _ _ hv
  have hu2 : ∃ u2 : V, ({x, u2} : Finset V) = U := by
    exact @helper_hu2_251 (@V) (@E) inferInstance inferInstance inferInstance inferInstance (@G)
        (@k) (@e0) (@phi) (@T) (@C) (@D) (@d) (@x) (@hx)
  rcases hu2 with ⟨u2, hpair⟩
  have hu2U : u2 ∈ U := by rw [← hpair]; simp
  have hu1U : x ∈ U := hx
  have hu12 : x ≠ u2 := by
    exact @helper_hu12_262 (@V) (@E) inferInstance inferInstance inferInstance inferInstance (@G)
        (@k) (@e0) (@phi) (@T) (@C) (@D) (@d) (@x) (@hu_card) (@u2) (@hpair) (@hu2U)
  have hu2X : u2 ∈ X := by
    simp only [U, Finset.mem_insert, Finset.mem_singleton] at hu2U
    rcases hu2U with h | h
    · simpa [h] using hu0X
    · simpa [h] using hu1X
  have halpha_gamma : D.alpha0 ≠ C.gamma i := D.alpha0_not_block i
  have hg2 := ScheideStructuralInternalPair G k e0 phi T C i D.alpha0
    halpha_gamma ⟨_, hy0Z, D.alpha0_missing_at_y0⟩
  rcases hg2 with ⟨g2, hg2color, hg2ends⟩
  have hfacts := ScheideGlobalMaximumBoundaryFacts G k e0 phi T C.globally_maximum
  have hBcard : 3 ≤ (BoundaryColorEdges G phi X d.1).card := by
    simpa [X] using (hfacts.2.2 d.1 d.2).2
  have hdnot : ∀ v, v ∈ X → d.1 ∉ MissingColors G phi v := by
    intro v hv hm
    obtain ⟨b, hb⟩ := Finset.card_pos.mp (by omega : 0 < (BoundaryColorEdges G phi X d.1).card)
    have hbc := Finset.mem_filter.mp hb
    exact hclosed hbc.1 hv hbc.2 hm
  have hgammadelta : C.gamma i ≠ d.1 := by
    intro h
    exact hdnot (D.v0 d) hv0X (h ▸ hv0gamma)
  have halphadelta : D.alpha0 ≠ d.1 := by
    intro h
    exact hdnot _ hy0X (h ▸ D.alpha0_missing_at_y0)
  have hbad : g1 ∉ BoundaryColorEdges G phi X d.1 := by
    exact @helper_hbad_291 (@V) (@E) inferInstance inferInstance inferInstance inferInstance (@G)
        (@k) (@e0) (@phi) (@T) (@C) (@D) (@d) (@g1) (@x) (@hx) (@hxg1) (@z1) (@hz1) (@hz1g1)
        (@hxX) (@hg1ends) (@u2) (@hpair) (@hu1U) (@hu12)
  have hparts : ∀ e, e ∈ BoundaryColorEdges G phi X d.1 →
      ∃ a ∈ X, ∃ b ∉ X, G.ends e = s(a,b) := by
    intro e he
    have hb := (Finset.mem_filter.mp he).1
    simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and] at hb
    exact hb
  have hu_endpoint : ∀ e, e ∈ BoundaryColorEdges G phi X d.1 →
      ∀ a, a ∈ U → Incident G a e → a ≠ x := by
    exact @helper_hu_endpoint_309 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@phi) (@T) (@C) (@D) (@d) (@g1) (@hg1) (@x) (@hxg1)
        (@hproper) (@hbad)
  have hu_unique : ∀ e f, e ∈ BoundaryColorEdges G phi X d.1 →
      f ∈ BoundaryColorEdges G phi X d.1 → e ≠ f →
      ¬ ((∃ a ∈ U, Incident G a e) ∧ (∃ a ∈ U, Incident G a f)) := by
    exact @helper_hu_unique_320 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@phi) (@T) (@C) (@D) (@d) (@x) (@hproper) (@u2) (@hpair) (@hu_endpoint)
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ :=
    Finset.two_lt_card_iff.mp (lt_of_lt_of_le (by omega) hBcard)
  have split_edge : ∀ e, e ∈ BoundaryColorEdges G phi X d.1 →
      e = D.f0 d ∨ (∃ z ∈ Z, ∃ w ∉ X, G.ends e = s(z,w)) ∨
        ∃ a ∈ U, Incident G a e := by
    exact @helper_split_edge_339 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@phi) (@T) (@C) (@D) (@d) (@hparts)
  have hg3 : ∃ g3, g3 ∈ BoundaryColorEdges G phi X d.1 ∧ g3 ≠ D.f0 d ∧
      ∃ z3 ∈ Z, ∃ w3 ∉ X, G.ends g3 = s(z3,w3) := by
    exact @ScheideDefectiveCrossingSelection_hg3_279 V E inferInstance inferInstance
        inferInstance inferInstance G k e0 phi T C D d hu_unique a b c ha hb hc hab hac hbc
        split_edge
  rcases hg3 with ⟨g3, hg3B, hg3f0, z3, hz3, w3, hw3, hg3ends⟩
  have hg2ends' : G.ends g2 = s(x,u2) := by
    have hx' : x = C.blockVertex i 0 ∨ x = C.blockVertex i 1 := by simpa [U] using hu1U
    have hu' : u2 = C.blockVertex i 0 ∨ u2 = C.blockVertex i 1 := by simpa [U] using hu2U
    rcases hx' with rfl | rfl <;> rcases hu' with rfl | rfl <;> simp_all []
  refine ⟨x, u2, g2, g3, z3, w3, by simpa [i] using hpair, rfl, hu12, hu1U, hu2U,
    hxX, hu2X, hv0Z, hy0Z, halpha_gamma, halphadelta, hgammadelta,
    hg1ends, hg2color, hg2ends', hg3B, hg3f0, hz3, hw3, hg3ends, ?_, ?_, ?_⟩
  · intro h
    exact halphadelta (Option.some.inj ((h ▸ hg2color).symm.trans hg1))
  · intro h
    exact hbad (h ▸ hg3B)
  · intro h
    exact halphadelta (Option.some.inj (hg2color.symm.trans (h ▸ (Finset.mem_filter.mp hg3B).2)))

end GoldbergSeymour

end
