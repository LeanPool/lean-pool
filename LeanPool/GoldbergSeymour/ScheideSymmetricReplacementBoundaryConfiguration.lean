/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.DefectiveColors
public import LeanPool.GoldbergSeymour.ScheideDefectiveSetup
public import LeanPool.GoldbergSeymour.ScheideDefectiveSwitchEffect
public import LeanPool.GoldbergSeymour.ScheideGlobalMaximumOrder
public import LeanPool.GoldbergSeymour.ScheideReplacementData
public import LeanPool.GoldbergSeymour.ScheideReplacementMaximum
public import LeanPool.GoldbergSeymour.ScheideReplacementPairFixed
public import LeanPool.GoldbergSeymour.ScheideStructuralConfiguration
public import LeanPool.GoldbergSeymour.ScheideStructuralExitsInBase
public import LeanPool.GoldbergSeymour.TreeSequence

/-!
# Scheide Symmetric Replacement Boundary Configuration

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

open scoped Sym2

private theorem helper_hbaseZ_165.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
      [DecidableEq V] [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (C : ScheideReducedConfiguration G k e0 phi T)
      (D : ScheideDefectiveSetup G k e0 phi T C)
      (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))),
    let Z : Finset V :=
      TreeSequenceVertexSet T \
        {C.blockVertex (D.gammaIndex d) (0 : Fin (2 : ℕ)),
          C.blockVertex (D.gammaIndex d) (1 : Fin (2 : ℕ))};
    ∀ (q : Fin C.p),
    C.y q ∈ Z := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D d Z q
  simp only [Z, Finset.mem_sdiff]
  constructor
  · simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ,
      true_and]
    exact ⟨⟨q.val, by rw [C.length_eq]; omega⟩,
      C.base_vertex_position q⟩
  · simp only [Finset.mem_insert, Finset.mem_singleton]
    intro he
    rcases he with he | he
    · have hi := T.vertex_injective
        ((C.base_vertex_position q).trans
          (he.trans (C.block_vertex_position (D.gammaIndex d) 0).symm))
      have hv := congrArg Fin.val hi
      have hc := C.length_eq
      have hq := q.isLt
      have hp := C.p_ge_two
      have hg := (D.gammaIndex d).isLt
      change q.val = C.p + 2 * (D.gammaIndex d).val at hv
      omega
    · have hi := T.vertex_injective
        ((C.base_vertex_position q).trans
          (he.trans (C.block_vertex_position (D.gammaIndex d) 1).symm))
      have hv := congrArg Fin.val hi
      have hc := C.length_eq
      have hq := q.isLt
      have hp := C.p_ge_two
      have hg := (D.gammaIndex d).isLt
      change q.val = C.p + 2 * (D.gammaIndex d).val + 1 at hv
      omega

private theorem helper_branch_348.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
      [DecidableEq V] [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (C : ScheideReducedConfiguration G k e0 phi T)
      (D : ScheideDefectiveSetup G k e0 phi T C)
      (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T)))
      (R : ScheideReplacementData G k e0 phi T C D d),
    let gamma : Fin k := C.gamma (D.gammaIndex d);
    TreeSequenceVertexSet R.replacementTree =
        TreeSequenceVertexSet T \
            {C.blockVertex (D.gammaIndex d) (0 : Fin (2 : ℕ)),
              C.blockVertex (D.gammaIndex d) (1 : Fin (2 : ℕ))} ∪
          { R.u1, R.u2 } →
    phi (C.blockEdge (D.gammaIndex d) (0 : Fin (2 : ℕ))) = some (C.gamma (D.gammaIndex d)) →
    phi (C.blockEdge (D.gammaIndex d) (1 : Fin (2 : ℕ))) = some (C.gamma (D.gammaIndex d)) →
    (∃ (q : Fin C.p),
        G.ends (C.blockEdge (D.gammaIndex d) (0 : Fin (2 : ℕ))) =
          s(C.y q, C.blockVertex (D.gammaIndex d) (0 : Fin (2 : ℕ)))) →
    (∃ (q : Fin C.p),
        G.ends (C.blockEdge (D.gammaIndex d) (1 : Fin (2 : ℕ))) =
          s(C.y q, C.blockVertex (D.gammaIndex d) (1 : Fin (2 : ℕ)))) →
    (∀ (f : E),
        (∃ v ∈ TreeSequenceVertexSet T, Incident G v f) →
          ¬f = D.f0 d →
            TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d)) (↑d : Fin k)
                (Sum.inl (D.v0 d)) f =
              phi f) →
    IsProperEdgeColoring G phi →
    (∀ f ∈ BoundaryEdges G (TreeSequenceVertexSet T), phi f = some gamma → False) →
    ∀ (f : E),
    (TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d)) (↑d : Fin k) (Sum.inl (D.v0 d))
            f =
          some (C.gamma (D.gammaIndex d)) ∧
        ∃
          v ∈
            TreeSequenceVertexSet T \
              {C.blockVertex (D.gammaIndex d) (0 : Fin (2 : ℕ)),
                C.blockVertex (D.gammaIndex d) (1 : Fin (2 : ℕ))},
          ∃ w ∉ TreeSequenceVertexSet R.replacementTree, G.ends f = s(v, w)) →
    f = D.f0 d ∨
      f = C.blockEdge (D.gammaIndex d) (0 : Fin (2 : ℕ)) ∨
        f = C.blockEdge (D.gammaIndex d) (1 : Fin (2 : ℕ)) := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D d R gamma hrep hblock0 hblock1 hf1ends hf2ends hfix hproper0
      hnoext f
  rintro ⟨hfc, v, hv, w, hw, he⟩
  by_cases hff : f = D.f0 d
  · exact Or.inl hff
  have hfo : phi f = some gamma := (hfix f
    ⟨v, (Finset.mem_sdiff.mp hv).1, by
      change v ∈ G.ends f
      rw [he]
      exact Sym2.mem_mk_left _ _⟩ hff).symm.trans hfc
  have hwT : w ∈ TreeSequenceVertexSet T := by
    by_contra hwt
    apply hnoext f
    · simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ,
        true_and]
      exact ⟨v, (Finset.mem_sdiff.mp hv).1, w, hwt, he⟩
    · exact hfo
  have hwr : w ∉ TreeSequenceVertexSet T \
      {C.blockVertex (D.gammaIndex d) 0,
        C.blockVertex (D.gammaIndex d) 1} := by
    intro hwr
    apply hw
    rw [hrep]
    exact Finset.mem_union.mpr (Or.inl hwr)
  have hwb : w = C.blockVertex (D.gammaIndex d) 0 ∨
      w = C.blockVertex (D.gammaIndex d) 1 := by
    by_contra hn
    apply hwr
    exact Finset.mem_sdiff.mpr ⟨hwT, by simpa using hn⟩
  rcases hwb with rfl | rfl
  · apply Or.inr (Or.inl ?_)
    by_contra hne
    have hadj : AdjacentEdges G f (C.blockEdge (D.gammaIndex d) 0) := by
      refine ⟨C.blockVertex (D.gammaIndex d) 0, ?_, ?_⟩
      · change C.blockVertex (D.gammaIndex d) 0 ∈ G.ends f
        rw [he]
        exact Sym2.mem_mk_right _ _
      · obtain ⟨q, hq⟩ := hf1ends
        change C.blockVertex (D.gammaIndex d) 0 ∈
          G.ends (C.blockEdge (D.gammaIndex d) 0)
        rw [hq]
        exact Sym2.mem_mk_right _ _
    exact (hproper0 hne hadj hfo) hblock0
  · apply Or.inr (Or.inr ?_)
    by_contra hne
    have hadj : AdjacentEdges G f (C.blockEdge (D.gammaIndex d) 1) := by
      refine ⟨C.blockVertex (D.gammaIndex d) 1, ?_, ?_⟩
      · change C.blockVertex (D.gammaIndex d) 1 ∈ G.ends f
        rw [he]
        exact Sym2.mem_mk_right _ _
      · obtain ⟨q, hq⟩ := hf2ends
        change C.blockVertex (D.gammaIndex d) 1 ∈
          G.ends (C.blockEdge (D.gammaIndex d) 1)
        rw [hq]
        exact Sym2.mem_mk_right _ _
    exact (hproper0 hne hadj hfo) hblock1

private theorem helper_hne0_225.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
      [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
      (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (C : ScheideReducedConfiguration G k e0 phi T)
      (D : ScheideDefectiveSetup G k e0 phi T C)
      (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))),
    G.ends (D.f0 d) = s(D.v0 d, D.u0 d) →
    (∃ (q : Fin C.p),
        G.ends (C.blockEdge (D.gammaIndex d) (0 : Fin (2 : ℕ))) =
          s(C.y q, C.blockVertex (D.gammaIndex d) (0 : Fin (2 : ℕ)))) →
    D.f0 d ≠ C.blockEdge (D.gammaIndex d) (0 : Fin (2 : ℕ)) := by
  classical
  intro V E _ _ _ G k e0 phi T C D d hf0ends hf1ends he
  have hu : D.u0 d ∈ G.ends (C.blockEdge (D.gammaIndex d) 0) := by
    rw [← he, hf0ends]
    exact Sym2.mem_mk_right _ _
  obtain ⟨q, hq⟩ := hf1ends
  rw [hq] at hu
  have hcases : D.u0 d = C.y q ∨
      D.u0 d = C.blockVertex (D.gammaIndex d) 0 := by
    simpa using hu
  rcases hcases with hcase | hcase
  · apply D.u0_outside d
    rw [hcase]
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ,
      true_and]
    exact ⟨⟨q.val, by rw [C.length_eq]; omega⟩,
      C.base_vertex_position q⟩
  · exact (D.u0_outside d) (hcase ▸ by
      simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ,
        true_and]
      exact ⟨⟨C.p + 2 * (D.gammaIndex d).val, by
        rw [C.length_eq]; omega⟩,
        C.block_vertex_position (D.gammaIndex d) (0 : Fin 2)⟩)

private theorem helper_hne1_248.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
      [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
      (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (C : ScheideReducedConfiguration G k e0 phi T)
      (D : ScheideDefectiveSetup G k e0 phi T C)
      (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))),
    G.ends (D.f0 d) = s(D.v0 d, D.u0 d) →
    (∃ (q : Fin C.p),
        G.ends (C.blockEdge (D.gammaIndex d) (1 : Fin (2 : ℕ))) =
          s(C.y q, C.blockVertex (D.gammaIndex d) (1 : Fin (2 : ℕ)))) →
    D.f0 d ≠ C.blockEdge (D.gammaIndex d) (1 : Fin (2 : ℕ)) := by
  classical
  intro V E _ _ _ G k e0 phi T C D d hf0ends hf2ends he
  have hu : D.u0 d ∈ G.ends (C.blockEdge (D.gammaIndex d) 1) := by
    rw [← he, hf0ends]
    exact Sym2.mem_mk_right _ _
  obtain ⟨q, hq⟩ := hf2ends
  rw [hq] at hu
  have hcases : D.u0 d = C.y q ∨
      D.u0 d = C.blockVertex (D.gammaIndex d) 1 := by
    simpa using hu
  rcases hcases with hcase | hcase
  · exact (D.u0_outside d) (hcase ▸ by
      simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ,
        true_and]
      exact ⟨⟨q.val, by rw [C.length_eq]; omega⟩,
        C.base_vertex_position q⟩)
  · exact (D.u0_outside d) (hcase ▸ by
      simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ,
        true_and]
      exact ⟨⟨C.p + 2 * (D.gammaIndex d).val + 1, by
        rw [C.length_eq]; omega⟩,
        C.block_vertex_position (D.gammaIndex d) (1 : Fin 2)⟩)

private theorem helper_hne12_270.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
      [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
      (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (C : ScheideReducedConfiguration G k e0 phi T)
      (D : ScheideDefectiveSetup G k e0 phi T C)
      (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))),
    C.blockEdge (D.gammaIndex d) (0 : Fin (2 : ℕ)) ≠
      C.blockEdge (D.gammaIndex d) (1 : Fin (2 : ℕ)) := by
  classical
  intro V E _ _ _ G k e0 phi T C D d he
  have hpos := C.block_edge_position (D.gammaIndex d) 0
  have hpos2 := C.block_edge_position (D.gammaIndex d) 1
  have hi : (⟨C.p - 1 + 2 * (D.gammaIndex d).val, by
      have hc := C.length_eq
      have hp := C.p_ge_two
      have hq := (D.gammaIndex d).isLt
      omega⟩ : Fin T.length) =
      ⟨C.p - 1 + 2 * (D.gammaIndex d).val + 1, by
        have hc := C.length_eq
        have hp := C.p_ge_two
        have hq := (D.gammaIndex d).isLt
        omega⟩ := by
    apply T.edge_injective
    exact hpos.trans (he.trans hpos2.symm)
  have hv := congrArg Fin.val hi
  have hzero : (0 : Nat) < 1 := by omega
  change C.p - 1 + 2 * (D.gammaIndex d).val =
    C.p - 1 + 2 * (D.gammaIndex d).val + 1 at hv
  omega

private theorem helper_hu0_416.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
      [DecidableEq V] [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (C : ScheideReducedConfiguration G k e0 phi T)
      (D : ScheideDefectiveSetup G k e0 phi T C)
      (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T)))
      (R : ScheideReplacementData G k e0 phi T C D d),
    let Xd : Finset V := TreeSequenceVertexSet R.replacementTree;
    TreeSequenceVertexSet R.replacementTree =
        TreeSequenceVertexSet T \
            {C.blockVertex (D.gammaIndex d) (0 : Fin (2 : ℕ)),
              C.blockVertex (D.gammaIndex d) (1 : Fin (2 : ℕ))} ∪
          { R.u1, R.u2 } →
    IsProperEdgeColoring G phi →
    D.u0 d ∉ Xd := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D d R Xd hrep hproper0
  change D.u0 d ∉ TreeSequenceVertexSet R.replacementTree
  rw [hrep]
  intro hu
  rcases Finset.mem_union.mp hu with hr | hu
  · exact D.u0_outside d (Finset.mem_sdiff.mp hr).1
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with hu | hu
    · have hadj : AdjacentEdges G (D.f0 d) R.f1 := by
        refine ⟨D.u0 d, ?_, ?_⟩
        · change D.u0 d ∈ G.ends (D.f0 d)
          rw [D.f0_ends]
          exact Sym2.mem_mk_right _ _
        · have hi : R.u1 ∈ G.ends R.f1 := by
            rw [R.f1_ends]
            exact Sym2.mem_mk_right _ _
          exact hu ▸ hi
      have hbad := hproper0 R.f0_ne_f1 hadj (D.f0_color d)
      exact hbad R.f1_color
    · have hadj : AdjacentEdges G (D.f0 d) R.f2 := by
        refine ⟨D.u0 d, ?_, ?_⟩
        · change D.u0 d ∈ G.ends (D.f0 d)
          rw [D.f0_ends]
          exact Sym2.mem_mk_right _ _
        · have hi : R.u2 ∈ G.ends R.f2 := by
            rw [R.f2_ends]
            exact Sym2.mem_mk_right _ _
          exact hu ▸ hi
      have hbad := hproper0 R.f0_ne_f2 hadj (D.f0_color d)
      exact hbad R.f2_color

private theorem helper_branch_458.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
      [DecidableEq V] [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (C : ScheideReducedConfiguration G k e0 phi T)
      (D : ScheideDefectiveSetup G k e0 phi T C)
      (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T)))
      (R : ScheideReplacementData G k e0 phi T C D d),
    let gamma : Fin k := C.gamma (D.gammaIndex d);
    let phiD : PartialEdgeColoring E k :=
      TwoColorComponentSwap G phi gamma (↑d : Fin k) (Sum.inl (D.v0 d));
    let Xd : Finset V := TreeSequenceVertexSet R.replacementTree;
    let Z : Finset V :=
      TreeSequenceVertexSet T \
        {C.blockVertex (D.gammaIndex d) (0 : Fin (2 : ℕ)),
          C.blockVertex (D.gammaIndex d) (1 : Fin (2 : ℕ))};
    TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d)) (↑d : Fin k) (Sum.inl (D.v0 d))
          (D.f0 d) =
        some (C.gamma (D.gammaIndex d)) →
    TreeSequenceVertexSet R.replacementTree =
        TreeSequenceVertexSet T \
            {C.blockVertex (D.gammaIndex d) (0 : Fin (2 : ℕ)),
              C.blockVertex (D.gammaIndex d) (1 : Fin (2 : ℕ))} ∪
          { R.u1, R.u2 } →
    (∃ (q : Fin C.p),
        G.ends (C.blockEdge (D.gammaIndex d) (0 : Fin (2 : ℕ))) =
          s(C.y q, C.blockVertex (D.gammaIndex d) (0 : Fin (2 : ℕ)))) →
    (∃ (q : Fin C.p),
        G.ends (C.blockEdge (D.gammaIndex d) (1 : Fin (2 : ℕ))) =
          s(C.y q, C.blockVertex (D.gammaIndex d) (1 : Fin (2 : ℕ)))) →
    (∀ (j : Fin (2 : ℕ)), C.blockVertex (D.gammaIndex d) j ∈ TreeSequenceVertexSet T) →
    (∀ (q : Fin C.p), C.y q ∈ Z) →
    phiD (C.blockEdge (D.gammaIndex d) (0 : Fin (2 : ℕ))) = some gamma →
    phiD (C.blockEdge (D.gammaIndex d) (1 : Fin (2 : ℕ))) = some gamma →
    D.v0 d ∈ Z →
    D.u0 d ∉ Xd →
    ∀ (f : E),
    f = D.f0 d ∨
        f = C.blockEdge (D.gammaIndex d) (0 : Fin (2 : ℕ)) ∨
          f = C.blockEdge (D.gammaIndex d) (1 : Fin (2 : ℕ)) →
    TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d)) (↑d : Fin k) (Sum.inl (D.v0 d))
          f =
        some (C.gamma (D.gammaIndex d)) ∧
      ∃
        v ∈
          TreeSequenceVertexSet T \
            {C.blockVertex (D.gammaIndex d) (0 : Fin (2 : ℕ)),
              C.blockVertex (D.gammaIndex d) (1 : Fin (2 : ℕ))},
        ∃ w ∉ TreeSequenceVertexSet R.replacementTree, G.ends f = s(v, w) := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D d R gamma phiD Xd Z hf0c hrep hf1ends hf2ends htreeBlock
      hbaseZ hblockc0 hblockc1 hv0Z hu0 f hf
  rcases hf with rfl | rfl | rfl
  · exact ⟨hf0c, D.v0 d, hv0Z, D.u0 d, hu0, D.f0_ends d⟩
  · exact ⟨hblockc0, by
      obtain ⟨q, hq⟩ := hf1ends
      refine ⟨C.y q, ?_, C.blockVertex (D.gammaIndex d) 0, ?_, hq⟩
      · exact hbaseZ q
      · rw [hrep]
        intro hb
        rcases Finset.mem_union.mp hb with hr | hu
        · exact (Finset.mem_sdiff.mp hr).2 (by simp)
        · simp only [Finset.mem_insert, Finset.mem_singleton] at hu
          rcases hu with hu | hu
          · exact R.u1_outside (hu ▸ htreeBlock 0)
          · exact R.u2_outside (hu ▸ htreeBlock 0)⟩
  · exact ⟨hblockc1, by
      obtain ⟨q, hq⟩ := hf2ends
      refine ⟨C.y q, ?_, C.blockVertex (D.gammaIndex d) 1, ?_, hq⟩
      · exact hbaseZ q
      · rw [hrep]
        intro hb
        rcases Finset.mem_union.mp hb with hr | hu
        · exact (Finset.mem_sdiff.mp hr).2 (by simp)
        · simp only [Finset.mem_insert, Finset.mem_singleton] at hu
          rcases hu with hu | hu
          · exact R.u1_outside (hu ▸ htreeBlock 1)
          · exact R.u2_outside (hu ▸ htreeBlock 1)⟩

theorem ScheideSymmetricReplacementBoundaryConfiguration {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (C : ScheideReducedConfiguration G k e0 phi T)
    (D : ScheideDefectiveSetup G k e0 phi T C)
    (d : {delta // delta ∈ DefectiveColors G phi (TreeSequenceVertexSet T)})
    (R : ScheideReplacementData G k e0 phi T C D d) :
    let gamma := C.gamma (D.gammaIndex d)
    let phiD := TwoColorComponentSwap G phi gamma d.1 (Sum.inl (D.v0 d))
    let Xd := TreeSequenceVertexSet R.replacementTree
    let Z :=
      TreeSequenceVertexSet T \
        {C.blockVertex (D.gammaIndex d) 0, C.blockVertex (D.gammaIndex d) 1}
    gamma ∈ DefectiveColors G phiD Xd ∧
      phiD (D.f0 d) = some gamma ∧
        phiD (C.blockEdge (D.gammaIndex d) 0) = some gamma ∧
          phiD (C.blockEdge (D.gammaIndex d) 1) = some gamma ∧
            D.f0 d ≠ C.blockEdge (D.gammaIndex d) 0 ∧
              D.f0 d ≠ C.blockEdge (D.gammaIndex d) 1 ∧
                C.blockEdge (D.gammaIndex d) 0 ≠ C.blockEdge (D.gammaIndex d) 1 ∧
                  ∀ f : E,
                    (phiD f = some gamma ∧ ∃ v ∈ Z, ∃ w ∉ Xd, G.ends f = s(v, w)) ↔
                      f = D.f0 d ∨
                        f = C.blockEdge (D.gammaIndex d) 0 ∨
                          f = C.blockEdge (D.gammaIndex d) 1 := by
  classical
  let gamma := C.gamma (D.gammaIndex d)
  let phiD := TwoColorComponentSwap G phi gamma d.1 (Sum.inl (D.v0 d))
  let Xd := TreeSequenceVertexSet R.replacementTree
  let Z := TreeSequenceVertexSet T \
    {C.blockVertex (D.gammaIndex d) 0,
      C.blockVertex (D.gammaIndex d) 1}
  have hmax := ScheideReplacementMaximum G k e0 phi T C D d R
  dsimp [gamma, phiD, Xd, Z] at hmax ⊢
  have hproper : IsProperEdgeColoring G
      (TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d)) d.1
        (Sum.inl (D.v0 d))) := hmax.1
  have horder := ScheideGlobalMaximumOrder G k e0 phi T C.globally_maximum
  have hclosed : ColoredVertexSetClosed G phi (TreeSequenceVertexSet T) :=
    horder.2.2.2.2
  have hsw := ScheideDefectiveSwitchEffect G k e0 phi T C D d
  dsimp at hsw
  have hf0c := hsw.2.2.1
  have hrep := R.replacement_vertices
  have hblock0 := C.block_color (D.gammaIndex d) 0
  have hblock1 := C.block_color (D.gammaIndex d) 1
  have hf0ends := D.f0_ends d
  have hf1ends := C.block_attaches_to_base (D.gammaIndex d) 0
  have hf2ends := C.block_attaches_to_base (D.gammaIndex d) 1
  have hfix := hsw.2.2.2.2.1
  have hne0 := @helper_hne0_225 V E inferInstance inferInstance inferInstance G k e0 phi T C D d
      hf0ends hf1ends
  have hne1 := @helper_hne1_248 V E inferInstance inferInstance inferInstance G k e0 phi T C D d
      hf0ends hf2ends
  have hne12 := @helper_hne12_270 V E inferInstance inferInstance inferInstance G k e0 phi T C D d
  have htreeY : ∀ q : Fin C.p, C.y q ∈ TreeSequenceVertexSet T := by
    intro q
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ,
      true_and]
    exact ⟨⟨q.val, by rw [C.length_eq]; omega⟩,
      C.base_vertex_position q⟩
  have htreeBlock : ∀ j : Fin 2,
      C.blockVertex (D.gammaIndex d) j ∈ TreeSequenceVertexSet T := by
    intro j
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ,
      true_and]
    exact ⟨⟨C.p + 2 * (D.gammaIndex d).val + j.val, by
      rw [C.length_eq]; omega⟩, C.block_vertex_position _ _⟩
  have hbaseZ := @helper_hbaseZ_165 V E inferInstance inferInstance inferInstance inferInstance G k
      e0 phi T C D d
  have hblockmem0 : C.blockEdge (D.gammaIndex d) 0 ∈
      BoundaryEdges G Xd := by
    simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and]
    obtain ⟨q, hq⟩ := hf1ends
    have hy : C.y q ∈ Xd := by
      change C.y q ∈ TreeSequenceVertexSet R.replacementTree
      rw [hrep]
      exact Finset.mem_union.mpr (Or.inl (Finset.mem_sdiff.mpr
        ⟨htreeY q, (Finset.mem_sdiff.mp (hbaseZ q)).2⟩))
    refine ⟨C.y q, hy, C.blockVertex (D.gammaIndex d) 0, ?_, hq⟩
    change C.blockVertex (D.gammaIndex d) 0 ∉
      TreeSequenceVertexSet R.replacementTree
    rw [hrep]
    intro hb
    rcases Finset.mem_union.mp hb with hr | hu
    · exact (Finset.mem_sdiff.mp hr).2 (by simp)
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with hu | hu
      · exact R.u1_outside (hu ▸ htreeBlock 0)
      · exact R.u2_outside (hu ▸ htreeBlock 0)
  have hblockmem1 : C.blockEdge (D.gammaIndex d) 1 ∈
      BoundaryEdges G Xd := by
    simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and]
    obtain ⟨q, hq⟩ := hf2ends
    have hy : C.y q ∈ Xd := by
      change C.y q ∈ TreeSequenceVertexSet R.replacementTree
      rw [hrep]
      exact Finset.mem_union.mpr (Or.inl (Finset.mem_sdiff.mpr
        ⟨htreeY q, (Finset.mem_sdiff.mp (hbaseZ q)).2⟩))
    refine ⟨C.y q, hy, C.blockVertex (D.gammaIndex d) 1, ?_, hq⟩
    change C.blockVertex (D.gammaIndex d) 1 ∉
      TreeSequenceVertexSet R.replacementTree
    rw [hrep]
    intro hb
    rcases Finset.mem_union.mp hb with hr | hu
    · exact (Finset.mem_sdiff.mp hr).2 (by simp)
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with hu | hu
      · exact R.u1_outside (hu ▸ htreeBlock 1)
      · exact R.u2_outside (hu ▸ htreeBlock 1)
  have hblockc0 : phiD (C.blockEdge (D.gammaIndex d) 0) = some gamma := by
    obtain ⟨q, hq⟩ := hf1ends
    have hi : ∃ v ∈ TreeSequenceVertexSet T,
        Incident G v (C.blockEdge (D.gammaIndex d) 0) := by
      refine ⟨C.y q, ?_, ?_⟩
      · simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ,
          true_and]
        exact ⟨⟨q.val, by rw [C.length_eq]; omega⟩,
          C.base_vertex_position q⟩
      · change C.y q ∈ G.ends (C.blockEdge (D.gammaIndex d) 0)
        rw [hq]
        exact Sym2.mem_mk_left _ _
    simpa [gamma] using (hfix _ hi hne0.symm).trans hblock0
  have hblockc1 : phiD (C.blockEdge (D.gammaIndex d) 1) = some gamma := by
    obtain ⟨q, hq⟩ := hf2ends
    have hi : ∃ v ∈ TreeSequenceVertexSet T,
        Incident G v (C.blockEdge (D.gammaIndex d) 1) := by
      refine ⟨C.y q, ?_, ?_⟩
      · simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ,
          true_and]
        exact ⟨⟨q.val, by rw [C.length_eq]; omega⟩,
          C.base_vertex_position q⟩
      · change C.y q ∈ G.ends (C.blockEdge (D.gammaIndex d) 1)
        rw [hq]
        exact Sym2.mem_mk_left _ _
    simpa [gamma] using (hfix _ hi hne1.symm).trans hblock1
  have hb0 : C.blockEdge (D.gammaIndex d) 0 ∈
      BoundaryColorEdges G phiD Xd gamma := by
    exact Finset.mem_filter.mpr ⟨hblockmem0, hblockc0⟩
  have hb1 : C.blockEdge (D.gammaIndex d) 1 ∈
      BoundaryColorEdges G phiD Xd gamma := by
    exact Finset.mem_filter.mpr ⟨hblockmem1, hblockc1⟩
  have hcard : 2 ≤ (BoundaryColorEdges G phiD Xd gamma).card := by
    have hs : ({C.blockEdge (D.gammaIndex d) 0,
        C.blockEdge (D.gammaIndex d) 1} : Finset E) ⊆
        BoundaryColorEdges G phiD Xd gamma := by
      intro e he
      simp only [Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with rfl | rfl
      · exact hb0
      · exact hb1
    have hc := Finset.card_le_card hs
    simpa [hne12] using hc
  refine ⟨?_, hf0c, hblockc0, hblockc1, hne0, hne1, hne12, ?_⟩
  · simp only [DefectiveColors, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hcard
  have hproper0 : IsProperEdgeColoring G phi :=
    C.globally_maximum.1.2.2.2.1
  have helem : ColoredVertexSetElementary G phi
      (TreeSequenceVertexSet T) := horder.2.2.2.1
  have hnoext : ∀ f : E, f ∈ BoundaryEdges G (TreeSequenceVertexSet T) →
      phi f = some gamma → False := by
    intro f hf hc
    obtain ⟨v, hv, w, hw, he⟩ := by
      simpa [BoundaryEdges] using hf
    have hv0T : D.v0 d ∈ TreeSequenceVertexSet T := by
      have hx := ScheideStructuralExitsInBase G k e0 phi T C
        (D.v0_is_exit d)
      rcases Finset.mem_image.mp hx with ⟨q, hq, hv⟩
      exact hv ▸ htreeY q
    have hnot : gamma ∉ MissingColors G phi (D.v0 d) :=
      hclosed hf hv0T hc
    exact hnot (D.gamma_missing_at_v0 d)
  have hv0Z : D.v0 d ∈ Z := by
    have hx := ScheideStructuralExitsInBase G k e0 phi T C
      (D.v0_is_exit d)
    rcases Finset.mem_image.mp hx with ⟨q, hq, hv⟩
    rw [← hv]
    exact hbaseZ q
  have hu0 := @helper_hu0_416 V E inferInstance inferInstance inferInstance inferInstance G k e0 phi
      T C D d R hrep hproper0
  have hf0mem : D.f0 d ∈ BoundaryEdges G Xd := by
    simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and]
    have hv0Xd : D.v0 d ∈ Xd := by
      change D.v0 d ∈ TreeSequenceVertexSet R.replacementTree
      rw [hrep]
      exact Finset.mem_union.mpr (Or.inl hv0Z)
    refine ⟨D.v0 d, hv0Xd, D.u0 d, hu0, D.f0_ends d⟩
  have hf0col : D.f0 d ∈ BoundaryColorEdges G phiD Xd gamma := by
    exact Finset.mem_filter.mpr ⟨hf0mem, hf0c⟩
  intro f
  constructor
  · exact @helper_branch_348 V E inferInstance inferInstance inferInstance inferInstance G k e0
      phi T C D d R hrep hblock0 hblock1 hf1ends hf2ends hfix hproper0 hnoext f
  · exact @helper_branch_458 V E inferInstance inferInstance inferInstance inferInstance G k e0
      phi T C D d R hf0c hrep hf1ends hf2ends htreeBlock hbaseZ hblockc0 hblockc1 hv0Z hu0 f
end GoldbergSeymour

end
