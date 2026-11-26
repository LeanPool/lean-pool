/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM09.Section11b
public import LeanPool.GraphMinor.GM09.EarUnion
public import LeanPool.GraphMinor.GM09.NestUncrossing

/-!
# Lawns

We fix a presentation of a simple rural neighborhood, with `Δ₀` a closed disc and with the drawing
meeting the boundary of `Δ₀` only in the vertices of `ΩBar₀`. Each short path with ends in `ΩBar₀`
is an
ear on `Δ₀`, and its disc is the disc `Δ(P)` of Graph Minors IX, page 67. We prove (11.1), that two
distinct lawns meet only in common ends. The paper omits this proof.
-/

@[expose] public section

namespace GraphMinor.GM09

open Set Function Topology Graph GraphMinor GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM11

universe u v

variable {α : Type u} {β : Type v}

/-! ## Drawings -/

section Drawing

variable {G P : Graph α β} (Γ : GraphDrawing G EuclideanPlane)

theorem graphDrawingEdgeSet_mem {e : β} (he : e ∈ E(G)) : graphDrawingEdgeSet Γ e ∈ Γ.drawing.E
  := by
  rw [graphDrawingEdgeSet_eq Γ he]
  exact (Γ.iso.edgeEquiv ⟨e, he⟩).2

theorem eq_of_mem_edgeSet {e f : β} (he : e ∈ E(G)) (hf : f ∈ E(G)) {x : EuclideanPlane}
    (hxe : x ∈ graphDrawingEdgeSet Γ e) (hxf : x ∈ graphDrawingEdgeSet Γ f) : e = f := by
  have h := Γ.drawing.edge_eq_of_mem (graphDrawingEdgeSet_mem Γ he) (graphDrawingEdgeSet_mem Γ hf)
    hxe hxf
  rw [graphDrawingEdgeSet_eq Γ he, graphDrawingEdgeSet_eq Γ hf] at h
  have h' := Γ.iso.edgeEquiv.injective (Subtype.ext h)
  exact congrArg Subtype.val h'

theorem edgeSet_disjoint_V {e : β} (he : e ∈ E(G)) {x : EuclideanPlane}
    (hx : x ∈ graphDrawingEdgeSet Γ e) : x ∉ Γ.drawing.V :=
  ((graphDrawingEdgeSet_mem Γ he).2.1 hx).2

theorem vertexPt_mem_V {v : α} (hv : v ∈ V(G)) : vertexPt Γ v ∈ Γ.drawing.V := by
  rw [← vertexEquiv_eq_vertexPt Γ ⟨v, hv⟩]
  exact (Γ.iso.vertexEquiv ⟨v, hv⟩).2

theorem exists_vertexPt_of_mem_V {x : EuclideanPlane} (hx : x ∈ Γ.drawing.V) :
    ∃ v ∈ V(G), x = vertexPt Γ v := by
  let w := Γ.iso.vertexEquiv.symm ⟨x, hx⟩
  refine ⟨w.1, w.2, ?_⟩
  rw [← vertexEquiv_eq_vertexPt Γ w]
  simp [w]

theorem mem_vertexSet_iff {v : α} (hv : v ∈ V(G)) {x : EuclideanPlane} :
    x ∈ graphDrawingVertexSet Γ v ↔ x = vertexPt Γ v := by
  rw [vertexSet_eq_vertexPt Γ hv]
  rfl

/-- A point of the drawing of a subgraph is a vertex of the subgraph or lies on one of its open
edges. -/
theorem mem_subgraphU_cases (hP : P ≤ G) {x : EuclideanPlane} (hx : x ∈ graphDrawingSubgraphU Γ P) :
    (∃ v ∈ V(P), x = vertexPt Γ v) ∨
      (∃ e ∈ E(P), x ∈ graphDrawingEdgeSet Γ e ∧ x ∉ Γ.drawing.V) := by
  rcases hx with hx | hx
  · obtain ⟨v, hv, hxv⟩ := mem_iUnion₂.mp hx
    exact Or.inl ⟨v, hv, (mem_vertexSet_iff Γ (hP.vertexSet_mono hv)).mp hxv⟩
  · obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp hx
    obtain ⟨a, b, hl⟩ := P.exists_isLink_of_mem_edgeSet he
    have hlG := hl.mono hP
    obtain ⟨hmem, hcap⟩ := closure_inter_V_of_isLink Γ hlG
    by_cases hxV : x ∈ Γ.drawing.V
    · left
      have h : x ∈ closure (graphDrawingEdgeSet Γ e) ∩ Γ.drawing.V := ⟨hxe, hxV⟩
      rw [hcap] at h
      rcases h with h | h
      · exact ⟨a, hl.left_mem, h⟩
      · exact ⟨b, hl.right_mem, h⟩
    · right
      refine ⟨e, he, ?_, hxV⟩
      rw [← Γ.drawing.closure_diff_V hmem]
      exact ⟨hxe, hxV⟩

theorem subgraphU_subset_U (hP : P ≤ G) : graphDrawingSubgraphU Γ P ⊆ Γ.drawing.U := by
  intro x hx
  rcases mem_subgraphU_cases Γ hP hx with ⟨v, hv, rfl⟩ | ⟨e, he, hxe, -⟩
  · exact vertexPt_mem_U Γ (hP.vertexSet_mono hv)
  · exact (graphDrawingEdgeSet_mem Γ (hP.edgeSet_mono he)).2.1 hxe |>.1

theorem vertexPt_mem_subgraphU {v : α} (hv : v ∈ V(P)) (hP : P ≤ G) :
    vertexPt Γ v ∈ graphDrawingSubgraphU Γ P :=
  graphDrawingVertexSet_subset_subgraphU_of_mem Γ hv
    ((mem_vertexSet_iff Γ (hP.vertexSet_mono hv)).mpr rfl)

theorem mem_vertexSet_of_vertexPt_mem (hP : P ≤ G) {v : α} (hv : v ∈ V(G))
    (hx : vertexPt Γ v ∈ graphDrawingSubgraphU Γ P) : v ∈ V(P) := by
  refine mem_vertexSet_of_graphDrawingVertexSet_subset_subgraphU Γ hP hv ?_
  rw [vertexSet_eq_vertexPt Γ hv, singleton_subset_iff]
  exact hx

/-- The closure of an edge with two different ends is a line between the images of its ends. -/
theorem isLine_closure_of_isLink {e : β} {u w : α} (hl : G.IsLink e u w) (huw : u ≠ w) :
    IsLineWithEnds (closure (graphDrawingEdgeSet Γ e)) (vertexPt Γ u) (vertexPt Γ w) := by
  obtain ⟨hmem, hcap⟩ := closure_inter_V_of_isLink Γ hl
  have hne : vertexPt Γ u ≠ vertexPt Γ w := fun h =>
    huw (vertexPt_injOn Γ hl.left_mem hl.right_mem h)
  rcases Γ.drawing.edge_cond _ hmem with ⟨p, q, -, hc, hL⟩ | ⟨p, hc, -⟩
  · rw [hc] at hcap
    have h₁ : vertexPt Γ u ∈ ({p, q} : Set EuclideanPlane) := hcap ▸ Or.inl rfl
    have h₂ : vertexPt Γ w ∈ ({p, q} : Set EuclideanPlane) := hcap ▸ Or.inr rfl
    rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
    · exact (hne (h₁.trans h₂.symm)).elim
    · rw [h₁, show vertexPt Γ w = q from h₂]
      exact hL
    · rw [h₂, show vertexPt Γ u = q from h₁]
      exact hL.symm
    · exact (hne ((show vertexPt Γ u = q from h₁).trans (show vertexPt Γ w = q from h₂).symm)).elim
  · rw [hc] at hcap
    have h₁ : vertexPt Γ u ∈ ({p} : Set EuclideanPlane) := hcap ▸ Or.inl rfl
    have h₂ : vertexPt Γ w ∈ ({p} : Set EuclideanPlane) := hcap ▸ Or.inr rfl
    exact (hne (h₁.trans h₂.symm)).elim

/-- The closures of two different edges at a vertex `m`, with different other ends, meet only in
the image of `m`. -/
theorem closure_inter_closure {e f : β} {m x y : α} (he : G.IsLink e m x) (hf : G.IsLink f m y)
    (hxy : x ≠ y) (hef : e ≠ f) :
    closure (graphDrawingEdgeSet Γ e) ∩ closure (graphDrawingEdgeSet Γ f) = {vertexPt Γ m} := by
  obtain ⟨hme, hce⟩ := closure_inter_V_of_isLink Γ he
  obtain ⟨hmf, hcf⟩ := closure_inter_V_of_isLink Γ hf
  ext w
  constructor
  · rintro ⟨h₁, h₂⟩
    by_cases hw : w ∈ Γ.drawing.V
    · have h₃ : w ∈ closure (graphDrawingEdgeSet Γ e) ∩ Γ.drawing.V := ⟨h₁, hw⟩
      have h₄ : w ∈ closure (graphDrawingEdgeSet Γ f) ∩ Γ.drawing.V := ⟨h₂, hw⟩
      rw [hce] at h₃
      rw [hcf] at h₄
      rcases h₃ with h₃ | h₃
      · exact h₃
      · rcases h₄ with h₄ | h₄
        · exact h₄
        · exfalso
          apply hxy
          exact vertexPt_injOn Γ he.right_mem hf.right_mem
            ((show w = vertexPt Γ x from h₃).symm.trans h₄)
    · exfalso
      apply hef
      have h₃ : w ∈ graphDrawingEdgeSet Γ e := Γ.drawing.closure_diff_V hme ▸ ⟨h₁, hw⟩
      have h₄ : w ∈ graphDrawingEdgeSet Γ f := Γ.drawing.closure_diff_V hmf ▸ ⟨h₂, hw⟩
      exact eq_of_mem_edgeSet Γ he.edge_mem hf.edge_mem h₃ h₄
  · rintro rfl
    have hm := (mem_vertexSet_iff Γ he.left_mem).mpr rfl
    exact ⟨graphDrawingVertexSet_subset_closure_edge Γ he hm,
      graphDrawingVertexSet_subset_closure_edge Γ hf hm⟩

theorem subgraphU_eq_of_one {e : β} {a b : α} (hV : V(P) = {a, b}) (hE : E(P) = {e})
    (hl : G.IsLink e a b) : graphDrawingSubgraphU Γ P = closure (graphDrawingEdgeSet Γ e) := by
  apply Subset.antisymm
  · rintro x (hx | hx)
    · obtain ⟨v, hv, hxv⟩ := mem_iUnion₂.mp hx
      rw [hV] at hv
      rcases hv with rfl | rfl
      · exact graphDrawingVertexSet_subset_closure_edge Γ hl hxv
      · exact graphDrawingVertexSet_subset_closure_edge Γ hl.symm hxv
    · obtain ⟨f, hf, hxf⟩ := mem_iUnion₂.mp hx
      rw [hE] at hf
      rw [show f = e from hf] at hxf
      exact hxf
  · intro x hx
    refine Or.inr (mem_iUnion₂.mpr ⟨e, ?_, hx⟩)
    rw [hE]
    rfl

theorem subgraphU_eq_of_two {e₁ e₂ : β} {a m b : α} (hV : V(P) = {a, m, b}) (hE : E(P) = {e₁, e₂})
    (hl₁ : G.IsLink e₁ m a) (hl₂ : G.IsLink e₂ m b) : graphDrawingSubgraphU Γ P =
      closure (graphDrawingEdgeSet Γ e₁) ∪ closure (graphDrawingEdgeSet Γ e₂) := by
  apply Subset.antisymm
  · rintro x (hx | hx)
    · obtain ⟨v, hv, hxv⟩ := mem_iUnion₂.mp hx
      rw [hV] at hv
      rcases hv with rfl | rfl | rfl
      · exact Or.inl (graphDrawingVertexSet_subset_closure_edge Γ hl₁.symm hxv)
      · exact Or.inl (graphDrawingVertexSet_subset_closure_edge Γ hl₁ hxv)
      · exact Or.inr (graphDrawingVertexSet_subset_closure_edge Γ hl₂.symm hxv)
    · obtain ⟨f, hf, hxf⟩ := mem_iUnion₂.mp hx
      rw [hE] at hf
      rcases hf with rfl | rfl
      · exact Or.inl hxf
      · exact Or.inr hxf
  · rintro x (hx | hx)
    · refine Or.inr (mem_iUnion₂.mpr ⟨e₁, ?_, hx⟩)
      rw [hE]
      exact Or.inl rfl
    · refine Or.inr (mem_iUnion₂.mpr ⟨e₂, ?_, hx⟩)
      rw [hE]
      exact Or.inr rfl

end Drawing

/-! ## Short paths -/

/-- A path with distinct ends in `ΩBar₀`, no internal vertex in `ΩBar₀`, and at most two edges:
properties
(i), (ii) and (iii) of a prominence, Graph Minors IX, page 67. -/
structure IsShortPath (N : Neighborhood α β) (P : Graph α β) (a b : α) : Prop where
  path : IsGraphPathWithEnds N.G P a b
  ne : a ≠ b
  left_mem : a ∈ N.Ω₀.bar
  right_mem : b ∈ N.Ω₀.bar
  disj : Disjoint (V(P) \ {a, b}) N.Ω₀.bar
  card : E(P).ncard ≤ 2

/-- A short path is a single edge between its ends, or it has a middle vertex outside `ΩBar₀`. -/
theorem IsShortPath.cases {N : Neighborhood α β} {P : Graph α β} {a b : α}
    (hS : IsShortPath N P a b) :
    (V(P) = {a, b} ∧ ∃ e, E(P) = {e} ∧ N.G.IsLink e a b) ∨
      ∃ m, m ∉ N.Ω₀.bar ∧ m ≠ a ∧ m ≠ b ∧ V(P) = {a, m, b} ∧ ∃ e₁ e₂, e₁ ≠ e₂ ∧
        E(P) = {e₁, e₂} ∧ N.G.IsLink e₁ m a ∧ N.G.IsLink e₂ m b := by
  classical
  have hfinE : E(P).Finite := N.finite_E.subset hS.path.le.edgeSet_mono
  by_cases hint : ∃ m, m ∈ V(P) ∧ m ≠ a ∧ m ≠ b
  · obtain ⟨m, hmV, hma, hmb⟩ := hint
    have hmi : m ∈ pathInternalVerts N.G P := by
      rw [hS.path.pathInternalVerts_eq]
      exact ⟨hmV, by rintro (h | h); exacts [hma h, hmb h]⟩
    obtain ⟨-, -, hV, e₁, he₁, e₂, he₂, hl₁, hl₂⟩ := path_of_internal_of_ncard_le_two hS.path
      hS.card hmi
    have hne : e₁ ≠ e₂ := by
      rintro rfl
      rcases hl₁.left_eq_or_eq hl₂ with h | h
      · exact hma h.symm
      · exact hS.ne h
    right
    have hmΩ : m ∉ N.Ω₀.bar := by
      intro h
      exact disjoint_left.mp hS.disj (by simpa only [hS.path.pathInternalVerts_eq] using hmi) h
    refine ⟨m, hmΩ, hma, hmb, hV, e₁, e₂, hne, ?_, (hl₁.mono hS.path.le).symm, hl₂.mono hS.path.le⟩
    have hsub : ({e₁, e₂} : Set β) ⊆ E(P) := pair_subset he₁ he₂
    refine (Set.eq_of_subset_of_ncard_le hsub ?_ hfinE).symm
    rw [ncard_pair hne]
    exact hS.card
  · left
    push Not at hint
    have hV : V(P) = {a, b} := by
      apply Subset.antisymm
      · intro m hm
        by_cases h : m = a
        · exact Or.inl h
        · exact Or.inr (hint m hm h)
      · exact pair_subset hS.path.left_mem hS.path.right_mem
    refine ⟨hV, ?_⟩
    obtain ⟨hle, W, hW, hVW, hEW⟩ := hS.path
    have hab := hS.ne
    cases W with
    | nil _ => exact (hab rfl).elim
    | @cons _ w₁ _ e₁ hl₁ W₁ =>
      cases W₁ with
      | nil _ =>
        refine ⟨e₁, ?_, hl₁.mono hle⟩
        rw [hEW]
        ext f
        simp [GraphWalk.edges_cons]
      | @cons _ w₂ _ e₂ hl₂ W₂ =>
        exfalso
        have hw₁ : w₁ ∈ V(P) := hl₂.left_mem
        have hnd : (a :: w₁ :: W₂.support).Nodup := hW
        have hb : b ∈ W₂.support := GraphWalk.end_mem_support W₂
        have hna : a ≠ w₁ := by
          intro h
          simp only [List.nodup_cons, List.mem_cons, not_or] at hnd
          exact hnd.1.1 h
        have hnb : w₁ ≠ b := by
          intro h
          simp only [List.nodup_cons, List.mem_cons, not_or] at hnd
          exact hnd.2.1 (h ▸ hb)
        exact hnb (hint w₁ hw₁ hna.symm)

/-- The presentations used in Section 11: `Δ₀` is a closed disc, the drawing meets the boundary of
`Δ₀` only in the vertices of `ΩBar₀`, and the graph is simple. -/
structure IsCleanPresentation {N : Neighborhood α β} (P : Presentation N) : Prop where
  disc₀ : IsClosedDisc P.Δ₀
  clean : P.Γ.drawing.U ∩ subBd P.Δ₀ ⊆ ⋃ v ∈ N.Ω₀.bar, graphDrawingVertexSet P.Γ v
  simple : IsSimpleGraph N.G

/-- A line in an `O`-arc has a complementary line in the arc with the same ends. -/
theorem exists_complement_line {X c : Set EuclideanPlane} {a b : EuclideanPlane} (hX : IsOArc X)
    (hc : IsLineWithEnds c a b) (hab : a ≠ b) (hs : c ⊆ X) :
    ∃ T, IsLineWithEnds T a b ∧ c ∩ T = {a, b} ∧ X = c ∪ T := by
  obtain ⟨φ⟩ := hX
  obtain ⟨I₁, I₂, -, -, hd, hu, -, -, hl₁, hl₂⟩ :=
    exists_open_arcs φ (hs hc.left_mem) (hs hc.right_mem) hab
  have hinter : (I₁ ∪ {a, b}) ∩ (I₂ ∪ {a, b}) = {a, b} := by
    ext x
    constructor
    · rintro ⟨h | h, h' | h'⟩
      · exact (disjoint_left.mp hd h h').elim
      · exact h'
      · exact h
      · exact h
    · intro h
      exact ⟨Or.inr h, Or.inr h⟩
  have hXu : (I₁ ∪ {a, b}) ∪ (I₂ ∪ {a, b}) = X := by
    rw [union_union_union_comm, hu, union_self, sdiff_union_of_subset
      (pair_subset (hs hc.left_mem) (hs hc.right_mem))]
  rcases line_eq_or_eq_of_subset_union hc hl₁ hl₂.symm hinter (hXu ▸ hs) with rfl | rfl
  · exact ⟨I₂ ∪ {a, b}, hl₂.symm, hinter, hXu.symm⟩
  · refine ⟨I₁ ∪ {a, b}, hl₁, ?_, ?_⟩
    · rw [inter_comm]
      exact hinter
    · rw [union_comm]
      exact hXu.symm

namespace IsCleanPresentation

variable {N : Neighborhood α β} {P_pres : Presentation N} (C : IsCleanPresentation P_pres)
include C

theorem exists_bar_of_mem {x : EuclideanPlane} (hx : x ∈ P_pres.Γ.drawing.U) (hx₀ : x ∈ P_pres.Δ₀) :
    ∃ v ∈ N.Ω₀.bar, x = vertexPt P_pres.Γ v := by
  have hb : x ∈ subBd P_pres.Δ₀ := by
    rw [subBd_eq_discBd_plane C.disc₀]
    by_contra hn
    have : x ∈ interior P_pres.Δ₀ := by
      rw [interior_eq_discInt_plane C.disc₀]
      exact ⟨hx₀, hn⟩
    exact (P_pres.U_subset hx).2 this
  obtain ⟨v, hv, hxv⟩ := mem_iUnion₂.mp (C.clean ⟨hx, hb⟩)
  exact ⟨v, hv, (mem_vertexSet_iff P_pres.Γ (N.bar₀_subset hv)).mp hxv⟩

omit C in
theorem vertexPt_mem_subBd {v : α} (hv : v ∈ N.Ω₀.bar) :
    vertexPt P_pres.Γ v ∈ subBd P_pres.Δ₀ := by
  have h := (P_pres.mem_bd_Δ₀_iff v (N.bar₀_subset hv)).mpr hv
  exact h ((mem_vertexSet_iff P_pres.Γ (N.bar₀_subset hv)).mpr rfl)

theorem vertexPt_mem_discBd {v : α} (hv : v ∈ N.Ω₀.bar) :
    vertexPt P_pres.Γ v ∈ discBd P_pres.Δ₀ := by
  rw [← subBd_eq_discBd_plane C.disc₀]
  exact vertexPt_mem_subBd hv

theorem vertexPt_not_mem {v : α} (hv : v ∈ V(N.G)) (hn : v ∉ N.Ω₀.bar) :
    vertexPt P_pres.Γ v ∉ P_pres.Δ₀ := by
  intro h
  obtain ⟨w, hw, hx⟩ := C.exists_bar_of_mem (vertexPt_mem_U P_pres.Γ hv) h
  rw [vertexPt_injOn P_pres.Γ hv (N.bar₀_subset hw) hx] at hn
  exact hn hw

/-- A short path is drawn as an ear on `Δ₀`. -/
theorem exists_ear {P : Graph α β} {a b : α} (hS : IsShortPath N P a b) :
    ∃ L A B, EarData P_pres.Δ₀ (graphDrawingSubgraphU P_pres.Γ P) L A B
      (vertexPt P_pres.Γ a) (vertexPt P_pres.Γ b) := by
  obtain ⟨hl, hne⟩ := isLineWithEnds_graphDrawingSubgraphU P_pres.Γ hS.path hS.ne
  rw [vertexEquiv_eq_vertexPt, vertexEquiv_eq_vertexPt] at hl hne
  refine exists_earData C.disc₀ hl hne (C.vertexPt_mem_discBd hS.left_mem)
    (C.vertexPt_mem_discBd hS.right_mem) ?_
  rintro x ⟨hx, hx₀⟩
  obtain ⟨v, hv, rfl⟩ := C.exists_bar_of_mem (subgraphU_subset_U P_pres.Γ hS.path.le hx) hx₀
  have hvP := mem_vertexSet_of_vertexPt_mem P_pres.Γ hS.path.le (N.bar₀_subset hv) hx
  by_contra hn
  refine disjoint_left.mp hS.disj ⟨hvP, ?_⟩ hv
  rintro (rfl | rfl)
  · exact hn (Or.inl rfl)
  · exact hn (Or.inr rfl)

/-- The disc of an ear is a path disc. -/
theorem isPathDisc_of_ear {P : Graph α β} {a b : α} (hS : IsShortPath N P a b)
    {L A B : Set EuclideanPlane} (E : EarData P_pres.Δ₀ (graphDrawingSubgraphU P_pres.Γ P) L A B
      (vertexPt P_pres.Γ a) (vertexPt P_pres.Γ b)) : IsPathDisc P_pres P L := by
  have hcΔ : graphDrawingSubgraphU P_pres.Γ P ⊆ P_pres.Δ := fun x hx =>
    (P_pres.U_subset (subgraphU_subset_U P_pres.Γ hS.path.le hx)).1
  refine ⟨⟨a, b, hS.path, hS.ne, hS.left_mem, hS.right_mem, hS.disj⟩, E.disc, ?_, ?_, ?_, ?_⟩
  · refine subset_of_discBd_subset P_pres.isClosedDisc_Δ E.disc ?_
    rw [E.bdL]
    exact union_subset (fun x hx => P_pres.Δ₀_subset_Δ (Surface.discBd_subset _
      (E.A_subset hx))) hcΔ
  · intro hsub
    obtain ⟨x, hx, hn⟩ := E.lineB.nonempty_sdiff
    have hxΔ : x ∈ P_pres.Δ₀ := Surface.discBd_subset _ (E.B_subset hx)
    exact hn (E.inter ▸ ⟨E.L_inter ▸ ⟨hsub hxΔ, hxΔ⟩, hx⟩)
  · rw [subBd_eq_discBd_plane E.disc, E.bdL]
    exact subset_union_right
  · rw [subBd_eq_discBd_plane E.disc, E.bdL, subBd_eq_discBd_plane C.disc₀, union_comm]
    exact union_subset_union_right _ E.A_subset

/-- The path disc of a short path is the disc of its ear, so it is unique. -/
theorem eq_of_isPathDisc {P : Graph α β} {a b : α}
    {L A B D : Set EuclideanPlane} (E : EarData P_pres.Δ₀ (graphDrawingSubgraphU P_pres.Γ P) L A B
      (vertexPt P_pres.Γ a) (vertexPt P_pres.Γ b)) (hD : IsPathDisc P_pres P D) : D = L := by
  obtain ⟨-, hd, -, hn, hs₁, hs₂⟩ := hD
  rw [subBd_eq_discBd_plane hd] at hs₁ hs₂
  rw [subBd_eq_discBd_plane C.disc₀] at hs₂
  obtain ⟨T, hT, hi, hX⟩ := exists_complement_line hd.isOArc_discBd E.line E.ne hs₁
  have hTs : T ⊆ discBd P_pres.Δ₀ := by
    intro t ht
    by_cases hm : t ∈ ({vertexPt P_pres.Γ a, vertexPt P_pres.Γ b} : Set EuclideanPlane)
    · rcases hm with rfl | rfl
      · exact E.left_mem
      · exact E.right_mem
    · have h₁ : t ∈ discBd D := hX ▸ Or.inr ht
      exact (hs₂ h₁).resolve_left fun h => hm (hi ▸ ⟨h, ht⟩)
  rcases E.eq_or_eq_of_discBd hd hT hTs hX with h | h
  · exact h
  · exact (hn (h ▸ subset_union_left)).elim

/-- The path of a prominence is short, and its lawn is the disc of its ear. -/
theorem exists_ear_of_prominence {P : Graph α β} {L : Set EuclideanPlane}
    (hL : IsProminenceWithDisc P_pres P L) :
    ∃ a b A B, IsShortPath N P a b ∧
      EarData P_pres.Δ₀ (graphDrawingSubgraphU P_pres.Γ P) L A B
        (vertexPt P_pres.Γ a) (vertexPt P_pres.Γ b) := by
  obtain ⟨a, b, hp, hab, ha, hb, hd⟩ := hL.1.1
  have hS : IsShortPath N P a b := ⟨hp, hab, ha, hb, hd, hL.2.1⟩
  obtain ⟨L', A, B, E⟩ := C.exists_ear hS
  have heq : L = L' := C.eq_of_isPathDisc E hL.1
  exact ⟨a, b, A, B, hS, heq ▸ E⟩

/-- The two-edge path at `m` with ends `x` and `y` is short, and it is an ear. -/
theorem exists_ear_two {e₁ e₂ : β} {m x y : α} (h₁ : N.G.IsLink e₁ m x) (h₂ : N.G.IsLink e₂ m y)
    (hx : x ∈ N.Ω₀.bar) (hy : y ∈ N.Ω₀.bar) (hxy : x ≠ y) (hm : m ∉ N.Ω₀.bar) :
    ∃ Q L A B, IsPathDisc P_pres Q L ∧ E(Q).ncard ≤ 2 ∧
      EarData P_pres.Δ₀
        (closure (graphDrawingEdgeSet P_pres.Γ e₁) ∪ closure (graphDrawingEdgeSet P_pres.Γ e₂))
        L A B (vertexPt P_pres.Γ x) (vertexPt P_pres.Γ y) := by
  have hmx : m ≠ x := fun h => hm (h ▸ hx)
  have hmy : m ≠ y := fun h => hm (h ▸ hy)
  obtain ⟨hp, hV, hV', hE, hc⟩ := isGraphPathWithEnds_two_edges h₁.symm h₂ hmx.symm hmy hxy
  have hS : IsShortPath N _ x y := ⟨hp, hxy, hx, hy, by
    rw [hV']
    exact disjoint_singleton_left.mpr hm, hc⟩
  obtain ⟨L, A, B, E⟩ := C.exists_ear hS
  refine ⟨_, L, A, B, C.isPathDisc_of_ear hS E, hc, ?_⟩
  rwa [subgraphU_eq_of_two P_pres.Γ hV hE h₁ h₂] at E

omit C in
/-- Two short paths are equal, or they have a common middle vertex, or their open parts are
disjoint. -/
theorem eq_or_middle_or_disjoint {P P' : Graph α β} {a b a' b' : α} (hS : IsShortPath N P a b)
    (hS' : IsShortPath N P' a' b') :
    P = P' ∨ (∃ m, m ∈ V(P) \ {a, b} ∧ m ∈ V(P') \ {a', b'}) ∨
      Disjoint (graphDrawingSubgraphU P_pres.Γ P \ {vertexPt P_pres.Γ a, vertexPt P_pres.Γ b})
        (graphDrawingSubgraphU P_pres.Γ P' \ {vertexPt P_pres.Γ a', vertexPt P_pres.Γ b'}) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hne, hnm, hnd⟩ := hcon
  obtain ⟨x, ⟨hx, hxn⟩, ⟨hx', hxn'⟩⟩ := not_disjoint_iff.mp hnd
  have hG := hS.path.le
  have hG' := hS'.path.le
  rcases mem_subgraphU_cases P_pres.Γ hG hx with ⟨v, hv, rfl⟩ | ⟨e, he, hxe, hxV⟩
  · refine hnm v ⟨hv, ?_⟩ ⟨mem_vertexSet_of_vertexPt_mem P_pres.Γ hG' (hG.vertexSet_mono hv) hx',
      ?_⟩
    · rintro (rfl | rfl)
      · exact hxn (Or.inl rfl)
      · exact hxn (Or.inr rfl)
    · rintro (rfl | rfl)
      · exact hxn' (Or.inl rfl)
      · exact hxn' (Or.inr rfl)
  · rcases mem_subgraphU_cases P_pres.Γ hG' hx' with ⟨v, hv, rfl⟩ | ⟨f, hf, hxf, -⟩
    · exact hxV (vertexPt_mem_V P_pres.Γ (hG'.vertexSet_mono hv))
    · have hef : e = f :=
        eq_of_mem_edgeSet P_pres.Γ (hG.edgeSet_mono he) (hG'.edgeSet_mono hf) hxe hxf
      subst hef
      -- An edge of a two-edge path has the middle vertex as an end, and this is not in `ΩBar₀`.
      have hmid : ∀ {Q : Graph α β} {c d m : α}, IsShortPath N Q c d → m ∉ N.Ω₀.bar →
          ∀ {g₁ g₂}, E(Q) = {g₁, g₂} → N.G.IsLink g₁ m c → N.G.IsLink g₂ m d → e ∈ E(Q) →
          ∃ r ∈ N.Ω₀.bar, N.G.IsLink e m r := by
        intro Q c d m hQ _ g₁ g₂ hE hl₁ hl₂ heQ
        rw [hE] at heQ
        rcases heQ with rfl | rfl
        · exact ⟨c, hQ.left_mem, hl₁⟩
        · exact ⟨d, hQ.right_mem, hl₂⟩
      rcases hS.cases with ⟨hV, e₀, hE, hl⟩ | ⟨m, hm, hma, hmb, hV, e₁, e₂, -, hE, hl₁, hl₂⟩
      · have hee : e = e₀ := by
          rw [hE] at he
          exact he
        subst hee
        rcases hS'.cases with ⟨hV', e₀', hE', hl'⟩ | ⟨m, hm, hma, hmb, hV', e₁, e₂, -, hE', hl₁,
          hl₂⟩
        · have hee : e = e₀' := by
            rw [hE'] at hf
            exact hf
          subst hee
          apply hne
          refine le_antisymm ((Compatible.of_le_le hG hG').le_iff.mpr ⟨?_, by rw [hE, hE']⟩)
            ((Compatible.of_le_le hG' hG).le_iff.mpr ⟨?_, by rw [hE, hE']⟩)
          · rw [hV, hV']
            rcases hl.eq_and_eq_or_eq_and_eq hl' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact Subset.rfl
            · exact (pair_comm _ _).subset
          · rw [hV, hV']
            rcases hl.eq_and_eq_or_eq_and_eq hl' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact Subset.rfl
            · exact (pair_comm _ _).subset
        · obtain ⟨r, -, hr⟩ := hmid hS' hm hE' hl₁ hl₂ hf
          rcases hr.left_eq_or_eq hl with h | h
          · exact hm (h ▸ hS.left_mem)
          · exact hm (h ▸ hS.right_mem)
      · obtain ⟨r, -, hr⟩ := hmid hS hm hE hl₁ hl₂ he
        have hmP : m ∈ V(P) \ {a, b} := ⟨by rw [hV]; exact Or.inr (Or.inl rfl), by
          rintro (h | h); exacts [hma h, hmb h]⟩
        rcases hS'.cases with ⟨hV', e₀', hE', hl'⟩ | ⟨m', hm', hma', hmb', hV', e₁', e₂', -, hE',
          hl₁', hl₂'⟩
        · have hee : e = e₀' := by
            rw [hE'] at hf
            exact hf
          subst hee
          rcases hr.left_eq_or_eq hl' with h | h
          · exact hm (h ▸ hS'.left_mem)
          · exact hm (h ▸ hS'.right_mem)
        · obtain ⟨r', hr'b, hr'⟩ := hmid hS' hm' hE' hl₁' hl₂' hf
          rcases hr.left_eq_or_eq hr' with h | h
          · subst h
            exact hnm m hmP ⟨by rw [hV']; exact Or.inr (Or.inl rfl), by
              rintro (h | h); exacts [hma' h, hmb' h]⟩
          · exact hm (h ▸ hr'b)

/-- Two prominences with a common middle vertex have the same lawn. -/
theorem lawn_eq_of_common_middle {P P' : Graph α β} {a b a' b' m : α} {L L' A B A' B' : Set
  EuclideanPlane}
    (hL : IsProminenceWithDisc P_pres P L) (hL' : IsProminenceWithDisc P_pres P' L')
    (hS : IsShortPath N P a b) (hS' : IsShortPath N P' a' b')
    (E : EarData P_pres.Δ₀ (graphDrawingSubgraphU P_pres.Γ P) L A B
      (vertexPt P_pres.Γ a) (vertexPt P_pres.Γ b))
    (E' : EarData P_pres.Δ₀ (graphDrawingSubgraphU P_pres.Γ P') L' A' B'
      (vertexPt P_pres.Γ a') (vertexPt P_pres.Γ b'))
    (hm : m ∈ V(P) \ {a, b}) (hm' : m ∈ V(P') \ {a', b'}) : L = L' := by
  have hmn : m ∉ N.Ω₀.bar := disjoint_left.mp hS.disj hm
  have hshape : ∀ {Q : Graph α β} {c d : α}, IsShortPath N Q c d → m ∈ V(Q) \ {c, d} →
      ∃ e₁ e₂, V(Q) = {c, m, d} ∧ E(Q) = {e₁, e₂} ∧ N.G.IsLink e₁ m c ∧ N.G.IsLink e₂ m d := by
    intro Q c d hQ hmQ
    rcases hQ.cases with ⟨hV, -⟩ | ⟨m₀, -, -, -, hV, e₁, e₂, -, hE, hl₁, hl₂⟩
    · exact (hmQ.2 (hV ▸ hmQ.1)).elim
    · have : m = m₀ := by
        have hm₀ := hmQ.1
        rw [hV] at hm₀
        rcases hm₀ with h | h | h
        · exact (hmQ.2 (Or.inl h)).elim
        · exact h
        · exact (hmQ.2 (Or.inr h)).elim
      subst this
      exact ⟨e₁, e₂, hV, hE, hl₁, hl₂⟩
  obtain ⟨e₁, e₂, hV, hE, hl₁, hl₂⟩ := hshape hS hm
  obtain ⟨e₁', e₂', hV', hE', hl₁', hl₂'⟩ := hshape hS' hm'
  have hmG : m ∈ V(N.G) := hl₁.left_mem
  have hU := subgraphU_eq_of_two P_pres.Γ hV hE hl₁ hl₂
  have hU' := subgraphU_eq_of_two P_pres.Γ hV' hE' hl₁' hl₂'
  have E₁ := E
  rw [hU] at E₁
  have hmΔ := C.vertexPt_not_mem hmG hmn
  have hline : ∀ {g : β} {z : α}, N.G.IsLink g m z → z ∈ N.Ω₀.bar →
      IsLineWithEnds (closure (graphDrawingEdgeSet P_pres.Γ g)) (vertexPt P_pres.Γ m)
        (vertexPt P_pres.Γ z) := fun h hz =>
    isLine_closure_of_isLink P_pres.Γ h fun e => hmn (e ▸ hz)
  have hcL : ∀ {x}, x ∈ graphDrawingSubgraphU P_pres.Γ P → x ∈ L := fun hx => E.c_subset_L hx
  have hab := hS.ne
  have hma : m ≠ a := fun h => hmn (h ▸ hS.left_mem)
  have hmb : m ≠ b := fun h => hmn (h ▸ hS.right_mem)
  have hee : e₁ ≠ e₂ := by
    rintro rfl
    exact hab (hl₁.right_unique hl₂)
  have key : ∀ {g : β} {z : α}, N.G.IsLink g m z → z ∈ N.Ω₀.bar →
      closure (graphDrawingEdgeSet P_pres.Γ g) \ {vertexPt P_pres.Γ m, vertexPt P_pres.Γ z} ⊆ L
        := by
    intro g z hg hz
    by_cases hza : z = a
    · subst hza
      have : g = e₁ := C.simple.2 g hg.edge_mem e₁ hl₁.edge_mem _ _ hg hl₁
      intro x hx
      exact hcL (hU ▸ Or.inl (this ▸ hx.1))
    by_cases hzb : z = b
    · subst hzb
      have : g = e₂ := C.simple.2 g hg.edge_mem e₂ hl₂.edge_mem _ _ hg hl₂
      intro x hx
      exact hcL (hU ▸ Or.inr (this ▸ hx.1))
    obtain ⟨Q₂, L₂, _, _, hQ₂, hc₂, E₂⟩ :=
      C.exists_ear_two hl₁ hg hS.left_mem hz (Ne.symm hza) hmn
    obtain ⟨Q₃, L₃, _, _, hQ₃, hc₃, E₃⟩ :=
      C.exists_ear_two hl₂ hg hS.right_mem hz (Ne.symm hzb) hmn
    have hmz : m ≠ z := fun h => hmn (h ▸ hz)
    have he₁g : e₁ ≠ g := by
      rintro rfl
      exact hza (hl₁.right_unique hg).symm
    have he₂g : e₂ ≠ g := by
      rintro rfl
      exact hzb (hl₂.right_unique hg).symm
    rcases E₁.third_leg E₂ E₃ (hline hl₁ hS.left_mem) (hline hl₂ hS.right_mem) (hline hg hz) hmΔ
      (fun h => hza (vertexPt_injOn P_pres.Γ hg.right_mem hl₁.right_mem h))
      (fun h => hzb (vertexPt_injOn P_pres.Γ hg.right_mem hl₂.right_mem h))
      (closure_inter_closure P_pres.Γ hl₁ hl₂ hab hee)
      (closure_inter_closure P_pres.Γ hl₁ hg (Ne.symm hza) he₁g)
      (closure_inter_closure P_pres.Γ hl₂ hg (Ne.symm hzb) he₂g) with h | ⟨h, hne⟩ | ⟨h,
        hne⟩
    · exact h
    · exact (hne (hL.2.2 Q₂ L₂ hQ₂ hc₂ h).symm).elim
    · exact (hne (hL.2.2 Q₃ L₃ hQ₃ hc₃ h).symm).elim
  have hsub : graphDrawingSubgraphU P_pres.Γ P' \ {vertexPt P_pres.Γ a', vertexPt P_pres.Γ b'} ⊆ L
    := by
    rintro x ⟨hx, hn⟩
    by_cases hxm : x = vertexPt P_pres.Γ m
    · exact hcL (hxm ▸ vertexPt_mem_subgraphU P_pres.Γ hm.1 hS.path.le)
    rw [hU'] at hx
    rcases hx with hx | hx
    · exact key hl₁' hS'.left_mem ⟨hx, by
        rintro (h | h)
        · exact hxm h
        · exact hn (Or.inl h)⟩
    · exact key hl₂' hS'.right_mem ⟨hx, by
        rintro (h | h)
        · exact hxm h
        · exact hn (Or.inr h)⟩
  exact hL'.2.2 P L hL.1 hL.2.1 (E.subset_of_open_subset E' hsub)

/-- **Graph Minors IX, (11.1)**: "If $L, L'$ are distinct lawns then every element of $L \cap L'$ is
the image under $\Gamma$
of a common end of the two corresponding prominences." -/
theorem lawn_inter_subset {P P' : Graph α β} {L L' : Set EuclideanPlane}
    (hL : IsProminenceWithDisc P_pres P L) (hL' : IsProminenceWithDisc P_pres P' L') (hne : L ≠ L')
    {x : EuclideanPlane} (hx : x ∈ L ∩ L') :
    ∃ v ∈ pathEnds N.G P ∩ pathEnds N.G P', x ∈ graphDrawingVertexSet P_pres.Γ v := by
  obtain ⟨a, b, A, B, hS, E⟩ := C.exists_ear_of_prominence hL
  obtain ⟨a', b', A', B', hS', E'⟩ := C.exists_ear_of_prominence hL'
  rcases eq_or_middle_or_disjoint hS hS' with rfl | ⟨m, hm, hm'⟩ | hd
  · exact (hne (C.eq_of_isPathDisc E hL'.1).symm).elim
  · exact (hne (C.lawn_eq_of_common_middle hL hL' hS hS' E E' hm hm')).elim
  rcases E.nested_or_inter E' hd with h | h | h
  · exact (hne (hL'.2.2 P L hL.1 hL.2.1 h)).elim
  · exact (hne (hL.2.2 P' L' hL'.1 hL'.2.1 h).symm).elim
  obtain ⟨h₁, h₂⟩ := h hx
  have hends : ∀ {Q : Graph α β} {c d : α}, IsShortPath N Q c d →
      c ∈ pathEnds N.G Q ∧ d ∈ pathEnds N.G Q := fun hQ => by
    rw [hQ.path.pathEnds_eq]
    exact ⟨Or.inl rfl, Or.inr rfl⟩
  have hv : ∀ {c c' : α}, c ∈ N.Ω₀.bar → c' ∈ N.Ω₀.bar → x = vertexPt P_pres.Γ c →
      x = vertexPt P_pres.Γ c' → c = c' := fun hc hc' h h' =>
    vertexPt_injOn P_pres.Γ (N.bar₀_subset hc) (N.bar₀_subset hc') (h.symm.trans h')
  rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
  · have := hv hS.left_mem hS'.left_mem h₁ h₂
    subst this
    exact ⟨a, ⟨(hends hS).1, (hends hS').1⟩, (mem_vertexSet_iff _ (N.bar₀_subset hS.left_mem)).mpr
      h₁⟩
  · have := hv hS.left_mem hS'.right_mem h₁ h₂
    subst this
    exact ⟨a, ⟨(hends hS).1, (hends hS').2⟩, (mem_vertexSet_iff _ (N.bar₀_subset hS.left_mem)).mpr
      h₁⟩
  · have := hv hS.right_mem hS'.left_mem h₁ h₂
    subst this
    exact ⟨b, ⟨(hends hS).2, (hends hS').1⟩, (mem_vertexSet_iff _ (N.bar₀_subset hS.right_mem)).mpr
      h₁⟩
  · have := hv hS.right_mem hS'.right_mem h₁ h₂
    subst this
    exact ⟨b, ⟨(hends hS).2, (hends hS').2⟩, (mem_vertexSet_iff _ (N.bar₀_subset hS.right_mem)).mpr
      h₁⟩

omit C in
/-- A connected piece of `U(Γ)` off the vertices has connected drawing. -/
theorem isPreconnected_edgeSet {e : β} (he : e ∈ E(N.G)) :
    IsPreconnected (graphDrawingEdgeSet P_pres.Γ e) :=
  (graphDrawingEdgeSet_mem P_pres.Γ he).2.2.1.isConnected.isPreconnected

omit C in
/-- A graph has only finitely many subgraphs. -/
theorem finite_subgraphs : {Q : Graph α β | Q ≤ N.G}.Finite := by
  classical
  let f : Graph α β → Set α × Set β := fun Q => (V(Q), E(Q))
  have hinj : InjOn f {Q : Graph α β | Q ≤ N.G} := by
    intro Q hQ Q' hQ' h
    have h₁ : V(Q) = V(Q') := congrArg Prod.fst h
    have h₂ : E(Q) = E(Q') := congrArg Prod.snd h
    exact le_antisymm ((Compatible.of_le_le hQ hQ').le_iff.mpr ⟨h₁.subset, h₂.subset⟩)
      ((Compatible.of_le_le hQ' hQ).le_iff.mpr ⟨h₁.symm.subset, h₂.symm.subset⟩)
  refine Set.Finite.of_finite_image ?_ hinj
  refine ((N.finite_V.finite_subsets).prod (N.finite_E.finite_subsets)).subset ?_
  rintro _ ⟨Q, hQ, rfl⟩
  exact ⟨hQ.vertexSet_mono, hQ.edgeSet_mono⟩

/-- There are only finitely many path discs of short paths. -/
theorem finite_pathDiscs :
    {D : Set EuclideanPlane | ∃ Q, IsPathDisc P_pres Q D ∧ E(Q).ncard ≤ 2}.Finite := by
  have hfin := finite_subgraphs (N := N)
  have hsub : {D : Set EuclideanPlane | ∃ Q, IsPathDisc P_pres Q D ∧ E(Q).ncard ≤ 2} ⊆
      ⋃ Q ∈ {Q : Graph α β | Q ≤ N.G}, {D | IsPathDisc P_pres Q D ∧ E(Q).ncard ≤ 2} := by
    rintro D ⟨Q, hD, hc⟩
    obtain ⟨a, b, hp, -⟩ := hD.1
    exact mem_iUnion₂.mpr ⟨Q, hp.le, hD, hc⟩
  refine (hfin.biUnion fun Q _ => ?_).subset hsub
  refine Set.Subsingleton.finite ?_
  rintro D ⟨hD, hc⟩ D' ⟨hD', -⟩
  obtain ⟨a, b, hp, hab, ha, hb, hd⟩ := hD.1
  have hS : IsShortPath N Q a b := ⟨hp, hab, ha, hb, hd, hc⟩
  obtain ⟨L, A, B, E⟩ := C.exists_ear hS
  rw [C.eq_of_isPathDisc E hD, C.eq_of_isPathDisc E hD']

/-- Every path disc of a short path lies in a lawn. -/
theorem exists_lawn_of_pathDisc {Q : Graph α β} {D : Set EuclideanPlane}
    (hD : IsPathDisc P_pres Q D) (hc : E(Q).ncard ≤ 2) :
    ∃ L, IsLawn P_pres L ∧ D ⊆ L := by
  obtain ⟨L, hDL, hmax⟩ := C.finite_pathDiscs.exists_le_maximal (a := D) ⟨Q, hD, hc⟩
  obtain ⟨Q', hQ', hc'⟩ := hmax.1
  refine ⟨L, ⟨Q', hQ', hc', fun P' L' hL' hc'' hle => ?_⟩, hDL⟩
  exact le_antisymm (hmax.2 ⟨P', hL', hc''⟩ hle) hle

theorem exists_lawn_of_short_path {Q : Graph α β} {a b : α} (hS : IsShortPath N Q a b) :
    ∃ D L, IsPathDisc P_pres Q D ∧ IsLawn P_pres L ∧ D ⊆ L := by
  obtain ⟨D, A, B, E⟩ := C.exists_ear hS
  have hD := C.isPathDisc_of_ear hS E
  obtain ⟨L, hL, hDL⟩ := C.exists_lawn_of_pathDisc hD hS.card
  exact ⟨D, L, hD, hL, hDL⟩

/-- The lawns form a family of ears, indexed by themselves. -/
theorem exists_earFamily :
    ∃ (Q : {L // IsLawn P_pres L} → Graph α β) (a b : {L // IsLawn P_pres L} → α)
      (A B : {L // IsLawn P_pres L} → Set EuclideanPlane),
      EarFamily P_pres.Δ₀ univ (fun i => graphDrawingSubgraphU P_pres.Γ (Q i)) (fun i => i.1) A B
        (fun i => vertexPt P_pres.Γ (a i)) (fun i => vertexPt P_pres.Γ (b i)) ∧
      ∀ i, IsProminenceWithDisc P_pres (Q i) i.1 ∧ IsShortPath N (Q i) (a i) (b i) := by
  have h : ∀ i : {L // IsLawn P_pres L}, ∃ (Q : Graph α β) (a b : α)
      (A B : Set EuclideanPlane), IsProminenceWithDisc P_pres Q i.1 ∧ IsShortPath N Q a b ∧
      EarData P_pres.Δ₀ (graphDrawingSubgraphU P_pres.Γ Q) i.1 A B
        (vertexPt P_pres.Γ a) (vertexPt P_pres.Γ b) := by
    intro i
    obtain ⟨Q, hQ⟩ := i.2
    obtain ⟨a, b, A, B, hS, E⟩ := C.exists_ear_of_prominence hQ
    exact ⟨Q, a, b, A, B, hQ, hS, E⟩
  choose Q a b A B h₁ h₂ h₃ using h
  have hfin : (univ : Set {L // IsLawn P_pres L}).Finite := by
    have hf : {L | IsLawn P_pres L}.Finite := C.finite_pathDiscs.subset fun L hL => by
      obtain ⟨Q', hQ'⟩ := hL
      exact ⟨Q', hQ'.1, hQ'.2.1⟩
    have : Finite {L // IsLawn P_pres L} := hf.to_subtype
    exact toFinite _
  refine ⟨Q, a, b, A, B, ⟨hfin, fun i _ => h₃ i, ?_⟩, fun i => ⟨h₁ i, h₂ i⟩⟩
  intro i _ j _ hij x hx
  have hne : i.1 ≠ j.1 := fun h => hij (Subtype.ext h)
  obtain ⟨v, ⟨hv, hv'⟩, hxv⟩ := C.lawn_inter_subset (h₁ i) (h₁ j) hne hx
  rw [(h₂ i).path.pathEnds_eq] at hv
  rw [(h₂ j).path.pathEnds_eq] at hv'
  have hG : v ∈ V(N.G) := by
    rcases hv with rfl | rfl
    · exact N.bar₀_subset (h₂ i).left_mem
    · exact N.bar₀_subset (h₂ i).right_mem
  have hxe := (mem_vertexSet_iff P_pres.Γ hG).mp hxv
  refine ⟨?_, ?_⟩
  · rcases hv with rfl | rfl
    · exact Or.inl hxe
    · exact Or.inr hxe
  · rcases hv' with h | h
    · rw [h] at hxe
      exact Or.inl hxe
    · rw [h] at hxe
      exact Or.inr hxe

omit C in
theorem wallDisc_eq :
    wallDisc P_pres = P_pres.Δ₀ ∪ ⋃ i ∈ (univ : Set {L // IsLawn P_pres L}), i.1 := by
  unfold wallDisc
  congr 1
  ext x
  simp only [mem_iUnion, mem_ofPred_eq, exists_prop, mem_univ, true_and, Subtype.exists]

theorem isClosedDisc_wallDisc : IsClosedDisc (wallDisc P_pres) := by
  obtain ⟨Q, a, b, A, B, F, -⟩ := C.exists_earFamily
  rw [wallDisc_eq]
  exact (F.isClosedDisc_union C.disc₀).1

theorem wall_eq : wall P_pres = discBd (wallDisc P_pres) :=
  subBd_eq_discBd_plane C.isClosedDisc_wallDisc

/-- A prominence is drawn in the wall, and its lawn meets the wall only in that drawing. -/
theorem prominence_U_subset_wall {Q : Graph α β} {L : Set EuclideanPlane}
    (hL : IsProminenceWithDisc P_pres Q L) :
    graphDrawingSubgraphU P_pres.Γ Q ⊆ wall P_pres ∧
      L ∩ wall P_pres ⊆ graphDrawingSubgraphU P_pres.Γ Q := by
  obtain ⟨Q₀, a, b, A, B, F, hF⟩ := C.exists_earFamily
  obtain ⟨a', b', A', B', -, E⟩ := C.exists_ear_of_prominence hL
  let i : {L // IsLawn P_pres L} := ⟨L, Q, hL⟩
  have hc : graphDrawingSubgraphU P_pres.Γ Q = graphDrawingSubgraphU P_pres.Γ (Q₀ i) :=
    E.c_eq (F.ear i (mem_univ i))
  rw [C.wall_eq, wallDisc_eq, hc]
  exact ⟨F.c_subset_discBd C.disc₀ (mem_univ i), F.L_inter_discBd_subset C.disc₀ (mem_univ i)⟩

/-- The wall lies in the boundary of `Δ₀` together with the images of the prominences. -/
theorem wall_subset :
    wall P_pres ⊆ subBd P_pres.Δ₀ ∪
      ⋃ (P : Graph α β) (_ : IsProminence P_pres P), graphDrawingSubgraphU P_pres.Γ P := by
  obtain ⟨Q₀, a, b, A, B, F, hF⟩ := C.exists_earFamily
  rw [C.wall_eq, wallDisc_eq, subBd_eq_discBd_plane C.disc₀]
  refine (F.isClosedDisc_union C.disc₀).2.trans (union_subset_union_right _ ?_)
  refine iUnion₂_subset fun i _ => ?_
  exact subset_biUnion_of_mem (u := fun P => graphDrawingSubgraphU P_pres.Γ P)
    (s := {P | IsProminence P_pres P}) ⟨i.1, (hF i).1⟩ |>.trans (by
      intro x hx
      obtain ⟨P, hP, hxP⟩ := mem_iUnion₂.mp hx
      exact mem_iUnion₂.mpr ⟨P, hP, hxP⟩)

/-- An open edge misses `Δ₀`. -/
theorem edgeSet_disjoint {e : β} (he : e ∈ E(N.G)) {x : EuclideanPlane}
    (hx : x ∈ graphDrawingEdgeSet P_pres.Γ e) : x ∉ P_pres.Δ₀ := by
  intro h₀
  have hxU := (graphDrawingEdgeSet_mem P_pres.Γ he).2.1 hx |>.1
  obtain ⟨v, hv, rfl⟩ := C.exists_bar_of_mem hxU h₀
  exact edgeSet_disjoint_V P_pres.Γ he hx (vertexPt_mem_V P_pres.Γ (N.bar₀_subset hv))

omit C in
/-- An open edge that is not in a path `Q` misses the drawing of `Q`. -/
theorem edgeSet_disjoint_subgraphU {e : β} {Q : Graph α β} (he : e ∈ E(N.G)) (hQ : Q ≤ N.G)
    (heQ : e ∉ E(Q)) {x : EuclideanPlane} (hx : x ∈ graphDrawingEdgeSet P_pres.Γ e) :
    x ∉ graphDrawingSubgraphU P_pres.Γ Q := by
  intro hxQ
  rcases mem_subgraphU_cases P_pres.Γ hQ hxQ with ⟨v, hv, rfl⟩ | ⟨f, hf, hxf, -⟩
  · exact edgeSet_disjoint_V P_pres.Γ he hx (vertexPt_mem_V P_pres.Γ (hQ.vertexSet_mono hv))
  · rw [eq_of_mem_edgeSet P_pres.Γ he (hQ.edgeSet_mono hf) hx hxf] at heQ
    exact heQ hf

/-- Every edge is internal, external, or a wall edge. -/
theorem edge_trichotomy {e : β} (he : e ∈ E(N.G)) :
    IsInternalEdge P_pres e ∨ IsExternalEdge P_pres e ∨ IsWallEdge P_pres e := by
  by_cases hex : ∃ Q, IsProminence P_pres Q ∧ e ∈ E(Q)
  · obtain ⟨Q, ⟨L, hL⟩, heQ⟩ := hex
    right
    right
    exact ⟨he, (graphDrawingEdgeSet_subset_subgraphU_of_mem P_pres.Γ heQ).trans
      (C.prominence_U_subset_wall hL).1⟩
  push Not at hex
  have hd : Disjoint (graphDrawingEdgeSet P_pres.Γ e) (discBd (wallDisc P_pres)) := by
    rw [disjoint_left, ← C.wall_eq]
    intro x hx hxw
    rcases C.wall_subset hxw with h | h
    · refine C.edgeSet_disjoint he hx (subBd_subset_of_isClosed C.disc₀.isCompact.isClosed h)
    · obtain ⟨Q, hQ, hxQ⟩ := mem_iUnion₂.mp h
      obtain ⟨L, hL⟩ := id hQ
      obtain ⟨a, b, hp, -⟩ := hL.1.1
      exact edgeSet_disjoint_subgraphU he hp.le (hex Q hQ) hx hxQ
  rcases subset_interior_or_compl C.isClosedDisc_wallDisc (isPreconnected_edgeSet he) hd with h | h
  · exact Or.inl ⟨he, h⟩
  · refine Or.inr (Or.inl ⟨he, fun x hx => ⟨?_, h hx⟩⟩)
    exact (P_pres.U_subset ((graphDrawingEdgeSet_mem P_pres.Γ he).2.1 hx).1).1

/-- An internal edge at the middle vertex of a prominence is drawn in its lawn. -/
theorem internal_edge_subset_lawn_of_middle {Q : Graph α β} {L : Set EuclideanPlane} {m : α} {e : β}
    (hL : IsProminenceWithDisc P_pres Q L) (hm : m ∈ pathInternalVerts N.G Q)
    (hi : IsInternalEdge P_pres e) (hinc : N.G.Inc e m) :
    graphDrawingEdgeSet P_pres.Γ e ⊆ L := by
  obtain ⟨Q₀, a, b, A, B, F, hF⟩ := C.exists_earFamily
  obtain ⟨a', b', A', B', hS, E⟩ := C.exists_ear_of_prominence hL
  by_cases heQ : e ∈ E(Q)
  · exact (graphDrawingEdgeSet_subset_subgraphU_of_mem P_pres.Γ heQ).trans
      (fun x hx => E.c_subset_L hx)
  let i : {L // IsLawn P_pres L} := ⟨L, Q, hL⟩
  have hc : graphDrawingSubgraphU P_pres.Γ Q = graphDrawingSubgraphU P_pres.Γ (Q₀ i) :=
    E.c_eq (F.ear i (mem_univ i))
  have he := hi.1
  obtain ⟨w, hlink⟩ := hinc
  have hmV : m ∈ V(Q) := by
    rw [hS.path.pathInternalVerts_eq] at hm
    exact hm.1
  have hmn : m ∉ ({a', b'} : Set α) := by
    rw [hS.path.pathInternalVerts_eq] at hm
    exact hm.2
  have hmbar : m ∉ N.Ω₀.bar := disjoint_left.mp hS.disj ⟨hmV, hmn⟩
  have hmG : m ∈ V(N.G) := hlink.left_mem
  have hmΔ := C.vertexPt_not_mem hmG hmbar
  have hmo : vertexPt P_pres.Γ m ∉ P_pres.Δ₀ ∪ ⋃ j ∈ (univ : Set {L // IsLawn P_pres L}) \ {i}, j.1
    := by
    rintro (h | h)
    · exact hmΔ h
    · obtain ⟨j, hj, hmj⟩ := mem_iUnion₂.mp h
      have hne : i ≠ j := fun h' => hj.2 h'.symm
      have hx := (F.inter i (mem_univ i) j hj.1 hne ⟨E.c_subset_L
        (vertexPt_mem_subgraphU P_pres.Γ hmV hS.path.le), hmj⟩).1
      have hmaP : vertexPt P_pres.Γ m ∈ P_pres.Δ₀ := by
        have hEi := F.ear i (mem_univ i)
        rcases hx with hx | hx
        · exact (Surface.discBd_subset _ hEi.left_mem : _ ∈ P_pres.Δ₀) |> (hx ▸ ·)
        · exact (Surface.discBd_subset _ hEi.right_mem : _ ∈ P_pres.Δ₀) |> (hx ▸ ·)
      exact hmΔ hmaP
  obtain ⟨N', hN', hmN, hsub⟩ := F.exists_nhds_subset C.disc₀ (mem_univ i) hmo
  have hd : Disjoint (graphDrawingEdgeSet P_pres.Γ e) (discBd L) := by
    rw [disjoint_left, E.bdL]
    rintro x hx (h | h)
    · exact C.edgeSet_disjoint he hx (Surface.discBd_subset _ (E.A_subset h))
    · exact edgeSet_disjoint_subgraphU he hS.path.le heQ hx h
  rcases subset_interior_or_compl E.disc (isPreconnected_edgeSet he) hd with h | h
  · exact h.trans interior_subset
  · exfalso
    have hcl : vertexPt P_pres.Γ m ∈ closure (graphDrawingEdgeSet P_pres.Γ e) :=
      graphDrawingVertexSet_subset_closure_edge P_pres.Γ hlink
        ((mem_vertexSet_iff P_pres.Γ hmG).mpr rfl)
    obtain ⟨y, hyN, hye⟩ := mem_closure_iff.mp hcl N' hN' hmN
    have hyW : y ∈ P_pres.Δ₀ ∪ ⋃ j ∈ (univ : Set {L // IsLawn P_pres L}), j.1 := by
      rw [← wallDisc_eq]
      exact interior_subset (hi.2 hye)
    exact h hye (hsub ⟨hyN, hyW⟩)

/-- **The first half of pages 67 and 68 of Graph Minors IX**: a clean presentation of a simple rural
neighborhood is regular. -/
theorem isRegularPresentation : IsRegularPresentation P_pres where
  lawn_inter_subset_common_ends := fun _ _ _ _ hL hL' hne _ hx => C.lawn_inter_subset hL hL' hne hx
  exists_lawn_of_short_path := fun _ _ _ hP hab ha hb hd hc =>
    C.exists_lawn_of_short_path ⟨hP, hab, ha, hb, hd, hc⟩
  isClosedDisc_wallDisc := C.isClosedDisc_wallDisc
  edge_trichotomy := fun _ he => C.edge_trichotomy he
  prominence_U_subset_wall := fun _ _ hL => C.prominence_U_subset_wall hL
  wall_subset := C.wall_subset
  internal_edge_subset_lawn_of_middle := fun _ _ _ _ hL hm hi hinc =>
    C.internal_edge_subset_lawn_of_middle hL hm hi hinc

end IsCleanPresentation

end GraphMinor.GM09
