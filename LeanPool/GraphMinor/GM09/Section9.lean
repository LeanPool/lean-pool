/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM09.Defs
public import LeanPool.GraphMinor.GM09.Basic
public import LeanPool.GraphMinor.Surface.Crossing
import LeanPool.GraphMinor.GM09.DiscDrawing
import LeanPool.GraphMinor.GM09.Section2d
import LeanPool.GraphMinor.GM09.Section3a
import LeanPool.GraphMinor.GM09.Section3b
import LeanPool.GraphMinor.GM09.Section3c
import LeanPool.GraphMinor.GM09.Section5a
public import LeanPool.GraphMinor.GM09.Restriction
import LeanPool.GraphMinor.GM09.Section11b
import LeanPool.GraphMinor.GM06.Section3Dual

/-!
# Graph Minors IX, Section 9: Removing a Rural Neighborhood

This file formalizes Section 9 (pages 62–63) of N. Robertson and P. D. Seymour,
*Graph Minors. IX. Disjoint crossed paths*, J. Combin. Theory Ser. B **49** (1990) 40–77.
-/

@[expose] public section

namespace GraphMinor.GM09

open Set Function Topology Metric Graph GraphMinor GraphMinor.Surface GraphMinor.GM06

universe u v w

variable {α : Type u} {β : Type v}

/-! ## Topological and Disc-Crossing Lemmas for Rural Presentations -/

theorem inter_subBd_subset_subBd {S : Type w} [TopologicalSpace S] {D Δ : Set S}
    (hDΔ : D ⊆ Δ) : D ∩ subBd Δ ⊆ subBd D :=
  fun _ ⟨hxD, _, hx_compl⟩ =>
    ⟨subset_closure hxD, closure_mono (sdiff_subset_sdiff_right hDΔ) hx_compl⟩

theorem subBd_eq_diff_interior_of_isClosed {S : Type w} [TopologicalSpace S] {D : Set S}
    (hD : IsClosed D) : subBd D = D \ interior D := by
  ext x
  simp only [subBd, mem_inter_iff, mem_sdiff, hD.closure_eq]
  rw [← compl_eq_univ_sdiff, closure_compl, mem_compl_iff]

/-- For any closed disc `Δ` in `EuclideanPlane`, its manifold boundary `discBd Δ` equals its
topological boundary `subBd Δ`. -/
theorem discBd_eq_subBd {Δ : Set EuclideanPlane} (hΔ : IsClosedDisc Δ) :
    discBd Δ = subBd Δ :=
  (subBd_eq_discBd_plane hΔ).symm

theorem inter_subBd_nonempty_of_isConnected {S : Type w} [TopologicalSpace S] {K D : Set S}
    (hK : IsConnected K) (hKD : (K ∩ D).Nonempty) (hKc : (K ∩ Dᶜ).Nonempty) :
    (K ∩ subBd D).Nonempty := by
  by_contra h_empty
  rw [not_nonempty_iff_eq_empty] at h_empty
  have hK_sub : K ⊆ interior D ∪ (closure D)ᶜ := by
    intro x hxK
    by_cases hx_cl : x ∈ closure D
    · by_cases hx_int : x ∈ interior D
      · exact Or.inl hx_int
      · exfalso
        have hx_bd : x ∈ subBd D := by
          refine ⟨hx_cl, ?_⟩
          rw [← compl_eq_univ_sdiff, closure_compl]
          exact hx_int
        have : x ∈ K ∩ subBd D := ⟨hxK, hx_bd⟩
        rw [h_empty] at this
        exact this
    · exact Or.inr hx_cl
  have hKD_int : (K ∩ interior D).Nonempty := by
    obtain ⟨x, hxK, hxD⟩ := hKD
    rcases hK_sub hxK with hx_int | hx_ncl
    · exact ⟨x, hxK, hx_int⟩
    · exact (hx_ncl (subset_closure hxD)).elim
  have hKc_ext : (K ∩ (closure D)ᶜ).Nonempty := by
    obtain ⟨x, hxK, hxc⟩ := hKc
    rcases hK_sub hxK with hx_int | hx_ncl
    · exact (hxc (interior_subset hx_int)).elim
    · exact ⟨x, hxK, hx_ncl⟩
  obtain ⟨x, _, hx_int, hx_ncl⟩ :=
    hK.2 (interior D) (closure D)ᶜ isOpen_interior isClosed_closure.isOpen_compl
      hK_sub hKD_int hKc_ext
  exact hx_ncl (subset_closure (interior_subset hx_int))

theorem closure_edge_diff_V_eq {S : Type w} [TopologicalSpace S]
    (G : Drawing S) {e : Set S} (he : e ∈ G.E) :
    closure e \ G.V = e := by
  rcases G.toGraph.exists_isLink_of_mem_edgeSet he with ⟨u, v, hlink⟩
  by_cases hne : u ≠ v
  · have hcl := closure_edge_eq_union_ends G hlink hne
    have hcap : closure e ∩ G.V = {u, v} := hlink.2.2.2
    ext x
    simp only [mem_sdiff]
    constructor
    · rintro ⟨hx_cl, hx_nV⟩
      rw [hcl] at hx_cl
      rcases hx_cl with hxe | hxe_uv
      · exact hxe
      · exfalso
        have : x ∈ closure e ∩ G.V := by rw [hcap]; exact hxe_uv
        exact hx_nV this.2
    · intro hxe
      exact ⟨subset_closure hxe, fun hxV => (he.2.1 hxe).2 hxV⟩
  · push Not at hne
    subst hne
    rcases G.edge_cond e he with ⟨u', v', huv', hcap', _⟩ | ⟨u', hcap', ⟨f⟩⟩
    · exfalso
      have hpair : ({u', v'} : Set S) = {u, u} := hcap'.symm.trans hlink.2.2.2
      rw [pair_eq_singleton] at hpair
      have hu' : u' = u := by
        have : u' ∈ ({u', v'} : Set S) := mem_insert u' {v'}
        rwa [hpair, mem_singleton_iff] at this
      have hv' : v' = u := by
        have : v' ∈ ({u', v'} : Set S) := mem_insert_of_mem u' rfl
        rwa [hpair, mem_singleton_iff] at this
      exact huv' (hu'.trans hv'.symm)
    · have hu'_cl : u' ∈ closure e := by
        have : u' ∈ closure e ∩ G.V := by rw [hcap']; exact mem_singleton u'
        exact this.1
      let v₀ : Circle := f.symm ⟨u', hu'_cl⟩
      have hfv₀ : (f v₀).1 = u' := congrArg Subtype.val (f.apply_symm_apply ⟨u', hu'_cl⟩)
      obtain ⟨g⟩ := nonempty_homeomorph_Ioo_nextSegment (finite_singleton v₀) (mem_singleton v₀)
      have hconv : Convex ℝ (Ioo (0 : ℝ) 1) := convex_Ioo 0 1
      have hpc_ioo : IsPathConnected (Ioo (0 : ℝ) 1) :=
        hconv.isPathConnected ⟨1 / 2, by constructor <;> linarith⟩
      let psi : Ioo (0 : ℝ) 1 → S := fun t => (f (g t).1).1
      have hpsi_cont : Continuous psi :=
        continuous_subtype_val.comp (f.continuous.comp (continuous_subtype_val.comp g.continuous))
      have himg_eq : range psi = closure e \ G.V := by
        ext z
        simp only [mem_range, mem_sdiff, psi]
        constructor
        · rintro ⟨t, rfl⟩
          refine ⟨(f (g t).1).2, fun hzV => ?_⟩
          have hz_in : (f (g t).1).1 ∈ closure e ∩ G.V := ⟨(f (g t).1).2, hzV⟩
          rw [hcap', mem_singleton_iff] at hz_in
          have heq : (g t).1 = v₀ :=
            f.injective (Subtype.ext (hz_in.trans hfv₀.symm))
          exact (g t).2.1 heq
        · rintro ⟨hz_cl, hz_nV⟩
          let w : Circle := f.symm ⟨z, hz_cl⟩
          have hfw : (f w).1 = z := congrArg Subtype.val (f.apply_symm_apply ⟨z, hz_cl⟩)
          have hw_seg : w ∈ nextSegment {v₀} v₀ := by
            refine ⟨fun hwv₀ => ?_, fun y hy => by simp at hy⟩
            have hzu' : z = u' := by rw [← hfw, hwv₀, hfv₀]
            have hu'V : u' ∈ G.V := by
              have : u' ∈ closure e ∩ G.V := by rw [hcap']; exact mem_singleton u'
              exact this.2
            exact hz_nV (hzu' ▸ hu'V)
          refine ⟨g.symm ⟨w, hw_seg⟩, ?_⟩
          have hg : (g (g.symm ⟨w, hw_seg⟩)).1 = w :=
            congrArg Subtype.val (g.apply_symm_apply ⟨w, hw_seg⟩)
          rw [hg, hfw]
      have hpc_diff : IsPathConnected (closure e \ G.V) := by
        have : PathConnectedSpace (Ioo (0 : ℝ) 1) :=
          isPathConnected_iff_pathConnectedSpace.mp hpc_ioo
        rw [← himg_eq, ← image_univ]
        exact isPathConnected_univ.image hpsi_cont
      have hsub_diff : closure e \ G.V ⊆ G.U \ G.V := by
        have hclU : closure e ⊆ G.U := G.isClosed_U.closure_subset_iff.mpr
          (he.2.1.trans sdiff_subset)
        exact sdiff_subset_sdiff_left hclU
      have he_sub_diff : e ⊆ closure e \ G.V :=
        subset_sdiff.mpr ⟨subset_closure, disjoint_left.mpr fun _ hxe hxV => (he.2.1 hxe).2 hxV⟩
      exact he.2.2.2 (closure e \ G.V) hsub_diff hpc_diff he_sub_diff

/-- If the closure of the drawing of an edge `e` with link `G.IsLink e u w` meets
`graphDrawingSubgraphU Γ H` (`H ≤ G`), then at least one endpoint `u` or `w` lies in `V(H)`. -/
theorem mem_vertexSet_or_of_closure_edge_inter_subgraphU_nonempty {S : Type w}
    [TopologicalSpace S] {G H : Graph α β} (Γ : GraphDrawing G S) (hHG : H ≤ G)
    {e : β} {u w : α} (hl : G.IsLink e u w)
    (hne : (closure (graphDrawingEdgeSet Γ e) ∩ graphDrawingSubgraphU Γ H).Nonempty) :
    u ∈ V(H) ∨ w ∈ V(H) := by
  obtain ⟨x, hx_cl, hx_H⟩ := hne
  have heG : e ∈ E(G) := hl.edge_mem
  have huG : u ∈ V(G) := hl.left_mem
  have hwG : w ∈ V(G) := hl.right_mem
  have hlink_to := (Γ.iso.isLink_iff ⟨e, heG⟩ ⟨u, huG⟩ ⟨w, hwG⟩).mp hl
  by_cases hxV : x ∈ Γ.drawing.V
  · have hx_inter : x ∈ closure (Γ.iso.edgeEquiv ⟨e, heG⟩).1 ∩ Γ.drawing.V := by
      rw [← graphDrawingEdgeSet_eq Γ heG]
      exact ⟨hx_cl, hxV⟩
    rw [hlink_to.2.2.2] at hx_inter
    rcases hx_inter with hxu | hxw
    · left
      refine mem_vertexSet_of_graphDrawingVertexSet_subset_subgraphU Γ hHG huG ?_
      rw [graphDrawingVertexSet_eq_singleton Γ huG, ← hxu, singleton_subset_iff]
      exact hx_H
    · right
      rw [mem_singleton_iff] at hxw
      refine mem_vertexSet_of_graphDrawingVertexSet_subset_subgraphU Γ hHG hwG ?_
      rw [graphDrawingVertexSet_eq_singleton Γ hwG, ← hxw, singleton_subset_iff]
      exact hx_H
  · have hxe : x ∈ (Γ.iso.edgeEquiv ⟨e, heG⟩).1 := by
      rw [graphDrawingEdgeSet_eq Γ heG] at hx_cl
      rw [← closure_edge_diff_V_eq Γ.drawing (Γ.iso.edgeEquiv ⟨e, heG⟩).2]
      exact ⟨hx_cl, hxV⟩
    rcases hx_H with hx_vert | hx_edge
    · obtain ⟨v, hvH, hxv⟩ := mem_iUnion₂.mp hx_vert
      have hvG : v ∈ V(G) := hHG.vertexSet_mono hvH
      rw [graphDrawingVertexSet_eq_singleton Γ hvG, mem_singleton_iff] at hxv
      exact (hxV (hxv ▸ (Γ.iso.vertexEquiv ⟨v, hvG⟩).2)).elim
    · obtain ⟨f, hfH, hxf⟩ := mem_iUnion₂.mp hx_edge
      have hfG : f ∈ E(G) := hHG.edgeSet_mono hfH
      have hxf' : x ∈ (Γ.iso.edgeEquiv ⟨f, hfG⟩).1 := by
        rw [graphDrawingEdgeSet_eq Γ hfG] at hxf
        rw [← closure_edge_diff_V_eq Γ.drawing (Γ.iso.edgeEquiv ⟨f, hfG⟩).2]
        exact ⟨hxf, hxV⟩
      have heq_set : (Γ.iso.edgeEquiv ⟨e, heG⟩).1 = (Γ.iso.edgeEquiv ⟨f, hfG⟩).1 := by
        by_contra hne_set
        exact disjoint_left.mp
          (disjoint_edges_of_ne Γ.drawing (Γ.iso.edgeEquiv ⟨e, heG⟩).2
            (Γ.iso.edgeEquiv ⟨f, hfG⟩).2 hne_set) hxe hxf'
      have hef : e = f :=
        congrArg Subtype.val (Γ.iso.edgeEquiv.injective (Subtype.ext heq_set))
      have heH : e ∈ E(H) := hef ▸ hfH
      obtain ⟨a, b, habH⟩ := H.exists_isLink_of_mem_edgeSet heH
      rcases hl.left_eq_or_eq (habH.mono hHG) with rfl | rfl
      · exact Or.inl habH.left_mem
      · exact Or.inl habH.right_mem

/-- Any walk `W : GraphWalk G x y` whose start vertex `x` is drawn outside `D` and whose end vertex
`y` is drawn inside `D` meets `V(C)` whenever `subBd D = graphDrawingSubgraphU Γ C` (`C ≤ G`). -/
theorem exists_mem_support_of_subBd_eq_subgraphU {S : Type w} [TopologicalSpace S]
    {G C : Graph α β} (Γ : GraphDrawing G S) (hCG : C ≤ G) {D : Set S}
    (hbd : subBd D = graphDrawingSubgraphU Γ C) {x y : α} (W : GraphWalk G x y)
    (hx : graphDrawingVertexSet Γ x ⊆ Dᶜ) (hy : graphDrawingVertexSet Γ y ⊆ D) :
    ∃ v ∈ W.support, v ∈ V(C) := by
  induction W with
  | @nil u hu =>
    obtain ⟨p, hp⟩ := graphDrawingVertexSet_nonempty Γ hu
    exact (hx hp (hy hp)).elim
  | @cons u z y e hl rest ih =>
    by_cases hz : graphDrawingVertexSet Γ z ⊆ D
    · have heG : e ∈ E(G) := hl.edge_mem
      have hK_conn : IsConnected (closure (graphDrawingEdgeSet Γ e)) := by
        rw [graphDrawingEdgeSet_eq Γ heG]
        exact isConnected_closure_edge Γ.drawing (Γ.iso.edgeEquiv ⟨e, heG⟩).2
      obtain ⟨pz, hpz⟩ := graphDrawingVertexSet_nonempty Γ hl.right_mem
      obtain ⟨pu, hpu⟩ := graphDrawingVertexSet_nonempty Γ hl.left_mem
      have hKD : (closure (graphDrawingEdgeSet Γ e) ∩ D).Nonempty :=
        ⟨pz, graphDrawingVertexSet_subset_closure_edge Γ hl.symm hpz, hz hpz⟩
      have hKc : (closure (graphDrawingEdgeSet Γ e) ∩ Dᶜ).Nonempty :=
        ⟨pu, graphDrawingVertexSet_subset_closure_edge Γ hl hpu, hx hpu⟩
      have hbd_ne := inter_subBd_nonempty_of_isConnected hK_conn hKD hKc
      rw [hbd] at hbd_ne
      rcases mem_vertexSet_or_of_closure_edge_inter_subgraphU_nonempty Γ hCG hl hbd_ne with huC |
        hzC
      · exact ⟨u, List.mem_cons_self, huC⟩
      · exact ⟨z, List.mem_cons_of_mem _ rest.start_mem_support, hzC⟩
    · have hzc : graphDrawingVertexSet Γ z ⊆ Dᶜ := by
        rw [graphDrawingVertexSet_eq_singleton Γ hl.right_mem, singleton_subset_iff] at hz ⊢
        exact hz
      obtain ⟨v, hv_rest, hvC⟩ := ih hzc hy
      exact ⟨v, List.mem_cons_of_mem _ hv_rest, hvC⟩

/-- If `t₁ < t₂ < t₁ + 2π`, the circular angle difference from `exp(t₁)` to `exp(t₂)` is `t₂ - t₁`.
-/
theorem angleDiff_exp_of_lt {t₁ t₂ : ℝ} (h12 : t₁ < t₂) (h2pi : t₂ < t₁ + 2 * Real.pi) :
    (Circle.exp t₁).angleDiff (Circle.exp t₂) = t₂ - t₁ := by
  have hmul : Circle.exp (t₂ - t₁) * Circle.exp t₁ = Circle.exp t₂ := by
    rw [← Circle.exp_add, sub_add_cancel]
  rw [← hmul]
  exact angleDiff_exp_mul (sub_pos.mpr h12) (sub_lt_iff_lt_add'.mpr h2pi)

/-- Clockwise agreement on an `O`-arc, for a map that sends each vertex to a set of points. -/
def SetAgreesWithOArcHomeo {S : Type w} [TopologicalSpace S] (ν : α → Set S) (Ω : CyclicPerm α)
    (C : Set S) (φ : Circle ≃ₜ C) : Prop :=
  (∀ v ∈ Ω.bar, ν v ⊆ C) ∧
    ∀ v₁ v₂ v₃ : α, Ω.IsClockwise3 v₁ v₂ v₃ →
      ∃ (t₁ t₂ t₃ : ℝ), t₁ < t₂ ∧ t₂ < t₃ ∧ t₃ < t₁ + 2 * Real.pi ∧
        (φ (Circle.exp t₁)).1 ∈ ν v₁ ∧ (φ (Circle.exp t₂)).1 ∈ ν v₂ ∧ (φ (Circle.exp t₃)).1 ∈ ν v₃

/-- Under `SetAgreesWithOArcHomeo`, clockwise order `Ω.IsClockwise3 v₁ v₂ v₃` yields
`z₁.angleDiff z₂ < z₁.angleDiff z₃` on `Circle`. -/
theorem angleDiff_lt_of_isClockwise3_set {S : Type w} [TopologicalSpace S]
    {ν : α → Set S} (hpt : ∀ {v p q}, p ∈ ν v → q ∈ ν v → p = q) {Ω : CyclicPerm α} {C : Set S}
    {φ : Circle ≃ₜ C} (hagree : SetAgreesWithOArcHomeo ν Ω C φ)
    {v₁ v₂ v₃ : α} (hclw : Ω.IsClockwise3 v₁ v₂ v₃)
    {z₁ z₂ z₃ : Circle}
    (hz₁ : (φ z₁).1 ∈ ν v₁)
    (hz₂ : (φ z₂).1 ∈ ν v₂)
    (hz₃ : (φ z₃).1 ∈ ν v₃) :
    z₁.angleDiff z₂ < z₁.angleDiff z₃ := by
  obtain ⟨t₁, t₂, t₃, ht12, ht23, ht31, hφ₁, hφ₂, hφ₃⟩ := hagree.2 v₁ v₂ v₃ hclw
  have heq₁ : z₁ = Circle.exp t₁ :=
    φ.injective (Subtype.ext (hpt hz₁ hφ₁))
  have heq₂ : z₂ = Circle.exp t₂ :=
    φ.injective (Subtype.ext (hpt hz₂ hφ₂))
  have heq₃ : z₃ = Circle.exp t₃ :=
    φ.injective (Subtype.ext (hpt hz₃ hφ₃))
  subst heq₁ heq₂ heq₃
  rw [angleDiff_exp_of_lt ht12 (ht23.trans ht31),
      angleDiff_exp_of_lt (ht12.trans ht23) ht31]
  linarith

/-- Under `SetAgreesWithOArcHomeo`, `Ω.Crosses v₁ v₃ v₂ v₄` implies `PairsCrossOn C p₁ p₃ p₂ p₄`
for the corresponding points on the boundary curve `C`. -/
theorem pairsCrossOn_of_crosses_set {S : Type w} [TopologicalSpace S]
    {ν : α → Set S} (hpt : ∀ {v p q}, p ∈ ν v → q ∈ ν v → p = q)
    (hinj : ∀ {u w p}, p ∈ ν u → p ∈ ν w → u = w) {Ω : CyclicPerm α} {C : Set S}
    {φ : Circle ≃ₜ C} (hagree : SetAgreesWithOArcHomeo ν Ω C φ)
    {v₁ v₃ v₂ v₄ : α} (hcr : Ω.Crosses v₁ v₃ v₂ v₄)
    {p₁ p₃ p₂ p₄ : S}
    (hp₁ : p₁ ∈ ν v₁)
    (hp₃ : p₃ ∈ ν v₃)
    (hp₂ : p₂ ∈ ν v₂)
    (hp₄ : p₄ ∈ ν v₄) :
    PairsCrossOn C p₁ p₃ p₂ p₄ := by
  have hcr_int := Ω.crosses_iff_interval.mp hcr
  have hv₁ : v₁ ∈ Ω.bar := by
    rcases hcr_int with ⟨h123, _⟩ | ⟨h143, _⟩
    · exact (Ω.isClockwise3_iff.mp h123.2).2.2.2.1
    · exact (Ω.isClockwise3_iff.mp h143.2).2.2.2.1
  have hv₃ : v₃ ∈ Ω.bar := by
    rcases hcr_int with ⟨h123, _⟩ | ⟨h143, _⟩
    · exact (Ω.isClockwise3_iff.mp h123.2).2.2.2.2.2.1
    · exact (Ω.isClockwise3_iff.mp h143.2).2.2.2.2.2.1
  have hv₂ : v₂ ∈ Ω.bar := by
    rcases hcr_int with ⟨h123, _⟩ | ⟨_, h321⟩
    · exact h123.1.1
    · exact h321.1.1
  have hv₄ : v₄ ∈ Ω.bar := by
    rcases hcr_int with ⟨_, h341⟩ | ⟨h143, _⟩
    · exact h341.1.1
    · exact h143.1.1
  have hp₁C : p₁ ∈ C := hagree.1 v₁ hv₁ hp₁
  have hp₃C : p₃ ∈ C := hagree.1 v₃ hv₃ hp₃
  have hp₂C : p₂ ∈ C := hagree.1 v₂ hv₂ hp₂
  have hp₄C : p₄ ∈ C := hagree.1 v₄ hv₄ hp₄
  let z₁ : Circle := φ.symm ⟨p₁, hp₁C⟩
  let z₃ : Circle := φ.symm ⟨p₃, hp₃C⟩
  let z₂ : Circle := φ.symm ⟨p₂, hp₂C⟩
  let z₄ : Circle := φ.symm ⟨p₄, hp₄C⟩
  have hz₁_val : (φ z₁).1 = p₁ := by simp [z₁]
  have hz₃_val : (φ z₃).1 = p₃ := by simp [z₃]
  have hz₂_val : (φ z₂).1 = p₂ := by simp [z₂]
  have hz₄_val : (φ z₄).1 = p₄ := by simp [z₄]
  have hz₁ : (φ z₁).1 ∈ ν v₁ := by rw [hz₁_val]; exact hp₁
  have hz₃ : (φ z₃).1 ∈ ν v₃ := by rw [hz₃_val]; exact hp₃
  have hz₂ : (φ z₂).1 ∈ ν v₂ := by rw [hz₂_val]; exact hp₂
  have hz₄ : (φ z₄).1 ∈ ν v₄ := by rw [hz₄_val]; exact hp₄
  have hcr_circle : CrossesOn (Set.univ : Set Circle) z₁ z₃ z₂ z₄ := by
    rw [crossesOn_univ_iff_angleDiff]
    have hz_ne : ∀ {u w : α} {zu zw : Circle} {pu pw : S},
        u ≠ w → pu ∈ ν u → pw ∈ ν w →
        (φ zu).1 = pu → (φ zw).1 = pw → zu ≠ zw := by
      intro u w zu zw pu pw huw hpu hpw hzu hzw h
      have hp : pu = pw := hzu.symm.trans ((congrArg Subtype.val (congrArg φ h)).trans hzw)
      exact huw (hinj hpu (hp ▸ hpw))
    rcases hcr_int with h1234 | h1432
    · have h123 : Ω.IsClockwise3 v₁ v₂ v₃ := h1234.1.2
      have h341 : Ω.IsClockwise3 v₃ v₄ v₁ := h1234.2.2
      have h134 : Ω.IsClockwise3 v₁ v₃ v₄ := Ω.isClockwise3_rotate (Ω.isClockwise3_rotate h341)
      have h234 : Ω.IsClockwise3 v₂ v₃ v₄ :=
        (Ω.isClockwise4_iff_interval.mp (Ω.isClockwise4_rotate
          (Ω.isClockwise4_iff_interval.mpr h1234))).1.2
      have h123_def := Ω.isClockwise3_iff.mp h123
      have h341_def := Ω.isClockwise3_iff.mp h341
      have h234_def := Ω.isClockwise3_iff.mp h234
      refine ⟨hz_ne h123_def.2.1 hp₁ hp₃ hz₁_val hz₃_val,
              hz_ne h234_def.2.1 hp₂ hp₄ hz₂_val hz₄_val,
              hz_ne h123_def.1 hp₁ hp₂ hz₁_val hz₂_val,
              hz_ne h341_def.2.2.1.symm hp₁ hp₄ hz₁_val hz₄_val,
              hz_ne h123_def.2.2.1.symm hp₃ hp₂ hz₃_val hz₂_val,
              hz_ne h341_def.1 hp₃ hp₄ hz₃_val hz₄_val, ?_⟩
      have hlt₁ : z₁.angleDiff z₂ < z₁.angleDiff z₃ :=
        angleDiff_lt_of_isClockwise3_set hpt hagree h123 hz₁ hz₂ hz₃
      have hlt₂ : z₁.angleDiff z₃ < z₁.angleDiff z₄ :=
        angleDiff_lt_of_isClockwise3_set hpt hagree h134 hz₁ hz₃ hz₄
      exact ⟨fun _ => not_lt.mpr hlt₂.le, fun _ => hlt₁⟩
    · have h143 : Ω.IsClockwise3 v₁ v₄ v₃ := h1432.1.2
      have h321 : Ω.IsClockwise3 v₃ v₂ v₁ := h1432.2.2
      have h132 : Ω.IsClockwise3 v₁ v₃ v₂ := Ω.isClockwise3_rotate (Ω.isClockwise3_rotate h321)
      have h432 : Ω.IsClockwise3 v₄ v₃ v₂ :=
        (Ω.isClockwise4_iff_interval.mp (Ω.isClockwise4_rotate
          (Ω.isClockwise4_iff_interval.mpr h1432))).1.2
      have h143_def := Ω.isClockwise3_iff.mp h143
      have h321_def := Ω.isClockwise3_iff.mp h321
      have h432_def := Ω.isClockwise3_iff.mp h432
      refine ⟨hz_ne h143_def.2.1 hp₁ hp₃ hz₁_val hz₃_val,
              hz_ne h432_def.2.1.symm hp₂ hp₄ hz₂_val hz₄_val,
              hz_ne h321_def.2.2.1.symm hp₁ hp₂ hz₁_val hz₂_val,
              hz_ne h143_def.1 hp₁ hp₄ hz₁_val hz₄_val,
              hz_ne h321_def.1 hp₃ hp₂ hz₃_val hz₂_val,
              hz_ne h143_def.2.2.1.symm hp₃ hp₄ hz₃_val hz₄_val, ?_⟩
      have hlt₁ : z₁.angleDiff z₄ < z₁.angleDiff z₃ :=
        angleDiff_lt_of_isClockwise3_set hpt hagree h143 hz₁ hz₄ hz₃
      have hlt₂ : z₁.angleDiff z₃ < z₁.angleDiff z₂ :=
        angleDiff_lt_of_isClockwise3_set hpt hagree h132 hz₁ hz₃ hz₂
      exact ⟨fun h => (hlt₂.not_gt h).elim, fun h => (h hlt₁).elim⟩
  have hcr_C : CrossesOn C (oArcMap φ z₁) (oArcMap φ z₃)
      (oArcMap φ z₂) (oArcMap φ z₄) :=
    (crossesOn_oArcMap_iff φ).mpr hcr_circle
  have ho₁ : oArcMap φ z₁ = p₁ := by simp [oArcMap, z₁]
  have ho₃ : oArcMap φ z₃ = p₃ := by simp [oArcMap, z₃]
  have ho₂ : oArcMap φ z₂ = p₂ := by simp [oArcMap, z₂]
  have ho₄ : oArcMap φ z₄ = p₄ := by simp [oArcMap, z₄]
  rw [ho₁, ho₃, ho₂, ho₄] at hcr_C
  exact hcr_C

/-- Under `DrawingAgreesWithOArcHomeo`, clockwise order `Ω.IsClockwise3 v₁ v₂ v₃` yields
`z₁.angleDiff z₂ < z₁.angleDiff z₃` on `Circle`. -/
theorem angleDiff_lt_of_isClockwise3 {S : Type w} [TopologicalSpace S]
    {G : Graph α β} {Γ : GraphDrawing G S} {Ω : CyclicPerm α} {C : Set S}
    {φ : Circle ≃ₜ C} (hagree : DrawingAgreesWithOArcHomeo Γ Ω C φ)
    {v₁ v₂ v₃ : α} (hclw : Ω.IsClockwise3 v₁ v₂ v₃)
    {z₁ z₂ z₃ : Circle}
    (hz₁ : (φ z₁).1 ∈ graphDrawingVertexSet Γ v₁)
    (hz₂ : (φ z₂).1 ∈ graphDrawingVertexSet Γ v₂)
    (hz₃ : (φ z₃).1 ∈ graphDrawingVertexSet Γ v₃) :
    z₁.angleDiff z₂ < z₁.angleDiff z₃ :=
  angleDiff_lt_of_isClockwise3_set (ν := graphDrawingVertexSet Γ)
    (fun h h' => h.2.symm.trans h'.2) hagree hclw hz₁ hz₂ hz₃

/-- Under `DrawingAgreesWithOArcHomeo`, `Ω.Crosses v₁ v₃ v₂ v₄` implies `PairsCrossOn C p₁ p₃ p₂ p₄`
for the corresponding vertex points on the boundary curve `C`. -/
theorem pairsCrossOn_of_crosses {S : Type w} [TopologicalSpace S]
    {G : Graph α β} {Γ : GraphDrawing G S} {Ω : CyclicPerm α} {C : Set S}
    {φ : Circle ≃ₜ C} (hagree : DrawingAgreesWithOArcHomeo Γ Ω C φ)
    {v₁ v₃ v₂ v₄ : α} (hcr : Ω.Crosses v₁ v₃ v₂ v₄)
    {p₁ p₃ p₂ p₄ : S}
    (hp₁ : p₁ ∈ graphDrawingVertexSet Γ v₁)
    (hp₃ : p₃ ∈ graphDrawingVertexSet Γ v₃)
    (hp₂ : p₂ ∈ graphDrawingVertexSet Γ v₂)
    (hp₄ : p₄ ∈ graphDrawingVertexSet Γ v₄) :
    PairsCrossOn C p₁ p₃ p₂ p₄ :=
  pairsCrossOn_of_crosses_set (ν := graphDrawingVertexSet Γ)
    (fun h h' => h.2.symm.trans h'.2) (fun h h' => graphDrawingVertexSet_inj Γ h h') hagree hcr
    hp₁ hp₃ hp₂ hp₄

/-- If two subgraphs `P₁, P₂ ≤ G` have intersecting drawing images in `Γ`, they share a vertex. -/
theorem nonempty_inter_vertexSet_of_nonempty_inter_subgraphU' {S : Type w}
    [TopologicalSpace S] {G P₁ P₂ : Graph α β}
    (Γ : GraphDrawing G S) (hP₁ : P₁ ≤ G) (hP₂ : P₂ ≤ G)
    (hne : (graphDrawingSubgraphU Γ P₁ ∩ graphDrawingSubgraphU Γ P₂).Nonempty) :
    (V(P₁) ∩ V(P₂)).Nonempty := by
  obtain ⟨x, hx₁, hx₂⟩ := hne
  rcases hx₁ with hx_vert | hx_edge
  · obtain ⟨v, hv₁, hxv⟩ := mem_iUnion₂.mp hx_vert
    have hvG : v ∈ V(G) := hP₁.vertexSet_mono hv₁
    have hsub : graphDrawingVertexSet Γ v ⊆ graphDrawingSubgraphU Γ P₂ := by
      rw [graphDrawingVertexSet_eq_singleton Γ hvG, hxv.2, singleton_subset_iff]
      exact hx₂
    exact ⟨v, hv₁, mem_vertexSet_of_graphDrawingVertexSet_subset_subgraphU Γ hP₂ hvG hsub⟩
  · obtain ⟨e, he₁, hxe⟩ := mem_iUnion₂.mp hx_edge
    obtain ⟨u, w, hl₁⟩ := P₁.exists_isLink_of_mem_edgeSet he₁
    rcases mem_vertexSet_or_of_closure_edge_inter_subgraphU_nonempty Γ hP₂ (hl₁.mono hP₁)
        ⟨x, hxe, hx₂⟩ with hu₂ | hw₂
    · exact ⟨u, hl₁.left_mem, hu₂⟩
    · exact ⟨w, hl₁.right_mem, hw₂⟩

/-- For any walk `W : GraphWalk G u v`, the union of vertex points in `W.support` and closures of
edge drawings in `W.edges` is connected. -/
theorem isConnected_walkDrawingU {S : Type w} [TopologicalSpace S]
    {G : Graph α β} (Γ : GraphDrawing G S) {u v : α} (W : GraphWalk G u v) :
    IsConnected ((⋃ w ∈ W.support, graphDrawingVertexSet Γ w) ∪
      (⋃ e ∈ W.edges, closure (graphDrawingEdgeSet Γ e))) := by
  induction W with
  | @nil x hx =>
    have heq : (⋃ w ∈ (GraphWalk.nil hx).support, graphDrawingVertexSet Γ w) ∪
        (⋃ e ∈ (GraphWalk.nil hx).edges, closure (graphDrawingEdgeSet Γ e)) =
        {(Γ.iso.vertexEquiv ⟨x, hx⟩).1} := by
      simp [GraphWalk.support, GraphWalk.edges, graphDrawingVertexSet_eq_singleton Γ hx]
    rw [heq]
    exact isConnected_singleton
  | @cons x z y e hl rest ih =>
    let E_cl := closure (graphDrawingEdgeSet Γ e)
    let R_U := (⋃ w ∈ rest.support, graphDrawingVertexSet Γ w) ∪
      (⋃ f ∈ rest.edges, closure (graphDrawingEdgeSet Γ f))
    have heq : (⋃ w ∈ (GraphWalk.cons hl rest).support, graphDrawingVertexSet Γ w) ∪
        (⋃ f ∈ (GraphWalk.cons hl rest).edges, closure (graphDrawingEdgeSet Γ f)) =
        E_cl ∪ R_U := by
      ext pt
      simp only [GraphWalk.support, GraphWalk.edges, List.mem_cons, mem_union, mem_iUnion,
        exists_prop, E_cl, R_U]
      constructor
      · rintro (⟨w, rfl | hw, hpt⟩ | ⟨f, rfl | hf, hpt⟩)
        · exact Or.inl (graphDrawingVertexSet_subset_closure_edge Γ hl hpt)
        · exact Or.inr (Or.inl ⟨w, hw, hpt⟩)
        · exact Or.inl hpt
        · exact Or.inr (Or.inr ⟨f, hf, hpt⟩)
      · rintro (hpt | ⟨w, hw, hpt⟩ | ⟨f, hf, hpt⟩)
        · exact Or.inr ⟨e, Or.inl rfl, hpt⟩
        · exact Or.inl ⟨w, Or.inr hw, hpt⟩
        · exact Or.inr ⟨f, Or.inr hf, hpt⟩
    rw [heq]
    have hE_conn : IsConnected E_cl := by
      dsimp [E_cl]
      rw [graphDrawingEdgeSet_eq Γ hl.edge_mem]
      exact isConnected_closure_edge Γ.drawing (Γ.iso.edgeEquiv ⟨e, hl.edge_mem⟩).2
    obtain ⟨pz, hpz⟩ := graphDrawingVertexSet_nonempty Γ hl.right_mem
    have hpz_E : pz ∈ E_cl := graphDrawingVertexSet_subset_closure_edge Γ hl.symm hpz
    have hpz_R : pz ∈ R_U :=
      Or.inl (mem_iUnion₂.mpr ⟨z, rest.start_mem_support, hpz⟩)
    exact ⟨⟨pz, Or.inl hpz_E⟩, hE_conn.isPreconnected.union pz hpz_E hpz_R ih.isPreconnected⟩

/-- If `P` is a path in `G` with ends `u` and `v` drawn inside a closed disc `D`, then
`graphDrawingSubgraphU Γ P` is compact and connected, and contains vertex points for `u` and `v`. -/
theorem isCompact_and_isConnected_subgraphU_of_isGraphPathWithEnds
    {S : Type w} [TopologicalSpace S] [T2Space S]
    {G : Graph α β} {Γ : GraphDrawing G S} {P : Graph α β} {u v : α} {D : Set S}
    (hD : IsClosedDisc D) (hP : IsGraphPathWithEnds G P u v)
    (hU : graphDrawingSubgraphU Γ P ⊆ D) :
    IsCompact (graphDrawingSubgraphU Γ P) ∧ IsConnected (graphDrawingSubgraphU Γ P) ∧
    (∃ p_u ∈ graphDrawingVertexSet Γ u, p_u ∈ graphDrawingSubgraphU Γ P) ∧
    (∃ p_v ∈ graphDrawingVertexSet Γ v, p_v ∈ graphDrawingSubgraphU Γ P) := by
  have huG : u ∈ V(G) := hP.le.vertexSet_mono hP.left_mem
  have hvG : v ∈ V(G) := hP.le.vertexSet_mono hP.right_mem
  obtain ⟨p_u, hp_u⟩ := graphDrawingVertexSet_nonempty Γ huG
  obtain ⟨p_v, hp_v⟩ := graphDrawingVertexSet_nonempty Γ hvG
  have hp_uU : p_u ∈ graphDrawingSubgraphU Γ P :=
    graphDrawingVertexSet_subset_subgraphU_of_mem Γ hP.left_mem hp_u
  have hp_vU : p_v ∈ graphDrawingSubgraphU Γ P :=
    graphDrawingVertexSet_subset_subgraphU_of_mem Γ hP.right_mem hp_v
  obtain ⟨hP_le, W, hW_simple, hVP, hEP⟩ := hP
  obtain ⟨W_G, hs_G, he_G⟩ := exists_walk_up_of_le hP_le W
  have hU_eq : graphDrawingSubgraphU Γ P =
      (⋃ w ∈ W_G.support, graphDrawingVertexSet Γ w) ∪
      (⋃ e ∈ W_G.edges, closure (graphDrawingEdgeSet Γ e)) := by
    simp only [graphDrawingSubgraphU, hs_G, he_G, hVP, hEP, mem_ofPred_eq]
  have hconn : IsConnected (graphDrawingSubgraphU Γ P) := by
    rw [hU_eq]
    exact isConnected_walkDrawingU Γ W_G
  have hclosed : IsClosed (graphDrawingSubgraphU Γ P) := by
    rw [hU_eq]
    refine IsClosed.union ?_ ?_
    · refine W_G.support.finite_toSet.isClosed_biUnion fun w hw => ?_
      have hwG : w ∈ V(G) := W_G.mem_vertexSet_of_mem_support hw
      rw [graphDrawingVertexSet_eq_singleton Γ hwG]
      exact isClosed_singleton
    · exact W_G.edges.finite_toSet.isClosed_biUnion fun e _ => isClosed_closure
  have hcomp : IsCompact (graphDrawingSubgraphU Γ P) :=
    (isCompact_of_isClosedDisc hD).of_isClosed_subset hclosed hU
  exact ⟨hcomp, hconn, ⟨p_u, hp_u, hp_uU⟩, ⟨p_v, hp_v, hp_vU⟩⟩

/-- If `D ⊆ EuclideanPlane` is a closed disc whose boundary `subBd D` agrees with a cyclic order `Ω`
via `φ`, and `P₁, P₂` are paths in `G` with ends `(v₁, v₃)` and `(v₂, v₄)` drawn inside `D` such
that `Ω.Crosses v₁ v₃ v₂ v₄`, then `V(P₁) ∩ V(P₂)` is nonempty. -/
theorem nonempty_inter_of_crosses_in_disc
    {G : Graph α β} {Γ : GraphDrawing G EuclideanPlane} {Ω : CyclicPerm α}
    {D : Set EuclideanPlane} {φ : Circle ≃ₜ subBd D}
    (hD : IsClosedDisc D) (hagree : DrawingAgreesWithOArcHomeo Γ Ω (subBd D) φ)
    {P₁ P₂ : Graph α β} {v₁ v₃ v₂ v₄ : α}
    (hP₁ : IsGraphPathWithEnds G P₁ v₁ v₃) (hP₂ : IsGraphPathWithEnds G P₂ v₂ v₄)
    (hU₁ : graphDrawingSubgraphU Γ P₁ ⊆ D) (hU₂ : graphDrawingSubgraphU Γ P₂ ⊆ D)
    (hcr : Ω.Crosses v₁ v₃ v₂ v₄) :
    (V(P₁) ∩ V(P₂)).Nonempty := by
  obtain ⟨hcomp₁, hconn₁, ⟨p₁, hp₁, hp₁U⟩, ⟨p₃, hp₃, hp₃U⟩⟩ :=
    isCompact_and_isConnected_subgraphU_of_isGraphPathWithEnds hD hP₁ hU₁
  obtain ⟨hcomp₂, hconn₂, ⟨p₂, hp₂, hp₂U⟩, ⟨p₄, hp₄, hp₄U⟩⟩ :=
    isCompact_and_isConnected_subgraphU_of_isGraphPathWithEnds hD hP₂ hU₂
  have hcr_bd : PairsCrossOn (discBd D) p₁ p₃ p₂ p₄ := by
    rw [discBd_eq_subBd hD]
    exact pairsCrossOn_of_crosses hagree hcr hp₁ hp₃ hp₂ hp₄
  have hU_inter : (graphDrawingSubgraphU Γ P₁ ∩ graphDrawingSubgraphU Γ P₂).Nonempty :=
    disc_crossing D (graphDrawingSubgraphU Γ P₁) (graphDrawingSubgraphU Γ P₂)
      p₁ p₃ p₂ p₄ hD hU₁ hU₂ hcomp₁ hcomp₂ hconn₁ hconn₂ hp₁U hp₃U hp₂U hp₄U hcr_bd
  exact nonempty_inter_vertexSet_of_nonempty_inter_subgraphU' Γ hP₁.le hP₂.le hU_inter

theorem graphDrawingSubgraphU_subset_U' {S : Type w} [TopologicalSpace S]
    {G : Graph α β} (Γ : GraphDrawing G S) (P : Graph α β) :
    graphDrawingSubgraphU Γ P ⊆ Γ.drawing.U := by
  refine union_subset (iUnion₂_subset fun v _ x hx => ?_) (iUnion₂_subset fun e _ => ?_)
  · rcases hx with ⟨hvG, rfl⟩
    exact Γ.drawing.V_subset_U (Γ.iso.vertexEquiv ⟨v, hvG⟩).2
  · by_cases heG : e ∈ E(G)
    · rw [graphDrawingEdgeSet_eq Γ heG]
      exact Γ.drawing.isClosed_U.closure_subset_iff.mpr
        (((Γ.iso.edgeEquiv ⟨e, heG⟩).2.2.1).trans sdiff_subset)
    · have hemp : graphDrawingEdgeSet Γ e = ∅ := by
        ext x; simp [graphDrawingEdgeSet, heG]
      rw [hemp, closure_empty]
      exact empty_subset _

/-- In a rural neighborhood `N`, no two disjoint `N.Ω`-paths in `N.G` can cross on `N.Ω`. -/
theorem not_omegaPathsCross_of_isRural {N : Neighborhood α β} (hrural : N.IsRural)
    {P₁ P₂ : Graph α β} :
    ¬ ({ G := N.G, Ω := N.Ω, finite_V := N.finite_V, finite_E := N.finite_E,
         bar_subset := N.bar_subset } : Society α β).OmegaPathsCross P₁ P₂ := by
  rintro ⟨hdisj, v₁, v₃, v₂, v₄, hP₁, hP₂, hcr⟩
  obtain ⟨Γ, Δ, Δ₀, hΔ, _, hU_sub, _, _, ⟨φ, _, hφ⟩, _⟩ := hrural
  have hU₁ : graphDrawingSubgraphU Γ P₁ ⊆ Δ :=
    (graphDrawingSubgraphU_subset_U' Γ P₁).trans (hU_sub.trans sdiff_subset)
  have hU₂ : graphDrawingSubgraphU Γ P₂ ⊆ Δ :=
    (graphDrawingSubgraphU_subset_U' Γ P₂).trans (hU_sub.trans sdiff_subset)
  obtain ⟨v, hv₁, hv₂⟩ :=
    nonempty_inter_of_crosses_in_disc hΔ hφ hP₁.1 hP₂.1 hU₁ hU₂ hcr
  exact disjoint_left.mp hdisj hv₁ hv₂

/-! ## Restriction of a cyclic permutation and fences -/

namespace CyclicPerm

variable (Ω : CyclicPerm α)

/-- The restriction `Ω | Y` of a cyclic permutation `Ω` to a subset `Y ⊆ Ω.bar`. -/
noncomputable def restrict (Y : Set α) (_hY : Y ⊆ Ω.bar) : CyclicPerm α :=
  (exists_isRestriction Ω Y).choose

theorem isRestriction_restrict {Y : Set α} (hY : Y ⊆ Ω.bar) :
    Ω.IsRestriction Y (Ω.restrict Y hY) := (exists_isRestriction Ω Y).choose_spec

@[simp]
theorem restrict_bar {Y : Set α} (hY : Y ⊆ Ω.bar) :
    (Ω.restrict Y hY).bar = Y := (Ω.isRestriction_restrict hY).1.trans (inter_eq_right.mpr hY)

theorem isClockwise3_restrict_iff {Y : Set α} (hY : Y ⊆ Ω.bar) {v₁ v₂ v₃ : α} :
    (Ω.restrict Y hY).IsClockwise3 v₁ v₂ v₃ ↔
      v₁ ∈ Y ∧ v₂ ∈ Y ∧ v₃ ∈ Y ∧ Ω.IsClockwise3 v₁ v₂ v₃ := by
  rw [(Ω.isRestriction_restrict hY).isClockwise3_iff, Ω.restrict_bar hY]

theorem crosses_restrict_iff {Y : Set α} (hY : Y ⊆ Ω.bar) {v₁ v₂ v₃ v₄ : α} :
    (Ω.restrict Y hY).Crosses v₁ v₂ v₃ v₄ ↔
      v₁ ∈ Y ∧ v₂ ∈ Y ∧ v₃ ∈ Y ∧ v₄ ∈ Y ∧ Ω.Crosses v₁ v₂ v₃ v₄ := by
  rw [(Ω.isRestriction_restrict hY).crosses_iff, Ω.restrict_bar hY]

theorem interval_restrict {Y : Set α} (hY : Y ⊆ Ω.bar) (v₁ v₂ : α) :
    v₁ ∈ Y → v₂ ∈ Y → (Ω.restrict Y hY).interval v₁ v₂ = Ω.interval v₁ v₂ ∩ Y := by
  intro hv₁ hv₂
  have h := (Ω.isRestriction_restrict hY).interval_eq (a := v₁) (b := v₂)
    (by rwa [Ω.restrict_bar hY]) (by rwa [Ω.restrict_bar hY])
  rwa [Ω.restrict_bar hY] at h

/-- For any distinct `u, v ∈ Ω.bar`, `{u} ∪ Ω(v, u)` and `{v} ∪ Ω(u, v)` form a fence of `Ω`. -/
theorem isFence_halfOpen_intervals {u v : α} (hu : u ∈ Ω.bar) (hv : v ∈ Ω.bar) (huv : u ≠ v) :
    Ω.IsFence ({u} ∪ Ω.interval v u) ({v} ∪ Ω.interval u v) := by
  have hA_sub : {u} ∪ Ω.interval v u ⊆ Ω.bar := by
    rintro z (rfl | hz); exacts [hu, Ω.interval_subset_bar v u hz]
  have hB_sub : {v} ∪ Ω.interval u v ⊆ Ω.bar := by
    rintro z (rfl | hz); exacts [hv, Ω.interval_subset_bar u v hz]
  have hdisj : Disjoint ({u} ∪ Ω.interval v u) ({v} ∪ Ω.interval u v) := by
    rw [disjoint_left]; intro z hz₁ hz₂
    rcases hz₁ with hzu | hz₁ <;> rcases hz₂ with hzv | hz₂
    · exact huv (hzu.symm.trans hzv)
    · rw [mem_singleton_iff] at hzu; subst hzu; exact Ω.not_mem_interval_left z v hz₂
    · rw [mem_singleton_iff] at hzv; subst hzv; exact Ω.not_mem_interval_left z u hz₁
    · exact disjoint_left.mp (Ω.disjoint_interval_swap v u) hz₁ hz₂
  have hunion : ({u} ∪ Ω.interval v u) ∪ ({v} ∪ Ω.interval u v) = Ω.bar := by
    ext z; simp only [mem_union, mem_singleton_iff]
    refine ⟨by rintro ((rfl | hz) | (rfl | hz)); exacts [hu, hz.1.1, hv, hz.1.1], fun hz => ?_⟩
    by_cases hzu : z = u
    · exact Or.inl (Or.inl hzu)
    · by_cases hzv : z = v
      · exact Or.inr (Or.inl hzv)
      · exact (Ω.mem_interval_or_interval_swap hv hu hz huv.symm hzv hzu).imp Or.inr Or.inr
  have hf₀ := Ω.isFence_interval_compl hv hu huv.symm
  have hf₁ := Ω.isFence_interval_compl hu hv huv
  refine ⟨hA_sub, hB_sub, hdisj, hunion, ?_⟩
  intro a₁ ha₁ a₂ ha₂ ha12 b₁ hb₁ b₂ hb₂ hb12 hcr
  have ha₁_0 : a₁ ∈ {v, u} ∪ Ω.interval v u := ha₁.elim (fun h => Or.inl (Or.inr h)) Or.inr
  have ha₂_0 : a₂ ∈ {v, u} ∪ Ω.interval v u := ha₂.elim (fun h => Or.inl (Or.inr h)) Or.inr
  have hb₁_1 : b₁ ∈ {u, v} ∪ Ω.interval u v := hb₁.elim (fun h => Or.inl (Or.inr h)) Or.inr
  have hb₂_1 : b₂ ∈ {u, v} ∪ Ω.interval u v := hb₂.elim (fun h => Or.inl (Or.inr h)) Or.inr
  have h_no_cross_uv : ∀ {x y : α}, x ∈ Ω.interval v u → y ∈ Ω.interval u v →
      ¬ Ω.Crosses u x v y := by
    intro x y hx hy hcr_xy
    have hv_ux : v ∈ Ω.interval u x := Ω.mem_interval_rotate_right hx
    have hy_ux : y ∈ Ω.interval u x := Ω.interval_subset_interval_left hv_ux hy
    have hdisj_ux := Ω.disjoint_interval_swap u x
    rcases Ω.crosses_iff_interval.mp hcr_xy with ⟨_, h2⟩ | ⟨_, h2⟩
    · exact disjoint_left.mp hdisj_ux hy_ux h2
    · exact disjoint_left.mp hdisj_ux hv_ux h2
  rcases ha₁ with rfl | ha₁_in <;> rcases ha₂ with rfl | ha₂_in
  · exact ha12 rfl
  · rcases hb₁ with rfl | hb₁_in <;> rcases hb₂ with rfl | hb₂_in
    · exact hb12 rfl
    · exact h_no_cross_uv ha₂_in hb₂_in hcr
    · exact h_no_cross_uv ha₂_in hb₁_in hcr.swap_right
    · exact hf₀.2.2.2.2 a₁ ha₁_0 a₂ ha₂_0 ha12 b₁ hb₁_in b₂ hb₂_in hb12 hcr
  · rcases hb₁ with rfl | hb₁_in <;> rcases hb₂ with rfl | hb₂_in
    · exact hb12 rfl
    · exact h_no_cross_uv ha₁_in hb₂_in hcr.swap_left
    · exact h_no_cross_uv ha₁_in hb₁_in hcr.swap_left.swap_right
    · exact hf₀.2.2.2.2 a₁ ha₁_0 a₂ ha₂_0 ha12 b₁ hb₁_in b₂ hb₂_in hb12 hcr
  · exact hf₁.symm.2.2.2.2 a₁ ha₁_in a₂ ha₂_in ha12 b₁ hb₁_1 b₂ hb₂_1 hb12 hcr

/-- Any fence `(A', B')` of `Ω.restrict Y hY` extends to a fence `(A, B)` of `Ω` with
`A' ⊆ A` and `B' ⊆ B`. -/
theorem exists_isFence_of_restrict {Y : Set α} (hY : Y ⊆ Ω.bar) {A' B' : Set α}
    (hfence' : (Ω.restrict Y hY).IsFence A' B') :
    ∃ A B : Set α, Ω.IsFence A B ∧ A' ⊆ A ∧ B' ⊆ B := by
  let Ω' := Ω.restrict Y hY
  by_cases hA' : A'.Nonempty
  · by_cases hB' : B'.Nonempty
    · have hW' : Y ⊆ Ω'.bar := by rw [Ω.restrict_bar hY]
      have hW'_AB : Y ⊆ A' ∪ B' := by
        have h_eq := hfence'.2.2.2.1; rw [Ω.restrict_bar hY] at h_eq; exact h_eq.symm.subset
      have ha_ne : (A' ∩ Y).Nonempty := by
        have h1 := hfence'.1; rw [Ω.restrict_bar hY] at h1; rwa [inter_eq_left.mpr h1]
      have hb_ne : (B' ∩ Y).Nonempty := by
        have h2 := hfence'.2.1; rw [Ω.restrict_bar hY] at h2; rwa [inter_eq_left.mpr h2]
      obtain ⟨a'_0, ha'_0, b_0, hb_0, hd_ab⟩ :=
        Ω'.exists_empty_interval_AB_of_subset_union hW' hW'_AB ha_ne hb_ne
      obtain ⟨b'_0, hb'_0, a_0, ha_0, hd_ba⟩ :=
        Ω'.exists_empty_interval_AB_of_subset_union hW' (union_comm A' B' ▸ hW'_AB) hb_ne ha_ne
      obtain ⟨hA_sub, hB_sub, _, _, _, _⟩ :=
        Society.four_arc_partition hfence' hW' ha_0 ha'_0 hb_0 hb'_0 hd_ab hd_ba
      have ha'_ne_b' : a'_0 ≠ b'_0 :=
        fun h => disjoint_left.mp hfence'.2.2.1 ha'_0.1 (h ▸ hb'_0.1)
      refine ⟨{a'_0} ∪ Ω.interval b'_0 a'_0, {b'_0} ∪ Ω.interval a'_0 b'_0,
        Ω.isFence_halfOpen_intervals (hY ha'_0.2) (hY hb'_0.2) ha'_ne_b', ?_, ?_⟩
      · intro x hx
        have hxY : x ∈ Y := by have h1 := hfence'.1 hx; rwa [Ω.restrict_bar hY] at h1
        rcases (hA_sub ⟨hx, hxY⟩).1 with rfl | hx_int
        · exact Or.inl rfl
        · rw [Ω.interval_restrict hY b'_0 a'_0 hb'_0.2 ha'_0.2] at hx_int; exact Or.inr hx_int.1
      · intro y hy
        have hyY : y ∈ Y := by have h2 := hfence'.2.1 hy; rwa [Ω.restrict_bar hY] at h2
        rcases (hB_sub ⟨hy, hyY⟩).1 with rfl | hy_int
        · exact Or.inl rfl
        · rw [Ω.interval_restrict hY a'_0 b'_0 ha'_0.2 hb'_0.2] at hy_int; exact Or.inr hy_int.1
    · rw [not_nonempty_iff_eq_empty] at hB'
      have h1 := hfence'.1; rw [Ω.restrict_bar hY] at h1
      refine ⟨Ω.bar, ∅, ⟨Subset.rfl, empty_subset _, disjoint_empty _, union_empty _, ?_⟩,
        h1.trans hY, by rw [hB']⟩
      intro _ _ _ _ _ _ hb₁; exact (notMem_empty _ hb₁).elim
  · rw [not_nonempty_iff_eq_empty] at hA'
    have h2 := hfence'.2.1; rw [Ω.restrict_bar hY] at h2
    refine ⟨∅, Ω.bar, ⟨empty_subset _, Subset.rfl, empty_disjoint _, empty_union _, ?_⟩,
      by rw [hA'], h2.trans hY⟩
    intro _ ha₁; exact (notMem_empty _ ha₁).elim

theorem isFence_inter_restrict {Y : Set α} (hY : Y ⊆ Ω.bar) {A B : Set α}
    (hfence : Ω.IsFence A B) :
    (Ω.restrict Y hY).IsFence (A ∩ Y) (B ∩ Y) := by
  refine ⟨by rw [Ω.restrict_bar hY]; exact inter_subset_right,
    by rw [Ω.restrict_bar hY]; exact inter_subset_right,
    hfence.2.2.1.mono inter_subset_left inter_subset_left, ?_, ?_⟩
  · rw [← union_inter_distrib_right, hfence.2.2.2.1, Ω.restrict_bar hY, inter_eq_right.mpr hY]
  · intro a₁ ha₁ a₂ ha₂ ha12 b₁ hb₁ b₂ hb₂ hb12 hcr
    exact hfence.2.2.2.2 a₁ ha₁.1 a₂ ha₂.1 ha12 b₁ hb₁.1 b₂ hb₂.1 hb12
      ((Ω.crosses_restrict_iff hY).mp hcr).2.2.2.2

end CyclicPerm

namespace Society

variable (S : Society α β)

/-- The society `(S.G, S.Ω | Y)` obtained by restricting `S.Ω` to `Y ⊆ S.Ω.bar`. -/
noncomputable def restrictOmega (Y : Set α) (hY : Y ⊆ S.Ω.bar) : Society α β where
  G := S.G
  Ω := S.Ω.restrict Y hY
  finite_V := S.finite_V
  finite_E := S.finite_E
  bar_subset := by rw [S.Ω.restrict_bar hY]; exact hY.trans S.bar_subset

@[simp]
theorem restrictOmega_G (Y : Set α) (hY : Y ⊆ S.Ω.bar) :
    (S.restrictOmega Y hY).G = S.G := rfl

@[simp]
theorem restrictOmega_Ω (Y : Set α) (hY : Y ⊆ S.Ω.bar) :
    (S.restrictOmega Y hY).Ω = S.Ω.restrict Y hY := rfl

theorem isOmegaPathWithEnds_restrictOmega_iff {Y : Set α} (hY : Y ⊆ S.Ω.bar)
    {P : Graph α β} {a b : α} :
    (S.restrictOmega Y hY).IsOmegaPathWithEnds P a b ↔
      S.IsOmegaPathWithEnds P a b ∧ a ∈ Y ∧ b ∈ Y := by
  simp only [IsOmegaPathWithEnds, restrictOmega_G, restrictOmega_Ω, CyclicPerm.restrict_bar]
  exact ⟨fun ⟨h1, h2, ha, hb⟩ => ⟨⟨h1, h2, hY ha, hY hb⟩, ha, hb⟩,
    fun ⟨⟨h1, h2, _, _⟩, ha, hb⟩ => ⟨h1, h2, ha, hb⟩⟩

theorem transactionEnds_restrictOmega_eq {Y : Set α} (hY : Y ⊆ S.Ω.bar)
    {P_set : Set (Graph α β)} (hends : S.transactionEnds P_set ⊆ Y) :
    (S.restrictOmega Y hY).transactionEnds P_set = S.transactionEnds P_set := by
  ext v; simp only [transactionEnds, mem_ofPred_eq, isOmegaPathWithEnds_restrictOmega_iff]
  exact ⟨fun ⟨P, hP, b, hP_ends, _, _⟩ => ⟨P, hP, b, hP_ends⟩,
    fun ⟨P, hP, b, hP_ends⟩ => ⟨P, hP, b, hP_ends,
      hends (hP_ends.mem_transactionEnds_left S hP),
      hends (hP_ends.mem_transactionEnds_right S hP)⟩⟩

/-- `P_set` is a crooked transaction in `(S.G, S.Ω | Y)` if and only if `P_set` is a crooked
transaction in `(S.G, S.Ω)` and `V(P_set) ⊆ Y`. -/
theorem isCrookedTransaction_restrictOmega_iff {Y : Set α} (hY : Y ⊆ S.Ω.bar)
    {P_set : Set (Graph α β)} :
    (S.restrictOmega Y hY).IsCrookedTransaction P_set ↔
      S.IsCrookedTransaction P_set ∧ S.transactionEnds P_set ⊆ Y := by
  let S' := S.restrictOmega Y hY
  constructor
  · rintro ⟨⟨A', B', hfence'⟩, hnot_per'⟩
    obtain ⟨A, B, hfence, hA', hB'⟩ := S.Ω.exists_isFence_of_restrict hY hfence'.2.1
    have hends_Y : S.transactionEnds P_set ⊆ Y := by
      rintro v ⟨P, hP, b, hP_ends⟩
      obtain ⟨a₀, _, b₀, _, hP_ends'⟩ := hfence'.2.2 P hP
      rw [S.isOmegaPathWithEnds_restrictOmega_iff hY] at hP_ends'
      rcases hP_ends.ends_eq S hP_ends'.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hP_ends'.2.1
      · exact hP_ends'.2.2
    have htr_S : S.IsFenceFor P_set A B := by
      refine ⟨⟨fun P hP => ?_, hfence'.1.2⟩, hfence, fun P hP => ?_⟩
      · obtain ⟨a, _, b, _, hP_e⟩ := hfence'.2.2 P hP
        exact ⟨a, b, ((S.isOmegaPathWithEnds_restrictOmega_iff hY).mp hP_e).1⟩
      · obtain ⟨a, ha, b, hb, hP_e⟩ := hfence'.2.2 P hP
        exact ⟨a, hA' ha, b, hB' hb, ((S.isOmegaPathWithEnds_restrictOmega_iff hY).mp hP_e).1⟩
    refine ⟨⟨⟨A, B, htr_S⟩, ?_⟩, hends_Y⟩
    intro P hP ⟨_, a, b, hP_ends, hdisj⟩
    have haY : a ∈ Y := hends_Y (hP_ends.mem_transactionEnds_left S hP)
    have hbY : b ∈ Y := hends_Y (hP_ends.mem_transactionEnds_right S hP)
    have hP_ends' : S'.IsOmegaPathWithEnds P a b :=
      (S.isOmegaPathWithEnds_restrictOmega_iff hY).mpr ⟨hP_ends, haY, hbY⟩
    have hW_eq : S'.transactionEnds P_set = S.transactionEnds P_set :=
      S.transactionEnds_restrictOmega_eq hY hends_Y
    apply hnot_per' P hP ⟨hP, a, b, hP_ends', ?_⟩
    change Disjoint ((S.Ω.restrict Y hY).interval a b) (S'.transactionEnds P_set) ∨
      Disjoint ((S.Ω.restrict Y hY).interval b a) (S'.transactionEnds P_set)
    rw [hW_eq, S.Ω.interval_restrict hY a b haY hbY, S.Ω.interval_restrict hY b a hbY haY]
    exact hdisj.imp (fun hd => hd.mono_left inter_subset_left)
      (fun hd => hd.mono_left inter_subset_left)
  · rintro ⟨⟨⟨A, B, hfence⟩, hnot_per⟩, hends_Y⟩
    have hW_eq : S'.transactionEnds P_set = S.transactionEnds P_set :=
      S.transactionEnds_restrictOmega_eq hY hends_Y
    refine ⟨⟨A ∩ Y, B ∩ Y, ⟨fun P hP => ?_, hfence.1.2⟩,
      S.Ω.isFence_inter_restrict hY hfence.2.1, fun P hP => ?_⟩, ?_⟩
    · obtain ⟨a, _, b, _, hP_e⟩ := hfence.2.2 P hP
      exact ⟨a, b, (S.isOmegaPathWithEnds_restrictOmega_iff hY).mpr
        ⟨hP_e, hends_Y (hP_e.mem_transactionEnds_left S hP),
          hends_Y (hP_e.mem_transactionEnds_right S hP)⟩⟩
    · obtain ⟨a, ha, b, hb, hP_e⟩ := hfence.2.2 P hP
      have haY : a ∈ Y := hends_Y (hP_e.mem_transactionEnds_left S hP)
      have hbY : b ∈ Y := hends_Y (hP_e.mem_transactionEnds_right S hP)
      exact ⟨a, ⟨ha, haY⟩, b, ⟨hb, hbY⟩,
        (S.isOmegaPathWithEnds_restrictOmega_iff hY).mpr ⟨hP_e, haY, hbY⟩⟩
    · intro P hP ⟨_, a, b, hP_ends', hdisj'⟩
      obtain ⟨hP_ends, haY, hbY⟩ := (S.isOmegaPathWithEnds_restrictOmega_iff hY).mp hP_ends'
      change Disjoint ((S.Ω.restrict Y hY).interval a b) (S'.transactionEnds P_set) ∨
        Disjoint ((S.Ω.restrict Y hY).interval b a) (S'.transactionEnds P_set) at hdisj'
      rw [hW_eq, S.Ω.interval_restrict hY a b haY hbY,
        S.Ω.interval_restrict hY b a hbY haY] at hdisj'
      apply hnot_per P hP ⟨hP, a, b, hP_ends, ?_⟩
      rcases hdisj' with hd | hd
      · exact Or.inl (disjoint_left.mpr fun z hz hzW => disjoint_left.mp hd ⟨hz, hends_Y hzW⟩ hzW)
      · exact Or.inr (disjoint_left.mpr fun z hz hzW => disjoint_left.mp hd ⟨hz, hends_Y hzW⟩ hzW)

/-- Transferring a crooked transaction between societies with the same cyclic permutation. -/
theorem isCrookedTransaction_of_omega_eq {S₁ S₂ : Society α β} {P_set : Set (Graph α β)}
    (hΩ : S₁.Ω = S₂.Ω) (hP₁ : ∀ P ∈ P_set, P ≤ S₁.G) (hP₂ : ∀ P ∈ P_set, P ≤ S₂.G)
    (hcr : S₁.IsCrookedTransaction P_set) : S₂.IsCrookedTransaction P_set := by
  obtain ⟨A, B, hfence⟩ := hcr.1
  have hends_iff : ∀ P ∈ P_set, ∀ a b : α,
      S₂.IsOmegaPathWithEnds P a b ↔ S₁.IsOmegaPathWithEnds P a b := fun P hP a b => by
    simp only [IsOmegaPathWithEnds, hΩ]
    exact ⟨fun ⟨h1, h2⟩ => ⟨⟨hP₁ P hP, h1.2⟩, h2⟩, fun ⟨h1, h2⟩ => ⟨⟨hP₂ P hP, h1.2⟩, h2⟩⟩
  have hW_eq : S₂.transactionEnds P_set = S₁.transactionEnds P_set := by
    ext z; simp only [transactionEnds, mem_ofPred_eq]
    exact ⟨fun ⟨P, hP, b, h⟩ => ⟨P, hP, b, (hends_iff P hP z b).mp h⟩,
      fun ⟨P, hP, b, h⟩ => ⟨P, hP, b, (hends_iff P hP z b).mpr h⟩⟩
  refine ⟨⟨A, B, ⟨fun P hP => ?_, hfence.1.2⟩, hΩ ▸ hfence.2.1, fun P hP => ?_⟩, ?_⟩
  · obtain ⟨a, _, b, _, h⟩ := hfence.2.2 P hP; exact ⟨a, b, (hends_iff P hP a b).mpr h⟩
  · obtain ⟨a, ha, b, hb, h⟩ := hfence.2.2 P hP; exact ⟨a, ha, b, hb, (hends_iff P hP a b).mpr h⟩
  · intro P hP ⟨_, a, b, hP_e, hdisj⟩
    rw [hW_eq, ← hΩ] at hdisj
    exact hcr.2 P hP ⟨hP, a, b, (hends_iff P hP a b).mp hP_e, hdisj⟩

end Society

/-! ## Subgraph helpers for rural neighborhoods -/

/-- Every vertex of a path `Q` with distinct ends `x ≠ y` is incident to some edge of `Q`. -/
theorem IsGraphPathWithEnds.exists_inc_of_mem_of_ne {G Q : Graph α β} {x y v : α}
    (hQ : IsGraphPathWithEnds G Q x y) (hxy : x ≠ y) (hv : v ∈ V(Q)) :
    ∃ e ∈ E(Q), Q.Inc e v := by
  obtain ⟨Q₁, Q₂, hQ₁, hQ₂, hp₁, hp₂, _, _, _⟩ := hQ.exists_split_at hv
  by_cases hvx : v = x
  · subst hvx; obtain ⟨e, he₂, hinc₂⟩ := hp₂.exists_inc_left_of_ne hxy
    exact ⟨e, hQ₂.edgeSet_mono he₂, hinc₂.mono hQ₂⟩
  · obtain ⟨e, he₁, hinc₁⟩ := hp₁.symm.exists_inc_left_of_ne hvx
    exact ⟨e, hQ₁.edgeSet_mono he₁, hinc₁.mono hQ₁⟩

/-- The single-vertex edgeless subgraph of `G` on `{v}`. -/
def section9SingleVertex (G : Graph α β) (v : α) : Graph α β :=
  (G.induce {v}).restrict ∅

@[simp]
theorem vertexSet_section9SingleVertex (G : Graph α β) (v : α) :
    V(section9SingleVertex G v) = {v} := rfl

@[simp]
theorem edgeSet_section9SingleVertex (G : Graph α β) (v : α) :
    E(section9SingleVertex G v) = ∅ := by simp [section9SingleVertex]

theorem section9SingleVertex_le {G : Graph α β} {v : α} (hv : v ∈ V(G)) :
    section9SingleVertex G v ≤ G :=
  restrict_le.trans (G.induce_le (singleton_subset_iff.mpr hv))

theorem isGraphPathWithEnds_section9SingleVertex {G : Graph α β} {v : α} (hv : v ∈ V(G)) :
    IsGraphPathWithEnds G (section9SingleVertex G v) v v := by
  let Q := section9SingleVertex G v
  have hvQ : v ∈ V(Q) := by simp [Q]
  exact ⟨section9SingleVertex_le hv, GraphWalk.nil hvQ,
    by simp [GraphWalk.IsSimple, GraphWalk.support],
    by ext x; simp [GraphWalk.support], by ext e; simp [GraphWalk.edges]⟩

/-- Deleting a single edge `e` from `G` while keeping all vertices. -/
def section9DeleteEdge (G : Graph α β) (e : β) : Graph α β :=
  G.restrict (E(G) \ {e})

@[simp]
theorem vertexSet_section9DeleteEdge (G : Graph α β) (e : β) :
    V(section9DeleteEdge G e) = V(G) := rfl

@[simp]
theorem edgeSet_section9DeleteEdge (G : Graph α β) (e : β) :
    E(section9DeleteEdge G e) = E(G) \ {e} := by
  unfold section9DeleteEdge; rw [edgeSet_restrict, inter_eq_right]; exact sdiff_subset

theorem section9DeleteEdge_le (G : Graph α β) (e : β) :
    section9DeleteEdge G e ≤ G := restrict_le

/-- Deleting an edge from a rural neighborhood preserves `IsRural`
(Graph Minors IX, Section 9, Claim (3), page 62). -/
theorem rural_deleteEdge (N : Neighborhood α β) (hrural : N.IsRural) (e : β) :
    (Neighborhood.mk (section9DeleteEdge N.G e) N.Ω N.Ω₀
      N.finite_V (N.finite_E.subset (section9DeleteEdge_le N.G e).edgeSet_mono)
      N.bar_subset N.bar₀_subset).IsRural :=
  hrural.ofSubgraph (section9DeleteEdge_le N.G e)
    (by rw [vertexSet_section9DeleteEdge, inter_eq_left.mpr N.bar_subset])
    (fun _ _ _ h => h)
    (by rw [vertexSet_section9DeleteEdge, inter_eq_left.mpr N.bar₀_subset])
    (fun _ _ _ h => h)

/-- Deleting an isolated vertex `v ∉ N.Ω₀.bar` (while restricting `N.Ω` to `N.Ω.bar \ {v}`)
from a rural neighborhood preserves `IsRural`
(Graph Minors IX, Section 9, Claim (3), page 62). -/
theorem rural_deleteIsolatedVertex (N : Neighborhood α β) (hrural : N.IsRural) {v : α}
    (hv₀ : v ∉ N.Ω₀.bar) :
    (Neighborhood.mk (deleteVertices N.G {v})
      (N.Ω.restrict (N.Ω.bar \ {v}) sdiff_subset) N.Ω₀
      (N.finite_V.subset (deleteVertices_le N.G {v}).vertexSet_mono)
      (N.finite_E.subset (deleteVertices_le N.G {v}).edgeSet_mono)
      (by rw [N.Ω.restrict_bar sdiff_subset]; exact fun z hz => ⟨N.bar_subset hz.1, hz.2⟩)
      (fun z hz => ⟨N.bar₀_subset hz, fun hzv => hv₀ (hzv ▸ hz)⟩)).IsRural :=
  hrural.ofSubgraph (deleteVertices_le N.G {v})
    (by
      change (N.Ω.restrict (N.Ω.bar \ {v}) sdiff_subset).bar = N.Ω.bar ∩ V(deleteVertices N.G {v})
      rw [N.Ω.restrict_bar sdiff_subset, vertexSet_deleteVertices]
      ext z; exact ⟨fun ⟨hz, hzv⟩ => ⟨hz, N.bar_subset hz, hzv⟩, fun ⟨hz, _, hzv⟩ => ⟨hz, hzv⟩⟩)
    (fun v₁ v₂ v₃ h => ((N.Ω.isClockwise3_restrict_iff sdiff_subset).mp h).2.2.2)
    (by
      change N.Ω₀.bar = N.Ω₀.bar ∩ V(deleteVertices N.G {v})
      rw [vertexSet_deleteVertices]
      ext z; exact ⟨fun hz => ⟨hz, N.bar₀_subset hz, fun hzv => hv₀ (hzv ▸ hz)⟩, fun ⟨hz, _⟩ => hz⟩)
    (fun _ _ _ h => h)

/-! ## Section 9 configurations and minimum weight -/

/-- `(N, S_comp, P_set)` is a Section 9 configuration for `(S, p)` if `N` is a rural neighborhood,
`S_comp` is the composition of `S` with `N`, and `P_set` is a crooked transaction in `S_comp` of
cardinality `≥ p` (Graph Minors IX, Section 9, (1), page 62). -/
def IsSection9Config (S : Society α β) (p : ℕ)
    (N : Neighborhood α β) (S_comp : Society α β) (P_set : Set (Graph α β)) : Prop :=
  S_comp.IsComposition S N ∧ N.IsRural ∧ S_comp.IsCrookedTransaction P_set ∧ p ≤ P_set.ncard

/-- Twice the objective `|V(G₁)| + |E(G₁)| + |E(⋃ P_set)| - (1/2)|ΩBar₁|` from (2) on page 62. -/
noncomputable def section9Weight (N : Neighborhood α β) (S_comp : Society α β)
    (P_set : Set (Graph α β)) : ℕ :=
  2 * V(N.G).ncard - N.Ω.bar.ncard +
    2 * (E(N.G).ncard + E(S_comp.transactionUnion P_set).ncard)

/-- `(N, S_comp, P_set)` satisfies (1) and (2) of the proof of (9.1) (page 62): it is a Section 9
configuration minimizing `section9Weight`. -/
def IsMinSection9Config (S : Society α β) (p : ℕ)
    (N : Neighborhood α β) (S_comp : Society α β) (P_set : Set (Graph α β)) : Prop :=
  IsSection9Config S p N S_comp P_set ∧
    ∀ (N' : Neighborhood α β) (S_comp' : Society α β) (P_set' : Set (Graph α β)),
      IsSection9Config S p N' S_comp' P_set' →
      section9Weight N S_comp P_set ≤ section9Weight N' S_comp' P_set'

/-- If there is a Section 9 configuration for `(S, p)`, then there is one of minimum weight. -/
theorem exists_isMinSection9Config (S : Society α β) (p : ℕ)
    (hex : ∃ (N : Neighborhood α β) (S_comp : Society α β) (P_set : Set (Graph α β)),
      IsSection9Config S p N S_comp P_set) :
    ∃ (N : Neighborhood α β) (S_comp : Society α β) (P_set : Set (Graph α β)),
      IsMinSection9Config S p N S_comp P_set := by
  rcases hex with ⟨N₀, S₀, P₀, h₀⟩
  have hex_w : ∃ w : ℕ, ∃ (N : Neighborhood α β) (S_comp : Society α β) (P_set : Set (Graph α β)),
      IsSection9Config S p N S_comp P_set ∧ section9Weight N S_comp P_set = w :=
    ⟨section9Weight N₀ S₀ P₀, N₀, S₀, P₀, h₀, rfl⟩
  classical
  obtain ⟨N, S_comp, P_set, hcfg, hw⟩ := Nat.find_spec hex_w
  refine ⟨N, S_comp, P_set, hcfg, fun N' S_comp' P_set' hcfg' => ?_⟩
  rw [hw]; exact Nat.find_min' hex_w ⟨N', S_comp', P_set', hcfg', rfl⟩

/-! ## Proof of Claim (3) (page 62) -/

/-- **Graph Minors IX, (9.1), Claim (3)** (page 62):
"Every edge of $G_1$ is an edge of $\bigcup \mathscr{P}$, and every vertex of $G_1$ not in $V(G)$
is a vertex of $\bigcup \mathscr{P}$." -/
theorem lemma_9_1_claim_3
    {S : Society α β} {p : ℕ}
    {N : Neighborhood α β} {S_comp : Society α β} {P_set : Set (Graph α β)}
    (hmin : IsMinSection9Config S p N S_comp P_set) :
    E(N.G) ⊆ E(S_comp.transactionUnion P_set) ∧
      V(N.G) \ V(S.G) ⊆ V(S_comp.transactionUnion P_set) := by
  rcases hmin with ⟨⟨hcomp, hrural, hcrooked, hcard⟩, hle_weight⟩
  obtain ⟨A, B, hfence⟩ := hcrooked.1
  have hP_le : ∀ P ∈ P_set, P ≤ S_comp.G := fun P hP => by
    obtain ⟨_, _, h⟩ := hfence.1.1 P hP; exact h.1.le
  have hEN_sub : E(N.G) ⊆ E(S_comp.transactionUnion P_set) := by
    intro e heN; by_contra he_not_U
    have he_not_S : e ∉ E(S.G) := fun heS => disjoint_right.mp hcomp.1.1.2.2.2.2 heN heS
    let G₁' := section9DeleteEdge N.G e
    let G_comp' := section9DeleteEdge S_comp.G e
    let N' : Neighborhood α β :=
      ⟨G₁', N.Ω, N.Ω₀, N.finite_V,
        N.finite_E.subset (section9DeleteEdge_le N.G e).edgeSet_mono,
        N.bar_subset, N.bar₀_subset⟩
    let S_comp' : Society α β :=
      ⟨G_comp', S_comp.Ω, S_comp.finite_V,
        S_comp.finite_E.subset (section9DeleteEdge_le S_comp.G e).edgeSet_mono,
        S_comp.bar_subset⟩
    have hcomp' : S_comp'.IsComposition S N' := by
      refine ⟨⟨⟨?_, ?_, hcomp.1.1.2.2.1, ?_, ?_⟩, hcomp.1.2⟩, hcomp.2.1, hcomp.2.2.1, hcomp.2.2.2⟩
      · rw [(Compatible.of_le_le hcomp.1.1.1 (section9DeleteEdge_le S_comp.G e)).le_iff,
          edgeSet_section9DeleteEdge]
        exact ⟨hcomp.1.1.1.vertexSet_mono, fun f hf => ⟨hcomp.1.1.1.edgeSet_mono hf,
          fun hfe => he_not_S (hfe ▸ hf)⟩⟩
      · rw [(Compatible.of_le_le ((section9DeleteEdge_le N.G e).trans hcomp.1.1.2.1)
          (section9DeleteEdge_le S_comp.G e)).le_iff,
          edgeSet_section9DeleteEdge, edgeSet_section9DeleteEdge]
        exact ⟨hcomp.1.1.2.1.vertexSet_mono,
          fun f hf => ⟨hcomp.1.1.2.1.edgeSet_mono hf.1, hf.2⟩⟩
      · simp only [S_comp', N', G_comp', G₁', edgeSet_section9DeleteEdge]
        ext f; simp only [mem_union, mem_sdiff, mem_singleton_iff]
        refine ⟨?_, fun ⟨hf_comp, hfe⟩ => by
          rw [← hcomp.1.1.2.2.2.1] at hf_comp; exact hf_comp.imp id (fun hfN => ⟨hfN, hfe⟩)⟩
        rintro (hfS | ⟨hfN, hfe⟩)
        · exact ⟨hcomp.1.1.1.edgeSet_mono hfS, fun hfe => he_not_S (hfe ▸ hfS)⟩
        · exact ⟨hcomp.1.1.2.1.edgeSet_mono hfN, hfe⟩
      · exact hcomp.1.1.2.2.2.2.mono_right (section9DeleteEdge_le N.G e).edgeSet_mono
    have hP_le' : ∀ P ∈ P_set, P ≤ S_comp'.G := by
      intro P hP
      rw [(Compatible.of_le_le (hP_le P hP) (section9DeleteEdge_le S_comp.G e)).le_iff,
        edgeSet_section9DeleteEdge]
      refine ⟨(hP_le P hP).vertexSet_mono, fun f hf => ⟨(hP_le P hP).edgeSet_mono hf, ?_⟩⟩
      intro hfe; apply he_not_U
      rw [Society.transactionUnion, edgeSet_subgraphSUnion hP_le, mem_iUnion₂]
      exact ⟨P, hP, hfe ▸ hf⟩
    have hcrooked' : S_comp'.IsCrookedTransaction P_set :=
      S_comp.isCrookedTransaction_of_omega_eq rfl hP_le hP_le' hcrooked
    have hEU_eq : E(S_comp'.transactionUnion P_set) = E(S_comp.transactionUnion P_set) := by
      rw [Society.transactionUnion, Society.transactionUnion,
        edgeSet_subgraphSUnion hP_le', edgeSet_subgraphSUnion hP_le]
    have hEN_lt : E(N'.G).ncard < E(N.G).ncard := by
      change E(section9DeleteEdge N.G e).ncard < E(N.G).ncard
      rw [edgeSet_section9DeleteEdge, ncard_sdiff_singleton_of_mem heN]
      have : 0 < E(N.G).ncard := (ncard_pos N.finite_E).mpr ⟨e, heN⟩
      omega
    have hw_le := hle_weight N' S_comp' P_set ⟨hcomp', rural_deleteEdge N hrural e, hcrooked',
      hcard⟩
    unfold section9Weight at hw_le
    change 2 * V(N.G).ncard - N.Ω.bar.ncard +
      2 * (E(N.G).ncard + E(S_comp.transactionUnion P_set).ncard) ≤
      2 * V(N.G).ncard - N.Ω.bar.ncard +
      2 * (E(N'.G).ncard + E(S_comp'.transactionUnion P_set).ncard) at hw_le
    rw [hEU_eq] at hw_le; omega
  refine ⟨hEN_sub, fun v ⟨hvN, hv_not_S⟩ => ?_⟩
  by_contra hv_not_U
  have hiso_N : ∀ e : β, ¬ N.G.Inc e v := by
    intro e hinc
    have heU : e ∈ E(S_comp.transactionUnion P_set) := hEN_sub hinc.edge_mem
    have hinc_comp : S_comp.G.Inc e v := hinc.mono hcomp.1.1.2.1
    rw [Society.transactionUnion, edgeSet_subgraphSUnion hP_le, mem_iUnion₂] at heU
    rcases heU with ⟨P, hP, heP⟩
    obtain ⟨x, y, hxyP⟩ := P.exists_isLink_of_mem_edgeSet heP
    rcases hinc_comp with ⟨w, hvw_comp⟩
    rcases hvw_comp.left_eq_or_eq (hxyP.mono (hP_le P hP)) with rfl | rfl
    · exact hv_not_U (mem_iUnion₂.mpr ⟨P, hP, hxyP.left_mem⟩)
    · exact hv_not_U (mem_iUnion₂.mpr ⟨P, hP, hxyP.right_mem⟩)
  have hiso_comp : ∀ e : β, ¬ S_comp.G.Inc e v := by
    intro e ⟨w, hvw⟩
    have he_comp : e ∈ E(S_comp.G) := hvw.edge_mem
    rw [← hcomp.1.1.2.2.2.1] at he_comp
    rcases he_comp with heS | heN
    · obtain ⟨x, y, hxyS⟩ := S.G.exists_isLink_of_mem_edgeSet heS
      rcases hvw.left_eq_or_eq (hxyS.mono hcomp.1.1.1) with rfl | rfl
      · exact hv_not_S hxyS.left_mem
      · exact hv_not_S hxyS.right_mem
    · obtain ⟨x, y, hxyN⟩ := N.G.exists_isLink_of_mem_edgeSet heN
      rcases hvw.left_eq_or_eq (hxyN.mono hcomp.1.1.2.1) with rfl | rfl
      · exact hiso_N e hxyN.inc_left
      · exact hiso_N e hxyN.inc_right
  have hv_not_Ω₀ : v ∉ N.Ω₀.bar := by
    intro hv₀
    have hv_in : v ∈ V(S.G) ∩ V(N.G) := by rw [← hcomp.2.2.2, ← hcomp.2.2.1]; exact hv₀
    exact hv_not_S hv_in.1
  let Y := N.Ω.bar \ {v}
  have hY_bar : Y ⊆ N.Ω.bar := sdiff_subset
  have hY_comp : Y ⊆ S_comp.Ω.bar := hcomp.2.1 ▸ hY_bar
  let G₁' := deleteVertices N.G {v}
  let G_comp' := deleteVertices S_comp.G {v}
  have hY_VN' : (N.Ω.restrict Y hY_bar).bar ⊆ V(G₁') := by
    rw [N.Ω.restrict_bar hY_bar]; exact fun z hz => ⟨N.bar_subset hz.1, hz.2⟩
  have hΩ₀_VN' : N.Ω₀.bar ⊆ V(G₁') :=
    fun z hz => ⟨N.bar₀_subset hz, fun hzv => hv_not_Ω₀ (hzv ▸ hz)⟩
  let N' : Neighborhood α β :=
    ⟨G₁', N.Ω.restrict Y hY_bar, N.Ω₀,
      N.finite_V.subset (deleteVertices_le N.G {v}).vertexSet_mono,
      N.finite_E.subset (deleteVertices_le N.G {v}).edgeSet_mono,
      hY_VN', hΩ₀_VN'⟩
  have hΩ'_Vcomp' : (S_comp.Ω.restrict Y hY_comp).bar ⊆ V(G_comp') := by
    rw [S_comp.Ω.restrict_bar hY_comp]; exact fun z hz => ⟨S_comp.bar_subset (hY_comp hz), hz.2⟩
  let S_comp' : Society α β :=
    ⟨G_comp', S_comp.Ω.restrict Y hY_comp,
      S_comp.finite_V.subset (deleteVertices_le S_comp.G {v}).vertexSet_mono,
      S_comp.finite_E.subset (deleteVertices_le S_comp.G {v}).edgeSet_mono,
      hΩ'_Vcomp'⟩
  have hEN'_eq : E(G₁') = E(N.G) := by
    ext e; simp only [G₁', deleteVertices, edgeSet_induce, mem_ofPred_eq, mem_sdiff,
      mem_singleton_iff]
    refine ⟨fun ⟨x, y, hxy, _, _⟩ => hxy.edge_mem, fun he => ?_⟩
    obtain ⟨x, y, hxy⟩ := N.G.exists_isLink_of_mem_edgeSet he
    exact ⟨x, y, hxy, ⟨hxy.left_mem, fun hxv => hiso_N e (hxv ▸ hxy.inc_left)⟩,
      ⟨hxy.right_mem, fun hyv => hiso_N e (hyv ▸ hxy.inc_right)⟩⟩
  have hEcomp'_eq : E(G_comp') = E(S_comp.G) := by
    ext e; simp only [G_comp', deleteVertices, edgeSet_induce, mem_ofPred_eq, mem_sdiff,
      mem_singleton_iff]
    refine ⟨fun ⟨x, y, hxy, _, _⟩ => hxy.edge_mem, fun he => ?_⟩
    obtain ⟨x, y, hxy⟩ := S_comp.G.exists_isLink_of_mem_edgeSet he
    exact ⟨x, y, hxy, ⟨hxy.left_mem, fun hxv => hiso_comp e (hxv ▸ hxy.inc_left)⟩,
      ⟨hxy.right_mem, fun hyv => hiso_comp e (hyv ▸ hxy.inc_right)⟩⟩
  have hcomp' : S_comp'.IsComposition S N' := by
    refine ⟨⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩, ?_, hcomp.2.2.1, ?_⟩
    · rw [(Compatible.of_le_le hcomp.1.1.1 (deleteVertices_le S_comp.G {v})).le_iff]
      exact ⟨fun z hz => ⟨hcomp.1.1.1.vertexSet_mono hz, fun hzv => hv_not_S (hzv ▸ hz)⟩,
        hEcomp'_eq.symm ▸ hcomp.1.1.1.edgeSet_mono⟩
    · rw [(Compatible.of_le_le ((deleteVertices_le N.G {v}).trans hcomp.1.1.2.1)
        (deleteVertices_le S_comp.G {v})).le_iff]
      exact ⟨fun z hz => ⟨hcomp.1.1.2.1.vertexSet_mono hz.1, hz.2⟩,
        hEcomp'_eq.symm ▸ hEN'_eq.symm ▸ hcomp.1.1.2.1.edgeSet_mono⟩
    · ext z; change z ∈ V(S.G) ∪ (V(N.G) \ {v}) ↔ z ∈ V(S_comp.G) \ {v}
      simp only [mem_union, mem_sdiff, mem_singleton_iff]
      refine ⟨?_, fun ⟨hz_comp, hzv⟩ => by
        rw [← hcomp.1.1.2.2.1] at hz_comp; exact hz_comp.imp id (fun hzN => ⟨hzN, hzv⟩)⟩
      rintro (hzS | ⟨hzN, hzv⟩)
      · exact ⟨hcomp.1.1.1.vertexSet_mono hzS, fun hzv => hv_not_S (hzv ▸ hzS)⟩
      · exact ⟨hcomp.1.1.2.1.vertexSet_mono hzN, hzv⟩
    · rw [hEN'_eq, hEcomp'_eq]; exact hcomp.1.1.2.2.2.1
    · rw [hEN'_eq]; exact hcomp.1.1.2.2.2.2
    · change (S_comp.Ω.restrict Y hY_comp).bar ⊆ V(G₁')
      rw [S_comp.Ω.restrict_bar hY_comp, ← N.Ω.restrict_bar hY_bar]; exact hY_VN'
    · change N.Ω.restrict Y hY_bar = S_comp.Ω.restrict Y hY_comp; simp_rw [← hcomp.2.1]
    · ext z; change z ∈ S.Ω.bar ↔ z ∈ V(S.G) ∧ (z ∈ V(N.G) ∧ z ≠ v)
      rw [hcomp.2.2.2, mem_inter_iff]
      exact ⟨fun ⟨hzS, hzN⟩ => ⟨hzS, hzN, fun hzv => hv_not_S (hzv ▸ hzS)⟩,
        fun ⟨hzS, hzN, _⟩ => ⟨hzS, hzN⟩⟩
  have hP_le' : ∀ P ∈ P_set, P ≤ S_comp'.G := by
    intro P hP
    rw [(Compatible.of_le_le (hP_le P hP) (deleteVertices_le S_comp.G {v})).le_iff]
    exact ⟨fun z hz => ⟨(hP_le P hP).vertexSet_mono hz,
      fun hzv => hv_not_U (mem_iUnion₂.mpr ⟨P, hP, hzv ▸ hz⟩)⟩,
      hEcomp'_eq.symm ▸ (hP_le P hP).edgeSet_mono⟩
  have hends_Y : S_comp.transactionEnds P_set ⊆ Y := by
    rintro z ⟨P, hP, b, hP_e⟩
    exact ⟨hcomp.2.1 ▸ hP_e.2.2.1,
      fun hzv => hv_not_U (mem_iUnion₂.mpr ⟨P, hP, hzv ▸ hP_e.1.left_mem⟩)⟩
  have hcrooked' : S_comp'.IsCrookedTransaction P_set :=
    (S_comp.restrictOmega Y hY_comp).isCrookedTransaction_of_omega_eq rfl hP_le hP_le'
      ((S_comp.isCrookedTransaction_restrictOmega_iff hY_comp).mpr ⟨hcrooked, hends_Y⟩)
  have hEU_eq : E(S_comp'.transactionUnion P_set) = E(S_comp.transactionUnion P_set) := by
    rw [Society.transactionUnion, Society.transactionUnion,
      edgeSet_subgraphSUnion hP_le', edgeSet_subgraphSUnion hP_le]
  have hVN'_eq : V(N'.G).ncard + 1 = V(N.G).ncard :=
    ncard_sdiff_singleton_add_one hvN N.finite_V
  have hbar'_le : N.Ω.bar.ncard ≤ N'.Ω.bar.ncard + 1 := by
    change N.Ω.bar.ncard ≤ (N.Ω.restrict Y hY_bar).bar.ncard + 1
    rw [N.Ω.restrict_bar hY_bar]
    change N.Ω.bar.ncard ≤ (N.Ω.bar \ {v}).ncard + 1
    by_cases hv_bar : v ∈ N.Ω.bar
    · rw [ncard_sdiff_singleton_add_one hv_bar N.Ω.finite_bar]
    · rw [sdiff_eq_left.mpr (disjoint_singleton_right.mpr hv_bar)]; omega
  have hVN'_ge_bar' : N'.Ω.bar.ncard ≤ V(N'.G).ncard := ncard_le_ncard N'.bar_subset N'.finite_V
  have hw_le := hle_weight N' S_comp' P_set
    ⟨hcomp', rural_deleteIsolatedVertex N hrural hv_not_Ω₀, hcrooked', hcard⟩
  unfold section9Weight at hw_le
  have hEN_ncard : E(N'.G).ncard = E(N.G).ncard := by
    change E(G₁').ncard = E(N.G).ncard; rw [hEN'_eq]
  rw [hEN_ncard, hEU_eq] at hw_le; omega

/-! ## Proof of Claim (4) (page 62) -/

/-- If `c ∈ pathInternalVerts S.G P ∩ S.Ω.bar` for some `P ∈ P_set` in a transaction `P_set`, then
`section9SingleVertex S.G c` is an attachment to `P_set` with foot `c` and leg `P`. -/
theorem isAttachmentWithEnds_section9SingleVertex (S : Society α β)
    {P_set : Set (Graph α β)} {P : Graph α β} {c : α}
    (hdisj : S.IsDisjointOmegaPathSet P_set) (hP_in : P ∈ P_set)
    (hc_int : c ∈ pathInternalVerts S.G P) (hc_bar : c ∈ S.Ω.bar) :
    S.IsAttachmentWithEnds P_set (section9SingleVertex S.G c) c c := by
  obtain ⟨a, b, hP_ends⟩ := hdisj.1 P hP_in
  have hcP : c ∈ V(P) := hc_int.1
  have hcG : c ∈ V(S.G) := hP_ends.1.le.vertexSet_mono hcP
  have hcU : c ∈ V(S.transactionUnion P_set) := mem_iUnion₂.mpr ⟨P, hP_in, hcP⟩
  have hc_not_ends : c ∉ S.transactionEnds P_set := by
    rintro ⟨R, hR_in, d, hR_ends⟩
    by_cases hRP : R = P
    · subst hRP; exact hc_int.2 ⟨d, hR_ends.1⟩
    · exact disjoint_left.mp (hdisj.2 hP_in hR_in (Ne.symm hRP)) hcP hR_ends.1.left_mem
  exact ⟨isGraphPathWithEnds_section9SingleVertex hcG, by ext z; simp [hcU],
    by ext z; simp [hc_bar, hc_not_ends]⟩

/-- If `section9SingleVertex S.G c` (`c ∈ pathInternalVerts S.G P ∩ S.Ω.bar`, `P ∈ P_set`) is an
exchangeable attachment to a crooked transaction `P_set`, then there is a crooked transaction
`P_set'` of the same cardinality with strictly fewer edges in `⋃ P_set'`. -/
theorem exists_lt_edges_of_isExchangeable_singleVertex (S : Society α β)
    {P_set : Set (Graph α β)} {P : Graph α β} {c : α}
    (hcrooked : S.IsCrookedTransaction P_set) (hP_in : P ∈ P_set)
    (hc_int : c ∈ pathInternalVerts S.G P) (hc_bar : c ∈ S.Ω.bar)
    (hexch : S.IsExchangeableAttachment P_set (section9SingleVertex S.G c)) :
    ∃ P_set' : Set (Graph α β), S.IsCrookedTransaction P_set' ∧
      P_set'.ncard = P_set.ncard ∧
      E(S.transactionUnion P_set').ncard < E(S.transactionUnion P_set).ncard := by
  obtain ⟨A, B, hfence⟩ := hcrooked.1
  let Q_c := section9SingleVertex S.G c
  have hatt_c : S.IsAttachmentWithEnds P_set Q_c c c :=
    isAttachmentWithEnds_section9SingleVertex S hfence.1 hP_in hc_int hc_bar
  rcases hexch with ⟨_, L, L', ⟨hL_in, b, u, a₁, b₁, hatt_bu, hbL, hL_ends, Q, hQ_or, rfl⟩, hcr'⟩
  have hbc : b = c := by
    have hbQ : b ∈ V(Q_c) := hatt_bu.1.left_mem
    rwa [vertexSet_section9SingleVertex, mem_singleton_iff] at hbQ
  have huc : u = c := by
    have huQ : u ∈ V(Q_c) := hatt_bu.1.right_mem
    rwa [vertexSet_section9SingleVertex, mem_singleton_iff] at huQ
  rcases hbc with rfl; rcases huc with rfl
  have hLP : L = P := by
    by_contra hne; exact disjoint_left.mp (hfence.1.2 hL_in hP_in hne) hbL hc_int.1
  subst hLP
  let P_set' := (P_set \ {L}) ∪ {subgraphUnion S.G Q_c Q}
  have hnot_diff : subgraphUnion S.G Q_c Q ∉ P_set \ {L} :=
    Society.IsAttachmentWithEnds.subgraphUnion_not_mem_sdiff S hfence.1 hatt_c hL_in hbL
  have hfin_P : P_set.Finite := hfence.1.finite S
  have hcard_eq : P_set'.ncard = P_set.ncard := by
    change ((P_set \ {L}) ∪ {subgraphUnion S.G Q_c Q}).ncard = P_set.ncard
    rw [union_comm, ← insert_eq, ncard_insert_of_notMem hnot_diff (hfin_P.subset sdiff_subset),
      ncard_sdiff_singleton_add_one hL_in hfin_P]
  have hR_le : ∀ R ∈ P_set, R ≤ S.G := fun R hR => by
    obtain ⟨_, _, h⟩ := hfence.1.1 R hR; exact h.1.le
  have hQc_le : Q_c ≤ S.G := hatt_c.1.le
  have hQ_L : Q ≤ L := by rcases hQ_or with h | h <;> exact h.le
  have hQ_le : Q ≤ S.G := hQ_L.trans (hR_le L hL_in)
  have hL'_le : subgraphUnion S.G Q_c Q ≤ S.G := subgraphUnion_le hQc_le hQ_le
  have hR'_le : ∀ R ∈ P_set', R ≤ S.G := by rintro R (hR | rfl); exacts [hR_le R hR.1, hL'_le]
  have hca₁ : u ≠ a₁ := fun h => hc_int.2 (h ▸ ⟨b₁, hL_ends.1⟩)
  have hcb₁ : u ≠ b₁ := fun h => hc_int.2 (h ▸ ⟨a₁, hL_ends.1.symm⟩)
  have hex_missing : ∃ e₀ ∈ E(L), e₀ ∉ E(Q) := by
    by_contra! hall
    have hEQ_eq : E(Q) = E(L) := Subset.antisymm hQ_L.edgeSet_mono hall
    have hVQ_eq : V(Q) = V(L) := by
      refine Subset.antisymm hQ_L.vertexSet_mono (fun v hvL => ?_)
      obtain ⟨e, heL, _, hlink⟩ := hL_ends.1.exists_inc_of_mem_of_ne hL_ends.2.1 hvL
      obtain ⟨x, y, hxyQ⟩ := Q.exists_isLink_of_mem_edgeSet (hEQ_eq ▸ heL)
      rcases hlink.left_eq_or_eq (hxyQ.mono hQ_L) with rfl | rfl
      · exact hxyQ.left_mem
      · exact hxyQ.right_mem
    have hQL_eq : Q = L := (Compatible.of_le_le hQ_L le_rfl).ext hVQ_eq hEQ_eq
    subst hQL_eq
    rcases hQ_or with hQ_ba₁ | hQ_bb₁
    · rcases (hQ_ba₁.mono hL_ends.1.le).ends_eq hL_ends.1 with ⟨h1, _⟩ | ⟨_, h2⟩
      · exact hca₁ h1.symm
      · exact hcb₁ h2.symm
    · rcases (hQ_bb₁.mono hL_ends.1.le).ends_eq hL_ends.1 with ⟨h1, _⟩ | ⟨_, h2⟩
      · exact hca₁ h1.symm
      · exact hcb₁ h2.symm
  obtain ⟨e₀, he₀_L, he₀_not_Q⟩ := hex_missing
  have hE_sub : E(S.transactionUnion P_set') ⊆ E(S.transactionUnion P_set) := by
    rw [Society.transactionUnion, Society.transactionUnion,
      edgeSet_subgraphSUnion hR'_le, edgeSet_subgraphSUnion hR_le]
    intro e he; rw [mem_iUnion₂] at he ⊢
    rcases he with ⟨R, hR | rfl, heR⟩
    · exact ⟨R, hR.1, heR⟩
    · rw [edgeSet_subgraphUnion hQc_le hQ_le, edgeSet_section9SingleVertex, empty_union] at heR
      exact ⟨L, hL_in, hQ_L.edgeSet_mono heR⟩
  have he₀_in_U : e₀ ∈ E(S.transactionUnion P_set) := by
    rw [Society.transactionUnion, edgeSet_subgraphSUnion hR_le, mem_iUnion₂]; exact ⟨L, hL_in,
      he₀_L⟩
  have he₀_not_U' : e₀ ∉ E(S.transactionUnion P_set') := by
    rw [Society.transactionUnion, edgeSet_subgraphSUnion hR'_le, mem_iUnion₂]
    rintro ⟨R, hR | rfl, he₀R⟩
    · obtain ⟨x, y, hxyL⟩ := L.exists_isLink_of_mem_edgeSet he₀_L
      obtain ⟨u_R, v_R, huvR⟩ := R.exists_isLink_of_mem_edgeSet he₀R
      have hne_LR : L ≠ R := fun h => hR.2 h.symm
      rcases (hxyL.mono (hR_le L hL_in)).left_eq_or_eq (huvR.mono (hR_le R hR.1)) with rfl | rfl
      · exact disjoint_left.mp (hfence.1.2 hL_in hR.1 hne_LR) hxyL.left_mem huvR.left_mem
      · exact disjoint_left.mp (hfence.1.2 hL_in hR.1 hne_LR) hxyL.left_mem huvR.right_mem
    · rw [edgeSet_subgraphUnion hQc_le hQ_le, edgeSet_section9SingleVertex, empty_union] at he₀R
      exact he₀_not_Q he₀R
  have hEU_fin : E(S.transactionUnion P_set).Finite :=
    S.finite_E.subset (subgraphSUnion_le hR_le).edgeSet_mono
  exact ⟨P_set', hcr', hcard_eq,
    ncard_lt_ncard ⟨hE_sub, fun h_all => he₀_not_U' (h_all he₀_in_U)⟩ hEU_fin⟩

/-- First part of Claim (4) (page 62): in a minimum-weight Section 9 configuration, each `P ∈ P_set`
has at most one internal vertex in `S_comp.Ω.bar`, and for such a vertex `c`, `P` is an overpass of
`P_set` and both subpaths `Q₁, Q₂` of `P` from `c` to the ends of `P` are non-separating `Ω`-paths
in `S_comp`. -/
theorem lemma_9_1_claim_4_nonSeparating {S : Society α β} {p : ℕ}
    {N : Neighborhood α β} {S_comp : Society α β} {P_set : Set (Graph α β)}
    (hmin : IsMinSection9Config S p N S_comp P_set) {P : Graph α β} (hP_in : P ∈ P_set) :
    (pathInternalVerts S_comp.G P ∩ S_comp.Ω.bar).Subsingleton ∧
      ∀ c ∈ pathInternalVerts S_comp.G P ∩ S_comp.Ω.bar, S_comp.IsOverpass P_set P ∧
        ∀ {a b : α} {Q : Graph α β}, S_comp.IsOmegaPathWithEnds P a b → Q ≤ P →
          (IsGraphPathWithEnds P Q c a ∨ IsGraphPathWithEnds P Q c b) →
          S_comp.IsNonSeparatingOmegaPath Q := by
  rcases hmin with ⟨⟨hcomp, hrural, hcrooked, hcard⟩, hle_weight⟩
  obtain ⟨A, B, hfence⟩ := hcrooked.1
  have hR_le : ∀ R ∈ P_set, R ≤ S_comp.G := fun R hR => by
    obtain ⟨_, _, h⟩ := hfence.1.1 R hR; exact h.1.le
  have hnot_exch : ∀ c ∈ pathInternalVerts S_comp.G P ∩ S_comp.Ω.bar,
      ¬ S_comp.IsExchangeableAttachment P_set (section9SingleVertex S_comp.G c) := by
    intro c ⟨hc_int, hc_bar⟩ hexch
    obtain ⟨P_set', hcr', hcard', hlt_E⟩ :=
      exists_lt_edges_of_isExchangeable_singleVertex S_comp hcrooked hP_in hc_int hc_bar hexch
    have hw_le := hle_weight N S_comp P_set' ⟨hcomp, hrural, hcr', hcard' ▸ hcard⟩
    unfold section9Weight at hw_le; omega
  have hsub : (pathInternalVerts S_comp.G P ∩ S_comp.Ω.bar).Subsingleton := by
    intro c₁ hc₁ c₂ hc₂; by_contra hc12
    let Q₁ := section9SingleVertex S_comp.G c₁
    let Q₂ := section9SingleVertex S_comp.G c₂
    have hatt₁ : S_comp.IsAttachment P_set Q₁ :=
      ⟨c₁, c₁, isAttachmentWithEnds_section9SingleVertex S_comp hfence.1 hP_in hc₁.1 hc₁.2⟩
    have hatt₂ : S_comp.IsAttachment P_set Q₂ :=
      ⟨c₂, c₂, isAttachmentWithEnds_section9SingleVertex S_comp hfence.1 hP_in hc₂.1 hc₂.2⟩
    have hdisj_12 : Disjoint V(Q₁) V(Q₂) := by simp [Q₁, Q₂, hc12]
    obtain ⟨P₁, hP₁_in, _, _, _, b, b', hb_foot, hbP₁, hb'_foot, hb'P₁,
        M, hMP₁, hM_path, P_set', hcr', hcard', hunion_le, hdisj_EM⟩ :=
      S_comp.theorem_3_3_proof hcrooked hatt₁ (hnot_exch c₁ hc₁) hatt₂ (hnot_exch c₂ hc₂) hdisj_12
    have hbc₁ : b = c₁ := by
      rcases hb_foot with ⟨u, hatt_bu⟩; have hbQ₁ : b ∈ V(Q₁) := hatt_bu.1.left_mem
      rwa [vertexSet_section9SingleVertex, mem_singleton_iff] at hbQ₁
    have hb'c₂ : b' = c₂ := by
      rcases hb'_foot with ⟨u', hatt'_b'u'⟩; have hb'Q₂ : b' ∈ V(Q₂) := hatt'_b'u'.1.left_mem
      rwa [vertexSet_section9SingleVertex, mem_singleton_iff] at hb'Q₂
    obtain ⟨e_M, he_M, _⟩ := hM_path.exists_inc_left_of_ne (hbc₁.symm ▸ hb'c₂.symm ▸ hc12)
    have hU_le : S_comp.transactionUnion P_set ≤ S_comp.G := subgraphSUnion_le hR_le
    have hQ₁_le : Q₁ ≤ S_comp.G :=
      section9SingleVertex_le ((hR_le P hP_in).vertexSet_mono hc₁.1.1)
    have hQ₂_le : Q₂ ≤ S_comp.G :=
      section9SingleVertex_le ((hR_le P hP_in).vertexSet_mono hc₂.1.1)
    have hQ12_le : subgraphUnion S_comp.G Q₁ Q₂ ≤ S_comp.G := subgraphUnion_le hQ₁_le hQ₂_le
    have hE_sub : E(S_comp.transactionUnion P_set') ⊆ E(S_comp.transactionUnion P_set) := by
      intro e he; have he' := hunion_le.edgeSet_mono he
      rw [edgeSet_subgraphUnion hU_le hQ12_le, edgeSet_subgraphUnion hQ₁_le hQ₂_le,
        edgeSet_section9SingleVertex, edgeSet_section9SingleVertex, union_self, union_empty] at he'
      exact he'
    have heM_in_U : e_M ∈ E(S_comp.transactionUnion P_set) := by
      rw [Society.transactionUnion, edgeSet_subgraphSUnion hR_le, mem_iUnion₂]
      exact ⟨P₁, hP₁_in, hMP₁.edgeSet_mono he_M⟩
    have heM_not_U' : e_M ∉ E(S_comp.transactionUnion P_set') := disjoint_left.mp hdisj_EM he_M
    have hlt_E : E(S_comp.transactionUnion P_set').ncard <
        E(S_comp.transactionUnion P_set).ncard :=
      ncard_lt_ncard ⟨hE_sub, fun h_all => heM_not_U' (h_all heM_in_U)⟩
        (S_comp.finite_E.subset hU_le.edgeSet_mono)
    have hw_le := hle_weight N S_comp P_set' ⟨hcomp, hrural, hcr', by omega⟩
    unfold section9Weight at hw_le; omega
  refine ⟨hsub, fun c hc => ?_⟩
  let Q_c := section9SingleVertex S_comp.G c
  have hatt_cc : S_comp.IsAttachmentWithEnds P_set Q_c c c :=
    isAttachmentWithEnds_section9SingleVertex S_comp hfence.1 hP_in hc.1 hc.2
  obtain ⟨_, P₁, hleg, hover⟩ :=
    S_comp.theorem_3_2_proof hcrooked ⟨c, c, hatt_cc⟩ (hnot_exch c hc)
  have hP₁_eq : P₁ = P := by
    rcases hleg with ⟨hP₁_in, b, ⟨u, hatt_bu⟩, hbP₁⟩
    have hbc : b = c := by
      have hbQ : b ∈ V(Q_c) := hatt_bu.1.left_mem
      rwa [vertexSet_section9SingleVertex, mem_singleton_iff] at hbQ
    subst hbc; by_contra hne; exact disjoint_left.mp (hfence.1.2 hP₁_in hP_in hne) hbP₁ hc.1.1
  subst hP₁_eq
  refine ⟨hover, fun {a b Q} hP_ends hQP hQ_or => ?_⟩
  obtain ⟨a₁_raw, ha₁_raw, b₁_raw, hb₁_raw, hP_ends_raw⟩ := hfence.2.2 P₁ hP_in
  rcases hover with ⟨_, _, R₁, hR₁_in, R₂, hR₂_in, hR12, hper₁, hper₂⟩
  obtain ⟨x₁, hx₁, y₁, hy₁, hR₁_ends⟩ := hfence.2.2 R₁ hR₁_in.1
  obtain ⟨x₂, hx₂, y₂, hy₂, hR₂_ends⟩ := hfence.2.2 R₂ hR₂_in.1
  let W' := S_comp.transactionEnds (P_set \ {P₁})
  have hW'_bar : W' ⊆ S_comp.Ω.bar := S_comp.transactionEnds_subset_bar (P_set \ {P₁})
  have hx₁W' : x₁ ∈ A ∩ W' := ⟨hx₁, hR₁_ends.mem_transactionEnds_left S_comp hR₁_in⟩
  have hy₁W' : y₁ ∈ B ∩ W' := ⟨hy₁, hR₁_ends.mem_transactionEnds_right S_comp hR₁_in⟩
  have hx₂W' : x₂ ∈ A ∩ W' := ⟨hx₂, hR₂_ends.mem_transactionEnds_left S_comp hR₂_in⟩
  have hy₂W' : y₂ ∈ B ∩ W' := ⟨hy₂, hR₂_ends.mem_transactionEnds_right S_comp hR₂_in⟩
  have hper₁' := (hR₁_ends.isPeripheralIn_iff S_comp hR₁_in).mp hper₁
  have hper₂' := (hR₂_ends.isPeripheralIn_iff S_comp hR₂_in).mp hper₂
  have hdisj_R12 : Disjoint V(R₁) V(R₂) := hfence.1.2 hR₁_in.1 hR₂_in.1 hR12
  have hx12 : x₁ ≠ x₂ :=
    fun h => disjoint_left.mp hdisj_R12 hR₁_ends.1.left_mem (h ▸ hR₂_ends.1.left_mem)
  have hy12 : y₁ ≠ y₂ :=
    fun h => disjoint_left.mp hdisj_R12 hR₁_ends.1.right_mem (h ▸ hR₂_ends.1.right_mem)
  have hex_boundary :
      ∃ a_0 ∈ A ∩ W', ∃ a'_0 ∈ A ∩ W', ∃ b_0 ∈ B ∩ W', ∃ b'_0 ∈ B ∩ W',
        Disjoint (S_comp.Ω.interval a'_0 b_0) W' ∧
        Disjoint (S_comp.Ω.interval b'_0 a_0) W' ∧
        (∃ R_ab ∈ P_set \ {P₁}, S_comp.IsOmegaPathWithEnds R_ab a'_0 b_0) ∧
        (∃ R_ba ∈ P_set \ {P₁}, S_comp.IsOmegaPathWithEnds R_ba a_0 b'_0) := by
    rcases hper₁' with hd₁ | hd₁ <;> rcases hper₂' with hd₂ | hd₂
    · exact (hx12 (S_comp.Ω.unique_empty_interval_AB_of_isFence hfence.2.1 hW'_bar
        hx₁W' hy₁W' hx₂W' hy₂W' hd₁ hd₂).1).elim
    · exact ⟨x₂, hx₂W', x₁, hx₁W', y₁, hy₁W', y₂, hy₂W', hd₁, hd₂,
        ⟨R₁, hR₁_in, hR₁_ends⟩, ⟨R₂, hR₂_in, hR₂_ends⟩⟩
    · exact ⟨x₁, hx₁W', x₂, hx₂W', y₂, hy₂W', y₁, hy₁W', hd₂, hd₁,
        ⟨R₂, hR₂_in, hR₂_ends⟩, ⟨R₁, hR₁_in, hR₁_ends⟩⟩
    · exact (hy12 (S_comp.Ω.unique_empty_interval_AB_of_isFence hfence.2.1.symm hW'_bar
        hy₁W' hx₁W' hy₂W' hx₂W' hd₁ hd₂).1).elim
  obtain ⟨a_0, ha_0, a'_0, ha'_0, b_0, hb_0, b'_0, hb'_0, hd_ab, hd_ba,
    ⟨R_ab, hR_ab_in, hR_ab_ends⟩, ⟨R_ba, hR_ba_in, hR_ba_ends⟩⟩ := hex_boundary
  have h_e_G₁ := S_comp.mem_interval_of_peripheral_diff_singleton hfence hcrooked hP_in hR_ab_in
    ha₁_raw hb₁_raw hP_ends_raw ha'_0.1 hb_0.1 hR_ab_ends hd_ab
  have hfence_BA : S_comp.IsFenceFor P_set B A :=
    ⟨hfence.1, hfence.2.1.symm, fun R hR => by
      obtain ⟨a_e, ha_e, b_e, hb_e, hR_e⟩ := hfence.2.2 R hR
      exact ⟨b_e, hb_e, a_e, ha_e, hR_e.symm S_comp⟩⟩
  have h_e_G₂ := S_comp.mem_interval_of_peripheral_diff_singleton hfence_BA hcrooked hP_in hR_ba_in
    hb₁_raw ha₁_raw (hP_ends_raw.symm S_comp) hb'_0.1 ha_0.1 (hR_ba_ends.symm S_comp) hd_ba
  obtain ⟨_, _, hG₂_sub, hG₁_sub, hdisj_P, _⟩ :=
    Society.four_arc_partition hfence.2.1 hW'_bar ha_0 ha'_0 hb_0 hb'_0 hd_ab hd_ba
  have hdisj_G₁G₂ : Disjoint (S_comp.Ω.interval a'_0 b_0) (S_comp.Ω.interval b'_0 a_0) :=
    hdisj_P.symm.mono (hG₁_sub.trans subset_union_right) (hG₂_sub.trans subset_union_right)
  have hex_ends : ∃ e₁ e₂ : α, S_comp.IsOmegaPathWithEnds P₁ e₁ e₂ ∧
      e₁ ∈ S_comp.Ω.interval a'_0 b_0 ∧ e₂ ∈ S_comp.Ω.interval b'_0 a_0 := by
    rcases h_e_G₁ with ⟨ha₁_G₁, _⟩ | ⟨hb₁_G₁, _⟩ <;>
    rcases h_e_G₂ with ⟨hb₁_G₂, _⟩ | ⟨ha₁_G₂, _⟩
    · exact ⟨a₁_raw, b₁_raw, hP_ends_raw, ha₁_G₁, hb₁_G₂⟩
    · exact (disjoint_left.mp hdisj_G₁G₂ ha₁_G₁ ha₁_G₂).elim
    · exact (disjoint_left.mp hdisj_G₁G₂ hb₁_G₁ hb₁_G₂).elim
    · exact ⟨b₁_raw, a₁_raw, hP_ends_raw.symm S_comp, hb₁_G₁, ha₁_G₂⟩
  obtain ⟨e₁, e₂, hP_e12, he₁_G₁, he₂_G₂⟩ := hex_ends
  have hc_gaps := S_comp.end_not_mem_gaps_of_not_exchangeable hcrooked hfence hatt_cc
    (hnot_exch c hc) hP_in hc.1.1 hP_e12 W' rfl ha_0 ha'_0 hb_0 hb'_0 hd_ab hd_ba he₁_G₁ he₂_G₂
  have hc_not_W' : c ∉ W' := fun hcW' =>
    hatt_cc.end_not_mem_transactionEnds S_comp
      (by rcases hcW' with ⟨R, hR, d, hR_e⟩; exact ⟨R, hR.1, d, hR_e⟩)
  have hc_b0a'0 : c ∈ S_comp.Ω.interval b_0 a'_0 := by
    have ha'_ne_b0 : a'_0 ≠ b_0 := fun h => disjoint_left.mp hfence.2.1.2.2.1 ha'_0.1 (h ▸ hb_0.1)
    exact (S_comp.Ω.mem_interval_or_interval_swap (hW'_bar ha'_0.2) (hW'_bar hb_0.2) hc.2
      ha'_ne_b0 (fun h => hc_not_W' (h ▸ ha'_0.2)) (fun h => hc_not_W'
        (h ▸ hb_0.2))).resolve_left hc_gaps.1
  have hc_a0b'0 : c ∈ S_comp.Ω.interval a_0 b'_0 := by
    have hb'_ne_a0 : b'_0 ≠ a_0 := fun h => disjoint_left.mp hfence.2.1.2.2.1 ha_0.1 (h ▸ hb'_0.1)
    exact (S_comp.Ω.mem_interval_or_interval_swap (hW'_bar hb'_0.2) (hW'_bar ha_0.2) hc.2
      hb'_ne_a0 (fun h => hc_not_W' (h ▸ hb'_0.2)) (fun h => hc_not_W'
        (h ▸ ha_0.2))).resolve_left hc_gaps.2
  have hce₁ : c ≠ e₁ := fun h => hc.1.2 (h ▸ ⟨e₂, hP_e12.1⟩)
  have hce₂ : c ≠ e₂ := fun h => hc.1.2 (h ▸ ⟨e₁, hP_e12.1.symm⟩)
  have hQ_ends_e : IsGraphPathWithEnds P₁ Q c e₁ ∨ IsGraphPathWithEnds P₁ Q c e₂ := by
    rcases hP_ends.ends_eq S_comp hP_e12 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩; exacts [hQ_or, hQ_or.symm]
  rcases hQ_ends_e with hQ_ce₁ | hQ_ce₂
  · have hQ_omega : S_comp.IsOmegaPathWithEnds Q c e₁ :=
      ⟨hQ_ce₁.mono hP_e12.1.le, hce₁, hc.2, hP_e12.2.2.1⟩
    exact ⟨⟨c, e₁, hQ_omega⟩, R_ab,
      (hfence.1.2 hR_ab_in.1 hP_in hR_ab_in.2).mono_right hQP.vertexSet_mono,
      a'_0, b_0, c, e₁, hR_ab_ends, hQ_omega,
      S_comp.Ω.crosses_iff_interval.mpr (Or.inr ⟨he₁_G₁, hc_b0a'0⟩)⟩
  · have hQ_omega : S_comp.IsOmegaPathWithEnds Q c e₂ :=
      ⟨hQ_ce₂.mono hP_e12.1.le, hce₂, hc.2, hP_e12.2.2.2⟩
    exact ⟨⟨c, e₂, hQ_omega⟩, R_ba,
      (hfence.1.2 hR_ba_in.1 hP_in hR_ba_in.2).mono_right hQP.vertexSet_mono,
      a_0, b'_0, c, e₂, hR_ba_ends, hQ_omega,
      S_comp.Ω.crosses_iff_interval.mpr (Or.inl ⟨hc_a0b'0, he₂_G₂⟩)⟩

/-- If `Q ≤ S_comp.G` is a path of positive length (has ends `x ≠ y`) in a composition
`S_comp.IsComposition S N` and `¬ Q ≤ N.G`, then `Q` has an edge in `E(S.G)`. -/
theorem nonempty_edgeSet_inter_of_not_le_right {S S_comp : Society α β} {N : Neighborhood α β}
    {Q : Graph α β} {x y : α} (hcomp : S_comp.IsComposition S N)
    (hQ : IsGraphPathWithEnds S_comp.G Q x y) (hxy : x ≠ y) (hnot_le : ¬ Q ≤ N.G) :
    (E(Q) ∩ E(S.G)).Nonempty := by
  by_contra h_empty
  rw [not_nonempty_iff_eq_empty, ← disjoint_iff_inter_eq_empty] at h_empty
  apply hnot_le; rw [(Compatible.of_le_le hQ.le hcomp.1.1.2.1).le_iff]
  have hEQ : E(Q) ⊆ E(N.G) := fun e heQ => by
    have he_comp : e ∈ E(S_comp.G) := hQ.le.edgeSet_mono heQ
    rw [← hcomp.1.1.2.2.2.1] at he_comp
    exact he_comp.resolve_left (fun heS => disjoint_left.mp h_empty heQ heS)
  refine ⟨fun v hvQ => ?_, hEQ⟩
  obtain ⟨e, heQ, z, hvzQ⟩ := hQ.exists_inc_of_mem_of_ne hxy hvQ
  obtain ⟨u, w, huwN⟩ := N.G.exists_isLink_of_mem_edgeSet (hEQ heQ)
  rcases (hvzQ.mono hQ.le).left_eq_or_eq (huwN.mono hcomp.1.1.2.1) with rfl | rfl
  · exact huwN.left_mem
  · exact huwN.right_mem

/-- Any two points `p₁, p₂` in a closed disc `Δ₀ ⊆ EuclideanPlane` are joined by a compact
connected subset `K₀ ⊆ Δ₀` that meets `subBd Δ₀` only in `{p₁, p₂}`. -/
theorem exists_compact_connected_in_disc_avoiding_bd {Δ₀ : Set EuclideanPlane}
    (hΔ₀ : IsClosedDisc Δ₀) {p₁ p₂ : EuclideanPlane} (hp₁ : p₁ ∈ Δ₀) (hp₂ : p₂ ∈ Δ₀) :
    ∃ K₀ : Set EuclideanPlane, IsCompact K₀ ∧ IsConnected K₀ ∧
      p₁ ∈ K₀ ∧ p₂ ∈ K₀ ∧ K₀ ⊆ Δ₀ ∧ K₀ ⊆ {p₁, p₂} ∪ interior Δ₀ := by
  obtain ⟨ψ₀⟩ := hΔ₀
  let z₁ : ClosedUnitDisc := ψ₀.symm ⟨p₁, hp₁⟩
  let z₂ : ClosedUnitDisc := ψ₀.symm ⟨p₂, hp₂⟩
  let clamp (t : ℝ) : ℝ := max 0 (min 1 t)
  have hclamp_cont : Continuous clamp :=
    continuous_const.max (continuous_const.min continuous_id)
  have hclamp_mem : ∀ (z : ClosedUnitDisc) (t : ℝ),
      clamp t • z.1 ∈ ClosedUnitDisc := by
    intro z t
    change clamp t • z.1 ∈ Metric.closedBall (0 : EuclideanPlane) 1
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs]
    have h0 : 0 ≤ clamp t := le_max_left 0 _
    have h1 : clamp t ≤ 1 := max_le (by norm_num) (min_le_left 1 t)
    have hz1 : ‖z.1‖ ≤ 1 := by
      have hz : z.1 ∈ Metric.closedBall (0 : EuclideanPlane) 1 := z.2
      rwa [Metric.mem_closedBall, dist_zero_right] at hz
    rw [abs_of_nonneg h0]
    exact (mul_le_of_le_one_left (norm_nonneg _) h1).trans hz1
  let seg (z : ClosedUnitDisc) (t : ℝ) : ClosedUnitDisc := ⟨clamp t • z.1, hclamp_mem z t⟩
  have hseg_cont : ∀ z : ClosedUnitDisc, Continuous (seg z) := fun z =>
    Continuous.subtype_mk (hclamp_cont.smul continuous_const) _
  have hclamp_Icc : ∀ {t : ℝ}, t ∈ Icc (0 : ℝ) 1 → clamp t = t := by
    intro t ht
    change max 0 (min 1 t) = t
    rw [min_eq_right ht.2, max_eq_right ht.1]
  let R : Set ClosedUnitDisc := seg z₁ '' Icc 0 1 ∪ seg z₂ '' Icc 0 1
  have hR_comp : IsCompact R :=
    (isCompact_Icc.image (hseg_cont z₁)).union (isCompact_Icc.image (hseg_cont z₂))
  have h0_Icc : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, by norm_num⟩
  have h1_Icc : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨by norm_num, le_rfl⟩
  have h0_mem : (0 : EuclideanPlane) ∈ ClosedUnitDisc := by
    rw [ClosedUnitDisc, Metric.mem_closedBall, dist_self]
    norm_num
  have hseg0 : ∀ z : ClosedUnitDisc, seg z 0 = ⟨0, h0_mem⟩ := by
    intro z; ext; simp [seg, clamp]
  have hseg1 : ∀ z : ClosedUnitDisc, seg z 1 = z := by
    intro z; ext; simp [seg, clamp]
  have hR_conn : IsConnected R := by
    refine IsConnected.union ?_
      ((isConnected_Icc (by norm_num)).image (seg z₁) (hseg_cont z₁).continuousOn)
      ((isConnected_Icc (by norm_num)).image (seg z₂) (hseg_cont z₂).continuousOn)
    refine ⟨seg z₁ 0, mem_image_of_mem (seg z₁) h0_Icc, ?_⟩
    rw [hseg0 z₁, ← hseg0 z₂]
    exact mem_image_of_mem (seg z₂) h0_Icc
  let ι : ClosedUnitDisc → EuclideanPlane := fun w => (ψ₀ w).1
  have hι_cont : Continuous ι := continuous_subtype_val.comp ψ₀.continuous
  refine ⟨ι '' R, hR_comp.image hι_cont, hR_conn.image ι hι_cont.continuousOn, ?_, ?_, ?_, ?_⟩
  · refine ⟨z₁, Or.inl ⟨1, h1_Icc, hseg1 z₁⟩, ?_⟩
    simp [ι, z₁]
  · refine ⟨z₂, Or.inr ⟨1, h1_Icc, hseg1 z₂⟩, ?_⟩
    simp [ι, z₂]
  · rintro _ ⟨w, _, rfl⟩; exact (ψ₀ w).2
  · have hbd_eq : subBd Δ₀ = discBd Δ₀ := subBd_eq_discBd_plane ⟨ψ₀⟩
    have hΔ₀_closed : IsClosed Δ₀ := (isCompact_of_isClosedDisc ⟨ψ₀⟩).isClosed
    have hint_eq : interior Δ₀ = Δ₀ \ subBd Δ₀ := by
      rw [subBd_eq_diff_interior_of_isClosed hΔ₀_closed]
      exact (sdiff_sdiff_right_self.trans (inf_eq_right.mpr interior_subset)).symm
    have hseg_int : ∀ (z : ClosedUnitDisc) {t : ℝ}, t ∈ Icc (0 : ℝ) 1 →
        ι (seg z t) = ι z ∨ ι (seg z t) ∈ interior Δ₀ := by
      intro z t ht
      rcases eq_or_lt_of_le ht.2 with rfl | hlt
      · left; rw [hseg1 z]
      · right
        rw [hint_eq, hbd_eq]
        refine ⟨(ψ₀ (seg z t)).2, ?_⟩
        intro hbd
        rw [disc_boundary Δ₀ ψ₀] at hbd
        obtain ⟨u, hu_bd, hu_eq⟩ := hbd
        have h_eq : seg z t = u := ψ₀.injective (Subtype.ext hu_eq.symm)
        have hu_norm : ‖u.1‖ = 1 := by
          change u.1 ∈ UnitCircle at hu_bd
          rwa [UnitCircle, Metric.mem_sphere, dist_zero_right] at hu_bd
        have hnorm1 : ‖(seg z t).1‖ = 1 := h_eq ▸ hu_norm
        change ‖clamp t • z.1‖ = 1 at hnorm1
        rw [hclamp_Icc ht, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1] at hnorm1
        have hz_le : ‖z.1‖ ≤ 1 := by
          have hz : z.1 ∈ Metric.closedBall (0 : EuclideanPlane) 1 := z.2
          rwa [Metric.mem_closedBall, dist_zero_right] at hz
        have h_lt1 : t * ‖z.1‖ < 1 := by
          rcases eq_or_lt_of_le ht.1 with rfl | hpos
          · norm_num
          · exact lt_of_le_of_lt (mul_le_of_le_one_right hpos.le hz_le) hlt
        linarith
    rintro _ ⟨w, ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩, rfl⟩
    · rcases hseg_int z₁ ht with h_eq | h_int
      · left; left; exact h_eq.trans (by simp [ι, z₁])
      · right; exact h_int
    · rcases hseg_int z₂ ht with h_eq | h_int
      · left; right; exact h_eq.trans (by simp [ι, z₂])
      · right; exact h_int

/-- If `R` is a path in `S_comp.G` with distinct ends `v₂ ≠ v₄` and `¬ R ≤ N.G`, then if
`v₂ ∈ N.Ω.bar` there is a subpath `R₁ ≤ R` with `R₁ ≤ N.G` from `v₂` to some `w₁ ∈ N.Ω₀.bar`. -/
theorem exists_subpath_to_left_of_not_le_right {S S_comp : Society α β} {N : Neighborhood α β}
    {R : Graph α β} {v₂ v₄ : α} (hcomp : S_comp.IsComposition S N)
    (hR : IsGraphPathWithEnds S_comp.G R v₂ v₄) (hv24 : v₂ ≠ v₄) (hnot_le : ¬ R ≤ N.G)
    (hv_bar : v₂ ∈ N.Ω.bar) :
    ∃ R₁ : Graph α β, ∃ w₁ ∈ N.Ω₀.bar,
      R₁ ≤ R ∧ R₁ ≤ N.G ∧ IsGraphPathWithEnds N.G R₁ v₂ w₁ := by
  obtain ⟨e₀, he₀R, he₀S⟩ := nonempty_edgeSet_inter_of_not_le_right hcomp hR hv24 hnot_le
  obtain ⟨x₀, y₀, hxy₀S⟩ := S.G.exists_isLink_of_mem_edgeSet he₀S
  obtain ⟨a₀, b₀, hab₀R⟩ := R.exists_isLink_of_mem_edgeSet he₀R
  have ha₀S : a₀ ∈ V(S.G) := by
    rcases (hab₀R.mono hR.le).left_eq_or_eq (hxy₀S.mono hcomp.1.1.1) with rfl | rfl
    · exact hxy₀S.left_mem
    · exact hxy₀S.right_mem
  obtain ⟨Q_va, _, hRa₀_le, _, hQ_va_comp, _, _, _, _⟩ := hR.exists_split_at hab₀R.left_mem
  obtain ⟨u₁, hu₁, w₁, hw₁S, R₁, hR₁_Qva, hft⟩ :=
    hQ_va_comp.exists_isFromToPathWithEnds (X := {v₂}) (Y := V(S.G))
      (mem_singleton v₂) ha₀S
  rw [mem_singleton_iff] at hu₁
  subst u₁
  have hR₁_R : R₁ ≤ R := hR₁_Qva.trans hRa₀_le
  have hR₁_comp : IsGraphPathWithEnds S_comp.G R₁ v₂ w₁ := hft.1.mono hR.le
  have hER₁_N : E(R₁) ⊆ E(N.G) := by
    intro f hf
    have hf_comp : f ∈ E(S_comp.G) := hR₁_comp.le.edgeSet_mono hf
    rw [← hcomp.1.1.2.2.2.1] at hf_comp
    rcases hf_comp with hfS | hfN
    · exfalso
      obtain ⟨x, y, hxyS⟩ := S.G.exists_isLink_of_mem_edgeSet hfS
      obtain ⟨x', y', hxyR₁⟩ := R₁.exists_isLink_of_mem_edgeSet hf
      have hx'S : x' ∈ V(S.G) := by
        rcases (hxyR₁.mono hR₁_comp.le).left_eq_or_eq (hxyS.mono hcomp.1.1.1) with rfl | rfl
        · exact hxyS.left_mem
        · exact hxyS.right_mem
      have hy'S : y' ∈ V(S.G) := by
        rcases (hxyR₁.symm.mono hR₁_comp.le).left_eq_or_eq (hxyS.mono hcomp.1.1.1) with rfl | rfl
        · exact hxyS.left_mem
        · exact hxyS.right_mem
      have hx'w₁ : x' = w₁ := by
        have hx'_in : x' ∈ V(R₁) ∩ V(S.G) := ⟨hxyR₁.left_mem, hx'S⟩
        rwa [hft.2.2, mem_singleton_iff] at hx'_in
      have hy'w₁ : y' = w₁ := by
        have hy'_in : y' ∈ V(R₁) ∩ V(S.G) := ⟨hxyR₁.right_mem, hy'S⟩
        rwa [hft.2.2, mem_singleton_iff] at hy'_in
      subst x'; subst y'
      exact hR₁_comp.not_isLoopAt hf w₁ (hxyR₁.mono hR₁_comp.le)
    · exact hfN
  have hVR₁_N : V(R₁) ⊆ V(N.G) := by
    intro z hz
    by_cases hzv : z = v₂
    · exact hzv ▸ N.bar_subset hv_bar
    · obtain ⟨Q₁, _, hQ₁, _, hp₁, _, _, _, _⟩ := hR₁_comp.exists_split_at hz
      obtain ⟨f, hf, w, hinc⟩ := hp₁.symm.exists_inc_left_of_ne hzv
      have hfN : f ∈ E(N.G) := hER₁_N (hQ₁.edgeSet_mono hf)
      obtain ⟨x, y, hxyN⟩ := N.G.exists_isLink_of_mem_edgeSet hfN
      rcases (hinc.mono (hQ₁.trans hR₁_comp.le)).left_eq_or_eq (hxyN.mono hcomp.1.1.2.1)
        with rfl | rfl
      · exact hxyN.left_mem
      · exact hxyN.right_mem
  have hR₁_N : R₁ ≤ N.G :=
    (Compatible.of_le_le hR₁_comp.le hcomp.1.1.2.1).le_iff.mpr ⟨hVR₁_N, hER₁_N⟩
  have hw₁_Ω₀ : w₁ ∈ N.Ω₀.bar := by
    rw [hcomp.2.2.1, hcomp.2.2.2]
    exact ⟨hw₁S, hVR₁_N hR₁_comp.right_mem⟩
  exact ⟨R₁, w₁, hw₁_Ω₀, hR₁_R, hR₁_N, hR₁_comp.of_le hR₁_N⟩

/-- Given a closed disc `Δ₀ ⊆ EuclideanPlane` and a boundary homeomorphism `φ₀ : Circle ≃ₜ subBd
Δ₀`,
the complement of `interior Δ₀` in the one-point compactification `OnePoint EuclideanPlane` is
contained in a closed disc `D_ext` with `discBd D_ext = OnePoint.some '' subBd Δ₀`. -/
theorem exists_exterior_disc_in_onePoint {Δ₀ : Set EuclideanPlane}
    (hΔ₀ : IsClosedDisc Δ₀) (φ₀ : Circle ≃ₜ subBd Δ₀) :
    ∃ D_ext : Set (OnePoint EuclideanPlane),
      IsClosedDisc D_ext ∧
      discBd D_ext = OnePoint.some '' subBd Δ₀ ∧
      ∀ x : EuclideanPlane, x ∉ interior Δ₀ → (x : OnePoint EuclideanPlane) ∈ D_ext := by
  let ι : EuclideanPlane → OnePoint EuclideanPlane := OnePoint.some
  have hι_emb : Topology.IsOpenEmbedding ι := OnePoint.isOpenEmbedding_coe
  have hι_cont : Continuous ι := OnePoint.continuous_coe
  have hι_inj : Function.Injective ι := OnePoint.coe_injective
  let F : Set (OnePoint EuclideanPlane) := ι '' subBd Δ₀
  let eF : subBd Δ₀ ≃ₜ F := hι_emb.isEmbedding.homeomorphImage (subBd Δ₀)
  have hF_oArc : IsOArc F := ⟨φ₀.trans eF⟩
  obtain ⟨Δ₁, Δ₂, _, hΔ₁, hΔ₂, hbd₁, hbd₂, huniv, hinter, _, huniq⟩ :=
    sphere_disc (OnePoint EuclideanPlane) ⟨Homeomorph.refl _⟩ F hF_oArc
  let D₀ : Set (OnePoint EuclideanPlane) := ι '' Δ₀
  have hΔ₀_comp : IsCompact Δ₀ := isCompact_of_isClosedDisc hΔ₀
  obtain ⟨ι', hι'_cont, hι'_left⟩ :=
    exists_inv_of_compactOn hΔ₀_comp hι_cont.continuousOn hι_inj.injOn
  obtain ⟨hD₀_disc, hD₀_bd⟩ := hΔ₀.image hι_cont.continuousOn hι'_cont hι'_left
  rw [← subBd_eq_discBd_plane hΔ₀] at hD₀_bd
  have hsub_compl : ∀ (D_ext : Set (OnePoint EuclideanPlane)),
      D₀ ∪ D_ext = univ → F ⊆ D_ext →
      ∀ x : EuclideanPlane, x ∉ interior Δ₀ → ι x ∈ D_ext := by
    intro D_ext huniv' hF_sub x hx_not_int
    have hmem : ι x ∈ D₀ ∪ D_ext := huniv' ▸ mem_univ (ι x)
    rcases hmem with ⟨y, hyΔ₀, hyx⟩ | hx_ext
    · have hxy : y = x := hι_inj hyx
      subst hxy
      have hx_bd : y ∈ subBd Δ₀ := by
        rw [subBd_eq_diff_interior_of_isClosed (isClosed_of_isClosedDisc hΔ₀)]
        exact ⟨hyΔ₀, hx_not_int⟩
      exact hF_sub (mem_image_of_mem ι hx_bd)
    · exact hx_ext
  rcases huniq D₀ hD₀_disc hD₀_bd with hD₀_eq | hD₀_eq
  · refine ⟨Δ₂, hΔ₂, hbd₂, hsub_compl Δ₂ (hD₀_eq.symm ▸ huniv) ?_⟩
    rw [← hinter]; exact inter_subset_right
  · refine ⟨Δ₁, hΔ₁, hbd₁, hsub_compl Δ₁ (hD₀_eq.symm ▸ union_comm Δ₁ Δ₂ ▸ huniv) ?_⟩
    rw [← hinter]; exact inter_subset_left

/-- Two compact connected subsets `V₁, V₂ ⊆ (interior Δ₀)ᶜ` whose endpoints on `subBd Δ₀` cross
with respect to `Ω₀` must intersect. -/
theorem nonempty_inter_of_crosses_on_inner_bd {G : Graph α β}
    {Γ : GraphDrawing G EuclideanPlane} {Ω₀ : CyclicPerm α} {Δ₀ : Set EuclideanPlane}
    (hΔ₀ : IsClosedDisc Δ₀) {φ₀ : Circle ≃ₜ subBd Δ₀}
    (hagrees₀ : DrawingAgreesWithOArcHomeo Γ Ω₀ (subBd Δ₀) φ₀)
    {v₁ v₃ v₂ v₄ : α} (hcr : Ω₀.Crosses v₁ v₃ v₂ v₄)
    {p₁ p₃ p₂ p₄ : EuclideanPlane}
    (hp₁ : p₁ ∈ graphDrawingVertexSet Γ v₁)
    (hp₃ : p₃ ∈ graphDrawingVertexSet Γ v₃)
    (hp₂ : p₂ ∈ graphDrawingVertexSet Γ v₂)
    (hp₄ : p₄ ∈ graphDrawingVertexSet Γ v₄)
    {V₁ V₂ : Set EuclideanPlane}
    (hV₁_comp : IsCompact V₁) (hV₂_comp : IsCompact V₂)
    (hV₁_conn : IsConnected V₁) (hV₂_conn : IsConnected V₂)
    (hV₁_sub : V₁ ⊆ (interior Δ₀)ᶜ) (hV₂_sub : V₂ ⊆ (interior Δ₀)ᶜ)
    (hp₁_V₁ : p₁ ∈ V₁) (hp₃_V₁ : p₃ ∈ V₁) (hp₂_V₂ : p₂ ∈ V₂) (hp₄_V₂ : p₄ ∈ V₂) :
    (V₁ ∩ V₂).Nonempty := by
  obtain ⟨D_ext, hD_ext, hbd_ext, hsub_ext⟩ := exists_exterior_disc_in_onePoint hΔ₀ φ₀
  let ι : EuclideanPlane → OnePoint EuclideanPlane := OnePoint.some
  have hι_cont : Continuous ι := OnePoint.continuous_coe
  have hι_inj : Function.Injective ι := OnePoint.coe_injective
  let eF : subBd Δ₀ ≃ₜ ι '' subBd Δ₀ :=
    OnePoint.isOpenEmbedding_coe.isEmbedding.homeomorphImage (subBd Δ₀)
  let φ₀' : Circle ≃ₜ discBd D_ext := (φ₀.trans eF).trans (Homeomorph.setCongr hbd_ext.symm)
  have hcr_bd₀ : PairsCrossOn (subBd Δ₀) p₁ p₃ p₂ p₄ :=
    pairsCrossOn_of_crosses hagrees₀ hcr hp₁ hp₃ hp₂ hp₄
  have hp₁_bd : p₁ ∈ subBd Δ₀ := hcr_bd₀.1
  have hp₂_bd : p₂ ∈ subBd Δ₀ := hcr_bd₀.2.1
  have hp₃_bd : p₃ ∈ subBd Δ₀ := hcr_bd₀.2.2.1
  have hp₄_bd : p₄ ∈ subBd Δ₀ := hcr_bd₀.2.2.2.1
  let z₁ : Circle := φ₀.symm ⟨p₁, hp₁_bd⟩
  let z₃ : Circle := φ₀.symm ⟨p₃, hp₃_bd⟩
  let z₂ : Circle := φ₀.symm ⟨p₂, hp₂_bd⟩
  let z₄ : Circle := φ₀.symm ⟨p₄, hp₄_bd⟩
  have ho_eq : ∀ (p : EuclideanPlane) (hp : p ∈ subBd Δ₀),
      oArcMap φ₀ (φ₀.symm ⟨p, hp⟩) = p := fun p hp => by simp [oArcMap]
  have ho'_eq : ∀ (p : EuclideanPlane) (hp : p ∈ subBd Δ₀),
      oArcMap φ₀' (φ₀.symm ⟨p, hp⟩) = ι p := fun p hp => by
    change ((Homeomorph.setCongr hbd_ext.symm) (eF (φ₀ (φ₀.symm ⟨p, hp⟩)))).1 = ι p
    rw [Homeomorph.apply_symm_apply]
    rfl
  have hcr_circle : CrossesOn (Set.univ : Set Circle) z₁ z₃ z₂ z₄ := by
    apply (crossesOn_oArcMap_iff φ₀).mp
    change PairsCrossOn (subBd Δ₀) (oArcMap φ₀ z₁) (oArcMap φ₀ z₃) (oArcMap φ₀ z₂) (oArcMap φ₀ z₄)
    rwa [ho_eq p₁ hp₁_bd, ho_eq p₃ hp₃_bd, ho_eq p₂ hp₂_bd, ho_eq p₄ hp₄_bd]
  have hcr_ext : PairsCrossOn (discBd D_ext) (ι p₁) (ι p₃) (ι p₂) (ι p₄) := by
    rw [← ho'_eq p₁ hp₁_bd, ← ho'_eq p₃ hp₃_bd, ← ho'_eq p₂ hp₂_bd, ← ho'_eq p₄ hp₄_bd]
    exact (crossesOn_oArcMap_iff φ₀').mpr hcr_circle
  have hV₁_ext : ι '' V₁ ⊆ D_ext := by
    rintro _ ⟨x, hx, rfl⟩; exact hsub_ext x (hV₁_sub hx)
  have hV₂_ext : ι '' V₂ ⊆ D_ext := by
    rintro _ ⟨x, hx, rfl⟩; exact hsub_ext x (hV₂_sub hx)
  obtain ⟨y, ⟨x₁, hx₁, rfl⟩, ⟨x₂, hx₂, hx12⟩⟩ :=
    disc_crossing D_ext (ι '' V₁) (ι '' V₂) (ι p₁) (ι p₃) (ι p₂) (ι p₄) hD_ext
      hV₁_ext hV₂_ext (hV₁_comp.image hι_cont) (hV₂_comp.image hι_cont)
      (hV₁_conn.image ι hι_cont.continuousOn) (hV₂_conn.image ι hι_cont.continuousOn)
      (mem_image_of_mem ι hp₁_V₁) (mem_image_of_mem ι hp₃_V₁)
      (mem_image_of_mem ι hp₂_V₂) (mem_image_of_mem ι hp₄_V₂) hcr_ext
  exact ⟨x₁, hx₁, hι_inj hx12.symm ▸ hx₂⟩

/-- Transferring a crooked transaction `P_set₀` in `S₀` to `f_P '' P_set₀` in `S₁` along an end map
`f_v` that is injective on `S₀.transactionEnds P_set₀` and preserves `Crosses`. -/
theorem isCrookedTransaction_of_end_map {S₀ S₁ : Society α β}
    {P_set₀ : Set (Graph α β)} (hcrooked₀ : S₀.IsCrookedTransaction P_set₀)
    {f_P : Graph α β → Graph α β} {f_v : α → α}
    (hf_ends : ∀ P ∈ P_set₀, ∀ a b : α,
      S₀.IsOmegaPathWithEnds P a b → S₁.IsOmegaPathWithEnds (f_P P) (f_v a) (f_v b))
    (hf_disj : ∀ P ∈ P_set₀, ∀ Q ∈ P_set₀, P ≠ Q → Disjoint V(f_P P) V(f_P Q))
    (hf_inj : InjOn f_v (S₀.transactionEnds P_set₀))
    (hf_cross : ∀ v₁ ∈ S₀.transactionEnds P_set₀, ∀ v₃ ∈ S₀.transactionEnds P_set₀,
      ∀ v₂ ∈ S₀.transactionEnds P_set₀, ∀ v₄ ∈ S₀.transactionEnds P_set₀,
      S₀.Ω.Crosses v₁ v₃ v₂ v₄ ↔ S₁.Ω.Crosses (f_v v₁) (f_v v₃) (f_v v₂) (f_v v₄)) :
    S₁.IsCrookedTransaction (f_P '' P_set₀) ∧ (f_P '' P_set₀).ncard = P_set₀.ncard := by
  let W₀ := S₀.transactionEnds P_set₀
  let P_set₁ := f_P '' P_set₀
  let W₁ := S₁.transactionEnds P_set₁
  obtain ⟨A₀, B₀, hfence₀⟩ := hcrooked₀.1
  have hf_P_inj : InjOn f_P P_set₀ := by
    intro P hP Q hQ hPQ_eq
    by_contra hne
    obtain ⟨a, _, b, _, hP_ab⟩ := hfence₀.2.2 P hP
    have hP'_ab := hf_ends P hP a b hP_ab
    have hmem : f_v a ∈ V(f_P P) := hP'_ab.1.left_mem
    exact disjoint_left.mp (hf_disj P hP Q hQ hne) hmem (hPQ_eq ▸ hmem)
  have hcard : P_set₁.ncard = P_set₀.ncard := Set.InjOn.ncard_image hf_P_inj
  have hW₁_eq : W₁ = f_v '' W₀ := by
    ext z; constructor
    · rintro ⟨P', ⟨P, hP, rfl⟩, d, hP'_zd⟩
      obtain ⟨a, _, b, _, hP_ab⟩ := hfence₀.2.2 P hP
      have hP'_ab := hf_ends P hP a b hP_ab
      rcases hP'_ab.ends_eq S₁ hP'_zd with ⟨rfl, _⟩ | ⟨rfl, _⟩
      · exact ⟨a, ⟨P, hP, b, hP_ab⟩, rfl⟩
      · exact ⟨b, ⟨P, hP, a, hP_ab.symm S₀⟩, rfl⟩
    · rintro ⟨a, ⟨P, hP, b, hP_ab⟩, rfl⟩
      exact ⟨f_P P, mem_image_of_mem f_P hP, f_v b, hf_ends P hP a b hP_ab⟩
  have hW₀_bar : W₀ ⊆ S₀.Ω.bar := S₀.transactionEnds_subset_bar P_set₀
  have hW₁_bar : W₁ ⊆ S₁.Ω.bar := S₁.transactionEnds_subset_bar P_set₁
  have hcr₀_W₀ : (S₀.restrictOmega W₀ hW₀_bar).IsCrookedTransaction P_set₀ :=
    ((S₀.isCrookedTransaction_restrictOmega_iff hW₀_bar).mpr ⟨hcrooked₀, Subset.rfl⟩)
  obtain ⟨A₀', B₀', hfence₀'⟩ := hcr₀_W₀.1
  have hbar₀' : (S₀.restrictOmega W₀ hW₀_bar).Ω.bar = W₀ := S₀.Ω.restrict_bar hW₀_bar
  have hbar₁' : (S₁.restrictOmega W₁ hW₁_bar).Ω.bar = W₁ := S₁.Ω.restrict_bar hW₁_bar
  have hA₀'_W₀ : A₀' ⊆ W₀ := hbar₀' ▸ hfence₀'.2.1.1
  have hB₀'_W₀ : B₀' ⊆ W₀ := hbar₀' ▸ hfence₀'.2.1.2.1
  let A₁' := f_v '' A₀'
  let B₁' := f_v '' B₀'
  have hA₁'_W₁ : A₁' ⊆ (S₁.restrictOmega W₁ hW₁_bar).Ω.bar := by
    rw [hbar₁', hW₁_eq]; exact image_mono hA₀'_W₀
  have hB₁'_W₁ : B₁' ⊆ (S₁.restrictOmega W₁ hW₁_bar).Ω.bar := by
    rw [hbar₁', hW₁_eq]; exact image_mono hB₀'_W₀
  have hdisj_AB₁' : Disjoint A₁' B₁' := by
    rw [disjoint_left]
    rintro _ ⟨a, ha, rfl⟩ ⟨b, hb, hba⟩
    have hab : a = b := hf_inj (hA₀'_W₀ ha) (hB₀'_W₀ hb) hba.symm
    exact disjoint_left.mp hfence₀'.2.1.2.2.1 ha (hab ▸ hb)
  have hunion_AB₁' : A₁' ∪ B₁' = (S₁.restrictOmega W₁ hW₁_bar).Ω.bar := by
    rw [hbar₁', hW₁_eq, ← image_union, hfence₀'.2.1.2.2.2.1, hbar₀']
  have hfence₁' : (S₁.restrictOmega W₁ hW₁_bar).Ω.IsFence A₁' B₁' := by
    refine ⟨hA₁'_W₁, hB₁'_W₁, hdisj_AB₁', hunion_AB₁', ?_⟩
    rintro _ ⟨a₁, ha₁, rfl⟩ _ ⟨a₂, ha₂, rfl⟩ ha12 _ ⟨b₁, hb₁, rfl⟩ _ ⟨b₂, hb₂, rfl⟩ hb12 hcr'
    have ha12₀ : a₁ ≠ a₂ := fun h => ha12 (congrArg f_v h)
    have hb12₀ : b₁ ≠ b₂ := fun h => hb12 (congrArg f_v h)
    have hcr₁ : S₁.Ω.Crosses (f_v a₁) (f_v a₂) (f_v b₁) (f_v b₂) :=
      ((S₁.Ω.crosses_restrict_iff hW₁_bar).mp hcr').2.2.2.2
    have hcr₀ : S₀.Ω.Crosses a₁ a₂ b₁ b₂ :=
      (hf_cross a₁ (hA₀'_W₀ ha₁) a₂ (hA₀'_W₀ ha₂) b₁ (hB₀'_W₀ hb₁) b₂ (hB₀'_W₀ hb₂)).mpr hcr₁
    have hcr₀' : (S₀.restrictOmega W₀ hW₀_bar).Ω.Crosses a₁ a₂ b₁ b₂ :=
      (S₀.Ω.crosses_restrict_iff hW₀_bar).mpr
        ⟨hA₀'_W₀ ha₁, hA₀'_W₀ ha₂, hB₀'_W₀ hb₁, hB₀'_W₀ hb₂, hcr₀⟩
    exact hfence₀'.2.1.2.2.2.2 a₁ ha₁ a₂ ha₂ ha12₀ b₁ hb₁ b₂ hb₂ hb12₀ hcr₀'
  obtain ⟨A₁, B₁, hfence₁, hA₁'A₁, hB₁'B₁⟩ := S₁.Ω.exists_isFence_of_restrict hW₁_bar hfence₁'
  have htx₁ : S₁.IsTransaction P_set₁ := by
    refine ⟨A₁, B₁, ⟨?_, ?_⟩, hfence₁, ?_⟩
    · rintro _ ⟨P, hP, rfl⟩
      obtain ⟨a, _, b, _, hP_ab⟩ := hfence₀.2.2 P hP
      exact ⟨f_v a, f_v b, hf_ends P hP a b hP_ab⟩
    · rintro _ ⟨P, hP, rfl⟩ _ ⟨Q, hQ, rfl⟩ hne
      exact hf_disj P hP Q hQ (fun h => hne (congrArg f_P h))
    · rintro _ ⟨P, hP, rfl⟩
      obtain ⟨a, ha, b, hb, hP_ab⟩ := hfence₀'.2.2 P hP
      have hP_ab₀ : S₀.IsOmegaPathWithEnds P a b :=
        ⟨hP_ab.1, hP_ab.2.1, hW₀_bar (hbar₀' ▸ hP_ab.2.2.1), hW₀_bar (hbar₀' ▸ hP_ab.2.2.2)⟩
      exact ⟨f_v a, hA₁'A₁ (mem_image_of_mem f_v ha), f_v b, hB₁'B₁ (mem_image_of_mem f_v hb),
        hf_ends P hP a b hP_ab₀⟩
  refine ⟨⟨htx₁, ?_⟩, hcard⟩
  rintro _ ⟨P, hP, rfl⟩ ⟨_, a', b', hP'_ab', hdisj_or⟩
  obtain ⟨a, haA, b, hbB, hP_ab⟩ := hfence₀.2.2 P hP
  have haW₀ : a ∈ W₀ := ⟨P, hP, b, hP_ab⟩
  have hbW₀ : b ∈ W₀ := ⟨P, hP, a, hP_ab.symm S₀⟩
  have hnot_periph₀ : ¬ S₀.IsPeripheralIn P_set₀ P := hcrooked₀.2 P hP
  have hne_ab : (S₀.Ω.interval a b ∩ W₀).Nonempty := by
    by_contra h_emp
    rw [not_nonempty_iff_eq_empty, ← disjoint_iff_inter_eq_empty] at h_emp
    exact hnot_periph₀ ⟨hP, a, b, hP_ab, Or.inl h_emp⟩
  have hne_ba : (S₀.Ω.interval b a ∩ W₀).Nonempty := by
    by_contra h_emp
    rw [not_nonempty_iff_eq_empty, ← disjoint_iff_inter_eq_empty] at h_emp
    exact hnot_periph₀ ⟨hP, a, b, hP_ab, Or.inr h_emp⟩
  rcases hne_ab with ⟨x, hx_ab, hxW₀⟩
  rcases hne_ba with ⟨y, hy_ba, hyW₀⟩
  have hP'_ab₁ := hf_ends P hP a b hP_ab
  have hcr₁' : S₁.Ω.Crosses a' b' (f_v x) (f_v y) := by
    rcases hP'_ab'.ends_eq S₁ hP'_ab₁ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact (hf_cross a haW₀ b hbW₀ x hxW₀ y hyW₀).mp
        (S₀.Ω.crosses_iff_interval.mpr (Or.inl ⟨hx_ab, hy_ba⟩))
    · exact (hf_cross b hbW₀ a haW₀ x hxW₀ y hyW₀).mp
        (S₀.Ω.crosses_iff_interval.mpr (Or.inr ⟨hy_ba, hx_ab⟩))
  have hfx_W₁ : f_v x ∈ W₁ := hW₁_eq ▸ mem_image_of_mem f_v hxW₀
  have hfy_W₁ : f_v y ∈ W₁ := hW₁_eq ▸ mem_image_of_mem f_v hyW₀
  rcases S₁.Ω.crosses_iff_interval.mp hcr₁' with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rcases hdisj_or with hdisj₁ | hdisj₂
    · exact disjoint_left.mp hdisj₁ h1 hfx_W₁
    · exact disjoint_left.mp hdisj₂ h2 hfy_W₁
  · rcases hdisj_or with hdisj₁ | hdisj₂
    · exact disjoint_left.mp hdisj₁ h1 hfy_W₁
    · exact disjoint_left.mp hdisj₂ h2 hfx_W₁

/-- Generalization of `isSeparatingOmegaPath_of_isRural`: if `Q ≤ N.G` is an `S_comp.Ω`-path with
ends `v₁, v₃` and `R₁, R₂` are paths in `S_comp.G` disjoint from `Q` with initial ends
`v₂, v₄ ∈ S_comp.Ω.bar` such that `S_comp.Ω.Crosses v₁ v₃ v₂ v₄`, then `R₁` and `R₂` cannot both
fail to be subgraphs of `N.G`. -/
theorem not_both_not_le_right_of_crosses_in_rural {S S_comp : Society α β} {N : Neighborhood α β}
    {Q R₁ R₂ : Graph α β} {v₁ v₃ v₂ a v₄ b : α}
    (hcomp : S_comp.IsComposition S N) (hrural : N.IsRural)
    (hQN : Q ≤ N.G) (hQ_ends : S_comp.IsOmegaPathWithEnds Q v₁ v₃)
    (hR₁_path : IsGraphPathWithEnds S_comp.G R₁ v₂ a) (hv₂a : v₂ ≠ a) (hv₂ : v₂ ∈ S_comp.Ω.bar)
    (hR₂_path : IsGraphPathWithEnds S_comp.G R₂ v₄ b) (hv₄b : v₄ ≠ b) (hv₄ : v₄ ∈ S_comp.Ω.bar)
    (hdisj₁ : Disjoint V(Q) V(R₁)) (hdisj₂ : Disjoint V(Q) V(R₂))
    (hcr : S_comp.Ω.Crosses v₁ v₃ v₂ v₄)
    (hnot₁ : ¬ R₁ ≤ N.G) (hnot₂ : ¬ R₂ ≤ N.G) : False := by
  have hv₁_bar : v₁ ∈ N.Ω.bar := hcomp.2.1 ▸ hQ_ends.2.2.1
  have hv₃_bar : v₃ ∈ N.Ω.bar := hcomp.2.1 ▸ hQ_ends.2.2.2
  have hv₂_bar : v₂ ∈ N.Ω.bar := hcomp.2.1 ▸ hv₂
  have hv₄_bar : v₄ ∈ N.Ω.bar := hcomp.2.1 ▸ hv₄
  have hcr_N : N.Ω.Crosses v₁ v₃ v₂ v₄ := hcomp.2.1 ▸ hcr
  obtain ⟨R₁', w₁, hw₁_bar₀, hR₁'_R₁, hR₁'_N, hR₁'_path⟩ :=
    exists_subpath_to_left_of_not_le_right hcomp hR₁_path hv₂a hnot₁ hv₂_bar
  obtain ⟨R₂', w₂, hw₂_bar₀, hR₂'_R₂, hR₂'_N, hR₂'_path⟩ :=
    exists_subpath_to_left_of_not_le_right hcomp hR₂_path hv₄b hnot₂ hv₄_bar
  obtain ⟨Γ, Δ, Δ₀, hΔ, hΔ₀_sub, hU_sub, hbd, hbd₀, ⟨φ, _, hφ⟩, hinner⟩ := hrural
  rcases hinner with ⟨_, hΩ₀_emp⟩ | ⟨hΔ₀_disc, _⟩
  · exact (notMem_empty w₁ (hΩ₀_emp ▸ hw₁_bar₀)).elim
  · have hv₁G : v₁ ∈ V(N.G) := N.bar_subset hv₁_bar
    have hv₃G : v₃ ∈ V(N.G) := N.bar_subset hv₃_bar
    have hv₂G : v₂ ∈ V(N.G) := N.bar_subset hv₂_bar
    have hv₄G : v₄ ∈ V(N.G) := N.bar_subset hv₄_bar
    have hw₁G : w₁ ∈ V(N.G) := N.bar₀_subset hw₁_bar₀
    have hw₂G : w₂ ∈ V(N.G) := N.bar₀_subset hw₂_bar₀
    let p₁ := (Γ.iso.vertexEquiv ⟨v₁, hv₁G⟩).1
    let p₃ := (Γ.iso.vertexEquiv ⟨v₃, hv₃G⟩).1
    let p₂ := (Γ.iso.vertexEquiv ⟨v₂, hv₂G⟩).1
    let p₄ := (Γ.iso.vertexEquiv ⟨v₄, hv₄G⟩).1
    let q₁ := (Γ.iso.vertexEquiv ⟨w₁, hw₁G⟩).1
    let q₂ := (Γ.iso.vertexEquiv ⟨w₂, hw₂G⟩).1
    have hq₁_bd₀ : q₁ ∈ subBd Δ₀ := (hbd₀ w₁ hw₁G).mpr hw₁_bar₀ ⟨hw₁G, rfl⟩
    have hq₂_bd₀ : q₂ ∈ subBd Δ₀ := (hbd₀ w₂ hw₂G).mpr hw₂_bar₀ ⟨hw₂G, rfl⟩
    have hbd₀_sub : subBd Δ₀ ⊆ Δ₀ :=
      subBd_eq_discBd_plane hΔ₀_disc ▸ Surface.discBd_subset Δ₀
    obtain ⟨K₀, hK₀_comp, hK₀_conn, hq₁_K₀, hq₂_K₀, hK₀_Δ₀, hK₀_int⟩ :=
      exists_compact_connected_in_disc_avoiding_bd hΔ₀_disc (hbd₀_sub hq₁_bd₀) (hbd₀_sub hq₂_bd₀)
    have hQ_path : IsGraphPathWithEnds N.G Q v₁ v₃ := hQ_ends.1.of_le hQN
    have hV₁_Δ : graphDrawingSubgraphU Γ Q ⊆ Δ :=
      (graphDrawingSubgraphU_subset_U' Γ Q).trans (hU_sub.trans sdiff_subset)
    have hUR₁_Δ : graphDrawingSubgraphU Γ R₁' ⊆ Δ :=
      (graphDrawingSubgraphU_subset_U' Γ R₁').trans (hU_sub.trans sdiff_subset)
    have hUR₂_Δ : graphDrawingSubgraphU Γ R₂' ⊆ Δ :=
      (graphDrawingSubgraphU_subset_U' Γ R₂').trans (hU_sub.trans sdiff_subset)
    obtain ⟨hUQ_comp, hUQ_conn, _, _⟩ :=
      isCompact_and_isConnected_subgraphU_of_isGraphPathWithEnds hΔ hQ_path hV₁_Δ
    obtain ⟨hUR₁_comp, hUR₁_conn, _, _⟩ :=
      isCompact_and_isConnected_subgraphU_of_isGraphPathWithEnds hΔ hR₁'_path hUR₁_Δ
    obtain ⟨hUR₂_comp, hUR₂_conn, _, _⟩ :=
      isCompact_and_isConnected_subgraphU_of_isGraphPathWithEnds hΔ hR₂'_path hUR₂_Δ
    have hq₁_UR₁ : q₁ ∈ graphDrawingSubgraphU Γ R₁' :=
      Or.inl (mem_iUnion₂.mpr ⟨w₁, hR₁'_path.right_mem, hw₁G, rfl⟩)
    have hq₂_UR₂ : q₂ ∈ graphDrawingSubgraphU Γ R₂' :=
      Or.inl (mem_iUnion₂.mpr ⟨w₂, hR₂'_path.right_mem, hw₂G, rfl⟩)
    let V₁ := graphDrawingSubgraphU Γ Q
    let V₂ := (graphDrawingSubgraphU Γ R₁' ∪ K₀) ∪ graphDrawingSubgraphU Γ R₂'
    have hV₂_comp : IsCompact V₂ := (hUR₁_comp.union hK₀_comp).union hUR₂_comp
    have hV₂_conn : IsConnected V₂ :=
      IsConnected.union ⟨q₂, Or.inr hq₂_K₀, hq₂_UR₂⟩
        (IsConnected.union ⟨q₁, hq₁_UR₁, hq₁_K₀⟩ hUR₁_conn hK₀_conn) hUR₂_conn
    have hV₂_Δ : V₂ ⊆ Δ :=
      union_subset (union_subset hUR₁_Δ (hK₀_Δ₀.trans hΔ₀_sub)) hUR₂_Δ
    have hp₁_V₁ : p₁ ∈ V₁ := Or.inl (mem_iUnion₂.mpr ⟨v₁, hQ_path.left_mem, hv₁G, rfl⟩)
    have hp₃_V₁ : p₃ ∈ V₁ := Or.inl (mem_iUnion₂.mpr ⟨v₃, hQ_path.right_mem, hv₃G, rfl⟩)
    have hp₂_V₂ : p₂ ∈ V₂ :=
      Or.inl (Or.inl (Or.inl (mem_iUnion₂.mpr ⟨v₂, hR₁'_path.left_mem, hv₂G, rfl⟩)))
    have hp₄_V₂ : p₄ ∈ V₂ :=
      Or.inr (Or.inl (mem_iUnion₂.mpr ⟨v₄, hR₂'_path.left_mem, hv₄G, rfl⟩))
    have hcross_bd : PairsCrossOn (discBd Δ) p₁ p₃ p₂ p₄ := by
      rw [discBd_eq_subBd hΔ]
      exact pairsCrossOn_of_crosses hφ hcr_N ⟨hv₁G, rfl⟩ ⟨hv₃G, rfl⟩ ⟨hv₂G, rfl⟩ ⟨hv₄G, rfl⟩
    obtain ⟨x, hx₁, hx₂⟩ := disc_crossing Δ V₁ V₂ p₁ p₃ p₂ p₄ hΔ hV₁_Δ hV₂_Δ
      hUQ_comp hV₂_comp hUQ_conn hV₂_conn hp₁_V₁ hp₃_V₁ hp₂_V₂ hp₄_V₂ hcross_bd
    have hdisj₁' : Disjoint V(Q) V(R₁') := hdisj₁.mono_right hR₁'_R₁.vertexSet_mono
    have hdisj₂' : Disjoint V(Q) V(R₂') := hdisj₂.mono_right hR₂'_R₂.vertexSet_mono
    rcases hx₂ with (hxR₁ | hxK₀) | hxR₂
    · obtain ⟨u, huQ, huR₁⟩ :=
        nonempty_inter_vertexSet_of_nonempty_inter_subgraphU' Γ hQN hR₁'_N ⟨x, hx₁, hxR₁⟩
      exact disjoint_left.mp hdisj₁' huQ huR₁
    · rcases hK₀_int hxK₀ with (rfl | rfl) | hx_int₀
      · obtain ⟨u, huQ, huR₁⟩ :=
          nonempty_inter_vertexSet_of_nonempty_inter_subgraphU' Γ hQN hR₁'_N ⟨q₁, hx₁, hq₁_UR₁⟩
        exact disjoint_left.mp hdisj₁' huQ huR₁
      · obtain ⟨u, huQ, huR₂⟩ :=
          nonempty_inter_vertexSet_of_nonempty_inter_subgraphU' Γ hQN hR₂'_N ⟨q₂, hx₁, hq₂_UR₂⟩
        exact disjoint_left.mp hdisj₂' huQ huR₂
      · exact (hU_sub (graphDrawingSubgraphU_subset_U' Γ Q hx₁)).2 hx_int₀
    · obtain ⟨u, huQ, huR₂⟩ :=
        nonempty_inter_vertexSet_of_nonempty_inter_subgraphU' Γ hQN hR₂'_N ⟨x, hx₁, hxR₂⟩
      exact disjoint_left.mp hdisj₂' huQ huR₂

/-- In a rural composition `S_comp.IsComposition S N`, every `S_comp.Ω`-path `Q` that is a subgraph
of `N.G` is separating in `S_comp` (Graph Minors IX, Section 9, Claim (4), page 62). -/
theorem isSeparatingOmegaPath_of_isRural {S S_comp : Society α β} {N : Neighborhood α β}
    {Q : Graph α β} (hcomp : S_comp.IsComposition S N) (hrural : N.IsRural)
    (hQN : Q ≤ N.G) (hQ : S_comp.IsOmegaPath Q) :
    S_comp.IsSeparatingOmegaPath Q := by
  refine ⟨hQ, ?_⟩
  rintro ⟨R, hdisj_RQ, v₂, v₄, v₁, v₃, hR_ends, hQ_ends, hcr_RQ⟩
  by_cases hRN : R ≤ N.G
  · have hv₁_bar : v₁ ∈ N.Ω.bar := hcomp.2.1 ▸ hQ_ends.2.2.1
    have hv₃_bar : v₃ ∈ N.Ω.bar := hcomp.2.1 ▸ hQ_ends.2.2.2
    have hv₂_bar : v₂ ∈ N.Ω.bar := hcomp.2.1 ▸ hR_ends.2.2.1
    have hv₄_bar : v₄ ∈ N.Ω.bar := hcomp.2.1 ▸ hR_ends.2.2.2
    have hcr_N : N.Ω.Crosses v₁ v₃ v₂ v₄ := hcomp.2.1 ▸ hcr_RQ.symm
    exact not_omegaPathsCross_of_isRural hrural
      ⟨hdisj_RQ.symm, v₁, v₃, v₂, v₄,
        ⟨hQ_ends.1.of_le hQN, hQ_ends.2.1, hv₁_bar, hv₃_bar⟩,
        ⟨hR_ends.1.of_le hRN, hR_ends.2.1, hv₂_bar, hv₄_bar⟩,
        hcr_N⟩
  · exact not_both_not_le_right_of_crosses_in_rural hcomp hrural hQN hQ_ends
      hR_ends.1 hR_ends.2.1 hR_ends.2.2.1
      hR_ends.1.symm hR_ends.2.1.symm hR_ends.2.2.2
      hdisj_RQ.symm hdisj_RQ.symm hcr_RQ.symm hRN hRN

/-- Variation of `Society.theorem_5_1_proof` when the separating path `Q` belongs to `P_set` itself:
if `Q ∈ P_set`
has ends `a, b` and is separating in `S`, then there is a crossing pair in `P_set` with all ends in
`S.Ω.interval a b`. -/
theorem exists_cross_in_interval_of_mem_separating {S : Society α β}
    {P_set : Set (Graph α β)} {Q : Graph α β} {a b : α}
    (hQ_in : Q ∈ P_set) (hQ_ends : S.IsOmegaPathWithEnds Q a b)
    (hQ_sep : S.IsSeparatingOmegaPath Q) (hcrooked : S.IsCrookedTransaction P_set) :
    ∃ P₁ ∈ P_set, ∃ P₂ ∈ P_set,
      S.OmegaPathsCross P₁ P₂ ∧
      pathEnds S.G P₁ ⊆ S.Ω.interval a b ∧
      pathEnds S.G P₂ ⊆ S.Ω.interval a b := by
  obtain ⟨A, B, hfence⟩ := hcrooked.1
  have hnot_periph_Q : ¬ S.IsPeripheralIn P_set Q := hcrooked.2 Q hQ_in
  have hne : (S.Ω.interval a b ∩ S.transactionEnds P_set).Nonempty := by
    by_contra h_empty
    rw [not_nonempty_iff_eq_empty, ← disjoint_iff_inter_eq_empty] at h_empty
    exact hnot_periph_Q ⟨hQ_in, a, b, hQ_ends, Or.inl h_empty⟩
  have hex_good : ∀ R ∈ P_set, (pathEnds S.G R ∩ S.Ω.interval a b).Nonempty →
      ∃ s t : α, S.IsOmegaPathWithEnds R s t ∧
        s ∈ S.Ω.interval a b ∧ t ∈ S.Ω.interval a b ∧
        S.Ω.interval s t ⊆ S.Ω.interval a b ∧ Disjoint V(R) V(Q) := by
    intro R hR ⟨x, hx_end, hx_ab⟩
    obtain ⟨u, huA, v, hvB, hR_uv⟩ := hfence.2.2 R hR
    have huv_ne : u ≠ v := fun h => disjoint_left.mp hfence.2.1.2.2.1 huA (h ▸ hvB)
    have hRQ : R ≠ Q := by
      rintro rfl
      rw [hQ_ends.1.pathEnds_eq, mem_insert_iff, mem_singleton_iff] at hx_end
      exact hx_ab.1.2 hx_end
    have hdisj_RQ : Disjoint V(R) V(Q) := hfence.1.2 hR hQ_in hRQ
    rw [hR_uv.1.pathEnds_eq, mem_insert_iff, mem_singleton_iff] at hx_end
    have hu_ab : u ∈ S.Ω.interval a b := by
      rcases hx_end with rfl | rfl
      · exact hx_ab
      · exact S.both_ends_mem_interval_of_separating hQ_ends hQ_sep (hR_uv.symm S) hdisj_RQ hx_ab
    have hv_ab : v ∈ S.Ω.interval a b :=
      S.both_ends_mem_interval_of_separating hQ_ends hQ_sep hR_uv hdisj_RQ hu_ab
    rcases S.Ω.interval_subset_interval_or_swap hu_ab hv_ab huv_ne with hsub_uv | hsub_vu
    · exact ⟨u, v, hR_uv, hu_ab, hv_ab, hsub_uv, hdisj_RQ⟩
    · exact ⟨v, u, hR_uv.symm S, hv_ab, hu_ab, hsub_vu, hdisj_RQ⟩
  have hex_cand : ∃ n : ℕ, ∃ P ∈ P_set, ∃ s t : α,
      S.IsOmegaPathWithEnds P s t ∧
      s ∈ S.Ω.interval a b ∧ t ∈ S.Ω.interval a b ∧
      S.Ω.interval s t ⊆ S.Ω.interval a b ∧
      (S.Ω.interval s t).ncard = n := by
    rcases hne with ⟨x, hx_ab, P₀, hP₀, y₀, hP₀_xy⟩
    have hx_end : x ∈ pathEnds S.G P₀ := by
      rw [hP₀_xy.1.pathEnds_eq]; exact Or.inl rfl
    obtain ⟨s₀, t₀, hP₀_st, hs₀, ht₀, hsub₀, _⟩ := hex_good P₀ hP₀ ⟨x, hx_end, hx_ab⟩
    exact ⟨(S.Ω.interval s₀ t₀).ncard, P₀, hP₀, s₀, t₀, hP₀_st, hs₀, ht₀, hsub₀, rfl⟩
  classical
  let n_min := Nat.find hex_cand
  obtain ⟨P, hP_in, s, t, hP_ends, hs_ab, ht_ab, hsub_st, hcard_st⟩ := Nat.find_spec hex_cand
  have hmin_st : ∀ P' ∈ P_set, ∀ s' t' : α,
      S.IsOmegaPathWithEnds P' s' t' →
      s' ∈ S.Ω.interval a b → t' ∈ S.Ω.interval a b →
      S.Ω.interval s' t' ⊆ S.Ω.interval a b →
      n_min ≤ (S.Ω.interval s' t').ncard :=
    fun P' hP' s' t' hP'_st hs' ht' hsub' =>
      Nat.find_min' hex_cand ⟨P', hP', s', t', hP'_st, hs', ht', hsub', rfl⟩
  have hnot_periph : ¬ S.IsPeripheralIn P_set P := hcrooked.2 P hP_in
  have hhit_st : (S.Ω.interval s t ∩ S.transactionEnds P_set).Nonempty := by
    by_contra h_empty
    rw [not_nonempty_iff_eq_empty, ← disjoint_iff_inter_eq_empty] at h_empty
    exact hnot_periph ⟨hP_in, s, t, hP_ends, Or.inl h_empty⟩
  rcases hhit_st with ⟨x', hx'_st, P', hP'_in, y', hP'_ends⟩
  have hP'_ne_P : P' ≠ P := by
    rintro rfl
    rcases hP_ends.ends_eq S hP'_ends with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hx'_st.1.2 (Or.inl rfl)
    · exact hx'_st.1.2 (Or.inr rfl)
  have hdisj_PP' : Disjoint V(P) V(P') := hfence.1.2 hP_in hP'_in hP'_ne_P.symm
  have hx'_ab : x' ∈ S.Ω.interval a b := hsub_st hx'_st
  have hx'_end : x' ∈ pathEnds S.G P' := by rw [hP'_ends.1.pathEnds_eq]; exact Or.inl rfl
  obtain ⟨_, _, _, _, _, _, hdisj_P'Q⟩ := hex_good P' hP'_in ⟨x', hx'_end, hx'_ab⟩
  have hy'_ab : y' ∈ S.Ω.interval a b :=
    S.both_ends_mem_interval_of_separating hQ_ends hQ_sep hP'_ends hdisj_P'Q hx'_ab
  have hx'y'_ne : x' ≠ y' := hP'_ends.2.1
  have hy'_not_st : y' ∉ S.Ω.interval s t := by
    intro hy'_st
    have hfin_st : (S.Ω.interval s t).Finite := S.Ω.finite_bar.subset (S.Ω.interval_subset_bar s t)
    rcases S.Ω.interval_subset_interval_or_swap hx'_st hy'_st hx'y'_ne with hsub' | hsub'
    · have hlt : (S.Ω.interval x' y').ncard < (S.Ω.interval s t).ncard :=
        ncard_lt_ncard ⟨hsub', fun h_all => (h_all hy'_st).1.2 (Or.inr rfl)⟩ hfin_st
      have hge := hmin_st P' hP'_in x' y' hP'_ends hx'_ab hy'_ab (hsub'.trans hsub_st)
      omega
    · have hlt : (S.Ω.interval y' x').ncard < (S.Ω.interval s t).ncard :=
        ncard_lt_ncard ⟨hsub', fun h_all => (h_all hx'_st).1.2 (Or.inr rfl)⟩ hfin_st
      have hge := hmin_st P' hP'_in y' x' (hP'_ends.symm S) hy'_ab hx'_ab (hsub'.trans hsub_st)
      omega
  have hy'_ne_s : y' ≠ s := fun h =>
    disjoint_left.mp hdisj_PP' (h ▸ hP_ends.1.left_mem) hP'_ends.1.right_mem
  have hy'_ne_t : y' ≠ t := fun h =>
    disjoint_left.mp hdisj_PP' (h ▸ hP_ends.1.right_mem) hP'_ends.1.right_mem
  have hy'_ts : y' ∈ S.Ω.interval t s := by
    rcases S.Ω.mem_interval_or_interval_swap hP_ends.2.2.1 hP_ends.2.2.2
      hP'_ends.2.2.2 hP_ends.2.1 hy'_ne_s hy'_ne_t with h_st | h_ts
    · exact (hy'_not_st h_st).elim
    · exact h_ts
  refine ⟨P, hP_in, P', hP'_in, ⟨hdisj_PP', s, t, x', y', hP_ends, hP'_ends,
    S.Ω.crosses_iff_interval.mpr (Or.inl ⟨hx'_st, hy'_ts⟩)⟩, ?_, ?_⟩
  · rw [hP_ends.1.pathEnds_eq]; rintro z (rfl | rfl) <;> assumption
  · rw [hP'_ends.1.pathEnds_eq]; rintro z (rfl | rfl) <;> assumption

/-- In a rural composition `S_comp.IsComposition S N`, no member `Q` of a crooked transaction
`P_set`
in `S_comp` is a subgraph of `N.G`. -/
theorem forall_not_le_right_of_isCrookedTransaction {S S_comp : Society α β} {N : Neighborhood α β}
    {P_set : Set (Graph α β)} (hcomp : S_comp.IsComposition S N) (hrural : N.IsRural)
    (hcrooked : S_comp.IsCrookedTransaction P_set) :
    ∀ Q ∈ P_set, ¬ Q ≤ N.G := by
  intro Q hQ_in hQN
  obtain ⟨A, B, hfence⟩ := hcrooked.1
  obtain ⟨v₁, _, v₃, _, hQ_ends⟩ := hfence.2.2 Q hQ_in
  have hQ_sep : S_comp.IsSeparatingOmegaPath Q :=
    isSeparatingOmegaPath_of_isRural hcomp hrural hQN ⟨v₁, v₃, hQ_ends⟩
  have h_side : ∀ {x y : α}, S_comp.IsOmegaPathWithEnds Q x y →
      ∃ R ∈ P_set, ¬ R ≤ N.G ∧ Disjoint V(Q) V(R) ∧
        ∃ u w : α, S_comp.IsOmegaPathWithEnds R u w ∧ u ∈ S_comp.Ω.interval x y := by
    intro x y hQ_xy
    obtain ⟨P₁, hP₁_in, P₂, hP₂_in, hcr12, hends₁, hends₂⟩ :=
      exists_cross_in_interval_of_mem_separating hQ_in hQ_xy hQ_sep hcrooked
    rcases hcr12 with ⟨hdisj12, u₁, w₁, u₂, w₂, hP₁_ends, hP₂_ends, hcr_ends⟩
    have hu₁_xy : u₁ ∈ S_comp.Ω.interval x y := by
      apply hends₁; rw [hP₁_ends.1.pathEnds_eq]; exact Or.inl rfl
    have hu₂_xy : u₂ ∈ S_comp.Ω.interval x y := by
      apply hends₂; rw [hP₂_ends.1.pathEnds_eq]; exact Or.inl rfl
    have hP₁_ne_Q : P₁ ≠ Q := by
      intro h_eq; subst P₁
      have : u₁ ∈ pathEnds S_comp.G Q := by rw [hP₁_ends.1.pathEnds_eq]; exact Or.inl rfl
      rw [hQ_xy.1.pathEnds_eq, mem_insert_iff, mem_singleton_iff] at this
      exact hu₁_xy.1.2 this
    have hP₂_ne_Q : P₂ ≠ Q := by
      intro h_eq; subst P₂
      have : u₂ ∈ pathEnds S_comp.G Q := by rw [hP₂_ends.1.pathEnds_eq]; exact Or.inl rfl
      rw [hQ_xy.1.pathEnds_eq, mem_insert_iff, mem_singleton_iff] at this
      exact hu₂_xy.1.2 this
    by_cases hP₁_N : P₁ ≤ N.G
    · have hP₂_not_N : ¬ P₂ ≤ N.G := fun hP₂_N => by
        have hu₁_bar : u₁ ∈ N.Ω.bar := hcomp.2.1 ▸ hP₁_ends.2.2.1
        have hw₁_bar : w₁ ∈ N.Ω.bar := hcomp.2.1 ▸ hP₁_ends.2.2.2
        have hu₂_bar : u₂ ∈ N.Ω.bar := hcomp.2.1 ▸ hP₂_ends.2.2.1
        have hw₂_bar : w₂ ∈ N.Ω.bar := hcomp.2.1 ▸ hP₂_ends.2.2.2
        have hcr_N : N.Ω.Crosses u₁ w₁ u₂ w₂ := hcomp.2.1 ▸ hcr_ends
        exact not_omegaPathsCross_of_isRural hrural
          ⟨hdisj12, u₁, w₁, u₂, w₂,
            ⟨hP₁_ends.1.of_le hP₁_N, hP₁_ends.2.1, hu₁_bar, hw₁_bar⟩,
            ⟨hP₂_ends.1.of_le hP₂_N, hP₂_ends.2.1, hu₂_bar, hw₂_bar⟩,
            hcr_N⟩
      exact ⟨P₂, hP₂_in, hP₂_not_N, hfence.1.2 hQ_in hP₂_in hP₂_ne_Q.symm,
        u₂, w₂, hP₂_ends, hu₂_xy⟩
    · exact ⟨P₁, hP₁_in, hP₁_N, hfence.1.2 hQ_in hP₁_in hP₁_ne_Q.symm,
        u₁, w₁, hP₁_ends, hu₁_xy⟩
  obtain ⟨R₁, _, hR₁_not_N, hdisj₁, v₂, a, hR₁_ends, hv₂_int⟩ := h_side hQ_ends
  obtain ⟨R₂, _, hR₂_not_N, hdisj₂, v₄, b, hR₂_ends, hv₄_int⟩ := h_side (hQ_ends.symm S_comp)
  have hcr : S_comp.Ω.Crosses v₁ v₃ v₂ v₄ :=
    S_comp.Ω.crosses_iff_interval.mpr (Or.inl ⟨hv₂_int, hv₄_int⟩)
  exact not_both_not_le_right_of_crosses_in_rural hcomp hrural hQN hQ_ends
    hR₁_ends.1 hR₁_ends.2.1 hR₁_ends.2.2.1
    hR₂_ends.1 hR₂_ends.2.1 hR₂_ends.2.2.1
    hdisj₁ hdisj₂ hcr hR₁_not_N hR₂_not_N

/-- Two vertex-disjoint paths `Q₁, Q₂ ≤ N.G` in a rural neighborhood `N` with ends in `N.Ω₀.bar`
cannot have crossing ends in `N.Ω₀`. -/
theorem not_crosses_inner_of_disjoint_paths {N : Neighborhood α β} (hrural : N.IsRural)
    {Q₁ Q₂ : Graph α β} {x₁ y₁ x₂ y₂ : α}
    (hQ₁ : IsGraphPathWithEnds N.G Q₁ x₁ y₁) (hx₁ : x₁ ∈ N.Ω₀.bar) (hy₁ : y₁ ∈ N.Ω₀.bar)
    (hQ₂ : IsGraphPathWithEnds N.G Q₂ x₂ y₂) (hx₂ : x₂ ∈ N.Ω₀.bar) (hy₂ : y₂ ∈ N.Ω₀.bar)
    (hdisj : Disjoint V(Q₁) V(Q₂)) :
    ¬ N.Ω₀.Crosses x₁ y₁ x₂ y₂ := by
  intro hcr
  obtain ⟨Γ, Δ, Δ₀, hΔ, _, hU_sub, _, _, _, hinner⟩ := hrural
  rcases hinner with ⟨_, hΩ₀_emp⟩ | ⟨hΔ₀, φ₀, _, hφ₀⟩
  · exact notMem_empty x₁ (hΩ₀_emp ▸ hx₁)
  · have hx₁G : x₁ ∈ V(N.G) := N.bar₀_subset hx₁
    have hy₁G : y₁ ∈ V(N.G) := N.bar₀_subset hy₁
    have hx₂G : x₂ ∈ V(N.G) := N.bar₀_subset hx₂
    have hy₂G : y₂ ∈ V(N.G) := N.bar₀_subset hy₂
    have hV₁_Δ : graphDrawingSubgraphU Γ Q₁ ⊆ Δ :=
      (graphDrawingSubgraphU_subset_U' Γ Q₁).trans (hU_sub.trans sdiff_subset)
    have hV₂_Δ : graphDrawingSubgraphU Γ Q₂ ⊆ Δ :=
      (graphDrawingSubgraphU_subset_U' Γ Q₂).trans (hU_sub.trans sdiff_subset)
    obtain ⟨hV₁_comp, hV₁_conn, _, _⟩ :=
      isCompact_and_isConnected_subgraphU_of_isGraphPathWithEnds hΔ hQ₁ hV₁_Δ
    obtain ⟨hV₂_comp, hV₂_conn, _, _⟩ :=
      isCompact_and_isConnected_subgraphU_of_isGraphPathWithEnds hΔ hQ₂ hV₂_Δ
    have hV₁_sub : graphDrawingSubgraphU Γ Q₁ ⊆ (interior Δ₀)ᶜ :=
      fun p hp => (hU_sub (graphDrawingSubgraphU_subset_U' Γ Q₁ hp)).2
    have hV₂_sub : graphDrawingSubgraphU Γ Q₂ ⊆ (interior Δ₀)ᶜ :=
      fun p hp => (hU_sub (graphDrawingSubgraphU_subset_U' Γ Q₂ hp)).2
    have hne := nonempty_inter_of_crosses_on_inner_bd hΔ₀ hφ₀ hcr
      ⟨hx₁G, rfl⟩ ⟨hy₁G, rfl⟩ ⟨hx₂G, rfl⟩ ⟨hy₂G, rfl⟩
      hV₁_comp hV₂_comp hV₁_conn hV₂_conn hV₁_sub hV₂_sub
      (Or.inl (mem_iUnion₂.mpr ⟨x₁, hQ₁.left_mem, hx₁G, rfl⟩))
      (Or.inl (mem_iUnion₂.mpr ⟨y₁, hQ₁.right_mem, hy₁G, rfl⟩))
      (Or.inl (mem_iUnion₂.mpr ⟨x₂, hQ₂.left_mem, hx₂G, rfl⟩))
      (Or.inl (mem_iUnion₂.mpr ⟨y₂, hQ₂.right_mem, hy₂G, rfl⟩))
    obtain ⟨u, hu₁, hu₂⟩ := nonempty_inter_vertexSet_of_nonempty_inter_subgraphU' Γ hQ₁.le hQ₂.le
      hne
    exact disjoint_left.mp hdisj hu₁ hu₂

/-- If `Q ≤ N.G` is a path with ends `x, y ∈ N.Ω₀.bar` and `T₁, T₂ ≤ N.G` are paths from
`a₁, a₂ ∈ N.Ω.bar` to `z₁, z₂ ∈ N.Ω₀.bar` both vertex-disjoint from `Q`, then `x, y` cannot cross
`z₁, z₂` in `N.Ω₀`. -/
theorem not_crosses_inner_of_disjoint_paths_to_outer {N : Neighborhood α β} (hrural : N.IsRural)
    {Q T₁ T₂ : Graph α β} {x y a₁ z₁ a₂ z₂ : α}
    (hQ : IsGraphPathWithEnds N.G Q x y) (hx : x ∈ N.Ω₀.bar) (hy : y ∈ N.Ω₀.bar)
    (hT₁ : IsGraphPathWithEnds N.G T₁ a₁ z₁) (ha₁ : a₁ ∈ N.Ω.bar) (hz₁ : z₁ ∈ N.Ω₀.bar)
    (hT₂ : IsGraphPathWithEnds N.G T₂ a₂ z₂) (ha₂ : a₂ ∈ N.Ω.bar) (hz₂ : z₂ ∈ N.Ω₀.bar)
    (hdisj₁ : Disjoint V(Q) V(T₁)) (hdisj₂ : Disjoint V(Q) V(T₂)) :
    ¬ N.Ω₀.Crosses x y z₁ z₂ := by
  intro hcr
  obtain ⟨Γ, Δ, Δ₀, hΔ, hΔ₀_sub, hU_sub, hbd, hbd₀, ⟨φ, _, hφ⟩, hinner⟩ := hrural
  let Y : Set α := {a₁, a₂}
  have hY_bar : Y ⊆ N.Ω.bar := by rintro v (rfl | rfl) <;> assumption
  let Ω' := N.Ω.restrict Y hY_bar
  have hbar'G : Ω'.bar ⊆ V(N.G) := by
    rw [N.Ω.restrict_bar hY_bar]; exact hY_bar.trans N.bar_subset
  have hbar' : Ω'.bar ⊆ N.Ω.bar := by
    rw [N.Ω.restrict_bar hY_bar]; exact hY_bar
  have hcw' : ∀ v₁ v₂ v₃ : α, Ω'.IsClockwise3 v₁ v₂ v₃ → N.Ω.IsClockwise3 v₁ v₂ v₃ :=
    fun v₁ v₂ v₃ h => ((N.Ω.isClockwise3_restrict_iff hY_bar).mp h).2.2.2
  obtain ⟨Ψ, Ψ', Γ', Δ₀', _, _, _, _, _, _, hΔ₀'_sub, _, hU'_sub, _, _, _,
      hU'_inter_bd, _, hbd', _, _, hinner'⟩ :=
    exists_clean_presentation_of_restrict_outer hbar'G hbar' hcw' Γ Δ Δ₀ hΔ hΔ₀_sub hU_sub
      hbd hbd₀ φ hφ hinner
  rcases hinner' with ⟨_, hΩ₀_emp⟩ | ⟨hΔ₀'_disc, φ₀', _, hφ₀'⟩
  · exact notMem_empty x (hΩ₀_emp ▸ hx)
  · have hxG : x ∈ V(N.G) := N.bar₀_subset hx
    have hyG : y ∈ V(N.G) := N.bar₀_subset hy
    have ha₁G : a₁ ∈ V(N.G) := N.bar_subset ha₁
    have ha₂G : a₂ ∈ V(N.G) := N.bar_subset ha₂
    have hz₁G : z₁ ∈ V(N.G) := N.bar₀_subset hz₁
    have hz₂G : z₂ ∈ V(N.G) := N.bar₀_subset hz₂
    have hUQ_Δ : graphDrawingSubgraphU Γ' Q ⊆ Δ :=
      (graphDrawingSubgraphU_subset_U' Γ' Q).trans (hU'_sub.trans sdiff_subset)
    have hUT₁_Δ : graphDrawingSubgraphU Γ' T₁ ⊆ Δ :=
      (graphDrawingSubgraphU_subset_U' Γ' T₁).trans (hU'_sub.trans sdiff_subset)
    have hUT₂_Δ : graphDrawingSubgraphU Γ' T₂ ⊆ Δ :=
      (graphDrawingSubgraphU_subset_U' Γ' T₂).trans (hU'_sub.trans sdiff_subset)
    obtain ⟨hUQ_comp, hUQ_conn, _, _⟩ :=
      isCompact_and_isConnected_subgraphU_of_isGraphPathWithEnds hΔ hQ hUQ_Δ
    obtain ⟨hUT₁_comp, hUT₁_conn, _, _⟩ :=
      isCompact_and_isConnected_subgraphU_of_isGraphPathWithEnds hΔ hT₁ hUT₁_Δ
    obtain ⟨hUT₂_comp, hUT₂_conn, _, _⟩ :=
      isCompact_and_isConnected_subgraphU_of_isGraphPathWithEnds hΔ hT₂ hUT₂_Δ
    have hbd_eq_range : subBd Δ = range (Subtype.val ∘ φ) := by
      ext p; simp only [mem_range, Function.comp_apply]
      exact ⟨fun hp => ⟨φ.symm ⟨p, hp⟩, by simp⟩, fun ⟨z, hz⟩ => hz ▸ (φ z).2⟩
    have hbd_comp : IsCompact (subBd Δ) := by
      rw [hbd_eq_range]; exact isCompact_range (continuous_subtype_val.comp φ.continuous)
    have hbd_conn : IsConnected (subBd Δ) := by
      rw [hbd_eq_range]; exact isConnected_range (continuous_subtype_val.comp φ.continuous)
    let p_a₁ := (Γ'.iso.vertexEquiv ⟨a₁, ha₁G⟩).1
    let p_a₂ := (Γ'.iso.vertexEquiv ⟨a₂, ha₂G⟩).1
    have ha₁_Ω' : a₁ ∈ Ω'.bar := by rw [N.Ω.restrict_bar hY_bar]; exact Or.inl rfl
    have ha₂_Ω' : a₂ ∈ Ω'.bar := by rw [N.Ω.restrict_bar hY_bar]; exact Or.inr rfl
    have hp_a₁_bd : p_a₁ ∈ subBd Δ := (hbd' a₁ ha₁G).mpr ha₁_Ω' ⟨ha₁G, rfl⟩
    have hp_a₂_bd : p_a₂ ∈ subBd Δ := (hbd' a₂ ha₂G).mpr ha₂_Ω' ⟨ha₂G, rfl⟩
    have hp_a₁_T₁ : p_a₁ ∈ graphDrawingSubgraphU Γ' T₁ :=
      Or.inl (mem_iUnion₂.mpr ⟨a₁, hT₁.left_mem, ha₁G, rfl⟩)
    have hp_a₂_T₂ : p_a₂ ∈ graphDrawingSubgraphU Γ' T₂ :=
      Or.inl (mem_iUnion₂.mpr ⟨a₂, hT₂.left_mem, ha₂G, rfl⟩)
    let V₁ := graphDrawingSubgraphU Γ' Q
    let V₂ := (graphDrawingSubgraphU Γ' T₁ ∪ subBd Δ) ∪ graphDrawingSubgraphU Γ' T₂
    have hV₂_comp : IsCompact V₂ := (hUT₁_comp.union hbd_comp).union hUT₂_comp
    have hV₂_conn : IsConnected V₂ :=
      IsConnected.union ⟨p_a₂, Or.inr hp_a₂_bd, hp_a₂_T₂⟩
        (IsConnected.union ⟨p_a₁, hp_a₁_T₁, hp_a₁_bd⟩ hUT₁_conn hbd_conn) hUT₂_conn
    have hV₁_sub : V₁ ⊆ (interior Δ₀')ᶜ :=
      fun p hp => (hU'_sub (graphDrawingSubgraphU_subset_U' Γ' Q hp)).2
    have hbd_sub_compl : subBd Δ ⊆ (interior Δ₀')ᶜ := by
      intro p hp hp_int₀
      have hp_int_Δ : p ∈ interior Δ := interior_mono hΔ₀'_sub hp_int₀
      rw [subBd_eq_diff_interior_of_isClosed (isClosed_of_isClosedDisc hΔ)] at hp
      exact hp.2 hp_int_Δ
    have hV₂_sub : V₂ ⊆ (interior Δ₀')ᶜ :=
      union_subset (union_subset
        (fun p hp => (hU'_sub (graphDrawingSubgraphU_subset_U' Γ' T₁ hp)).2)
        hbd_sub_compl)
        (fun p hp => (hU'_sub (graphDrawingSubgraphU_subset_U' Γ' T₂ hp)).2)
    obtain ⟨p, hp₁, hp₂⟩ := nonempty_inter_of_crosses_on_inner_bd hΔ₀'_disc hφ₀' hcr
      ⟨hxG, rfl⟩ ⟨hyG, rfl⟩ ⟨hz₁G, rfl⟩ ⟨hz₂G, rfl⟩
      hUQ_comp hV₂_comp hUQ_conn hV₂_conn hV₁_sub hV₂_sub
      (Or.inl (mem_iUnion₂.mpr ⟨x, hQ.left_mem, hxG, rfl⟩))
      (Or.inl (mem_iUnion₂.mpr ⟨y, hQ.right_mem, hyG, rfl⟩))
      (Or.inl (Or.inl (Or.inl (mem_iUnion₂.mpr ⟨z₁, hT₁.right_mem, hz₁G, rfl⟩))))
      (Or.inr (Or.inl (mem_iUnion₂.mpr ⟨z₂, hT₂.right_mem, hz₂G, rfl⟩)))
    rcases hp₂ with (hpT₁ | hp_bd) | hpT₂
    · obtain ⟨u, huQ, huT₁⟩ :=
        nonempty_inter_vertexSet_of_nonempty_inter_subgraphU' Γ' hQ.le hT₁.le ⟨p, hp₁, hpT₁⟩
      exact disjoint_left.mp hdisj₁ huQ huT₁
    · have hp_U : p ∈ Γ'.drawing.U := graphDrawingSubgraphU_subset_U' Γ' Q hp₁
      have hp_inter : p ∈ Γ'.drawing.U ∩ subBd Δ := ⟨hp_U, hp_bd⟩
      rw [hU'_inter_bd, mem_iUnion₂] at hp_inter
      rcases hp_inter with ⟨v, hv_Ω', hp_v⟩
      rw [N.Ω.restrict_bar hY_bar] at hv_Ω'
      have hv_V : p ∈ graphDrawingSubgraphU Γ' (section9SingleVertex N.G v) := by
        left; rw [mem_iUnion₂]; exact ⟨v, by simp [section9SingleVertex], hp_v⟩
      obtain ⟨u, huQ, huv⟩ := nonempty_inter_vertexSet_of_nonempty_inter_subgraphU' Γ'
        hQ.le (section9SingleVertex_le (hbar'G (by rw [N.Ω.restrict_bar hY_bar]; exact hv_Ω')))
        ⟨p, hp₁, hv_V⟩
      rw [vertexSet_section9SingleVertex, mem_singleton_iff] at huv
      subst u
      rcases hv_Ω' with rfl | rfl
      · exact disjoint_left.mp hdisj₁ huQ hT₁.left_mem
      · exact disjoint_left.mp hdisj₂ huQ hT₂.left_mem
    · obtain ⟨u, huQ, huT₂⟩ :=
        nonempty_inter_vertexSet_of_nonempty_inter_subgraphU' Γ' hQ.le hT₂.le ⟨p, hp₁, hpT₂⟩
      exact disjoint_left.mp hdisj₂ huQ huT₂

/-- If `Ω₀.IsClockwise3 z₁ z₃ z₂` and `Ω₀.IsClockwise3 z₁ z₃ z₄`, there is a compact connected arc
`K₁ ⊆ subBd Δ₀` containing `q₁` and `q₃` and avoiding `q₂` and `q₄`. -/
theorem exists_arc_in_subBd_avoiding_pair {G : Graph α β}
    {Γ : GraphDrawing G EuclideanPlane} {Ω₀ : CyclicPerm α} {Δ₀ : Set EuclideanPlane}
    {φ₀ : Circle ≃ₜ subBd Δ₀} (hagrees₀ : DrawingAgreesWithOArcHomeo Γ Ω₀ (subBd Δ₀) φ₀)
    {z₁ z₃ z₂ z₄ : α}
    (hclw₂ : Ω₀.IsClockwise3 z₁ z₃ z₂) (hclw₄ : Ω₀.IsClockwise3 z₁ z₃ z₄)
    {q₁ q₃ q₂ q₄ : EuclideanPlane}
    (hq₁ : q₁ ∈ graphDrawingVertexSet Γ z₁)
    (hq₃ : q₃ ∈ graphDrawingVertexSet Γ z₃)
    (hq₂ : q₂ ∈ graphDrawingVertexSet Γ z₂)
    (hq₄ : q₄ ∈ graphDrawingVertexSet Γ z₄) :
    ∃ K₁ : Set EuclideanPlane,
      IsCompact K₁ ∧ IsConnected K₁ ∧ q₁ ∈ K₁ ∧ q₃ ∈ K₁ ∧ K₁ ⊆ subBd Δ₀ ∧
      q₂ ∉ K₁ ∧ q₄ ∉ K₁ := by
  obtain ⟨t₁, t₃, t₂, ht13, ht32, ht21, hφ₁, hφ₃, _⟩ := hagrees₀.2 z₁ z₃ z₂ hclw₂
  let f : ℝ → EuclideanPlane := fun t => (φ₀ (Circle.exp t)).1
  have hf_cont : Continuous f :=
    continuous_subtype_val.comp (φ₀.continuous.comp Circle.exp.continuous)
  let K₁ : Set EuclideanPlane := f '' Icc t₁ t₃
  have h_not_mem : ∀ {u : α} {q_u : EuclideanPlane},
      Ω₀.IsClockwise3 z₁ z₃ u → q_u ∈ graphDrawingVertexSet Γ u → q_u ∉ K₁ := by
    rintro u q_u hclw_u hq_u ⟨t, ⟨ht₁, ht₃⟩, ht_eq⟩
    have hφ_t : (φ₀ (Circle.exp t)).1 ∈ graphDrawingVertexSet Γ u := by
      change f t ∈ _; rw [ht_eq]; exact hq_u
    by_cases h_eq : t = t₁
    · subst h_eq
      have hzu : z₁ = u := graphDrawingVertexSet_inj Γ hφ₁ hφ_t
      exact (Ω₀.isClockwise3_iff.mp hclw_u).2.1 hzu
    · have ht1_lt : t₁ < t := lt_of_le_of_ne ht₁ (Ne.symm h_eq)
      have ht_2pi : t < t₁ + 2 * Real.pi := lt_of_le_of_lt ht₃ (ht32.trans ht21)
      have ht3_2pi : t₃ < t₁ + 2 * Real.pi := ht32.trans ht21
      have hlt_ang := angleDiff_lt_of_isClockwise3 hagrees₀ hclw_u hφ₁ hφ₃ hφ_t
      rw [angleDiff_exp_of_lt ht13 ht3_2pi, angleDiff_exp_of_lt ht1_lt ht_2pi] at hlt_ang
      linarith
  refine ⟨K₁, isCompact_Icc.image hf_cont,
    (isConnected_Icc ht13.le).image f hf_cont.continuousOn,
    ⟨t₁, left_mem_Icc.mpr ht13.le, hφ₁.2.symm.trans hq₁.2⟩,
    ⟨t₃, right_mem_Icc.mpr ht13.le, hφ₃.2.symm.trans hq₃.2⟩,
    by rintro _ ⟨t, _, rfl⟩; exact (φ₀ (Circle.exp t)).2,
    h_not_mem hclw₂ hq₂, h_not_mem hclw₄ hq₄⟩

/-- If `T₁, T₂, T₃, T₄ ≤ N.G` are pairwise vertex-disjoint paths from `a₁, a₂, a₃, a₄ ∈ N.Ω.bar`
to `z₁, z₂, z₃, z₄ ∈ N.Ω₀.bar`, then `N.Ω₀.Crosses z₁ z₂ z₃ z₄` implies
`¬ N.Ω.Crosses a₁ a₃ a₂ a₄`. -/
theorem not_crosses_outer_of_crosses_inner_swap {N : Neighborhood α β} (hrural : N.IsRural)
    {T₁ T₂ T₃ T₄ : Graph α β} {a₁ a₂ a₃ a₄ z₁ z₂ z₃ z₄ : α}
    (hT₁ : IsGraphPathWithEnds N.G T₁ a₁ z₁) (ha₁ : a₁ ∈ N.Ω.bar) (hz₁ : z₁ ∈ N.Ω₀.bar)
    (hT₂ : IsGraphPathWithEnds N.G T₂ a₂ z₂) (ha₂ : a₂ ∈ N.Ω.bar) (hz₂ : z₂ ∈ N.Ω₀.bar)
    (hT₃ : IsGraphPathWithEnds N.G T₃ a₃ z₃) (ha₃ : a₃ ∈ N.Ω.bar) (hz₃ : z₃ ∈ N.Ω₀.bar)
    (hT₄ : IsGraphPathWithEnds N.G T₄ a₄ z₄) (ha₄ : a₄ ∈ N.Ω.bar) (hz₄ : z₄ ∈ N.Ω₀.bar)
    (hd12 : Disjoint V(T₁) V(T₂)) (hd14 : Disjoint V(T₁) V(T₄))
    (hd32 : Disjoint V(T₃) V(T₂)) (hd34 : Disjoint V(T₃) V(T₄))
    (hcr₀ : N.Ω₀.Crosses z₁ z₂ z₃ z₄) :
    ¬ N.Ω.Crosses a₁ a₃ a₂ a₄ := by
  intro hcr
  obtain ⟨Γ, Δ, Δ₀, hΔ, hΔ₀_sub, hU_sub, hbd, hbd₀, ⟨φ, _, hφ⟩, hinner⟩ := hrural
  rcases hinner with ⟨_, hΩ₀_emp⟩ | ⟨hΔ₀_disc, φ₀, _, hφ₀⟩
  · exact notMem_empty z₁ (hΩ₀_emp ▸ hz₁)
  · have ha₁G : a₁ ∈ V(N.G) := N.bar_subset ha₁
    have ha₂G : a₂ ∈ V(N.G) := N.bar_subset ha₂
    have ha₃G : a₃ ∈ V(N.G) := N.bar_subset ha₃
    have ha₄G : a₄ ∈ V(N.G) := N.bar_subset ha₄
    have hz₁G : z₁ ∈ V(N.G) := N.bar₀_subset hz₁
    have hz₂G : z₂ ∈ V(N.G) := N.bar₀_subset hz₂
    have hz₃G : z₃ ∈ V(N.G) := N.bar₀_subset hz₃
    have hz₄G : z₄ ∈ V(N.G) := N.bar₀_subset hz₄
    let p₁ := (Γ.iso.vertexEquiv ⟨a₁, ha₁G⟩).1
    let p₂ := (Γ.iso.vertexEquiv ⟨a₂, ha₂G⟩).1
    let p₃ := (Γ.iso.vertexEquiv ⟨a₃, ha₃G⟩).1
    let p₄ := (Γ.iso.vertexEquiv ⟨a₄, ha₄G⟩).1
    let q₁ := (Γ.iso.vertexEquiv ⟨z₁, hz₁G⟩).1
    let q₂ := (Γ.iso.vertexEquiv ⟨z₂, hz₂G⟩).1
    let q₃ := (Γ.iso.vertexEquiv ⟨z₃, hz₃G⟩).1
    let q₄ := (Γ.iso.vertexEquiv ⟨z₄, hz₄G⟩).1
    have hq₁_v : q₁ ∈ graphDrawingVertexSet Γ z₁ := ⟨hz₁G, rfl⟩
    have hq₂_v : q₂ ∈ graphDrawingVertexSet Γ z₂ := ⟨hz₂G, rfl⟩
    have hq₃_v : q₃ ∈ graphDrawingVertexSet Γ z₃ := ⟨hz₃G, rfl⟩
    have hq₄_v : q₄ ∈ graphDrawingVertexSet Γ z₄ := ⟨hz₄G, rfl⟩
    have hex_K₁ : ∃ K₁ : Set EuclideanPlane,
        IsCompact K₁ ∧ IsConnected K₁ ∧ q₁ ∈ K₁ ∧ q₃ ∈ K₁ ∧ K₁ ⊆ subBd Δ₀ ∧
        q₂ ∉ K₁ ∧ q₄ ∉ K₁ := by
      rcases N.Ω₀.crosses_iff_interval.mp hcr₀ with ⟨h132, h241⟩ | ⟨h142, h231⟩
      · have hc4 := N.Ω₀.isClockwise4_iff_interval.mpr ⟨h132, h241⟩
        have h134 : N.Ω₀.IsClockwise3 z₁ z₃ z₄ :=
          N.Ω₀.isClockwise3_rotate
            (N.Ω₀.isClockwise4_iff_interval.mp
              (N.Ω₀.isClockwise4_rotate (N.Ω₀.isClockwise4_rotate (N.Ω₀.isClockwise4_rotate
                hc4)))).1.2
        exact exists_arc_in_subBd_avoiding_pair hφ₀ h132.2 h134 hq₁_v hq₃_v hq₂_v hq₄_v
      · have hc4 := N.Ω₀.isClockwise4_iff_interval.mpr ⟨h142, h231⟩
        have h312 : N.Ω₀.IsClockwise3 z₃ z₁ z₂ := N.Ω₀.isClockwise3_rotate h231.2
        have h314 : N.Ω₀.IsClockwise3 z₃ z₁ z₄ :=
          (N.Ω₀.isClockwise4_iff_interval.mp (N.Ω₀.isClockwise4_rotate hc4)).2.2
        obtain ⟨K₁, hcomp, hconn, hq₃_K₁, hq₁_K₁, hsub, hq₂_not, hq₄_not⟩ :=
          exists_arc_in_subBd_avoiding_pair hφ₀ h312 h314 hq₃_v hq₁_v hq₂_v hq₄_v
        exact ⟨K₁, hcomp, hconn, hq₁_K₁, hq₃_K₁, hsub, hq₂_not, hq₄_not⟩
    obtain ⟨R₁, hR₁_comp, hR₁_conn, hq₁_R₁, hq₃_R₁, hR₁_bd₀, hq₂_not_R₁, hq₄_not_R₁⟩ := hex_K₁
    have hbd₀_eq : subBd Δ₀ = discBd Δ₀ := subBd_eq_discBd_plane hΔ₀_disc
    have hbd₀_sub : subBd Δ₀ ⊆ Δ₀ := hbd₀_eq ▸ Surface.discBd_subset Δ₀
    have hq₁_bd₀ : q₁ ∈ subBd Δ₀ := (hbd₀ z₁ hz₁G).mpr hz₁ hq₁_v
    have hq₂_bd₀ : q₂ ∈ subBd Δ₀ := (hbd₀ z₂ hz₂G).mpr hz₂ hq₂_v
    have hq₃_bd₀ : q₃ ∈ subBd Δ₀ := (hbd₀ z₃ hz₃G).mpr hz₃ hq₃_v
    have hq₄_bd₀ : q₄ ∈ subBd Δ₀ := (hbd₀ z₄ hz₄G).mpr hz₄ hq₄_v
    obtain ⟨R₀, hR₀_comp, hR₀_conn, hq₂_R₀, hq₄_R₀, hR₀_Δ₀, hR₀_int⟩ :=
      exists_compact_connected_in_disc_avoiding_bd hΔ₀_disc (hbd₀_sub hq₂_bd₀) (hbd₀_sub hq₄_bd₀)
    let F : Set EuclideanPlane := {q₁, q₃, q₂, q₄}
    have hF_closed : IsClosed F :=
      (Finite.insert _ (Finite.insert _ (Finite.insert _ (finite_singleton _)))).isClosed
    have hF_sub : F ⊆ discBd Δ₀ := by
      rw [← hbd₀_eq]; rintro x (rfl | rfl | rfl | rfl) <;> assumption
    obtain ⟨Ψ, _, hΨ_cont, _, _, hΨ_inj, hΨ_sub, hΨ_fix, hΨ_int⟩ :=
      exists_disc_shrink_map hΔ₀_disc hF_closed hF_sub
    have hR₁_Δ₀ : R₁ ⊆ Δ₀ := hR₁_bd₀.trans hbd₀_sub
    let K₁ := Ψ '' R₁
    let K₀ := Ψ '' R₀
    have hK₁_comp : IsCompact K₁ := hR₁_comp.image_of_continuousOn (hΨ_cont.mono hR₁_Δ₀)
    have hK₀_comp : IsCompact K₀ := hR₀_comp.image_of_continuousOn (hΨ_cont.mono hR₀_Δ₀)
    have hK₁_conn : IsConnected K₁ := hR₁_conn.image Ψ (hΨ_cont.mono hR₁_Δ₀)
    have hK₀_conn : IsConnected K₀ := hR₀_conn.image Ψ (hΨ_cont.mono hR₀_Δ₀)
    have hq₁_K₁ : q₁ ∈ K₁ := ⟨q₁, hq₁_R₁, hΨ_fix q₁ (by simp [F])⟩
    have hq₃_K₁ : q₃ ∈ K₁ := ⟨q₃, hq₃_R₁, hΨ_fix q₃ (by simp [F])⟩
    have hq₂_K₀ : q₂ ∈ K₀ := ⟨q₂, hq₂_R₀, hΨ_fix q₂ (by simp [F])⟩
    have hq₄_K₀ : q₄ ∈ K₀ := ⟨q₄, hq₄_R₀, hΨ_fix q₄ (by simp [F])⟩
    have hK₁_Δ₀ : K₁ ⊆ Δ₀ := (image_mono hR₁_Δ₀).trans hΨ_sub
    have hK₀_Δ₀ : K₀ ⊆ Δ₀ := (image_mono hR₀_Δ₀).trans hΨ_sub
    have hΔ₀_diff_bd : Δ₀ \ discBd Δ₀ = interior Δ₀ := by
      rw [← hbd₀_eq, subBd_eq_diff_interior_of_isClosed (isClosed_of_isClosedDisc hΔ₀_disc)]
      ext x; simp only [mem_sdiff, not_and, not_not]
      exact ⟨fun ⟨hx, h⟩ => h hx, fun hx => ⟨interior_subset hx, fun _ => hx⟩⟩
    have hK₁_int : K₁ ⊆ {q₁, q₃} ∪ interior Δ₀ := by
      rintro _ ⟨y, hyR₁, rfl⟩
      by_cases hyF : y ∈ F
      · rcases hyF with rfl | rfl | rfl | rfl
        · left; left; exact hΨ_fix q₁ (by simp [F])
        · left; right; exact hΨ_fix q₃ (by simp [F])
        · exact (hq₂_not_R₁ hyR₁).elim
        · exact (hq₄_not_R₁ hyR₁).elim
      · right; rw [← hΔ₀_diff_bd]; exact hΨ_int y ⟨hR₁_Δ₀ hyR₁, hyF⟩
    have hK₀_int : K₀ ⊆ {q₂, q₄} ∪ interior Δ₀ := by
      rintro _ ⟨y, hyR₀, rfl⟩
      by_cases hyF : y ∈ F
      · rw [hΨ_fix y hyF]
        rcases hR₀_int hyR₀ with hy | hy
        · exact Or.inl hy
        · apply Or.inr
          exact hy
      · exact Or.inr (hΔ₀_diff_bd ▸ hΨ_int y ⟨hR₀_Δ₀ hyR₀, hyF⟩)
    have hdisj_K₁K₀ : Disjoint K₁ K₀ := by
      rw [disjoint_left]
      rintro _ ⟨y₁, hy₁, rfl⟩ ⟨y₂, hy₂, hy_eq⟩
      have hy12 : y₁ = y₂ := hΨ_inj (hR₁_Δ₀ hy₁) (hR₀_Δ₀ hy₂) hy_eq.symm
      subst hy12
      rcases hR₀_int hy₂ with (rfl | rfl) | hy_int
      · exact hq₂_not_R₁ hy₁
      · exact hq₄_not_R₁ hy₁
      · exact (subBd_eq_diff_interior_of_isClosed
          (isClosed_of_isClosedDisc hΔ₀_disc) ▸ hR₁_bd₀ hy₁).2 hy_int
    have hUT₁_Δ : graphDrawingSubgraphU Γ T₁ ⊆ Δ :=
      (graphDrawingSubgraphU_subset_U' Γ T₁).trans (hU_sub.trans sdiff_subset)
    have hUT₂_Δ : graphDrawingSubgraphU Γ T₂ ⊆ Δ :=
      (graphDrawingSubgraphU_subset_U' Γ T₂).trans (hU_sub.trans sdiff_subset)
    have hUT₃_Δ : graphDrawingSubgraphU Γ T₃ ⊆ Δ :=
      (graphDrawingSubgraphU_subset_U' Γ T₃).trans (hU_sub.trans sdiff_subset)
    have hUT₄_Δ : graphDrawingSubgraphU Γ T₄ ⊆ Δ :=
      (graphDrawingSubgraphU_subset_U' Γ T₄).trans (hU_sub.trans sdiff_subset)
    obtain ⟨hUT₁_comp, hUT₁_conn, _, _⟩ :=
      isCompact_and_isConnected_subgraphU_of_isGraphPathWithEnds hΔ hT₁ hUT₁_Δ
    obtain ⟨hUT₂_comp, hUT₂_conn, _, _⟩ :=
      isCompact_and_isConnected_subgraphU_of_isGraphPathWithEnds hΔ hT₂ hUT₂_Δ
    obtain ⟨hUT₃_comp, hUT₃_conn, _, _⟩ :=
      isCompact_and_isConnected_subgraphU_of_isGraphPathWithEnds hΔ hT₃ hUT₃_Δ
    obtain ⟨hUT₄_comp, hUT₄_conn, _, _⟩ :=
      isCompact_and_isConnected_subgraphU_of_isGraphPathWithEnds hΔ hT₄ hUT₄_Δ
    have hq₁_T₁ : q₁ ∈ graphDrawingSubgraphU Γ T₁ :=
      Or.inl (mem_iUnion₂.mpr ⟨z₁, hT₁.right_mem, hz₁G, rfl⟩)
    have hq₂_T₂ : q₂ ∈ graphDrawingSubgraphU Γ T₂ :=
      Or.inl (mem_iUnion₂.mpr ⟨z₂, hT₂.right_mem, hz₂G, rfl⟩)
    have hq₃_T₃ : q₃ ∈ graphDrawingSubgraphU Γ T₃ :=
      Or.inl (mem_iUnion₂.mpr ⟨z₃, hT₃.right_mem, hz₃G, rfl⟩)
    have hq₄_T₄ : q₄ ∈ graphDrawingSubgraphU Γ T₄ :=
      Or.inl (mem_iUnion₂.mpr ⟨z₄, hT₄.right_mem, hz₄G, rfl⟩)
    let V₁ := (graphDrawingSubgraphU Γ T₁ ∪ K₁) ∪ graphDrawingSubgraphU Γ T₃
    let V₂ := (graphDrawingSubgraphU Γ T₂ ∪ K₀) ∪ graphDrawingSubgraphU Γ T₄
    have hV₁_comp : IsCompact V₁ := (hUT₁_comp.union hK₁_comp).union hUT₃_comp
    have hV₂_comp : IsCompact V₂ := (hUT₂_comp.union hK₀_comp).union hUT₄_comp
    have hV₁_conn : IsConnected V₁ :=
      IsConnected.union ⟨q₃, Or.inr hq₃_K₁, hq₃_T₃⟩
        (IsConnected.union ⟨q₁, hq₁_T₁, hq₁_K₁⟩ hUT₁_conn hK₁_conn) hUT₃_conn
    have hV₂_conn : IsConnected V₂ :=
      IsConnected.union ⟨q₄, Or.inr hq₄_K₀, hq₄_T₄⟩
        (IsConnected.union ⟨q₂, hq₂_T₂, hq₂_K₀⟩ hUT₂_conn hK₀_conn) hUT₄_conn
    have hV₁_Δ : V₁ ⊆ Δ :=
      union_subset (union_subset hUT₁_Δ (hK₁_Δ₀.trans hΔ₀_sub)) hUT₃_Δ
    have hV₂_Δ : V₂ ⊆ Δ :=
      union_subset (union_subset hUT₂_Δ (hK₀_Δ₀.trans hΔ₀_sub)) hUT₄_Δ
    have hp₁_V₁ : p₁ ∈ V₁ :=
      Or.inl (Or.inl (Or.inl (mem_iUnion₂.mpr ⟨a₁, hT₁.left_mem, ha₁G, rfl⟩)))
    have hp₃_V₁ : p₃ ∈ V₁ :=
      Or.inr (Or.inl (mem_iUnion₂.mpr ⟨a₃, hT₃.left_mem, ha₃G, rfl⟩))
    have hp₂_V₂ : p₂ ∈ V₂ :=
      Or.inl (Or.inl (Or.inl (mem_iUnion₂.mpr ⟨a₂, hT₂.left_mem, ha₂G, rfl⟩)))
    have hp₄_V₂ : p₄ ∈ V₂ :=
      Or.inr (Or.inl (mem_iUnion₂.mpr ⟨a₄, hT₄.left_mem, ha₄G, rfl⟩))
    have hcross_bd : PairsCrossOn (discBd Δ) p₁ p₃ p₂ p₄ := by
      rw [discBd_eq_subBd hΔ]
      exact pairsCrossOn_of_crosses hφ hcr ⟨ha₁G, rfl⟩ ⟨ha₃G, rfl⟩ ⟨ha₂G, rfl⟩ ⟨ha₄G, rfl⟩
    obtain ⟨x, hx₁, hx₂⟩ := disc_crossing Δ V₁ V₂ p₁ p₃ p₂ p₄ hΔ hV₁_Δ hV₂_Δ
      hV₁_comp hV₂_comp hV₁_conn hV₂_conn hp₁_V₁ hp₃_V₁ hp₂_V₂ hp₄_V₂ hcross_bd
    have h_not_T_K₀ : ∀ {T : Graph α β}, T ≤ N.G →
        Disjoint V(T) V(T₂) → Disjoint V(T) V(T₄) →
        x ∈ graphDrawingSubgraphU Γ T → x ∈ K₀ → False := by
      intro T hTG hd2 hd4 hxT hxK₀
      rcases hK₀_int hxK₀ with (rfl | rfl) | hx_int₀
      · obtain ⟨u, huT, huT₂⟩ :=
          nonempty_inter_vertexSet_of_nonempty_inter_subgraphU' Γ hTG hT₂.le ⟨q₂, hxT, hq₂_T₂⟩
        exact disjoint_left.mp hd2 huT huT₂
      · obtain ⟨u, huT, huT₄⟩ :=
          nonempty_inter_vertexSet_of_nonempty_inter_subgraphU' Γ hTG hT₄.le ⟨q₄, hxT, hq₄_T₄⟩
        exact disjoint_left.mp hd4 huT huT₄
      · exact (hU_sub (graphDrawingSubgraphU_subset_U' Γ T hxT)).2 hx_int₀
    have h_not_K₁_T : ∀ {T : Graph α β}, T ≤ N.G →
        Disjoint V(T₁) V(T) → Disjoint V(T₃) V(T) →
        x ∈ K₁ → x ∈ graphDrawingSubgraphU Γ T → False := by
      intro T hTG hd1 hd3 hxK₁ hxT
      rcases hK₁_int hxK₁ with (rfl | rfl) | hx_int₀
      · obtain ⟨u, huT₁, huT⟩ :=
          nonempty_inter_vertexSet_of_nonempty_inter_subgraphU' Γ hT₁.le hTG ⟨q₁, hq₁_T₁, hxT⟩
        exact disjoint_left.mp hd1 huT₁ huT
      · obtain ⟨u, huT₃, huT⟩ :=
          nonempty_inter_vertexSet_of_nonempty_inter_subgraphU' Γ hT₃.le hTG ⟨q₃, hq₃_T₃, hxT⟩
        exact disjoint_left.mp hd3 huT₃ huT
      · exact (hU_sub (graphDrawingSubgraphU_subset_U' Γ T hxT)).2 hx_int₀
    rcases hx₁ with (hxT₁ | hxK₁) | hxT₃ <;> rcases hx₂ with (hxT₂ | hxK₀) | hxT₄
    · obtain ⟨u, hu₁, hu₂⟩ :=
        nonempty_inter_vertexSet_of_nonempty_inter_subgraphU' Γ hT₁.le hT₂.le ⟨x, hxT₁, hxT₂⟩
      exact disjoint_left.mp hd12 hu₁ hu₂
    · exact h_not_T_K₀ hT₁.le hd12 hd14 hxT₁ hxK₀
    · obtain ⟨u, hu₁, hu₄⟩ :=
        nonempty_inter_vertexSet_of_nonempty_inter_subgraphU' Γ hT₁.le hT₄.le ⟨x, hxT₁, hxT₄⟩
      exact disjoint_left.mp hd14 hu₁ hu₄
    · exact h_not_K₁_T hT₂.le hd12 hd32 hxK₁ hxT₂
    · exact disjoint_left.mp hdisj_K₁K₀ hxK₁ hxK₀
    · exact h_not_K₁_T hT₄.le hd14 hd34 hxK₁ hxT₄
    · obtain ⟨u, hu₃, hu₂⟩ :=
        nonempty_inter_vertexSet_of_nonempty_inter_subgraphU' Γ hT₃.le hT₂.le ⟨x, hxT₃, hxT₂⟩
      exact disjoint_left.mp hd32 hu₃ hu₂
    · exact h_not_T_K₀ hT₃.le hd32 hd34 hxT₃ hxK₀
    · obtain ⟨u, hu₃, hu₄⟩ :=
        nonempty_inter_vertexSet_of_nonempty_inter_subgraphU' Γ hT₃.le hT₄.le ⟨x, hxT₃, hxT₄⟩
      exact disjoint_left.mp hd34 hu₃ hu₄

/-- Four pairwise vertex-disjoint paths `T₁, T₂, T₃, T₄ ≤ N.G` from `a₁, a₂, a₃, a₄ ∈ N.Ω.bar` to
`z₁, z₂, z₃, z₄ ∈ N.Ω₀.bar` preserve and reflect crossing of opposite pairs:
`N.Ω.Crosses a₁ a₃ a₂ a₄ ↔ N.Ω₀.Crosses z₁ z₃ z₂ z₄`. -/
theorem crosses_outer_iff_crosses_inner_of_disjoint_paths {N : Neighborhood α β}
  (hrural : N.IsRural)
    {T₁ T₂ T₃ T₄ : Graph α β} {a₁ a₂ a₃ a₄ z₁ z₂ z₃ z₄ : α}
    (hT₁ : IsGraphPathWithEnds N.G T₁ a₁ z₁) (ha₁ : a₁ ∈ N.Ω.bar) (hz₁ : z₁ ∈ N.Ω₀.bar)
    (hT₂ : IsGraphPathWithEnds N.G T₂ a₂ z₂) (ha₂ : a₂ ∈ N.Ω.bar) (hz₂ : z₂ ∈ N.Ω₀.bar)
    (hT₃ : IsGraphPathWithEnds N.G T₃ a₃ z₃) (ha₃ : a₃ ∈ N.Ω.bar) (hz₃ : z₃ ∈ N.Ω₀.bar)
    (hT₄ : IsGraphPathWithEnds N.G T₄ a₄ z₄) (ha₄ : a₄ ∈ N.Ω.bar) (hz₄ : z₄ ∈ N.Ω₀.bar)
    (hd12 : Disjoint V(T₁) V(T₂)) (hd13 : Disjoint V(T₁) V(T₃)) (hd14 : Disjoint V(T₁) V(T₄))
    (hd23 : Disjoint V(T₂) V(T₃)) (hd24 : Disjoint V(T₂) V(T₄)) (hd34 : Disjoint V(T₃) V(T₄)) :
    N.Ω.Crosses a₁ a₃ a₂ a₄ ↔ N.Ω₀.Crosses z₁ z₃ z₂ z₄ := by
  have ha12 : a₁ ≠ a₂ := fun h => disjoint_left.mp hd12 hT₁.left_mem (h ▸ hT₂.left_mem)
  have ha13 : a₁ ≠ a₃ := fun h => disjoint_left.mp hd13 hT₁.left_mem (h ▸ hT₃.left_mem)
  have ha14 : a₁ ≠ a₄ := fun h => disjoint_left.mp hd14 hT₁.left_mem (h ▸ hT₄.left_mem)
  have ha23 : a₂ ≠ a₃ := fun h => disjoint_left.mp hd23 hT₂.left_mem (h ▸ hT₃.left_mem)
  have ha24 : a₂ ≠ a₄ := fun h => disjoint_left.mp hd24 hT₂.left_mem (h ▸ hT₄.left_mem)
  have ha34 : a₃ ≠ a₄ := fun h => disjoint_left.mp hd34 hT₃.left_mem (h ▸ hT₄.left_mem)
  have hz12 : z₁ ≠ z₂ := fun h => disjoint_left.mp hd12 hT₁.right_mem (h ▸ hT₂.right_mem)
  have hz13 : z₁ ≠ z₃ := fun h => disjoint_left.mp hd13 hT₁.right_mem (h ▸ hT₃.right_mem)
  have hz14 : z₁ ≠ z₄ := fun h => disjoint_left.mp hd14 hT₁.right_mem (h ▸ hT₄.right_mem)
  have hz23 : z₂ ≠ z₃ := fun h => disjoint_left.mp hd23 hT₂.right_mem (h ▸ hT₃.right_mem)
  have hz24 : z₂ ≠ z₄ := fun h => disjoint_left.mp hd24 hT₂.right_mem (h ▸ hT₄.right_mem)
  have hz34 : z₃ ≠ z₄ := fun h => disjoint_left.mp hd34 hT₃.right_mem (h ▸ hT₄.right_mem)
  refine ⟨fun hcr => ?_, fun hcr₀ => ?_⟩
  · rcases N.Ω₀.crosses_of_four_distinct hz₁ hz₂ hz₃ hz₄ hz12 hz13 hz14 hz23 hz24 hz34 with
      h14 | h12 | h13
    · exfalso
      exact not_crosses_outer_of_crosses_inner_swap hrural
        hT₁ ha₁ hz₁ hT₄ ha₄ hz₄ hT₃ ha₃ hz₃ hT₂ ha₂ hz₂
        hd14 hd12 hd34 hd23.symm h14.swap_right hcr.swap_right
    · exfalso
      exact not_crosses_outer_of_crosses_inner_swap hrural
        hT₁ ha₁ hz₁ hT₂ ha₂ hz₂ hT₃ ha₃ hz₃ hT₄ ha₄ hz₄
        hd12 hd14 hd23.symm hd34 h12 hcr
    · exact h13
  · rcases N.Ω.crosses_of_four_distinct ha₁ ha₂ ha₃ ha₄ ha12 ha13 ha14 ha23 ha24 ha34 with
      h14 | h12 | h13
    · exfalso
      exact not_crosses_outer_of_crosses_inner_swap hrural
        hT₁ ha₁ hz₁ hT₃ ha₃ hz₃ hT₄ ha₄ hz₄ hT₂ ha₂ hz₂
        hd13 hd12 hd34.symm hd24.symm hcr₀.swap_right h14.swap_right
    · exfalso
      exact not_crosses_outer_of_crosses_inner_swap hrural
        hT₁ ha₁ hz₁ hT₃ ha₃ hz₃ hT₂ ha₂ hz₂ hT₄ ha₄ hz₄
        hd13 hd14 hd23 hd24 hcr₀ h12
    · exact h13

/-- **Graph Minors IX, (9.1), Claim (4)** (page 62):
"For any $P \in \mathscr{P}$, at most one internal vertex of $P$ is in $\bar{\Omega}_1$, and the
subpaths of $P$ from such a vertex to the ends of $P$ both have an edge in $E(G)$." -/
theorem lemma_9_1_claim_4
    {S : Society α β} {p : ℕ}
    {N : Neighborhood α β} {S_comp : Society α β} {P_set : Set (Graph α β)}
    (hmin : IsMinSection9Config S p N S_comp P_set) {P : Graph α β} (hP_in : P ∈ P_set) :
    (pathInternalVerts S_comp.G P ∩ N.Ω.bar).Subsingleton ∧
      ∀ c ∈ pathInternalVerts S_comp.G P ∩ N.Ω.bar,
        ∀ {a b : α} {Q : Graph α β}, S_comp.IsOmegaPathWithEnds P a b → Q ≤ P →
          (IsGraphPathWithEnds P Q c a ∨ IsGraphPathWithEnds P Q c b) →
          (E(Q) ∩ E(S.G)).Nonempty := by
  have hbar_eq : N.Ω.bar = S_comp.Ω.bar := by rw [hmin.1.1.2.1]
  rw [hbar_eq]
  obtain ⟨hsub, hnonsep⟩ := lemma_9_1_claim_4_nonSeparating hmin hP_in
  refine ⟨hsub, fun c hc {a b Q} hP_ends hQP hQ_or => ?_⟩
  have hQ_ns : S_comp.IsNonSeparatingOmegaPath Q := (hnonsep c hc).2 hP_ends hQP hQ_or
  have hQ_not_le : ¬ Q ≤ N.G :=
    fun hQ_N => (isSeparatingOmegaPath_of_isRural hmin.1.1 hmin.1.2.1 hQ_N hQ_ns.1).2 hQ_ns.2
  rcases hQ_or with hQ_ca | hQ_cb
  · exact nonempty_edgeSet_inter_of_not_le_right hmin.1.1 (hQ_ca.mono hP_ends.1.le)
      (fun h => hc.1.2 (h ▸ ⟨b, hP_ends.1⟩)) hQ_not_le
  · exact nonempty_edgeSet_inter_of_not_le_right hmin.1.1 (hQ_cb.mono hP_ends.1.le)
      (fun h => hc.1.2 (h ▸ ⟨a, hP_ends.1.symm⟩)) hQ_not_le

/-! ## Proof of Claim (5) and (9.1) (pages 62–63) -/

theorem IsGraphPathWithEnds.inc_left_unique {G P : Graph α β} {a b : α}
    (hP : IsGraphPathWithEnds G P a b) {e₁ e₂ : β}
    (he₁ : e₁ ∈ E(P)) (he₂ : e₂ ∈ E(P)) (hinc₁ : P.Inc e₁ a) (hinc₂ : P.Inc e₂ a) :
    e₁ = e₂ := by
  rcases hP with ⟨_, W, hW, _, hEP⟩
  rw [hEP, mem_ofPred_eq] at he₁ he₂
  exact unique_inc_first hW he₁ he₂ hinc₁ hinc₂

/-- Given a path `P` from `s` to `t` and a set `Y` meeting `V(P)`, there is a first vertex
`u ∈ V(P) ∩ Y` from `s` along `P`, splitting `P` into `P₁` (`s` to `u`) and `P₂` (`u` to `t`) with
`Disjoint (V(P₁) \ {u}) Y`. -/
theorem IsGraphPathWithEnds.exists_first_split_at_mem {G P : Graph α β} {s t : α} {Y : Set α}
    (hP : IsGraphPathWithEnds G P s t) (hne : (V(P) ∩ Y).Nonempty) :
    ∃ u ∈ V(P) ∩ Y, ∃ P₁ P₂ : Graph α β,
      P₁ ≤ P ∧ P₂ ≤ P ∧
      IsGraphPathWithEnds P P₁ s u ∧
      IsGraphPathWithEnds P P₂ u t ∧
      GM09.subgraphUnion P P₁ P₂ = P ∧
      V(P₁) ∩ V(P₂) = {u} ∧
      Disjoint E(P₁) E(P₂) ∧
      Disjoint (V(P₁) \ {u}) Y := by
  classical
  have hex : ∃ n : ℕ, ∃ u ∈ V(P) ∩ Y, ∃ P₁ P₂ : Graph α β,
      P₁ ≤ P ∧ P₂ ≤ P ∧
      IsGraphPathWithEnds P P₁ s u ∧
      IsGraphPathWithEnds P P₂ u t ∧
      GM09.subgraphUnion P P₁ P₂ = P ∧
      V(P₁) ∩ V(P₂) = {u} ∧
      Disjoint E(P₁) E(P₂) ∧
      V(P₁).ncard = n := by
    rcases hne with ⟨u₀, hu₀P, hu₀Y⟩
    obtain ⟨P₁, P₂, hP₁, hP₂, hp₁, hp₂, hunion, hinter, hdisjE⟩ := hP.exists_split_at hu₀P
    exact ⟨V(P₁).ncard, u₀, ⟨hu₀P, hu₀Y⟩, P₁, P₂, hP₁, hP₂, hp₁, hp₂, hunion, hinter, hdisjE, rfl⟩
  let n_min := Nat.find hex
  obtain ⟨u, hu, P₁, P₂, hP₁, hP₂, hp₁, hp₂, hunion, hinter, hdisjE, hcard⟩ := Nat.find_spec hex
  refine ⟨u, hu, P₁, P₂, hP₁, hP₂, hp₁, hp₂, hunion, hinter, hdisjE, ?_⟩
  rw [disjoint_left]
  intro z ⟨hzP₁, hzu⟩ hzY
  rw [mem_singleton_iff] at hzu
  obtain ⟨Q₁, Q₂, hQ₁, hQ₂, hq₁, hq₂, hunionQ, hinterQ, hdisjEQ⟩ := hp₁.exists_split_at hzP₁
  have hQ₁_P : Q₁ ≤ P := hQ₁.trans hP₁
  have hQ₂_P : Q₂ ≤ P := hQ₂.trans hP₁
  let P₂' := GM09.subgraphUnion P Q₂ P₂
  have hV_Q₂_P₂ : V(Q₂) ∩ V(P₂) = {u} := by
    refine Subset.antisymm ?_ (singleton_subset_iff.mpr ⟨hq₂.right_mem, hp₂.left_mem⟩)
    rw [← hinter]
    exact inter_subset_inter_left _ hQ₂.vertexSet_mono
  have hp₂' : IsGraphPathWithEnds P P₂' z t :=
    (hq₂.mono hP₁).subgraphUnion hp₂ hV_Q₂_P₂
  have hV_Q₁_P₂' : V(Q₁) ∩ V(P₂') = {z} := by
    ext w; simp only [P₂', vertexSet_subgraphUnion, mem_inter_iff, mem_union, mem_singleton_iff]
    refine ⟨?_, fun h => h ▸ ⟨hq₁.right_mem, Or.inl hq₂.left_mem⟩⟩
    rintro ⟨hwQ₁, hwQ₂ | hwP₂⟩
    · have hw_in : w ∈ V(Q₁) ∩ V(Q₂) := ⟨hwQ₁, hwQ₂⟩
      rwa [hinterQ, mem_singleton_iff] at hw_in
    · have hw_u : w = u := by
        have hw_in : w ∈ V(P₁) ∩ V(P₂) := ⟨hQ₁.vertexSet_mono hwQ₁, hwP₂⟩
        rwa [hinter, mem_singleton_iff] at hw_in
      subst hw_u
      have hu_in : w ∈ V(Q₁) ∩ V(Q₂) := ⟨hwQ₁, hq₂.right_mem⟩
      rwa [hinterQ, mem_singleton_iff] at hu_in
  have hP₂'_P : P₂' ≤ P := subgraphUnion_le hQ₂_P hP₂
  have hunion' : GM09.subgraphUnion P Q₁ P₂' = P := by
    have hQ₁Q₂ : GM09.subgraphUnion P Q₁ Q₂ = P₁ := by
      have h1 : GM09.subgraphUnion P Q₁ Q₂ ≤ P := subgraphUnion_le hQ₁_P hQ₂_P
      refine (Compatible.of_le_le h1 hP₁).ext ?_ ?_
      · rw [vertexSet_subgraphUnion, ← vertexSet_subgraphUnion P₁ Q₁ Q₂, hunionQ]
      · rw [edgeSet_subgraphUnion hQ₁_P hQ₂_P, ← edgeSet_subgraphUnion hQ₁ hQ₂, hunionQ]
    refine (Compatible.of_le_le (subgraphUnion_le hQ₁_P hP₂'_P) le_rfl).ext ?_ ?_
    · rw [vertexSet_subgraphUnion, vertexSet_subgraphUnion, ← union_assoc,
        ← vertexSet_subgraphUnion P Q₁ Q₂, hQ₁Q₂, ← vertexSet_subgraphUnion P P₁ P₂, hunion]
    · rw [edgeSet_subgraphUnion hQ₁_P hP₂'_P, edgeSet_subgraphUnion hQ₂_P hP₂, ← union_assoc,
        ← edgeSet_subgraphUnion hQ₁_P hQ₂_P, hQ₁Q₂, ← edgeSet_subgraphUnion hP₁ hP₂, hunion]
  have hdisjE' : Disjoint E(Q₁) E(P₂') :=
    disjoint_edgeSet_of_inter_singleton (hq₁.mono hP₁) hP₂'_P hV_Q₁_P₂'.subset
  have hu_not_Q₁ : u ∉ V(Q₁) := fun huQ₁ => by
    have hu_in : u ∈ V(Q₁) ∩ V(Q₂) := ⟨huQ₁, hq₂.right_mem⟩
    rw [hinterQ, mem_singleton_iff] at hu_in
    exact hzu hu_in.symm
  have hlt : V(Q₁).ncard < n_min := by
    change V(Q₁).ncard < Nat.find hex
    rw [← hcard]
    exact ncard_lt_ncard
      ⟨hQ₁.vertexSet_mono, fun hsub => hu_not_Q₁ (hsub hp₁.right_mem)⟩
      hp₁.vertexSet_finite
  exact Nat.find_min hex hlt ⟨z, ⟨hP₁.vertexSet_mono hzP₁, hzY⟩, Q₁, P₂',
    hQ₁_P, hP₂'_P, hq₁.mono hP₁, hp₂', hunion', hV_Q₁_P₂', hdisjE', rfl⟩

/-- **Step A**: If `P` is an `S_comp.Ω`-path in `S_comp` (where `S_comp.IsComposition S N`) with
ends
`s, t` and `¬ P ≤ N.G`, then `P` splits into a prefix `L_P ≤ N.G` from `s` to `u ∈ S.Ω.bar`, a
middle subpath `M_P ≤ P` from `u` to `w ∈ S.Ω.bar` (`u ≠ w`) whose first and last edges are in
`E(S.G)`, and a suffix `R_P ≤ N.G` from `t` to `w`. -/
theorem exists_middle_subpath_in_composition {S S_comp : Society α β} {N : Neighborhood α β}
    {P : Graph α β} {s t : α}
    (hcomp : S_comp.IsComposition S N)
    (hP : S_comp.IsOmegaPathWithEnds P s t) (hnot_le : ¬ P ≤ N.G) :
    ∃ u ∈ S.Ω.bar, ∃ w ∈ S.Ω.bar, u ≠ w ∧
      ∃ L_P M_P R_P : Graph α β,
        L_P ≤ P ∧ M_P ≤ P ∧ R_P ≤ P ∧
        IsGraphPathWithEnds N.G L_P s u ∧
        IsGraphPathWithEnds S_comp.G M_P u w ∧
        IsGraphPathWithEnds N.G R_P t w ∧
        V(L_P) ∩ V(M_P) = {u} ∧
        V(R_P) ∩ V(M_P) = {w} ∧
        Disjoint V(L_P) V(R_P) ∧
        (∀ c e, M_P.IsLink e u c → e ∈ E(S.G)) ∧
        (∀ c e, M_P.IsLink e w c → e ∈ E(S.G)) := by
  let Y : Set α := {v ∈ V(P) | ∃ e ∈ E(P) ∩ E(S.G), P.Inc e v}
  obtain ⟨e₀, he₀P, he₀S⟩ := nonempty_edgeSet_inter_of_not_le_right hcomp hP.1 hP.2.1 hnot_le
  obtain ⟨x₀, y₀, hx₀y₀⟩ := P.exists_isLink_of_mem_edgeSet he₀P
  have hx₀Y : x₀ ∈ V(P) ∩ Y := ⟨hx₀y₀.left_mem, hx₀y₀.left_mem, e₀, ⟨he₀P, he₀S⟩, y₀, hx₀y₀⟩
  obtain ⟨u, ⟨huP, _, e_u, ⟨he_uP, he_uS⟩, z_u, hinc_u⟩, L_P, Q_ut,
    hL_P, hQ_ut, hp_L, hp_Q, hunion₁, hinter₁, hdisjE₁, hdisjY₁⟩ :=
    hP.1.exists_first_split_at_mem ⟨x₀, hx₀Y⟩
  have hE_LP_disj : Disjoint E(L_P) E(S.G) := by
    rw [disjoint_left]
    intro e heL heS
    have heP : e ∈ E(P) := hL_P.edgeSet_mono heL
    obtain ⟨x, y, hxyL⟩ := L_P.exists_isLink_of_mem_edgeSet heL
    have hxyP : P.IsLink e x y := hxyL.mono hL_P
    have hxY : x ∈ Y := ⟨hxyP.left_mem, e, ⟨heP, heS⟩, y, hxyP⟩
    have hyY : y ∈ Y := ⟨hxyP.right_mem, e, ⟨heP, heS⟩, x, hxyP.symm⟩
    have hxu : x = u := by
      by_contra hne; exact disjoint_left.mp hdisjY₁ ⟨hxyL.left_mem, hne⟩ hxY
    have hyu : y = u := by
      by_contra hne; exact disjoint_left.mp hdisjY₁ ⟨hxyL.right_mem, hne⟩ hyY
    rw [hxu, hyu] at hxyP
    exact hP.1.not_isLoopAt heP u (hxyP.mono hP.1.le)
  have hLP_N : L_P ≤ N.G := by
    have hLP_comp : L_P ≤ S_comp.G := hL_P.trans hP.1.le
    rw [(Compatible.of_le_le hLP_comp hcomp.1.1.2.1).le_iff]
    have hEL : E(L_P) ⊆ E(N.G) := fun e heL => by
      have he_comp : e ∈ E(S_comp.G) := hLP_comp.edgeSet_mono heL
      rw [← hcomp.1.1.2.2.2.1] at he_comp
      exact he_comp.resolve_left (disjoint_left.mp hE_LP_disj heL)
    refine ⟨fun v hvL => ?_, hEL⟩
    by_cases hsu : s = u
    · subst hsu
      rcases hp_L with ⟨_, W, hW, hVL, _⟩
      cases W with
      | nil _ =>
        simp only [hVL, GraphWalk.support, List.mem_cons, List.not_mem_nil, or_false,
          mem_ofPred_eq] at hvL
        subst hvL
        exact N.bar_subset (hcomp.2.1 ▸ hP.2.2.1)
      | @cons _ w_c _ f_c _ W' =>
        exact ((List.nodup_cons.mp hW).1 W'.end_mem_support).elim
    · obtain ⟨e, heL, w_e, hvw⟩ := hp_L.exists_inc_of_mem_of_ne hsu hvL
      obtain ⟨a_e, b_e, habN⟩ := N.G.exists_isLink_of_mem_edgeSet (hEL heL)
      rcases (hvw.mono hLP_comp).left_eq_or_eq (habN.mono hcomp.1.1.2.1) with rfl | rfl
      · exact habN.left_mem
      · exact habN.right_mem
  have he_u_Q : e_u ∈ E(Q_ut) := by
    have he_u_union : e_u ∈ E(L_P) ∪ E(Q_ut) := by
      rw [← edgeSet_subgraphUnion hL_P hQ_ut, hunion₁]; exact he_uP
    exact he_u_union.resolve_left fun h => disjoint_left.mp hE_LP_disj h he_uS
  have hu_Q_Y : u ∈ V(Q_ut) ∩ Y := ⟨hp_Q.left_mem, huP, e_u, ⟨he_uP, he_uS⟩, z_u, hinc_u⟩
  obtain ⟨w, ⟨hwQ, hwP, e_w, ⟨he_wP, he_wS⟩, z_w, hinc_w⟩, R_P, M_P',
    hR_Q, hM_Q, hp_R, hp_M', hunion₂, hinter₂, hdisjE₂, hdisjY₂⟩ :=
    hp_Q.symm.exists_first_split_at_mem ⟨u, hu_Q_Y⟩
  have hR_P : R_P ≤ P := hR_Q.trans hQ_ut
  have hM_P : M_P' ≤ P := hM_Q.trans hQ_ut
  have hE_RP_disj : Disjoint E(R_P) E(S.G) := by
    rw [disjoint_left]
    intro e heR heS
    have heP : e ∈ E(P) := hR_P.edgeSet_mono heR
    obtain ⟨x, y, hxyR⟩ := R_P.exists_isLink_of_mem_edgeSet heR
    have hxyP : P.IsLink e x y := hxyR.mono hR_P
    have hxY : x ∈ Y := ⟨hxyP.left_mem, e, ⟨heP, heS⟩, y, hxyP⟩
    have hyY : y ∈ Y := ⟨hxyP.right_mem, e, ⟨heP, heS⟩, x, hxyP.symm⟩
    have hxw : x = w := by
      by_contra hne; exact disjoint_left.mp hdisjY₂ ⟨hxyR.left_mem, hne⟩ hxY
    have hyw : y = w := by
      by_contra hne; exact disjoint_left.mp hdisjY₂ ⟨hxyR.right_mem, hne⟩ hyY
    rw [hxw, hyw] at hxyP
    exact hP.1.not_isLoopAt heP w (hxyP.mono hP.1.le)
  have hRP_N : R_P ≤ N.G := by
    have hRP_comp : R_P ≤ S_comp.G := hR_P.trans hP.1.le
    rw [(Compatible.of_le_le hRP_comp hcomp.1.1.2.1).le_iff]
    have hER : E(R_P) ⊆ E(N.G) := fun e heR => by
      have he_comp : e ∈ E(S_comp.G) := hRP_comp.edgeSet_mono heR
      rw [← hcomp.1.1.2.2.2.1] at he_comp
      exact he_comp.resolve_left (disjoint_left.mp hE_RP_disj heR)
    refine ⟨fun v hvR => ?_, hER⟩
    by_cases htw : t = w
    · subst htw
      rcases hp_R with ⟨_, W, hW, hVR, _⟩
      cases W with
      | nil _ =>
        simp only [hVR, GraphWalk.support, List.mem_cons, List.not_mem_nil, or_false,
          mem_ofPred_eq] at hvR
        subst hvR
        exact N.bar_subset (hcomp.2.1 ▸ hP.2.2.2)
      | @cons _ w_c _ f_c _ W' =>
        exact ((List.nodup_cons.mp hW).1 W'.end_mem_support).elim
    · obtain ⟨e, heR, w_e, hvw⟩ := hp_R.exists_inc_of_mem_of_ne htw hvR
      obtain ⟨a_e, b_e, habN⟩ := N.G.exists_isLink_of_mem_edgeSet (hER heR)
      rcases (hvw.mono hRP_comp).left_eq_or_eq (habN.mono hcomp.1.1.2.1) with rfl | rfl
      · exact habN.left_mem
      · exact habN.right_mem
  have he_u_M : e_u ∈ E(M_P') := by
    have he_u_union : e_u ∈ E(R_P) ∪ E(M_P') := by
      rw [← edgeSet_subgraphUnion hR_Q hM_Q, hunion₂]; exact he_u_Q
    exact he_u_union.resolve_left fun h => disjoint_left.mp hE_RP_disj h he_uS
  have he_w_Q : e_w ∈ E(Q_ut) := by
    have he_w_union : e_w ∈ E(L_P) ∪ E(Q_ut) := by
      rw [← edgeSet_subgraphUnion hL_P hQ_ut, hunion₁]; exact he_wP
    exact he_w_union.resolve_left fun h => disjoint_left.mp hE_LP_disj h he_wS
  have he_w_M : e_w ∈ E(M_P') := by
    have he_w_union : e_w ∈ E(R_P) ∪ E(M_P') := by
      rw [← edgeSet_subgraphUnion hR_Q hM_Q, hunion₂]; exact he_w_Q
    exact he_w_union.resolve_left fun h => disjoint_left.mp hE_RP_disj h he_wS
  have hp_M : IsGraphPathWithEnds P M_P' u w := (hp_M'.mono hQ_ut).symm
  have huw : u ≠ w := by
    rintro rfl
    rcases hp_M with ⟨_, W, hW, _, hEM⟩
    cases W with
    | nil _ =>
      simp only [hEM, GraphWalk.edges, List.not_mem_nil, mem_ofPred_eq] at he_u_M
    | @cons _ w_c _ f_c _ W' =>
      exact (List.nodup_cons.mp hW).1 W'.end_mem_support
  have hu_VS : u ∈ V(S.G) := by
    obtain ⟨a_e, b_e, habS⟩ := S.G.exists_isLink_of_mem_edgeSet he_uS
    rcases (hinc_u.mono hP.1.le).left_eq_or_eq (habS.mono hcomp.1.1.1) with rfl | rfl
    · exact habS.left_mem
    · exact habS.right_mem
  have hw_VS : w ∈ V(S.G) := by
    obtain ⟨a_e, b_e, habS⟩ := S.G.exists_isLink_of_mem_edgeSet he_wS
    rcases (hinc_w.mono hP.1.le).left_eq_or_eq (habS.mono hcomp.1.1.1) with rfl | rfl
    · exact habS.left_mem
    · exact habS.right_mem
  have hu_bar : u ∈ S.Ω.bar := by
    rw [hcomp.2.2.2]; exact ⟨hu_VS, hLP_N.vertexSet_mono hp_L.right_mem⟩
  have hw_bar : w ∈ S.Ω.bar := by
    rw [hcomp.2.2.2]; exact ⟨hw_VS, hRP_N.vertexSet_mono hp_R.right_mem⟩
  have hinter_LM : V(L_P) ∩ V(M_P') = {u} := by
    refine Subset.antisymm ?_ (singleton_subset_iff.mpr ⟨hp_L.right_mem, hp_M.left_mem⟩)
    rw [← hinter₁]
    exact inter_subset_inter_right _ hM_Q.vertexSet_mono
  have hdisj_LR : Disjoint V(L_P) V(R_P) := by
    rw [disjoint_left]
    intro z hzL hzR
    have hzu : z = u := by
      have hz_in : z ∈ V(L_P) ∩ V(Q_ut) := ⟨hzL, hR_Q.vertexSet_mono hzR⟩
      rwa [hinter₁, mem_singleton_iff] at hz_in
    subst hzu
    have hu_in : z ∈ V(R_P) ∩ V(M_P') := ⟨hzR, hp_M.left_mem⟩
    rw [hinter₂, mem_singleton_iff] at hu_in
    exact huw hu_in
  refine ⟨u, hu_bar, w, hw_bar, huw, L_P, M_P', R_P, hL_P, hM_P, hR_P,
    (hp_L.mono hP.1.le).of_le hLP_N, hp_M.mono hP.1.le, (hp_R.mono (hQ_ut.trans hP.1.le)).of_le
      hRP_N,
    hinter_LM, hinter₂, hdisj_LR, ?_, ?_⟩
  · intro c e hlink_M
    have hinc_u_M : M_P'.Inc e_u u := ⟨z_u, (hM_P.isLink_iff he_u_M).mpr hinc_u⟩
    have he_eq : e = e_u :=
      hp_M.inc_left_unique hlink_M.edge_mem he_u_M ⟨c, hlink_M⟩ hinc_u_M
    exact he_eq ▸ he_uS
  · intro c e hlink_M
    have hinc_w_M : M_P'.Inc e_w w := ⟨z_w, (hM_P.isLink_iff he_w_M).mpr hinc_w⟩
    have he_eq : e = e_w :=
      hp_M.symm.inc_left_unique hlink_M.edge_mem he_w_M ⟨c, hlink_M⟩ hinc_w_M
    exact he_eq ▸ he_wS

/-- If `x, y ∈ Ω.bar \ W` (`x ≠ y`) have `Disjoint (Ω.interval x y) W ∨ Disjoint (Ω.interval y x)
W`,
then `x` and `y` belong to the exact same open intervals between vertices of `W`. -/
theorem mem_interval_iff_of_disjoint_interval {Ω : CyclicPerm α} {W : Set α} {x y : α}
    (hx_bar : x ∈ Ω.bar) (hy_bar : y ∈ Ω.bar) (hxy : x ≠ y)
    (hxW : x ∉ W) (hyW : y ∉ W)
    (hdisj : Disjoint (Ω.interval x y) W ∨ Disjoint (Ω.interval y x) W)
    {u v : α} (huW : u ∈ W) (hvW : v ∈ W) :
    x ∈ Ω.interval u v ↔ y ∈ Ω.interval u v := by
  have haux : ∀ {x₁ y₁ : α}, x₁ ∈ Ω.bar → y₁ ∈ Ω.bar → x₁ ≠ y₁ → x₁ ∉ W → y₁ ∉ W →
      (Disjoint (Ω.interval x₁ y₁) W ∨ Disjoint (Ω.interval y₁ x₁) W) →
      x₁ ∈ Ω.interval u v → y₁ ∈ Ω.interval u v := by
    intro x₁ y₁ hx₁_bar hy₁_bar hx₁y₁ hx₁W hy₁W hdisj₁ hx₁_uv
    by_contra hy₁_not_uv
    obtain ⟨_, h13, _, hu_bar, _, hv_bar, _⟩ := Ω.isClockwise3_iff.mp hx₁_uv.2
    have huv : u ≠ v := h13
    have hy₁u : y₁ ≠ u := fun h => hy₁W (h ▸ huW)
    have hy₁v : y₁ ≠ v := fun h => hy₁W (h ▸ hvW)
    have hy₁_vu : y₁ ∈ Ω.interval v u :=
      (Ω.mem_interval_or_interval_swap hu_bar hv_bar hy₁_bar huv hy₁u hy₁v).resolve_left hy₁_not_uv
    have hcr : Ω.Crosses x₁ y₁ u v :=
      (Ω.crosses_iff_interval.mpr (Or.inl ⟨hx₁_uv, hy₁_vu⟩)).symm
    rcases Ω.crosses_iff_interval.mp hcr with ⟨hu_xy, hv_yx⟩ | ⟨hv_xy, hu_yx⟩
    · rcases hdisj₁ with hd | hd
      · exact disjoint_left.mp hd hu_xy huW
      · exact disjoint_left.mp hd hv_yx hvW
    · rcases hdisj₁ with hd | hd
      · exact disjoint_left.mp hd hv_xy hvW
      · exact disjoint_left.mp hd hu_yx huW
  exact ⟨haux hx_bar hy_bar hxy hxW hyW hdisj,
    haux hy_bar hx_bar hxy.symm hyW hxW hdisj.symm⟩

/-- Under the hypotheses of `mem_interval_iff_of_disjoint_interval`, replacing `x` by `y` on
`W ∪ {x}` preserves and reflects `Ω.Crosses`. -/
theorem crosses_iff_of_disjoint_interval {Ω : CyclicPerm α} {W : Set α} {x y : α}
    (hx_bar : x ∈ Ω.bar) (hy_bar : y ∈ Ω.bar) (hxy : x ≠ y)
    (hxW : x ∉ W) (hyW : y ∉ W)
    (hdisj : Disjoint (Ω.interval x y) W ∨ Disjoint (Ω.interval y x) W)
    {v₁ v₃ v₂ v₄ : α}
    (hv₁ : v₁ ∈ W ∪ {x}) (hv₃ : v₃ ∈ W ∪ {x}) (hv₂ : v₂ ∈ W ∪ {x}) (hv₄ : v₄ ∈ W ∪ {x}) :
    letI := Classical.decEq α
    Ω.Crosses v₁ v₃ v₂ v₄ ↔
      Ω.Crosses (if v₁ = x then y else v₁) (if v₃ = x then y else v₃)
        (if v₂ = x then y else v₂) (if v₄ = x then y else v₄) := by
  classical
  have hsingle : ∀ {a b c : α}, a ∈ W → b ∈ W → c ∈ W →
      (Ω.Crosses a b c x ↔ Ω.Crosses a b c y) := by
    intro a b c ha hb hc
    rw [Ω.crosses_iff_interval, Ω.crosses_iff_interval,
      mem_interval_iff_of_disjoint_interval hx_bar hy_bar hxy hxW hyW hdisj ha hb,
      mem_interval_iff_of_disjoint_interval hx_bar hy_bar hxy hxW hyW hdisj hb ha]
  have hnot_eq : ∀ {a b c d : α}, Ω.Crosses a b c d →
      a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by
    intro a b c d h
    rcases h with h | h
    · obtain ⟨h12, h13, h14, h23, h24, h34, _⟩ := Ω.isClockwise4_iff.mp h
      exact ⟨h13, h12, h14, h23.symm, h34, h24⟩
    · obtain ⟨h12, h13, h14, h23, h24, h34, _⟩ := Ω.isClockwise4_iff.mp h
      exact ⟨h24.symm, h34.symm, h14.symm, h23, h12.symm, h13.symm⟩
  by_cases h1 : v₁ = x <;> by_cases h3 : v₃ = x <;> by_cases h2 : v₂ = x <;> by_cases h4 : v₄ = x
  · subst h1 h3; exact ⟨fun h => ((hnot_eq h).1 rfl).elim, fun h => ((hnot_eq h).1 rfl).elim⟩
  · subst h1 h3; exact ⟨fun h => ((hnot_eq h).1 rfl).elim, fun h => ((hnot_eq h).1 rfl).elim⟩
  · subst h1 h3; exact ⟨fun h => ((hnot_eq h).1 rfl).elim, fun h => ((hnot_eq h).1 rfl).elim⟩
  · subst h1 h3; exact ⟨fun h => ((hnot_eq h).1 rfl).elim, fun h => ((hnot_eq h).1 rfl).elim⟩
  · subst h1 h2; exact ⟨fun h => ((hnot_eq h).2.1 rfl).elim, fun h => ((hnot_eq h).2.1 rfl).elim⟩
  · subst h1 h2; exact ⟨fun h => ((hnot_eq h).2.1 rfl).elim, fun h => ((hnot_eq h).2.1 rfl).elim⟩
  · subst h1 h4; exact ⟨fun h => ((hnot_eq h).2.2.1 rfl).elim, fun h =>
    ((hnot_eq h).2.2.1 rfl).elim⟩
  · subst h1
    have hv₃W : v₃ ∈ W := hv₃.resolve_right h3
    have hv₂W : v₂ ∈ W := hv₂.resolve_right h2
    have hv₄W : v₄ ∈ W := hv₄.resolve_right h4
    rw [ite_eq_left rfl, ite_eq_right h3, ite_eq_right h2, ite_eq_right h4]
    exact ⟨fun h => ((hsingle hv₂W hv₄W hv₃W).mp h.symm.swap_right).swap_right.symm,
      fun h => ((hsingle hv₂W hv₄W hv₃W).mpr h.symm.swap_right).swap_right.symm⟩
  · subst h3 h2; exact ⟨fun h => ((hnot_eq h).2.2.2.1 rfl).elim, fun h =>
    ((hnot_eq h).2.2.2.1 rfl).elim⟩
  · subst h3 h2; exact ⟨fun h => ((hnot_eq h).2.2.2.1 rfl).elim, fun h =>
    ((hnot_eq h).2.2.2.1 rfl).elim⟩
  · subst h3 h4; exact ⟨fun h => ((hnot_eq h).2.2.2.2.1 rfl).elim, fun h =>
    ((hnot_eq h).2.2.2.2.1 rfl).elim⟩
  · subst h3
    have hv₁W : v₁ ∈ W := hv₁.resolve_right h1
    have hv₂W : v₂ ∈ W := hv₂.resolve_right h2
    have hv₄W : v₄ ∈ W := hv₄.resolve_right h4
    rw [ite_eq_right h1, ite_eq_left rfl, ite_eq_right h2, ite_eq_right h4]
    exact ⟨fun h => ((hsingle hv₂W hv₄W hv₁W).mp h.symm).symm,
      fun h => ((hsingle hv₂W hv₄W hv₁W).mpr h.symm).symm⟩
  · subst h2 h4; exact ⟨fun h => ((hnot_eq h).2.2.2.2.2 rfl).elim, fun h =>
    ((hnot_eq h).2.2.2.2.2 rfl).elim⟩
  · subst h2
    have hv₁W : v₁ ∈ W := hv₁.resolve_right h1
    have hv₃W : v₃ ∈ W := hv₃.resolve_right h3
    have hv₄W : v₄ ∈ W := hv₄.resolve_right h4
    rw [ite_eq_right h1, ite_eq_right h3, ite_eq_left rfl, ite_eq_right h4]
    exact ⟨fun h => ((hsingle hv₁W hv₃W hv₄W).mp h.swap_right).swap_right,
      fun h => ((hsingle hv₁W hv₃W hv₄W).mpr h.swap_right).swap_right⟩
  · subst h4
    have hv₁W : v₁ ∈ W := hv₁.resolve_right h1
    have hv₃W : v₃ ∈ W := hv₃.resolve_right h3
    have hv₂W : v₂ ∈ W := hv₂.resolve_right h2
    rw [ite_eq_right h1, ite_eq_right h3, ite_eq_right h2, ite_eq_left rfl]
    exact hsingle hv₁W hv₃W hv₂W
  · rw [ite_eq_right h1, ite_eq_right h3, ite_eq_right h2, ite_eq_right h4]

private theorem cardinalityAfterReplacingPath
    {S : Society α β} {P_set : Set (Graph α β)} {P P_left Q P_right : Graph α β}
    (hP_in : P ∈ P_set) (hP_left : P_left ≤ P) (hQ : Q ≤ P) (hP_right : P_right ≤ P) {A B : Set α}
    (hfence : S.IsFenceFor P_set A B) (hR_le : ∀ R ∈ P_set, R ≤ S.G) (hP_le : P ≤ S.G)
    (hPL_le : P_left ≤ S.G) (hPR_le : P_right ≤ S.G) (hPL_not_diff : P_left ∉ P_set \ {P})
    (hPR_not_diff : P_right ∉ P_set \ {P}) (hPL_ne_PR : P_left ≠ P_right) (hfin_P : P_set.Finite)
    (hfin_diff : (P_set \ {P}).Finite) {e_Q : β} (he_Q : e_Q ∈ E(Q))
    (hdisj_EQ_L : Disjoint E(Q) E(P_left)) (hdisj_EQ_R : Disjoint E(Q) E(P_right))
    {P_set' : Set (Graph α β)}
    (hor : P_set' = P_set \ {P} ∪ {P_left} ∨ P_set' = P_set \ {P} ∪ {P_right} ∨ P_set' = P_set \
      {P} ∪ {P_left, P_right}) :
    P_set.ncard ≤ P_set'.ncard ∧ E(S.transactionUnion P_set').ncard < E(S.transactionUnion
      P_set).ncard := by
  classical
  have hcard_le : P_set.ncard ≤ P_set'.ncard := by
    rcases hor with rfl | rfl | rfl
    · rw [union_comm, ← insert_eq, ncard_insert_of_notMem hPL_not_diff hfin_diff,
        ncard_sdiff_singleton_add_one hP_in hfin_P]
    · rw [union_comm, ← insert_eq, ncard_insert_of_notMem hPR_not_diff hfin_diff,
        ncard_sdiff_singleton_add_one hP_in hfin_P]
    · have hset_eq : (P_set \ {P}) ∪ {P_left, P_right} =
          insert P_left (insert P_right (P_set \ {P})) := by
        ext R; aesop
      rw [hset_eq,
        ncard_insert_of_notMem (by simp [hPL_ne_PR, hPL_not_diff]) (hfin_diff.insert P_right),
        ncard_insert_of_notMem hPR_not_diff hfin_diff,
        ncard_sdiff_singleton_add_one hP_in hfin_P]
      omega
  have hR'_le : ∀ R ∈ P_set', R ≤ S.G := by
    intro R hR
    rcases hor with rfl | rfl | rfl
    · rcases hR with hR | rfl; exacts [hR_le R hR.1, hPL_le]
    · rcases hR with hR | rfl; exacts [hR_le R hR.1, hPR_le]
    · rcases hR with hR | rfl | rfl; exacts [hR_le R hR.1, hPL_le, hPR_le]
  have hsub_each : ∀ R ∈ P_set', E(R) ⊆ E(S.transactionUnion P_set) ∧ e_Q ∉ E(R) := by
    intro R hR
    have hcases : R ∈ P_set \ {P} ∨ R = P_left ∨ R = P_right := by
      rcases hor with rfl | rfl | rfl
      · rcases hR with h | rfl; exacts [Or.inl h, Or.inr (Or.inl rfl)]
      · rcases hR with h | rfl; exacts [Or.inl h, Or.inr (Or.inr rfl)]
      · exact hR
    rcases hcases with hR_diff | rfl | rfl
    · refine ⟨fun e he => ?_, fun he_QR => ?_⟩
      · rw [Society.transactionUnion, edgeSet_subgraphSUnion hR_le, mem_iUnion₂]
        exact ⟨R, hR_diff.1, he⟩
      · obtain ⟨u₁, v₁, huvQ⟩ := Q.exists_isLink_of_mem_edgeSet he_Q
        obtain ⟨u₂, v₂, huvR⟩ := R.exists_isLink_of_mem_edgeSet he_QR
        have hne_PR : P ≠ R := fun h => hR_diff.2 h.symm
        rcases (huvQ.mono (hQ.trans hP_le)).left_eq_or_eq (huvR.mono (hR_le R hR_diff.1))
          with rfl | rfl
        · exact disjoint_left.mp (hfence.1.2 hP_in hR_diff.1 hne_PR)
            (hQ.vertexSet_mono huvQ.left_mem) huvR.left_mem
        · exact disjoint_left.mp (hfence.1.2 hP_in hR_diff.1 hne_PR)
            (hQ.vertexSet_mono huvQ.left_mem) huvR.right_mem
    · refine ⟨fun e he => ?_, disjoint_left.mp hdisj_EQ_L he_Q⟩
      rw [Society.transactionUnion, edgeSet_subgraphSUnion hR_le, mem_iUnion₂]
      exact ⟨P, hP_in, hP_left.edgeSet_mono he⟩
    · refine ⟨fun e he => ?_, disjoint_left.mp hdisj_EQ_R he_Q⟩
      rw [Society.transactionUnion, edgeSet_subgraphSUnion hR_le, mem_iUnion₂]
      exact ⟨P, hP_in, hP_right.edgeSet_mono he⟩
  have hE_sub : E(S.transactionUnion P_set') ⊆ E(S.transactionUnion P_set) := by
    rw [Society.transactionUnion, edgeSet_subgraphSUnion hR'_le]
    intro e he; rw [mem_iUnion₂] at he
    rcases he with ⟨R, hR, heR⟩
    exact (hsub_each R hR).1 heR
  have heQ_in_U : e_Q ∈ E(S.transactionUnion P_set) := by
    rw [Society.transactionUnion, edgeSet_subgraphSUnion hR_le, mem_iUnion₂]
    exact ⟨P, hP_in, hQ.edgeSet_mono he_Q⟩
  have heQ_not_U' : e_Q ∉ E(S.transactionUnion P_set') := by
    rw [Society.transactionUnion, edgeSet_subgraphSUnion hR'_le, mem_iUnion₂]
    rintro ⟨R, hR, heR⟩
    exact (hsub_each R hR).2 heR
  have hEU_fin : E(S.transactionUnion P_set).Finite :=
    S.finite_E.subset (subgraphSUnion_le hR_le).edgeSet_mono
  exact ⟨hcard_le,
    ncard_lt_ncard ⟨hE_sub, fun hall => heQ_not_U' (hall heQ_in_U)⟩ hEU_fin⟩

private theorem crookedAfterTwoSwitches
    {S : Society α β} {P_set : Set (Graph α β)} {A B : Set α} {P₁ L₁ L₂ : Graph α β}
    (hdisj_LR : ∀ R ∈ P_set \ {P₁}, Disjoint V(L₁) V(R) ∧ Disjoint V(L₂) V(R))
    (hfence : S.IsFenceFor P_set A B)
    (hW'_bar : (S.transactionEnds (P_set \ {P₁})) ⊆ S.Ω.bar) {a_0 : α}
    (ha_0 : a_0 ∈ A ∩ (S.transactionEnds (P_set \ {P₁}))) {a'_0 : α}
    (ha'_0 : a'_0 ∈ A ∩ (S.transactionEnds (P_set \ {P₁}))) {b_0 : α}
    (hb_0 : b_0 ∈ B ∩ (S.transactionEnds (P_set \ {P₁}))) {b'_0 : α}
    (hb'_0 : b'_0 ∈ B ∩ (S.transactionEnds (P_set \ {P₁})))
    (hd_ab : Disjoint (S.Ω.interval a'_0 b_0) (S.transactionEnds (P_set \ {P₁})))
    (hd_ba : Disjoint (S.Ω.interval b'_0 a_0) (S.transactionEnds (P_set \ {P₁}))) {e₁ e₂ : α}
    (he₁_G₁ : e₁ ∈ S.Ω.interval a'_0 b_0) (he₂_G₂ : e₂ ∈ S.Ω.interval b'_0 a_0)
    {u₁ u₂ : α} (hdisj_L12 : Disjoint V(L₁) V(L₂)) (hL₁_ends : S.IsOmegaPathWithEnds L₁ u₁ e₁)
    (hL₂_ends : S.IsOmegaPathWithEnds L₂ u₂ e₂) (hu₁_bar : u₁ ∈ S.Ω.bar)
    (hu₁_not_W' : u₁ ∉ (S.transactionEnds (P_set \ {P₁}))) (hu₁_G₁ : u₁ ∉ S.Ω.interval a'_0 b_0)
    (hu₁_G₂ : u₁ ∉ S.Ω.interval b'_0 a_0) (hu₂_bar : u₂ ∈ S.Ω.bar)
    (hu₂_not_W' : u₂ ∉ (S.transactionEnds (P_set \ {P₁}))) (hu₂_G₁ : u₂ ∉ S.Ω.interval a'_0 b_0)
    (hu₂_G₂ : u₂ ∉ S.Ω.interval b'_0 a_0) :
    S.IsCrookedTransaction (P_set \ {P₁} ∪ {L₁, L₂}) := by
  classical
  let W' := S.transactionEnds (P_set \ {P₁})
  let P_set'' := (P_set \ {P₁}) ∪ {L₁, L₂}
  obtain ⟨A_f, B_f, hff, hAf, hBf, h_u₁e₁, h_u₂e₂⟩ :=
    Society.exists_fence_for_two_switches hfence.2.1 hW'_bar ha_0 ha'_0 hb_0 hb'_0 hd_ab hd_ba
      he₁_G₁ he₂_G₂ hu₁_bar hu₁_not_W' hu₁_G₁ hu₁_G₂ hu₂_bar hu₂_not_W' hu₂_G₁ hu₂_G₂
  have hdisj'' : S.IsDisjointOmegaPathSet P_set'' := by
    refine ⟨?_, ?_⟩
    · rintro R (hR | rfl | rfl)
      · exact hfence.1.1 R hR.1
      · exact ⟨u₁, e₁, hL₁_ends⟩
      · exact ⟨u₂, e₂, hL₂_ends⟩
    · rintro M₁ (hM₁ | rfl | rfl) M₂ (hM₂ | rfl | rfl) hne
      · exact hfence.1.2 hM₁.1 hM₂.1 hne
      · exact (hdisj_LR M₁ hM₁).1.symm
      · exact (hdisj_LR M₁ hM₁).2.symm
      · exact (hdisj_LR M₂ hM₂).1
      · exact (hne rfl).elim
      · exact hdisj_L12
      · exact (hdisj_LR M₂ hM₂).2
      · exact hdisj_L12.symm
      · exact (hne rfl).elim
  have hfence'' : S.IsFenceFor P_set'' A_f B_f := by
    refine ⟨hdisj'', hff, ?_⟩
    rintro R (hR | rfl | rfl)
    · obtain ⟨a_R, ha_R, b_R, hb_R, hR_ends⟩ := hfence.2.2 R hR.1
      have ha_R_W' : a_R ∈ A ∩ W' := ⟨ha_R, hR_ends.mem_transactionEnds_left S hR⟩
      have hb_R_W' : b_R ∈ B ∩ W' := ⟨hb_R, hR_ends.mem_transactionEnds_right S hR⟩
      exact ⟨a_R, hAf ha_R_W', b_R, hBf hb_R_W', hR_ends⟩
    · rcases h_u₁e₁ with ⟨hu₁A, he₁B⟩ | ⟨he₁A, hu₁B⟩
      · exact ⟨u₁, hu₁A, e₁, he₁B, hL₁_ends⟩
      · exact ⟨e₁, he₁A, u₁, hu₁B, hL₁_ends.symm S⟩
    · rcases h_u₂e₂ with ⟨hu₂A, he₂B⟩ | ⟨he₂A, hu₂B⟩
      · exact ⟨u₂, hu₂A, e₂, he₂B, hL₂_ends⟩
      · exact ⟨e₂, he₂A, u₂, hu₂B, hL₂_ends.symm S⟩
  have hW'_sub_ends : W' ⊆ S.transactionEnds P_set'' :=
    fun z ⟨R, hR, y_e, hR_e⟩ => ⟨R, Or.inl hR, y_e, hR_e⟩
  have he₁_mem_ends : e₁ ∈ S.transactionEnds P_set'' :=
    hL₁_ends.mem_transactionEnds_right S (Or.inr (Or.inl rfl))
  have he₂_mem_ends : e₂ ∈ S.transactionEnds P_set'' :=
    hL₂_ends.mem_transactionEnds_right S (Or.inr (Or.inr rfl))
  refine ⟨⟨A_f, B_f, hfence''⟩, ?_⟩
  rintro R (hR | rfl | rfl) hper
  · obtain ⟨a_R, ha_R, b_R, hb_R, hR_ends⟩ := hfence.2.2 R hR.1
    have ha_R_W' : a_R ∈ A ∩ W' := ⟨ha_R, hR_ends.mem_transactionEnds_left S hR⟩
    have hb_R_W' : b_R ∈ B ∩ W' := ⟨hb_R, hR_ends.mem_transactionEnds_right S hR⟩
    have hper' := (hR_ends.isPeripheralIn_iff S (Or.inl hR)).mp hper
    rcases hper' with hd₁ | hd₂
    · have hsub₁ := S.Ω.interval_subset_of_disjoint_AB hfence.2.1 hW'_bar
        ha'_0 hb_0 hd_ab ha_R_W' hb_R_W'
      exact disjoint_left.mp hd₁ (hsub₁ he₁_G₁) he₁_mem_ends
    · have hsub₂ := S.Ω.interval_subset_of_disjoint_AB hfence.2.1.symm hW'_bar
        hb'_0 ha_0 hd_ba hb_R_W' ha_R_W'
      exact disjoint_left.mp hd₂ (hsub₂ he₂_G₂) he₂_mem_ends
  · have hper' := (hL₁_ends.isPeripheralIn_iff S (Or.inr (Or.inl rfl))).mp hper
    have ha'_ne_b : a'_0 ≠ b_0 := fun h =>
      disjoint_left.mp hfence.2.1.2.2.1 ha'_0.1 (h ▸ hb_0.1)
    have hu₁_ne_a' : u₁ ≠ a'_0 := fun h => hu₁_not_W' (h ▸ ha'_0.2)
    have hu₁_ne_b : u₁ ≠ b_0 := fun h => hu₁_not_W' (h ▸ hb_0.2)
    have h_in := Society.mem_interval_of_mem_gap_and_not_mem
      (hW'_bar ha'_0.2) (hW'_bar hb_0.2) ha'_ne_b he₁_G₁ hu₁_bar hu₁_ne_a' hu₁_ne_b hu₁_G₁
    rcases hper' with hd₁ | hd₂
    · exact disjoint_left.mp hd₁ h_in.2 (hW'_sub_ends ha'_0.2)
    · exact disjoint_left.mp hd₂ h_in.1 (hW'_sub_ends hb_0.2)
  · have hper' := (hL₂_ends.isPeripheralIn_iff S (Or.inr (Or.inr rfl))).mp hper
    have hb'_ne_a : b'_0 ≠ a_0 := fun h =>
      disjoint_left.mp hfence.2.1.2.2.1 ha_0.1 (h ▸ hb'_0.1)
    have hu₂_ne_b' : u₂ ≠ b'_0 := fun h => hu₂_not_W' (h ▸ hb'_0.2)
    have hu₂_ne_a : u₂ ≠ a_0 := fun h => hu₂_not_W' (h ▸ ha_0.2)
    have h_in := Society.mem_interval_of_mem_gap_and_not_mem
      (hW'_bar hb'_0.2) (hW'_bar ha_0.2) hb'_ne_a he₂_G₂ hu₂_bar hu₂_ne_b' hu₂_ne_a hu₂_G₂
    rcases hper' with hd₁ | hd₂
    · exact disjoint_left.mp hd₁ h_in.2 (hW'_sub_ends hb'_0.2)
    · exact disjoint_left.mp hd₂ h_in.1 (hW'_sub_ends ha_0.2)

private theorem replaceByOneEndPath
    {S : Society α β} {P_set : Set (Graph α β)} {P P_left P_right : Graph α β} {s t x y : α}
    (hP_in : P ∈ P_set) (hP_ends : S.IsOmegaPathWithEnds P s t)
    (hx : x ∈ pathInternalVerts S.G P ∩ S.Ω.bar) (hy : y ∈ pathInternalVerts S.G P ∩ S.Ω.bar)
    (hxy : x ≠ y) (hP_left : P_left ≤ P) (hP_right : P_right ≤ P)
    (hdisj_int : Disjoint (S.Ω.interval x y) (S.transactionEnds P_set) ∨ Disjoint (S.Ω.interval y
      x) (S.transactionEnds P_set))
    {A B : Set α} (hfence : S.IsFenceFor P_set A B) (hx_ne_t : x ≠ t)
    (hP_left_ends : S.IsOmegaPathWithEnds P_left s x)
    (hP_right_ends : S.IsOmegaPathWithEnds P_right y t) (hx_not_W : x ∉ (S.transactionEnds P_set))
    (hy_not_W : y ∉ (S.transactionEnds P_set))
    (hcard_and_lt : ∀ {P_set' : Set (Graph α β)}, P_set' = P_set \ {P} ∪ {P_left} ∨ P_set' = P_set
      \ {P} ∪ {P_right} ∨ P_set' = P_set \ {P} ∪ {P_left, P_right} → P_set.ncard ≤
      P_set'.ncard ∧ E(S.transactionUnion P_set').ncard < E(S.transactionUnion P_set).ncard)
    (hexch : S.IsExchangeableAttachment P_set (section9SingleVertex S.G x)) :
    ∃ P_set', (P_set' = P_set \ {P} ∪ {P_left} ∨ P_set' = P_set \ {P} ∪ {P_right} ∨ P_set' = P_set
      \ {P} ∪ {P_left, P_right}) ∧ S.IsCrookedTransaction P_set' ∧ P_set.ncard ≤ P_set'.ncard ∧
      E(S.transactionUnion P_set').ncard < E(S.transactionUnion P_set).ncard := by
  classical
  let W := S.transactionEnds P_set
  let Q_x := section9SingleVertex S.G x
  rcases hexch with ⟨_, L, L', ⟨hL_in, b, u, a₁, b₁, hatt_bu, hbL, hL_ends, Q_sub, hQ_or, rfl⟩,
    hcr'⟩
  have hbx : b = x := by
    have hbQ : b ∈ V(Q_x) := hatt_bu.1.left_mem
    rwa [vertexSet_section9SingleVertex, mem_singleton_iff] at hbQ
  have hux : u = x := by
    have huQ : u ∈ V(Q_x) := hatt_bu.1.right_mem
    rwa [vertexSet_section9SingleVertex, mem_singleton_iff] at huQ
  rcases hbx.symm with rfl; rcases hux.symm with rfl
  have hLP : L = P := by
    by_contra hne; exact disjoint_left.mp (hfence.1.2 hL_in hP_in hne) hbL hx.1.1
  subst hLP
  let L' := subgraphUnion S.G Q_x Q_sub
  let P_set_L := (P_set \ {L}) ∪ {L'}
  have hL'_not_diff : L' ∉ P_set \ {L} :=
    Society.IsAttachmentWithEnds.subgraphUnion_not_mem_sdiff S hfence.1 hatt_bu hL_in hbL
  have hne_L' : ∀ {R : Graph α β}, R ∈ P_set \ {L} → R ≠ L' :=
    fun hR h => hL'_not_diff (h ▸ hR)
  have hex_end : ∃ e_end : α, (e_end = s ∨ e_end = t) ∧ S.IsOmegaPathWithEnds L' x e_end := by
    have hpair := hL_ends.1.pair_ends_eq hP_ends.1
    rcases hQ_or with hQ_xa₁ | hQ_xb₁
    · have ha₁_in : a₁ ∈ ({s, t} : Set α) := by rw [← hpair]; simp
      exact ⟨a₁, by simpa using ha₁_in,
        hatt_bu.isOmegaPathWithEnds_subgraphUnion S hL_in hbL hL_ends hQ_xa₁ (Or.inl rfl)⟩
    · have hb₁_in : b₁ ∈ ({s, t} : Set α) := by rw [← hpair]; simp
      exact ⟨b₁, by simpa using hb₁_in,
        hatt_bu.isOmegaPathWithEnds_subgraphUnion S hL_in hbL hL_ends hQ_xb₁ (Or.inr rfl)⟩
  obtain ⟨e_end, he_end_or, hL'_ends⟩ := hex_end
  rcases he_end_or with rfl | rfl
  · -- Replace `L'` (ends `x, s`) with `P_left` (ends `s, x`) via `f_v = id`.
    let f_P : Graph α β → Graph α β := fun R => if R = L' then P_left else R
    have hfP_diff : ∀ {R : Graph α β}, R ∈ P_set \ {L} → f_P R = R :=
      fun hR => ite_eq_right (hne_L' hR)
    have hfP_L' : f_P L' = P_left := ite_eq_left rfl
    have hcr_PL : S.IsCrookedTransaction (f_P '' P_set_L) := by
      refine (isCrookedTransaction_of_end_map hcr' (f_P := f_P) (f_v := id) ?_ ?_
        (injOn_id _) (fun _ _ _ _ _ _ _ _ => Iff.rfl)).1
      · rintro R (hR | rfl) a b hR_ab
        · rw [hfP_diff hR]; exact hR_ab
        · rw [hfP_L']
          rcases hL'_ends.ends_eq S hR_ab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact hP_left_ends.symm S
          · exact hP_left_ends
      · rintro R₁ (hR₁ | rfl) R₂ (hR₂ | rfl) hne
        · rw [hfP_diff hR₁, hfP_diff hR₂]
          exact hfence.1.2 hR₁.1 hR₂.1 hne
        · rw [hfP_diff hR₁, hfP_L']
          exact (hfence.1.2 hR₁.1 hL_in hR₁.2).mono_right hP_left.vertexSet_mono
        · rw [hfP_L', hfP_diff hR₂]
          exact (hfence.1.2 hL_in hR₂.1 (Ne.symm hR₂.2)).mono_left hP_left.vertexSet_mono
        · exact (hne rfl).elim
    have himg_eq : f_P '' P_set_L = (P_set \ {L}) ∪ {P_left} := by
      ext R; simp only [P_set_L, image_union, image_singleton, hfP_L', mem_union,
        mem_image, mem_singleton_iff]
      refine ⟨?_, ?_⟩
      · rintro (⟨R₀, hR₀, rfl⟩ | rfl)
        · rw [hfP_diff hR₀]; exact Or.inl hR₀
        · exact Or.inr rfl
      · rintro (hR | rfl)
        · exact Or.inl ⟨R, hR, hfP_diff hR⟩
        · exact Or.inr rfl
    rw [himg_eq] at hcr_PL
    obtain ⟨hcard, hlt⟩ := hcard_and_lt (Or.inl rfl)
    exact ⟨(P_set \ {L}) ∪ {P_left}, Or.inl rfl, hcr_PL, hcard, hlt⟩
  · -- Replace `L'` (ends `x, t`) with `P_right` (ends `y, t`) via `f_v z := if z = x then y else
    -- z`.
    let f_P : Graph α β → Graph α β := fun R => if R = L' then P_right else R
    let f_v : α → α := fun z => if z = x then y else z
    have hfP_diff : ∀ {R : Graph α β}, R ∈ P_set \ {L} → f_P R = R :=
      fun hR => ite_eq_right (hne_L' hR)
    have hfP_L' : f_P L' = P_right := ite_eq_left rfl
    have hWL_sub : S.transactionEnds P_set_L ⊆ W ∪ {x} := by
      rintro z ⟨R, hR | rfl, d, hR_zd⟩
      · exact Or.inl ⟨R, hR.1, d, hR_zd⟩
      · rcases hL'_ends.ends_eq S hR_zd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inr rfl
        · exact Or.inl ⟨L, hL_in, s, hP_ends.symm S⟩
    have hcr_PR : S.IsCrookedTransaction (f_P '' P_set_L) := by
      refine (isCrookedTransaction_of_end_map hcr' (f_P := f_P) (f_v := f_v) ?_ ?_ ?_ ?_).1
      · rintro R (hR | rfl) a b hR_ab
        · have haW : a ∈ W := ⟨R, hR.1, b, hR_ab⟩
          have hbW : b ∈ W := ⟨R, hR.1, a, hR_ab.symm S⟩
          have hax : a ≠ x := fun h => hx_not_W (h ▸ haW)
          have hbx : b ≠ x := fun h => hx_not_W (h ▸ hbW)
          rw [hfP_diff hR]
          change S.IsOmegaPathWithEnds R (if a = x then y else a) (if b = x then y else b)
          rw [ite_eq_right hax, ite_eq_right hbx]
          exact hR_ab
        · rw [hfP_L']
          change S.IsOmegaPathWithEnds P_right (if a = x then y else a) (if b = x then y else b)
          rcases hL'_ends.ends_eq S hR_ab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · rw [ite_eq_left rfl, ite_eq_right hx_ne_t.symm]
            exact hP_right_ends
          · rw [ite_eq_right hx_ne_t.symm, ite_eq_left rfl]
            exact hP_right_ends.symm S
      · rintro R₁ (hR₁ | rfl) R₂ (hR₂ | rfl) hne
        · rw [hfP_diff hR₁, hfP_diff hR₂]
          exact hfence.1.2 hR₁.1 hR₂.1 hne
        · rw [hfP_diff hR₁, hfP_L']
          exact (hfence.1.2 hR₁.1 hL_in hR₁.2).mono_right hP_right.vertexSet_mono
        · rw [hfP_L', hfP_diff hR₂]
          exact (hfence.1.2 hL_in hR₂.1 (Ne.symm hR₂.2)).mono_left hP_right.vertexSet_mono
        · exact (hne rfl).elim
      · intro z₁ hz₁ z₂ hz₂ heq
        rcases hWL_sub hz₁ with hz₁W | hz₁_eq <;> rcases hWL_sub hz₂ with hz₂W | hz₂_eq
        · have h1 : z₁ ≠ x := fun h => hx_not_W (h ▸ hz₁W)
          have h2 : z₂ ≠ x := fun h => hx_not_W (h ▸ hz₂W)
          change (if z₁ = x then y else z₁) = (if z₂ = x then y else z₂) at heq
          rw [ite_eq_right h1, ite_eq_right h2] at heq
          exact heq
        · rw [mem_singleton_iff] at hz₂_eq
          have h1 : z₁ ≠ x := fun h => hx_not_W (h ▸ hz₁W)
          change (if z₁ = x then y else z₁) = (if z₂ = x then y else z₂) at heq
          rw [ite_eq_right h1, ite_eq_left hz₂_eq] at heq
          exact (hy_not_W (heq ▸ hz₁W)).elim
        · rw [mem_singleton_iff] at hz₁_eq
          have h2 : z₂ ≠ x := fun h => hx_not_W (h ▸ hz₂W)
          change (if z₁ = x then y else z₁) = (if z₂ = x then y else z₂) at heq
          rw [ite_eq_left hz₁_eq, ite_eq_right h2] at heq
          exact (hy_not_W (heq.symm ▸ hz₂W)).elim
        · rw [mem_singleton_iff] at hz₁_eq hz₂_eq
          exact hz₁_eq.trans hz₂_eq.symm
      · intro v₁ hv₁ v₃ hv₃ v₂ hv₂ v₄ hv₄
        exact crosses_iff_of_disjoint_interval hx.2 hy.2 hxy hx_not_W hy_not_W hdisj_int
          (hWL_sub hv₁) (hWL_sub hv₃) (hWL_sub hv₂) (hWL_sub hv₄)
    have himg_eq : f_P '' P_set_L = (P_set \ {L}) ∪ {P_right} := by
      ext R; simp only [P_set_L, image_union, image_singleton, hfP_L', mem_union,
        mem_image, mem_singleton_iff]
      refine ⟨?_, ?_⟩
      · rintro (⟨R₀, hR₀, rfl⟩ | rfl)
        · rw [hfP_diff hR₀]; exact Or.inl hR₀
        · exact Or.inr rfl
      · rintro (hR | rfl)
        · exact Or.inl ⟨R, hR, hfP_diff hR⟩
        · exact Or.inr rfl
    rw [himg_eq] at hcr_PR
    obtain ⟨hcard, hlt⟩ := hcard_and_lt (Or.inr (Or.inl rfl))
    exact ⟨(P_set \ {L}) ∪ {P_right}, Or.inr (Or.inl rfl), hcr_PR, hcard, hlt⟩

private theorem replaceByBothEndPaths
    {S : Society α β} {P_set : Set (Graph α β)} {P P_left P_right : Graph α β} {s t x y : α}
    (hcrooked : S.IsCrookedTransaction P_set) (hP_in : P ∈ P_set)
    (hP_ends : S.IsOmegaPathWithEnds P s t) (hx : x ∈ pathInternalVerts S.G P ∩ S.Ω.bar)
    (hy : y ∈ pathInternalVerts S.G P ∩ S.Ω.bar) (hxy : x ≠ y) (hP_left : P_left ≤ P)
    (hP_right : P_right ≤ P) (hdisj_LR : Disjoint V(P_left) V(P_right))
    (hdisj_int : Disjoint (S.Ω.interval x y) (S.transactionEnds P_set) ∨ Disjoint (S.Ω.interval y
      x) (S.transactionEnds P_set))
    {A B : Set α} (hfence : S.IsFenceFor P_set A B)
    (hP_left_ends : S.IsOmegaPathWithEnds P_left s x)
    (hP_right_ends : S.IsOmegaPathWithEnds P_right y t) (hx_not_W : x ∉ (S.transactionEnds P_set))
    (hy_not_W : y ∉ (S.transactionEnds P_set))
    (hcard_and_lt : ∀ {P_set' : Set (Graph α β)}, P_set' = P_set \ {P} ∪ {P_left} ∨ P_set' = P_set
      \ {P} ∪ {P_right} ∨ P_set' = P_set \ {P} ∪ {P_left, P_right} → P_set.ncard ≤
      P_set'.ncard ∧ E(S.transactionUnion P_set').ncard < E(S.transactionUnion P_set).ncard)
    (hatt_x : S.IsAttachmentWithEnds P_set (section9SingleVertex S.G x) x x)
    (hexch : ¬S.IsExchangeableAttachment P_set (section9SingleVertex S.G x)) :
    ∃ P_set', (P_set' = P_set \ {P} ∪ {P_left} ∨ P_set' = P_set \ {P} ∪ {P_right} ∨ P_set' = P_set
      \ {P} ∪ {P_left, P_right}) ∧ S.IsCrookedTransaction P_set' ∧ P_set.ncard ≤ P_set'.ncard ∧
      E(S.transactionUnion P_set').ncard < E(S.transactionUnion P_set).ncard := by
  classical
  let W := S.transactionEnds P_set
  let Q_x := section9SingleVertex S.G x
  obtain ⟨_, P₁, hleg, hover⟩ := S.theorem_3_2_proof hcrooked ⟨x, x, hatt_x⟩ hexch
  have hP₁_eq : P₁ = P := by
    rcases hleg with ⟨hP₁_in, b, ⟨u, hatt_bu⟩, hbP₁⟩
    have hbx : b = x := by
      have hbQ : b ∈ V(Q_x) := hatt_bu.1.left_mem
      rwa [vertexSet_section9SingleVertex, mem_singleton_iff] at hbQ
    subst hbx; by_contra hne; exact disjoint_left.mp (hfence.1.2 hP₁_in hP_in hne) hbP₁ hx.1.1
  subst hP₁_eq
  obtain ⟨a₁_raw, ha₁_raw, b₁_raw, hb₁_raw, hP_ends_raw⟩ := hfence.2.2 P₁ hP_in
  rcases hover with ⟨_, _, R₁, hR₁_in, R₂, hR₂_in, hR12, hper₁, hper₂⟩
  obtain ⟨x₁, hx₁, y₁, hy₁, hR₁_ends⟩ := hfence.2.2 R₁ hR₁_in.1
  obtain ⟨x₂, hx₂, y₂, hy₂, hR₂_ends⟩ := hfence.2.2 R₂ hR₂_in.1
  let W' := S.transactionEnds (P_set \ {P₁})
  have hW'_sub_W : W' ⊆ W := fun z ⟨R, hR, d, hR_zd⟩ => ⟨R, hR.1, d, hR_zd⟩
  have hW'_bar : W' ⊆ S.Ω.bar := S.transactionEnds_subset_bar (P_set \ {P₁})
  have hx₁W' : x₁ ∈ A ∩ W' := ⟨hx₁, hR₁_ends.mem_transactionEnds_left S hR₁_in⟩
  have hy₁W' : y₁ ∈ B ∩ W' := ⟨hy₁, hR₁_ends.mem_transactionEnds_right S hR₁_in⟩
  have hx₂W' : x₂ ∈ A ∩ W' := ⟨hx₂, hR₂_ends.mem_transactionEnds_left S hR₂_in⟩
  have hy₂W' : y₂ ∈ B ∩ W' := ⟨hy₂, hR₂_ends.mem_transactionEnds_right S hR₂_in⟩
  have hper₁' := (hR₁_ends.isPeripheralIn_iff S hR₁_in).mp hper₁
  have hper₂' := (hR₂_ends.isPeripheralIn_iff S hR₂_in).mp hper₂
  have hdisj_R12 : Disjoint V(R₁) V(R₂) := hfence.1.2 hR₁_in.1 hR₂_in.1 hR12
  have hx12 : x₁ ≠ x₂ :=
    fun h => disjoint_left.mp hdisj_R12 hR₁_ends.1.left_mem (h ▸ hR₂_ends.1.left_mem)
  have hy12 : y₁ ≠ y₂ :=
    fun h => disjoint_left.mp hdisj_R12 hR₁_ends.1.right_mem (h ▸ hR₂_ends.1.right_mem)
  have hex_boundary :
      ∃ a_0 ∈ A ∩ W', ∃ a'_0 ∈ A ∩ W', ∃ b_0 ∈ B ∩ W', ∃ b'_0 ∈ B ∩ W',
        Disjoint (S.Ω.interval a'_0 b_0) W' ∧
        Disjoint (S.Ω.interval b'_0 a_0) W' ∧
        (∃ R_ab ∈ P_set \ {P₁}, S.IsOmegaPathWithEnds R_ab a'_0 b_0) ∧
        (∃ R_ba ∈ P_set \ {P₁}, S.IsOmegaPathWithEnds R_ba a_0 b'_0) := by
    rcases hper₁' with hd₁ | hd₁ <;> rcases hper₂' with hd₂ | hd₂
    · exact (hx12 (S.Ω.unique_empty_interval_AB_of_isFence hfence.2.1 hW'_bar
        hx₁W' hy₁W' hx₂W' hy₂W' hd₁ hd₂).1).elim
    · exact ⟨x₂, hx₂W', x₁, hx₁W', y₁, hy₁W', y₂, hy₂W', hd₁, hd₂,
        ⟨R₁, hR₁_in, hR₁_ends⟩, ⟨R₂, hR₂_in, hR₂_ends⟩⟩
    · exact ⟨x₁, hx₁W', x₂, hx₂W', y₂, hy₂W', y₁, hy₁W', hd₂, hd₁,
        ⟨R₂, hR₂_in, hR₂_ends⟩, ⟨R₁, hR₁_in, hR₁_ends⟩⟩
    · exact (hy12 (S.Ω.unique_empty_interval_AB_of_isFence hfence.2.1.symm hW'_bar
        hy₁W' hx₁W' hy₂W' hx₂W' hd₁ hd₂).1).elim
  obtain ⟨a_0, ha_0, a'_0, ha'_0, b_0, hb_0, b'_0, hb'_0, hd_ab, hd_ba,
    ⟨R_ab, hR_ab_in, hR_ab_ends⟩, ⟨R_ba, hR_ba_in, hR_ba_ends⟩⟩ := hex_boundary
  have h_e_G₁ := S.mem_interval_of_peripheral_diff_singleton hfence hcrooked hP_in hR_ab_in
    ha₁_raw hb₁_raw hP_ends_raw ha'_0.1 hb_0.1 hR_ab_ends hd_ab
  have hfence_BA : S.IsFenceFor P_set B A :=
    ⟨hfence.1, hfence.2.1.symm, fun R hR => by
      obtain ⟨a_e, ha_e, b_e, hb_e, hR_e⟩ := hfence.2.2 R hR
      exact ⟨b_e, hb_e, a_e, ha_e, hR_e.symm S⟩⟩
  have h_e_G₂ := S.mem_interval_of_peripheral_diff_singleton hfence_BA hcrooked hP_in hR_ba_in
    hb₁_raw ha₁_raw (hP_ends_raw.symm S) hb'_0.1 ha_0.1 (hR_ba_ends.symm S) hd_ba
  obtain ⟨_, _, hG₂_sub, hG₁_sub, hdisj_P, _⟩ :=
    Society.four_arc_partition hfence.2.1 hW'_bar ha_0 ha'_0 hb_0 hb'_0 hd_ab hd_ba
  have hdisj_G₁G₂ : Disjoint (S.Ω.interval a'_0 b_0) (S.Ω.interval b'_0 a_0) :=
    hdisj_P.symm.mono (hG₁_sub.trans subset_union_right) (hG₂_sub.trans subset_union_right)
  have hex_ends : ∃ e₁ e₂ : α, S.IsOmegaPathWithEnds P₁ e₁ e₂ ∧
      e₁ ∈ S.Ω.interval a'_0 b_0 ∧ e₂ ∈ S.Ω.interval b'_0 a_0 := by
    rcases h_e_G₁ with ⟨ha₁_G₁, _⟩ | ⟨hb₁_G₁, _⟩ <;>
    rcases h_e_G₂ with ⟨hb₁_G₂, _⟩ | ⟨ha₁_G₂, _⟩
    · exact ⟨a₁_raw, b₁_raw, hP_ends_raw, ha₁_G₁, hb₁_G₂⟩
    · exact (disjoint_left.mp hdisj_G₁G₂ ha₁_G₁ ha₁_G₂).elim
    · exact (disjoint_left.mp hdisj_G₁G₂ hb₁_G₁ hb₁_G₂).elim
    · exact ⟨b₁_raw, a₁_raw, hP_ends_raw.symm S, hb₁_G₁, ha₁_G₂⟩
  obtain ⟨e₁, e₂, hP_e12, he₁_G₁, he₂_G₂⟩ := hex_ends
  have hx_gaps := S.end_not_mem_gaps_of_not_exchangeable hcrooked hfence hatt_x
    hexch hP_in hx.1.1 hP_e12 W' rfl ha_0 ha'_0 hb_0 hb'_0 hd_ab hd_ba he₁_G₁ he₂_G₂
  have hy_gaps : y ∉ S.Ω.interval a'_0 b_0 ∧ y ∉ S.Ω.interval b'_0 a_0 := by
    rw [← mem_interval_iff_of_disjoint_interval hx.2 hy.2 hxy hx_not_W hy_not_W hdisj_int
        (hW'_sub_W ha'_0.2) (hW'_sub_W hb_0.2),
      ← mem_interval_iff_of_disjoint_interval hx.2 hy.2 hxy hx_not_W hy_not_W hdisj_int
        (hW'_sub_W hb'_0.2) (hW'_sub_W ha_0.2)]
    exact hx_gaps
  have hx_not_W' : x ∉ W' := fun h => hx_not_W (hW'_sub_W h)
  have hy_not_W' : y ∉ W' := fun h => hy_not_W (hW'_sub_W h)
  have hcr_symm : ∀ {L₁ L₂ : Graph α β} {u₁ u₂ : α},
      Disjoint V(L₁) V(L₂) →
      (∀ R ∈ P_set \ {P₁}, Disjoint V(L₁) V(R) ∧ Disjoint V(L₂) V(R)) →
      S.IsOmegaPathWithEnds L₁ u₁ e₁ →
      S.IsOmegaPathWithEnds L₂ u₂ e₂ →
      u₁ ∈ S.Ω.bar → u₁ ∉ W' → u₁ ∉ S.Ω.interval a'_0 b_0 → u₁ ∉ S.Ω.interval b'_0 a_0 →
      u₂ ∈ S.Ω.bar → u₂ ∉ W' → u₂ ∉ S.Ω.interval a'_0 b_0 → u₂ ∉ S.Ω.interval b'_0 a_0 →
      S.IsCrookedTransaction ((P_set \ {P₁}) ∪ {L₁, L₂}) := by
    intro L₁ L₂ u₁ u₂ hdisj_L12 hdisj_LR hL₁_ends hL₂_ends
      hu₁_bar hu₁_not_W' hu₁_G₁ hu₁_G₂ hu₂_bar hu₂_not_W' hu₂_G₁ hu₂_G₂
    exact crookedAfterTwoSwitches hdisj_LR hfence hW'_bar ha_0 ha'_0 hb_0 hb'_0 hd_ab hd_ba
      he₁_G₁ he₂_G₂ hdisj_L12 hL₁_ends hL₂_ends hu₁_bar hu₁_not_W' hu₁_G₁ hu₁_G₂ hu₂_bar
      hu₂_not_W' hu₂_G₁ hu₂_G₂
  have hdisj_LR_R : ∀ R ∈ P_set \ {P₁}, Disjoint V(P_left) V(R) ∧ Disjoint V(P_right) V(R) :=
    fun R hR =>
      ⟨(hfence.1.2 hP_in hR.1 (Ne.symm hR.2)).mono_left hP_left.vertexSet_mono,
        (hfence.1.2 hP_in hR.1 (Ne.symm hR.2)).mono_left hP_right.vertexSet_mono⟩
  have hcr_both : S.IsCrookedTransaction ((P_set \ {P₁}) ∪ {P_left, P_right}) := by
    rcases hP_ends.ends_eq S hP_e12 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hcr_symm hdisj_LR hdisj_LR_R (hP_left_ends.symm S) hP_right_ends
        hx.2 hx_not_W' hx_gaps.1 hx_gaps.2 hy.2 hy_not_W' hy_gaps.1 hy_gaps.2
    · have hpair : ({P_left, P_right} : Set (Graph α β)) = {P_right, P_left} :=
        pair_comm P_left P_right
      rw [hpair]
      exact hcr_symm hdisj_LR.symm (fun R hR => ⟨(hdisj_LR_R R hR).2, (hdisj_LR_R R hR).1⟩)
        hP_right_ends (hP_left_ends.symm S)
        hy.2 hy_not_W' hy_gaps.1 hy_gaps.2 hx.2 hx_not_W' hx_gaps.1 hx_gaps.2
  obtain ⟨hcard, hlt⟩ := hcard_and_lt (Or.inr (Or.inr rfl))
  exact ⟨(P_set \ {P₁}) ∪ {P_left, P_right}, Or.inr (Or.inr rfl), hcr_both, hcard, hlt⟩

/-- **Step B reduction step**: If `P ∈ P_set` (with ends `s, t`) in a crooked transaction `P_set` of
`S` splits at two distinct internal boundary vertices `x, y ∈ pathInternalVerts S.G P ∩ S.Ω.bar`
into `P_left` (`s` to `x`), `Q` (`x` to `y`), and `P_right` (`y` to `t`), and one of the open
intervals `S.Ω.interval x y` or `S.Ω.interval y x` is disjoint from `S.transactionEnds P_set`, then
at least one of `(P_set \ {P}) ∪ {P_left}`, `(P_set \ {P}) ∪ {P_right}`, or
`(P_set \ {P}) ∪ {P_left, P_right}` is a crooked transaction of `S` (with cardinality
`≥ P_set.ncard` and strictly fewer edges in `transactionUnion`). -/
theorem exists_crooked_drop_middle_of_empty_interval {S : Society α β}
    {P_set : Set (Graph α β)} {P P_left Q P_right : Graph α β} {s t x y : α}
    (hcrooked : S.IsCrookedTransaction P_set) (hP_in : P ∈ P_set)
    (hP_ends : S.IsOmegaPathWithEnds P s t)
    (hx : x ∈ pathInternalVerts S.G P ∩ S.Ω.bar)
    (hy : y ∈ pathInternalVerts S.G P ∩ S.Ω.bar) (hxy : x ≠ y)
    (hP_left : P_left ≤ P) (hQ : Q ≤ P) (hP_right : P_right ≤ P)
    (hp_left : IsGraphPathWithEnds P P_left s x)
    (hp_Q : IsGraphPathWithEnds P Q x y)
    (hp_right : IsGraphPathWithEnds P P_right y t)
    (hinter_LQ : V(P_left) ∩ V(Q) = {x})
    (hinter_QR : V(Q) ∩ V(P_right) = {y})
    (hdisj_LR : Disjoint V(P_left) V(P_right))
    (hdisj_int : Disjoint (S.Ω.interval x y) (S.transactionEnds P_set) ∨
      Disjoint (S.Ω.interval y x) (S.transactionEnds P_set)) :
    ∃ P_set' : Set (Graph α β),
      (P_set' = (P_set \ {P}) ∪ {P_left} ∨
        P_set' = (P_set \ {P}) ∪ {P_right} ∨
        P_set' = (P_set \ {P}) ∪ {P_left, P_right}) ∧
      S.IsCrookedTransaction P_set' ∧
      P_set.ncard ≤ P_set'.ncard ∧
      E(S.transactionUnion P_set').ncard < E(S.transactionUnion P_set).ncard := by
  classical
  obtain ⟨A, B, hfence⟩ := hcrooked.1
  let W := S.transactionEnds P_set
  have hx_ne_s : x ≠ s := fun h => hx.1.2 (h ▸ ⟨t, hP_ends.1⟩)
  have hx_ne_t : x ≠ t := fun h => hx.1.2 (h ▸ ⟨s, hP_ends.1.symm⟩)
  have hy_ne_s : y ≠ s := fun h => hy.1.2 (h ▸ ⟨t, hP_ends.1⟩)
  have hy_ne_t : y ≠ t := fun h => hy.1.2 (h ▸ ⟨s, hP_ends.1.symm⟩)
  have hP_left_ends : S.IsOmegaPathWithEnds P_left s x :=
    ⟨hp_left.mono hP_ends.1.le, hx_ne_s.symm, hP_ends.2.2.1, hx.2⟩
  have hP_right_ends : S.IsOmegaPathWithEnds P_right y t :=
    ⟨hp_right.mono hP_ends.1.le, hy_ne_t, hy.2, hP_ends.2.2.2⟩
  have hx_not_W : x ∉ W := by
    rintro ⟨R, hR, d, hR_xd⟩
    by_cases hRP : R = P
    · exact hx.1.2 (hRP ▸ ⟨d, hR_xd.1⟩)
    · exact disjoint_left.mp (hfence.1.2 hR hP_in hRP) hR_xd.1.left_mem hx.1.1
  have hy_not_W : y ∉ W := by
    rintro ⟨R, hR, d, hR_yd⟩
    by_cases hRP : R = P
    · exact hy.1.2 (hRP ▸ ⟨d, hR_yd.1⟩)
    · exact disjoint_left.mp (hfence.1.2 hR hP_in hRP) hR_yd.1.left_mem hy.1.1
  have hR_le : ∀ R ∈ P_set, R ≤ S.G := fun R hR => by
    obtain ⟨_, _, h⟩ := hfence.1.1 R hR; exact h.1.le
  have hP_le : P ≤ S.G := hP_ends.1.le
  have hPL_le : P_left ≤ S.G := hP_left.trans hP_le
  have hPR_le : P_right ≤ S.G := hP_right.trans hP_le
  have hPL_not_diff : P_left ∉ P_set \ {P} := fun h =>
    disjoint_left.mp (hfence.1.2 h.1 hP_in h.2) hp_left.left_mem hP_ends.1.left_mem
  have hPR_not_diff : P_right ∉ P_set \ {P} := fun h =>
    disjoint_left.mp (hfence.1.2 h.1 hP_in h.2) hp_right.right_mem hP_ends.1.right_mem
  have hPL_ne_PR : P_left ≠ P_right := fun h =>
    disjoint_left.mp hdisj_LR hp_left.left_mem (h ▸ hp_left.left_mem)
  have hfin_P : P_set.Finite := hfence.1.finite S
  have hfin_diff : (P_set \ {P}).Finite := hfin_P.sdiff
  obtain ⟨e_Q, he_Q, _⟩ := hp_Q.exists_inc_left_of_ne hxy
  have hdisj_EQ_L : Disjoint E(Q) E(P_left) :=
    disjoint_edgeSet_of_inter_singleton hp_Q hP_left (by rw [inter_comm, hinter_LQ])
  have hdisj_EQ_R : Disjoint E(Q) E(P_right) :=
    disjoint_edgeSet_of_inter_singleton hp_Q hP_right hinter_QR.subset
  have hcard_and_lt : ∀ {P_set' : Set (Graph α β)},
      (P_set' = (P_set \ {P}) ∪ {P_left} ∨
        P_set' = (P_set \ {P}) ∪ {P_right} ∨
        P_set' = (P_set \ {P}) ∪ {P_left, P_right}) →
      P_set.ncard ≤ P_set'.ncard ∧
      E(S.transactionUnion P_set').ncard < E(S.transactionUnion P_set).ncard := by
    intro P_set' hor
    exact cardinalityAfterReplacingPath hP_in hP_left hQ hP_right hfence hR_le hP_le hPL_le hPR_le
      hPL_not_diff hPR_not_diff hPL_ne_PR hfin_P hfin_diff he_Q hdisj_EQ_L hdisj_EQ_R hor
  let Q_x := section9SingleVertex S.G x
  have hatt_x : S.IsAttachmentWithEnds P_set Q_x x x :=
    isAttachmentWithEnds_section9SingleVertex S hfence.1 hP_in hx.1 hx.2
  by_cases hexch : S.IsExchangeableAttachment P_set Q_x
  · exact replaceByOneEndPath hP_in hP_ends hx hy hxy hP_left hP_right hdisj_int hfence hx_ne_t
      hP_left_ends hP_right_ends hx_not_W hy_not_W hcard_and_lt hexch
  · exact replaceByBothEndPaths hcrooked hP_in hP_ends hx hy hxy hP_left hP_right hdisj_LR
      hdisj_int hfence hP_left_ends hP_right_ends hx_not_W hy_not_W hcard_and_lt hatt_x hexch

/-- A three-way split of `P` into `P_left` (`s` to `x`), `Q ≤ N_keep` (`x` to `y`), and `P_right`
(`y` to `t`), where `x ≠ y ∈ S.Ω.bar` and the edges of `P_left` at `x` and `P_right` at `y` lie in
`E(S.G)`. -/
def IsSplitExcursion (S S_mid : Society α β) (N_keep : Graph α β)
    (P P_left Q P_right : Graph α β) (s t x y : α) : Prop :=
  S_mid.IsOmegaPathWithEnds P s t ∧
  P_left ≤ P ∧ Q ≤ P ∧ P_right ≤ P ∧ Q ≤ N_keep ∧
  IsGraphPathWithEnds P P_left s x ∧
  IsGraphPathWithEnds P Q x y ∧
  IsGraphPathWithEnds P P_right y t ∧
  x ≠ y ∧ x ∈ S.Ω.bar ∧ y ∈ S.Ω.bar ∧
  V(P_left) ∩ V(Q) = {x} ∧
  V(Q) ∩ V(P_right) = {y} ∧
  Disjoint V(P_left) V(P_right) ∧
  (∃ e_x ∈ E(P_left) ∩ E(S.G), P_left.Inc e_x x) ∧
  (∃ e_y ∈ E(P_right) ∩ E(S.G), P_right.Inc e_y y)

theorem IsSplitExcursion.symm {S S_mid : Society α β} {N_keep P P_left Q P_right : Graph α β}
    {s t x y : α} (h : IsSplitExcursion S S_mid N_keep P P_left Q P_right s t x y) :
    IsSplitExcursion S S_mid N_keep P P_right Q P_left t s y x := by
  rcases h with ⟨hP, hPL, hQ, hPR, hQN, hpL, hpQ, hpR, hxy, hx, hy, hiLQ, hiQR, hdLR, hex, hey⟩
  exact ⟨hP.symm S_mid, hPR, hQ, hPL, hQN, hpR.symm, hpQ.symm, hpL.symm, hxy.symm, hy, hx,
    inter_comm V(P_right) V(Q) ▸ hiQR, inter_comm V(Q) V(P_left) ▸ hiLQ, hdLR.symm, hey, hex⟩

theorem IsSplitExcursion.internal_and_links {S S_mid : Society α β}
    {N_keep P P_left Q P_right : Graph α β} {s t x y : α}
    (h : IsSplitExcursion S S_mid N_keep P P_left Q P_right s t x y)
    (hdisj_SN : Disjoint E(S.G) E(N_keep)) :
    x ∈ pathInternalVerts S_mid.G P ∩ S.Ω.bar ∧
    y ∈ pathInternalVerts S_mid.G P ∩ S.Ω.bar ∧
    (∀ c e, P_left.IsLink e x c → e ∈ E(S.G)) ∧
    (∀ c e, P_right.IsLink e y c → e ∈ E(S.G)) := by
  have haux : ∀ {P_l Q_m P_r : Graph α β} {s₀ t₀ x₀ y₀ : α},
      IsSplitExcursion S S_mid N_keep P P_l Q_m P_r s₀ t₀ x₀ y₀ →
      x₀ ∈ pathInternalVerts S_mid.G P ∩ S.Ω.bar ∧
      (∀ c e, P_l.IsLink e x₀ c → e ∈ E(S.G)) := by
    rintro P_l Q_m P_r s₀ t₀ x₀ y₀
      ⟨hP, hPL, hQ, _, hQN, hpL, hpQ, hpR, hxy, hx, _, _, _, hdLR, ⟨e_x, ⟨hex_L, hex_S⟩, hinc_x⟩, _⟩
    have hlink_S : ∀ c e, P_l.IsLink e x₀ c → e ∈ E(S.G) := fun c e hlink => by
      have heq : e = e_x := hpL.symm.inc_left_unique hlink.edge_mem hex_L ⟨c, hlink⟩ hinc_x
      exact heq ▸ hex_S
    obtain ⟨f_x, hfx_Q, hinc_fx⟩ := hpQ.exists_inc_left_of_ne hxy
    have hfx_not_S : f_x ∉ E(S.G) :=
      fun hS => disjoint_left.mp hdisj_SN hS (hQN.edgeSet_mono hfx_Q)
    have hx_ne_s : x₀ ≠ s₀ := by
      rintro rfl
      have heq : f_x = e_x := hP.1.inc_left_unique
        (hQ.edgeSet_mono hfx_Q) (hPL.edgeSet_mono hex_L)
        (hinc_fx.mono hQ) (hinc_x.mono hPL)
      exact hfx_not_S (heq ▸ hex_S)
    have hx_ne_t : x₀ ≠ t₀ := fun h =>
      disjoint_left.mp hdLR hpL.right_mem (h ▸ hpR.right_mem)
    have hx_int : x₀ ∈ pathInternalVerts S_mid.G P := by
      rw [hP.1.pathInternalVerts_eq]
      exact ⟨hPL.vertexSet_mono hpL.right_mem, fun h_or => h_or.elim hx_ne_s hx_ne_t⟩
    exact ⟨⟨hx_int, hx⟩, hlink_S⟩
  obtain ⟨hx_int, hlink_x⟩ := haux h
  obtain ⟨hy_int, hlink_y⟩ := haux h.symm
  exact ⟨hx_int, hy_int, hlink_x, hlink_y⟩

theorem IsSplitExcursion.extend_right {S S_mid : Society α β}
    {N_keep P P_left Q P_right P'_left Q' P'_right : Graph α β} {s t x y x' y' : α}
    (h : IsSplitExcursion S S_mid N_keep P P_left Q P_right s t x y)
    (hdisj_SN : Disjoint E(S.G) E(N_keep))
    (h' : IsSplitExcursion S S_mid N_keep P_left P'_left Q' P'_right s x x' y') :
    IsSplitExcursion S S_mid N_keep P P'_left Q'
      (subgraphUnion P P'_right (subgraphUnion P Q P_right)) s t x' y' ∧
    Disjoint V(Q') V(Q) := by
  obtain ⟨_, hy'_int, _, _⟩ := h'.internal_and_links hdisj_SN
  obtain ⟨_, _, hlink_x, _⟩ := h.internal_and_links hdisj_SN
  rcases h with ⟨hP, hPL, hQ, hPR, _, hpL, hpQ, hpR, _, _, _, hiLQ, hiQR, hdLR, _, hey⟩
  rcases h' with ⟨hPL_ends, hP'L, hQ', hP'R, hQ'N, hp'L, hp'Q, hp'R, hx'y', hx', hy',
    hi'LQ, hi'QR, hd'LR, hex', hey'⟩
  have hy'_ne_x : y' ≠ x := fun h_eq =>
    hy'_int.1.2 (by rw [hPL_ends.1.pathEnds_eq, h_eq]; exact Or.inr rfl)
  have hx_not_Q' : x ∉ V(Q') := fun hxQ' => by
    have hx_in : x ∈ V(Q') ∩ V(P'_right) := ⟨hxQ', hp'R.right_mem⟩
    rw [hi'QR, mem_singleton_iff] at hx_in
    exact hy'_ne_x hx_in.symm
  have hx_not_P'L : x ∉ V(P'_left) := fun hxP'L =>
    disjoint_left.mp hd'LR hxP'L hp'R.right_mem
  have hdisj_Q'Q : Disjoint V(Q') V(Q) := by
    rw [disjoint_left]
    intro z hzQ' hzQ
    have hzx : z = x := by
      have hz_in : z ∈ V(P_left) ∩ V(Q) := ⟨hQ'.vertexSet_mono hzQ', hzQ⟩
      rwa [hiLQ, mem_singleton_iff] at hz_in
    exact hx_not_Q' (hzx ▸ hzQ')
  let QR := subgraphUnion P Q P_right
  have hQR_P : QR ≤ P := subgraphUnion_le hQ hPR
  have hp_QR : IsGraphPathWithEnds P QR x t := hpQ.subgraphUnion hpR hiQR
  have hP'R_P : P'_right ≤ P := hP'R.trans hPL
  have hi_P'R_QR : V(P'_right) ∩ V(QR) = {x} := by
    refine Subset.antisymm ?_ (singleton_subset_iff.mpr ⟨hp'R.right_mem, Or.inl hpQ.left_mem⟩)
    rintro z ⟨hzP'R, hzQ | hzPR⟩
    · have hz_in : z ∈ V(P_left) ∩ V(Q) := ⟨hP'R.vertexSet_mono hzP'R, hzQ⟩
      rwa [hiLQ] at hz_in
    · exact (disjoint_left.mp hdLR (hP'R.vertexSet_mono hzP'R) hzPR).elim
  let P₀_right := subgraphUnion P P'_right QR
  have hP₀R_P : P₀_right ≤ P := subgraphUnion_le hP'R_P hQR_P
  have hp₀_R : IsGraphPathWithEnds P P₀_right y' t :=
    (hp'R.mono hPL).subgraphUnion hp_QR hi_P'R_QR
  have hi_Q'_P₀R : V(Q') ∩ V(P₀_right) = {y'} := by
    refine Subset.antisymm ?_ (singleton_subset_iff.mpr ⟨hp'Q.right_mem, Or.inl hp'R.left_mem⟩)
    rintro z ⟨hzQ', hzP'R | hzQ | hzPR⟩
    · have hz_in : z ∈ V(Q') ∩ V(P'_right) := ⟨hzQ', hzP'R⟩
      rwa [hi'QR] at hz_in
    · exact (disjoint_left.mp hdisj_Q'Q hzQ' hzQ).elim
    · exact (disjoint_left.mp hdLR (hQ'.vertexSet_mono hzQ') hzPR).elim
  have hd_P'L_P₀R : Disjoint V(P'_left) V(P₀_right) := by
    rw [disjoint_left]
    rintro z hzP'L (hzP'R | hzQ | hzPR)
    · exact disjoint_left.mp hd'LR hzP'L hzP'R
    · have hzx : z = x := by
        have hz_in : z ∈ V(P_left) ∩ V(Q) := ⟨hP'L.vertexSet_mono hzP'L, hzQ⟩
        rwa [hiLQ, mem_singleton_iff] at hz_in
      exact hx_not_P'L (hzx ▸ hzP'L)
    · exact disjoint_left.mp hdLR (hP'L.vertexSet_mono hzP'L) hzPR
  have hey'₀ : ∃ e_y ∈ E(P₀_right) ∩ E(S.G), P₀_right.Inc e_y y' := by
    rcases hey' with ⟨e_y, ⟨hey_R, hey_S⟩, hinc_y⟩
    have hle : P'_right ≤ P₀_right := le_subgraphUnion_left hP'R_P hQR_P
    exact ⟨e_y, ⟨hle.edgeSet_mono hey_R, hey_S⟩, hinc_y.mono hle⟩
  exact ⟨⟨hP, hP'L.trans hPL, hQ'.trans hPL, hP₀R_P, hQ'N,
    hp'L.mono hPL, hp'Q.mono hPL, hp₀_R, hx'y', hx', hy',
    hi'LQ, hi_Q'_P₀R, hd_P'L_P₀R, hex', hey'₀⟩, hdisj_Q'Q⟩

theorem IsSplitExcursion.lift_of_subpath {S S_mid : Society α β}
    {N_keep P P_left Q P_right P' P'_left Q' P'_right : Graph α β}
    {s t x y s' t' x' y' : α}
    (h : IsSplitExcursion S S_mid N_keep P P_left Q P_right s t x y)
    (hdisj_SN : Disjoint E(S.G) E(N_keep))
    (hP'_or : P' = P_left ∨ P' = P_right)
    (h' : IsSplitExcursion S S_mid N_keep P' P'_left Q' P'_right s' t' x' y') :
    ∃ s₀ t₀ x₀ y₀ : α, ∃ P₀_left P₀_right : Graph α β,
      ({x₀, y₀} : Set α) = {x', y'} ∧
      IsSplitExcursion S S_mid N_keep P P₀_left Q' P₀_right s₀ t₀ x₀ y₀ ∧
      Disjoint V(Q') V(Q) := by
  have hleft_case : ∀ {P_l Q_m P_r : Graph α β} {s₁ t₁ x₁ y₁ : α},
      IsSplitExcursion S S_mid N_keep P P_l Q_m P_r s₁ t₁ x₁ y₁ →
      IsSplitExcursion S S_mid N_keep P_l P'_left Q' P'_right s' t' x' y' →
      ∃ s₀ t₀ x₀ y₀ : α, ∃ P₀_left P₀_right : Graph α β,
        ({x₀, y₀} : Set α) = {x', y'} ∧
        IsSplitExcursion S S_mid N_keep P P₀_left Q' P₀_right s₀ t₀ x₀ y₀ ∧
        Disjoint V(Q') V(Q_m) := by
    intro P_l Q_m P_r s₁ t₁ x₁ y₁ h₁ h₂
    rcases (h₁.2.2.2.2.2.1.mono h₁.1.1.le).ends_eq h₂.1.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · obtain ⟨h_ext, hdisj⟩ := h₁.extend_right hdisj_SN h₂
      exact ⟨s', t₁, x', y', P'_left, _, rfl, h_ext, hdisj⟩
    · obtain ⟨h_ext, hdisj⟩ := h₁.extend_right hdisj_SN h₂.symm
      exact ⟨t', t₁, y', x', P'_right, _, pair_comm y' x', h_ext, hdisj⟩
  rcases hP'_or with rfl | rfl
  · exact hleft_case h h'
  · exact hleft_case h.symm h'

theorem exists_isSplitExcursion_of_not_le {S S_mid : Society α β} {N_keep P : Graph α β} {s t : α}
    (hE_mid : E(S_mid.G) ⊆ E(S.G) ∪ E(N_keep))
    (hSG_le : S.G ≤ S_mid.G) (hN_le : N_keep ≤ S_mid.G)
    (hV_inter : V(S.G) ∩ V(N_keep) ⊆ S.Ω.bar)
    (hP_ends : S_mid.IsOmegaPathWithEnds P s t)
    (hfirst : ∀ c e, P.IsLink e s c → e ∈ E(S.G))
    (hlast : ∀ c e, P.IsLink e t c → e ∈ E(S.G))
    (hnot_le : ¬ P ≤ S.G) :
    ∃ P_left Q P_right : Graph α β, ∃ x y : α,
      IsSplitExcursion S S_mid N_keep P P_left Q P_right s t x y := by
  have hex_edge : ∃ e₀ ∈ E(P), e₀ ∉ E(S.G) := by
    by_contra! hall
    apply hnot_le
    rw [(Compatible.of_le_le hP_ends.1.le hSG_le).le_iff]
    refine ⟨fun v hvP => ?_, hall⟩
    obtain ⟨e, heP, z, hvz⟩ := hP_ends.1.exists_inc_of_mem_of_ne hP_ends.2.1 hvP
    obtain ⟨a_e, b_e, habS⟩ := S.G.exists_isLink_of_mem_edgeSet (hall e heP)
    rcases (hvz.mono hP_ends.1.le).left_eq_or_eq (habS.mono hSG_le) with rfl | rfl
    · exact habS.left_mem
    · exact habS.right_mem
  obtain ⟨e₀, he₀P, he₀_not_S⟩ := hex_edge
  obtain ⟨u₀, v₀, hu₀v₀⟩ := P.exists_isLink_of_mem_edgeSet he₀P
  let Y_N : Set α := {v ∈ V(P) | ∃ e ∈ E(P) \ E(S.G), P.Inc e v}
  have hu₀_YN : u₀ ∈ V(P) ∩ Y_N :=
    ⟨hu₀v₀.left_mem, hu₀v₀.left_mem, e₀, ⟨he₀P, he₀_not_S⟩, v₀, hu₀v₀⟩
  obtain ⟨x, ⟨hxP, _, f_x, ⟨hfx_P, hfx_not_S⟩, z_x, hfx_inc⟩, P_left, P_xt,
    hP_left, hP_xt, hp_left, hp_xt, hunion₁, hinter₁, hdisjE₁, hdisjY₁⟩ :=
    hP_ends.1.exists_first_split_at_mem ⟨u₀, hu₀_YN⟩
  have hEL_sub_S : E(P_left) ⊆ E(S.G) := by
    intro e heL
    by_contra he_not_S
    have heP : e ∈ E(P) := hP_left.edgeSet_mono heL
    obtain ⟨a, b, habL⟩ := P_left.exists_isLink_of_mem_edgeSet heL
    have habP : P.IsLink e a b := habL.mono hP_left
    have haY : a ∈ Y_N := ⟨habP.left_mem, e, ⟨heP, he_not_S⟩, b, habP⟩
    have hbY : b ∈ Y_N := ⟨habP.right_mem, e, ⟨heP, he_not_S⟩, a, habP.symm⟩
    have hax : a = x := by
      by_contra hne; exact disjoint_left.mp hdisjY₁ ⟨habL.left_mem, hne⟩ haY
    have hbx : b = x := by
      by_contra hne; exact disjoint_left.mp hdisjY₁ ⟨habL.right_mem, hne⟩ hbY
    rw [hax, hbx] at habP
    exact hP_ends.1.not_isLoopAt heP x (habP.mono hP_ends.1.le)
  have hfx_xt : f_x ∈ E(P_xt) := by
    have hfx_union : f_x ∈ E(P_left) ∪ E(P_xt) := by
      rw [← edgeSet_subgraphUnion hP_left hP_xt, hunion₁]; exact hfx_P
    exact hfx_union.resolve_left fun hL => hfx_not_S (hEL_sub_S hL)
  have hfx_link_xt : P_xt.IsLink f_x x z_x := by
    obtain ⟨a, b, hab⟩ := P_xt.exists_isLink_of_mem_edgeSet hfx_xt
    rcases (hab.mono hP_xt).left_eq_or_eq hfx_inc with rfl | rfl
    · rcases (hab.symm.mono hP_xt).left_eq_or_eq hfx_inc.symm with rfl | rfl
      · exact hab
      · exact (hP_ends.1.not_isLoopAt hfx_P b (hab.mono (hP_xt.trans hP_ends.1.le))).elim
    · rcases (hab.symm.mono hP_xt).left_eq_or_eq hfx_inc with rfl | rfl
      · exact hab.symm
      · exact (hP_ends.1.not_isLoopAt hfx_P b (hab.mono (hP_xt.trans hP_ends.1.le))).elim
  have hx_ne_s : x ≠ s := by
    rintro rfl
    exact hfx_not_S (hfirst z_x f_x hfx_inc)
  have hx_ne_t : x ≠ t := by
    rintro rfl
    exact hfx_not_S (hlast z_x f_x hfx_inc)
  obtain ⟨e_x, hex_L, c_x, hlink_ex⟩ := hp_left.symm.exists_inc_left_of_ne hx_ne_s
  have hex_S : e_x ∈ E(S.G) := hEL_sub_S hex_L
  obtain ⟨e_t, het_xt, c_t, hlink_et⟩ := hp_xt.symm.exists_inc_left_of_ne hx_ne_t.symm
  have het_S : e_t ∈ E(S.G) := hlast c_t e_t (hlink_et.mono hP_xt)
  let Y_S : Set α := {v ∈ V(P_xt) | ∃ e ∈ E(P_xt) ∩ E(S.G), P_xt.Inc e v}
  have ht_YS : t ∈ V(P_xt) ∩ Y_S :=
    ⟨hp_xt.right_mem, hp_xt.right_mem, e_t, ⟨het_xt, het_S⟩, c_t, hlink_et⟩
  obtain ⟨y, ⟨hy_xt, _, e_y, ⟨hey_xt, hey_S⟩, z_y, hey_inc⟩, Q, P_right,
    hQ_xt, hP_right_xt, hp_Q, hp_right, hunion₂, hinter₂, hdisjE₂, hdisjY₂⟩ :=
    hp_xt.exists_first_split_at_mem ⟨t, ht_YS⟩
  have hx_not_YS : x ∉ Y_S := by
    rintro ⟨_, e, ⟨he_xt, he_S⟩, z, he_inc⟩
    have heq : e = f_x := hp_xt.inc_left_unique he_xt hfx_xt ⟨z, he_inc⟩ ⟨z_x, hfx_link_xt⟩
    exact hfx_not_S (heq ▸ he_S)
  have hxy : x ≠ y := by
    rintro rfl; exact hx_not_YS ⟨hy_xt, e_y, ⟨hey_xt, hey_S⟩, z_y, hey_inc⟩
  have hEQ_disj_S : Disjoint E(Q) E(S.G) := by
    rw [disjoint_left]
    intro e heQ heS
    have he_xt : e ∈ E(P_xt) := hQ_xt.edgeSet_mono heQ
    obtain ⟨a, b, habQ⟩ := Q.exists_isLink_of_mem_edgeSet heQ
    have hab_xt : P_xt.IsLink e a b := habQ.mono hQ_xt
    have haY : a ∈ Y_S := ⟨hab_xt.left_mem, e, ⟨he_xt, heS⟩, b, hab_xt⟩
    have hbY : b ∈ Y_S := ⟨hab_xt.right_mem, e, ⟨he_xt, heS⟩, a, hab_xt.symm⟩
    have hay : a = y := by
      by_contra hne; exact disjoint_left.mp hdisjY₂ ⟨habQ.left_mem, hne⟩ haY
    have hby : b = y := by
      by_contra hne; exact disjoint_left.mp hdisjY₂ ⟨habQ.right_mem, hne⟩ hbY
    rw [hay, hby] at hab_xt
    exact hP_ends.1.not_isLoopAt (hP_xt.edgeSet_mono he_xt) y (hab_xt.mono
      (hP_xt.trans hP_ends.1.le))
  have hQ_P : Q ≤ P := hQ_xt.trans hP_xt
  have hP_right_P : P_right ≤ P := hP_right_xt.trans hP_xt
  have hQ_N : Q ≤ N_keep := by
    have hQ_mid : Q ≤ S_mid.G := hQ_P.trans hP_ends.1.le
    rw [(Compatible.of_le_le hQ_mid hN_le).le_iff]
    have hEQ_N : E(Q) ⊆ E(N_keep) := fun e heQ =>
      (hE_mid (hQ_mid.edgeSet_mono heQ)).resolve_left (disjoint_left.mp hEQ_disj_S heQ)
    refine ⟨fun v hvQ => ?_, hEQ_N⟩
    obtain ⟨e, heQ, z, hvzQ⟩ := hp_Q.exists_inc_of_mem_of_ne hxy hvQ
    obtain ⟨a_e, b_e, habN⟩ := N_keep.exists_isLink_of_mem_edgeSet (hEQ_N heQ)
    rcases (hvzQ.mono hQ_mid).left_eq_or_eq (habN.mono hN_le) with rfl | rfl
    · exact habN.left_mem
    · exact habN.right_mem
  have hey_right : e_y ∈ E(P_right) := by
    have hey_union : e_y ∈ E(Q) ∪ E(P_right) := by
      rw [← edgeSet_subgraphUnion hQ_xt hP_right_xt, hunion₂]; exact hey_xt
    exact hey_union.resolve_left fun hQ => disjoint_left.mp hEQ_disj_S hQ hey_S
  have hey_inc_right : P_right.Inc e_y y := by
    obtain ⟨a, b, hab⟩ := P_right.exists_isLink_of_mem_edgeSet hey_right
    rcases hey_inc.left_eq_or_eq (hab.mono hP_right_xt) with rfl | rfl
    · exact ⟨b, hab⟩
    · exact ⟨a, hab.symm⟩
  have hx_VS : x ∈ V(S.G) := by
    obtain ⟨a, b, habS⟩ := S.G.exists_isLink_of_mem_edgeSet hex_S
    rcases (hlink_ex.mono (hP_left.trans hP_ends.1.le)).left_eq_or_eq
      (habS.mono hSG_le) with rfl | rfl
    · exact habS.left_mem
    · exact habS.right_mem
  have hy_VS : y ∈ V(S.G) := by
    rcases hey_inc_right with ⟨w, hlink_ey⟩
    obtain ⟨a, b, habS⟩ := S.G.exists_isLink_of_mem_edgeSet hey_S
    rcases (hlink_ey.mono (hP_right_P.trans hP_ends.1.le)).left_eq_or_eq
      (habS.mono hSG_le) with rfl | rfl
    · exact habS.left_mem
    · exact habS.right_mem
  have hx_bar : x ∈ S.Ω.bar := hV_inter ⟨hx_VS, hQ_N.vertexSet_mono hp_Q.left_mem⟩
  have hy_bar : y ∈ S.Ω.bar := hV_inter ⟨hy_VS, hQ_N.vertexSet_mono hp_Q.right_mem⟩
  have hi_LQ : V(P_left) ∩ V(Q) = {x} := by
    refine Subset.antisymm ?_ (singleton_subset_iff.mpr ⟨hp_left.right_mem, hp_Q.left_mem⟩)
    rw [← hinter₁]
    exact inter_subset_inter_right _ hQ_xt.vertexSet_mono
  have hd_LR : Disjoint V(P_left) V(P_right) := by
    rw [disjoint_left]
    intro z hzL hzR
    have hzx : z = x := by
      have hz_in : z ∈ V(P_left) ∩ V(P_xt) := ⟨hzL, hP_right_xt.vertexSet_mono hzR⟩
      rwa [hinter₁, mem_singleton_iff] at hz_in
    have hzy : z = y := by
      have hz_in : z ∈ V(Q) ∩ V(P_right) := ⟨hzx ▸ hp_Q.left_mem, hzR⟩
      rwa [hinter₂, mem_singleton_iff] at hz_in
    exact hxy (hzx.symm.trans hzy)
  exact ⟨P_left, Q, P_right, x, y, hP_ends, hP_left, hQ_P, hP_right_P, hQ_N,
    hp_left, hp_Q.mono hP_xt, hp_right.mono hP_xt, hxy, hx_bar, hy_bar,
    hi_LQ, hinter₂, hd_LR, ⟨e_x, ⟨hex_L, hex_S⟩, c_x, hlink_ex⟩, ⟨e_y, ⟨hey_right, hey_S⟩,
      hey_inc_right⟩⟩

/-- Invariant maintained during Step B of `(9.1)` while eliminating excursions into `N_keep`. -/
def IsValidStepBConfig (S S_mid : Society α β) (N_keep : Graph α β) (p : ℕ)
    (P_set : Set (Graph α β)) : Prop :=
  S_mid.IsCrookedTransaction P_set ∧
  p ≤ P_set.ncard ∧
  (∀ P ∈ P_set, ∀ s t c e, S_mid.IsOmegaPathWithEnds P s t → P.IsLink e s c → e ∈ E(S.G)) ∧
  (∀ P ∈ P_set, ∀ P_left Q P_right s t x y,
    IsSplitExcursion S S_mid N_keep P P_left Q P_right s t x y →
    Disjoint (S.Ω.interval x y) (S_mid.transactionEnds P_set) ∨
    Disjoint (S.Ω.interval y x) (S_mid.transactionEnds P_set))

theorem stepB_of_theorem_9_1 {S S_mid : Society α β} {N : Neighborhood α β}
    {N_keep : Graph α β} {p : ℕ} {P_set₁ : Set (Graph α β)}
    (hrural : N.IsRural)
    (hΩ_mid : S_mid.Ω = S.Ω)
    (hΩ₀ : N.Ω₀ = S.Ω)
    (hE_mid : E(S_mid.G) ⊆ E(S.G) ∪ E(N_keep))
    (hSG_le : S.G ≤ S_mid.G) (hN_le : N_keep ≤ S_mid.G) (hN_keep_le : N_keep ≤ N.G)
    (hdisj_SN : Disjoint E(S.G) E(N_keep))
    (hV_inter : V(S.G) ∩ V(N_keep) ⊆ S.Ω.bar)
    (hvalid₁ : IsValidStepBConfig S S_mid N_keep p P_set₁) :
    ∃ P_set : Set (Graph α β), S.IsCrookedTransaction P_set ∧ p ≤ P_set.ncard := by
  classical
  have hex_B : ∃ m : ℕ, ∃ P_set : Set (Graph α β),
      IsValidStepBConfig S S_mid N_keep p P_set ∧
      E(S_mid.transactionUnion P_set).ncard = m :=
    ⟨E(S_mid.transactionUnion P_set₁).ncard, P_set₁, hvalid₁, rfl⟩
  let m_min := Nat.find hex_B
  obtain ⟨P_set, hvalid, hcard_m⟩ := Nat.find_spec hex_B
  have hP_le_S : ∀ P ∈ P_set, P ≤ S.G := by
    by_contra! hnot_all
    rcases hnot_all with ⟨P₀, hP₀_in, hP₀_not_le⟩
    obtain ⟨A, B, hfence⟩ := hvalid.1.1
    let W := S_mid.transactionEnds P_set
    have hex_exc : ∃ d : ℕ, ∃ P₁ ∈ P_set, ∃ P_left Q P_right : Graph α β, ∃ s t x y : α,
        IsSplitExcursion S S_mid N_keep P₁ P_left Q P_right s t x y ∧
        Disjoint (S.Ω.interval x y) W ∧
        S.Ω.bar.ncard - (S.Ω.interval x y).ncard = d := by
      obtain ⟨s₀, _, t₀, _, hP₀_ends⟩ := hfence.2.2 P₀ hP₀_in
      obtain ⟨P₀_left, Q₀, P₀_right, x₀, y₀, hexc₀⟩ :=
        exists_isSplitExcursion_of_not_le hE_mid hSG_le hN_le hV_inter hP₀_ends
          (fun c e hl => hvalid.2.2.1 P₀ hP₀_in s₀ t₀ c e hP₀_ends hl)
          (fun c e hl => hvalid.2.2.1 P₀ hP₀_in t₀ s₀ c e (hP₀_ends.symm S_mid) hl)
          hP₀_not_le
      rcases hvalid.2.2.2 P₀ hP₀_in P₀_left Q₀ P₀_right s₀ t₀ x₀ y₀ hexc₀ with hdisj | hdisj
      · exact ⟨_, P₀, hP₀_in, P₀_left, Q₀, P₀_right, s₀, t₀, x₀, y₀, hexc₀, hdisj, rfl⟩
      · exact ⟨_, P₀, hP₀_in, P₀_right, Q₀, P₀_left, t₀, s₀, y₀, x₀, hexc₀.symm, hdisj, rfl⟩
    let d_min := Nat.find hex_exc
    obtain ⟨P₁, hP₁_in, P_left, Q, P_right, s, t, x, y, hexc, hdisj_xy, hd_eq⟩ :=
      Nat.find_spec hex_exc
    have hmax_xy : ∀ P' ∈ P_set, ∀ P'_left Q' P'_right : Graph α β, ∀ s' t' x' y' : α,
        IsSplitExcursion S S_mid N_keep P' P'_left Q' P'_right s' t' x' y' →
        Disjoint (S.Ω.interval x' y') W →
        (S.Ω.interval x' y').ncard ≤ (S.Ω.interval x y).ncard := by
      intro P' hP' P'_left Q' P'_right s' t' x' y' hexc' hdisj'
      have hle_d : d_min ≤ S.Ω.bar.ncard - (S.Ω.interval x' y').ncard :=
        Nat.find_min' hex_exc ⟨P', hP', P'_left, Q', P'_right, s', t', x', y', hexc', hdisj', rfl⟩
      have hsub_bar : (S.Ω.interval x' y').ncard ≤ S.Ω.bar.ncard :=
        ncard_le_ncard (S.Ω.interval_subset_bar x' y') S.Ω.finite_bar
      omega
    obtain ⟨hx_int, hy_int, hlink_x, hlink_y⟩ := hexc.internal_and_links hdisj_SN
    have hP₁_ends := hexc.1
    obtain ⟨hP_left_le, hQ_le, hP_right_le, hQ_N, hp_left, hp_Q, hp_right,
      hxy, hx_bar, hy_bar, hi_LQ, hi_QR, hd_LR, _, _⟩ := hexc.2
    have hpL_mid : IsGraphPathWithEnds S_mid.G P_left s x := hp_left.mono hP₁_ends.1.le
    have hpR_mid : IsGraphPathWithEnds S_mid.G P_right y t := hp_right.mono hP₁_ends.1.le
    have hx_int' : x ∈ pathInternalVerts S_mid.G P₁ ∩ S_mid.Ω.bar := by
      rwa [hΩ_mid]
    have hy_int' : y ∈ pathInternalVerts S_mid.G P₁ ∩ S_mid.Ω.bar := by
      rwa [hΩ_mid]
    have hdisj_xy_mid : Disjoint (S_mid.Ω.interval x y) W ∨ Disjoint (S_mid.Ω.interval y x) W := by
      rw [hΩ_mid]; exact Or.inl hdisj_xy
    obtain ⟨P_set', hP_set'_or, hcr', hcard_le, hlt_E⟩ :=
      exists_crooked_drop_middle_of_empty_interval hvalid.1 hP₁_in hP₁_ends hx_int' hy_int' hxy
        hP_left_le hQ_le hP_right_le hp_left hp_Q hp_right
        hi_LQ hi_QR hd_LR hdisj_xy_mid
    have hR_cases_of_mem : ∀ {R : Graph α β}, R ∈ P_set' →
        R ∈ P_set \ {P₁} ∨ R = P_left ∨ R = P_right := by
      intro R hR_in'
      rcases hP_set'_or with rfl | rfl | rfl
      · rcases hR_in' with h | h
        · exact Or.inl h
        · rw [mem_singleton_iff] at h; exact Or.inr (Or.inl h)
      · rcases hR_in' with h | h
        · exact Or.inl h
        · rw [mem_singleton_iff] at h; exact Or.inr (Or.inr h)
      · rcases hR_in' with h | (h | h)
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · rw [mem_singleton_iff] at h; exact Or.inr (Or.inr h)
    have hW'_sub : S_mid.transactionEnds P_set' ⊆ W ∪ {x, y} := by
      rintro z ⟨R, hR_in', d, hR_ends⟩
      rcases hR_cases_of_mem hR_in' with hR_diff | hR_eq | hR_eq
      · exact Or.inl ⟨R, hR_diff.1, d, hR_ends⟩
      · rw [hR_eq] at hR_ends
        rcases hR_ends.1.ends_eq hpL_mid with ⟨hz, _⟩ | ⟨_, hz⟩
        · rw [← hz]; exact Or.inl ⟨P₁, hP₁_in, t, hP₁_ends⟩
        · rw [← hz]; exact Or.inr (Or.inl rfl)
      · rw [hR_eq] at hR_ends
        rcases hR_ends.1.ends_eq hpR_mid with ⟨hz, _⟩ | ⟨_, hz⟩
        · rw [← hz]; exact Or.inr (Or.inr rfl)
        · rw [← hz]; exact Or.inl ⟨P₁, hP₁_in, s, hP₁_ends.symm S_mid⟩
    have hvalid' : IsValidStepBConfig S S_mid N_keep p P_set' := by
      refine ⟨hcr', hvalid.2.1.trans hcard_le, ?_, ?_⟩
      · intro R hR_in' s' t' c e hR_ends hlink
        rcases hR_cases_of_mem hR_in' with hR_diff | hR_eq | hR_eq
        · exact hvalid.2.2.1 R hR_diff.1 s' t' c e hR_ends hlink
        · rw [hR_eq] at hR_ends hlink
          rcases hR_ends.1.ends_eq hpL_mid with ⟨hs', _⟩ | ⟨_, hs'⟩
          · rw [← hs'] at hlink
            exact hvalid.2.2.1 P₁ hP₁_in s t c e hP₁_ends (hlink.mono hP_left_le)
          · rw [← hs'] at hlink
            exact hlink_x c e hlink
        · rw [hR_eq] at hR_ends hlink
          rcases hR_ends.1.ends_eq hpR_mid with ⟨hs', _⟩ | ⟨_, hs'⟩
          · rw [← hs'] at hlink
            exact hlink_y c e hlink
          · rw [← hs'] at hlink
            exact hvalid.2.2.1 P₁ hP₁_in t s c e (hP₁_ends.symm S_mid) (hlink.mono hP_right_le)
      · intro R hR_in' P'_left Q' P'_right s' t' x' y' hexc'
        have h_lifted : ∃ R₀ ∈ P_set, ∃ s₀ t₀ : α, ∃ P₀_left P₀_right : Graph α β,
            IsSplitExcursion S S_mid N_keep R₀ P₀_left Q' P₀_right s₀ t₀ x' y' ∧
            Disjoint V(Q') V(Q) := by
          rcases hR_cases_of_mem hR_in' with hR_diff | hR_or
          · refine ⟨R, hR_diff.1, s', t', P'_left, P'_right, hexc', ?_⟩
            exact (hfence.1.2 hR_diff.1 hP₁_in hR_diff.2).mono
              hexc'.2.2.1.vertexSet_mono hQ_le.vertexSet_mono
          · obtain ⟨s₀, t₀, x₀, y₀, P₀_left, P₀_right, hpair, hexc₀, hdisj_Q'Q⟩ :=
              hexc.lift_of_subpath hdisj_SN hR_or hexc'
            have hx₀_in : x₀ ∈ ({x', y'} : Set α) := by rw [← hpair]; simp
            have hy₀_in : y₀ ∈ ({x', y'} : Set α) := by rw [← hpair]; simp
            have hx₀y₀ : x₀ ≠ y₀ := by
              obtain ⟨_, _, _, _, _, _, _, _, hne, _⟩ := hexc₀; exact hne
            rcases hx₀_in with h1 | h1 <;> rcases hy₀_in with h2 | h2
            · exact (hx₀y₀ (h1.trans h2.symm)).elim
            · rw [h1, h2] at hexc₀
              exact ⟨P₁, hP₁_in, s₀, t₀, P₀_left, P₀_right, hexc₀, hdisj_Q'Q⟩
            · rw [h1, h2] at hexc₀
              exact ⟨P₁, hP₁_in, t₀, s₀, P₀_right, P₀_left, hexc₀.symm, hdisj_Q'Q⟩
            · exact (hx₀y₀ (h1.trans h2.symm)).elim
        obtain ⟨R₀, hR₀_in, s₀, t₀, P₀_left, P₀_right, hexc₀, hdisj_Q'Q⟩ := h_lifted
        have h_empty_W' : ∀ {P_l P_r : Graph α β} {s₁ t₁ a' b' : α},
            IsSplitExcursion S S_mid N_keep R₀ P_l Q' P_r s₁ t₁ a' b' →
            Disjoint (S.Ω.interval a' b') W →
            Disjoint (S.Ω.interval a' b') (S_mid.transactionEnds P_set') := by
          intro P_l P_r s₁ t₁ a' b' hexc_ab hdisj_ab_W
          have hcard_ab_le : (S.Ω.interval a' b').ncard ≤ (S.Ω.interval x y).ncard :=
            hmax_xy R₀ hR₀_in P_l Q' P_r s₁ t₁ a' b' hexc_ab hdisj_ab_W
          obtain ⟨hR₀_ends, _, _, _, hQ'_N, _, hp_Q', _, ha'b', ha'_bar, hb'_bar, _⟩ := hexc_ab
          have hQ_path_N : IsGraphPathWithEnds N.G Q x y :=
            (hp_Q.mono hP₁_ends.1.le).of_le (hQ_N.trans hN_keep_le)
          have hQ'_path_N : IsGraphPathWithEnds N.G Q' a' b' :=
            (hp_Q'.mono hR₀_ends.1.le).of_le (hQ'_N.trans hN_keep_le)
          have hnot_cr : ¬ S.Ω.Crosses a' b' x y := by
            rw [← hΩ₀]
            exact not_crosses_inner_of_disjoint_paths hrural
              hQ'_path_N (hΩ₀.symm ▸ ha'_bar) (hΩ₀.symm ▸ hb'_bar)
              hQ_path_N (hΩ₀.symm ▸ hx_bar) (hΩ₀.symm ▸ hy_bar) hdisj_Q'Q
          have hx_ne_a' : x ≠ a' := fun h =>
            disjoint_left.mp hdisj_Q'Q hQ'_path_N.left_mem (h ▸ hQ_path_N.left_mem)
          have hx_ne_b' : x ≠ b' := fun h =>
            disjoint_left.mp hdisj_Q'Q hQ'_path_N.right_mem (h ▸ hQ_path_N.left_mem)
          have hy_ne_a' : y ≠ a' := fun h =>
            disjoint_left.mp hdisj_Q'Q hQ'_path_N.left_mem (h ▸ hQ_path_N.right_mem)
          have hy_ne_b' : y ≠ b' := fun h =>
            disjoint_left.mp hdisj_Q'Q hQ'_path_N.right_mem (h ▸ hQ_path_N.right_mem)
          have hboth_not : x ∉ S.Ω.interval a' b' ∧ y ∉ S.Ω.interval a' b' := by
            have hboth_if_one : x ∈ S.Ω.interval a' b' ∨ y ∈ S.Ω.interval a' b' →
                x ∈ S.Ω.interval a' b' ∧ y ∈ S.Ω.interval a' b' := by
              rintro (hx_ab | hy_ab)
              · refine ⟨hx_ab, ?_⟩
                rcases S.Ω.mem_interval_or_interval_swap ha'_bar hb'_bar hy_bar ha'b' hy_ne_a'
                  hy_ne_b'
                  with hy_ab | hy_ba
                · exact hy_ab
                · exact (hnot_cr (S.Ω.crosses_iff_interval.mpr (Or.inl ⟨hx_ab, hy_ba⟩))).elim
              · refine ⟨?_, hy_ab⟩
                rcases S.Ω.mem_interval_or_interval_swap ha'_bar hb'_bar hx_bar ha'b' hx_ne_a'
                  hx_ne_b'
                  with hx_ab | hx_ba
                · exact hx_ab
                · exact (hnot_cr (S.Ω.crosses_iff_interval.mpr (Or.inr ⟨hy_ab, hx_ba⟩))).elim
            by_contra hnot
            have hor : x ∈ S.Ω.interval a' b' ∨ y ∈ S.Ω.interval a' b' := by tauto
            obtain ⟨hx_ab, hy_ab⟩ := hboth_if_one hor
            rcases S.Ω.interval_subset_interval_or_swap hx_ab hy_ab hxy with hsub_xy | hsub_yx
            · have hfin_ab : (S.Ω.interval a' b').Finite :=
                S.Ω.finite_bar.subset (S.Ω.interval_subset_bar a' b')
              have hlt_card : (S.Ω.interval x y).ncard < (S.Ω.interval a' b').ncard :=
                ncard_lt_ncard ⟨hsub_xy, fun hall => (hall hy_ab).1.2 (Or.inr rfl)⟩ hfin_ab
              omega
            · have hs_W : s ∈ W := ⟨P₁, hP₁_in, t, hP₁_ends⟩
              have hs_bar : s ∈ S.Ω.bar := hΩ_mid ▸ hP₁_ends.2.2.1
              have hs_ne_x : s ≠ x := fun h => hx_int.1.2 (h ▸ ⟨t, hP₁_ends.1⟩)
              have hs_ne_y : s ≠ y := fun h => hy_int.1.2 (h ▸ ⟨t, hP₁_ends.1⟩)
              rcases S.Ω.mem_interval_or_interval_swap hx_bar hy_bar hs_bar hxy hs_ne_x hs_ne_y
                with hs_xy | hs_yx
              · exact disjoint_left.mp hdisj_xy hs_xy hs_W
              · exact disjoint_left.mp hdisj_ab_W (hsub_yx hs_yx) hs_W
          rw [disjoint_left]
          intro z hz_ab hz_W'
          rcases hW'_sub hz_W' with hz_W | (rfl | rfl)
          · exact disjoint_left.mp hdisj_ab_W hz_ab hz_W
          · exact hboth_not.1 hz_ab
          · exact hboth_not.2 hz_ab
        rcases hvalid.2.2.2 R₀ hR₀_in P₀_left Q' P₀_right s₀ t₀ x' y' hexc₀ with hd1 | hd2
        · exact Or.inl (h_empty_W' hexc₀ hd1)
        · exact Or.inr (h_empty_W' hexc₀.symm hd2)
    have hlt_m : E(S_mid.transactionUnion P_set').ncard < m_min := by
      change E(S_mid.transactionUnion P_set').ncard < Nat.find hex_B
      omega
    exact Nat.find_min hex_B hlt_m ⟨P_set', hvalid', rfl⟩
  obtain ⟨A, B, hfence⟩ := hvalid.1.1
  have hP_le_mid : ∀ P ∈ P_set, P ≤ S_mid.G := fun P hP => by
    obtain ⟨_, _, h⟩ := hfence.1.1 P hP; exact h.1.le
  exact ⟨P_set, Society.isCrookedTransaction_of_omega_eq hΩ_mid hP_le_mid hP_le_S hvalid.1,
    hvalid.2.1⟩

private theorem endMap_atPathEnds {S : Society α β} {P_set : Set (Graph α β)}
    {P : Graph α β} (hP : P ∈ P_set) {s t : Graph α β → α}
    (hends : S.IsOmegaPathWithEnds P (s P) (t P)) {f : α → α} {P_v : α → Graph α β}
    {u w : Graph α β → α}
    (hPv_eq : ∀ v ∈ S.transactionEnds P_set, v ∈ V(P) → P_v v = P)
    (hside : ∀ v ∈ S.transactionEnds P_set,
      (v = s (P_v v) ∧ f v = u (P_v v)) ∨ (v = t (P_v v) ∧ f v = w (P_v v))) :
    (s P ∈ S.transactionEnds P_set ∧ f (s P) = u P) ∧
      (t P ∈ S.transactionEnds P_set ∧ f (t P) = w P) := by
  have hs := hends.mem_transactionEnds_left S hP
  have ht := hends.mem_transactionEnds_right S hP
  constructor
  · refine ⟨hs, ?_⟩
    have hor := hside (s P) hs
    rw [hPv_eq _ hs hends.1.left_mem] at hor
    rcases hor with h | h
    · exact h.2
    · exact (hends.2.1 h.1).elim
  · refine ⟨ht, ?_⟩
    have hor := hside (t P) ht
    rw [hPv_eq _ ht hends.1.right_mem] at hor
    rcases hor with h | h
    · exact (hends.2.1 h.1.symm).elim
    · exact h.2

private theorem disjointEndSegments {S : Society α β} {P_set : Set (Graph α β)}
    {A B : Set α} (hfence : S.IsFenceFor P_set A B)
    {s t : Graph α β → α} {L R : Graph α β → Graph α β}
    (hdisj_LR : ∀ P ∈ P_set, Disjoint V(L P) V(R P))
    {P_v T_v : α → Graph α β} {W : Set α}
    (h_end : ∀ v ∈ W, P_v v ∈ P_set ∧
      ((v = s (P_v v) ∧ T_v v = L (P_v v)) ∨ (v = t (P_v v) ∧ T_v v = R (P_v v))) ∧
        T_v v ≤ P_v v)
    {v₁ v₂ : α} (hv₁ : v₁ ∈ W) (hv₂ : v₂ ∈ W) (hne : v₁ ≠ v₂) :
    Disjoint V(T_v v₁) V(T_v v₂) := by
  classical
  obtain ⟨hP₁, hor₁, hT₁_le⟩ := h_end v₁ hv₁
  obtain ⟨hP₂, hor₂, hT₂_le⟩ := h_end v₂ hv₂
  by_cases hP_eq : P_v v₁ = P_v v₂
  · rw [hP_eq] at hor₁
    have hdLR := hdisj_LR (P_v v₂) hP₂
    rcases hor₁ with ⟨hv₁_s, hT₁_L⟩ | ⟨hv₁_t, hT₁_R⟩ <;>
      rcases hor₂ with ⟨hv₂_s, hT₂_L⟩ | ⟨hv₂_t, hT₂_R⟩
    · exact (hne (hv₁_s.trans hv₂_s.symm)).elim
    · rw [hT₁_L, hT₂_R]; exact hdLR
    · rw [hT₁_R, hT₂_L]; exact hdLR.symm
    · exact (hne (hv₁_t.trans hv₂_t.symm)).elim
  · exact (hfence.1.2 hP₁ hP₂ hP_eq).mono hT₁_le.vertexSet_mono hT₂_le.vertexSet_mono

private theorem transportCrossingThroughRural {N : Neighborhood α β} (hrural : N.IsRural)
    {W : Set α} (hbar : W ⊆ N.Ω.bar) {f : α → α} {T : α → Graph α β}
    (hpath : ∀ v ∈ W, IsGraphPathWithEnds N.G (T v) v (f v) ∧ f v ∈ N.Ω₀.bar)
    (hdisj : ∀ v₁ ∈ W, ∀ v₂ ∈ W, v₁ ≠ v₂ → Disjoint V(T v₁) V(T v₂))
    {v₁ v₂ v₃ v₄ : α} (hv₁ : v₁ ∈ W) (hv₃ : v₃ ∈ W) (hv₂ : v₂ ∈ W) (hv₄ : v₄ ∈ W) :
    N.Ω.Crosses v₁ v₃ v₂ v₄ ↔ N.Ω₀.Crosses (f v₁) (f v₃) (f v₂) (f v₄) := by
  classical
  have hnot_eq : ∀ {Ω : CyclicPerm α} {a b c d : α}, Ω.Crosses a b c d →
      a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by
    intro Ω a b c d h
    rcases h with h | h
    · obtain ⟨h12, h13, h14, h23, h24, h34, _⟩ := Ω.isClockwise4_iff.mp h
      exact ⟨h13, h12, h14, h23.symm, h34, h24⟩
    · obtain ⟨h12, h13, h14, h23, h24, h34, _⟩ := Ω.isClockwise4_iff.mp h
      exact ⟨h24.symm, h34.symm, h14.symm, h23, h12.symm, h13.symm⟩
  by_cases hdist : v₁ ≠ v₂ ∧ v₁ ≠ v₃ ∧ v₁ ≠ v₄ ∧ v₂ ≠ v₃ ∧ v₂ ≠ v₄ ∧ v₃ ≠ v₄
  · rcases hdist with ⟨h12, h13, h14, h23, h24, h34⟩
    exact crosses_outer_iff_crosses_inner_of_disjoint_paths hrural
      (hpath v₁ hv₁).1 (hbar hv₁) (hpath v₁ hv₁).2
      (hpath v₂ hv₂).1 (hbar hv₂) (hpath v₂ hv₂).2
      (hpath v₃ hv₃).1 (hbar hv₃) (hpath v₃ hv₃).2
      (hpath v₄ hv₄).1 (hbar hv₄) (hpath v₄ hv₄).2
      (hdisj v₁ hv₁ v₂ hv₂ h12) (hdisj v₁ hv₁ v₃ hv₃ h13) (hdisj v₁ hv₁ v₄ hv₄ h14)
      (hdisj v₂ hv₂ v₃ hv₃ h23) (hdisj v₂ hv₂ v₄ hv₄ h24) (hdisj v₃ hv₃ v₄ hv₄ h34)
  · refine ⟨fun hcr => ?_, fun hcr' => ?_⟩
    · obtain ⟨h13, h12, h14, h23, h34, h24⟩ := hnot_eq hcr
      exact (hdist ⟨h12, h13, h14, h23.symm, h24, h34⟩).elim
    · obtain ⟨h13, h12, h14, h23, h34, h24⟩ := hnot_eq hcr'
      refine (hdist ⟨fun h => h12 (congrArg f h), fun h => h13 (congrArg f h),
        fun h => h14 (congrArg f h), fun h => h23 (congrArg f h.symm),
        fun h => h24 (congrArg f h), fun h => h34 (congrArg f h)⟩).elim

private theorem validationAfterRestriction
    {S S_comp S_mid : Society α β} {N : Neighborhood α β} {p : ℕ}
    (hcomp : S_comp.IsComposition S N) (hrural : N.IsRural)
    {P_set₀ : Set (Graph α β)} (hcard₀ : p ≤ P_set₀.ncard)
    {M_fn : Graph α β → Graph α β} {s_fn t_fn u_fn w_fn : Graph α β → α}
    (hM_edge : ∀ P ∈ P_set₀, (∀ c e, (M_fn P).IsLink e (u_fn P) c → e ∈ E(S.G)) ∧
      (∀ c e, (M_fn P).IsLink e (w_fn P) c → e ∈ E(S.G)))
    {N_keep : Graph α β} (hN_keep_le : N_keep ≤ N.G) {V_drop : Set α}
    (hN_edges : ∀ e ∈ E(N_keep), ∀ v ∈ V_drop, ¬ N.G.Inc e v)
    (hM_ends_mid : ∀ P ∈ P_set₀, S_mid.IsOmegaPathWithEnds (M_fn P) (u_fn P) (w_fn P))
    {f_v : α → α} {T_v : α → Graph α β}
    (h_end : ∀ v ∈ S_comp.transactionEnds P_set₀, f_v v ∈ S.Ω.bar ∧
      IsGraphPathWithEnds N.G (T_v v) v (f_v v) ∧ V(T_v v) ⊆ V_drop)
    (hfv_s : ∀ P ∈ P_set₀, s_fn P ∈ S_comp.transactionEnds P_set₀ ∧ f_v (s_fn P) = u_fn P)
    (hfv_t : ∀ P ∈ P_set₀, t_fn P ∈ S_comp.transactionEnds P_set₀ ∧ f_v (t_fn P) = w_fn P)
    (hcr₁ : S_mid.IsCrookedTransaction (M_fn '' P_set₀))
    (hcard₁_eq : (M_fn '' P_set₀).ncard = P_set₀.ncard) :
    IsValidStepBConfig S S_mid N_keep p (M_fn '' P_set₀) := by
  classical
  let W₀ := S_comp.transactionEnds P_set₀
  let P_set₁ := M_fn '' P_set₀
  refine ⟨hcr₁, hcard₁_eq ▸ hcard₀, ?_, ?_⟩
  · rintro _ ⟨P, hP, rfl⟩ s t c e hM_st hlink
    obtain ⟨hfu, hfw⟩ := hM_edge P hP
    rcases (hM_ends_mid P hP).ends_eq S_mid hM_st with ⟨rfl, _⟩ | ⟨rfl, _⟩
    · exact hfu c e hlink
    · exact hfw c e hlink
  · rintro _ ⟨P, hP, rfl⟩ P_left Q P_right s t x y hexc
    obtain ⟨hM_st, _, _, _, hQ_N, _, hp_Q, _, hxy, hx_bar, hy_bar, _⟩ := hexc
    have hQ_disj_drop : Disjoint V(Q) V_drop := by
      rw [disjoint_left]
      intro v hvQ hv_drop
      obtain ⟨e, heQ, z, hvzQ⟩ := hp_Q.exists_inc_of_mem_of_ne hxy hvQ
      have he_keep : e ∈ E(N_keep) := hQ_N.edgeSet_mono heQ
      exact hN_edges e he_keep v hv_drop ⟨z, hvzQ.mono (hQ_N.trans hN_keep_le)⟩
    have hQ_path_N : IsGraphPathWithEnds N.G Q x y :=
      (hp_Q.mono hM_st.1.le).of_le (hQ_N.trans hN_keep_le)
    have hW₁_sub : S_mid.transactionEnds P_set₁ ⊆ f_v '' W₀ := by
      rintro z ⟨_, ⟨P₀, hP₀, rfl⟩, d, hM₀_zd⟩
      rcases (hM_ends_mid P₀ hP₀).ends_eq S_mid hM₀_zd with ⟨rfl, _⟩ | ⟨rfl, _⟩
      · exact ⟨s_fn P₀, (hfv_s P₀ hP₀).1, (hfv_s P₀ hP₀).2⟩
      · exact ⟨t_fn P₀, (hfv_t P₀ hP₀).1, (hfv_t P₀ hP₀).2⟩
    by_contra hnot_or
    push Not at hnot_or
    rw [not_disjoint_iff_nonempty_inter, not_disjoint_iff_nonempty_inter] at hnot_or
    rcases hnot_or with ⟨⟨z₁, hz₁_xy, hz₁_W₁⟩, ⟨z₂, hz₂_yx, hz₂_W₁⟩⟩
    rcases hW₁_sub hz₁_W₁ with ⟨v₁, hv₁_W₀, rfl⟩
    rcases hW₁_sub hz₂_W₁ with ⟨v₂, hv₂_W₀, rfl⟩
    have hbar₀ : W₀ ⊆ N.Ω.bar := hcomp.2.1 ▸ S_comp.transactionEnds_subset_bar P_set₀
    have h1 := h_end v₁ hv₁_W₀
    have h2 := h_end v₂ hv₂_W₀
    have hcr_inner : N.Ω₀.Crosses x y (f_v v₁) (f_v v₂) := by
      rw [hcomp.2.2.1]
      exact S.Ω.crosses_iff_interval.mpr (Or.inl ⟨hz₁_xy, hz₂_yx⟩)
    exact not_crosses_inner_of_disjoint_paths_to_outer hrural
      hQ_path_N (hcomp.2.2.1.symm ▸ hx_bar) (hcomp.2.2.1.symm ▸ hy_bar)
      h1.2.1 (hbar₀ hv₁_W₀) (hcomp.2.2.1.symm ▸ h1.1)
      h2.2.1 (hbar₀ hv₂_W₀) (hcomp.2.2.1.symm ▸ h2.1)
      (hQ_disj_drop.mono_right h1.2.2)
      (hQ_disj_drop.mono_right h2.2.2)
      hcr_inner

/-- **Graph Minors IX, (9.1)** (pages 62–63):
"If the composition of a society $(G, \Omega)$ with some rural neighborhood has a crooked
transaction of cardinality $\ge p$, then so does $(G, \Omega)$." -/
theorem theorem_9_1_proof
    {S S_comp : Society α β} {N : Neighborhood α β} {p : ℕ}
    (hcomp : S_comp.IsComposition S N) (hrural : N.IsRural)
    {P_set₀ : Set (Graph α β)}
    (hcrooked₀ : S_comp.IsCrookedTransaction P_set₀) (hcard₀ : p ≤ P_set₀.ncard) :
    ∃ P_set : Set (Graph α β), S.IsCrookedTransaction P_set ∧ p ≤ P_set.ncard := by
  classical
  rcases P_set₀.eq_empty_or_nonempty with rfl | ⟨P_init, hP_init⟩
  · refine ⟨∅, ⟨⟨S.Ω.bar, ∅, ⟨fun _ h => h.elim, fun _ h => h.elim⟩,
      ⟨Subset.rfl, empty_subset _, disjoint_empty _, union_empty _,
        fun _ _ _ _ _ _ hb => hb.elim⟩,
      fun _ h => h.elim⟩, fun _ h => h.elim⟩, hcard₀⟩
  obtain ⟨A₀, B₀, hfence₀⟩ := hcrooked₀.1
  obtain ⟨s_init, _, _, _, _⟩ := hfence₀.2.2 P_init hP_init
  have hnot_le₀ : ∀ P ∈ P_set₀, ¬ P ≤ N.G :=
    forall_not_le_right_of_isCrookedTransaction hcomp hrural hcrooked₀
  have hex_split : ∀ P : Graph α β,
      ∃ s t u w : α, ∃ L_P M_P R_P : Graph α β, P ∈ P_set₀ →
        S_comp.IsOmegaPathWithEnds P s t ∧
        u ∈ S.Ω.bar ∧ w ∈ S.Ω.bar ∧ u ≠ w ∧
        L_P ≤ P ∧ M_P ≤ P ∧ R_P ≤ P ∧
        IsGraphPathWithEnds N.G L_P s u ∧
        IsGraphPathWithEnds S_comp.G M_P u w ∧
        IsGraphPathWithEnds N.G R_P t w ∧
        V(L_P) ∩ V(M_P) = {u} ∧
        V(R_P) ∩ V(M_P) = {w} ∧
        Disjoint V(L_P) V(R_P) ∧
        (∀ c e, M_P.IsLink e u c → e ∈ E(S.G)) ∧
        (∀ c e, M_P.IsLink e w c → e ∈ E(S.G)) := by
    intro P
    by_cases hP : P ∈ P_set₀
    · obtain ⟨s, _, t, _, hP_ends⟩ := hfence₀.2.2 P hP
      obtain ⟨u, hu, w, hw, huw, L_P, M_P, R_P, hL, hM, hR, hpL, hpM, hpR, hiL, hiR, hdLR, hfu,
        hfw⟩ :=
        exists_middle_subpath_in_composition hcomp hP_ends (hnot_le₀ P hP)
      exact ⟨s, t, u, w, L_P, M_P, R_P, fun _ =>
        ⟨hP_ends, hu, hw, huw, hL, hM, hR, hpL, hpM, hpR, hiL, hiR, hdLR, hfu, hfw⟩⟩
    · exact ⟨s_init, s_init, s_init, s_init, P_init, P_init, P_init, fun h => (hP h).elim⟩
  choose s_fn t_fn u_fn w_fn L_fn M_fn R_fn hsplit using hex_split
  let V_drop : Set α := ⋃ P ∈ P_set₀, (V(L_fn P) ∪ V(R_fn P))
  let E_keep : Set β := {e ∈ E(N.G) | ∀ v ∈ V_drop, ¬ N.G.Inc e v}
  let N_keep : Graph α β := N.G.restrict E_keep
  let G_mid : Graph α β := S_comp.G.restrict (E(S.G) ∪ E_keep)
  have hMid_le : G_mid ≤ S_comp.G := restrict_le
  have hbar_mid : S.Ω.bar ⊆ V(G_mid) := by
    rw [vertexSet_restrict]
    exact S.bar_subset.trans hcomp.1.1.1.vertexSet_mono
  have hfinV_mid : V(G_mid).Finite := by
    rw [vertexSet_restrict]; exact S_comp.finite_V
  have hfinE_mid : E(G_mid).Finite :=
    S_comp.finite_E.subset hMid_le.edgeSet_mono
  let S_mid : Society α β := ⟨G_mid, S.Ω, hfinV_mid, hfinE_mid, hbar_mid⟩
  have hSG_le_mid : S.G ≤ S_mid.G := by
    rw [(Compatible.of_le_le hcomp.1.1.1 hMid_le).le_iff]
    refine ⟨?_, ?_⟩
    · rw [vertexSet_restrict]; exact hcomp.1.1.1.vertexSet_mono
    · rw [edgeSet_restrict]; exact subset_inter hcomp.1.1.1.edgeSet_mono subset_union_left
  have hN_keep_le : N_keep ≤ N.G := restrict_le
  have hN_le_comp : N_keep ≤ S_comp.G := hN_keep_le.trans hcomp.1.1.2.1
  have hN_le_mid : N_keep ≤ S_mid.G := by
    rw [(Compatible.of_le_le hN_le_comp hMid_le).le_iff]
    refine ⟨?_, ?_⟩
    · rw [vertexSet_restrict, vertexSet_restrict]; exact hcomp.1.1.2.1.vertexSet_mono
    · rw [edgeSet_restrict, edgeSet_restrict]
      exact subset_inter (inter_subset_left.trans hcomp.1.1.2.1.edgeSet_mono)
        (inter_subset_right.trans subset_union_right)
  have hE_mid : E(S_mid.G) ⊆ E(S.G) ∪ E(N_keep) := by
    rintro e ⟨_, heS | he_keep⟩
    · exact Or.inl heS
    · exact Or.inr ⟨he_keep.1, he_keep⟩
  have hdisj_SN : Disjoint E(S.G) E(N_keep) :=
    hcomp.1.1.2.2.2.2.mono_right hN_keep_le.edgeSet_mono
  have hV_inter : V(S.G) ∩ V(N_keep) ⊆ S.Ω.bar := by
    rw [vertexSet_restrict, hcomp.2.2.2]
  have hM_ends_mid : ∀ P ∈ P_set₀,
      S_mid.IsOmegaPathWithEnds (M_fn P) (u_fn P) (w_fn P) := by
    intro P hP
    obtain ⟨hP_ends, hu, hw, huw, hL, hM, hR, _, hpM, _, hiL, hiR, _, hfu, hfw⟩ := hsplit P hP
    have hM_le_mid : M_fn P ≤ S_mid.G := by
      rw [(Compatible.of_le_le hpM.le hMid_le).le_iff]
      refine ⟨by rw [vertexSet_restrict]; exact hpM.le.vertexSet_mono, fun e heM => ?_⟩
      have he_comp : e ∈ E(S_comp.G) := hpM.le.edgeSet_mono heM
      refine ⟨he_comp, ?_⟩
      by_cases heS : e ∈ E(S.G)
      · exact Or.inl heS
      · have heN : e ∈ E(N.G) := by
          rw [← hcomp.1.1.2.2.2.1] at he_comp; exact he_comp.resolve_left heS
        refine Or.inr ⟨heN, fun v hv_drop hinc_N => ?_⟩
        obtain ⟨a, b, habM⟩ := (M_fn P).exists_isLink_of_mem_edgeSet heM
        rcases hinc_N with ⟨w₀, hvw₀N⟩
        have hinc_M : (M_fn P).Inc e v := by
          rcases (hvw₀N.mono hcomp.1.1.2.1).left_eq_or_eq (habM.mono hpM.le) with rfl | rfl
          · exact ⟨b, habM⟩
          · exact ⟨a, habM.symm⟩
        rcases hinc_M with ⟨c, hlink_M⟩
        rcases mem_iUnion₂.mp hv_drop with ⟨P₀, hP₀, hv_LR⟩
        have hP₀_eq : P₀ = P := by
          by_contra hne
          have hvP : v ∈ V(P) := hM.vertexSet_mono hlink_M.left_mem
          have hvP₀ : v ∈ V(P₀) := by
            rcases hv_LR with hvL | hvR
            · exact (hsplit P₀ hP₀).2.2.2.2.1.vertexSet_mono hvL
            · exact (hsplit P₀ hP₀).2.2.2.2.2.2.1.vertexSet_mono hvR
          exact disjoint_left.mp (hfence₀.1.2 hP₀ hP hne) hvP₀ hvP
        rw [hP₀_eq] at hv_LR
        rcases hv_LR with hvL | hvR
        · have hv_u : v = u_fn P := by
            have hv_in : v ∈ V(L_fn P) ∩ V(M_fn P) := ⟨hvL, hlink_M.left_mem⟩
            rwa [hiL, mem_singleton_iff] at hv_in
          exact heS (hfu c e (hv_u ▸ hlink_M))
        · have hv_w : v = w_fn P := by
            have hv_in : v ∈ V(R_fn P) ∩ V(M_fn P) := ⟨hvR, hlink_M.left_mem⟩
            rwa [hiR, mem_singleton_iff] at hv_in
          exact heS (hfw c e (hv_w ▸ hlink_M))
    exact ⟨hpM.of_le hM_le_mid, huw, hu, hw⟩
  let W₀ := S_comp.transactionEnds P_set₀
  have hex_end : ∀ v : α,
      ∃ P : Graph α β, ∃ z : α, ∃ T : Graph α β, v ∈ W₀ →
        P ∈ P_set₀ ∧ z ∈ S.Ω.bar ∧
        ((v = s_fn P ∧ z = u_fn P ∧ T = L_fn P) ∨ (v = t_fn P ∧ z = w_fn P ∧ T = R_fn P)) ∧
        IsGraphPathWithEnds N.G T v z ∧
        T ≤ P ∧
        V(T) ⊆ V_drop := by
    intro v
    by_cases hv : v ∈ W₀
    · rcases hv with ⟨P, hP, d, hP_vd⟩
      obtain ⟨hP_ends, hu, hw, _, hL, _, hR, hpL, _, hpR, _⟩ := hsplit P hP
      rcases hP_ends.ends_eq S_comp hP_vd with ⟨rfl, _⟩ | ⟨rfl, _⟩
      · refine ⟨P, u_fn P, L_fn P, fun _ => ⟨hP, hu, Or.inl ⟨rfl, rfl, rfl⟩, hpL, hL,
          fun x hx => ?_⟩⟩
        exact mem_iUnion₂.mpr ⟨P, hP, Or.inl hx⟩
      · refine ⟨P, w_fn P, R_fn P, fun _ => ⟨hP, hw, Or.inr ⟨rfl, rfl, rfl⟩, hpR, hR,
          fun x hx => ?_⟩⟩
        exact mem_iUnion₂.mpr ⟨P, hP, Or.inr hx⟩
    · exact ⟨P_init, s_init, P_init, fun h => (hv h).elim⟩
  choose P_v f_v T_v h_end using hex_end
  have hPv_eq : ∀ P ∈ P_set₀, ∀ v ∈ W₀, v ∈ V(P) → P_v v = P := by
    intro P hP v hvW₀ hvP
    obtain ⟨hPv_in, _, _, hpT, hT_le, _⟩ := h_end v hvW₀
    by_contra hne
    exact disjoint_left.mp (hfence₀.1.2 hPv_in hP hne) (hT_le.vertexSet_mono hpT.left_mem) hvP
  have hfv (P : Graph α β) (hP : P ∈ P_set₀) :=
    endMap_atPathEnds hP (hsplit P hP).1 (hPv_eq P hP) fun v hv =>
      (h_end v hv).2.2.1.imp (fun h => ⟨h.1, h.2.1⟩) (fun h => ⟨h.1, h.2.1⟩)
  have hfv_s := fun P hP => (hfv P hP).1
  have hfv_t := fun P hP => (hfv P hP).2
  have hTv_disj : ∀ v₁ ∈ W₀, ∀ v₂ ∈ W₀, v₁ ≠ v₂ → Disjoint V(T_v v₁) V(T_v v₂) := by
    intro v₁ hv₁ v₂ hv₂ hne
    refine disjointEndSegments hfence₀ (s := s_fn) (t := t_fn) (L := L_fn) (R := R_fn)
      (P_v := P_v) ?_ ?_ hv₁ hv₂ hne
    · intro P hP
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hdLR, _⟩ := hsplit P hP
      exact hdLR
    · intro v hv
      obtain ⟨hP, _, hside, _, hle, _⟩ := h_end v hv
      refine ⟨hP, ?_, hle⟩
      rcases hside with ⟨hs, _, hL⟩ | ⟨ht, _, hR⟩
      · exact Or.inl ⟨hs, hL⟩
      · exact Or.inr ⟨ht, hR⟩
  have hf_ends : ∀ P ∈ P_set₀, ∀ a b : α,
      S_comp.IsOmegaPathWithEnds P a b → S_mid.IsOmegaPathWithEnds (M_fn P) (f_v a) (f_v b) := by
    intro P hP a b hP_ab
    obtain ⟨hP_ends, _⟩ := hsplit P hP
    rcases hP_ends.ends_eq S_comp hP_ab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [(hfv_s P hP).2, (hfv_t P hP).2]
      exact hM_ends_mid P hP
    · rw [(hfv_t P hP).2, (hfv_s P hP).2]
      exact (hM_ends_mid P hP).symm S_mid
  have hf_disj : ∀ P ∈ P_set₀, ∀ Q ∈ P_set₀, P ≠ Q → Disjoint V(M_fn P) V(M_fn Q) := by
    intro P hP Q hQ hne
    exact (hfence₀.1.2 hP hQ hne).mono
      (hsplit P hP).2.2.2.2.2.1.vertexSet_mono (hsplit Q hQ).2.2.2.2.2.1.vertexSet_mono
  have hf_inj : InjOn f_v W₀ := by
    intro v₁ hv₁ v₂ hv₂ heq
    by_contra hne
    have hm₁ : f_v v₁ ∈ V(T_v v₁) := (h_end v₁ hv₁).2.2.2.1.right_mem
    have hm₂ : f_v v₂ ∈ V(T_v v₂) := (h_end v₂ hv₂).2.2.2.1.right_mem
    exact disjoint_left.mp (hTv_disj v₁ hv₁ v₂ hv₂ hne) hm₁ (heq ▸ hm₂)
  have hf_cross : ∀ v₁ ∈ W₀, ∀ v₃ ∈ W₀, ∀ v₂ ∈ W₀, ∀ v₄ ∈ W₀,
      S_comp.Ω.Crosses v₁ v₃ v₂ v₄ ↔ S_mid.Ω.Crosses (f_v v₁) (f_v v₃) (f_v v₂) (f_v v₄) := by
    intro v₁ hv₁ v₃ hv₃ v₂ hv₂ v₄ hv₄
    change S_comp.Ω.Crosses v₁ v₃ v₂ v₄ ↔ S.Ω.Crosses (f_v v₁) (f_v v₃) (f_v v₂) (f_v v₄)
    rw [← hcomp.2.1, ← hcomp.2.2.1]
    exact transportCrossingThroughRural hrural
      (hcomp.2.1 ▸ S_comp.transactionEnds_subset_bar P_set₀)
      (fun v hv => ⟨(h_end v hv).2.2.2.1, hcomp.2.2.1.symm ▸ (h_end v hv).2.1⟩)
      hTv_disj hv₁ hv₃ hv₂ hv₄
  obtain ⟨hcr₁, hcard₁_eq⟩ :=
    isCrookedTransaction_of_end_map hcrooked₀ hf_ends hf_disj hf_inj hf_cross
  let P_set₁ := M_fn '' P_set₀
  have hvalid₁ : IsValidStepBConfig S S_mid N_keep p P_set₁ := by
    refine validationAfterRestriction (T_v := T_v) hcomp hrural hcard₀ ?_ hN_keep_le
      (fun _ he => he.2.2) hM_ends_mid ?_ hfv_s hfv_t hcr₁ hcard₁_eq
    · intro P hP
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hfu, hfw⟩ := hsplit P hP
      exact ⟨hfu, hfw⟩
    · intro v hv
      obtain ⟨_, hfv, _, hpath, _, hsub⟩ := h_end v hv
      exact ⟨hfv, hpath, hsub⟩
  exact stepB_of_theorem_9_1 hrural (rfl : S_mid.Ω = S.Ω) hcomp.2.2.1 hE_mid
    hSG_le_mid hN_le_mid hN_keep_le hdisj_SN hV_inter hvalid₁

end GraphMinor.GM09
