/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM14.Section6
public import LeanPool.GraphMinor.GM14.PieceDrawing
public import LeanPool.GraphMinor.GM14.WhitneyGraph

/-!
# Graph Minors XIV – Separations of Order at Most 2 in Subdivisions of Simple 3-Connected Graphs

This file proves general 2-separation lemmas for subdivisions of simple 3-connected graphs:
- `isSubdivision_toGraph_of_spanEmbedding`: if `η.imageGraph` is a subdivision of a simple
  3-connected graph, then so is `H.toGraph`.
- `SubDataSepGeneral.sep_general`: for any `A ⊆ E(G)` with `(bdry G A).ncard ≤ 2`, `A.Nonempty`,
  and `(E(G) \ A).Nonempty` in a subdivision `G` of a simple 3-connected graph `G₀`, either `A`
  or `E(G) \ A` is the edge set of a subpath `Q` of some subdivision path `P e` (`e ∈ E(G₀)`)
  joining the two vertices of `bdry G A`.
-/

@[expose] public section

namespace GraphMinor.GM14

open Set Function Topology Metric Graph Hypergraph
open GraphMinor GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09 GraphMinor.GM10
open GraphMinor.GM11 GraphMinor.GM14.Whitney

universe u v u' v' w

/-! ## 1. Moving subdivisions between span embeddings -/

/-- If `η : SpanEmbedding H G` has `IsSubdivisionOfSimpleThreeConnected η.imageGraph`, then
`IsSubdivisionOfSimpleThreeConnected H.toGraph`. -/
theorem isSubdivision_toGraph_of_spanEmbedding {S : Type w} [TopologicalSpace S]
    {α : Type u} {β : Type v} {H : Drawing S} {G : Graph α β}
    (η : SpanEmbedding H G) (h : IsSubdivisionOfSimpleThreeConnected η.imageGraph) :
    IsSubdivisionOfSimpleThreeConnected H.toGraph := by
  obtain ⟨G₀, hsimple, hsub⟩ := h
  have h4 := hsimple.2.1
  have hV₀_ne : V(G₀).Nonempty := by
    by_contra hemp
    rw [not_nonempty_iff_eq_empty] at hemp
    rw [hemp, Set.ncard_empty] at h4
    omega
  obtain ⟨v₀, hv₀⟩ := hV₀_ne
  have hv₀_im : v₀ ∈ V(η.imageGraph) := hsub.1 hv₀
  obtain ⟨s₀, hs₀, _⟩ := η.bijOn_v.surjOn hv₀_im
  have : Nonempty S := ⟨s₀⟩
  obtain ⟨ι, _, _⟩ := η.exists_iso
  exact isSubdivision_of_iso_het ⟨G₀, hsimple, hsub⟩ (isoSymm ι)

/-! ## 2. General Separations of Order at Most 2 in a Subdivision of a Simple 3-Connected Graph -/

namespace SubDataSepGeneral

variable {α : Type u} {β : Type v}
variable {G G₀ : Graph α β} {P : β → Graph α β}

/-- Along any walk `W` from `a` to `b`, if `a ∈ verts G A` and `b ∉ verts G A`, some vertex on `W`
other than `b` belongs to `bdry G A`. -/
theorem exists_bdry_of_walk {A : Set β} {a b : α} (W : GraphWalk G a b)
    (ha : a ∈ verts G A) (hb : b ∉ verts G A) :
    ∃ z ∈ W.support, z ≠ b ∧ z ∈ bdry G A := by
  induction W with
  | nil _ => exact (hb ha).elim
  | @cons u v w g hlink rest ih =>
    by_cases hv : v ∈ verts G A
    · obtain ⟨z, hz, hzb, hbd⟩ := ih hv hb
      exact ⟨z, by simp [GraphWalk.support, hz], hzb, hbd⟩
    · have hgA : g ∉ A := fun hg => hv ⟨g, hg, u, hlink.symm⟩
      have hu_out : u ∈ verts G (E(G) \ A) := ⟨g, ⟨hlink.edge_mem, hgA⟩, v, hlink⟩
      exact ⟨u, by simp [GraphWalk.support], fun h => hb (h ▸ ha), ha, hu_out⟩

/-- Every edge of `G` incident with an internal vertex `x ∈ V(P e) \ V(G₀)` belongs to `E(P e)`. -/
theorem inc_mem_path_of_notMem_V₀ (h : SubData G G₀ P) {e g : β} {x : α}
    (he : e ∈ E(G₀)) (hxP : x ∈ V(P e)) (hx₀ : x ∉ V(G₀)) (hg : g ∈ E(G)) (hinc : G.Inc g x) :
    g ∈ E(P e) := by
  rw [h.eunion] at hg
  obtain ⟨f, hf, hgf⟩ := mem_iUnion₂.mp hg
  by_cases hfe : f = e
  · exact hfe ▸ hgf
  · obtain ⟨_, _, -, hp, -, -⟩ := h.path f hf
    obtain ⟨y, hy⟩ := hinc
    have hxPf : x ∈ V(P f) := ((hp.le.isLink_iff hgf).mpr hy).left_mem
    exact (hx₀ ((h.disj e he f hf (Ne.symm hfe)).2 ⟨hxP, hxPf⟩)).elim

/-- Every vertex in `bdry G A` belongs to `V(G)`. -/
theorem bdry_subset_V (A : Set β) : bdry G A ⊆ V(G) := by
  rintro x ⟨_, g, ⟨hg, _⟩, y, hlink⟩
  exact hlink.left_mem

/-- For any `SubData G G₀ P`, `E(G₀)`, `V(G)`, and `bdry G A` are finite. -/
theorem finite_V (h : SubData G G₀ P) : V(G).Finite := by
  classical
  have hfinV₀ : V(G₀).Finite := h.finite_V₀
  have : Finite V(G₀) := hfinV₀.to_subtype
  have hfinE₀ : E(G₀).Finite := by
    have hex : ∀ e : E(G₀), ∃ u v : V(G₀), G₀.IsLink e.1 u.1 v.1 := by
      intro e
      obtain ⟨u, v, hl, -⟩ := h.path e.1 e.2
      exact ⟨⟨u, hl.left_mem⟩, ⟨v, hl.right_mem⟩, hl⟩
    choose u v hlink using hex
    have hinj : Function.Injective (fun e : E(G₀) => (u e, v e)) := by
      intro e₁ e₂ heq
      have h1 : (u e₁).1 = (u e₂).1 := congrArg (fun p => p.1.1) heq
      have h2 : (v e₁).1 = (v e₂).1 := congrArg (fun p => p.2.1) heq
      apply Subtype.ext
      exact h.simple.1.2 e₁.1 e₁.2 e₂.1 e₂.2 (u e₁).1 (v e₁).1 (hlink e₁)
        (h1 ▸ h2 ▸ hlink e₂)
    exact Finite.of_injective _ hinj
  rw [h.vunion]
  refine hfinV₀.union (hfinE₀.biUnion fun e he => ?_)
  obtain ⟨_, _, -, ⟨_, W, _, hV, _⟩, -⟩ := h.path e he
  rw [hV]
  exact W.support.toFinset.finite_toSet.subset fun x hx => List.mem_toFinset.mpr hx

theorem finite_bdry (h : SubData G G₀ P) (A : Set β) : (bdry G A).Finite :=
  (finite_V h).subset (bdry_subset_V A)

/-- If `x ∈ V(G)` is not in `V(P e)`, no edge of `E(P e)` is incident with `x` in `G`. -/
theorem not_inc_of_notMem_path (h : SubData G G₀ P) {e g : β} {x : α}
    (he : e ∈ E(G₀)) (hx : x ∉ V(P e)) (hg : g ∈ E(P e)) : ¬ G.Inc g x := by
  obtain ⟨_, _, -, hp, -, -⟩ := h.path e he
  rintro ⟨y, hy⟩
  exact hx (((hp.le.isLink_iff hg).mpr hy).left_mem)

/-- In a simple 3-connected graph `G₀`, for any edge `e₁ ∈ E(G₀)` there exist three distinct edges
in `E(G₀) \ {e₁}`. -/
theorem exists_three_edges_outside (h : SubData G G₀ P) {e₁ : β} (he₁ : e₁ ∈ E(G₀)) :
    ∃ a₁ a₂ a₃ : β, a₁ ∈ E(G₀) \ {e₁} ∧ a₂ ∈ E(G₀) \ {e₁} ∧ a₃ ∈ E(G₀) \ {e₁} ∧
      a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃ := by
  obtain ⟨u₁, v₁, hl₁, -, -, -⟩ := h.path e₁ he₁
  have h4 := h.simple.2.1
  have hne : (V(G₀) \ {u₁, v₁}).Nonempty := by
    by_contra hemp
    have hsub : V(G₀) ⊆ {u₁, v₁} := fun x hx => by
      by_contra hx_not
      exact hemp ⟨x, hx, hx_not⟩
    have hle := (Set.ncard_le_ncard hsub (Set.toFinite _)).trans (Set.ncard_insert_le u₁ {v₁})
    rw [Set.ncard_singleton] at hle
    omega
  obtain ⟨x, hxV₀, hx_not⟩ := hne
  obtain ⟨a₁, a₂, a₃, h12, h13, h23, hi₁, hi₂, hi₃⟩ :=
    IsSimpleThreeConnected.exists_three_edges h.simple hxV₀
  have hnot_e₁ : ∀ {a : β}, G₀.Inc a x → a ∈ E(G₀) \ {e₁} := by
    rintro a ⟨y, hlink⟩
    refine ⟨hlink.edge_mem, ?_⟩
    rintro rfl
    rcases G₀.eq_or_eq_of_isLink_of_isLink hlink hl₁ with rfl | rfl
    · exact hx_not (Or.inl rfl)
    · exact hx_not (Or.inr rfl)
  exact ⟨a₁, a₂, a₃, hnot_e₁ hi₁, hnot_e₁ hi₂, hnot_e₁ hi₃, h12, h13, h23⟩

/-- It is impossible to have a set `B₁ ⊆ E(G)` disjoint from `E(P e₁)` (`e₁ ∈ E(G₀)`) such that
`B₁.Nonempty`, `(E(G) \ (B₁ ∪ E(P e₁))).Nonempty`, and both `B₁` and `B₁ ∪ E(P e₁)` have boundary
in `V(G₀)` of size `≤ 2`. -/
theorem not_both_sep_of_union_path (h : SubData G G₀ P) {e₁ : β} (he₁ : e₁ ∈ E(G₀))
    {B₁ : Set β} (hB₁ : B₁ ⊆ E(G)) (hdisj : Disjoint B₁ E(P e₁))
    (hne₁ : B₁.Nonempty) (hne₂ : (E(G) \ (B₁ ∪ E(P e₁))).Nonempty)
    (hbd₁ : bdry G B₁ ⊆ V(G₀)) (hc₁ : (bdry G B₁).ncard ≤ 2)
    (hbd₂ : bdry G (B₁ ∪ E(P e₁)) ⊆ V(G₀)) (hc₂ : (bdry G (B₁ ∪ E(P e₁))).ncard ≤ 2) :
    False := by
  have hPe₁_sub : E(P e₁) ⊆ E(G) := by
    intro g hg
    rw [h.eunion]
    exact mem_iUnion₂.mpr ⟨e₁, he₁, hg⟩
  obtain ⟨_, _, -, -, hPe₁_ne, -⟩ := h.path e₁ he₁
  have hne₁' : (E(G) \ B₁).Nonempty := by
    obtain ⟨g, hg⟩ := hPe₁_ne
    exact ⟨g, hPe₁_sub hg, disjoint_right.mp hdisj hg⟩
  have hB₂_sub : B₁ ∪ E(P e₁) ⊆ E(G) := union_subset hB₁ hPe₁_sub
  have hne₂_left : (B₁ ∪ E(P e₁)).Nonempty := hne₁.mono subset_union_left
  obtain ⟨f₁, hf₁, hsep₁⟩ := h.sep hB₁ hbd₁ hc₁ hne₁ hne₁'
  obtain ⟨f₂, hf₂, hsep₂⟩ := h.sep hB₂_sub hbd₂ hc₂ hne₂_left hne₂
  have hB₁_eq : B₁ = E(P f₁) := by
    rcases hsep₁ with h1 | h1
    · exact h1
    · exfalso
      obtain ⟨g₁, hg₁⟩ := hPe₁_ne
      have hg₁_in : g₁ ∈ E(P f₁) := h1 ▸ ⟨hPe₁_sub hg₁, disjoint_right.mp hdisj hg₁⟩
      have hf₁_eq : f₁ = e₁ := by
        by_contra hne
        exact disjoint_left.mp (h.disj f₁ hf₁ e₁ he₁ hne).1 hg₁_in hg₁
      subst hf₁_eq
      obtain ⟨g₂, hg₂E, hg₂_not⟩ := hne₂
      have hg₂_in : g₂ ∈ E(P f₁) := h1 ▸ ⟨hg₂E, fun h => hg₂_not (Or.inl h)⟩
      exact hg₂_not (Or.inr hg₂_in)
  have hB₂_compl_eq : E(G) \ (B₁ ∪ E(P e₁)) = E(P f₂) := by
    rcases hsep₂ with h2 | h2
    · exfalso
      obtain ⟨g₁, hg₁⟩ := hPe₁_ne
      have hg₁_in : g₁ ∈ E(P f₂) := h2 ▸ Or.inr hg₁
      have hf₂_eq : f₂ = e₁ := by
        by_contra hne
        exact disjoint_left.mp (h.disj f₂ hf₂ e₁ he₁ hne).1 hg₁_in hg₁
      subst hf₂_eq
      obtain ⟨g₀, hg₀⟩ := hne₁
      have hg₀_in : g₀ ∈ E(P f₂) := h2 ▸ Or.inl hg₀
      exact disjoint_left.mp hdisj hg₀ hg₀_in
    · exact h2
  obtain ⟨a₁, a₂, a₃, ha₁, ha₂, ha₃, h12, h13, h23⟩ := exists_three_edges_outside h he₁
  have hmem_f : ∀ a ∈ E(G₀) \ {e₁}, a = f₁ ∨ a = f₂ := by
    rintro a ⟨ha, ha_ne⟩
    obtain ⟨_, _, -, -, ⟨g, hg⟩, -⟩ := h.path a ha
    have hgE : g ∈ E(G) := by
      rw [h.eunion]
      exact mem_iUnion₂.mpr ⟨a, ha, hg⟩
    have hg_not_e₁ : g ∉ E(P e₁) :=
      disjoint_left.mp (h.disj a ha e₁ he₁ ha_ne).1 hg
    by_cases hgB₁ : g ∈ B₁
    · left
      rw [hB₁_eq] at hgB₁
      by_contra hne
      exact disjoint_left.mp (h.disj a ha f₁ hf₁ hne).1 hg hgB₁
    · right
      have hg_in : g ∈ E(P f₂) := hB₂_compl_eq ▸ ⟨hgE, not_or.mpr ⟨hgB₁, hg_not_e₁⟩⟩
      by_contra hne
      exact disjoint_left.mp (h.disj a ha f₂ hf₂ hne).1 hg hg_in
  rcases hmem_f a₁ ha₁ with h1 | h1 <;>
    rcases hmem_f a₂ ha₂ with h2 | h2 <;>
    rcases hmem_f a₃ ha₃ with h3 | h3
  · exact h12 (h1.trans h2.symm)
  · exact h12 (h1.trans h2.symm)
  · exact h13 (h1.trans h3.symm)
  · exact h23 (h2.trans h3.symm)
  · exact h23 (h2.trans h3.symm)
  · exact h13 (h1.trans h3.symm)
  · exact h12 (h1.trans h2.symm)
  · exact h12 (h1.trans h2.symm)

/-- If `e ∈ E(G₀)` has ends `u, v` and `bdry G A ∩ (V(P e) \ V(G₀)) = {w}`, then removing `E(P e)`
from `A` and adding `E(P e)` to `A` move `w` to `{u, v}` without increasing the boundary size. -/
theorem move_internal_bdry (h : SubData G G₀ P) {A : Set β} (hA : A ⊆ E(G))
    {e : β} (he : e ∈ E(G₀)) {w : α} (hw : bdry G A ∩ (V(P e) \ V(G₀)) = {w}) :
    ∃ u v : α, G₀.IsLink e u v ∧
      bdry G (A \ E(P e)) ⊆ (bdry G A \ (V(P e) \ V(G₀))) ∪ {u} ∧
      bdry G (A ∪ E(P e)) ⊆ (bdry G A \ (V(P e) \ V(G₀))) ∪ {v} := by
  obtain ⟨u, v, hl, ⟨hle, W, hs, hV, hE⟩, _, hcap⟩ := h.path e he
  have hw_mem : w ∈ bdry G A ∧ w ∈ V(P e) \ V(G₀) := by
    have : w ∈ bdry G A ∩ (V(P e) \ V(G₀)) := hw.symm ▸ mem_singleton w
    exact this
  have hwP : w ∈ V(P e) := hw_mem.2.1
  have hwW : w ∈ W.support := by rwa [hV] at hwP
  obtain ⟨W₁, W₂, hW_eq⟩ := W.exists_append_of_mem hwW
  have hs' : (W₁.append W₂).IsSimple := hW_eq ▸ hs
  have hsp := GM09.isSimple_of_append hs'
  have hnd_V : (W₁.support ++ W₂.support.tail).Nodup := by
    have h1 : (W₁.append W₂).support.Nodup := hs'
    rwa [GraphWalk.support_append] at h1
  have hd_V := List.nodup_append.mp hnd_V
  have hmemE : ∀ {g : β}, g ∈ W.edges → g ∈ E(G) := fun {g} hg =>
    hle.edgeSet_mono (by rw [hE]; exact hg)
  have hincG : ∀ {g x}, (P e).Inc g x → G.Inc g x := fun ⟨y, hy⟩ => ⟨y, hy.mono hle⟩
  have hW₁_pure : ∀ e₁ ∈ W₁.edges, ∀ e₂ ∈ W₁.edges, e₁ ∈ A ↔ e₂ ∈ A := by
    refine walk_pure W₁ hsp.1 fun x hx hxu hxw e₁ he₁ e₂ he₂ hi₁ hi₂ => ?_
    have hxW : x ∈ W.support := by
      rw [hW_eq, GraphWalk.mem_support_append]
      exact Or.inl hx
    have hxv : x ≠ v := by
      rintro rfl
      have hv₂ : x ∈ W₂.support := W₂.end_mem_support
      rw [W₂.support_eq_cons] at hv₂
      rcases List.mem_cons.mp hv₂ with rfl | hv_tail
      · exact hxw rfl
      · exact hd_V.2.2 x hx x hv_tail rfl
    have hx_not_V₀ : x ∉ V(G₀) := by
      intro hx₀
      have hm : x ∈ V(P e) ∩ V(G₀) := ⟨hV ▸ hxW, hx₀⟩
      rw [hcap] at hm
      exact hm.elim hxu hxv
    have hx_not_bd : x ∉ bdry G A := by
      intro hbd
      have : x ∈ bdry G A ∩ (V(P e) \ V(G₀)) := ⟨hbd, hV ▸ hxW, hx_not_V₀⟩
      rw [hw] at this
      exact hxw this
    have he₁W : e₁ ∈ W.edges := by
      rw [hW_eq, GraphWalk.edges_append]
      exact List.mem_append_left _ he₁
    have he₂W : e₂ ∈ W.edges := by
      rw [hW_eq, GraphWalk.edges_append]
      exact List.mem_append_left _ he₂
    constructor <;> intro h₁ <;> by_contra h₂
    · exact hx_not_bd ⟨⟨e₁, h₁, hincG hi₁⟩, e₂, ⟨hmemE he₂W, h₂⟩, hincG hi₂⟩
    · exact hx_not_bd ⟨⟨e₂, h₁, hincG hi₂⟩, e₁, ⟨hmemE he₁W, h₂⟩, hincG hi₁⟩
  have hW₂_pure : ∀ e₁ ∈ W₂.edges, ∀ e₂ ∈ W₂.edges, e₁ ∈ A ↔ e₂ ∈ A := by
    refine walk_pure W₂ hsp.2 fun x hx hxw hxv e₁ he₁ e₂ he₂ hi₁ hi₂ => ?_
    have hxW : x ∈ W.support := by
      rw [hW_eq, GraphWalk.mem_support_append]
      exact Or.inr hx
    have hxu : x ≠ u := by
      rintro rfl
      have hu₁ : x ∈ W₁.support := W₁.start_mem_support
      rw [W₂.support_eq_cons] at hx
      rcases List.mem_cons.mp hx with rfl | hx_tail
      · exact hxw rfl
      · exact hd_V.2.2 x hu₁ x hx_tail rfl
    have hx_not_V₀ : x ∉ V(G₀) := by
      intro hx₀
      have hm : x ∈ V(P e) ∩ V(G₀) := ⟨hV ▸ hxW, hx₀⟩
      rw [hcap] at hm
      exact hm.elim hxu hxv
    have hx_not_bd : x ∉ bdry G A := by
      intro hbd
      have : x ∈ bdry G A ∩ (V(P e) \ V(G₀)) := ⟨hbd, hV ▸ hxW, hx_not_V₀⟩
      rw [hw] at this
      exact hxw this
    have he₁W : e₁ ∈ W.edges := by
      rw [hW_eq, GraphWalk.edges_append]
      exact List.mem_append_right _ he₁
    have he₂W : e₂ ∈ W.edges := by
      rw [hW_eq, GraphWalk.edges_append]
      exact List.mem_append_right _ he₂
    constructor <;> intro h₁ <;> by_contra h₂
    · exact hx_not_bd ⟨⟨e₁, h₁, hincG hi₁⟩, e₂, ⟨hmemE he₂W, h₂⟩, hincG hi₂⟩
    · exact hx_not_bd ⟨⟨e₂, h₁, hincG hi₂⟩, e₁, ⟨hmemE he₁W, h₂⟩, hincG hi₁⟩
  have huw : u ≠ w := fun h => hw_mem.2.2 (h ▸ hl.left_mem)
  have hvw : v ≠ w := fun h => hw_mem.2.2 (h ▸ hl.right_mem)
  obtain ⟨gu, hgu₁, hiu⟩ := exists_edge_at_start W₁ huw
  obtain ⟨gv, hgv₂_rev, hiv⟩ := exists_edge_at_start W₂.reverse hvw
  have hgv₂ : gv ∈ W₂.edges := by
    rw [GraphWalk.edges_reverse] at hgv₂_rev
    exact List.mem_reverse.mp hgv₂_rev
  have hgu_Pe : gu ∈ E(P e) := by
    rw [hE, hW_eq, GraphWalk.edges_append]
    exact List.mem_append_left _ hgu₁
  have hgv_Pe : gv ∈ E(P e) := by
    rw [hE, hW_eq, GraphWalk.edges_append]
    exact List.mem_append_right _ hgv₂
  have hnot_iff : ¬ (gu ∈ A ↔ gv ∈ A) := by
    intro hiff
    obtain ⟨⟨f₁, hf₁A, hif₁⟩, f₂, ⟨hf₂E, hf₂A⟩, hif₂⟩ := hw_mem.1
    have hf₁_Pe : f₁ ∈ E(P e) :=
      inc_mem_path_of_notMem_V₀ h he hw_mem.2.1 hw_mem.2.2 (hA hf₁A) hif₁
    have hf₂_Pe : f₂ ∈ E(P e) :=
      inc_mem_path_of_notMem_V₀ h he hw_mem.2.1 hw_mem.2.2 hf₂E hif₂
    have hall : ∀ g ∈ E(P e), g ∈ A ↔ gu ∈ A := by
      intro g hg
      rw [hE, hW_eq, mem_ofPred_eq, GraphWalk.edges_append] at hg
      rcases List.mem_append.mp hg with hg₁ | hg₂
      · exact hW₁_pure g hg₁ gu hgu₁
      · exact (hW₂_pure g hg₂ gv hgv₂).trans hiff.symm
    exact hf₂A ((hall f₂ hf₂_Pe).mpr ((hall f₁ hf₁_Pe).mp hf₁A))
  have hstep : ∀ (u' v' : α) (gu' gv' : β),
      G₀.IsLink e u' v' → ({u', v'} : Set α) = {u, v} →
      gu' ∈ E(P e) → gv' ∈ E(P e) → G.Inc gu' u' → G.Inc gv' v' →
      gu' ∈ A → gv' ∉ A →
      bdry G (A \ E(P e)) ⊆ (bdry G A \ (V(P e) \ V(G₀))) ∪ {u'} ∧
      bdry G (A ∪ E(P e)) ⊆ (bdry G A \ (V(P e) \ V(G₀))) ∪ {v'} := by
    intro u' v' gu' gv' hl' hpair hgu' hgv' hiu' hiv' hgu'A hgv'A
    refine ⟨?_, ?_⟩
    · intro x hx
      by_cases hxu' : x = u'
      · exact Or.inr hxu'
      · left
        have hx_not_int : x ∉ V(P e) \ V(G₀) := by
          rintro ⟨hxP, hx₀⟩
          obtain ⟨⟨g, ⟨hgA, hgPe⟩, hig⟩, -⟩ := hx
          exact hgPe (inc_mem_path_of_notMem_V₀ h he hxP hx₀ (hA hgA) hig)
        refine ⟨?_, hx_not_int⟩
        obtain ⟨⟨g₁, ⟨hg₁A, _⟩, hig₁⟩, g₂, ⟨hg₂E, hg₂_not⟩, hig₂⟩ := hx
        refine ⟨⟨g₁, hg₁A, hig₁⟩, g₂, ⟨hg₂E, fun hg₂A => hg₂_not ⟨hg₂A, fun hg₂Pe => ?_⟩⟩, hig₂⟩
        have hxP : x ∈ V(P e) := ((hle.isLink_iff hg₂Pe).mpr hig₂.choose_spec).left_mem
        have hxV₀ : x ∈ V(G₀) := by_contra fun hx₀ => hx_not_int ⟨hxP, hx₀⟩
        have hx_uv : x ∈ ({u', v'} : Set α) := hpair.symm ▸ (hcap ▸ ⟨hxP, hxV₀⟩)
        have hxv' : x = v' := hx_uv.resolve_left hxu'
        subst hxv'
        have hgeq : g₂ = gv' := h.eq_of_end he hl'.right_mem hg₂Pe hgv' hig₂ hiv'
        exact hgv'A (hgeq ▸ hg₂A)
    · intro x hx
      by_cases hxv' : x = v'
      · exact Or.inr hxv'
      · left
        have hx_not_int : x ∉ V(P e) \ V(G₀) := by
          rintro ⟨hxP, hx₀⟩
          obtain ⟨-, g, ⟨hgE, hg_not⟩, hig⟩ := hx
          exact hg_not (Or.inr (inc_mem_path_of_notMem_V₀ h he hxP hx₀ hgE hig))
        refine ⟨?_, hx_not_int⟩
        obtain ⟨⟨g₁, hg₁_in, hig₁⟩, g₂, ⟨hg₂E, hg₂_not⟩, hig₂⟩ := hx
        refine ⟨⟨g₁, ?_, hig₁⟩, g₂, ⟨hg₂E, fun hg₂A => hg₂_not (Or.inl hg₂A)⟩, hig₂⟩
        rcases hg₁_in with hg₁A | hg₁Pe
        · exact hg₁A
        · have hxP : x ∈ V(P e) := ((hle.isLink_iff hg₁Pe).mpr hig₁.choose_spec).left_mem
          have hxV₀ : x ∈ V(G₀) := by_contra fun hx₀ => hx_not_int ⟨hxP, hx₀⟩
          have hx_uv : x ∈ ({u', v'} : Set α) := hpair.symm ▸ (hcap ▸ ⟨hxP, hxV₀⟩)
          have hxu' : x = u' := hx_uv.resolve_right hxv'
          subst hxu'
          have hgeq : g₁ = gu' := h.eq_of_end he hl'.left_mem hg₁Pe hgu' hig₁ hiu'
          exact hgeq ▸ hgu'A
  by_cases hguA : gu ∈ A
  · have hgvA : gv ∉ A := fun h => hnot_iff ⟨fun _ => h, fun _ => hguA⟩
    exact ⟨u, v, hl, (hstep u v gu gv hl rfl hgu_Pe hgv_Pe (hincG hiu) (hincG hiv) hguA hgvA).1,
      (hstep u v gu gv hl rfl hgu_Pe hgv_Pe (hincG hiu) (hincG hiv) hguA hgvA).2⟩
  · have hgvA : gv ∈ A := by_contra fun h => hnot_iff ⟨fun h1 => (hguA h1).elim, fun h2 =>
      (h h2).elim⟩
    exact ⟨v, u, hl.symm,
      (hstep v u gv gu hl.symm (pair_comm v u) hgv_Pe hgu_Pe (hincG hiv) (hincG hiu) hgvA hguA).1,
      (hstep v u gv gu hl.symm (pair_comm v u) hgv_Pe hgu_Pe (hincG hiv) (hincG hiu) hgvA hguA).2⟩

/-- For any `A ⊆ E(G)` with `(bdry G A).ncard ≤ 2`, `A.Nonempty`, and `(E(G) \ A).Nonempty`,
`bdry G A` is contained in `V(P e)` for some `e ∈ E(G₀)`. -/
theorem bdry_subset_path (h : SubData G G₀ P) {A : Set β} (hA : A ⊆ E(G))
    (hc : (bdry G A).ncard ≤ 2) (hne : A.Nonempty) (hne' : (E(G) \ A).Nonempty) :
    ∃ e ∈ E(G₀), bdry G A ⊆ V(P e) := by
  by_cases hbd₀ : bdry G A ⊆ V(G₀)
  · obtain ⟨e, he, heq | heq⟩ := h.sep hA hbd₀ hc hne hne'
    · refine ⟨e, he, ?_⟩
      intro x hx
      obtain ⟨⟨g, hgA, y, hlink⟩, -⟩ := hx
      rw [heq] at hgA
      obtain ⟨_, _, -, hp, -, -⟩ := h.path e he
      exact ((hp.le.isLink_iff hgA).mpr hlink).left_mem
    · refine ⟨e, he, ?_⟩
      intro x hx
      obtain ⟨-, g, hgA, y, hlink⟩ := hx
      rw [heq] at hgA
      obtain ⟨_, _, -, hp, -, -⟩ := h.path e he
      exact ((hp.le.isLink_iff hgA).mpr hlink).left_mem
  · obtain ⟨w₁, hw₁_bd, hw₁_not₀⟩ := not_subset.mp hbd₀
    have hw₁_V : w₁ ∈ V(G) := bdry_subset_V A hw₁_bd
    rw [h.vunion] at hw₁_V
    have hw₁_union : w₁ ∈ ⋃ e ∈ E(G₀), V(P e) := hw₁_V.resolve_left hw₁_not₀
    obtain ⟨e₁, he₁, hw₁_Pe₁⟩ := mem_iUnion₂.mp hw₁_union
    refine ⟨e₁, he₁, ?_⟩
    by_contra hnot_sub
    obtain ⟨z, hz_bd, hz_not_Pe₁⟩ := not_subset.mp hnot_sub
    have hzw₁ : z ≠ w₁ := fun h => hz_not_Pe₁ (h ▸ hw₁_Pe₁)
    have hbd_eq : bdry G A = {w₁, z} := by
      have hsub : ({w₁, z} : Set α) ⊆ bdry G A := by
        rintro x (rfl | rfl)
        · exact hw₁_bd
        · exact hz_bd
      exact (Set.eq_of_subset_of_ncard_le hsub
        (by rw [Set.ncard_pair hzw₁.symm]; exact hc) (finite_bdry h A)).symm
    have hex_A' : ∃ (A' : Set β) (u' : α),
        A' ⊆ E(G) ∧ u' ∈ V(G₀) ∧ bdry G A' ⊆ {w₁, u'} ∧ w₁ ∈ bdry G A' ∧
        (A' \ E(P e₁)).Nonempty ∧ (E(G) \ (A' ∪ E(P e₁))).Nonempty := by
      by_cases hz₀ : z ∈ V(G₀)
      · refine ⟨A, z, hA, hz₀, hbd_eq.subset, hw₁_bd, ?_, ?_⟩
        · obtain ⟨⟨g, hgA, hig⟩, -⟩ := hz_bd
          exact ⟨g, hgA, fun hgP => not_inc_of_notMem_path h he₁ hz_not_Pe₁ hgP hig⟩
        · obtain ⟨-, g, ⟨hgE, hgA⟩, hig⟩ := hz_bd
          exact ⟨g, hgE, not_or.mpr ⟨hgA, fun hgP => not_inc_of_notMem_path h he₁ hz_not_Pe₁ hgP
            hig⟩⟩
      · have hz_V : z ∈ V(G) := bdry_subset_V A hz_bd
        rw [h.vunion] at hz_V
        obtain ⟨e₂, he₂, hz_Pe₂⟩ := mem_iUnion₂.mp (hz_V.resolve_left hz₀)
        have he12 : e₁ ≠ e₂ := fun heq => hz_not_Pe₁ (heq ▸ hz_Pe₂)
        have hdisj12 : Disjoint E(P e₁) E(P e₂) := (h.disj e₁ he₁ e₂ he₂ he12).1
        have hPe₂_sub : E(P e₂) ⊆ E(G) := fun g hg => by
          rw [h.eunion]; exact mem_iUnion₂.mpr ⟨e₂, he₂, hg⟩
        obtain ⟨_, _, -, -, ⟨g₂, hg₂_Pe₂⟩, -⟩ := h.path e₂ he₂
        have hz_inter : bdry G A ∩ (V(P e₂) \ V(G₀)) = {z} := by
          ext x
          rw [hbd_eq]
          simp only [mem_inter_iff, mem_insert_iff, mem_singleton_iff, mem_sdiff]
          constructor
          · exact fun ⟨hx, hxP, hx₀⟩ => hx.resolve_left (fun hxw =>
              hx₀ ((h.disj e₁ he₁ e₂ he₂ he12).2 ⟨hxw ▸ hw₁_Pe₁, hxP⟩))
          · rintro rfl
            exact ⟨Or.inr rfl, hz_Pe₂, hz₀⟩
        obtain ⟨u₂, v₂, hl₂, hs₁, hs₂⟩ := move_internal_bdry h hA he₂ hz_inter
        have hdiff₂ : bdry G A \ (V(P e₂) \ V(G₀)) = {w₁} := by
          ext x
          rw [hbd_eq]
          simp only [mem_sdiff, mem_insert_iff, mem_singleton_iff]
          constructor
          · exact fun ⟨hx, hnot⟩ => hx.resolve_right (fun hxz => hnot (hxz ▸ ⟨hz_Pe₂, hz₀⟩))
          · rintro rfl
            exact ⟨Or.inl rfl, fun ⟨hwP₂, _⟩ =>
              hw₁_not₀ ((h.disj e₁ he₁ e₂ he₂ he12).2 ⟨hw₁_Pe₁, hwP₂⟩)⟩
        rw [hdiff₂] at hs₁ hs₂
        obtain ⟨⟨gw₁, hgw₁A, higw₁⟩, fw₁, ⟨hfw₁E, hfw₁A⟩, hifw₁⟩ := hw₁_bd
        have hgw₁_Pe₁ : gw₁ ∈ E(P e₁) :=
          inc_mem_path_of_notMem_V₀ h he₁ hw₁_Pe₁ hw₁_not₀ (hA hgw₁A) higw₁
        have hfw₁_Pe₁ : fw₁ ∈ E(P e₁) :=
          inc_mem_path_of_notMem_V₀ h he₁ hw₁_Pe₁ hw₁_not₀ hfw₁E hifw₁
        have hw₁_in_diff : w₁ ∈ bdry G (A \ E(P e₂)) :=
          ⟨⟨gw₁, ⟨hgw₁A, disjoint_left.mp hdisj12 hgw₁_Pe₁⟩, higw₁⟩,
            fw₁, ⟨hfw₁E, fun h => hfw₁A h.1⟩, hifw₁⟩
        have hw₁_in_union : w₁ ∈ bdry G (A ∪ E(P e₂)) :=
          ⟨⟨gw₁, Or.inl hgw₁A, higw₁⟩, fw₁,
            ⟨hfw₁E, not_or.mpr ⟨hfw₁A, disjoint_left.mp hdisj12 hfw₁_Pe₁⟩⟩, hifw₁⟩
        by_cases hrem : (E(G) \ ((A ∪ E(P e₂)) ∪ E(P e₁))).Nonempty
        · refine ⟨A ∪ E(P e₂), v₂, union_subset hA hPe₂_sub, hl₂.right_mem, hs₂, hw₁_in_union,
            ⟨g₂, Or.inr hg₂_Pe₂, disjoint_right.mp hdisj12 hg₂_Pe₂⟩, hrem⟩
        · refine ⟨A \ E(P e₂), u₂, sdiff_subset.trans hA, hl₂.left_mem, hs₁, hw₁_in_diff, ?_,
            ⟨g₂, hPe₂_sub hg₂_Pe₂, not_or.mpr ⟨fun h => h.2 hg₂_Pe₂, disjoint_right.mp hdisj12
              hg₂_Pe₂⟩⟩⟩
          obtain ⟨a₁, a₂, a₃, ha₁, ha₂, ha₃, h12, h13, _⟩ := exists_three_edges_outside h he₁
          have hex_a : ∃ a ∈ E(G₀) \ {e₁}, a ≠ e₂ := by
            by_cases ha₁_eq : a₁ = e₂
            · exact ⟨a₂, ha₂, fun h2 => h12 (ha₁_eq.trans h2.symm)⟩
            · exact ⟨a₁, ha₁, ha₁_eq⟩
          obtain ⟨a, ⟨ha, ha_ne₁⟩, ha_ne₂⟩ := hex_a
          obtain ⟨_, _, -, -, ⟨ga, hga⟩, -⟩ := h.path a ha
          have hgaE : ga ∈ E(G) := by rw [h.eunion]; exact mem_iUnion₂.mpr ⟨a, ha, hga⟩
          have hga_not₁ : ga ∉ E(P e₁) := disjoint_left.mp (h.disj a ha e₁ he₁ ha_ne₁).1 hga
          have hga_not₂ : ga ∉ E(P e₂) := disjoint_left.mp (h.disj a ha e₂ he₂ ha_ne₂).1 hga
          have hgaA : ga ∈ A := by
            by_contra hgaA
            exact hrem ⟨ga, hgaE, not_or.mpr ⟨not_or.mpr ⟨hgaA, hga_not₂⟩, hga_not₁⟩⟩
          exact ⟨ga, ⟨hgaA, hga_not₂⟩, hga_not₁⟩
    obtain ⟨A', u', hA', hu'₀, hbdA', hw₁A', hB₁_ne, hB₂_ne⟩ := hex_A'
    have hw₁_inter' : bdry G A' ∩ (V(P e₁) \ V(G₀)) = {w₁} := by
      ext x
      simp only [mem_inter_iff, mem_sdiff, mem_singleton_iff]
      constructor
      · exact fun ⟨hx, _, hx₀⟩ => (hbdA' hx).resolve_right (fun hxu => hx₀ (hxu ▸ hu'₀))
      · rintro rfl
        exact ⟨hw₁A', hw₁_Pe₁, hw₁_not₀⟩
    obtain ⟨u₁', v₁', hl₁', hsub₁', hsub₂'⟩ := move_internal_bdry h hA' he₁ hw₁_inter'
    have hdiff_sub' : bdry G A' \ (V(P e₁) \ V(G₀)) ⊆ {u'} := by
      rintro x ⟨hx, hx_not⟩
      exact (hbdA' hx).resolve_left (fun hxw => hx_not (hxw ▸ ⟨hw₁_Pe₁, hw₁_not₀⟩))
    have hs₁' : bdry G (A' \ E(P e₁)) ⊆ {u', u₁'} :=
      hsub₁'.trans (union_subset_union_left _ hdiff_sub')
    have hs₂' : bdry G (A' ∪ E(P e₁)) ⊆ {u', v₁'} :=
      hsub₂'.trans (union_subset_union_left _ hdiff_sub')
    have hbd₁_V₀ : bdry G (A' \ E(P e₁)) ⊆ V(G₀) := by
      refine hs₁'.trans ?_
      rintro x (rfl | rfl)
      · exact hu'₀
      · exact hl₁'.left_mem
    have hc₁ : (bdry G (A' \ E(P e₁))).ncard ≤ 2 :=
      (Set.ncard_le_ncard hs₁' (Set.toFinite _)).trans (Set.ncard_insert_le _ _ |>.trans (by simp))
    have hbd₂_V₀ : bdry G (A' ∪ E(P e₁)) ⊆ V(G₀) := by
      refine hs₂'.trans ?_
      rintro x (rfl | rfl)
      · exact hu'₀
      · exact hl₁'.right_mem
    have hc₂ : (bdry G (A' ∪ E(P e₁))).ncard ≤ 2 :=
      (Set.ncard_le_ncard hs₂' (Set.toFinite _)).trans (Set.ncard_insert_le _ _ |>.trans (by simp))
    have hB₂_eq : A' \ E(P e₁) ∪ E(P e₁) = A' ∪ E(P e₁) := sdiff_union_self
    have hB₂_ne' : (E(G) \ (A' \ E(P e₁) ∪ E(P e₁))).Nonempty := hB₂_eq.symm ▸ hB₂_ne
    exact (not_both_sep_of_union_path h he₁ (sdiff_subset.trans hA') disjoint_sdiff_left
      hB₁_ne hB₂_ne' hbd₁_V₀ hc₁ (hB₂_eq ▸ hbd₂_V₀) (hB₂_eq ▸ hc₂)).elim

/-- If `bdry G A ⊆ V(P e)` (`e ∈ E(G₀)`), then `A ⊆ E(P e)` or `E(G) \ A ⊆ E(P e)`. -/
theorem subset_or_compl_subset_path (h : SubData G G₀ P) {A : Set β} (hA : A ⊆ E(G))
    {e : β} (he : e ∈ E(G₀)) (hbd : bdry G A ⊆ V(P e)) :
    A ⊆ E(P e) ∨ E(G) \ A ⊆ E(P e) := by
  by_contra! hnot
  obtain ⟨u, v, hl, ⟨hle, _, _, _, _⟩, _, hcap⟩ := h.path e he
  have hB₁_ne : (A \ E(P e)).Nonempty := not_subset.mp hnot.1
  have hB₂_ne : (E(G) \ (A \ E(P e) ∪ E(P e))).Nonempty := by
    rw [sdiff_union_self]
    obtain ⟨g, ⟨hgE, hgA⟩, hgP⟩ := not_subset.mp hnot.2
    exact ⟨g, hgE, not_or.mpr ⟨hgA, hgP⟩⟩
  have hbd_B₁ : bdry G (A \ E(P e)) ⊆ {u, v} := by
    intro x hx
    rw [← hcap]
    have hxP : x ∈ V(P e) := by
      by_contra hxP
      obtain ⟨⟨g₁, ⟨hg₁A, _⟩, hig₁⟩, g₂, ⟨hg₂E, hg₂_not⟩, hig₂⟩ := hx
      have hg₂A : g₂ ∉ A := fun hg₂A =>
        hg₂_not ⟨hg₂A, fun hg₂P => not_inc_of_notMem_path h he hxP hg₂P hig₂⟩
      exact hxP (hbd ⟨⟨g₁, hg₁A, hig₁⟩, g₂, ⟨hg₂E, hg₂A⟩, hig₂⟩)
    refine ⟨hxP, ?_⟩
    by_contra hx₀
    obtain ⟨⟨g₁, ⟨hg₁A, hg₁P⟩, hig₁⟩, -⟩ := hx
    exact hg₁P (inc_mem_path_of_notMem_V₀ h he hxP hx₀ (hA hg₁A) hig₁)
  have hbd_B₂ : bdry G (A ∪ E(P e)) ⊆ {u, v} := by
    intro x hx
    rw [← hcap]
    have hxP : x ∈ V(P e) := by
      by_contra hxP
      obtain ⟨⟨g₁, hg₁_in, hig₁⟩, g₂, ⟨hg₂E, hg₂_not⟩, hig₂⟩ := hx
      have hg₁A : g₁ ∈ A := hg₁_in.resolve_right fun hg₁P =>
        not_inc_of_notMem_path h he hxP hg₁P hig₁
      exact hxP (hbd ⟨⟨g₁, hg₁A, hig₁⟩, g₂, ⟨hg₂E, fun hg₂A => hg₂_not (Or.inl hg₂A)⟩, hig₂⟩)
    refine ⟨hxP, ?_⟩
    by_contra hx₀
    obtain ⟨-, g₂, ⟨hg₂E, hg₂_not⟩, hig₂⟩ := hx
    exact hg₂_not (Or.inr (inc_mem_path_of_notMem_V₀ h he hxP hx₀ hg₂E hig₂))
  have huv_V₀ : ({u, v} : Set α) ⊆ V(G₀) := by
    rintro x (rfl | rfl)
    · exact hl.left_mem
    · exact hl.right_mem
  have hc₁ : (bdry G (A \ E(P e))).ncard ≤ 2 :=
    (Set.ncard_le_ncard hbd_B₁ (Set.toFinite _)).trans (Set.ncard_insert_le _ _ |>.trans (by simp))
  have hc₂ : (bdry G (A ∪ E(P e))).ncard ≤ 2 :=
    (Set.ncard_le_ncard hbd_B₂ (Set.toFinite _)).trans (Set.ncard_insert_le _ _ |>.trans (by simp))
  have hB₂_eq : A \ E(P e) ∪ E(P e) = A ∪ E(P e) := sdiff_union_self
  exact not_both_sep_of_union_path h he (sdiff_subset.trans hA) disjoint_sdiff_left
    hB₁_ne hB₂_ne (hbd_B₁.trans huv_V₀) hc₁
    (hB₂_eq ▸ hbd_B₂.trans huv_V₀) (hB₂_eq ▸ hc₂)

/-- Associativity of `GraphWalk.append`. -/
theorem walk_append_assoc {H : Graph α β} {a b c d : α}
    (W₁ : GraphWalk H a b) (W₂ : GraphWalk H b c) (W₃ : GraphWalk H c d) :
    (W₁.append W₂).append W₃ = W₁.append (W₂.append W₃) := by
  induction W₁ with
  | nil _ => rfl
  | cons hlk rest ih => exact congrArg (GraphWalk.cons hlk) (ih W₂)

/-- Decomposing a walk at one of its edges. -/
theorem exists_decomp_of_mem_edges {H : Graph α β} {a b : α} (W : GraphWalk H a b)
    {g : β} (hg : g ∈ W.edges) :
    ∃ (x₀ y₀ : α) (hl : H.IsLink g x₀ y₀) (W₁ : GraphWalk H a x₀) (W₂ : GraphWalk H y₀ b),
      W = W₁.append (GraphWalk.cons hl W₂) := by
  induction W with
  | nil _ => simp [GraphWalk.edges] at hg
  | @cons u v w f hlink rest ih =>
    simp only [GraphWalk.edges, List.mem_cons] at hg
    rcases hg with rfl | hg
    · exact ⟨u, v, hlink, .nil hlink.left_mem, rest, rfl⟩
    · obtain ⟨x₀, y₀, hl, W₁, W₂, rfl⟩ := ih hg
      exact ⟨x₀, y₀, hl, .cons hlink W₁, W₂, rfl⟩

private theorem middle_walk_edges_have_uniform_side
    {α : Type u}
    {β : Type v}
    {G : Graph α β}
    {P : β → Graph α β}
    {e : β}
    {A : Set β}
    (u : α)
    (v : α)
    (W : GraphWalk (P e) u v)
    (x : α)
    (y : α)
    (hbd_eq : bdry G A = {x, y})
    (W_ux : GraphWalk (P e) u x)
    (W_yv : GraphWalk (P e) y v)
    (W_mid : GraphWalk (P e) x y)
    (hW_full : W = W_ux.append (W_mid.append W_yv))
    (hs_mid : W_mid.IsSimple)
    (hmemE : ∀ {g : β}, g ∈ W.edges → g ∈ E(G))
    (hincG : ∀ {g : β} {z : α}, (P e).Inc g z → G.Inc g z) :
    ∀ e₁ ∈ W_mid.edges, ∀ e₂ ∈ W_mid.edges, e₁ ∈ A ↔ e₂ ∈ A := by
  refine walk_pure W_mid hs_mid fun z hz hzx hzy e₁ he₁ e₂ he₂ hi₁ hi₂ => ?_
  have hz_not_bd : z ∉ bdry G A := by
    rw [hbd_eq]
    exact not_or.mpr ⟨hzx, hzy⟩
  have he₁W : e₁ ∈ W.edges := by
    rw [hW_full, GraphWalk.edges_append, GraphWalk.edges_append]
    exact List.mem_append_right _ (List.mem_append_left _ he₁)
  have he₂W : e₂ ∈ W.edges := by
    rw [hW_full, GraphWalk.edges_append, GraphWalk.edges_append]
    exact List.mem_append_right _ (List.mem_append_left _ he₂)
  constructor <;> intro h₁ <;> by_contra h₂
  · exact hz_not_bd ⟨⟨e₁, h₁, hincG hi₁⟩, e₂, ⟨hmemE he₂W, h₂⟩, hincG hi₂⟩
  · exact hz_not_bd ⟨⟨e₂, h₁, hincG hi₂⟩, e₁, ⟨hmemE he₁W, h₂⟩, hincG hi₁⟩

/-- When `A ⊆ E(P e)` is nonempty and `(bdry G A).ncard ≤ 2`, `A` is the edge set of a subpath `Q`
of `P e` between the two distinct vertices of `bdry G A`. -/
theorem sep_of_subset_path (h : SubData G G₀ P) {e : β} (he : e ∈ E(G₀))
    {A : Set β} (hA : A ⊆ E(P e)) (hc : (bdry G A).ncard ≤ 2) (hne : A.Nonempty) :
    ∃ (x y : α) (Q : Graph α β),
      x ≠ y ∧ bdry G A = {x, y} ∧ Q ≤ P e ∧
      IsGraphPathWithEnds G Q x y ∧ A = E(Q) ∧ verts G A = V(Q) := by
  obtain ⟨u, v, hl, ⟨hle, W, hs, hV, hE⟩, _, hcap⟩ := h.path e he
  obtain ⟨g₀, hg₀A⟩ := hne
  have hg₀W : g₀ ∈ W.edges := by
    have : g₀ ∈ E(P e) := hA hg₀A
    rwa [hE] at this
  obtain ⟨x₀, y₀, hl₀, W₁, W₂, hW_eq⟩ := exists_decomp_of_mem_edges W hg₀W
  have hsupp_eq : W.support = W₁.support ++ W₂.support := by
    rw [hW_eq, GraphWalk.support_append]
    rfl
  have hnd_12 : (W₁.support ++ W₂.support).Nodup := hsupp_eq ▸ hs
  have hd_12 := List.nodup_append.mp hnd_12
  obtain ⟨fu, hfuE, hfu_not, hifu⟩ := h.exists_other_edge hl
  obtain ⟨fv, hfvE, hfv_not, hifv⟩ := h.exists_other_edge hl.symm
  have hu_out : u ∈ verts G (E(G) \ A) := ⟨fu, ⟨hfuE, fun h => hfu_not (hA h)⟩, hifu⟩
  have hv_out : v ∈ verts G (E(G) \ A) := ⟨fv, ⟨hfvE, fun h => hfv_not (hA h)⟩, hifv⟩
  have hx₀_in : x₀ ∈ verts G A := ⟨g₀, hg₀A, y₀, hl₀.mono hle⟩
  have hy₀_in : y₀ ∈ verts G A := ⟨g₀, hg₀A, x₀, (hl₀.mono hle).symm⟩
  have hex_x : ∃ x ∈ W₁.support, x ∈ bdry G A := by
    by_cases hu_in : u ∈ verts G A
    · exact ⟨u, W₁.start_mem_support, hu_in, hu_out⟩
    · obtain ⟨W₁G, hsupp₁, _⟩ := W₁.reverse.exists_transfer (G' := G)
        (fun _ _ _ _ hlk => hlk.mono hle)
        (fun z hz => hle.vertexSet_mono (W₁.reverse.mem_vertexSet_of_mem_support hz))
      obtain ⟨x, hxG, _, hxbd⟩ := exists_bdry_of_walk W₁G hx₀_in hu_in
      rw [hsupp₁, GraphWalk.support_reverse, List.mem_reverse] at hxG
      exact ⟨x, hxG, hxbd⟩
  have hex_y : ∃ y ∈ W₂.support, y ∈ bdry G A := by
    by_cases hv_in : v ∈ verts G A
    · exact ⟨v, W₂.end_mem_support, hv_in, hv_out⟩
    · obtain ⟨W₂G, hsupp₂, _⟩ := W₂.exists_transfer (G' := G)
        (fun _ _ _ _ hlk => hlk.mono hle)
        (fun z hz => hle.vertexSet_mono (W₂.mem_vertexSet_of_mem_support hz))
      obtain ⟨y, hyG, _, hybd⟩ := exists_bdry_of_walk W₂G hy₀_in hv_in
      rw [hsupp₂] at hyG
      exact ⟨y, hyG, hybd⟩
  obtain ⟨x, hxW₁, hx_bd⟩ := hex_x
  obtain ⟨y, hyW₂, hy_bd⟩ := hex_y
  have hxy : x ≠ y := fun heq => hd_12.2.2 x hxW₁ y hyW₂ heq
  have hbd_eq : bdry G A = {x, y} := by
    have hsub : ({x, y} : Set α) ⊆ bdry G A := by
      rintro z (rfl | rfl)
      · exact hx_bd
      · exact hy_bd
    exact (Set.eq_of_subset_of_ncard_le hsub
      (by rw [Set.ncard_pair hxy]; exact hc) (finite_bdry h A)).symm
  obtain ⟨W_ux, W_xx₀, hW₁_eq⟩ := W₁.exists_append_of_mem hxW₁
  obtain ⟨W_y₀y, W_yv, hW₂_eq⟩ := W₂.exists_append_of_mem hyW₂
  let W_mid : GraphWalk (P e) x y := W_xx₀.append (GraphWalk.cons hl₀ W_y₀y)
  have hW_full : W = W_ux.append (W_mid.append W_yv) := by
    dsimp [W_mid]
    rw [hW_eq, hW₁_eq, hW₂_eq, walk_append_assoc]
    exact congrArg (W_ux.append ·) (walk_append_assoc W_xx₀ (GraphWalk.cons hl₀ W_y₀y) W_yv).symm
  have hs_full : (W_ux.append (W_mid.append W_yv)).IsSimple := hW_full ▸ hs
  have hs_ux : W_ux.IsSimple := (GM09.isSimple_of_append hs_full).1
  have hs_mid_yv : (W_mid.append W_yv).IsSimple := (GM09.isSimple_of_append hs_full).2
  have hs_mid : W_mid.IsSimple := (GM09.isSimple_of_append hs_mid_yv).1
  have hs_yv : W_yv.IsSimple := (GM09.isSimple_of_append hs_mid_yv).2
  have hnd_ux_rest : (W_ux.support ++ (W_mid.append W_yv).support.tail).Nodup := by
    have h1 : (W_ux.append (W_mid.append W_yv)).support.Nodup := hs_full
    rwa [GraphWalk.support_append] at h1
  have hd_ux_rest := List.nodup_append.mp hnd_ux_rest
  have hnd_mid_yv : (W_mid.support ++ W_yv.support.tail).Nodup := by
    have h1 : (W_mid.append W_yv).support.Nodup := hs_mid_yv
    rwa [GraphWalk.support_append] at h1
  have hd_mid_yv := List.nodup_append.mp hnd_mid_yv
  have hmemE : ∀ {g : β}, g ∈ W.edges → g ∈ E(G) := fun {g} hg =>
    hle.edgeSet_mono (by rw [hE]; exact hg)
  have hincG : ∀ {g z}, (P e).Inc g z → G.Inc g z := fun ⟨w, hw⟩ => ⟨w, hw.mono hle⟩
  have hmid_pure : ∀ e₁ ∈ W_mid.edges, ∀ e₂ ∈ W_mid.edges, e₁ ∈ A ↔ e₂ ∈ A := by
    exact middle_walk_edges_have_uniform_side (α := α) (β := β) (G := G) (P := P) (e := e) (A :=
      A) u v W x y hbd_eq W_ux W_yv W_mid hW_full hs_mid hmemE hincG
  have hg₀_mid : g₀ ∈ W_mid.edges := by
    dsimp [W_mid]
    rw [GraphWalk.edges_append]
    exact List.mem_append_right _ List.mem_cons_self
  have hmid_sub_A : ∀ a ∈ W_mid.edges, a ∈ A :=
    fun a ha => (hmid_pure a ha g₀ hg₀_mid).mpr hg₀A
  have hux_disj_A : ∀ a ∈ W_ux.edges, a ∉ A := by
    intro a ha
    have hux_ne : u ≠ x := by
      rintro rfl
      have hlen0 := GraphWalk.IsSimple.length_eq_zero hs_ux
      exact List.ne_nil_of_mem ha (List.length_eq_zero_iff.mp hlen0)
    have huy : u ≠ y := by
      rintro rfl
      exact hd_12.2.2 u W₁.start_mem_support u hyW₂ rfl
    have hu_not_bd : u ∉ bdry G A := by
      rw [hbd_eq]
      exact not_or.mpr ⟨hux_ne, huy⟩
    have hu_not_in : u ∉ verts G A := fun hu_in => hu_not_bd ⟨hu_in, hu_out⟩
    obtain ⟨gu, hgu, hiu⟩ := exists_edge_at_start W_ux hux_ne
    have hgu_not_A : gu ∉ A := fun h => hu_not_in ⟨gu, h, hincG hiu⟩
    have hux_pure : ∀ e₁ ∈ W_ux.edges, ∀ e₂ ∈ W_ux.edges, e₁ ∈ A ↔ e₂ ∈ A := by
      refine walk_pure W_ux hs_ux fun z hz hzu hzx e₁ he₁ e₂ he₂ hi₁ hi₂ => ?_
      have hzy : z ≠ y := by
        rintro rfl
        have hy_rest : z ∈ (W_mid.append W_yv).support := by
          rw [GraphWalk.mem_support_append]
          exact Or.inl W_mid.end_mem_support
        rw [(W_mid.append W_yv).support_eq_cons] at hy_rest
        rcases List.mem_cons.mp hy_rest with rfl | hy_tail
        · exact hzx rfl
        · exact hd_ux_rest.2.2 z hz z hy_tail rfl
      have hz_not_bd : z ∉ bdry G A := by
        rw [hbd_eq]
        exact not_or.mpr ⟨hzx, hzy⟩
      have he₁W : e₁ ∈ W.edges := by
        rw [hW_full, GraphWalk.edges_append]
        exact List.mem_append_left _ he₁
      have he₂W : e₂ ∈ W.edges := by
        rw [hW_full, GraphWalk.edges_append]
        exact List.mem_append_left _ he₂
      constructor <;> intro h₁ <;> by_contra h₂
      · exact hz_not_bd ⟨⟨e₁, h₁, hincG hi₁⟩, e₂, ⟨hmemE he₂W, h₂⟩, hincG hi₂⟩
      · exact hz_not_bd ⟨⟨e₂, h₁, hincG hi₂⟩, e₁, ⟨hmemE he₁W, h₂⟩, hincG hi₁⟩
    exact fun haA => hgu_not_A ((hux_pure a ha gu hgu).mp haA)
  have hyv_disj_A : ∀ a ∈ W_yv.edges, a ∉ A := by
    intro a ha
    have hyv_ne : y ≠ v := by
      rintro rfl
      have hlen0 := GraphWalk.IsSimple.length_eq_zero hs_yv
      exact List.ne_nil_of_mem ha (List.length_eq_zero_iff.mp hlen0)
    have hxv : x ≠ v := by
      rintro rfl
      exact hd_12.2.2 x hxW₁ x W₂.end_mem_support rfl
    have hv_not_bd : v ∉ bdry G A := by
      rw [hbd_eq]
      exact not_or.mpr ⟨Ne.symm hxv, Ne.symm hyv_ne⟩
    have hv_not_in : v ∉ verts G A := fun hv_in => hv_not_bd ⟨hv_in, hv_out⟩
    obtain ⟨gv, hgv_rev, hiv⟩ := exists_edge_at_start W_yv.reverse hyv_ne.symm
    have hgv : gv ∈ W_yv.edges := by
      rw [GraphWalk.edges_reverse] at hgv_rev
      exact List.mem_reverse.mp hgv_rev
    have hgv_not_A : gv ∉ A := fun h => hv_not_in ⟨gv, h, hincG hiv⟩
    have hyv_pure : ∀ e₁ ∈ W_yv.edges, ∀ e₂ ∈ W_yv.edges, e₁ ∈ A ↔ e₂ ∈ A := by
      refine walk_pure W_yv hs_yv fun z hz hzy hzv e₁ he₁ e₂ he₂ hi₁ hi₂ => ?_
      have hzx : z ≠ x := by
        rintro rfl
        have hx_mid : z ∈ W_mid.support := W_mid.start_mem_support
        rw [W_yv.support_eq_cons] at hz
        rcases List.mem_cons.mp hz with rfl | hz_tail
        · exact hzy rfl
        · exact hd_mid_yv.2.2 z hx_mid z hz_tail rfl
      have hz_not_bd : z ∉ bdry G A := by
        rw [hbd_eq]
        exact not_or.mpr ⟨hzx, hzy⟩
      have he₁W : e₁ ∈ W.edges := by
        rw [hW_full, GraphWalk.edges_append, GraphWalk.edges_append]
        exact List.mem_append_right _ (List.mem_append_right _ he₁)
      have he₂W : e₂ ∈ W.edges := by
        rw [hW_full, GraphWalk.edges_append, GraphWalk.edges_append]
        exact List.mem_append_right _ (List.mem_append_right _ he₂)
      constructor <;> intro h₁ <;> by_contra h₂
      · exact hz_not_bd ⟨⟨e₁, h₁, hincG hi₁⟩, e₂, ⟨hmemE he₂W, h₂⟩, hincG hi₂⟩
      · exact hz_not_bd ⟨⟨e₂, h₁, hincG hi₂⟩, e₁, ⟨hmemE he₁W, h₂⟩, hincG hi₁⟩
    exact fun haA => hgv_not_A ((hyv_pure a ha gv hgv).mp haA)
  let Q : Graph α β := walkSubgraph W_mid
  have hQ_le_Pe : Q ≤ P e := walkSubgraph_le W_mid
  have hQ_path : IsGraphPathWithEnds G Q x y :=
    (isGraphPathWithEnds_walkSubgraph hs_mid).of_le (hQ_le_Pe.trans hle)
  have hA_eq_EQ : A = E(Q) := by
    rw [edgeSet_walkSubgraph]
    ext a
    simp only [mem_ofPred_eq]
    constructor
    · intro haA
      have haW : a ∈ W.edges := by
        have : a ∈ E(P e) := hA haA
        rwa [hE] at this
      rw [hW_full, GraphWalk.edges_append, GraphWalk.edges_append] at haW
      rcases List.mem_append.mp haW with hux | hrest
      · exact (hux_disj_A a hux haA).elim
      · rcases List.mem_append.mp hrest with hmid | hyv
        · exact hmid
        · exact (hyv_disj_A a hyv haA).elim
    · exact fun ha => hmid_sub_A a ha
  have hverts_eq_VQ : verts G A = V(Q) := by
    rw [hA_eq_EQ, edgeSet_walkSubgraph, vertexSet_walkSubgraph]
    ext z
    simp only [verts, mem_ofPred_eq]
    constructor
    · rintro ⟨a, ha, hia⟩
      have haQ : a ∈ E(Q) := by rw [edgeSet_walkSubgraph]; exact ha
      exact inc_mem_support W_mid ha (SubData.inc_path hle (hQ_le_Pe.edgeSet_mono haQ) hia)
    · intro hz
      by_cases hzx : z = x
      · subst hzx
        obtain ⟨a, ha, hia⟩ := exists_edge_at_start W_mid hxy
        exact ⟨a, ha, hincG hia⟩
      · by_cases hzy : z = y
        · subst hzy
          obtain ⟨a, ha_rev, hia⟩ := exists_edge_at_start W_mid.reverse hxy.symm
          rw [GraphWalk.edges_reverse] at ha_rev
          exact ⟨a, List.mem_reverse.mp ha_rev, hincG hia⟩
        · obtain ⟨a, ha, _, _, _, hia, _⟩ := exists_two_edges_at_inner W_mid hs_mid hz hzx hzy
          exact ⟨a, ha, hincG hia⟩
  exact ⟨x, y, Q, hxy, hbd_eq, hQ_le_Pe, hQ_path, hA_eq_EQ, hverts_eq_VQ⟩

/-- **General 2-Separation Theorem for Subdivisions of Simple 3-Connected Graphs**:
For any `A ⊆ E(G)` with `(bdry G A).ncard ≤ 2`, `A.Nonempty`, and `(E(G) \ A).Nonempty`, either
`A` or `E(G) \ A` is the edge set of a subpath `Q` of some subdivision path `P e` (`e ∈ E(G₀)`)
joining the two vertices of `bdry G A`. -/
theorem sep_general (h : SubData G G₀ P) {A : Set β} (hA : A ⊆ E(G))
    (hc : (bdry G A).ncard ≤ 2) (hne : A.Nonempty) (hne' : (E(G) \ A).Nonempty) :
    ∃ (e : β) (x y : α) (Q : Graph α β),
      e ∈ E(G₀) ∧ x ≠ y ∧ bdry G A = {x, y} ∧ Q ≤ P e ∧
      IsGraphPathWithEnds G Q x y ∧
      ((A = E(Q) ∧ verts G A = V(Q)) ∨
       (E(G) \ A = E(Q) ∧ verts G (E(G) \ A) = V(Q))) := by
  obtain ⟨e, he, hbd_Pe⟩ := bdry_subset_path h hA hc hne hne'
  rcases subset_or_compl_subset_path h hA he hbd_Pe with hsub | hsub
  · obtain ⟨x, y, Q, hxy, hbd_eq, hQ_le, hQ_path, hAE, hAV⟩ :=
      sep_of_subset_path h he hsub hc hne
    exact ⟨e, x, y, Q, he, hxy, hbd_eq, hQ_le, hQ_path, Or.inl ⟨hAE, hAV⟩⟩
  · have hc' : (bdry G (E(G) \ A)).ncard ≤ 2 := by rwa [bdry_compl hA]
    obtain ⟨x, y, Q, hxy, hbd_eq, hQ_le, hQ_path, hAE, hAV⟩ :=
      sep_of_subset_path h he hsub hc' hne'
    rw [bdry_compl hA] at hbd_eq
    exact ⟨e, x, y, Q, he, hxy, hbd_eq, hQ_le, hQ_path, Or.inr ⟨hAE, hAV⟩⟩

/-- Every vertex of a subdivision of a simple 3-connected graph is incident with an edge. -/
theorem exists_inc_of_mem_V (h : SubData G G₀ P) {x : α} (hx : x ∈ V(G)) :
    ∃ g ∈ E(G), G.Inc g x := by
  have hex_P : ∃ e ∈ E(G₀), x ∈ V(P e) := by
    rw [h.vunion] at hx
    rcases hx with hx₀ | hxP
    · obtain ⟨e, _, _, _, _, _, ⟨y, hl⟩, _, _⟩ :=
        IsSimpleThreeConnected.exists_three_edges h.simple hx₀
      obtain ⟨u, v, hlu, _, _, hcap⟩ := h.path e hl.edge_mem
      have hx_uv : x = u ∨ x = v := G₀.eq_or_eq_of_isLink_of_isLink hl hlu
      have hx_cap : x ∈ V(P e) ∩ V(G₀) := by
        rw [hcap]
        exact hx_uv
      exact ⟨e, hl.edge_mem, hx_cap.1⟩
    · obtain ⟨e, he, hxP⟩ := mem_iUnion₂.mp hxP
      exact ⟨e, he, hxP⟩
  obtain ⟨e, he, hxP⟩ := hex_P
  obtain ⟨u, v, hl, ⟨hle, W, hs, hV, hE⟩, ⟨g₀, hg₀⟩, _⟩ := h.path e he
  have huv : u ≠ v := by
    rintro rfl
    have hlen0 := GraphWalk.IsSimple.length_eq_zero hs
    have hg₀W : g₀ ∈ W.edges := by rwa [hE] at hg₀
    exact List.ne_nil_of_mem hg₀W (List.length_eq_zero_iff.mp hlen0)
  have hxW : x ∈ W.support := by rwa [hV] at hxP
  by_cases hxu : x = u
  · subst hxu
    obtain ⟨g, hg, w, hlk⟩ := exists_edge_at_start W huv
    have hgP : g ∈ E(P e) := by rw [hE]; exact hg
    exact ⟨g, hle.edgeSet_mono hgP, w, hlk.mono hle⟩
  · by_cases hxv : x = v
    · subst hxv
      obtain ⟨g, hg_rev, w, hlk⟩ := exists_edge_at_start W.reverse huv.symm
      rw [GraphWalk.edges_reverse] at hg_rev
      have hgP : g ∈ E(P e) := by rw [hE]; exact List.mem_reverse.mp hg_rev
      exact ⟨g, hle.edgeSet_mono hgP, w, hlk.mono hle⟩
    · obtain ⟨g, hg, _, _, _, ⟨w, hlk⟩, _⟩ := exists_two_edges_at_inner W hs hxW hxu hxv
      have hgP : g ∈ E(P e) := by rw [hE]; exact hg
      exact ⟨g, hle.edgeSet_mono hgP, w, hlk.mono hle⟩

end SubDataSepGeneral

end GraphMinor.GM14
