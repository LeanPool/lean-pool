/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM20.Section6d

/-!
# Graph Minors XX, Section 7, (7.1)

For a free patchwork `P` and a set `W` of roots, the groupings feasible in `P/W` are those `K` with
`K ∪ N_W` feasible in `P`. One direction adds the vertices of `W` as isolated vertices. For the
other,
take a realization `H` of `P`. No root outside `W` is connected to `W` in `H`, so deleting `W` keeps
the connections between the roots outside `W`, and the free patches allow the deletion.
-/

@[expose] public section

namespace GraphMinor.GM20

open Set GraphMinor.GM18 GraphMinor.GM10 Hypergraph GraphMinor.GM04

universe u v

variable {α : Type u} {β : Type v} {Ω : Type*}

/-- Feasibility depends only on the base and the march of the roots. -/
theorem feasible_of_sameBase {Ω₂ : Type*} {P : Patchwork Ω α β} {Q : Patchwork Ω₂ α β}
    (hb : SameBase P Q) (hr : P.G.roots = Q.G.roots) {K : (⊤ : SimpleGraph α).Subgraph}
    (hK : IsFeasibleGrouping P K) : IsFeasibleGrouping Q K := by
  have hrs : P.G.rootSet = Q.G.rootSet := by
    change {v | v ∈ P.G.roots} = {v | v ∈ Q.G.roots}
    rw [hr]
  obtain ⟨h₁, h₂, H, hH, hc⟩ := hK
  refine ⟨hrs ▸ h₁, hrs ▸ h₂, H, hH.congr hb.vertexSet_eq hb.edgeSet_eq fun e he ↦ hb.Δ_eq he, ?_⟩
  rw [← hrs]
  exact hc

theorem sameComponent_of_adj_imp {T H : (⊤ : SimpleGraph α).Subgraph}
    (hadj : ∀ a b, T.Adj a b → H.Adj a b) {x y : α} (hx : x ∈ H.verts)
    (h : sameComponent T x y) : sameComponent H x y := by
  obtain ⟨hp, hq, hr⟩ := sameComponent_iff.mp h
  rw [SimpleGraph.reachable_iff_reflTransGen] at hr
  suffices ∀ w : T.verts, Relation.ReflTransGen T.coe.Adj ⟨x, hp⟩ w → sameComponent H x w.1 from
    this ⟨y, hq⟩ hr
  intro w hw
  induction hw with
  | refl => exact sameComponent_iff.mpr ⟨hx, hx, SimpleGraph.Reachable.refl _⟩
  | @tail a b _ hab ih => exact ih.trans (sameComponent_of_adj (hadj a.1 b.1 hab))

theorem eq_of_sameComponent_of_isolated {T : (⊤ : SimpleGraph α).Subgraph} {w y : α}
    (hiso : ∀ b, ¬ T.Adj w b) (h : sameComponent T w y) : w = y := by
  obtain ⟨hp, hq, hr⟩ := sameComponent_iff.mp h
  rw [SimpleGraph.reachable_iff_reflTransGen] at hr
  suffices ∀ z : T.verts, Relation.ReflTransGen T.coe.Adj ⟨w, hp⟩ z → w = z.1 from
    this ⟨y, hq⟩ hr
  intro z hz
  induction hz with
  | refl => rfl
  | @tail a b _ hab ih =>
    have h₁ : T.Adj a.1 b.1 := hab
    rw [← ih] at h₁
    exact absurd h₁ (hiso _)

/-- Removing the vertices of `W` from a subgraph. -/
def dropVerts (δ : (⊤ : SimpleGraph α).Subgraph) (W : Set α) : (⊤ : SimpleGraph α).Subgraph where
  verts := δ.verts \ W
  Adj a b := δ.Adj a b ∧ a ∉ W ∧ b ∉ W
  adj_sub h := δ.adj_sub h.1
  edge_vert h := ⟨δ.edge_vert h.1, h.2.1⟩
  symm := ⟨fun _ _ h ↦ ⟨h.1.symm, h.2.2, h.2.1⟩⟩

theorem isGrouping_dropVerts {V W : Set α} {δ : (⊤ : SimpleGraph α).Subgraph}
    (h : IsGrouping V δ) : IsGrouping (V \ W) (dropVerts δ W) := by
  rw [isGrouping_iff] at h ⊢
  refine ⟨fun x hx ↦ ⟨h.1 hx.1, hx.2⟩, fun a b c hac hab hbc ↦ ?_⟩
  exact ⟨h.2 a b c hac hab.1 hbc.1, hab.2.1, hbc.2.2⟩

/-- Graph Minors XX, (7.1), the direction from `P/W` to `P`. -/
theorem feasible_of_feasible_slash {P : Patchwork Ω α β} {W : Set α} (hW : W ⊆ P.G.rootSet)
    {K : (⊤ : SimpleGraph α).Subgraph} (hK : IsFeasibleGrouping (P.slash W) K) :
    IsFeasibleGrouping P (K ⊔ emptySubgraph W) := by
  obtain ⟨hg, hv, H, hH, hc⟩ := hK
  have hrs : (P.slash W).G.rootSet = P.G.rootSet \ W := by
    ext x
    exact mem_slash_rootSet
  rw [hrs] at hg hv hc
  have hWV : W ⊆ P.G.vertexSet := fun x hx ↦ P.G.roots_subset x (hW hx)
  have hKW : W ∩ P.G.rootSet = W := inter_eq_left.mpr hW
  have hgr : IsGrouping P.G.rootSet (K ⊔ emptySubgraph W) := by
    have := isGrouping_sup_emptySubgraph (Z := P.G.rootSet) hg
    rwa [hKW] at this
  have hreal : P.IsRealization (H ⊔ emptySubgraph W) := by
    refine realization_sup_emptySubgraph W hH ?_ rfl fun e he δ hδ ↦ ?_
    · change P.G.vertexSet = (P.G.vertexSet \ W) ∪ W
      rw [Set.sdiff_union_of_subset hWV]
    · have h₂ := hδ.2.2
      rwa [P.Δ_verts e he] at h₂
  have hHv : H.verts = P.G.vertexSet \ W := hH.verts_eq
  have hadj : ∀ a b, (H ⊔ emptySubgraph W).Adj a b → H.Adj a b := fun a b h ↦ by
    simpa [not_emptySubgraph_adj] using h
  have hiso : ∀ {w}, w ∈ W → ∀ {y}, sameComponent (H ⊔ emptySubgraph W) w y → w = y := by
    intro w hw y h
    refine eq_of_sameComponent_of_isolated (fun b hb ↦ ?_) h
    have := H.edge_vert (hadj w b hb)
    rw [hHv] at this
    exact this.2 hw
  refine ⟨hgr, ?_, _, hreal, fun x hx y hy hne ↦ ?_⟩
  · change K.verts ∪ W = _
    rw [hv, Set.sdiff_union_of_subset hW]
  rw [← sameComponent_iff_connectedIn]
  have hsup : (K ⊔ emptySubgraph W).Adj x y ↔ K.Adj x y := by
    simp [not_emptySubgraph_adj]
  rw [hsup]
  have hKW : ∀ {a b}, K.Adj a b → a ∉ W ∧ b ∉ W := fun {a b} h ↦ by
    have h₁ := K.edge_vert h
    have h₂ := K.edge_vert h.symm
    rw [hv] at h₁ h₂
    exact ⟨h₁.2, h₂.2⟩
  by_cases hxW : x ∈ W
  · exact ⟨fun h ↦ absurd (hiso hxW h) hne, fun h ↦ absurd hxW (hKW h).1⟩
  by_cases hyW : y ∈ W
  · exact ⟨fun h ↦ absurd (hiso hyW h.symm) hne.symm, fun h ↦ absurd hyW (hKW h).2⟩
  have hxV : x ∈ H.verts := by
    rw [hHv]
    exact ⟨P.G.roots_subset x hx, hxW⟩
  rw [← hc x ⟨hx, hxW⟩ y ⟨hy, hyW⟩ hne, ← sameComponent_iff_connectedIn]
  exact ⟨sameComponent_of_adj_imp hadj hxV, sameComponent.mono le_sup_left⟩

/-- Graph Minors XX, (7.1), the direction from `P` to `P/W`, where `P` is free. -/
theorem feasible_slash_of_feasible {P : Patchwork Ω α β} (hfree : IsFree P) {W : Set α}
    (hW : W ⊆ P.G.rootSet) {K : (⊤ : SimpleGraph α).Subgraph} (hg : IsGrouping (P.G.rootSet \ W) K)
    (hv : K.verts = P.G.rootSet \ W) (hK : IsFeasibleGrouping P (K ⊔ emptySubgraph W)) :
    IsFeasibleGrouping (P.slash W) K := by
  obtain ⟨-, -, H, ⟨δ, hδ, rfl⟩, hc⟩ := hK
  have hrs : (P.slash W).G.rootSet = P.G.rootSet \ W := by
    ext x
    exact mem_slash_rootSet
  have hmem : ∀ e ∈ (P.slash W).G.edgeSet, dropVerts (δ e) W ∈ (P.slash W).Δ e := by
    intro e he
    have hgr := (P.Δ e).isGrouping _ (hδ e he)
    have hvt := (P.Δ e).verts_eq _ (hδ e he)
    have hdg : IsGrouping ((P.Δ e).verts \ W) (dropVerts (δ e) W) := isGrouping_dropVerts hgr
    have hdv : (dropVerts (δ e) W).verts = (P.Δ e).verts \ W := by
      change (δ e).verts \ W = _
      rw [hvt]
    refine ⟨hdg, hdv, hfree e he _ (isGrouping_sup_emptySubgraph hdg) ?_⟩
    change (dropVerts (δ e) W).verts ∪ (W ∩ (P.Δ e).verts) = _
    rw [hdv]
    ext x
    by_cases hx : x ∈ W <;> simp [hx]
  have hreal : (P.slash W).IsRealization
      (realizationOf (P.slash W).G.toHypergraph fun e ↦ dropVerts (δ e) W) := ⟨_, hmem, rfl⟩
  set H' := realizationOf (P.slash W).G.toHypergraph fun e ↦ dropVerts (δ e) W with hH'
  set H := realizationOf P.G.toHypergraph δ with hH
  have hHr : P.IsRealization H := ⟨δ, hδ, rfl⟩
  have hsup : ∀ {x y}, (K ⊔ emptySubgraph W).Adj x y ↔ K.Adj x y := by
    intro x y
    simp [not_emptySubgraph_adj]
  have hH'H : ∀ a b, H'.Adj a b → H.Adj a b := by
    intro a b h
    obtain ⟨e, he, h₁⟩ := realizationOf_adj.mp h
    exact realizationOf_adj.mpr ⟨e, he, h₁.1⟩
  refine ⟨hrs ▸ hg, hrs ▸ hv, H', hreal, fun x hx y hy hne ↦ ?_⟩
  rw [hrs] at hx hy
  have hxr := hx.1
  have hyr := hy.1
  rw [← sameComponent_iff_connectedIn]
  have hcon := hc x hxr y hyr hne
  rw [← sameComponent_iff_connectedIn, hsup] at hcon
  rw [← hcon]
  constructor
  · refine sameComponent_of_forall_adj ?_ (fun a b h ↦ sameComponent_of_adj (hH'H a b h))
    rw [hreal.verts_eq, hHr.verts_eq]
    exact fun z hz ↦ hz.1
  · intro hxy
    -- No vertex connected to `x` in `H` lies in `W`.
    have hnoW : ∀ {w}, sameComponent H x w → w ∉ W := by
      intro w hw hwW
      have hne' : x ≠ w := fun h ↦ hx.2 (h ▸ hwW)
      have h₁ := hc x hxr w (hW hwW) hne'
      rw [← sameComponent_iff_connectedIn, hsup] at h₁
      have h₂ := K.edge_vert (h₁.mp hw).symm
      rw [hv] at h₂
      exact h₂.2 hwW
    have hxH' : x ∈ H'.verts := by
      rw [hreal.verts_eq]
      exact ⟨P.G.roots_subset x hxr, hx.2⟩
    obtain ⟨hxV, hyV, hr⟩ := sameComponent_iff.mp hxy
    rw [SimpleGraph.reachable_iff_reflTransGen] at hr
    suffices hS : ∀ w : H.verts, Relation.ReflTransGen H.coe.Adj ⟨x, hxV⟩ w →
        sameComponent H x w.1 ∧ sameComponent H' x w.1 from (hS ⟨y, hyV⟩ hr).2
    intro w hw
    induction hw with
    | refl => exact ⟨sameComponent_iff.mpr ⟨hxV, hxV, SimpleGraph.Reachable.refl _⟩,
        sameComponent_iff.mpr ⟨hxH', hxH', SimpleGraph.Reachable.refl _⟩⟩
    | @tail a b _ hab ih =>
      have hab' : H.Adj a.1 b.1 := hab
      have h₁ := ih.1.trans (sameComponent_of_adj hab')
      refine ⟨h₁, ih.2.trans (sameComponent_of_adj ?_)⟩
      obtain ⟨e, he, h₂⟩ := realizationOf_adj.mp hab'
      exact realizationOf_adj.mpr ⟨e, he, h₂, hnoW ih.1, hnoW h₁⟩

/-- Graph Minors XX, (7.1) (page 346): "Let $P = (G, \mu, \Delta)$ be a free patchwork and $W
\subseteq \bar{\pi}(G)$. Let $K$ be a
grouping with $V(K) = \bar{\pi}(G) \setminus W$. Then $K$ is feasible in $P/W$ if and only
if $K \cup N_W$ is feasible in $P$." -/
theorem theorem_7_1_proof {P : Patchwork Ω α β} (hfree : IsFree P) {W : Set α}
  (hW : W ⊆ P.G.rootSet)
    {K : (⊤ : SimpleGraph α).Subgraph} (hg : IsGrouping (P.G.rootSet \ W) K)
    (hv : K.verts = P.G.rootSet \ W) :
    IsFeasibleGrouping (P.slash W) K ↔ IsFeasibleGrouping P (K ⊔ emptySubgraph W) :=
  ⟨feasible_of_feasible_slash hW, feasible_slash_of_feasible hfree hW hg hv⟩

end GraphMinor.GM20
