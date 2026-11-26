/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM04.Patchwork.Stars
public import LeanPool.GraphMinor.GM18.Section4
import LeanPool.GraphMinor.GM04.Patchwork.Menger

/-!
# Graph Minors XVIII, Section 5 (Part 1): Patchworks, Feasible Groupings, and Hearts

This file formalizes the first part of Section 5 (pages 89–95) of Robertson and Seymour,
*Graph Minors. XVIII. Tree-decompositions and well-quasi-ordering*, J. Combin. Theory Ser. B 89
(2003) 77–108:

* `theorem_5_1_proof` (5.1, page 91, with Claim (1) `lemma_5_1_claim_1`): gluing realizations
  across a common separation `(Gᵢ', G₀)` preserves connectivity on `V(G₀)` when connectivity on
  `πBar(G₁') = πBar(G₂')` agrees and the patches on `G₀` agree.
* `theorem_5_2_proof` (5.2, page 92): inclusion of feasible groupings and agreement on the patches
  of `G₀` transport realizations while preserving connectivity on `V(G₀)`.
* `theorem_5_3_proof` (5.3, page 92): a realizable labelled expansion into `P₁` with edge images
  in `G₀` and vertex images meeting `V(G₀)` gives an expansion into `P₂` with the same edge
  map and the same intersection with `V(G₀)`. The shared edge labels satisfy a pointwise bound.
* `theorem_5_4` (5.4, page 93, with Claim (1) `lemma_5_4_claim_1`): for a patchwork `P`, rooted
  location `ℒ`, and heart `P' = P | ℒ`,
  `V(G) \ πBar(G) = (V(G') \ πBar(G')) ∪ ⋃_{A ∈ ℒ} (V(A) \ πBar(A))` and `gr(P) = gr(P')`.
-/

public section

namespace GraphMinor.GM18

open Hypergraph SimpleGraph

universe u v w

variable {α : Type u} {β : Type v} {Ω : Type w}

/-! ## Basic equivalences for `ConnectedIn` and `GM04.sameComponent` -/

theorem connectedIn_iff {K : (⊤ : SimpleGraph α).Subgraph} {p q : α} :
    ConnectedIn K p q ↔
      ∃ (hp : p ∈ K.verts) (hq : q ∈ K.verts), K.coe.Reachable ⟨p, hp⟩ ⟨q, hq⟩ := by
  constructor
  · rintro ⟨D, hD, hp, hq⟩
    obtain ⟨x, rfl⟩ := hD
    rw [GM04.component_verts, GM04.mem_componentVerts_iff] at hp hq
    exact ⟨hp.1, hq.1, hp.2.symm.trans hq.2⟩
  · rintro ⟨hp, hq, hr⟩
    refine ⟨GM04.component K ⟨p, hp⟩, ⟨⟨p, hp⟩, rfl⟩,
      GM04.self_mem_componentVerts K ⟨p, hp⟩, ?_⟩
    rw [GM04.component_verts, GM04.mem_componentVerts_iff]
    exact ⟨hq, hr⟩

theorem connectedIn_iff_sameComponent {H : (⊤ : SimpleGraph α).Subgraph} {x y : α} :
    ConnectedIn H x y ↔ GM04.sameComponent H x y :=
  connectedIn_iff.trans GM04.sameComponent_iff.symm

theorem ConnectedIn.refl {H : (⊤ : SimpleGraph α).Subgraph} {x : α} (hx : x ∈ H.verts) :
    ConnectedIn H x x :=
  connectedIn_iff.2 ⟨hx, hx, Reachable.refl (⟨x, hx⟩ : H.verts)⟩

theorem ConnectedIn.symm {H : (⊤ : SimpleGraph α).Subgraph} {x y : α}
    (h : ConnectedIn H x y) : ConnectedIn H y x :=
  connectedIn_iff_sameComponent.2 (GM04.sameComponent.symm (connectedIn_iff_sameComponent.1 h))

theorem ConnectedIn.trans {H : (⊤ : SimpleGraph α).Subgraph} {x y z : α}
    (hxy : ConnectedIn H x y) (hyz : ConnectedIn H y z) : ConnectedIn H x z :=
  connectedIn_iff_sameComponent.2
    (GM04.sameComponent.trans (connectedIn_iff_sameComponent.1 hxy)
      (connectedIn_iff_sameComponent.1 hyz))

theorem ConnectedIn.mono {H₁ H₂ : (⊤ : SimpleGraph α).Subgraph} (hle : H₁ ≤ H₂) {x y : α}
    (h : ConnectedIn H₁ x y) : ConnectedIn H₂ x y :=
  connectedIn_iff_sameComponent.2
    (GM04.sameComponent.mono hle (connectedIn_iff_sameComponent.1 h))

theorem connectedIn_of_adj {H : (⊤ : SimpleGraph α).Subgraph} {x y : α} (h : H.Adj x y) :
    ConnectedIn H x y :=
  connectedIn_iff_sameComponent.2 (GM04.sameComponent_of_adj h)

theorem ConnectedIn.verts_left {H : (⊤ : SimpleGraph α).Subgraph} {x y : α}
    (h : ConnectedIn H x y) : x ∈ H.verts :=
  (connectedIn_iff.1 h).1

theorem ConnectedIn.verts_right {H : (⊤ : SimpleGraph α).Subgraph} {x y : α}
    (h : ConnectedIn H x y) : y ∈ H.verts :=
  (connectedIn_iff.1 h).2.1

theorem rootSet_subset (G : RootedHypergraph α β) : G.rootSet ⊆ G.vertexSet :=
  fun v hv ↦ G.roots_subset v hv

/-! ## Realizations and separations -/

private theorem emptySubgraph_sup_emptySubgraph (X Y : Set α) :
    GM04.emptySubgraph X ⊔ GM04.emptySubgraph Y = GM04.emptySubgraph (X ∪ Y) := by
  ext v w
  · rfl
  · simp [GM04.emptySubgraph]

/-- If `(G', G₀)` is a separation of `P.G`, then the union `H₀ ⊔ H'` of a realization `H₀` of
`P | G₀` and a realization `H'` of `P | G'` is a realization of `P`. -/
theorem isRealization_sup_of_isSeparation {P : GM04.Patchwork Ω α β}
    {G' G₀ : RootedHypergraph α β} (hsep : P.G.IsSeparation G' G₀)
    {H₀ H' : (⊤ : SimpleGraph α).Subgraph}
    (hH₀ : (P.restrict G₀).IsRealization H₀)
    (hH' : (P.restrict G').IsRealization H') :
    P.IsRealization (H₀ ⊔ H') := by
  classical
  obtain ⟨δ₀, hδ₀, rfl⟩ := hH₀
  obtain ⟨δ', hδ', rfl⟩ := hH'
  have hle' := hsep.isSeparation.left_le
  have hle₀ := hsep.isSeparation.right_le
  have hdisjE := GM04.isSeparation_disjoint_edgeSet hsep.isSeparation
  let δ : β → (⊤ : SimpleGraph α).Subgraph :=
    fun e ↦ if e ∈ G'.edgeSet then δ' e else δ₀ e
  have he_or : ∀ e ∈ P.G.edgeSet, e ∈ G'.edgeSet ∨ (e ∈ G₀.edgeSet ∧ e ∉ G'.edgeSet) := by
    intro e he
    by_cases he' : e ∈ G'.edgeSet
    · exact Or.inl he'
    · rw [← GM04.isSeparation_edgeSet_union hsep.isSeparation] at he
      rcases he with he'_abs | he₀
      · exact (he' he'_abs).elim
      · exact Or.inr ⟨he₀, he'⟩
  refine ⟨δ, fun e he ↦ ?_, ?_⟩
  · rcases he_or e he with he' | ⟨he₀, hne'⟩
    · simp only [δ, he', ↓reduceIte]
      have hmem := hδ' e he'
      change δ' e ∈ (P.restrict G').Δ e at hmem
      rwa [P.restrict_Δ hle' he'] at hmem
    · simp only [δ, hne', ↓reduceIte]
      have hmem := hδ₀ e he₀
      change δ₀ e ∈ (P.restrict G₀).Δ e at hmem
      rwa [P.restrict_Δ hle₀ he₀] at hmem
  · change (GM04.emptySubgraph G₀.vertexSet ⊔ ⨆ e ∈ G₀.edgeSet, δ₀ e) ⊔
        (GM04.emptySubgraph G'.vertexSet ⊔ ⨆ e ∈ G'.edgeSet, δ' e) =
      GM04.emptySubgraph P.G.vertexSet ⊔ ⨆ e ∈ P.G.edgeSet, δ e
    rw [sup_sup_sup_comm, emptySubgraph_sup_emptySubgraph, Set.union_comm G₀.vertexSet,
      GM04.isSeparation_vertexSet_union hsep.isSeparation]
    congr 1
    apply le_antisymm
    · refine sup_le (iSup₂_le fun e he₀ ↦ ?_) (iSup₂_le fun e he' ↦ ?_)
      · have hne' : e ∉ G'.edgeSet := fun h ↦ Set.disjoint_left.1 hdisjE h he₀
        have hδ_eq : δ₀ e = δ e := by simp [δ, hne']
        rw [hδ_eq]
        exact le_biSup δ (hle₀.edgeSet_subset he₀)
      · have hδ_eq : δ' e = δ e := by simp [δ, he']
        rw [hδ_eq]
        exact le_biSup δ (hle'.edgeSet_subset he')
    · refine iSup₂_le fun e he ↦ ?_
      rcases he_or e he with he' | ⟨he₀, hne'⟩
      · have hδ_eq : δ e = δ' e := by simp [δ, he']
        rw [hδ_eq]
        exact le_sup_of_le_right (le_biSup δ' he')
      · have hδ_eq : δ e = δ₀ e := by simp [δ, hne']
        rw [hδ_eq]
        exact le_sup_of_le_left (le_biSup δ₀ he₀)

/-- Conversely, every realization `H` of `P` splits across a separation `(G', G₀)` of `P.G` as
`H = H₀ ⊔ H'` where `H₀` is a realization of `P | G₀` and `H'` is a realization of `P | G'`. -/
theorem exists_isRealization_split_of_isSeparation {P : GM04.Patchwork Ω α β}
    {G' G₀ : RootedHypergraph α β} (hsep : P.G.IsSeparation G' G₀)
    {H : (⊤ : SimpleGraph α).Subgraph} (hH : P.IsRealization H) :
    ∃ H₀ H' : (⊤ : SimpleGraph α).Subgraph,
      (P.restrict G₀).IsRealization H₀ ∧
      (P.restrict G').IsRealization H' ∧
      H = H₀ ⊔ H' := by
  obtain ⟨δ, hδ, rfl⟩ := hH
  have hle' := hsep.isSeparation.left_le
  have hle₀ := hsep.isSeparation.right_le
  let H₀ := GM04.realizationOf G₀.toHypergraph δ
  let H' := GM04.realizationOf G'.toHypergraph δ
  have hH₀ : (P.restrict G₀).IsRealization H₀ := by
    refine ⟨δ, fun e he ↦ ?_, rfl⟩
    change δ e ∈ ((P.restrict G₀).Δ e).groupings
    rw [P.restrict_Δ hle₀ he]
    exact hδ e (hle₀.edgeSet_subset he)
  have hH' : (P.restrict G').IsRealization H' := by
    refine ⟨δ, fun e he ↦ ?_, rfl⟩
    change δ e ∈ ((P.restrict G').Δ e).groupings
    rw [P.restrict_Δ hle' he]
    exact hδ e (hle'.edgeSet_subset he)
  refine ⟨H₀, H', hH₀, hH', ?_⟩
  change GM04.emptySubgraph P.G.vertexSet ⊔ (⨆ e ∈ P.G.edgeSet, δ e) =
    (GM04.emptySubgraph G₀.vertexSet ⊔ ⨆ e ∈ G₀.edgeSet, δ e) ⊔
      (GM04.emptySubgraph G'.vertexSet ⊔ ⨆ e ∈ G'.edgeSet, δ e)
  rw [sup_sup_sup_comm, emptySubgraph_sup_emptySubgraph, Set.union_comm G₀.vertexSet,
    GM04.isSeparation_vertexSet_union hsep.isSeparation]
  congr 1
  apply le_antisymm
  · refine iSup₂_le fun e he ↦ ?_
    rw [← GM04.isSeparation_edgeSet_union hsep.isSeparation] at he
    rcases he with he' | he₀
    · exact le_sup_of_le_right (le_biSup δ he')
    · exact le_sup_of_le_left (le_biSup δ he₀)
  · exact sup_le
      (iSup₂_le fun e he₀ ↦ le_biSup δ (hle₀.edgeSet_subset he₀))
      (iSup₂_le fun e he' ↦ le_biSup δ (hle'.edgeSet_subset he'))

/-! ## (5.1), (5.2), and (5.3) -/

/-- **Claim (1)** in the proof of Graph Minors XVIII, (5.1) (page 91):
Any walk in `H₀ ⊔ H₁'` between two vertices `x, y ∈ V(G₀)` connects `x` and `y` in `H₀ ⊔ H₂'`,
provided `H₁'` and `H₂'` induce the same connectivity on `πBar(G₁') = πBar(G₂')`.
We prove this by induction on the walk in `H₀ ⊔ H₁'`: each maximal segment outside `E(H₀)` starts
and ends in `V(G₀) ∩ V(G₁') = πBar(G₁')` and lies in `H₁'`. -/
theorem lemma_5_1_claim_1 {P₁ P₂ : GM04.Patchwork Ω α β}
    {G₁' G₂' G₀ : RootedHypergraph α β}
    (hsep₁ : P₁.G.IsSeparation G₁' G₀)
    {H₀ H₁' H₂' : (⊤ : SimpleGraph α).Subgraph}
    (hH₀ : (P₁.restrict G₀).IsRealization H₀)
    (hH₁' : (P₁.restrict G₁').IsRealization H₁')
    (hH₂' : (P₂.restrict G₂').IsRealization H₂')
    (hconn' : ∀ x ∈ G₁'.rootSet, ∀ y ∈ G₁'.rootSet,
      ConnectedIn H₁' x y ↔ ConnectedIn H₂' x y)
    {x y : α} (hx : x ∈ G₀.vertexSet) (hy : y ∈ G₀.vertexSet)
    (hxy : ConnectedIn (H₀ ⊔ H₁') x y) :
    ConnectedIn (H₀ ⊔ H₂') x y := by
  have hV₀ : H₀.verts = G₀.vertexSet := hH₀.verts_eq
  have hV₁' : H₁'.verts = G₁'.vertexSet := hH₁'.verts_eq
  have hV₂' : H₂'.verts = G₂'.vertexSet := hH₂'.verts_eq
  have hH₂_verts : (H₀ ⊔ H₂').verts = G₀.vertexSet ∪ G₂'.vertexSet := by
    change H₀.verts ∪ H₂'.verts = _
    rw [hV₀, hV₂']
  obtain ⟨hx₁, hy₁, ⟨w⟩⟩ := connectedIn_iff.1 hxy
  -- Generalize to any walk `w` in `(H₀ ⊔ H₁').coe` ending at `y ∈ V(G₀)` from any `u`:
  -- if `u ∈ V(G₀)`, then `ConnectedIn (H₀ ⊔ H₂') u y`; if `u ∈ V(G₁')`, and `z ∈ V(G₀) ∩ V(G₁')`
  -- is connected to `u` in `H₁'`, then `ConnectedIn (H₀ ⊔ H₂') z y`.
  suffices hwalk : ∀ (u v : (H₀ ⊔ H₁').verts) (p : (H₀ ⊔ H₁').coe.Walk u v),
      v.1 ∈ G₀.vertexSet →
      (u.1 ∈ G₀.vertexSet → ConnectedIn (H₀ ⊔ H₂') u.1 v.1) ∧
      (∀ z ∈ G₁'.rootSet, ConnectedIn H₁' z u.1 → ConnectedIn (H₀ ⊔ H₂') z v.1) from
    (hwalk ⟨x, hx₁⟩ ⟨y, hy₁⟩ w hy).1 hx
  intro u v p
  induction p with
  | @nil a =>
    intro ha₀
    have ha_H₂ : a.1 ∈ (H₀ ⊔ H₂').verts := hH₂_verts.symm ▸ Or.inl ha₀
    refine ⟨fun _ ↦ ConnectedIn.refl ha_H₂, fun z hz hzu ↦ ?_⟩
    have ha₁' : a.1 ∈ G₁'.vertexSet := hV₁' ▸ hzu.verts_right
    have ha_root : a.1 ∈ G₁'.rootSet := by
      rw [hsep₁.rootSet_left]
      exact ⟨ha₁', ha₀⟩
    exact ((hconn' z hz a.1 ha_root).1 hzu).mono le_sup_right
  | @cons a b c hab q ih =>
    intro hc₀
    have ⟨ih_G₀, ih_root⟩ := ih hc₀
    have hab' : H₀.Adj a.1 b.1 ∨ H₁'.Adj a.1 b.1 := Subgraph.sup_adj.1 hab
    rcases hab' with hab₀ | hab₁'
    · -- The step from `a` to `b` is an edge of `H₀`, so both `a` and `b` lie in `V(G₀)`.
      have ha₀ : a.1 ∈ G₀.vertexSet := hV₀ ▸ H₀.edge_vert hab₀
      have hb₀ : b.1 ∈ G₀.vertexSet := hV₀ ▸ H₀.edge_vert hab₀.symm
      have hab_H₂ : ConnectedIn (H₀ ⊔ H₂') a.1 b.1 :=
        (connectedIn_of_adj hab₀).mono le_sup_left
      have hbc_H₂ : ConnectedIn (H₀ ⊔ H₂') b.1 c.1 := ih_G₀ hb₀
      have hac_H₂ : ConnectedIn (H₀ ⊔ H₂') a.1 c.1 := hab_H₂.trans hbc_H₂
      refine ⟨fun _ ↦ hac_H₂, fun z hz hza ↦ ?_⟩
      have ha₁' : a.1 ∈ G₁'.vertexSet := hV₁' ▸ hza.verts_right
      have ha_root : a.1 ∈ G₁'.rootSet := by
        rw [hsep₁.rootSet_left]
        exact ⟨ha₁', ha₀⟩
      have hza_H₂ : ConnectedIn (H₀ ⊔ H₂') z a.1 :=
        ((hconn' z hz a.1 ha_root).1 hza).mono le_sup_right
      exact hza_H₂.trans hac_H₂
    · -- The step from `a` to `b` is an edge of `H₁'`.
      have ha₁' : a.1 ∈ G₁'.vertexSet := hV₁' ▸ H₁'.edge_vert hab₁'
      have hab_conn : ConnectedIn H₁' a.1 b.1 := connectedIn_of_adj hab₁'
      refine ⟨fun ha₀ ↦ ?_, fun z hz hza ↦ ih_root z hz (hza.trans hab_conn)⟩
      have ha_root : a.1 ∈ G₁'.rootSet := by
        rw [hsep₁.rootSet_left]
        exact ⟨ha₁', ha₀⟩
      exact ih_root a.1 ha_root hab_conn

/-- **Graph Minors XVIII, (5.1)** (page 91):
"For $i = 1, 2$ let $P_i = (G_i, \mu_i, \Delta_i)$ be a patchwork, and let $(G_i', G_0)$ be a
separation of $G_i$. Let $\pi(G_1') = \pi(G_2')$, and let $P_1|G_0 = P_2|G_0$. For $i = 1,
2$ let $H_i'$ be a realization of $P_i|G_i'$, such that for $x, y \in \bar{\pi}(G_1') =
\bar{\pi}(G_2')$, $x$ and $y$ are connected in $H_1'$ if and only if they are connected in
$H_2'$. Let $H_0$ be a realization of $P_1|G_0 = P_2|G_0$, and let $H_i = H_0 \cup H_i'$ ($i
= 1, 2$). Then for $i = 1, 2, H_i$ is a realization of $P_i$, and for $x, y \in V(G_0)$, $x$
and $y$ are connected in $H_1$ if and only if they are connected in $H_2$."

The Lean version assumes equality of the patches `Δ e` on each edge of the common piece `G₀`.
The printed statement assumes equality of the entire restricted patchworks there. -/
theorem theorem_5_1_proof {P₁ P₂ : GM04.Patchwork Ω α β}
    {G₁' G₂' G₀ : RootedHypergraph α β}
    (hsep₁ : P₁.G.IsSeparation G₁' G₀)
    (hsep₂ : P₂.G.IsSeparation G₂' G₀)
    (hroots : G₁'.roots = G₂'.roots)
    (hG₀ : ∀ e ∈ G₀.edgeSet, (P₁.restrict G₀).Δ e = (P₂.restrict G₀).Δ e)
    {H₀ H₁' H₂' : (⊤ : SimpleGraph α).Subgraph}
    (hH₀ : (P₁.restrict G₀).IsRealization H₀)
    (hH₁' : (P₁.restrict G₁').IsRealization H₁')
    (hH₂' : (P₂.restrict G₂').IsRealization H₂')
    (hconn' : ∀ x ∈ G₁'.rootSet, ∀ y ∈ G₁'.rootSet,
      ConnectedIn H₁' x y ↔ ConnectedIn H₂' x y) :
    P₁.IsRealization (H₀ ⊔ H₁') ∧
    P₂.IsRealization (H₀ ⊔ H₂') ∧
    ∀ x ∈ G₀.vertexSet, ∀ y ∈ G₀.vertexSet,
      ConnectedIn (H₀ ⊔ H₁') x y ↔ ConnectedIn (H₀ ⊔ H₂') x y := by
  have hrootSet : G₁'.rootSet = G₂'.rootSet := by
    ext v
    simp [RootedHypergraph.rootSet, hroots]
  have hH₀₂ : (P₂.restrict G₀).IsRealization H₀ := by
    obtain ⟨δ₀, hδ₀, rfl⟩ := hH₀
    refine ⟨δ₀, fun e he ↦ ?_, rfl⟩
    change δ₀ e ∈ ((P₂.restrict G₀).Δ e).groupings
    rw [← hG₀ e he]
    exact hδ₀ e he
  refine ⟨isRealization_sup_of_isSeparation hsep₁ hH₀ hH₁',
    isRealization_sup_of_isSeparation hsep₂ hH₀₂ hH₂',
    fun x hx y hy ↦ ⟨lemma_5_1_claim_1 hsep₁ hH₀ hH₁' hH₂' hconn' hx hy,
      lemma_5_1_claim_1 hsep₂ hH₀₂ hH₂' hH₁'
        (fun a ha b hb ↦ (hconn' a (hrootSet.symm ▸ ha) b (hrootSet.symm ▸ hb)).symm) hx hy⟩⟩

/-- From any realization `H` of `P`, the induced connectivity on `πBar(G)` is a feasible grouping in
`P`. -/
theorem exists_isFeasibleGrouping_of_isRealization {P : GM04.Patchwork Ω α β}
    {H : (⊤ : SimpleGraph α).Subgraph} (hH : P.IsRealization H) :
    ∃ K ∈ feasibleGroupings P,
      ∀ x ∈ P.G.rootSet, ∀ y ∈ P.G.rootSet, x ≠ y → (ConnectedIn H x y ↔ K.Adj x y) := by
  let K : (⊤ : SimpleGraph α).Subgraph :=
    { verts := P.G.rootSet
      Adj x y := x ∈ P.G.rootSet ∧ y ∈ P.G.rootSet ∧ x ≠ y ∧ ConnectedIn H x y
      adj_sub h := h.2.2.1
      edge_vert h := h.1
      symm := ⟨fun _ _ ⟨hx, hy, hne, hconn⟩ ↦ ⟨hy, hx, hne.symm, hconn.symm⟩⟩ }
  have hgrp : GM04.IsGrouping P.G.rootSet K := by
    rw [GM04.isGrouping_iff]
    refine ⟨subset_rfl, fun a b c hac ⟨ha, _, _, hab⟩ ⟨_, hc, _, hbc⟩ ↦
      ⟨ha, hc, hac, hab.trans hbc⟩⟩
  have hfeas : IsFeasibleGrouping P K :=
    ⟨hgrp, rfl, H, hH, fun x hx y hy hne ↦ ⟨fun h ↦ ⟨hx, hy, hne, h⟩, fun h ↦ h.2.2.2⟩⟩
  exact ⟨K, hfeas, fun x hx y hy hne ↦ ⟨fun h ↦ ⟨hx, hy, hne, h⟩, fun h ↦ h.2.2.2⟩⟩

/-- **Graph Minors XVIII, (5.2)** (page 92):
"For $i = 1, 2$ let $P_i = (G_i, \mu_i, \Delta_i)$ be a patchwork, and let $(G_i', G_0)$ be a
separation of $G_i$, such that $\pi(G_1') = \pi(G_2')$, $P_1|G_0 = P_2|G_0$, and
$gr(P_1|G_1') \subseteq gr(P_2|G_2')$. Then for every realization $H_1$ of $P_1$ there is a
realization $H_2$ of $P_2$ such that for $x, y \in V(G_0)$, $x$ and $y$ are connected in
$H_1$ if and only if they are connected in $H_2$."

As in the Lean version of (5.1), the common-piece hypothesis compares the patches `Δ e` on
each edge of `G₀`. -/
theorem theorem_5_2_proof {P₁ P₂ : GM04.Patchwork Ω α β}
    {G₁' G₂' G₀ : RootedHypergraph α β}
    (hsep₁ : P₁.G.IsSeparation G₁' G₀)
    (hsep₂ : P₂.G.IsSeparation G₂' G₀)
    (hroots : G₁'.roots = G₂'.roots)
    (hG₀ : ∀ e ∈ G₀.edgeSet, (P₁.restrict G₀).Δ e = (P₂.restrict G₀).Δ e)
    (hgr : (feasibleGroupings (P₁.restrict G₁')).groupings ⊆
      (feasibleGroupings (P₂.restrict G₂')).groupings)
    {H₁ : (⊤ : SimpleGraph α).Subgraph} (hH₁ : P₁.IsRealization H₁) :
    ∃ H₂ : (⊤ : SimpleGraph α).Subgraph,
      P₂.IsRealization H₂ ∧
      ∀ x ∈ G₀.vertexSet, ∀ y ∈ G₀.vertexSet,
        ConnectedIn H₁ x y ↔ ConnectedIn H₂ x y := by
  obtain ⟨H₀, H₁', hH₀, hH₁', rfl⟩ := exists_isRealization_split_of_isSeparation hsep₁ hH₁
  obtain ⟨K, hK₁, hK_adj⟩ := exists_isFeasibleGrouping_of_isRealization hH₁'
  have hK₂ : IsFeasibleGrouping (P₂.restrict G₂') K := hgr hK₁
  obtain ⟨_, _, H₂', hH₂', hH₂'_adj⟩ := hK₂
  have hrootSet : G₁'.rootSet = G₂'.rootSet := by
    ext v
    simp [RootedHypergraph.rootSet, hroots]
  have hconn' : ∀ x ∈ G₁'.rootSet, ∀ y ∈ G₁'.rootSet,
      ConnectedIn H₁' x y ↔ ConnectedIn H₂' x y := by
    intro x hx y hy
    by_cases hne : x = y
    · subst hne
      have hx₁ : x ∈ H₁'.verts :=
        hH₁'.verts_eq.symm ▸ rootSet_subset G₁' hx
      have hx₂ : x ∈ H₂'.verts :=
        hH₂'.verts_eq.symm ▸ rootSet_subset G₂' (hrootSet ▸ hx)
      exact ⟨fun _ ↦ ConnectedIn.refl hx₂, fun _ ↦ ConnectedIn.refl hx₁⟩
    · exact (hK_adj x hx y hy hne).trans
        (hH₂'_adj x (hrootSet ▸ hx) y (hrootSet ▸ hy) hne).symm
  have ⟨_, hH₂, hconn⟩ := theorem_5_1_proof hsep₁ hsep₂ hroots hG₀ hH₀ hH₁' hH₂' hconn'
  exact ⟨H₀ ⊔ H₂', hH₂, hconn⟩

private theorem separation_delete_right_edges {P : GM04.Patchwork Ω α β}
    {L R : RootedHypergraph α β} (hsep : P.G.IsSeparation L R)
    {F : Set β} (hF_sub : F ⊆ R.edgeSet) :
    (P.deleteEdges F).G.IsSeparation L (R.deleteEdges F) := by
  have hL := hsep.isSeparation.left_le
  have hR := hsep.isSeparation.right_le
  have hdisjoint := GM04.isSeparation_disjoint_edgeSet hsep.isSeparation
  refine ⟨⟨⟨hL.vertexSet_subset, ?_, ?_⟩,
    ⟨hR.vertexSet_subset, Set.sdiff_subset_sdiff hR.edgeSet_subset subset_rfl, ?_⟩,
    ?_, ?_⟩, hsep.roots_right, hsep.rootSet_left⟩
  · intro e he
    exact ⟨hL.edgeSet_subset he, fun hF ↦ Set.disjoint_left.1 hdisjoint he (hF_sub hF)⟩
  · intro e he
    ext v
    change (P.G.Inc e v ∧ e ∉ F) ↔ L.Inc e v
    have hneF : e ∉ F := fun hF ↦ Set.disjoint_left.1 hdisjoint he (hF_sub hF)
    exact ⟨fun h ↦ (GM10.inc_iff_of_le hL he).2 h.1,
      fun h ↦ ⟨(GM10.inc_iff_of_le hL he).1 h, hneF⟩⟩
  · intro e he
    ext v
    change (P.G.Inc e v ∧ e ∉ F) ↔ (R.Inc e v ∧ e ∉ F)
    exact and_congr_left fun _ ↦ (GM10.inc_iff_of_le hR he.1).symm
  · apply Hypergraph.ext (GM04.isSeparation_vertexSet_union hsep.isSeparation)
    · ext e
      change e ∈ L.edgeSet ∨ (e ∈ R.edgeSet ∧ e ∉ F) ↔ e ∈ P.G.edgeSet ∧ e ∉ F
      rw [← GM04.isSeparation_edgeSet_union hsep.isSeparation]
      simp only [Set.mem_union]
      constructor
      · rintro (he₁' | ⟨he₀, hneF⟩)
        · exact ⟨Or.inl he₁', fun hF ↦ Set.disjoint_left.1 hdisjoint he₁' (hF_sub hF)⟩
        · exact ⟨Or.inr he₀, hneF⟩
      · rintro ⟨he₁' | he₀, hneF⟩
        · exact Or.inl he₁'
        · exact Or.inr ⟨he₀, hneF⟩
    · ext e v
      change (L.Inc e v ∨ (R.Inc e v ∧ e ∉ F)) ↔ (P.G.Inc e v ∧ e ∉ F)
      constructor
      · rintro (h₁ | ⟨h₀, hneF⟩)
        · have he₁' : e ∈ L.edgeSet := L.edge_mem_of_inc h₁
          exact ⟨GM10.inc_of_le hL h₁,
            fun hF ↦ Set.disjoint_left.1 hdisjoint he₁' (hF_sub hF)⟩
        · exact ⟨GM10.inc_of_le hR h₀, hneF⟩
      · rintro ⟨hP, hneF⟩
        have he : e ∈ L.edgeSet ∪ R.edgeSet := by
          rw [GM04.isSeparation_edgeSet_union hsep.isSeparation]
          exact P.G.edge_mem_of_inc hP
        rcases he with he₁' | he₀
        · exact Or.inl ((GM10.inc_iff_of_le hL he₁').2 hP)
        · exact Or.inr ⟨(GM10.inc_iff_of_le hR he₀).2 hP, hneF⟩
  · ext e
    change e ∈ L.edgeSet ∧ (e ∈ R.edgeSet ∧ e ∉ F) ↔ False
    simp only [iff_false, not_and]
    intro he₁' he₀ _
    exact Set.disjoint_left.1 hdisjoint he₁' he₀

/-- **Graph Minors XVIII, (5.3)** (page 92):
"For $i = 1, 2$ let $P_i = (G_i, \mu_i, \Delta_i)$ be a patchwork, and let $(G_i', G_0)$ be a
separation of $G_i$, such that $\pi(G_1') = \pi(G_2')$, $P_1|G_0 = P_2|G_0$, and
$gr(P_1|G_1') \subseteq gr(P_2|G_2')$. Let $\eta_1$ be a realizable expansion of some
patchwork $P = (G, \mu, \Delta)$ in $P_1$ such that $\eta_1(e) \in E(G_0)$ for every $e \in
E(G)$ and $\eta_1(v) \cap V(G_0) \ne \emptyset$ for each $v \in V(G)$. Then there is a
realizable expansion $\eta_2$ of $P$ in $P_2$ such that $\eta_2(e) = \eta_1(e)$ for each $e
\in E(G)$, and $\eta_2(v) \cap V(G_0) = \eta_1(v) \cap V(G_0)$ for each $v \in V(G)$."

The Lean version permits labels from a preorder. On the common piece `G₀`, the marked-edge
domains agree, the markings `μ` agree at each marked edge, and the patches `Δ` agree at each
edge. For each edge of `G₀`, the label in `P₁` is bounded above by the label in `P₂`. -/
theorem theorem_5_3_proof [Preorder Ω] {α₀ β₀ : Type*}
    {P : GM04.Patchwork Ω α₀ β₀} {P₁ P₂ : GM04.Patchwork Ω α β}
    {G₁' G₂' G₀ : RootedHypergraph α β}
    (hsep₁ : P₁.G.IsSeparation G₁' G₀)
    (hsep₂ : P₂.G.IsSeparation G₂' G₀)
    (hroots : G₁'.roots = G₂'.roots)
    (hG₀_dom : ∀ e ∈ G₀.edgeSet, e ∈ P₁.dom ↔ e ∈ P₂.dom)
    (hG₀_μ : ∀ e ∈ G₀.edgeSet, e ∈ P₁.dom → P₁.μ e = P₂.μ e)
    (hG₀_Δ : ∀ e ∈ G₀.edgeSet, P₁.Δ e = P₂.Δ e)
    (hG₀_φ : ∀ e ∈ G₀.edgeSet, P₁.φ e ≤ P₂.φ e)
    (hgr : (feasibleGroupings (P₁.restrict G₁')).groupings ⊆
      (feasibleGroupings (P₂.restrict G₂')).groupings)
    {η₁v : α₀ → Set α} {η₁e : β₀ → β}
    (hη₁ : GM04.IsRealizableExpansion P P₁ η₁v η₁e)
    (he_G₀ : ∀ e ∈ P.G.edgeSet, η₁e e ∈ G₀.edgeSet)
    (hv_G₀ : ∀ v ∈ P.G.vertexSet, (η₁v v ∩ G₀.vertexSet).Nonempty) :
    ∃ η₂v : α₀ → Set α,
      GM04.IsRealizableExpansion P P₂ η₂v η₁e ∧
      ∀ v ∈ P.G.vertexSet, η₂v v ∩ G₀.vertexSet = η₁v v ∩ G₀.vertexSet := by
  classical
  obtain ⟨hexp₁, H₁, hreal₁, hcomp₁⟩ := hη₁
  have hle₀₁ := hsep₁.isSeparation.right_le
  have hle₀₂ := hsep₂.isSeparation.right_le
  have hle₁' := hsep₁.isSeparation.left_le
  have hle₂' := hsep₂.isSeparation.left_le
  let F : Set β := η₁e '' P.G.edgeSet
  have hF_sub : F ⊆ G₀.edgeSet := by
    rintro _ ⟨e, he, rfl⟩
    exact he_G₀ e he
  let G₀_del : RootedHypergraph α β := G₀.deleteEdges F
  have hsep₁_del : (P₁.deleteEdges F).G.IsSeparation G₁' G₀_del :=
    separation_delete_right_edges hsep₁ hF_sub
  have hsep₂_del : (P₂.deleteEdges F).G.IsSeparation G₂' G₀_del :=
    separation_delete_right_edges hsep₂ hF_sub
  have hG₀_del_Δ : ∀ e ∈ G₀_del.edgeSet,
      ((P₁.deleteEdges F).restrict G₀_del).Δ e = ((P₂.deleteEdges F).restrict G₀_del).Δ e := by
    intro e he
    rw [(P₁.deleteEdges F).restrict_Δ hsep₁_del.isSeparation.right_le he,
      (P₂.deleteEdges F).restrict_Δ hsep₂_del.isSeparation.right_le he]
    exact hG₀_Δ e he.1
  have hgr_del :
      (feasibleGroupings ((P₁.deleteEdges F).restrict G₁')).groupings ⊆
        (feasibleGroupings ((P₂.deleteEdges F).restrict G₂')).groupings := by
    have hreal_iff : ∀ (P' : GM04.Patchwork Ω α β) (G' : RootedHypergraph α β)
        (hle' : G'.toHypergraph ≤ P'.G.toHypergraph)
        (hle'_del : G'.toHypergraph ≤ (P'.deleteEdges F).G.toHypergraph)
        (H : (⊤ : SimpleGraph α).Subgraph),
        ((P'.deleteEdges F).restrict G').IsRealization H ↔ (P'.restrict G').IsRealization H := by
      intro P' G' hle' hle'_del H
      refine ⟨fun ⟨δ, hδ, hH⟩ ↦ ⟨δ, fun e he ↦ ?_, hH⟩,
        fun ⟨δ, hδ, hH⟩ ↦ ⟨δ, fun e he ↦ ?_, hH⟩⟩
      · have h := hδ e he
        change δ e ∈ ((P'.deleteEdges F).restrict G').Δ e at h
        rw [(P'.deleteEdges F).restrict_Δ hle'_del he] at h
        change δ e ∈ (P'.restrict G').Δ e
        rw [P'.restrict_Δ hle' he]
        exact h
      · have h := hδ e he
        change δ e ∈ (P'.restrict G').Δ e at h
        rw [P'.restrict_Δ hle' he] at h
        change δ e ∈ ((P'.deleteEdges F).restrict G').Δ e
        rw [(P'.deleteEdges F).restrict_Δ hle'_del he]
        exact h
    intro K hK
    rcases hK with ⟨hgrp, hverts, H, hH, hconn⟩
    have hK₁ : IsFeasibleGrouping (P₁.restrict G₁') K :=
      ⟨hgrp, hverts, H, (hreal_iff P₁ G₁' hle₁' hsep₁_del.isSeparation.left_le H).1 hH, hconn⟩
    obtain ⟨hgrp₂, hverts₂, H₂', hH₂', hconn₂'⟩ := hgr hK₁
    exact ⟨hgrp₂, hverts₂, H₂',
      (hreal_iff P₂ G₂' hle₂' hsep₂_del.isSeparation.left_le H₂').2 hH₂', hconn₂'⟩
  -- Apply (5.2) to `P₁ \ F` and `P₂ \ F` to get a realization `H₂` of `P₂ \ F`.
  obtain ⟨H₂, hH₂, hconn_G₀⟩ :=
    theorem_5_2_proof hsep₁_del hsep₂_del hroots hG₀_del_Δ hgr_del hreal₁
  have hH₁_verts : H₁.verts = P₁.G.vertexSet := hreal₁.verts_eq
  have hH₂_verts : H₂.verts = P₂.G.vertexSet := hH₂.verts_eq
  -- For each `v ∈ V(G)`, choose a witness `w₀(v) ∈ η₁(v) ∩ V(G₀)` and define `η₂(v)` as the
  -- vertex set of the component of `H₂` containing `w₀(v)`.
  let η₂v : α₀ → Set α := fun v ↦
    if hv : v ∈ P.G.vertexSet then
      let w₀ := (hv_G₀ v hv).choose
      have hw₀_G₀ : w₀ ∈ G₀.vertexSet := (hv_G₀ v hv).choose_spec.2
      have hw₀_H₂ : w₀ ∈ H₂.verts := hH₂_verts.symm ▸ hle₀₂.vertexSet_subset hw₀_G₀
      (GM04.component H₂ ⟨w₀, hw₀_H₂⟩).verts
    else ∅
  have hη₂_comp : ∀ v ∈ P.G.vertexSet,
      (∃ D, GM04.IsComponent H₂ D ∧ D.verts = η₂v v) ∧
      η₂v v ∩ G₀.vertexSet = η₁v v ∩ G₀.vertexSet := by
    intro v hv
    let w₀ := (hv_G₀ v hv).choose
    have hw₀_η₁ : w₀ ∈ η₁v v := (hv_G₀ v hv).choose_spec.1
    have hw₀_G₀ : w₀ ∈ G₀.vertexSet := (hv_G₀ v hv).choose_spec.2
    have hw₀_H₂ : w₀ ∈ H₂.verts := hH₂_verts.symm ▸ hle₀₂.vertexSet_subset hw₀_G₀
    have hη₂_eq : η₂v v = (GM04.component H₂ ⟨w₀, hw₀_H₂⟩).verts := by
      simp only [η₂v, hv, ↓reduceDIte]
      rfl
    obtain ⟨D₁, hD₁, hD₁_verts⟩ := hcomp₁ v hv
    refine ⟨⟨GM04.component H₂ ⟨w₀, hw₀_H₂⟩, ⟨⟨w₀, hw₀_H₂⟩, rfl⟩, hη₂_eq.symm⟩, ?_⟩
    rw [hη₂_eq]
    ext x
    simp only [Set.mem_inter_iff, GM04.component_verts, GM04.mem_componentVerts_iff]
    constructor
    · rintro ⟨⟨hx_H₂, hreach₂⟩, hx_G₀⟩
      have hconn₂ : ConnectedIn H₂ w₀ x :=
        connectedIn_iff.2 ⟨hw₀_H₂, hx_H₂, hreach₂⟩
      have hconn₁ : ConnectedIn H₁ w₀ x := (hconn_G₀ w₀ hw₀_G₀ x hx_G₀).2 hconn₂
      obtain ⟨D₁', hD₁', hw₀_D₁', hx_D₁'⟩ := hconn₁
      have hD_eq : D₁' = D₁ := hD₁'.eq_of_mem hD₁ hw₀_D₁' (hD₁_verts ▸ hw₀_η₁)
      exact ⟨hD₁_verts ▸ hD_eq ▸ hx_D₁', hx_G₀⟩
    · rintro ⟨hx_η₁, hx_G₀⟩
      have hconn₁ : ConnectedIn H₁ w₀ x :=
        ⟨D₁, hD₁, hD₁_verts.symm ▸ hw₀_η₁, hD₁_verts.symm ▸ hx_η₁⟩
      have hconn₂ : ConnectedIn H₂ w₀ x := (hconn_G₀ w₀ hw₀_G₀ x hx_G₀).1 hconn₁
      obtain ⟨_, hx_H₂, hreach₂⟩ := connectedIn_iff.1 hconn₂
      exact ⟨⟨hx_H₂, hreach₂⟩, hx_G₀⟩
  refine ⟨η₂v, ⟨?_, H₂, hH₂, fun v hv ↦ (hη₂_comp v hv).1⟩, fun v hv ↦ (hη₂_comp v hv).2⟩
  refine
    { vertex_nonempty := fun v hv ↦ by
        obtain ⟨D, hD, hD_eq⟩ := (hη₂_comp v hv).1
        exact hD_eq ▸ hD.verts_nonempty
      vertex_subset := fun v hv ↦ by
        obtain ⟨D, hD, hD_eq⟩ := (hη₂_comp v hv).1
        rw [← hD_eq, ← hH₂_verts]
        exact hD.le.1
      edge_mem := fun e he ↦ hle₀₂.edgeSet_subset (he_G₀ e he)
      vertex_disjoint := fun v₁ hv₁ v₂ hv₂ hne ↦ by
        obtain ⟨D₁, hD₁, hD₁_eq⟩ := (hη₂_comp v₁ hv₁).1
        obtain ⟨D₂, hD₂, hD₂_eq⟩ := (hη₂_comp v₂ hv₂).1
        rw [← hD₁_eq, ← hD₂_eq]
        refine hD₁.disjoint_verts_of_ne hD₂ fun hEq ↦ ?_
        obtain ⟨w, hw₁, hw₀⟩ := hv_G₀ v₁ hv₁
        have hw_D₁ : w ∈ D₁.verts ∩ G₀.vertexSet := by
          rw [hD₁_eq, (hη₂_comp v₁ hv₁).2]
          exact ⟨hw₁, hw₀⟩
        have hw_D₂ : w ∈ η₂v v₂ ∩ G₀.vertexSet := by
          rw [← hD₂_eq, ← hEq]
          exact hw_D₁
        rw [(hη₂_comp v₂ hv₂).2] at hw_D₂
        exact Set.disjoint_left.1 (hexp₁.vertex_disjoint v₁ hv₁ v₂ hv₂ hne) hw₁ hw_D₂.1
      edge_injOn := hexp₁.edge_injOn
      mem_dom_iff := fun e he ↦
        (hexp₁.mem_dom_iff e he).trans (hG₀_dom (η₁e e) (he_G₀ e he))
      ends_nonempty := fun e he hnd v hinc ↦ by
        obtain ⟨v', hv', hinc₁⟩ := hexp₁.ends_nonempty e he hnd v hinc
        have he₀ : η₁e e ∈ G₀.edgeSet := he_G₀ e he
        have hinc₀ : G₀.Inc (η₁e e) v' := (GM10.inc_iff_of_le hle₀₁ he₀).2 hinc₁
        have hv'_G₀ : v' ∈ G₀.vertexSet := G₀.vertex_mem_of_inc hinc₀
        have hv'_η₂ : v' ∈ η₂v v ∩ G₀.vertexSet := by
          rw [(hη₂_comp v (P.G.vertex_mem_of_inc hinc)).2]
          exact ⟨hv', hv'_G₀⟩
        exact ⟨v', hv'_η₂.1, GM10.inc_of_le hle₀₂ hinc₀⟩
      μ_length := fun e he ↦ by
        have heE : e ∈ P.G.edgeSet := P.dom_subset he
        have he₀ : η₁e e ∈ G₀.edgeSet := he_G₀ e heE
        have he₁_dom : η₁e e ∈ P₁.dom := (hexp₁.mem_dom_iff e heE).1 he
        rw [← hG₀_μ (η₁e e) he₀ he₁_dom]
        exact hexp₁.μ_length e he
      μ_mem := fun e he i hi hi₂ ↦ by
        have heE : e ∈ P.G.edgeSet := P.dom_subset he
        have he₀ : η₁e e ∈ G₀.edgeSet := he_G₀ e heE
        have he₁_dom : η₁e e ∈ P₁.dom := (hexp₁.mem_dom_iff e heE).1 he
        have hi₁ : i < (P₁.μ (η₁e e)).length := (hG₀_μ (η₁e e) he₀ he₁_dom).symm ▸ hi₂
        have hmem₁ : (P₁.μ (η₁e e))[i] ∈ η₁v (P.μ e)[i] := hexp₁.μ_mem e he i hi hi₁
        have hv'_inc₁ : P₁.G.Inc (η₁e e) (P₁.μ (η₁e e))[i] := by
          change (P₁.μ (η₁e e))[i] ∈ P₁.G.ends (η₁e e)
          rw [← P₁.μ_set (η₁e e) he₁_dom]
          exact List.getElem_mem hi₁
        have hv'_G₀ : (P₁.μ (η₁e e))[i] ∈ G₀.vertexSet :=
          G₀.vertex_mem_of_inc ((GM10.inc_iff_of_le hle₀₁ he₀).2 hv'_inc₁)
        have hv_V : (P.μ e)[i] ∈ P.G.vertexSet := by
          apply P.G.vertex_mem_of_inc
          change (P.μ e)[i] ∈ P.G.ends e
          rw [← P.μ_set e he]
          exact List.getElem_mem hi
        have hmem₂ : (P₁.μ (η₁e e))[i] ∈ η₂v (P.μ e)[i] ∩ G₀.vertexSet := by
          rw [(hη₂_comp (P.μ e)[i] hv_V).2]
          exact ⟨hmem₁, hv'_G₀⟩
        have hEq : (P₂.μ (η₁e e))[i] = (P₁.μ (η₁e e))[i] := by
          simp [hG₀_μ (η₁e e) he₀ he₁_dom]
        rw [hEq]
        exact hmem₂.1
      roots_length := by
        rw [hexp₁.roots_length, ← hsep₁.roots_right, hsep₂.roots_right]
      roots_mem := fun i hi hi₂ ↦ by
        have hroots₁₂ : P₁.G.roots = P₂.G.roots :=
          hsep₁.roots_right.symm.trans hsep₂.roots_right
        have hi₁ : i < P₁.G.roots.length := hroots₁₂.symm ▸ hi₂
        have hmem₁ : P₁.G.roots[i] ∈ η₁v P.G.roots[i] := hexp₁.roots_mem i hi hi₁
        have hv'_G₀ : P₁.G.roots[i] ∈ G₀.vertexSet := by
          have hmem_root : P₁.G.roots[i] ∈ G₀.rootSet := by
            change P₁.G.roots[i] ∈ G₀.roots
            rw [hsep₁.roots_right]
            exact List.getElem_mem hi₁
          exact G₀.roots_subset _ hmem_root
        have hv_V : P.G.roots[i] ∈ P.G.vertexSet := P.G.roots_subset _ (List.getElem_mem hi)
        have hmem₂ : P₁.G.roots[i] ∈ η₂v P.G.roots[i] ∩ G₀.vertexSet := by
          rw [(hη₂_comp P.G.roots[i] hv_V).2]
          exact ⟨hmem₁, hv'_G₀⟩
        have hEq : P₂.G.roots[i] = P₁.G.roots[i] := by simp [hroots₁₂]
        rw [hEq]
        exact hmem₂.1
      maps_Δ := fun e he ↦ by
        have heE : e ∈ P.G.edgeSet := P.dom_subset he
        have he₀ : η₁e e ∈ G₀.edgeSet := he_G₀ e heE
        have he₁_dom : η₁e e ∈ P₁.dom := (hexp₁.mem_dom_iff e heE).1 he
        rw [← hG₀_μ (η₁e e) he₀ he₁_dom, ← hG₀_Δ (η₁e e) he₀]
        exact hexp₁.maps_Δ e he
      φ_le := fun e he ↦ (hexp₁.φ_le e he).trans (hG₀_φ (η₁e e) (he_G₀ e he)) }

/-! ## Complemented subhypergraphs, rooted locations, and (5.4) -/

theorem complementHypergraph_eq_of_isComplemented {G A : RootedHypergraph α β}
    (hA : IsComplemented G A) :
    complementHypergraph G A = (complement G A hA).toHypergraph := by
  have hroot_sub : A.rootSet ⊆ G.vertexSet :=
    (rootSet_subset A).trans hA.le.vertexSet_subset
  ext v e
  · simp [complementHypergraph, complement, Set.inter_eq_right.2 hroot_sub]
  · rfl
  · simp only [complementHypergraph, complement]
    refine ⟨fun h ↦ ⟨h.1, h.2.1⟩, fun h ↦ ⟨h.1, h.2, ?_⟩⟩
    rw [Set.inter_eq_right.2 hroot_sub]
    exact (complement G A hA).vertex_mem_of_inc h

/-- If `A ⊆ G` is complemented in `G`, then `(A, G \ A)` is a separation of `G`
(Graph Minors XVIII, Section 5, page 93). -/
theorem IsComplemented.isSeparation {G A : RootedHypergraph α β}
    (hA : IsComplemented G A) :
    G.IsSeparation A (complement G A hA) where
  isSeparation :=
    { left_le := hA.le
      right_le :=
        { vertexSet_subset :=
            Set.union_subset Set.sdiff_subset ((rootSet_subset A).trans hA.le.vertexSet_subset)
          edgeSet_subset := Set.sdiff_subset
          ends_eq := fun e he ↦ Set.ext fun v ↦ ⟨fun h ↦ ⟨he, h⟩, fun h ↦ h.2⟩ }
      union_eq := by
        refine GM10.eq_of_le_of_vertexSet_eq_of_edgeSet_eq
          (GM10.union_le hA.le
            ⟨Set.union_subset Set.sdiff_subset ((rootSet_subset A).trans hA.le.vertexSet_subset),
              Set.sdiff_subset, fun e he ↦ Set.ext fun v ↦ ⟨fun h ↦ ⟨he, h⟩, fun h ↦ h.2⟩⟩)
          le_rfl ?_ (Set.union_sdiff_cancel hA.le.edgeSet_subset)
        ext v
        simp only [GM10.union_vertexSet, complement, Set.mem_union, Set.mem_sdiff]
        exact ⟨fun h ↦ h.elim (fun hvA ↦ hA.le.vertexSet_subset hvA)
          (fun h2 ↦ h2.elim (fun h1 ↦ h1.1) (fun hr ↦ hA.le.vertexSet_subset
            (A.roots_subset v hr))),
          fun hvG ↦ by
            by_cases hvA : v ∈ A.vertexSet
            · exact Or.inl hvA
            · exact Or.inr (Or.inl ⟨hvG, hvA⟩)⟩
      edgeSet_inter_eq := Set.inter_sdiff_self A.edgeSet G.edgeSet }
  roots_right := rfl
  rootSet_left := by
    ext v
    simp only [GM10.inter_vertexSet, complement, Set.mem_inter_iff, Set.mem_union, Set.mem_sdiff]
    exact ⟨fun hr ↦ ⟨A.roots_subset v hr, Or.inr hr⟩,
      fun ⟨hvA, h⟩ ↦ h.elim (fun hnot ↦ (hnot.2 hvA).elim) id⟩

/-- If `ℒ` is a rooted location in `G`, then `ℒ⁻` (`rootedLocationToLocation G ℒ`) is a location in
`G⁻` (Graph Minors XVIII, Section 5, page 93). -/
theorem IsRootedLocation.isLocation {G : RootedHypergraph α β}
    {ℒ : Set (RootedHypergraph α β)} (hℒ : IsRootedLocation G ℒ) :
    GM10.IsLocation G.toHypergraph (rootedLocationToLocation G ℒ) where
  isSeparation := by
    rintro _ ⟨A, hA, rfl⟩
    dsimp only
    rw [complementHypergraph_eq_of_isComplemented (hℒ.isComplemented hA)]
    exact (hℒ.isComplemented hA).isSeparation.isSeparation
  left_le_right := by
    rintro _ ⟨A₁, hA₁, rfl⟩ _ ⟨A₂, hA₂, rfl⟩ hne
    have hA_ne : A₁ ≠ A₂ := fun hEq ↦ hne (by subst hEq; rfl)
    dsimp only
    rw [complementHypergraph_eq_of_isComplemented (hℒ.isComplemented hA₂)]
    exact hℒ.le_complement hA₁ hA₂ hA_ne

/-- Every rooted location `ℒ` in `G` is finite. -/
theorem IsRootedLocation.finite {G : RootedHypergraph α β}
    {ℒ : Set (RootedHypergraph α β)} (hℒ : IsRootedLocation G ℒ) :
    ℒ.Finite := by
  classical
  let f : RootedHypergraph α β → Hypergraph α β × List α := fun A ↦ (A.toHypergraph, A.roots)
  have hinj : Set.InjOn f ℒ := by
    rintro ⟨H₁, r₁, _, _⟩ _ ⟨H₂, r₂, _, _⟩ _ hEq
    have hH : H₁ = H₂ := congrArg Prod.fst hEq
    have hr : r₁ = r₂ := congrArg Prod.snd hEq
    subst hH hr
    rfl
  have hnodup_fin : {l : List α | l.Nodup ∧ {x | x ∈ l} ⊆ G.vertexSet}.Finite := by
    let _ : Fintype G.vertexSet := G.vertexSet_finite.fintype
    have hlen_le : ∀ l : List α, l.Nodup → {x | x ∈ l} ⊆ G.vertexSet →
        l.length ≤ Fintype.card G.vertexSet := by
      intro l hnodup hsub
      let emb : Fin l.length ↪ G.vertexSet :=
        ⟨fun i ↦ ⟨l[i.1], hsub (List.getElem_mem i.2)⟩,
          fun i j hij ↦ Fin.ext ((hnodup.getElem_inj_iff).1 (congrArg Subtype.val hij))⟩
      have hle := Fintype.card_le_of_embedding emb
      rwa [Fintype.card_fin] at hle
    let g : {l : List α // l.Nodup ∧ {x | x ∈ l} ⊆ G.vertexSet} →
        Fin (Fintype.card G.vertexSet) → Option G.vertexSet :=
      fun ⟨l, _, hsub⟩ i ↦
        if hi : i.1 < l.length then some ⟨l[i.1], hsub (List.getElem_mem hi)⟩ else none
    have hg_inj : Function.Injective g := by
      rintro ⟨l₁, hnodup₁, hsub₁⟩ ⟨l₂, hnodup₂, hsub₂⟩ hEq
      have hlen₁ := hlen_le l₁ hnodup₁ hsub₁
      have hlen₂ := hlen_le l₂ hnodup₂ hsub₂
      have hlen : l₁.length = l₂.length := by
        by_contra hne
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · have hfi := congrFun hEq ⟨l₁.length, lt_of_lt_of_le hlt hlen₂⟩
          simp only [g, lt_irrefl, ↓reduceDIte, hlt] at hfi
          cases hfi
        · have hfi := congrFun hEq ⟨l₂.length, lt_of_lt_of_le hgt hlen₁⟩
          simp only [g, lt_irrefl, ↓reduceDIte, hgt] at hfi
          cases hfi
      apply Subtype.ext
      refine List.ext_getElem hlen fun i hi₁ hi₂ ↦ ?_
      have hfi := congrFun hEq ⟨i, lt_of_lt_of_le hi₁ hlen₁⟩
      simp only [g, hi₁, hi₂, ↓reduceDIte, Option.some.injEq, Subtype.mk.injEq] at hfi
      exact hfi
    exact Set.finite_coe_iff.1 (Finite.of_injective g hg_inj)
  have himg_sub : f '' ℒ ⊆
      {H : Hypergraph α β | H ≤ G.toHypergraph} ×ˢ
        {l : List α | l.Nodup ∧ {x | x ∈ l} ⊆ G.vertexSet} := by
    rintro _ ⟨A, hA, rfl⟩
    have hcomp := hℒ.isComplemented hA
    exact ⟨hcomp.le, A.roots_nodup, (rootSet_subset A).trans hcomp.le.vertexSet_subset⟩
  exact Set.Finite.of_finite_image
    (((subhypergraphs_finite G.toHypergraph).prod hnodup_fin).subset himg_sub) hinj

theorem mem_rootedLocationCore_vertexSet_iff {G : RootedHypergraph α β}
    {ℒ : Set (RootedHypergraph α β)} (hℒ : IsRootedLocation G ℒ) {v : α} :
    v ∈ (rootedLocationCore G ℒ).vertexSet ↔
      v ∈ G.vertexSet ∧ ∀ A ∈ ℒ, v ∈ A.vertexSet → v ∈ A.rootSet := by
  simp only [rootedLocationCore, GM10.locationCore, rootedLocationToLocation, Set.mem_sep_iff,
    Set.forall_mem_image]
  refine and_congr_right fun hvG ↦ forall₂_congr fun A hA ↦ ?_
  rw [complementHypergraph_eq_of_isComplemented (hℒ.isComplemented hA)]
  simp only [complement, Set.mem_union, Set.mem_sdiff]
  exact ⟨fun h hvA ↦ h.resolve_left (fun h1 ↦ h1.2 hvA),
    fun h ↦ by by_cases hvA : v ∈ A.vertexSet <;> [exact Or.inr (h hvA); exact Or.inl ⟨hvG, hvA⟩]⟩

theorem mem_rootedLocationCore_edgeSet_iff {G : RootedHypergraph α β}
    {ℒ : Set (RootedHypergraph α β)} {e : β} :
    e ∈ (rootedLocationCore G ℒ).edgeSet ↔
      e ∈ G.edgeSet ∧ ∀ A ∈ ℒ, e ∉ A.edgeSet := by
  simp only [rootedLocationCore, GM10.locationCore, rootedLocationToLocation, Set.mem_sep_iff,
    Set.forall_mem_image, complementHypergraph, Set.mem_sdiff]
  exact ⟨fun ⟨heG, hall⟩ ↦ ⟨heG, fun A hA ↦ (hall hA).2⟩,
    fun ⟨heG, hall⟩ ↦ ⟨heG, fun _ hA ↦ ⟨heG, hall _ hA⟩⟩⟩

theorem rootSet_subset_rootedLocationCore {G : RootedHypergraph α β}
    {ℒ : Set (RootedHypergraph α β)} (hℒ : IsRootedLocation G ℒ) :
    G.rootSet ⊆ (rootedLocationCore G ℒ).vertexSet := by
  intro v hv
  rw [mem_rootedLocationCore_vertexSet_iff hℒ]
  exact ⟨G.roots_subset v hv, fun A hA hvA ↦ (hℒ.isComplemented hA).roots_mem hvA hv⟩

theorem mem_rootSet_subset_rootedLocationCore {G : RootedHypergraph α β}
    {ℒ : Set (RootedHypergraph α β)} (hℒ : IsRootedLocation G ℒ)
    {A₀ : RootedHypergraph α β} (hA₀ : A₀ ∈ ℒ) :
    A₀.rootSet ⊆ (rootedLocationCore G ℒ).vertexSet := by
  intro v hv
  rw [mem_rootedLocationCore_vertexSet_iff hℒ]
  refine ⟨(hℒ.isComplemented hA₀).le.vertexSet_subset (A₀.roots_subset v hv), fun A hA hvA ↦ ?_⟩
  by_cases hEq : A₀ = A
  · subst hEq
    exact hv
  · have hle_comp := hℒ.le_complement hA₀ hA hEq
    have hv_comp := hle_comp.vertexSet_subset (A₀.roots_subset v hv)
    exact hv_comp.resolve_left fun h1 ↦ h1.2 hvA

/-- First assertion of **Graph Minors XVIII, (5.4)** (page 93):
`V(G) \ πBar(G) = (V(G') \ πBar(G')) ∪ ⋃_{A ∈ ℒ} (V(A) \ πBar(A))`. -/
theorem theorem_5_4_vertexSet {P P' : UnlabeledPatchwork α β}
    {ℒ : Set (RootedHypergraph α β)} {newEdge : RootedHypergraph α β → β}
    (hheart : IsPatchworkHeart P ℒ newEdge P') :
    P.G.vertexSet \ P.G.rootSet =
      (P'.G.vertexSet \ P'.G.rootSet) ∪ ⋃ A ∈ ℒ, (A.vertexSet \ A.rootSet) := by
  have hℒ := hheart.isRootedLocation
  have hrootSet_eq : P'.G.rootSet = P.G.rootSet := by
    ext v
    simp [RootedHypergraph.rootSet, hheart.roots_eq]
  rw [hheart.vertexSet_eq, hrootSet_eq]
  ext v
  simp only [Set.mem_sdiff, Set.mem_union, Set.mem_iUnion,
    mem_rootedLocationCore_vertexSet_iff hℒ]
  constructor
  · rintro ⟨hvG, hnot_root⟩
    by_cases hall : ∀ A ∈ ℒ, v ∈ A.vertexSet → v ∈ A.rootSet
    · exact Or.inl ⟨⟨hvG, hall⟩, hnot_root⟩
    · push Not at hall
      rcases hall with ⟨A, hA, hvA, hnot_A⟩
      exact Or.inr ⟨A, hA, hvA, hnot_A⟩
  · rintro (⟨⟨hvG, _⟩, hnot_root⟩ | ⟨A, hA, hvA, hnot_A⟩)
    · exact ⟨hvG, hnot_root⟩
    · have hcomp := hℒ.isComplemented hA
      exact ⟨hcomp.le.vertexSet_subset hvA, fun hv_root ↦ hnot_A (hcomp.roots_mem hvA hv_root)⟩

/-- For a patchwork `P'` whose underlying rooted hypergraph has a single edge `e₀` with
ends `V(P'.G) = πBar(P'.G)`, a grouping `K` is feasible in `P'` if and only if `K ∈ Δ'(e₀)`. -/
theorem isFeasibleGrouping_singleEdge_iff {P' : GM04.Patchwork Ω α β} {e₀ : β}
    (hE : P'.G.edgeSet = {e₀}) (hV : P'.G.vertexSet = P'.G.rootSet)
    (hends : P'.G.ends e₀ = P'.G.rootSet)
    (K : (⊤ : SimpleGraph α).Subgraph) :
    IsFeasibleGrouping P' K ↔ K ∈ P'.Δ e₀ := by
  have he₀ : e₀ ∈ P'.G.edgeSet := hE ▸ Set.mem_singleton e₀
  have hΔ_verts : (P'.Δ e₀).verts = P'.G.rootSet :=
    (P'.Δ_verts e₀ he₀).trans hends
  have hreal_eq : ∀ δ : β → (⊤ : SimpleGraph α).Subgraph,
      δ e₀ ∈ P'.Δ e₀ → GM04.realizationOf P'.G.toHypergraph δ = δ e₀ := by
    intro δ hδ
    have hδ_verts : (δ e₀).verts = P'.G.vertexSet := by
      rw [((P'.Δ e₀).verts_eq (δ e₀) hδ).trans hΔ_verts, hV]
    ext u v
    · simp [GM04.realizationOf, hE, hδ_verts]
    · simp [GM04.realizationOf, hE]
  constructor
  · rintro ⟨hgrp, hK_verts, H, ⟨δ, hδ, rfl⟩, hconn⟩
    have hδ_e₀ : δ e₀ ∈ P'.Δ e₀ := hδ e₀ he₀
    rw [hreal_eq δ hδ_e₀] at hconn
    have hδ_grp : GM04.IsGrouping P'.G.rootSet (δ e₀) :=
      hΔ_verts ▸ (P'.Δ e₀).isGrouping (δ e₀) hδ_e₀
    have hδ_verts : (δ e₀).verts = P'.G.rootSet :=
      ((P'.Δ e₀).verts_eq (δ e₀) hδ_e₀).trans hΔ_verts
    have hK_eq : K = δ e₀ := by
      ext u v
      · rw [hK_verts, hδ_verts]
      · by_cases hne : u = v
        · subst hne
          exact ⟨fun h ↦ False.elim (K.loopless.irrefl u h),
            fun h ↦ False.elim ((δ e₀).loopless.irrefl u h)⟩
        · constructor
          · intro huv
            have hu : u ∈ P'.G.rootSet := hK_verts ▸ K.edge_vert huv
            have hv : v ∈ P'.G.rootSet := hK_verts ▸ K.edge_vert huv.symm
            have hsc : GM04.sameComponent (δ e₀) u v :=
              connectedIn_iff_sameComponent.1 ((hconn u hu v hv hne).2 huv)
            exact (GM04.sameComponent_iff_adj_of_isGrouping hδ_grp hne).1 hsc
          · intro huv
            have hu : u ∈ P'.G.rootSet := hδ_verts ▸ (δ e₀).edge_vert huv
            have hv : v ∈ P'.G.rootSet := hδ_verts ▸ (δ e₀).edge_vert huv.symm
            exact (hconn u hu v hv hne).1 (connectedIn_of_adj huv)
    rwa [hK_eq]
  · intro hK
    have hgrp : GM04.IsGrouping P'.G.rootSet K := hΔ_verts ▸ (P'.Δ e₀).isGrouping K hK
    have hK_verts : K.verts = P'.G.rootSet := ((P'.Δ e₀).verts_eq K hK).trans hΔ_verts
    refine ⟨hgrp, hK_verts, K, ⟨fun _ ↦ K, fun e he ↦ ?_, (hreal_eq (fun _ ↦ K) hK).symm⟩,
      fun x _ y _ hne ↦ connectedIn_iff_sameComponent.trans
        (GM04.sameComponent_iff_adj_of_isGrouping hgrp hne)⟩
    rw [hE, Set.mem_singleton_iff] at he
    rwa [he]

/-! ### Intermediate patchworks `P_S` for the proof of (5.4)

Following the proof of `theorem_3_4_proof` in `Section3.lean`, we work in `β ⊕ RootedHypergraph α β`
so
that `Sum.inl e` (`e ∈ E(G)`) and `Sum.inr A` (`A ∈ ℒ`) are disjoint by construction, and then push
forward to `P'` along the edge bijection `Sum.inl e ↦ e`, `Sum.inr A ↦ newEdge A`. -/

/-- The left edge-label inclusion used for patchworks. -/
abbrev mapInlH (γ : Type*) (G : Hypergraph α β) : Hypergraph α (β ⊕ γ) := mapInl γ G

/-- Maps a `RootedHypergraph α β` to `RootedHypergraph α (β ⊕ γ)` via `mapInlH γ`. -/
@[expose] def mapInlRooted (γ : Type*) (G : RootedHypergraph α β) : RootedHypergraph α (β ⊕ γ) where
  toHypergraph := mapInlH γ G.toHypergraph
  roots := G.roots
  roots_nodup := G.roots_nodup
  roots_subset := G.roots_subset

/-- Maps a `GM04.Patchwork Ω α β` to `GM04.Patchwork Ω α (β ⊕ γ)` via `Sum.inl`. -/
@[expose] def mapInlPatchwork (γ : Type*) (P : GM04.Patchwork Ω α β) [Inhabited Ω] :
    GM04.Patchwork Ω α (β ⊕ γ) where
  G := mapInlRooted γ P.G
  dom := Sum.inl '' P.dom
  μ e := match e with
    | Sum.inl e₀ => P.μ e₀
    | Sum.inr _ => []
  Δ e := match e with
    | Sum.inl e₀ => P.Δ e₀
    | Sum.inr _ => GM04.freePatch ∅
  φ e := match e with
    | Sum.inl e₀ => P.φ e₀
    | Sum.inr _ => default
  dom_subset := Set.image_mono P.dom_subset
  μ_nodup := by
    rintro _ ⟨e₀, he₀, rfl⟩
    exact P.μ_nodup e₀ he₀
  μ_set := by
    rintro _ ⟨e₀, he₀, rfl⟩
    exact P.μ_set e₀ he₀
  Δ_verts := by
    rintro _ ⟨e₀, he₀, rfl⟩
    exact P.Δ_verts e₀ he₀
  Δ_free := by
    rintro _ ⟨e₀, he₀, rfl⟩ hnd
    exact P.Δ_free e₀ he₀ fun hd ↦ hnd ⟨e₀, hd, rfl⟩

/-- The single-edge rooted hypergraph `A'_j` in `β ⊕ RootedHypergraph α β` on `πBar(A)` with edge
`Sum.inr A` and roots `π(A)` (Graph Minors XVIII, Section 5, proof of (5.4), page 94). -/
@[expose] def placeNewEdgeSum (A : RootedHypergraph α β) :
    RootedHypergraph α (β ⊕ RootedHypergraph α β) where
  toHypergraph :=
    { vertexSet := A.rootSet
      edgeSet := {Sum.inr A}
      Inc e v := e = Sum.inr A ∧ v ∈ A.rootSet
      vertex_mem_of_inc _ _ h := h.2
      edge_mem_of_inc _ _ h := h.1
      vertexSet_finite := A.vertexSet_finite.subset (rootSet_subset A)
      edgeSet_finite := Set.finite_singleton _ }
  roots := A.roots
  roots_nodup := A.roots_nodup
  roots_subset _ h := h

/-- The ambient hypergraph in `β ⊕ RootedHypergraph α β` for a rooted location `ℒ` in `G`. -/
@[expose] def placeSumAmbient (G : RootedHypergraph α β) {ℒ : Set (RootedHypergraph α β)}
    (hℒ : IsRootedLocation G ℒ) :
    Hypergraph α (β ⊕ RootedHypergraph α β) where
  vertexSet := G.vertexSet
  edgeSet := (Sum.inl '' G.edgeSet) ∪ (Sum.inr '' ℒ)
  Inc e v := match e with
    | Sum.inl e₀ => G.Inc e₀ v
    | Sum.inr A => A ∈ ℒ ∧ v ∈ A.rootSet
  vertex_mem_of_inc e v h := by
    cases e with
    | inl e₀ => exact G.vertex_mem_of_inc h
    | inr A => exact (hℒ.isComplemented h.1).le.vertexSet_subset (A.roots_subset v h.2)
  edge_mem_of_inc e v h := by
    cases e with
    | inl e₀ => exact Or.inl ⟨e₀, G.edge_mem_of_inc h, rfl⟩
    | inr A => exact Or.inr ⟨A, h.1, rfl⟩
  vertexSet_finite := G.vertexSet_finite
  edgeSet_finite := (G.edgeSet_finite.image Sum.inl).union (hℒ.finite.image Sum.inr)

theorem mapInlH_le_placeSumAmbient {G : RootedHypergraph α β}
    {ℒ : Set (RootedHypergraph α β)} (hℒ : IsRootedLocation G ℒ)
    {H : Hypergraph α β} (hH : H ≤ G.toHypergraph) :
    mapInlH (RootedHypergraph α β) H ≤ placeSumAmbient G hℒ where
  vertexSet_subset := hH.vertexSet_subset
  edgeSet_subset := (Set.image_mono hH.edgeSet_subset).trans Set.subset_union_left
  ends_eq e he := by
    rcases he with ⟨e₀, he₀, rfl⟩
    exact hH.ends_eq e₀ he₀

theorem placeNewEdgeSum_le_placeSumAmbient {G : RootedHypergraph α β}
    {ℒ : Set (RootedHypergraph α β)} (hℒ : IsRootedLocation G ℒ)
    {A : RootedHypergraph α β} (hA : A ∈ ℒ) :
    (placeNewEdgeSum A).toHypergraph ≤ placeSumAmbient G hℒ where
  vertexSet_subset := (rootSet_subset A).trans (hℒ.isComplemented hA).le.vertexSet_subset
  edgeSet_subset := by
    rintro _ rfl
    exact Or.inr ⟨A, hA, rfl⟩
  ends_eq e he := by
    rcases Set.mem_singleton_iff.1 he with rfl
    ext v
    change (A ∈ ℒ ∧ v ∈ A.rootSet) ↔ (Sum.inr A = Sum.inr A ∧ v ∈ A.rootSet)
    exact ⟨fun h ↦ ⟨rfl, h.2⟩, fun h ↦ ⟨hA, h.2⟩⟩

open Classical in
/-- The intermediate rooted hypergraph `G_S` in `β ⊕ RootedHypergraph α β` in the proof of (5.4)
(page 94), where `S ⊆ ℒ` is the set of members of `ℒ` that have not yet been replaced by new
edges (so `S = ∅` corresponds to the heart `P | ℒ` and `S = ℒ` corresponds to `P`). -/
@[expose] noncomputable def placeSumStepHypergraph (G : RootedHypergraph α β)
    {ℒ : Set (RootedHypergraph α β)} (hℒ : IsRootedLocation G ℒ)
    (S : Finset (RootedHypergraph α β)) :
    RootedHypergraph α (β ⊕ RootedHypergraph α β) where
  toHypergraph :=
    mapInlH _ (rootedLocationCore G ℒ) ∪
      Hypergraph.biUnion S (fun A ↦ mapInlH _ A.toHypergraph) ∪
      Hypergraph.biUnion (hℒ.finite.toFinset \ S) (fun A ↦ (placeNewEdgeSum A).toHypergraph)
  roots := G.roots
  roots_nodup := G.roots_nodup
  roots_subset _ hv := Or.inl (Or.inl (rootSet_subset_rootedLocationCore hℒ hv))

open Classical in
/-- The side rooted hypergraph `B` in `β ⊕ RootedHypergraph α β` in the proof of (5.4) (page 94). -/
@[expose] noncomputable def placeSumStepSide (G : RootedHypergraph α β)
    {ℒ : Set (RootedHypergraph α β)} (hℒ : IsRootedLocation G ℒ)
    (S : Finset (RootedHypergraph α β)) (A₀ : RootedHypergraph α β) :
    RootedHypergraph α (β ⊕ RootedHypergraph α β) where
  toHypergraph :=
    mapInlH _ (rootedLocationCore G ℒ) ∪
      Hypergraph.biUnion (S.erase A₀) (fun A ↦ mapInlH _ A.toHypergraph) ∪
      Hypergraph.biUnion ((hℒ.finite.toFinset \ S).erase A₀)
        (fun A ↦ (placeNewEdgeSum A).toHypergraph)
  roots := G.roots
  roots_nodup := G.roots_nodup
  roots_subset _ hv := Or.inl (Or.inl (rootSet_subset_rootedLocationCore hℒ hv))

open Classical in
theorem placeSumStepHypergraph_le_ambient {G : RootedHypergraph α β}
    {ℒ : Set (RootedHypergraph α β)} (hℒ : IsRootedLocation G ℒ)
    {S : Finset (RootedHypergraph α β)} (hS : S ⊆ hℒ.finite.toFinset) :
    (placeSumStepHypergraph G hℒ S).toHypergraph ≤ placeSumAmbient G hℒ := by
  refine GM10.union_le
    (GM10.union_le (mapInlH_le_placeSumAmbient hℒ (locationCore_le hℒ.isLocation)) ?_) ?_
  · refine biUnion_le fun A hA ↦ ?_
    have hA_ℒ : A ∈ ℒ := hℒ.finite.mem_toFinset.1 (hS hA)
    exact mapInlH_le_placeSumAmbient hℒ (hℒ.isComplemented hA_ℒ).le
  · refine biUnion_le fun A hA ↦ ?_
    have hA_ℒ : A ∈ ℒ := hℒ.finite.mem_toFinset.1 (Finset.sdiff_subset hA)
    exact placeNewEdgeSum_le_placeSumAmbient hℒ hA_ℒ

open Classical in
theorem placeSumStepSide_le_ambient {G : RootedHypergraph α β}
    {ℒ : Set (RootedHypergraph α β)} (hℒ : IsRootedLocation G ℒ)
    {S : Finset (RootedHypergraph α β)} (hS : S ⊆ hℒ.finite.toFinset)
    (A₀ : RootedHypergraph α β) :
    (placeSumStepSide G hℒ S A₀).toHypergraph ≤ placeSumAmbient G hℒ := by
  refine GM10.union_le
    (GM10.union_le (mapInlH_le_placeSumAmbient hℒ (locationCore_le hℒ.isLocation)) ?_) ?_
  · refine biUnion_le fun A hA ↦ ?_
    have hA_ℒ : A ∈ ℒ := hℒ.finite.mem_toFinset.1 (hS (Finset.mem_of_mem_erase hA))
    exact mapInlH_le_placeSumAmbient hℒ (hℒ.isComplemented hA_ℒ).le
  · refine biUnion_le fun A hA ↦ ?_
    have hA_ℒ : A ∈ ℒ :=
      hℒ.finite.mem_toFinset.1 (Finset.sdiff_subset (Finset.mem_of_mem_erase hA))
    exact placeNewEdgeSum_le_placeSumAmbient hℒ hA_ℒ

open Classical in
/-- The intermediate patchwork `P_S` in `β ⊕ RootedHypergraph α β` in the proof of (5.4) (page 94).
-/
@[expose] noncomputable def placeSumStepPatchwork (P : UnlabeledPatchwork α β)
    {ℒ : Set (RootedHypergraph α β)} (hℒ : IsRootedLocation P.G ℒ)
    (S : Finset (RootedHypergraph α β)) (hS : S ⊆ hℒ.finite.toFinset) :
    UnlabeledPatchwork α (β ⊕ RootedHypergraph α β) where
  G := placeSumStepHypergraph P.G hℒ S
  dom := ((Sum.inl '' P.dom) ∩ (placeSumStepHypergraph P.G hℒ S).edgeSet) ∪
    (Sum.inr '' ((hℒ.finite.toFinset \ S : Finset (RootedHypergraph α β)) : Set _))
  μ e := match e with
    | Sum.inl e₀ => P.μ e₀
    | Sum.inr A => A.roots
  Δ e := match e with
    | Sum.inl e₀ => P.Δ e₀
    | Sum.inr A => feasibleGroupings (P.restrict A)
  φ _ := ()
  dom_subset := by
    rintro e (⟨_, he⟩ | ⟨A, hA, rfl⟩)
    · exact he
    · refine Or.inr ?_
      simp only [biUnion, Set.mem_iUnion, placeNewEdgeSum, Set.mem_singleton_iff]
      exact ⟨A, hA, rfl⟩
  μ_nodup := by
    rintro e (⟨⟨e₀, he₀, rfl⟩, _⟩ | ⟨A, _, rfl⟩)
    · exact P.μ_nodup e₀ he₀
    · exact A.roots_nodup
  μ_set := by
    have hle_amb := placeSumStepHypergraph_le_ambient hℒ hS
    rintro e (⟨⟨e₀, he₀, rfl⟩, he_edge⟩ | ⟨A, hA_sdiff, rfl⟩)
    · rw [P.μ_set e₀ he₀]
      have hends := hle_amb.ends_eq (Sum.inl e₀) he_edge
      exact hends
    · have he_edge : Sum.inr A ∈ (placeSumStepHypergraph P.G hℒ S).edgeSet := by
        refine Or.inr ?_
        simp only [biUnion, Set.mem_iUnion, placeNewEdgeSum, Set.mem_singleton_iff]
        exact ⟨A, hA_sdiff, rfl⟩
      have hends := hle_amb.ends_eq (Sum.inr A) he_edge
      have hA_ℒ : A ∈ ℒ := hℒ.finite.mem_toFinset.1 (Finset.sdiff_subset hA_sdiff)
      rw [← hends]
      ext v
      change v ∈ A.rootSet ↔ (A ∈ ℒ ∧ v ∈ A.rootSet)
      exact ⟨fun hv ↦ ⟨hA_ℒ, hv⟩, fun h ↦ h.2⟩
  Δ_verts := by
    have hle_amb := placeSumStepHypergraph_le_ambient hℒ hS
    intro e he_edge
    have hends := hle_amb.ends_eq e he_edge
    cases e with
    | inl e₀ =>
      have he₀_G : e₀ ∈ P.G.edgeSet := by
        rcases hle_amb.edgeSet_subset he_edge with ⟨e₁, he₁, hEq⟩ | ⟨_, _, hEq⟩
        · cases hEq
          exact he₁
        · cases hEq
      exact (P.Δ_verts e₀ he₀_G).trans hends
    | inr A =>
      have hA_ℒ : A ∈ ℒ := by
        rcases hle_amb.edgeSet_subset he_edge with ⟨_, _, hEq⟩ | ⟨A', hA', hEq⟩
        · cases hEq
        · cases hEq
          exact hA'
      rw [← hends]
      ext v
      change v ∈ A.rootSet ↔ (A ∈ ℒ ∧ v ∈ A.rootSet)
      exact ⟨fun hv ↦ ⟨hA_ℒ, hv⟩, fun h ↦ h.2⟩
  Δ_free := by
    have hle_amb := placeSumStepHypergraph_le_ambient hℒ hS
    intro e he_edge hnot_dom
    cases e with
    | inl e₀ =>
      have he₀_G : e₀ ∈ P.G.edgeSet := by
        rcases hle_amb.edgeSet_subset he_edge with ⟨e₁, he₁, hEq⟩ | ⟨_, _, hEq⟩
        · cases hEq
          exact he₁
        · cases hEq
      have hnot_dom₀ : e₀ ∉ P.dom := fun hd ↦ hnot_dom (Or.inl ⟨⟨e₀, hd, rfl⟩, he_edge⟩)
      exact P.Δ_free e₀ he₀_G hnot_dom₀
    | inr A =>
      exfalso
      rcases he_edge with (he_core | he_S) | he_sdiff
      · rcases he_core with ⟨_, _, hEq⟩
        cases hEq
      · simp only [biUnion, Set.mem_iUnion, mapInlH, mapInl, Set.mem_image, reduceCtorEq, and_false,
          exists_false] at he_S
      · simp only [biUnion, Set.mem_iUnion, placeNewEdgeSum, Set.mem_singleton_iff,
          Sum.inr.injEq] at he_sdiff
        rcases he_sdiff with ⟨A', hA', hEq⟩
        subst hEq
        exact hnot_dom (Or.inr ⟨A, hA', rfl⟩)

@[simp] theorem placeSumStepPatchwork_G (P : UnlabeledPatchwork α β)
    {ℒ : Set (RootedHypergraph α β)} (hℒ : IsRootedLocation P.G ℒ)
    (S : Finset (RootedHypergraph α β)) (hS : S ⊆ hℒ.finite.toFinset) :
    (placeSumStepPatchwork P hℒ S hS).G = placeSumStepHypergraph P.G hℒ S := rfl

@[simp] theorem placeSumStepPatchwork_Δ_inl (P : UnlabeledPatchwork α β)
    {ℒ : Set (RootedHypergraph α β)} (hℒ : IsRootedLocation P.G ℒ)
    (S : Finset (RootedHypergraph α β)) (hS : S ⊆ hℒ.finite.toFinset) (e₀ : β) :
    (placeSumStepPatchwork P hℒ S hS).Δ (Sum.inl e₀) = P.Δ e₀ := rfl

@[simp] theorem placeSumStepPatchwork_Δ_inr (P : UnlabeledPatchwork α β)
    {ℒ : Set (RootedHypergraph α β)} (hℒ : IsRootedLocation P.G ℒ)
    (S : Finset (RootedHypergraph α β)) (hS : S ⊆ hℒ.finite.toFinset)
    (A : RootedHypergraph α β) :
    (placeSumStepPatchwork P hℒ S hS).Δ (Sum.inr A) = feasibleGroupings (P.restrict A) := rfl

open Classical in
/-- `GM04.IsRealization` is invariant under an edge bijection preserving vertices and patches. -/
theorem isRealization_iff_of_edge_bij {Ω₁ Ω₂ : Type*}
    {β₁ β₂ : Type*} (P₁ : GM04.Patchwork Ω₁ α β₁) (P₂ : GM04.Patchwork Ω₂ α β₂)
    (f : β₁ → β₂)
    (hV : P₁.G.vertexSet = P₂.G.vertexSet)
    (hE : f '' P₁.G.edgeSet = P₂.G.edgeSet)
    (hinj : Set.InjOn f P₁.G.edgeSet)
    (hΔ : ∀ e ∈ P₁.G.edgeSet, P₂.Δ (f e) = P₁.Δ e)
    (H : (⊤ : SimpleGraph α).Subgraph) :
    P₁.IsRealization H ↔ P₂.IsRealization H := by
  constructor
  · rintro ⟨δ₁, hδ₁, rfl⟩
    let δ₂ : β₂ → (⊤ : SimpleGraph α).Subgraph := fun e₂ ↦
      if h : ∃ e₁ ∈ P₁.G.edgeSet, f e₁ = e₂ then δ₁ h.choose else ⊥
    have hδ₂_eq : ∀ e₁ ∈ P₁.G.edgeSet, δ₂ (f e₁) = δ₁ e₁ := by
      intro e₁ he₁
      have hex : ∃ e' ∈ P₁.G.edgeSet, f e' = f e₁ := ⟨e₁, he₁, rfl⟩
      have hdif : δ₂ (f e₁) = δ₁ hex.choose := by simp only [δ₂, hex, ↓reduceDIte]
      rw [hdif]
      exact congrArg δ₁ (hinj hex.choose_spec.1 he₁ hex.choose_spec.2)
    have hδ₂ : ∀ e₂ ∈ P₂.G.edgeSet, δ₂ e₂ ∈ P₂.Δ e₂ := by
      intro e₂ he₂
      rw [← hE] at he₂
      rcases he₂ with ⟨e₁, he₁, rfl⟩
      rw [hδ₂_eq e₁ he₁, hΔ e₁ he₁]
      exact hδ₁ e₁ he₁
    have hreal₁ : P₁.IsRealization (GM04.realizationOf P₁.G.toHypergraph δ₁) := ⟨δ₁, hδ₁, rfl⟩
    have hreal₂ : P₂.IsRealization (GM04.realizationOf P₂.G.toHypergraph δ₂) := ⟨δ₂, hδ₂, rfl⟩
    refine ⟨δ₂, hδ₂, ?_⟩
    ext u v
    · rw [hreal₁.verts_eq, hreal₂.verts_eq, hV]
    · simp only [GM04.realizationOf_adj, ← hE, Set.mem_image, exists_exists_and_eq_and]
      exact exists_congr fun e₁ ↦ and_congr_right fun he₁ ↦ by rw [hδ₂_eq e₁ he₁]
  · rintro ⟨δ₂, hδ₂, rfl⟩
    let δ₁ : β₁ → (⊤ : SimpleGraph α).Subgraph := fun e₁ ↦ δ₂ (f e₁)
    have hδ₁ : ∀ e₁ ∈ P₁.G.edgeSet, δ₁ e₁ ∈ P₁.Δ e₁ := by
      intro e₁ he₁
      have hfe₁ : f e₁ ∈ P₂.G.edgeSet := hE ▸ ⟨e₁, he₁, rfl⟩
      rw [← hΔ e₁ he₁]
      exact hδ₂ (f e₁) hfe₁
    have hreal₁ : P₁.IsRealization (GM04.realizationOf P₁.G.toHypergraph δ₁) := ⟨δ₁, hδ₁, rfl⟩
    have hreal₂ : P₂.IsRealization (GM04.realizationOf P₂.G.toHypergraph δ₂) := ⟨δ₂, hδ₂, rfl⟩
    refine ⟨δ₁, hδ₁, ?_⟩
    ext u v
    · rw [hreal₂.verts_eq, hreal₁.verts_eq, hV]
    · simp only [GM04.realizationOf_adj, ← hE, Set.mem_image, exists_exists_and_eq_and, δ₁]

/-- `feasibleGroupings` is invariant under an edge bijection preserving vertices, roots, and
patches. -/
theorem feasibleGroupings_eq_of_edge_bij {Ω₁ Ω₂ : Type*}
    {β₁ β₂ : Type*} (P₁ : GM04.Patchwork Ω₁ α β₁) (P₂ : GM04.Patchwork Ω₂ α β₂)
    (f : β₁ → β₂)
    (hV : P₁.G.vertexSet = P₂.G.vertexSet)
    (hR : P₁.G.rootSet = P₂.G.rootSet)
    (hE : f '' P₁.G.edgeSet = P₂.G.edgeSet)
    (hinj : Set.InjOn f P₁.G.edgeSet)
    (hΔ : ∀ e ∈ P₁.G.edgeSet, P₂.Δ (f e) = P₁.Δ e) :
    feasibleGroupings P₁ = feasibleGroupings P₂ := by
  refine GM04.Patch.ext hR (Set.ext fun K ↦ ?_)
  change IsFeasibleGrouping P₁ K ↔ IsFeasibleGrouping P₂ K
  simp only [IsFeasibleGrouping, hR]
  refine and_congr_right fun _ ↦ and_congr_right fun _ ↦ exists_congr fun H ↦
    and_congr_left fun _ ↦ ?_
  exact isRealization_iff_of_edge_bij P₁ P₂ f hV hE hinj hΔ H

/-- Corollary of `(5.2)`: if `(G₁', G₀)` and `(G₂', G₀)` are separations of `P₁.G` and `P₂.G` with
`π(G₁') = π(G₂')`, `P₁` and `P₂` having identical patches on `E(G₀)`, and
`gr(P₁ | G₁') = gr(P₂ | G₂')`, then `gr(P₁) = gr(P₂)`. -/
theorem feasibleGroupings_eq_of_theorem_5_2 {P₁ P₂ : GM04.Patchwork Ω α β}
    {G₁' G₂' G₀ : RootedHypergraph α β}
    (hsep₁ : P₁.G.IsSeparation G₁' G₀)
    (hsep₂ : P₂.G.IsSeparation G₂' G₀)
    (hroots : G₁'.roots = G₂'.roots)
    (hG₀_Δ : ∀ e ∈ G₀.edgeSet, P₁.Δ e = P₂.Δ e)
    (hgr : feasibleGroupings (P₁.restrict G₁') = feasibleGroupings (P₂.restrict G₂')) :
    feasibleGroupings P₁ = feasibleGroupings P₂ := by
  have hG₀ : ∀ e ∈ G₀.edgeSet, (P₁.restrict G₀).Δ e = (P₂.restrict G₀).Δ e := by
    intro e he
    rw [P₁.restrict_Δ hsep₁.isSeparation.right_le he, P₂.restrict_Δ hsep₂.isSeparation.right_le he]
    exact hG₀_Δ e he
  have hR₁ : G₀.rootSet = P₁.G.rootSet := by
    ext v
    simp [RootedHypergraph.rootSet, hsep₁.roots_right]
  have hR₂ : G₀.rootSet = P₂.G.rootSet := by
    ext v
    simp [RootedHypergraph.rootSet, hsep₂.roots_right]
  have hR : P₁.G.rootSet = P₂.G.rootSet := hR₁.symm.trans hR₂
  refine GM04.Patch.ext hR (Set.ext fun K ↦ ?_)
  change IsFeasibleGrouping P₁ K ↔ IsFeasibleGrouping P₂ K
  constructor
  · rintro ⟨hgrp, hK_verts, H₁, hH₁, hconn₁⟩
    obtain ⟨H₂, hH₂, hconn_G₀⟩ := theorem_5_2_proof hsep₁ hsep₂ hroots hG₀ (by rw [hgr]) hH₁
    refine ⟨hR ▸ hgrp, hK_verts.trans hR, H₂, hH₂, ?_⟩
    intro x hx y hy hne
    have hx₀ : x ∈ G₀.vertexSet := rootSet_subset G₀ (hR₂.symm ▸ hx)
    have hy₀ : y ∈ G₀.vertexSet := rootSet_subset G₀ (hR₂.symm ▸ hy)
    exact (hconn_G₀ x hx₀ y hy₀).symm.trans (hconn₁ x (hR.symm ▸ hx) y (hR.symm ▸ hy) hne)
  · rintro ⟨hgrp, hK_verts, H₂, hH₂, hconn₂⟩
    have hG₀' : ∀ e ∈ G₀.edgeSet, (P₂.restrict G₀).Δ e = (P₁.restrict G₀).Δ e :=
      fun e he ↦ (hG₀ e he).symm
    obtain ⟨H₁, hH₁, hconn_G₀⟩ := theorem_5_2_proof hsep₂ hsep₁ hroots.symm hG₀' (by rw [hgr]) hH₂
    refine ⟨hR.symm ▸ hgrp, hK_verts.trans hR.symm, H₁, hH₁, ?_⟩
    intro x hx y hy hne
    have hx₀ : x ∈ G₀.vertexSet := rootSet_subset G₀ (hR₁.symm ▸ hx)
    have hy₀ : y ∈ G₀.vertexSet := rootSet_subset G₀ (hR₁.symm ▸ hy)
    exact (hconn_G₀ x hx₀ y hy₀).symm.trans (hconn₂ x (hR ▸ hx) y (hR ▸ hy) hne)

private theorem biUnion_insert {ι γ : Type*} [DecidableEq ι] (a : ι) (s : Finset ι)
    (f : ι → Hypergraph α γ) :
    biUnion (insert a s) f = f a ∪ biUnion s f := by
  ext v e
  · simp [biUnion]
  · simp [biUnion]
  · simp [biUnion]

open Classical in
theorem isSeparation_placeSumStep_insert (P : UnlabeledPatchwork α β)
    {ℒ : Set (RootedHypergraph α β)} (hℒ : IsRootedLocation P.G ℒ)
    {S : Finset (RootedHypergraph α β)} {A₀ : RootedHypergraph α β}
    (hS : insert A₀ S ⊆ hℒ.finite.toFinset) (hnotMem : A₀ ∉ S) :
    (placeSumStepPatchwork P hℒ (insert A₀ S) hS).G.IsSeparation
      (mapInlRooted (RootedHypergraph α β) A₀)
      (placeSumStepSide P.G hℒ S A₀) := by
  have hS' : S ⊆ hℒ.finite.toFinset := (Finset.subset_insert A₀ S).trans hS
  have hA₀_fin : A₀ ∈ hℒ.finite.toFinset := hS (Finset.mem_insert_self A₀ S)
  have hA₀_ℒ : A₀ ∈ ℒ := hℒ.finite.mem_toFinset.1 hA₀_fin
  have hle_amb_B := placeSumStepSide_le_ambient hℒ hS' A₀
  have hle_amb_A : (mapInlRooted (RootedHypergraph α β) A₀).toHypergraph ≤
      placeSumAmbient P.G hℒ :=
    mapInlH_le_placeSumAmbient hℒ (hℒ.isComplemented hA₀_ℒ).le
  have hSdiff_insert : hℒ.finite.toFinset \ insert A₀ S = (hℒ.finite.toFinset \ S).erase A₀ := by
    ext B
    simp only [Finset.mem_sdiff, Finset.mem_insert, not_or, Finset.mem_erase]
    tauto
  have hunion_eq :
      (mapInlRooted (RootedHypergraph α β) A₀).toHypergraph ∪
        (placeSumStepSide P.G hℒ S A₀).toHypergraph =
      (placeSumStepHypergraph P.G hℒ (insert A₀ S)).toHypergraph := by
    change mapInlH _ A₀.toHypergraph ∪
      ((mapInlH _ (rootedLocationCore P.G ℒ) ∪
        biUnion (S.erase A₀) (fun A ↦ mapInlH _ A.toHypergraph)) ∪
        biUnion ((hℒ.finite.toFinset \ S).erase A₀) (fun A ↦ (placeNewEdgeSum A).toHypergraph)) =
      (mapInlH _ (rootedLocationCore P.G ℒ) ∪
        biUnion (insert A₀ S) (fun A ↦ mapInlH _ A.toHypergraph)) ∪
        biUnion (hℒ.finite.toFinset \ insert A₀ S) (fun A ↦ (placeNewEdgeSum A).toHypergraph)
    rw [Finset.erase_eq_of_notMem hnotMem, hSdiff_insert, biUnion_insert]
    simp only [← GM10.union_assoc,
      GM10.union_comm (mapInlH _ A₀.toHypergraph) (mapInlH _ (rootedLocationCore P.G ℒ))]
  have hA_le : (mapInlRooted (RootedHypergraph α β) A₀).toHypergraph ≤
      (placeSumStepHypergraph P.G hℒ (insert A₀ S)).toHypergraph :=
    hunion_eq ▸ GM10.le_union_left hle_amb_A hle_amb_B
  have hB_le : (placeSumStepSide P.G hℒ S A₀).toHypergraph ≤
      (placeSumStepHypergraph P.G hℒ (insert A₀ S)).toHypergraph :=
    hunion_eq ▸ GM10.le_union_right hle_amb_A hle_amb_B
  have hdisjE : Disjoint (mapInlRooted (RootedHypergraph α β) A₀).edgeSet
      (placeSumStepSide P.G hℒ S A₀).edgeSet := by
    rw [Set.disjoint_left]
    rintro _ ⟨e₀, he₀, rfl⟩ ((⟨e₁, he₁, hEq⟩ | he_S) | he_sdiff)
    · cases hEq
      exact (mem_rootedLocationCore_edgeSet_iff.1 he₁).2 A₀ hA₀_ℒ he₀
    · simp only [biUnion, Set.mem_iUnion, mapInlH, mapInl, Set.mem_image] at he_S
      rcases he_S with ⟨A, hA_erase, e₁, he₁, hEq⟩
      cases hEq
      have hA_ℒ : A ∈ ℒ := hℒ.finite.mem_toFinset.1 (hS' (Finset.mem_of_mem_erase hA_erase))
      have hne : A ≠ A₀ := Finset.ne_of_mem_erase hA_erase
      have hle_comp := hℒ.le_complement hA_ℒ hA₀_ℒ hne
      exact (hle_comp.edgeSet_subset he₁).2 he₀
    · simp only [biUnion, Set.mem_iUnion, placeNewEdgeSum, Set.mem_singleton_iff,
        reduceCtorEq, exists_false] at he_sdiff
  have hroot_core : A₀.rootSet ⊆ (rootedLocationCore P.G ℒ).vertexSet :=
    mem_rootSet_subset_rootedLocationCore hℒ hA₀_ℒ
  have hcore_B : (rootedLocationCore P.G ℒ).vertexSet ⊆
      (placeSumStepSide P.G hℒ S A₀).vertexSet := fun _ hv ↦ Or.inl (Or.inl hv)
  refine ⟨⟨hA_le, hB_le, hunion_eq, Set.disjoint_iff_inter_eq_empty.1 hdisjE⟩, rfl, ?_⟩
  ext v
  change v ∈ A₀.rootSet ↔ v ∈ A₀.vertexSet ∧ v ∈ (placeSumStepSide P.G hℒ S A₀).vertexSet
  constructor
  · intro hv
    exact ⟨A₀.roots_subset v hv, hcore_B (hroot_core hv)⟩
  · rintro ⟨hvA₀, (hv_core | hv_S) | hv_sdiff⟩
    · exact ((mem_rootedLocationCore_vertexSet_iff hℒ).1 hv_core).2 A₀ hA₀_ℒ hvA₀
    · simp only [biUnion, Set.mem_iUnion] at hv_S
      rcases hv_S with ⟨A, hA_erase, hvA⟩
      have hA_ℒ : A ∈ ℒ := hℒ.finite.mem_toFinset.1 (hS' (Finset.mem_of_mem_erase hA_erase))
      have hne : A ≠ A₀ := Finset.ne_of_mem_erase hA_erase
      have hle_comp := hℒ.le_complement hA_ℒ hA₀_ℒ hne
      exact (hle_comp.vertexSet_subset hvA).resolve_left fun h1 ↦ h1.2 hvA₀
    · simp only [biUnion, Set.mem_iUnion] at hv_sdiff
      rcases hv_sdiff with ⟨A, hA_erase, hvA_root⟩
      have hA_ℒ : A ∈ ℒ :=
        hℒ.finite.mem_toFinset.1 (Finset.sdiff_subset (Finset.mem_of_mem_erase hA_erase))
      have hne : A ≠ A₀ := Finset.ne_of_mem_erase hA_erase
      have hle_comp := hℒ.le_complement hA_ℒ hA₀_ℒ hne
      exact (hle_comp.vertexSet_subset (A.roots_subset v hvA_root)).resolve_left fun h1 ↦ h1.2 hvA₀

open Classical in
theorem isSeparation_placeSumStep_sdiff (P : UnlabeledPatchwork α β)
    {ℒ : Set (RootedHypergraph α β)} (hℒ : IsRootedLocation P.G ℒ)
    {S : Finset (RootedHypergraph α β)} {A₀ : RootedHypergraph α β}
    (hS : insert A₀ S ⊆ hℒ.finite.toFinset) (hnotMem : A₀ ∉ S) :
    have hS' : S ⊆ hℒ.finite.toFinset := (Finset.subset_insert A₀ S).trans hS
    (placeSumStepPatchwork P hℒ S hS').G.IsSeparation
      (placeNewEdgeSum A₀)
      (placeSumStepSide P.G hℒ S A₀) := by
  intro hS'
  have hA₀_fin : A₀ ∈ hℒ.finite.toFinset := hS (Finset.mem_insert_self A₀ S)
  have hA₀_ℒ : A₀ ∈ ℒ := hℒ.finite.mem_toFinset.1 hA₀_fin
  have hA₀_sdiff : A₀ ∈ hℒ.finite.toFinset \ S := Finset.mem_sdiff.2 ⟨hA₀_fin, hnotMem⟩
  have hle_amb_B := placeSumStepSide_le_ambient hℒ hS' A₀
  have hle_amb_A : (placeNewEdgeSum A₀).toHypergraph ≤ placeSumAmbient P.G hℒ :=
    placeNewEdgeSum_le_placeSumAmbient hℒ hA₀_ℒ
  have hInsert_erase : insert A₀ ((hℒ.finite.toFinset \ S).erase A₀) = hℒ.finite.toFinset \ S :=
    Finset.insert_erase hA₀_sdiff
  have hunion_eq :
      (placeNewEdgeSum A₀).toHypergraph ∪
        (placeSumStepSide P.G hℒ S A₀).toHypergraph =
      (placeSumStepHypergraph P.G hℒ S).toHypergraph := by
    change (placeNewEdgeSum A₀).toHypergraph ∪
      ((mapInlH _ (rootedLocationCore P.G ℒ) ∪
        biUnion (S.erase A₀) (fun A ↦ mapInlH _ A.toHypergraph)) ∪
        biUnion ((hℒ.finite.toFinset \ S).erase A₀) (fun A ↦ (placeNewEdgeSum A).toHypergraph)) =
      (mapInlH _ (rootedLocationCore P.G ℒ) ∪
        biUnion S (fun A ↦ mapInlH _ A.toHypergraph)) ∪
        biUnion (hℒ.finite.toFinset \ S) (fun A ↦ (placeNewEdgeSum A).toHypergraph)
    conv_rhs => rw [← hInsert_erase, biUnion_insert]
    rw [Finset.erase_eq_of_notMem hnotMem, ← GM10.union_assoc,
      GM10.union_comm (placeNewEdgeSum A₀).toHypergraph, GM10.union_assoc]
  have hA_le : (placeNewEdgeSum A₀).toHypergraph ≤
      (placeSumStepHypergraph P.G hℒ S).toHypergraph :=
    hunion_eq ▸ GM10.le_union_left hle_amb_A hle_amb_B
  have hB_le : (placeSumStepSide P.G hℒ S A₀).toHypergraph ≤
      (placeSumStepHypergraph P.G hℒ S).toHypergraph :=
    hunion_eq ▸ GM10.le_union_right hle_amb_A hle_amb_B
  have hdisjE : Disjoint (placeNewEdgeSum A₀).edgeSet
      (placeSumStepSide P.G hℒ S A₀).edgeSet := by
    rw [Set.disjoint_left]
    rintro _ rfl ((⟨_, _, hEq⟩ | he_S) | he_sdiff)
    · cases hEq
    · simp only [biUnion, Set.mem_iUnion, mapInlH, mapInl, Set.mem_image, reduceCtorEq, and_false,
        exists_false] at he_S
    · simp only [biUnion, Set.mem_iUnion, placeNewEdgeSum, Set.mem_singleton_iff,
        Sum.inr.injEq] at he_sdiff
      rcases he_sdiff with ⟨A, hA_erase, rfl⟩
      exact Finset.ne_of_mem_erase hA_erase rfl
  have hroot_core : A₀.rootSet ⊆ (rootedLocationCore P.G ℒ).vertexSet :=
    mem_rootSet_subset_rootedLocationCore hℒ hA₀_ℒ
  have hcore_B : (rootedLocationCore P.G ℒ).vertexSet ⊆
      (placeSumStepSide P.G hℒ S A₀).vertexSet := fun _ hv ↦ Or.inl (Or.inl hv)
  refine ⟨⟨hA_le, hB_le, hunion_eq, Set.disjoint_iff_inter_eq_empty.1 hdisjE⟩, rfl, ?_⟩
  ext v
  change v ∈ A₀.rootSet ↔ v ∈ A₀.rootSet ∧ v ∈ (placeSumStepSide P.G hℒ S A₀).vertexSet
  exact ⟨fun hv ↦ ⟨hv, hcore_B (hroot_core hv)⟩, fun h ↦ h.1⟩

open Classical in
/-- Claim (1) in the proof of (5.4) (Graph Minors XVIII, Section 5, page 94):
`gr(P₁ | A_j) = gr(P₂ | A'_j)`, where `A_j` is `mapInlRooted _ A₀` in `P_{insert A₀ S}` and `A'_j`
is
`placeNewEdgeSum A₀` in `P_S`. -/
theorem lemma_5_4_claim_1 (P : UnlabeledPatchwork α β)
    {ℒ : Set (RootedHypergraph α β)} (hℒ : IsRootedLocation P.G ℒ)
    {S : Finset (RootedHypergraph α β)} {A₀ : RootedHypergraph α β}
    (hS : insert A₀ S ⊆ hℒ.finite.toFinset)
    (hS' : S ⊆ hℒ.finite.toFinset)
    (hnotMem : A₀ ∉ S) :
    feasibleGroupings
        ((placeSumStepPatchwork P hℒ (insert A₀ S) hS).restrict (mapInlRooted _ A₀)) =
      feasibleGroupings
        ((placeSumStepPatchwork P hℒ S hS').restrict (placeNewEdgeSum A₀)) := by
  have hA₀_fin : A₀ ∈ hℒ.finite.toFinset := hS (Finset.mem_insert_self A₀ S)
  have hA₀_ℒ : A₀ ∈ ℒ := hℒ.finite.mem_toFinset.1 hA₀_fin
  have hsep_ins := isSeparation_placeSumStep_insert P hℒ hS hnotMem
  have hsep_sd := isSeparation_placeSumStep_sdiff P hℒ hS hnotMem
  have h₁ : feasibleGroupings (P.restrict A₀) =
      feasibleGroupings
        ((placeSumStepPatchwork P hℒ (insert A₀ S) hS).restrict (mapInlRooted _ A₀)) := by
    refine feasibleGroupings_eq_of_edge_bij (P.restrict A₀)
      ((placeSumStepPatchwork P hℒ (insert A₀ S) hS).restrict (mapInlRooted _ A₀))
      Sum.inl rfl rfl rfl Sum.inl_injective.injOn ?_
    intro e he
    rw [(placeSumStepPatchwork P hℒ (insert A₀ S) hS).restrict_Δ hsep_ins.isSeparation.left_le
      ⟨e, he, rfl⟩, P.restrict_Δ (hℒ.isComplemented hA₀_ℒ).le he]
    rfl
  have h₂ : feasibleGroupings
      ((placeSumStepPatchwork P hℒ S hS').restrict (placeNewEdgeSum A₀)) =
      feasibleGroupings (P.restrict A₀) := by
    have hV : ((placeSumStepPatchwork P hℒ S hS').restrict (placeNewEdgeSum A₀)).G.vertexSet =
        ((placeSumStepPatchwork P hℒ S hS').restrict (placeNewEdgeSum A₀)).G.rootSet := rfl
    have hE : ((placeSumStepPatchwork P hℒ S hS').restrict (placeNewEdgeSum A₀)).G.edgeSet =
        {Sum.inr A₀} := rfl
    have hends : ((placeSumStepPatchwork P hℒ S hS').restrict (placeNewEdgeSum A₀)).G.ends
        (Sum.inr A₀) =
        ((placeSumStepPatchwork P hℒ S hS').restrict (placeNewEdgeSum A₀)).G.rootSet := by
      ext v
      change Sum.inr A₀ = Sum.inr A₀ ∧ v ∈ A₀.rootSet ↔ v ∈ A₀.rootSet
      exact ⟨fun h ↦ h.2, fun h ↦ ⟨rfl, h⟩⟩
    refine GM04.Patch.ext rfl (Set.ext fun K ↦ ?_)
    change IsFeasibleGrouping
      ((placeSumStepPatchwork P hℒ S hS').restrict (placeNewEdgeSum A₀)) K ↔
      K ∈ feasibleGroupings (P.restrict A₀)
    rw [isFeasibleGrouping_singleEdge_iff hE hV hends K]
    change K ∈ (((placeSumStepPatchwork P hℒ S hS').restrict (placeNewEdgeSum A₀)).Δ
      (Sum.inr A₀)).groupings ↔ K ∈ (feasibleGroupings (P.restrict A₀)).groupings
    rw [(placeSumStepPatchwork P hℒ S hS').restrict_Δ hsep_sd.isSeparation.left_le
      (Set.mem_singleton _)]
    rfl
  rw [← h₁, h₂]

open Classical in
/-- By induction on `S ⊆ ℒ`, `feasibleGroupings (placeSumStepPatchwork P hℒ S hS)` equals
`feasibleGroupings (placeSumStepPatchwork P hℒ ∅ _)` (proof of (5.4), page 94). -/
theorem feasibleGroupings_placeSumStepPatchwork (P : UnlabeledPatchwork α β)
    {ℒ : Set (RootedHypergraph α β)} (hℒ : IsRootedLocation P.G ℒ)
    (S : Finset (RootedHypergraph α β)) (hS : S ⊆ hℒ.finite.toFinset) :
    feasibleGroupings (placeSumStepPatchwork P hℒ S hS) =
      feasibleGroupings (placeSumStepPatchwork P hℒ ∅ (Finset.empty_subset _)) := by
  induction S using Finset.induction_on with
  | empty => rfl
  | @insert A₀ S hnotMem ih =>
    have hS' : S ⊆ hℒ.finite.toFinset := (Finset.subset_insert A₀ S).trans hS
    rw [← ih hS']
    refine feasibleGroupings_eq_of_theorem_5_2
      (isSeparation_placeSumStep_insert P hℒ hS hnotMem)
      (isSeparation_placeSumStep_sdiff P hℒ hS hnotMem)
      rfl (fun _ _ ↦ rfl) (lemma_5_4_claim_1 P hℒ hS hS' hnotMem)

/-- **Graph Minors XVIII, (5.4)** (page 93):
"**5.4.** *Let $P = (G, \mu, \Delta)$ be a patchwork, let $\mathscr{L}$ be a rooted location in
$G$, and let $P' = (G', \mu', \Delta')$ be the heart of $(P, \mathscr{L})$. Then*
$$V(G) \setminus \bar{\pi}(G) = (V(G') \setminus \bar{\pi}(G')) \cup \bigcup_{A \in \mathscr{L}}
(V(A) \setminus \bar{\pi}(A)),$$
*and $gr(P) = gr(P')$.*" -/
theorem theorem_5_4_proof {P P' : UnlabeledPatchwork α β}
    {ℒ : Set (RootedHypergraph α β)} {newEdge : RootedHypergraph α β → β}
    (hP' : IsPatchworkHeart P ℒ newEdge P') :
    P.G.vertexSet \ P.G.rootSet =
      (P'.G.vertexSet \ P'.G.rootSet) ∪ (⋃ A ∈ ℒ, A.vertexSet \ A.rootSet) ∧
    feasibleGroupings P = feasibleGroupings P' := by
  classical
  have hℒ := hP'.isRootedLocation
  refine ⟨theorem_5_4_vertexSet hP', ?_⟩
  have h_top : feasibleGroupings P =
      feasibleGroupings (placeSumStepPatchwork P hℒ hℒ.finite.toFinset Finset.Subset.rfl) := by
    refine feasibleGroupings_eq_of_edge_bij P
      (placeSumStepPatchwork P hℒ hℒ.finite.toFinset Finset.Subset.rfl)
      Sum.inl ?_ rfl ?_ Sum.inl_injective.injOn (fun _ _ ↦ rfl)
    · rw [placeSumStepPatchwork_G]
      ext v
      change v ∈ P.G.vertexSet ↔
        (v ∈ (rootedLocationCore P.G ℒ).vertexSet ∨
          v ∈ (biUnion hℒ.finite.toFinset
            (fun A : RootedHypergraph α β ↦ mapInlH _ A.toHypergraph)).vertexSet) ∨
        v ∈ (biUnion (hℒ.finite.toFinset \ hℒ.finite.toFinset)
          (fun A : RootedHypergraph α β ↦ (placeNewEdgeSum A).toHypergraph)).vertexSet
      simp only [Finset.sdiff_self, biUnion, Finset.notMem_empty, Set.iUnion_of_empty,
        Set.iUnion_empty, Set.mem_empty_iff_false, or_false, Set.mem_iUnion,
        Set.Finite.mem_toFinset, mapInlH, mapInl]
      constructor
      · intro hv
        by_cases hcore : v ∈ (rootedLocationCore P.G ℒ).vertexSet
        · exact Or.inl hcore
        · rw [mem_rootedLocationCore_vertexSet_iff hℒ, not_and, not_forall] at hcore
          rcases hcore hv with ⟨A, hA⟩
          rw [Classical.not_imp] at hA
          rcases hA with ⟨hA_ℒ, hA_imp⟩
          rw [Classical.not_imp] at hA_imp
          exact Or.inr ⟨A, hA_ℒ, hA_imp.1⟩
      · rintro (hcore | ⟨A, hA, hvA⟩)
        · exact ((mem_rootedLocationCore_vertexSet_iff hℒ).1 hcore).1
        · exact (hℒ.isComplemented hA).le.vertexSet_subset hvA
    · rw [placeSumStepPatchwork_G]
      ext e
      change e ∈ Sum.inl '' P.G.edgeSet ↔
        (e ∈ Sum.inl '' (rootedLocationCore P.G ℒ).edgeSet ∨
          e ∈ (biUnion hℒ.finite.toFinset
            (fun A : RootedHypergraph α β ↦ mapInlH _ A.toHypergraph)).edgeSet) ∨
        e ∈ (biUnion (hℒ.finite.toFinset \ hℒ.finite.toFinset)
          (fun A : RootedHypergraph α β ↦ (placeNewEdgeSum A).toHypergraph)).edgeSet
      simp only [Finset.sdiff_self, biUnion, Finset.notMem_empty, Set.iUnion_of_empty,
        Set.iUnion_empty, Set.mem_empty_iff_false, or_false, Set.mem_iUnion,
        Set.Finite.mem_toFinset, mapInlH, mapInl, Set.mem_image]
      constructor
      · rintro ⟨e₀, he₀, rfl⟩
        by_cases hcore : e₀ ∈ (rootedLocationCore P.G ℒ).edgeSet
        · exact Or.inl ⟨e₀, hcore, rfl⟩
        · rw [mem_rootedLocationCore_edgeSet_iff, not_and, not_forall] at hcore
          rcases hcore he₀ with ⟨A, hA⟩
          rw [Classical.not_imp, not_not] at hA
          exact Or.inr ⟨A, hA.1, e₀, hA.2, rfl⟩
      · rintro (⟨e₀, hcore, rfl⟩ | ⟨A, hA, e₀, heA, rfl⟩)
        · exact ⟨e₀, (mem_rootedLocationCore_edgeSet_iff.1 hcore).1, rfl⟩
        · exact ⟨e₀, (hℒ.isComplemented hA).le.edgeSet_subset heA, rfl⟩
  have hE_bot : (placeSumStepHypergraph P.G hℒ ∅).edgeSet =
      (Sum.inl '' (rootedLocationCore P.G ℒ).edgeSet) ∪ (Sum.inr '' ℒ) := by
    ext e
    change (e ∈ Sum.inl '' (rootedLocationCore P.G ℒ).edgeSet ∨
        e ∈ (biUnion ∅
          (fun A : RootedHypergraph α β ↦ mapInlH _ A.toHypergraph)).edgeSet) ∨
      e ∈ (biUnion (hℒ.finite.toFinset \ ∅)
        (fun A : RootedHypergraph α β ↦ (placeNewEdgeSum A).toHypergraph)).edgeSet ↔
      e ∈ (Sum.inl '' (rootedLocationCore P.G ℒ).edgeSet) ∪ (Sum.inr '' ℒ)
    simp only [Finset.sdiff_empty, biUnion, Finset.notMem_empty, Set.iUnion_of_empty,
      Set.iUnion_empty, Set.mem_empty_iff_false, or_false, Set.mem_union, Set.mem_iUnion,
      Set.Finite.mem_toFinset, placeNewEdgeSum, Set.mem_singleton_iff, Set.mem_image]
    exact or_congr_right ⟨fun ⟨A, hA, hEq⟩ ↦ ⟨A, hA, hEq.symm⟩,
      fun ⟨A, hA, hEq⟩ ↦ ⟨A, hA, hEq.symm⟩⟩
  have h_bot : feasibleGroupings (placeSumStepPatchwork P hℒ ∅ (Finset.empty_subset _)) =
      feasibleGroupings P' := by
    refine feasibleGroupings_eq_of_edge_bij
      (placeSumStepPatchwork P hℒ ∅ (Finset.empty_subset _)) P'
      (Sum.elim id newEdge) ?_ ?_ ?_ ?_ ?_
    · rw [placeSumStepPatchwork_G, hP'.vertexSet_eq]
      ext v
      change (v ∈ (rootedLocationCore P.G ℒ).vertexSet ∨
          v ∈ (biUnion ∅
            (fun A : RootedHypergraph α β ↦ mapInlH _ A.toHypergraph)).vertexSet) ∨
        v ∈ (biUnion (hℒ.finite.toFinset \ ∅)
          (fun A : RootedHypergraph α β ↦ (placeNewEdgeSum A).toHypergraph)).vertexSet ↔
        v ∈ (rootedLocationCore P.G ℒ).vertexSet
      simp only [Finset.sdiff_empty, biUnion, Finset.notMem_empty, Set.iUnion_of_empty,
        Set.iUnion_empty, Set.mem_empty_iff_false, or_false, Set.mem_iUnion,
        Set.Finite.mem_toFinset, placeNewEdgeSum]
      refine ⟨?_, fun hv ↦ Or.inl hv⟩
      rintro (hv | ⟨A, hA, hvA⟩)
      · exact hv
      · exact mem_rootSet_subset_rootedLocationCore hℒ hA hvA
    · rw [placeSumStepPatchwork_G]
      ext v
      change v ∈ P.G.roots ↔ v ∈ P'.G.roots
      rw [hP'.roots_eq]
    · rw [placeSumStepPatchwork_G, hE_bot, hP'.edgeSet_eq, Set.image_union,
        ← Set.image_comp, ← Set.image_comp]
      change id '' (rootedLocationCore P.G ℒ).edgeSet ∪ newEdge '' ℒ = _
      rw [Set.image_id]
    · rw [placeSumStepPatchwork_G, hE_bot]
      rintro x (⟨e₁, he₁, rfl⟩ | ⟨A₁, hA₁, rfl⟩) y (⟨e₂, he₂, rfl⟩ | ⟨A₂, hA₂, rfl⟩) hEq
      · exact congrArg Sum.inl hEq
      · exfalso
        change e₁ = newEdge A₂ at hEq
        exact hP'.newEdge_notMem_core hA₂ (hEq ▸ he₁)
      · exfalso
        change newEdge A₁ = e₂ at hEq
        exact hP'.newEdge_notMem_core hA₁ (hEq.symm ▸ he₂)
      · exact congrArg Sum.inr (hP'.injOn_newEdge hA₁ hA₂ hEq)
    · rw [placeSumStepPatchwork_G]
      intro x hx
      rw [hE_bot] at hx
      rcases hx with ⟨e₀, he₀, rfl⟩ | ⟨A, hA, rfl⟩
      · rw [placeSumStepPatchwork_Δ_inl]
        exact hP'.Δ_core he₀
      · rw [placeSumStepPatchwork_Δ_inr]
        exact hP'.Δ_newEdge hA
  rw [h_top, feasibleGroupings_placeSumStepPatchwork P hℒ hℒ.finite.toFinset Finset.Subset.rfl,
    h_bot]

end GraphMinor.GM18
end
