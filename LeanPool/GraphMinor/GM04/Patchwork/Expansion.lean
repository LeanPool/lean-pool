/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM04.Patchwork.Defs
import LeanPool.GraphMinor.GM04.Patchwork.Menger

/-!
# Composition of patchwork expansions and simulation quasi-order (Graph Minors IV, Section 7)

This file formalizes Graph Minors IV, (7.1) (pages 244–247):

* `compVertex` and `compEdge`: composition `η''` of two expansions `η` and `η'`.
* `lemma_7_1_claim_1`–`lemma_7_1_claim_5` and `IsExpansion.comp`: the composition of two expansions
  is an expansion.
* `lemma_7_1_claim_6`–`lemma_7_1_claim_9` and `IsRealizableExpansion.comp`: the composition of two
  realizable expansions is realizable.
* `Simulated.refl` and `Simulated.trans`: simulation is reflexive and transitive (a quasi-order on
  `Ω`-patchworks).
-/

public section

namespace GraphMinor.GM04

open SimpleGraph

universe u v w

variable {Ω : Type w} [Preorder Ω] {α α' α'' : Type*} {β β' β'' : Type*}

/-! ### Properties of `MarchCorresponds` and `marchMapSubgraph` -/

theorem marchCorresponds_refl {π : List α} {x y : α} :
    MarchCorresponds π π x y ↔ x ∈ π ∧ x = y := by
  constructor
  · rintro ⟨i, hi, _, rfl, rfl⟩
    exact ⟨List.getElem_mem hi, rfl⟩
  · rintro ⟨hx, rfl⟩
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    exact ⟨i, hi, hi, rfl, rfl⟩

theorem marchCorresponds_unique_left {π : List α} {π' : List α'} (hπ' : π'.Nodup)
    {x₁ x₂ : α} {y : α'} (h₁ : MarchCorresponds π π' x₁ y) (h₂ : MarchCorresponds π π' x₂ y) :
    x₁ = x₂ := by
  obtain ⟨i₁, hi₁, hi₁', rfl, hy₁⟩ := h₁
  obtain ⟨i₂, hi₂, hi₂', rfl, hy₂⟩ := h₂
  have hidx : i₁ = i₂ := (hπ'.getElem_inj_iff (hi := hi₁') (hj := hi₂')).mp (hy₁.trans hy₂.symm)
  subst hidx
  rfl

theorem marchCorresponds_unique_right {π : List α} {π' : List α'} (hπ : π.Nodup)
    {x : α} {y₁ y₂ : α'} (h₁ : MarchCorresponds π π' x y₁) (h₂ : MarchCorresponds π π' x y₂) :
    y₁ = y₂ := by
  obtain ⟨i₁, hi₁, hi₁', hx₁, rfl⟩ := h₁
  obtain ⟨i₂, hi₂, hi₂', hx₂, rfl⟩ := h₂
  have hidx : i₁ = i₂ := (hπ.getElem_inj_iff (hi := hi₁) (hj := hi₂)).mp (hx₁.trans hx₂.symm)
  subst hidx
  rfl

theorem marchCorresponds_comp {π₁ : List α} {π₂ : List α'} {π₃ : List α''}
    (h₂ : π₂.Nodup) (h₁₂ : π₁.length = π₂.length)
    {x : α} {z : α''} :
    MarchCorresponds π₁ π₃ x z ↔
      ∃ y : α', MarchCorresponds π₁ π₂ x y ∧ MarchCorresponds π₂ π₃ y z := by
  constructor
  · rintro ⟨i, hi₁, hi₃, rfl, rfl⟩
    have hi₂ : i < π₂.length := h₁₂ ▸ hi₁
    exact ⟨π₂[i], ⟨i, hi₁, hi₂, rfl, rfl⟩, ⟨i, hi₂, hi₃, rfl, rfl⟩⟩
  · rintro ⟨y, ⟨i, hi₁, hi₂, rfl, rfl⟩, ⟨j, hj₂, hj₃, hy, rfl⟩⟩
    have hij : i = j := (h₂.getElem_inj_iff (hi := hi₂) (hj := hj₂)).mp hy.symm
    subst hij
    exact ⟨i, hi₁, hj₃, rfl, rfl⟩

theorem marchMapSubgraph_id {π : List α} {δ : (⊤ : SimpleGraph α).Subgraph}
    (hverts : δ.verts ⊆ {x | x ∈ π}) :
    marchMapSubgraph π π δ = δ := by
  ext x y
  · simp only [marchMapSubgraph, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨x', hx', hcorr⟩
      obtain ⟨_, rfl⟩ := marchCorresponds_refl.mp hcorr
      exact hx'
    · intro hx
      exact ⟨x, hx, marchCorresponds_refl.mpr ⟨hverts hx, rfl⟩⟩
  · simp only [marchMapSubgraph]
    constructor
    · rintro ⟨_, x₁, x₂, hx₁, hx₂, hadj⟩
      obtain ⟨_, rfl⟩ := marchCorresponds_refl.mp hx₁
      obtain ⟨_, rfl⟩ := marchCorresponds_refl.mp hx₂
      exact hadj
    · intro hadj
      have hx : x ∈ π := hverts (δ.edge_vert hadj)
      have hy : y ∈ π := hverts (δ.edge_vert hadj.symm)
      exact ⟨hadj.ne, x, y, marchCorresponds_refl.mpr ⟨hx, rfl⟩,
        marchCorresponds_refl.mpr ⟨hy, rfl⟩, hadj⟩

theorem marchMapSubgraph_comp {π₁ : List α} {π₂ : List α'} {π₃ : List α''}
    (h₂ : π₂.Nodup) (h₁₂ : π₁.length = π₂.length) (δ : (⊤ : SimpleGraph α).Subgraph) :
    marchMapSubgraph π₂ π₃ (marchMapSubgraph π₁ π₂ δ) = marchMapSubgraph π₁ π₃ δ := by
  ext z₁ z₂
  · simp only [marchMapSubgraph, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨y, ⟨x, hx, hxy⟩, hyz⟩
      exact ⟨x, hx, (marchCorresponds_comp h₂ h₁₂).mpr ⟨y, hxy, hyz⟩⟩
    · rintro ⟨x, hx, hxz⟩
      obtain ⟨y, hxy, hyz⟩ := (marchCorresponds_comp h₂ h₁₂).mp hxz
      exact ⟨y, ⟨x, hx, hxy⟩, hyz⟩
  · simp only [marchMapSubgraph]
    constructor
    · rintro ⟨hne, y₁, y₂, hyz₁, hyz₂, _, x₁, x₂, hxy₁, hxy₂, hadj⟩
      exact ⟨hne, x₁, x₂, (marchCorresponds_comp h₂ h₁₂).mpr ⟨y₁, hxy₁, hyz₁⟩,
        (marchCorresponds_comp h₂ h₁₂).mpr ⟨y₂, hxy₂, hyz₂⟩, hadj⟩
    · rintro ⟨hne, x₁, x₂, hxz₁, hxz₂, hadj⟩
      obtain ⟨y₁, hxy₁, hyz₁⟩ := (marchCorresponds_comp h₂ h₁₂).mp hxz₁
      obtain ⟨y₂, hxy₂, hyz₂⟩ := (marchCorresponds_comp h₂ h₁₂).mp hxz₂
      have hyne : y₁ ≠ y₂ := by
        intro hEq
        subst hEq
        exact hne (marchCorresponds_unique_right h₂ hyz₁ hyz₂)
      exact ⟨hne, y₁, y₂, hyz₁, hyz₂, hyne, x₁, x₂, hxy₁, hxy₂, hadj⟩

/-! ### Composition of expansions: Graph Minors IV, (7.1), claims (1)–(5) -/

/-- The vertex map `η''(v) = ⋃ (η'(v') : v' ∈ η(v))` of the composed expansion in (7.1)
(Graph Minors IV, page 244). -/
def compVertex (ηv : α → Set α') (η'v : α' → Set α'') (v : α) : Set α'' :=
  ⋃ v' ∈ ηv v, η'v v'

/-- The edge map `η''(e) = η'(η(e))` of the composed expansion in (7.1)
(Graph Minors IV, page 244). -/
def compEdge (ηe : β → β') (η'e : β' → β'') (e : β) : β'' :=
  η'e (ηe e)

@[simp]
theorem mem_compVertex_iff {ηv : α → Set α'} {η'v : α' → Set α''} {v : α} {w : α''} :
    w ∈ compVertex ηv η'v v ↔ ∃ v' ∈ ηv v, w ∈ η'v v' := by
  simp [compVertex]

@[simp]
theorem compEdge_apply (ηe : β → β') (η'e : β' → β'') (e : β) :
    compEdge ηe η'e e = η'e (ηe e) := by
  rfl

/-- Graph Minors IV, (7.1), claim (1) (page 245):
"For distinct $v_1, v_2 \in V(G)$, $\eta''(v_1) \cap \eta''(v_2) = \emptyset$" -/
theorem lemma_7_1_claim_1 {P : Patchwork Ω α β} {P' : Patchwork Ω α' β'}
    {P'' : Patchwork Ω α'' β''} {ηv : α → Set α'} {ηe : β → β'}
    {η'v : α' → Set α''} {η'e : β' → β''}
    (hη : IsExpansion P P' ηv ηe) (hη' : IsExpansion P' P'' η'v η'e)
    {v₁ v₂ : α} (hv₁ : v₁ ∈ P.G.vertexSet) (hv₂ : v₂ ∈ P.G.vertexSet) (hne : v₁ ≠ v₂) :
    Disjoint (compVertex ηv η'v v₁) (compVertex ηv η'v v₂) := by
  refine Set.disjoint_left.mpr fun w h₁ h₂ ↦ ?_
  rw [mem_compVertex_iff] at h₁ h₂
  obtain ⟨v₁', hv₁', hw₁⟩ := h₁
  obtain ⟨v₂', hv₂', hw₂⟩ := h₂
  have hne' : v₁' ≠ v₂' := by
    intro hEq
    subst hEq
    exact Set.disjoint_left.mp (hη.vertex_disjoint v₁ hv₁ v₂ hv₂ hne) hv₁' hv₂'
  exact Set.disjoint_left.mp
    (hη'.vertex_disjoint v₁' (hη.vertex_subset v₁ hv₁ hv₁')
      v₂' (hη.vertex_subset v₂ hv₂ hv₂') hne')
    hw₁ hw₂

/-- Graph Minors IV, (7.1), claim (2) (page 245):
"For each $e \in E(G) - \operatorname{dom}(\mu)$, if $v$ is an end of $e$ in $G$ then
$\eta''(v)$ contains an end of $\eta''(e)$ in $G''$." -/
theorem lemma_7_1_claim_2 {P : Patchwork Ω α β} {P' : Patchwork Ω α' β'}
    {P'' : Patchwork Ω α'' β''} {ηv : α → Set α'} {ηe : β → β'}
    {η'v : α' → Set α''} {η'e : β' → β''}
    (hη : IsExpansion P P' ηv ηe) (hη' : IsExpansion P' P'' η'v η'e)
    {e : β} (he : e ∈ P.G.edgeSet) (hnd : e ∉ P.dom) {v : α} (hinc : P.G.Inc e v) :
    ∃ v'' ∈ compVertex ηv η'v v, P''.G.Inc (compEdge ηe η'e e) v'' := by
  obtain ⟨v', hv', hinc'⟩ := hη.ends_nonempty e he hnd v hinc
  have he' : ηe e ∈ P'.G.edgeSet := hη.edge_mem e he
  have hnd' : ηe e ∉ P'.dom := fun hd' ↦ hnd ((hη.mem_dom_iff e he).mpr hd')
  obtain ⟨v'', hv'', hinc''⟩ := hη'.ends_nonempty (ηe e) he' hnd' v' hinc'
  exact ⟨v'', mem_compVertex_iff.mpr ⟨v', hv', hv''⟩, hinc''⟩

/-- Graph Minors IV, (7.1), claim (3) (page 245):
"For each $e \in \operatorname{dom}(\mu)$, $\mu(e)$ and $\mu''(\eta''(e))$ have the same
length, $k$, say, and for $1 \le i \le k$, $\eta''(v)$ contains the $i$th term of
$\mu''(\eta''(e))$ where $v$ is the $i$th term of $\mu(e)$." -/
theorem lemma_7_1_claim_3 {P : Patchwork Ω α β} {P' : Patchwork Ω α' β'}
    {P'' : Patchwork Ω α'' β''} {ηv : α → Set α'} {ηe : β → β'}
    {η'v : α' → Set α''} {η'e : β' → β''}
    (hη : IsExpansion P P' ηv ηe) (hη' : IsExpansion P' P'' η'v η'e)
    {e : β} (he : e ∈ P.dom) :
    (P.μ e).length = (P''.μ (compEdge ηe η'e e)).length ∧
      ∀ (i : ℕ) (hi : i < (P.μ e).length) (hi'' : i < (P''.μ (compEdge ηe η'e e)).length),
        (P''.μ (compEdge ηe η'e e))[i] ∈ compVertex ηv η'v (P.μ e)[i] := by
  have heE : e ∈ P.G.edgeSet := P.dom_subset he
  have he' : ηe e ∈ P'.dom := (hη.mem_dom_iff e heE).mp he
  have hlen1 := hη.μ_length e he
  have hlen2 := hη'.μ_length (ηe e) he'
  refine ⟨hlen1.trans hlen2, fun i hi hi'' ↦ ?_⟩
  have hi' : i < (P'.μ (ηe e)).length := hlen1 ▸ hi
  exact mem_compVertex_iff.mpr ⟨(P'.μ (ηe e))[i], hη.μ_mem e he i hi hi',
    hη'.μ_mem (ηe e) he' i hi' hi''⟩

/-- Graph Minors IV, (7.1), claim (4) (page 245):
"$\pi(G)$ and $\pi(G'')$ have the same length, $k$, say, and for $1 \le i \le k$ $\eta''(v)$
contains the $i$th term of $\pi(G'')$ where $v$ is the $i$th term of $\pi(G)$." -/
theorem lemma_7_1_claim_4 {P : Patchwork Ω α β} {P' : Patchwork Ω α' β'}
    {P'' : Patchwork Ω α'' β''} {ηv : α → Set α'} {ηe : β → β'}
    {η'v : α' → Set α''} {η'e : β' → β''}
    (hη : IsExpansion P P' ηv ηe) (hη' : IsExpansion P' P'' η'v η'e) :
    P.G.roots.length = P''.G.roots.length ∧
      ∀ (i : ℕ) (hi : i < P.G.roots.length) (hi'' : i < P''.G.roots.length),
        P''.G.roots[i] ∈ compVertex ηv η'v P.G.roots[i] := by
  refine ⟨hη.roots_length.trans hη'.roots_length, fun i hi hi'' ↦ ?_⟩
  have hi' : i < P'.G.roots.length := hη.roots_length ▸ hi
  exact mem_compVertex_iff.mpr ⟨P'.G.roots[i], hη.roots_mem i hi hi',
    hη'.roots_mem i hi' hi''⟩

/-- Graph Minors IV, (7.1), claim (5) (page 245):
"For each $e \in \operatorname{dom}(\mu)$, $\mu(e) \to \mu''(\eta''(e))$ maps $\Delta(e)$ to
$\Delta''(\eta''(e))$." -/
theorem lemma_7_1_claim_5 {P : Patchwork Ω α β} {P' : Patchwork Ω α' β'}
    {P'' : Patchwork Ω α'' β''} {ηv : α → Set α'} {ηe : β → β'}
    {η'v : α' → Set α''} {η'e : β' → β''}
    (hη : IsExpansion P P' ηv ηe) (hη' : IsExpansion P' P'' η'v η'e)
    {e : β} (he : e ∈ P.dom) :
    Set.MapsTo (marchMapSubgraph (P.μ e) (P''.μ (compEdge ηe η'e e)))
      (P.Δ e).groupings (P''.Δ (compEdge ηe η'e e)).groupings := by
  intro δ hδ
  have heE : e ∈ P.G.edgeSet := P.dom_subset he
  have he' : ηe e ∈ P'.dom := (hη.mem_dom_iff e heE).mp he
  rw [← marchMapSubgraph_comp (P'.μ_nodup (ηe e) he') (hη.μ_length e he) δ]
  exact hη'.maps_Δ (ηe e) he' (hη.maps_Δ e he hδ)

/-- First statement of Graph Minors IV, (7.1) (page 245): the composition `η''` of an expansion `η`
of `P` in `P'` and an expansion `η'` of `P'` in `P''` is an expansion of `P` in `P''`. -/
theorem IsExpansion.comp {P : Patchwork Ω α β} {P' : Patchwork Ω α' β'}
    {P'' : Patchwork Ω α'' β''} {ηv : α → Set α'} {ηe : β → β'}
    {η'v : α' → Set α''} {η'e : β' → β''}
    (hη : IsExpansion P P' ηv ηe) (hη' : IsExpansion P' P'' η'v η'e) :
    IsExpansion P P'' (compVertex ηv η'v) (compEdge ηe η'e) where
  vertex_nonempty v hv := by
    obtain ⟨v', hv'⟩ := hη.vertex_nonempty v hv
    obtain ⟨v'', hv''⟩ := hη'.vertex_nonempty v' (hη.vertex_subset v hv hv')
    exact ⟨v'', mem_compVertex_iff.mpr ⟨v', hv', hv''⟩⟩
  vertex_subset v hv := by
    intro v'' hv''
    rw [mem_compVertex_iff] at hv''
    obtain ⟨v', hv', hv''⟩ := hv''
    exact hη'.vertex_subset v' (hη.vertex_subset v hv hv') hv''
  edge_mem e he := hη'.edge_mem (ηe e) (hη.edge_mem e he)
  vertex_disjoint _ hv₁ _ hv₂ hne := lemma_7_1_claim_1 hη hη' hv₁ hv₂ hne
  edge_injOn e₁ he₁ e₂ he₂ hEq :=
    hη.edge_injOn he₁ he₂ (hη'.edge_injOn (hη.edge_mem e₁ he₁) (hη.edge_mem e₂ he₂) hEq)
  mem_dom_iff e he :=
    (hη.mem_dom_iff e he).trans (hη'.mem_dom_iff (ηe e) (hη.edge_mem e he))
  ends_nonempty _ he hnd _ hinc := lemma_7_1_claim_2 hη hη' he hnd hinc
  μ_length _ he := (lemma_7_1_claim_3 hη hη' he).1
  μ_mem _ he := (lemma_7_1_claim_3 hη hη' he).2
  roots_length := (lemma_7_1_claim_4 hη hη').1
  roots_mem := (lemma_7_1_claim_4 hη hη').2
  maps_Δ _ he := lemma_7_1_claim_5 hη hη' he
  φ_le e he := (hη.φ_le e he).trans (hη'.φ_le (ηe e) (hη.edge_mem e he))

/-! ### Helper lemmas on `sameComponent`, `Realizes`, and `expandedGrouping` -/

/-- For any `e ∈ E(G)` (whether in `dom(μ)` or not) and `v ∈ V_G(e)`, `η(v)` contains an end of
`η(e)` in `G'`. -/
theorem IsExpansion.exists_inc_of_inc {P : Patchwork Ω α β} {P' : Patchwork Ω α' β'}
    {ηv : α → Set α'} {ηe : β → β'} (hη : IsExpansion P P' ηv ηe)
    {e : β} (he : e ∈ P.G.edgeSet) {v : α} (hv : P.G.Inc e v) :
    ∃ v' ∈ ηv v, P'.G.Inc (ηe e) v' := by
  by_cases hd : e ∈ P.dom
  · have hv_mem : v ∈ P.μ e := by
      have hset := P.μ_set e hd
      have hv' : v ∈ P.G.ends e := hv
      rwa [← hset] at hv'
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hv_mem
    have hi' : i < (P'.μ (ηe e)).length := (hη.μ_length e hd) ▸ hi
    refine ⟨(P'.μ (ηe e))[i], hη.μ_mem e hd i hi hi', ?_⟩
    have hd' : ηe e ∈ P'.dom := (hη.mem_dom_iff e he).mp hd
    have hset' := P'.μ_set (ηe e) hd'
    change (P'.μ (ηe e))[i] ∈ P'.G.ends (ηe e)
    rw [← hset']
    exact List.getElem_mem hi'
  · exact hη.ends_nonempty e he hd v hv

/-- Two vertices `p, q` belong to the same component of a subgraph `K`. -/
def sameComponent (K : (⊤ : SimpleGraph α).Subgraph) (p q : α) : Prop :=
  ∃ D, IsComponent K D ∧ p ∈ D.verts ∧ q ∈ D.verts

theorem sameComponent_iff {K : (⊤ : SimpleGraph α).Subgraph} {p q : α} :
    sameComponent K p q ↔
      ∃ (hp : p ∈ K.verts) (hq : q ∈ K.verts), K.coe.Reachable ⟨p, hp⟩ ⟨q, hq⟩ := by
  constructor
  · rintro ⟨_, ⟨x, rfl⟩, ⟨hp, hxp⟩, ⟨hq, hxq⟩⟩
    exact ⟨hp, hq, hxp.symm.trans hxq⟩
  · rintro ⟨hp, hq, hr⟩
    exact ⟨component K ⟨p, hp⟩, ⟨⟨p, hp⟩, rfl⟩,
      self_mem_componentVerts K ⟨p, hp⟩, ⟨hq, hr⟩⟩

theorem sameComponent.symm {K : (⊤ : SimpleGraph α).Subgraph} {p q : α}
    (h : sameComponent K p q) : sameComponent K q p := by
  obtain ⟨D, hD, hp, hq⟩ := h
  exact ⟨D, hD, hq, hp⟩

theorem sameComponent.trans {K : (⊤ : SimpleGraph α).Subgraph} {p q r : α}
    (hpq : sameComponent K p q) (hqr : sameComponent K q r) : sameComponent K p r := by
  obtain ⟨D₁, hD₁, hp, hq₁⟩ := hpq
  obtain ⟨D₂, hD₂, hq₂, hr⟩ := hqr
  have hEq : D₁ = D₂ := hD₁.eq_of_mem hD₂ hq₁ hq₂
  exact ⟨D₁, hD₁, hp, hEq ▸ hr⟩

theorem sameComponent_of_adj {K : (⊤ : SimpleGraph α).Subgraph} {p q : α}
    (h : K.Adj p q) : sameComponent K p q :=
  sameComponent_iff.mpr ⟨K.edge_vert h, K.edge_vert h.symm, Adj.reachable h.coe⟩

theorem sameComponent.mono {K H : (⊤ : SimpleGraph α).Subgraph} (hle : K ≤ H) {p q : α}
    (h : sameComponent K p q) : sameComponent H p q := by
  rw [sameComponent_iff] at h ⊢
  obtain ⟨hp, hq, hr⟩ := h
  refine ⟨hle.1 hp, hle.1 hq, ?_⟩
  suffices ∀ x y : K.verts, K.coe.Reachable x y →
      H.coe.Reachable ⟨x.1, hle.1 x.2⟩ ⟨y.1, hle.1 y.2⟩ from
    this ⟨p, hp⟩ ⟨q, hq⟩ hr
  intro x y hxy
  rw [reachable_iff_reflTransGen] at hxy ⊢
  induction hxy with
  | refl => exact Relation.ReflTransGen.refl
  | @tail a b _ hab ih =>
    exact Relation.ReflTransGen.tail ih (hle.2 hab)

theorem sameComponent_iff_adj_of_isGrouping {V : Set α} {δ : (⊤ : SimpleGraph α).Subgraph}
    (hgrp : IsGrouping V δ) {p q : α} (hne : p ≠ q) :
    sameComponent δ p q ↔ δ.Adj p q := by
  constructor
  · rintro ⟨D, hD, hp, hq⟩
    have hcomp := isCompleteSubgraph_iff.mp (hgrp.2 D hD)
    exact hD.le.2 (hcomp p hp q hq hne)
  · exact sameComponent_of_adj

theorem exists_isComponent_verts_eq_iff {H : (⊤ : SimpleGraph α).Subgraph} {S : Set α}
    (hne : S.Nonempty) (hsub : S ⊆ H.verts) :
    (∃ D, IsComponent H D ∧ D.verts = S) ↔
      (∀ a ∈ S, ∀ b, H.Adj a b → b ∈ S) ∧
      (∀ a ∈ S, ∀ b ∈ S, sameComponent H a b) := by
  constructor
  · rintro ⟨D, hD, rfl⟩
    refine ⟨?_, fun a ha b hb ↦ ⟨D, hD, ha, hb⟩⟩
    obtain ⟨x, rfl⟩ := hD
    rintro a ⟨ha, hxa⟩ b hab
    exact ⟨H.edge_vert hab.symm, hxa.trans (Adj.reachable hab.coe)⟩
  · rintro ⟨hclosed, hconn⟩
    obtain ⟨a₀, ha₀⟩ := hne
    let x : H.verts := ⟨a₀, hsub ha₀⟩
    refine ⟨component H x, ⟨x, rfl⟩, ?_⟩
    ext b
    simp only [component_verts, mem_componentVerts_iff]
    constructor
    · rintro ⟨hbH, hxb⟩
      suffices ∀ y : H.verts, H.coe.Reachable x y → y.1 ∈ S from this ⟨b, hbH⟩ hxb
      intro y hy
      rw [reachable_iff_reflTransGen] at hy
      induction hy with
      | refl => exact ha₀
      | @tail u w _ huw ih => exact hclosed u.1 ih w.1 huw
    · intro hbS
      obtain ⟨_, hbH, hreach⟩ := sameComponent_iff.mp (hconn a₀ ha₀ b hbS)
      exact ⟨hbH, hreach⟩

/-- The subgraph of `K_{V''}` on `V''` in which distinct `a, b ∈ V''` are adjacent if and only if
`a ∈ η'v p` and `b ∈ η'v q` for some `p, q` in the same component of `δ`
(Graph Minors IV, Section 7, page 246). -/
def expandedGrouping (V'' : Set α'') (η'v : α' → Set α'')
    (δ : (⊤ : SimpleGraph α').Subgraph) : (⊤ : SimpleGraph α'').Subgraph where
  verts := V''
  Adj a b := a ∈ V'' ∧ b ∈ V'' ∧ a ≠ b ∧
    ∃ p q, sameComponent δ p q ∧ a ∈ η'v p ∧ b ∈ η'v q
  adj_sub h := h.2.2.1
  edge_vert h := h.1
  symm := ⟨by
    rintro a b ⟨ha, hb, hne, p, q, hpq, hap, hbq⟩
    exact ⟨hb, ha, hne.symm, q, p, hpq.symm, hbq, hap⟩⟩

@[simp]
theorem expandedGrouping_verts (V'' : Set α'') (η'v : α' → Set α'')
    (δ : (⊤ : SimpleGraph α').Subgraph) :
    (expandedGrouping V'' η'v δ).verts = V'' := by
  rfl

theorem expandedGrouping_isGrouping {P' : Patchwork Ω α' β'} {P'' : Patchwork Ω α'' β''}
    {η'v : α' → Set α''} {η'e : β' → β''} (hη' : IsExpansion P' P'' η'v η'e)
    (V'' : Set α'') {δ : (⊤ : SimpleGraph α').Subgraph} (hδ_verts : δ.verts ⊆ P'.G.vertexSet) :
    IsGrouping V'' (expandedGrouping V'' η'v δ) := by
  rw [isGrouping_iff]
  refine ⟨subset_rfl, fun a b c hac hab hbc ↦ ?_⟩
  rcases hab with ⟨ha, _, _, p, q, hpq, hap, hbq⟩
  rcases hbc with ⟨_, hc, _, r, s, hrs, hbr, hcs⟩
  have hqV : q ∈ P'.G.vertexSet := by
    obtain ⟨_, hq, _⟩ := sameComponent_iff.mp hpq
    exact hδ_verts hq
  have hrV : r ∈ P'.G.vertexSet := by
    obtain ⟨hr, _, _⟩ := sameComponent_iff.mp hrs
    exact hδ_verts hr
  have hqr : q = r := by
    by_contra hne
    exact Set.disjoint_left.mp (hη'.vertex_disjoint q hqV r hrV hne) hbq hbr
  subst hqr
  exact ⟨ha, hc, hac, p, s, hpq.trans hrs, hap, hcs⟩

private theorem mem_η_iff_marchCorresponds {P' : Patchwork Ω α' β'} {P'' : Patchwork Ω α'' β''}
    {η'v : α' → Set α''} {η'e : β' → β''} (hη' : IsExpansion P' P'' η'v η'e)
    {f : β'} (hf : f ∈ P'.dom) {p : α'} (hp : p ∈ P'.G.ends f) {a : α''} :
    (a ∈ P''.G.ends (η'e f) ∧ a ∈ η'v p) ↔
      MarchCorresponds (P'.μ f) (P''.μ (η'e f)) p a := by
  have hfE : f ∈ P'.G.edgeSet := P'.dom_subset hf
  have he'' : η'e f ∈ P''.dom := (hη'.mem_dom_iff f hfE).mp hf
  constructor
  · rintro ⟨ha_end, hap⟩
    have ha_mem : a ∈ P''.μ (η'e f) := by
      rwa [← P''.μ_set (η'e f) he''] at ha_end
    obtain ⟨i, hi', rfl⟩ := List.getElem_of_mem ha_mem
    have hi : i < (P'.μ f).length := (hη'.μ_length f hf).symm ▸ hi'
    have hmem_i : (P''.μ (η'e f))[i] ∈ η'v (P'.μ f)[i] := hη'.μ_mem f hf i hi hi'
    have hp_i_end : (P'.μ f)[i] ∈ P'.G.ends f := by
      rw [← P'.μ_set f hf]
      exact List.getElem_mem hi
    have hEq : (P'.μ f)[i] = p := by
      by_contra hne
      exact Set.disjoint_left.mp
        (hη'.vertex_disjoint (P'.μ f)[i] (P'.G.vertex_mem_of_inc hp_i_end)
          p (P'.G.vertex_mem_of_inc hp) hne)
        hmem_i hap
    exact ⟨i, hi, hi', hEq, rfl⟩
  · rintro ⟨i, hi, hi', rfl, rfl⟩
    refine ⟨?_, hη'.μ_mem f hf i hi hi'⟩
    rw [← P''.μ_set (η'e f) he'']
    exact List.getElem_mem hi'

theorem expandedGrouping_eq_marchMapSubgraph {P' : Patchwork Ω α' β'} {P'' : Patchwork Ω α'' β''}
    {η'v : α' → Set α''} {η'e : β' → β''} (hη' : IsExpansion P' P'' η'v η'e)
    {f : β'} (hf : f ∈ P'.dom) {δ : (⊤ : SimpleGraph α').Subgraph} (hδ : δ ∈ P'.Δ f) :
    expandedGrouping (P''.G.ends (η'e f)) η'v δ =
      marchMapSubgraph (P'.μ f) (P''.μ (η'e f)) δ := by
  have hfE : f ∈ P'.G.edgeSet := P'.dom_subset hf
  have he'' : η'e f ∈ P''.dom := (hη'.mem_dom_iff f hfE).mp hf
  have hδ_verts : δ.verts = P'.G.ends f :=
    ((P'.Δ f).verts_eq δ hδ).trans (P'.Δ_verts f hfE)
  have hδ_grp : IsGrouping (P'.G.ends f) δ :=
    P'.Δ_verts f hfE ▸ (P'.Δ f).isGrouping δ hδ
  ext a b
  · simp only [expandedGrouping, marchMapSubgraph, Set.mem_ofPred_eq, hδ_verts]
    constructor
    · intro ha
      have ha_mem : a ∈ P''.μ (η'e f) := by rwa [← P''.μ_set (η'e f) he''] at ha
      obtain ⟨i, hi', rfl⟩ := List.getElem_of_mem ha_mem
      have hi : i < (P'.μ f).length := (hη'.μ_length f hf).symm ▸ hi'
      refine ⟨(P'.μ f)[i], ?_, ⟨i, hi, hi', rfl, rfl⟩⟩
      rw [← P'.μ_set f hf]
      exact List.getElem_mem hi
    · rintro ⟨x, hx, hcorr⟩
      exact ((mem_η_iff_marchCorresponds hη' hf hx).mpr hcorr).1
  · simp only [expandedGrouping, marchMapSubgraph]
    constructor
    · rintro ⟨ha, hb, hne, p, q, hpq, hap, hbq⟩
      obtain ⟨hp_verts, hq_verts, _⟩ := sameComponent_iff.mp hpq
      have hp_end : p ∈ P'.G.ends f := hδ_verts ▸ hp_verts
      have hq_end : q ∈ P'.G.ends f := hδ_verts ▸ hq_verts
      have hcorr_p := (mem_η_iff_marchCorresponds hη' hf hp_end).mp ⟨ha, hap⟩
      have hcorr_q := (mem_η_iff_marchCorresponds hη' hf hq_end).mp ⟨hb, hbq⟩
      have hpq_ne : p ≠ q := by
        intro hEq
        subst hEq
        exact hne (marchCorresponds_unique_right (P'.μ_nodup f hf) hcorr_p hcorr_q)
      exact ⟨hne, p, q, hcorr_p, hcorr_q,
        (sameComponent_iff_adj_of_isGrouping hδ_grp hpq_ne).mp hpq⟩
    · rintro ⟨hne, p, q, hcorr_p, hcorr_q, hadj⟩
      have hp_end : p ∈ P'.G.ends f := hδ_verts ▸ δ.edge_vert hadj
      have hq_end : q ∈ P'.G.ends f := hδ_verts ▸ δ.edge_vert hadj.symm
      obtain ⟨ha, hap⟩ := (mem_η_iff_marchCorresponds hη' hf hp_end).mpr hcorr_p
      obtain ⟨hb, hbq⟩ := (mem_η_iff_marchCorresponds hη' hf hq_end).mpr hcorr_q
      exact ⟨ha, hb, hne, p, q, sameComponent_of_adj hadj, hap, hbq⟩

/-- Graph Minors IV, (7.1), claim (6) (page 246):
For `f ∈ E(G')` with `e = η'(f)` and `δ_f ∈ Δ'(f)`, the subgraph `δ''_e` (`expandedGrouping`)
belongs to `Δ''(e)`. -/
theorem lemma_7_1_claim_6 {P' : Patchwork Ω α' β'} {P'' : Patchwork Ω α'' β''}
    {η'v : α' → Set α''} {η'e : β' → β''} (hη' : IsExpansion P' P'' η'v η'e)
    {f : β'} (hf : f ∈ P'.G.edgeSet) {δf : (⊤ : SimpleGraph α').Subgraph} (hδf : δf ∈ P'.Δ f) :
    expandedGrouping (P''.G.ends (η'e f)) η'v δf ∈ P''.Δ (η'e f) := by
  have he : η'e f ∈ P''.G.edgeSet := hη'.edge_mem f hf
  by_cases hf_dom : f ∈ P'.dom
  · rw [expandedGrouping_eq_marchMapSubgraph hη' hf_dom hδf]
    exact hη'.maps_Δ f hf_dom hδf
  · have he_not_dom : η'e f ∉ P''.dom := fun hd ↦ hf_dom ((hη'.mem_dom_iff f hf).mpr hd)
    have hfree : (P''.Δ (η'e f)).IsFree := P''.Δ_free (η'e f) he he_not_dom
    have hδf_verts : δf.verts ⊆ P'.G.vertexSet := by
      rw [((P'.Δ f).verts_eq δf hδf).trans (P'.Δ_verts f hf)]
      exact fun _ hv ↦ P'.G.vertex_mem_of_inc hv
    have hgrp : IsGrouping (P''.Δ (η'e f)).verts (expandedGrouping (P''.G.ends (η'e f)) η'v δf)
      := by
      rw [P''.Δ_verts (η'e f) he]
      exact expandedGrouping_isGrouping hη' _ hδf_verts
    exact hfree _ hgrp (P''.Δ_verts (η'e f) he).symm

/-! ### Composition of realizable expansions: Graph Minors IV, (7.1), claims (7)–(9) -/

open Classical in
/-- The family `δ''` constructed in the proof of (7.1) (Graph Minors IV, page 246):
for `e ∈ E(G'') - η''(E(G))`, `δ''_e = δ'_e` if `e ∉ η'(E(G'))`, and `δ''_e` is the expanded
grouping of `δ_f` if `e = η'(f)` with `f ∈ E(G')`. -/
noncomputable def compRealizationChoice (P' : Patchwork Ω α' β') (P'' : Patchwork Ω α'' β'')
    (η'v : α' → Set α'') (η'e : β' → β'')
    (δ : β' → (⊤ : SimpleGraph α').Subgraph) (δ' : β'' → (⊤ : SimpleGraph α'').Subgraph)
    (e : β'') : (⊤ : SimpleGraph α'').Subgraph :=
  if h : ∃ f ∈ P'.G.edgeSet, η'e f = e then
    expandedGrouping (P''.G.ends e) η'v (δ h.choose)
  else
    δ' e

omit [Preorder Ω] in
theorem compRealizationChoice_of_notMem {P' : Patchwork Ω α' β'} {P'' : Patchwork Ω α'' β''}
    {η'v : α' → Set α''} {η'e : β' → β''}
    {δ : β' → (⊤ : SimpleGraph α').Subgraph} {δ' : β'' → (⊤ : SimpleGraph α'').Subgraph}
    {e : β''} (he : e ∉ η'e '' P'.G.edgeSet) :
    compRealizationChoice P' P'' η'v η'e δ δ' e = δ' e := by
  have h : ¬∃ f ∈ P'.G.edgeSet, η'e f = e := fun ⟨f, hf, hfe⟩ ↦ he ⟨f, hf, hfe⟩
  dsimp only [compRealizationChoice]
  rw [dite_eq_right_of_eq_false (eq_false h)]

theorem compRealizationChoice_apply_image {P' : Patchwork Ω α' β'} {P'' : Patchwork Ω α'' β''}
    {η'v : α' → Set α''} {η'e : β' → β''} (hη' : IsExpansion P' P'' η'v η'e)
    {δ : β' → (⊤ : SimpleGraph α').Subgraph} {δ' : β'' → (⊤ : SimpleGraph α'').Subgraph}
    {f : β'} (hf : f ∈ P'.G.edgeSet) :
    compRealizationChoice P' P'' η'v η'e δ δ' (η'e f) =
      expandedGrouping (P''.G.ends (η'e f)) η'v (δ f) := by
  have h : ∃ f' ∈ P'.G.edgeSet, η'e f' = η'e f := ⟨f, hf, rfl⟩
  dsimp only [compRealizationChoice]
  rw [dite_eq_left_of_eq_true (eq_true h)]
  have hf_eq : h.choose = f := hη'.edge_injOn h.choose_spec.1 hf h.choose_spec.2
  rw [hf_eq]

/-- Graph Minors IV, (7.1), claim (7) (page 246):
"No edge of $H''$ joins a vertex of $\eta''(v)$ to a vertex of $V(G'') - \eta''(v)$." -/
theorem lemma_7_1_claim_7 {P : Patchwork Ω α β} {P' : Patchwork Ω α' β'}
    {P'' : Patchwork Ω α'' β''} {ηv : α → Set α'} {ηe : β → β'}
    {η'v : α' → Set α''} {η'e : β' → β''}
    (hη : IsExpansion P P' ηv ηe) (hη' : IsExpansion P' P'' η'v η'e)
    {δ : β' → (⊤ : SimpleGraph α').Subgraph}
    (hδ : ∀ f ∈ (P'.deleteEdges (ηe '' P.G.edgeSet)).G.edgeSet, δ f ∈ P'.Δ f)
    (hH_real : Realizes P P' ηv ηe
      (realizationOf (P'.deleteEdges (ηe '' P.G.edgeSet)).G.toHypergraph δ))
    {δ' : β'' → (⊤ : SimpleGraph α'').Subgraph}
    (hH'_real : Realizes P' P'' η'v η'e
      (realizationOf (P''.deleteEdges (η'e '' P'.G.edgeSet)).G.toHypergraph δ'))
    {v : α} (hv : v ∈ P.G.vertexSet) {a b : α''} (ha : a ∈ compVertex ηv η'v v)
    (hab : (realizationOf
      (P''.deleteEdges (compEdge ηe η'e '' P.G.edgeSet)).G.toHypergraph
      (compRealizationChoice P' P'' η'v η'e δ δ')).Adj a b) :
    b ∈ compVertex ηv η'v v := by
  obtain ⟨v', hv', ha_v'⟩ := mem_compVertex_iff.mp ha
  have hv'V : v' ∈ P'.G.vertexSet := hη.vertex_subset v hv hv'
  rw [realizationOf_adj] at hab
  obtain ⟨e, ⟨heE, he_not_comp⟩, hab⟩ := hab
  by_cases he_im : e ∈ η'e '' P'.G.edgeSet
  · obtain ⟨f, hfE, rfl⟩ := he_im
    have hf_not_im : f ∉ ηe '' P.G.edgeSet := by
      rintro ⟨g, hg, rfl⟩
      exact he_not_comp ⟨g, hg, rfl⟩
    have hf_del : f ∈ (P'.deleteEdges (ηe '' P.G.edgeSet)).G.edgeSet := ⟨hfE, hf_not_im⟩
    rw [compRealizationChoice_apply_image hη' hfE] at hab
    obtain ⟨_, _, _, p, q, hpq, hap, hbq⟩ := hab
    have hδf_verts : (δ f).verts = P'.G.ends f :=
      ((P'.Δ f).verts_eq (δ f) (hδ f hf_del)).trans (P'.Δ_verts f hfE)
    obtain ⟨hp_verts, _, _⟩ := sameComponent_iff.mp hpq
    have hpV : p ∈ P'.G.vertexSet := P'.G.vertex_mem_of_inc (hδf_verts ▸ hp_verts)
    have hp_eq : p = v' := by
      by_contra hne
      exact Set.disjoint_left.mp (hη'.vertex_disjoint p hpV v' hv'V hne) hap ha_v'
    subst hp_eq
    let H := realizationOf (P'.deleteEdges (ηe '' P.G.edgeSet)).G.toHypergraph δ
    have hδf_le_H : δ f ≤ H := by
      refine ⟨fun x hx ↦ ?_, fun x y hxy ↦ realizationOf_adj.mpr ⟨f, hf_del, hxy⟩⟩
      rw [hH_real.1.verts_eq]
      exact P'.G.vertex_mem_of_inc (hδf_verts ▸ hx)
    have hpq_H : sameComponent H p q := hpq.mono hδf_le_H
    obtain ⟨D, hD, hD_verts⟩ := hH_real.2 v hv
    obtain ⟨D', hD', hpD', hqD'⟩ := hpq_H
    have hD_eq : D' = D := hD'.eq_of_mem hD hpD' (hD_verts ▸ hv')
    have hq_mem : q ∈ ηv v := hD_verts ▸ hD_eq ▸ hqD'
    exact mem_compVertex_iff.mpr ⟨q, hq_mem, hbq⟩
  · rw [compRealizationChoice_of_notMem he_im] at hab
    let H' := realizationOf (P''.deleteEdges (η'e '' P'.G.edgeSet)).G.toHypergraph δ'
    have hab_H' : H'.Adj a b := realizationOf_adj.mpr ⟨e, ⟨heE, he_im⟩, hab⟩
    obtain ⟨D', hD', hD'_verts⟩ := hH'_real.2 v' hv'V
    have hclosed := ((exists_isComponent_verts_eq_iff (hη'.vertex_nonempty v' hv'V)
      (hH'_real.1.verts_eq.symm ▸ hη'.vertex_subset v' hv'V)).mp ⟨D', hD', hD'_verts⟩).1
    exact mem_compVertex_iff.mpr ⟨v', hv', hclosed a ha_v' b hab_H'⟩

/-- Graph Minors IV, (7.1), claim (8) (page 246):
"If $p, q \in V(H)$ are adjacent in $H$ then there exist $a \in \eta'(p)$ and $b \in
\eta'(q)$ adjacent in $H''$." -/
theorem lemma_7_1_claim_8 {P : Patchwork Ω α β} {P' : Patchwork Ω α' β'}
    {P'' : Patchwork Ω α'' β''} {ηv : α → Set α'} {ηe : β → β'}
    {η'v : α' → Set α''} {η'e : β' → β''}
    (hη : IsExpansion P P' ηv ηe) (hη' : IsExpansion P' P'' η'v η'e)
    {δ : β' → (⊤ : SimpleGraph α').Subgraph}
    (hδ : ∀ f ∈ (P'.deleteEdges (ηe '' P.G.edgeSet)).G.edgeSet, δ f ∈ P'.Δ f)
    {δ' : β'' → (⊤ : SimpleGraph α'').Subgraph}
    {p q : α'}
    (hpq : (realizationOf (P'.deleteEdges (ηe '' P.G.edgeSet)).G.toHypergraph δ).Adj p q) :
    ∃ a ∈ η'v p, ∃ b ∈ η'v q,
      (realizationOf
        (P''.deleteEdges (compEdge ηe η'e '' P.G.edgeSet)).G.toHypergraph
        (compRealizationChoice P' P'' η'v η'e δ δ')).Adj a b := by
  rw [realizationOf_adj] at hpq
  obtain ⟨f, hf_del, hpq_adj⟩ := hpq
  have hfE : f ∈ P'.G.edgeSet := hf_del.1
  have hδf_verts : (δ f).verts = P'.G.ends f :=
    ((P'.Δ f).verts_eq (δ f) (hδ f hf_del)).trans (P'.Δ_verts f hfE)
  have hp_end : p ∈ P'.G.ends f := hδf_verts ▸ (δ f).edge_vert hpq_adj
  have hq_end : q ∈ P'.G.ends f := hδf_verts ▸ (δ f).edge_vert hpq_adj.symm
  obtain ⟨a, hap, ha_inc⟩ := hη'.exists_inc_of_inc hfE hp_end
  obtain ⟨b, hbq, hb_inc⟩ := hη'.exists_inc_of_inc hfE hq_end
  have hab_ne : a ≠ b := by
    intro hEq
    subst hEq
    exact Set.disjoint_left.mp
      (hη'.vertex_disjoint p (P'.G.vertex_mem_of_inc hp_end)
        q (P'.G.vertex_mem_of_inc hq_end) hpq_adj.ne)
      hap hbq
  refine ⟨a, hap, b, hbq, realizationOf_adj.mpr ⟨η'e f, ⟨hη'.edge_mem f hfE, ?_⟩, ?_⟩⟩
  · rintro ⟨g, hg, hEq⟩
    exact hf_del.2 ⟨g, hg, hη'.edge_injOn (hη.edge_mem g hg) hfE hEq⟩
  · rw [compRealizationChoice_apply_image hη' hfE]
    exact ⟨ha_inc, hb_inc, hab_ne, p, q, sameComponent_of_adj hpq_adj, hap, hbq⟩

/-- Graph Minors IV, (7.1), claim (9) (pages 246–247):
"If $a, b \in \eta''(v)$ then $a, b$ belong to the same component of $H''$." -/
theorem lemma_7_1_claim_9 {P : Patchwork Ω α β} {P' : Patchwork Ω α' β'}
    {P'' : Patchwork Ω α'' β''} {ηv : α → Set α'} {ηe : β → β'}
    {η'v : α' → Set α''} {η'e : β' → β''}
    (hη : IsExpansion P P' ηv ηe) (hη' : IsExpansion P' P'' η'v η'e)
    {δ : β' → (⊤ : SimpleGraph α').Subgraph}
    (hδ : ∀ f ∈ (P'.deleteEdges (ηe '' P.G.edgeSet)).G.edgeSet, δ f ∈ P'.Δ f)
    (hH_real : Realizes P P' ηv ηe
      (realizationOf (P'.deleteEdges (ηe '' P.G.edgeSet)).G.toHypergraph δ))
    {δ' : β'' → (⊤ : SimpleGraph α'').Subgraph}
    (hδ' : ∀ e ∈ (P''.deleteEdges (η'e '' P'.G.edgeSet)).G.edgeSet, δ' e ∈ P''.Δ e)
    (hH'_real : Realizes P' P'' η'v η'e
      (realizationOf (P''.deleteEdges (η'e '' P'.G.edgeSet)).G.toHypergraph δ'))
    {v : α} (hv : v ∈ P.G.vertexSet)
    {a b : α''} (ha : a ∈ compVertex ηv η'v v) (hb : b ∈ compVertex ηv η'v v) :
    sameComponent
      (realizationOf
        (P''.deleteEdges (compEdge ηe η'e '' P.G.edgeSet)).G.toHypergraph
        (compRealizationChoice P' P'' η'v η'e δ δ'))
      a b := by
  let H := realizationOf (P'.deleteEdges (ηe '' P.G.edgeSet)).G.toHypergraph δ
  let H' := realizationOf (P''.deleteEdges (η'e '' P'.G.edgeSet)).G.toHypergraph δ'
  let δ'' := compRealizationChoice P' P'' η'v η'e δ δ'
  let H'' := realizationOf (P''.deleteEdges (compEdge ηe η'e '' P.G.edgeSet)).G.toHypergraph δ''
  have hδ''_mem : ∀ e ∈ (P''.deleteEdges (compEdge ηe η'e '' P.G.edgeSet)).G.edgeSet,
      δ'' e ∈ P''.Δ e := by
    rintro e ⟨heE, he_not_comp⟩
    dsimp only [δ'']
    by_cases he_im : e ∈ η'e '' P'.G.edgeSet
    · obtain ⟨f, hfE, rfl⟩ := he_im
      have hf_not_im : f ∉ ηe '' P.G.edgeSet := by
        rintro ⟨g, hg, rfl⟩
        exact he_not_comp ⟨g, hg, rfl⟩
      rw [compRealizationChoice_apply_image hη' hfE]
      exact lemma_7_1_claim_6 hη' hfE (hδ f ⟨hfE, hf_not_im⟩)
    · rw [compRealizationChoice_of_notMem he_im]
      exact hδ' e ⟨heE, he_im⟩
  have hH''_real : (P''.deleteEdges (compEdge ηe η'e '' P.G.edgeSet)).IsRealization H'' :=
    ⟨δ'', hδ''_mem, rfl⟩
  have hH'_le_H'' : H' ≤ H'' := by
    refine ⟨?_, fun x y hxy ↦ ?_⟩
    · rw [hH'_real.1.verts_eq, hH''_real.verts_eq]
      exact subset_rfl
    · rw [realizationOf_adj] at hxy ⊢
      obtain ⟨e, ⟨heE, he_not⟩, hxy⟩ := hxy
      have he_not_comp : e ∉ compEdge ηe η'e '' P.G.edgeSet := by
        rintro ⟨g, hg, rfl⟩
        exact he_not ⟨ηe g, hη.edge_mem g hg, rfl⟩
      refine ⟨e, ⟨heE, he_not_comp⟩, ?_⟩
      dsimp only [δ'']
      rwa [compRealizationChoice_of_notMem he_not]
  have hsame_v' : ∀ r ∈ P'.G.vertexSet, ∀ x ∈ η'v r, ∀ y ∈ η'v r, sameComponent H'' x y := by
    intro r hr x hx y hy
    obtain ⟨D', hD', hD'_verts⟩ := hH'_real.2 r hr
    have hconn := ((exists_isComponent_verts_eq_iff (hη'.vertex_nonempty r hr)
      (hH'_real.1.verts_eq.symm ▸ hη'.vertex_subset r hr)).mp ⟨D', hD', hD'_verts⟩).2
    exact (hconn x hx y hy).mono hH'_le_H''
  obtain ⟨p, hp, hap⟩ := mem_compVertex_iff.mp ha
  obtain ⟨q, hq, hbq⟩ := mem_compVertex_iff.mp hb
  obtain ⟨D, hD, hD_verts⟩ := hH_real.2 v hv
  have hconn_H := ((exists_isComponent_verts_eq_iff (hη.vertex_nonempty v hv)
    (hH_real.1.verts_eq.symm ▸ hη.vertex_subset v hv)).mp ⟨D, hD, hD_verts⟩).2
  obtain ⟨hpH, hqH, hreach⟩ := sameComponent_iff.mp (hconn_H p hp q hq)
  suffices ∀ x y : H.verts, H.coe.Reachable x y →
      ∀ x'' ∈ η'v x.1, ∀ y'' ∈ η'v y.1, sameComponent H'' x'' y'' from
    this ⟨p, hpH⟩ ⟨q, hqH⟩ hreach a hap b hbq
  intro x y hxy
  rw [reachable_iff_reflTransGen] at hxy
  induction hxy with
  | refl =>
    intro x'' hx'' y'' hy''
    have hxV : x.1 ∈ P'.G.vertexSet := hH_real.1.verts_eq ▸ x.2
    exact hsame_v' x.1 hxV x'' hx'' y'' hy''
  | @tail w z _ hwz ih =>
    intro x'' hx'' z'' hz''
    obtain ⟨c, hc, d, hd, hcd⟩ := lemma_7_1_claim_8 hη hη' hδ hwz
    have hzV : z.1 ∈ P'.G.vertexSet := hH_real.1.verts_eq ▸ z.2
    exact ((ih x'' hx'' c hc).trans (sameComponent_of_adj hcd)).trans
      (hsame_v' z.1 hzV d hd z'' hz'')

/-- Second statement of Graph Minors IV, (7.1) (pages 245–247): if `η` is a realizable expansion
of `P` in `P'` and `η'` is a realizable expansion of `P'` in `P''`, then the composed expansion
`η'' = (compVertex ηv η'v, compEdge ηe η'e)` is realizable. -/
theorem IsRealizableExpansion.comp {P : Patchwork Ω α β} {P' : Patchwork Ω α' β'}
    {P'' : Patchwork Ω α'' β''} {ηv : α → Set α'} {ηe : β → β'}
    {η'v : α' → Set α''} {η'e : β' → β''}
    (hη : IsRealizableExpansion P P' ηv ηe) (hη' : IsRealizableExpansion P' P'' η'v η'e) :
    IsRealizableExpansion P P'' (compVertex ηv η'v) (compEdge ηe η'e) := by
  have hcomp_exp := hη.1.comp hη'.1
  obtain ⟨H, ⟨δ, hδ, rfl⟩, hH_comp⟩ := hη.2
  obtain ⟨H', ⟨δ', hδ', rfl⟩, hH'_comp⟩ := hη'.2
  have hH_real : Realizes P P' ηv ηe
      (realizationOf (P'.deleteEdges (ηe '' P.G.edgeSet)).G.toHypergraph δ) :=
    ⟨⟨δ, hδ, rfl⟩, hH_comp⟩
  have hH'_real : Realizes P' P'' η'v η'e
      (realizationOf (P''.deleteEdges (η'e '' P'.G.edgeSet)).G.toHypergraph δ') :=
    ⟨⟨δ', hδ', rfl⟩, hH'_comp⟩
  let δ'' := compRealizationChoice P' P'' η'v η'e δ δ'
  let H'' := realizationOf (P''.deleteEdges (compEdge ηe η'e '' P.G.edgeSet)).G.toHypergraph δ''
  have hδ''_mem : ∀ e ∈ (P''.deleteEdges (compEdge ηe η'e '' P.G.edgeSet)).G.edgeSet,
      δ'' e ∈ P''.Δ e := by
    rintro e ⟨heE, he_not_comp⟩
    dsimp only [δ'']
    by_cases he_im : e ∈ η'e '' P'.G.edgeSet
    · obtain ⟨f, hfE, rfl⟩ := he_im
      have hf_not_im : f ∉ ηe '' P.G.edgeSet := by
        rintro ⟨g, hg, rfl⟩
        exact he_not_comp ⟨g, hg, rfl⟩
      rw [compRealizationChoice_apply_image hη'.1 hfE]
      exact lemma_7_1_claim_6 hη'.1 hfE (hδ f ⟨hfE, hf_not_im⟩)
    · rw [compRealizationChoice_of_notMem he_im]
      exact hδ' e ⟨heE, he_im⟩
  have hH''_isReal : (P''.deleteEdges (compEdge ηe η'e '' P.G.edgeSet)).IsRealization H'' :=
    ⟨δ'', hδ''_mem, rfl⟩
  refine ⟨hcomp_exp, H'', hH''_isReal, fun v hv ↦ ?_⟩
  rw [exists_isComponent_verts_eq_iff (hcomp_exp.vertex_nonempty v hv)
    (hH''_isReal.verts_eq.symm ▸ hcomp_exp.vertex_subset v hv)]
  exact ⟨fun a ha b hab ↦ lemma_7_1_claim_7 hη.1 hη'.1 hδ hH_real hH'_real hv ha hab,
    fun a ha b hb ↦ lemma_7_1_claim_9 hη.1 hη'.1 hδ hH_real hδ' hH'_real hv ha hb⟩

/-! ### Reflexivity and transitivity of simulation -/

/-- The identity expansion `(v ↦ {v}, e ↦ e)` of an `Ω`-patchwork `P` in itself
(Graph Minors IV, Section 7, page 247). -/
theorem IsExpansion.id (P : Patchwork Ω α β) :
    IsExpansion P P (fun v ↦ {v}) _root_.id where
  vertex_nonempty v _ := Set.singleton_nonempty v
  vertex_subset _ hv _ h := h.symm ▸ hv
  edge_mem _ he := he
  vertex_disjoint _ _ _ _ hne := Set.disjoint_singleton.mpr hne
  edge_injOn _ _ _ _ h := h
  mem_dom_iff _ _ := Iff.rfl
  ends_nonempty _ _ _ v hv := ⟨v, rfl, hv⟩
  μ_length _ _ := rfl
  μ_mem _ _ _ _ _ := rfl
  roots_length := rfl
  roots_mem _ _ _ := rfl
  maps_Δ e he δ hδ := by
    have heE : e ∈ P.G.edgeSet := P.dom_subset he
    have hverts : δ.verts ⊆ {x | x ∈ P.μ e} := by
      rw [((P.Δ e).verts_eq δ hδ).trans (P.Δ_verts e heE), P.μ_set e he]
    dsimp only [_root_.id]
    rwa [marchMapSubgraph_id hverts]
  φ_le _ _ := le_rfl

/-- The identity expansion of `P` in itself is realizable, realized by `N_{V(G)}`
(Graph Minors IV, Section 7, page 247). -/
theorem IsRealizableExpansion.id (P : Patchwork Ω α β) :
    IsRealizableExpansion P P (fun v ↦ {v}) _root_.id := by
  refine ⟨IsExpansion.id P, emptySubgraph P.G.vertexSet, ?_, fun v hv ↦ ?_⟩
  · refine ⟨fun _ ↦ emptySubgraph ∅, fun e ⟨he, hnot⟩ ↦ ?_, ?_⟩
    · exact False.elim (hnot ⟨e, he, rfl⟩)
    · ext u w
      · simp [Patchwork.deleteEdges, RootedHypergraph.deleteEdges, Hypergraph.deleteEdges,
          realizationOf]
      · simp only [not_emptySubgraph_adj, realizationOf_adj, false_iff, not_exists]
        rintro e ⟨⟨he, hnot⟩, _⟩
        exact hnot ⟨e, he, rfl⟩
  · let x : (emptySubgraph P.G.vertexSet).verts := ⟨v, hv⟩
    refine ⟨component (emptySubgraph P.G.vertexSet) x, ⟨x, rfl⟩, ?_⟩
    ext w
    simp only [component_verts, mem_componentVerts_iff, emptySubgraph_verts,
      Set.mem_singleton_iff]
    refine ⟨?_, fun hEq ↦ hEq ▸ ⟨hv, Reachable.refl x⟩⟩
    rintro ⟨hw, hr⟩
    suffices ∀ y : (emptySubgraph P.G.vertexSet).verts,
        (emptySubgraph P.G.vertexSet).coe.Reachable x y → y.1 = x.1 from
      this ⟨w, hw⟩ hr
    intro y hy
    rw [reachable_iff_reflTransGen] at hy
    induction hy with
    | refl => rfl
    | @tail _ _ _ hab => exact False.elim hab

/-- Simulation of `Ω`-patchworks is reflexive (Graph Minors IV, (7.1), page 247). -/
theorem Simulated.refl (P : Patchwork Ω α β) : Simulated P P :=
  ⟨fun v ↦ {v}, _root_.id, IsRealizableExpansion.id P⟩

/-- Simulation of `Ω`-patchworks is transitive (Graph Minors IV, (7.1), page 247). -/
theorem Simulated.trans {P : Patchwork Ω α β} {P' : Patchwork Ω α' β'}
    {P'' : Patchwork Ω α'' β''} (h₁ : Simulated P P') (h₂ : Simulated P' P'') :
    Simulated P P'' := by
  obtain ⟨ηv, ηe, hη⟩ := h₁
  obtain ⟨η'v, η'e, hη'⟩ := h₂
  exact ⟨compVertex ηv η'v, compEdge ηe η'e, hη.comp hη'⟩

/-- **Graph Minors IV, (7.1)** (pages 244–247): If `η = (ηv, ηe)` is an expansion of `P` in `P'`
and `η' = (η'v, η'e)` is an expansion of `P'` in `P''`, then `η'' = (compVertex ηv η'v, compEdge ηe
η'e)`
is an expansion of `P` in `P''`; and if `η` and `η'` are realizable then so is `η''`. -/
theorem theorem_7_1_proof {P : Patchwork Ω α β} {P' : Patchwork Ω α' β'}
    {P'' : Patchwork Ω α'' β''} {ηv : α → Set α'} {ηe : β → β'}
    {η'v : α' → Set α''} {η'e : β' → β''}
    (hη : IsExpansion P P' ηv ηe) (hη' : IsExpansion P' P'' η'v η'e) :
    IsExpansion P P'' (compVertex ηv η'v) (compEdge ηe η'e) ∧
      ((∃ H, Realizes P P' ηv ηe H) → (∃ H', Realizes P' P'' η'v η'e H') →
        ∃ H'', Realizes P P'' (compVertex ηv η'v) (compEdge ηe η'e) H'') :=
  ⟨hη.comp hη', fun h₁ h₂ ↦ (IsRealizableExpansion.comp ⟨hη, h₁⟩ ⟨hη', h₂⟩).2⟩

end GraphMinor.GM04
