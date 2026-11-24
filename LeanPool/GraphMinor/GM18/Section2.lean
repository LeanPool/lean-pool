/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM10.Section11
public import LeanPool.GraphMinor.GM18.Proved
public import LeanPool.GraphMinor.GM18.Defs
import LeanPool.GraphMinor.GM10.TangleLemmas
import LeanPool.GraphMinor.Thomas.Basic

/-!
# Graph Minors XVIII, Section 2: Hypergraphs, Tangles and Tree-Decompositions

This file formalizes Section 2 (pages 78–82) of Robertson and Seymour,
*Graph Minors. XVIII. Tree-decompositions and well-quasi-ordering*, J. Combin. Theory Ser. B 89
(2003) 77–108:

* `theorem_2_1` (2.1, page 79): lifting a tangle from a subhypergraph `G' ≤ G` to `G`.
* `theorem_2_2` (2.2, page 79): a hypergraph with no tangle of order `≥ θ` (`θ ≥ 1`) has
  tree-width `≤ (3/2) θ`.
* `theorem_2_3` (2.3, page 80): basic properties of a location `ℒ` and `M(G, ℒ)`.
* `theorem_2_4` (2.4, page 80): the location of a vertex `t₀` in a tree-decomposition `(T, τ)` is a
  location in `G`.
* `theorem_2_5` (2.5, page 80): if `ℒ` is the location of `t` in `(T, τ)`, then
  `τ(t) = M(G, ℒ)`.
* `theorem_2_6` (2.6, page 81): existence of a standard decomposition relative to distinct tangles
  `𝒯₁, …, 𝒯ₙ` of order `θ`.
* `theorem_2_7` (2.7, page 81): every standard decomposition is proper and rotund, and every
  separation made by an edge is robust.
-/

public section

namespace GraphMinor.GM18

open Hypergraph SimpleGraph

universe u v w

variable {α : Type u} {β : Type v} {ι : Type*}

/-! ## Helper lemmas on subhypergraphs, intersections, and `biUnion` -/

theorem subhypergraphs_finite (G : Hypergraph α β) :
    {H : Hypergraph α β | H ≤ G}.Finite := by
  let f : Hypergraph α β → Set α × Set β := fun H ↦ (H.vertexSet, H.edgeSet)
  have hinj : Set.InjOn f {H : Hypergraph α β | H ≤ G} := by
    rintro H₁ h₁ H₂ h₂ hfeq
    exact GM10.eq_of_le_of_vertexSet_eq_of_edgeSet_eq h₁ h₂
      (congrArg Prod.fst hfeq) (congrArg Prod.snd hfeq)
  have hprod_fin : (G.vertexSet.powerset ×ˢ G.edgeSet.powerset).Finite :=
    G.vertexSet_finite.powerset.prod G.edgeSet_finite.powerset
  have himg_sub : f '' {H : Hypergraph α β | H ≤ G} ⊆
      G.vertexSet.powerset ×ˢ G.edgeSet.powerset := by
    rintro _ ⟨H, hH, rfl⟩
    exact ⟨hH.vertexSet_subset, hH.edgeSet_subset⟩
  exact Set.Finite.of_finite_image (hprod_fin.subset himg_sub) hinj

theorem separations_finite (G : Hypergraph α β) :
    {p : Hypergraph α β × Hypergraph α β | G.IsSeparation p.1 p.2}.Finite := by
  refine ((subhypergraphs_finite G).prod (subhypergraphs_finite G)).subset ?_
  rintro ⟨A, B⟩ hsep
  exact ⟨hsep.left_le, hsep.right_le⟩

theorem inter_self_of_le {G' G : Hypergraph α β} (h : G' ≤ G) : G ∩ G' = G' :=
  GM10.eq_of_le_of_vertexSet_eq_of_edgeSet_eq (GM10.inter_le_right le_rfl h) le_rfl
    (Set.inter_eq_right.2 h.vertexSet_subset) (Set.inter_eq_right.2 h.edgeSet_subset)

theorem isSeparation_inter_of_le {G G' A B : Hypergraph α β}
    (hG' : G' ≤ G) (hsep : G.IsSeparation A B) :
    G'.IsSeparation (A ∩ G') (B ∩ G') := by
  have hAG' : A ∩ G' ≤ G' := GM10.inter_le_right hsep.left_le hG'
  have hBG' : B ∩ G' ≤ G' := GM10.inter_le_right hsep.right_le hG'
  rw [GM10.isSeparation_iff_of_le hAG' hBG']
  refine ⟨?_, ?_, ?_⟩
  · ext v
    simp only [GM10.inter_vertexSet, Set.mem_union, Set.mem_inter_iff]
    rw [← or_and_right, ← Set.mem_union, hsep.vertexSet_union]
    exact ⟨fun h ↦ h.2, fun hv ↦ ⟨hG'.vertexSet_subset hv, hv⟩⟩
  · ext e
    simp only [GM10.inter_edgeSet, Set.mem_union, Set.mem_inter_iff]
    rw [← or_and_right, ← Set.mem_union, hsep.edgeSet_union]
    exact ⟨fun h ↦ h.2, fun he ↦ ⟨hG'.edgeSet_subset he, he⟩⟩
  · ext e
    simp only [GM10.inter_edgeSet, Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
    rintro ⟨⟨heA, _⟩, ⟨heB, _⟩⟩
    exact hsep.notMem_edgeSet_right heA heB

theorem separationOrder_inter_le {G' A B : Hypergraph α β} :
    separationOrder (A ∩ G') (B ∩ G') ≤ separationOrder A B := by
  refine Set.ncard_le_ncard ?_ (A ∩ B).vertexSet_finite
  intro v hv
  exact ⟨hv.1.1, hv.2.1⟩

theorem biUnion_le {s : Finset ι} {τ : ι → Hypergraph α β} {G : Hypergraph α β}
    (hτ : ∀ t ∈ s, τ t ≤ G) :
    Hypergraph.biUnion s τ ≤ G where
  vertexSet_subset := by
    intro v hv
    simp only [biUnion, Set.mem_iUnion] at hv
    rcases hv with ⟨t, ht, hvt⟩
    exact (hτ t ht).vertexSet_subset hvt
  edgeSet_subset := by
    intro e he
    simp only [biUnion, Set.mem_iUnion] at he
    rcases he with ⟨t, ht, het⟩
    exact (hτ t ht).edgeSet_subset het
  ends_eq e he := by
    simp only [biUnion, Set.mem_iUnion] at he
    rcases he with ⟨t₀, ht₀, het₀⟩
    ext v
    simp only [ends, biUnion, Set.mem_ofPred_eq]
    constructor
    · intro hv
      exact ⟨t₀, ht₀, (GM10.inc_iff_of_le (hτ t₀ ht₀) het₀).2 hv⟩
    · rintro ⟨t, ht, hinc⟩
      exact GM10.inc_of_le (hτ t ht) hinc

theorem le_biUnion_of_mem {s : Finset ι} {τ : ι → Hypergraph α β} {G : Hypergraph α β}
    (hτ : ∀ t ∈ s, τ t ≤ G) {t₀ : ι} (ht₀ : t₀ ∈ s) :
    τ t₀ ≤ Hypergraph.biUnion s τ := by
  rw [GM10.le_iff_of_le (hτ t₀ ht₀) (biUnion_le hτ)]
  refine ⟨fun v hv ↦ ?_, fun e he ↦ ?_⟩
  · exact Set.mem_iUnion₂.2 ⟨t₀, ht₀, hv⟩
  · exact Set.mem_iUnion₂.2 ⟨t₀, ht₀, he⟩

theorem biUnion_mono {s₁ s₂ : Finset ι} {τ : ι → Hypergraph α β} {G : Hypergraph α β}
    (hτ : ∀ t ∈ s₂, τ t ≤ G) (hsub : s₁ ⊆ s₂) :
    Hypergraph.biUnion s₁ τ ≤ Hypergraph.biUnion s₂ τ := by
  rw [GM10.le_iff_of_le (biUnion_le fun t ht ↦ hτ t (hsub ht)) (biUnion_le hτ)]
  refine ⟨?_, ?_⟩
  · intro v hv
    simp only [biUnion, Set.mem_iUnion] at hv ⊢
    rcases hv with ⟨t, ht, hvt⟩
    exact ⟨t, hsub ht, hvt⟩
  · intro e he
    simp only [biUnion, Set.mem_iUnion] at he ⊢
    rcases he with ⟨t, ht, het⟩
    exact ⟨t, hsub ht, het⟩

/-! ## (2.1) and (2.2) -/

/-- **Graph Minors XVIII, (2.1)** (page 79):
"Let $G$ be a hypergraph, let $G' \subseteq G$, and let $\mathcal{T}'$ be a tangle in $G'$ of
order $\theta$. Let $\mathcal{T}$ be the set of all separations $(A, B)$ of $G$ of order
$<\theta$ such that $(A \cap G', B \cap G') \in \mathcal{T}'$. Then $\mathcal{T}$ is a
tangle in $G$ of order $\theta$." -/
theorem theorem_2_1_proof {G G' : Hypergraph α β} (hG' : G' ≤ G) {θ : ℕ}
    {𝒯' : Set (Hypergraph α β × Hypergraph α β)} (h𝒯' : GM10.IsTangle G' θ 𝒯') :
    GM10.IsTangle G θ
      {p | G.IsSeparation p.1 p.2 ∧ separationOrder p.1 p.2 < θ ∧
        (p.1 ∩ G', p.2 ∩ G') ∈ 𝒯'} where
  one_le := h𝒯'.one_le
  isSeparation _ _ h := h.1
  order_lt _ _ h := h.2.1
  axiom1 A B hsep hord := by
    have hsep' : G'.IsSeparation (A ∩ G') (B ∩ G') := isSeparation_inter_of_le hG' hsep
    have hord' : separationOrder (A ∩ G') (B ∩ G') < θ :=
      separationOrder_inter_le.trans_lt hord
    rcases h𝒯'.axiom1 hsep' hord' with h1 | h2
    · exact Or.inl ⟨hsep, hord, h1⟩
    · exact Or.inr ⟨hsep.symm, by rwa [GM10.separationOrder_comm], h2⟩
  axiom2 A₁ B₁ A₂ B₂ A₃ B₃ h₁ h₂ h₃ hU := by
    apply h𝒯'.axiom2 h₁.2.2 h₂.2.2 h₃.2.2
    have hle1 : (A₁ ∩ G') ∪ (A₂ ∩ G') ∪ (A₃ ∩ G') ≤ G' :=
      GM10.union_le (GM10.union_le (GM10.inter_le_right h₁.1.left_le hG')
        (GM10.inter_le_right h₂.1.left_le hG'))
        (GM10.inter_le_right h₃.1.left_le hG')
    refine GM10.eq_of_le_of_vertexSet_eq_of_edgeSet_eq hle1 le_rfl ?_ ?_
    · have hVG : (A₁ ∪ A₂ ∪ A₃).vertexSet = G.vertexSet := congrArg Hypergraph.vertexSet hU
      ext v
      simp only [GM10.union_vertexSet, GM10.inter_vertexSet, Set.mem_union, Set.mem_inter_iff]
      constructor
      · rintro ((⟨_, hv⟩ | ⟨_, hv⟩) | ⟨_, hv⟩) <;> exact hv
      · intro hvG'
        have hvG : v ∈ (A₁ ∪ A₂ ∪ A₃).vertexSet := hVG.symm ▸ hG'.vertexSet_subset hvG'
        rcases hvG with (hv₁ | hv₂) | hv₃
        · exact Or.inl (Or.inl ⟨hv₁, hvG'⟩)
        · exact Or.inl (Or.inr ⟨hv₂, hvG'⟩)
        · exact Or.inr ⟨hv₃, hvG'⟩
    · have hEG : (A₁ ∪ A₂ ∪ A₃).edgeSet = G.edgeSet := congrArg Hypergraph.edgeSet hU
      ext e
      simp only [GM10.union_edgeSet, GM10.inter_edgeSet, Set.mem_union, Set.mem_inter_iff]
      constructor
      · rintro ((⟨_, he⟩ | ⟨_, he⟩) | ⟨_, he⟩) <;> exact he
      · intro heG'
        have heG : e ∈ (A₁ ∪ A₂ ∪ A₃).edgeSet := hEG.symm ▸ hG'.edgeSet_subset heG'
        rcases heG with (he₁ | he₂) | he₃
        · exact Or.inl (Or.inl ⟨he₁, heG'⟩)
        · exact Or.inl (Or.inr ⟨he₂, heG'⟩)
        · exact Or.inr ⟨he₃, heG'⟩
  axiom3 A B h hVA := by
    apply h𝒯'.axiom3 h.2.2
    change A.vertexSet ∩ G'.vertexSet = G'.vertexSet
    rw [hVA, Set.inter_eq_right.2 hG'.vertexSet_subset]

/-- **Graph Minors XVIII, (2.2)** (page 79):
"**2.2.** *Let $G$ be a hypergraph with no tangle of order $\ge \theta$, where $\theta \ge 1$.
Then $G$ has tree-width $\le \frac{3}{2}\theta$.*" -/
theorem theorem_2_2_proof
    (G : Hypergraph α β) {θ : ℕ} (hθ : 1 ≤ θ)
    (hno : ∀ ⦃θ' : ℕ⦄ ⦃𝒯 : Set (Hypergraph α β × Hypergraph α β)⦄,
      GM10.IsTangle G θ' 𝒯 → θ' < θ) :
    2 * GM10.treeWidth G ≤ 3 * (θ : ℤ) := by
  have htn_lt : GM10.tangleNumber G < θ := by
    unfold GM10.tangleNumber
    rcases Set.eq_empty_or_nonempty {θ' : ℕ | ∃ 𝒯, GM10.IsTangle G θ' 𝒯} with hemp | hne
    · simp [hemp]
      omega
    · obtain ⟨𝒯, h𝒯⟩ := Nat.sSup_mem hne (GM10.bddAbove_tangle_orders G)
      exact hno h𝒯
  have h52_right : 2 * GM10.treeWidthPlusOne G ≤ 3 * GM10.tangleNumber G := (gm10Theorem52 G).2
  unfold GM10.treeWidth
  omega

/-! ## (2.3): Properties of Locations -/

theorem locationCore_le {G : Hypergraph α β} {ℒ : Set (Hypergraph α β × Hypergraph α β)}
    (hℒ : GM10.IsLocation G ℒ) :
    GM10.locationCore G ℒ ≤ G where
  vertexSet_subset _ h := h.1
  edgeSet_subset _ h := h.1
  ends_eq e he := by
    ext v
    change G.Inc e v ↔
      G.Inc e v ∧ (∀ p ∈ ℒ, v ∈ p.2.vertexSet) ∧ (∀ p ∈ ℒ, e ∈ p.2.edgeSet)
    refine ⟨fun h ↦ ⟨h, fun p hp ↦ ?_, he.2⟩, fun h ↦ h.1⟩
    exact p.2.vertex_mem_of_inc
      ((GM10.inc_iff_of_le (hℒ.isSeparation hp).right_le (he.2 p hp)).2 h)

theorem locationCore_le_right {G : Hypergraph α β} {ℒ : Set (Hypergraph α β × Hypergraph α β)}
    (hℒ : GM10.IsLocation G ℒ) {p : Hypergraph α β × Hypergraph α β} (hp : p ∈ ℒ) :
    GM10.locationCore G ℒ ≤ p.2 :=
  (GM10.le_iff_of_le (locationCore_le hℒ) (hℒ.isSeparation hp).right_le).2
    ⟨fun _ hv ↦ hv.2 p hp, fun _ he ↦ he.2 p hp⟩

/-- **Graph Minors XVIII, (2.3.1)** (page 80):
"**2.3.** *Let $\mathcal{L} = \{(A_1, B_1), \dots, (A_n, B_n)\}$ be a location in a hypergraph $G$.
Then*
1. *$A_1, \dots, A_n, M(G, \mathcal{L})$ are mutually edge-disjoint, and have union $G$,*" -/
theorem theorem_2_3_1 {G : Hypergraph α β} {ℒ : Set (Hypergraph α β × Hypergraph α β)}
    (hℒ : GM10.IsLocation G ℒ) :
    (∀ ⦃p₁⦄, p₁ ∈ ℒ → ∀ ⦃p₂⦄, p₂ ∈ ℒ → p₁ ≠ p₂ → Disjoint p₁.1.edgeSet p₂.1.edgeSet) ∧
    (∀ ⦃p⦄, p ∈ ℒ → Disjoint p.1.edgeSet (GM10.locationCore G ℒ).edgeSet) ∧
    GM10.locationCore G ℒ ∪ Hypergraph.biUnion hℒ.finite.toFinset Prod.fst = G := by
  refine ⟨?_, ?_, ?_⟩
  · intro p₁ hp₁ p₂ hp₂ hne
    have hle : p₁.1.edgeSet ⊆ p₂.2.edgeSet := (hℒ.left_le_right hp₁ hp₂ hne).edgeSet_subset
    exact Disjoint.mono_left hle (hℒ.isSeparation hp₂).disjoint_edgeSet.symm
  · intro p hp
    have hle : (GM10.locationCore G ℒ).edgeSet ⊆ p.2.edgeSet := fun _ he ↦ he.2 p hp
    exact Disjoint.mono_right hle (hℒ.isSeparation hp).disjoint_edgeSet
  · have hle_union : GM10.locationCore G ℒ ∪ Hypergraph.biUnion hℒ.finite.toFinset Prod.fst ≤ G :=
      GM10.union_le (locationCore_le hℒ)
        (biUnion_le fun p hp ↦ (hℒ.isSeparation (hℒ.finite.mem_toFinset.1 hp)).left_le)
    refine GM10.eq_of_le_of_vertexSet_eq_of_edgeSet_eq hle_union le_rfl ?_ ?_
    · ext v
      constructor
      · exact fun hv ↦ hle_union.vertexSet_subset hv
      · intro hvG
        simp only [GM10.union_vertexSet, GM10.locationCore, biUnion, Set.mem_union,
          Set.mem_sep_iff, Set.mem_iUnion, Set.Finite.mem_toFinset]
        by_cases hall : ∀ p ∈ ℒ, v ∈ p.2.vertexSet
        · exact Or.inl ⟨hvG, hall⟩
        · push Not at hall
          rcases hall with ⟨p, hp, hnot⟩
          have hvAB : v ∈ p.1.vertexSet ∪ p.2.vertexSet := by
            rwa [(hℒ.isSeparation hp).vertexSet_union]
          exact Or.inr ⟨p, hp, hvAB.resolve_right hnot⟩
    · ext e
      constructor
      · exact fun he ↦ hle_union.edgeSet_subset he
      · intro heG
        simp only [GM10.union_edgeSet, GM10.locationCore, biUnion, Set.mem_union,
          Set.mem_sep_iff, Set.mem_iUnion, Set.Finite.mem_toFinset]
        by_cases hall : ∀ p ∈ ℒ, e ∈ p.2.edgeSet
        · exact Or.inl ⟨heG, hall⟩
        · push Not at hall
          rcases hall with ⟨p, hp, hnot⟩
          have heAB : e ∈ p.1.edgeSet ∪ p.2.edgeSet := by
            rwa [(hℒ.isSeparation hp).edgeSet_union]
          exact Or.inr ⟨p, hp, heAB.resolve_right hnot⟩

/-- **Graph Minors XVIII, (2.3.3)** (page 80):
"for $1 \le i < j \le n$, $A_i \cap A_j \subseteq M(G, \mathcal{L})$, and* $$V(A_i \cap A_j)
= V(A_i \cap B_i) \cap V(A_j \cap B_j) \cap V(M(G, \mathcal{L})).$$" -/
theorem theorem_2_3_3 {G : Hypergraph α β} {ℒ : Set (Hypergraph α β × Hypergraph α β)}
    (hℒ : GM10.IsLocation G ℒ) {p₁ p₂ : Hypergraph α β × Hypergraph α β}
    (hp₁ : p₁ ∈ ℒ) (hp₂ : p₂ ∈ ℒ) (hne : p₁ ≠ p₂) :
    p₁.1 ∩ p₂.1 ≤ GM10.locationCore G ℒ ∧
    (p₁.1 ∩ p₂.1).vertexSet =
      (p₁.1 ∩ p₁.2).vertexSet ∩ (p₂.1 ∩ p₂.2).vertexSet ∩
        (GM10.locationCore G ℒ).vertexSet := by
  have hsep₁ := hℒ.isSeparation hp₁
  have hsep₂ := hℒ.isSeparation hp₂
  have hdisjE := (theorem_2_3_1 hℒ).1 hp₁ hp₂ hne
  have hE_empty : (p₁.1 ∩ p₂.1).edgeSet = ∅ := Set.disjoint_iff_inter_eq_empty.1 hdisjE
  have hle_core : p₁.1 ∩ p₂.1 ≤ GM10.locationCore G ℒ := by
    rw [GM10.le_iff_of_le (GM10.inter_le hsep₁.left_le hsep₂.left_le) (locationCore_le hℒ)]
    refine ⟨?_, ?_⟩
    · intro v ⟨hv₁, hv₂⟩
      refine ⟨hsep₁.left_le.vertexSet_subset hv₁, fun q hq ↦ ?_⟩
      by_cases hqp₁ : q = p₁
      · subst hqp₁
        exact (hℒ.left_le_right hp₂ hp₁ hne.symm).vertexSet_subset hv₂
      · exact (hℒ.left_le_right hp₁ hq (Ne.symm hqp₁)).vertexSet_subset hv₁
    · rw [hE_empty]
      exact Set.empty_subset _
  refine ⟨hle_core, ?_⟩
  ext v
  simp only [GM10.inter_vertexSet, Set.mem_inter_iff]
  constructor
  · rintro ⟨hv₁, hv₂⟩
    have hv_core : v ∈ (GM10.locationCore G ℒ).vertexSet := hle_core.vertexSet_subset ⟨hv₁, hv₂⟩
    exact ⟨⟨⟨hv₁, hv_core.2 p₁ hp₁⟩, ⟨hv₂, hv_core.2 p₂ hp₂⟩⟩, hv_core⟩
  · rintro ⟨⟨⟨hv₁, _⟩, ⟨hv₂, _⟩⟩, _⟩
    exact ⟨hv₁, hv₂⟩

open Classical in
/-- **Graph Minors XVIII, (2.3.2)** (page 80):
"for $1 \le i \le n$, $B_i = M(G, \mathcal{L}) \cup \bigcup(A_j: 1 \le j \le n, j \ne i)$,
and $A_i \cap M(G, \mathcal{L}) = A_i \cap B_i$" -/
theorem theorem_2_3_2 {G : Hypergraph α β} {ℒ : Set (Hypergraph α β × Hypergraph α β)}
    (hℒ : GM10.IsLocation G ℒ) {p : Hypergraph α β × Hypergraph α β} (hp : p ∈ ℒ) :
    p.2 = GM10.locationCore G ℒ ∪
      Hypergraph.biUnion (hℒ.finite.toFinset.filter (· ≠ p)) Prod.fst ∧
    p.1 ∩ GM10.locationCore G ℒ = p.1 ∩ p.2 := by
  have hsep := hℒ.isSeparation hp
  have hle_rhs : GM10.locationCore G ℒ ∪
      Hypergraph.biUnion (hℒ.finite.toFinset.filter (· ≠ p)) Prod.fst ≤ p.2 := by
    have hbi_le : Hypergraph.biUnion (hℒ.finite.toFinset.filter (· ≠ p)) Prod.fst ≤ p.2 := by
      refine biUnion_le fun q hq ↦ ?_
      rw [Finset.mem_filter, Set.Finite.mem_toFinset] at hq
      exact hℒ.left_le_right hq.1 hp hq.2
    exact GM10.union_le (locationCore_le_right hℒ hp) hbi_le
  have hB_eq : p.2 = GM10.locationCore G ℒ ∪
      Hypergraph.biUnion (hℒ.finite.toFinset.filter (· ≠ p)) Prod.fst := by
    refine (GM10.eq_of_le_of_vertexSet_eq_of_edgeSet_eq
      (hle_rhs.trans hsep.right_le) hsep.right_le ?_ ?_).symm
    · ext v
      constructor
      · exact fun hv ↦ hle_rhs.vertexSet_subset hv
      · intro hvp
        have hvG : v ∈ G.vertexSet := hsep.right_le.vertexSet_subset hvp
        by_cases hall : ∀ q ∈ ℒ, v ∈ q.2.vertexSet
        · exact Or.inl ⟨hvG, hall⟩
        · push Not at hall
          rcases hall with ⟨q, hq, hnot⟩
          have hqp : q ≠ p := fun heq ↦ hnot (heq ▸ hvp)
          have hvAB : v ∈ q.1.vertexSet ∪ q.2.vertexSet := by
            rwa [(hℒ.isSeparation hq).vertexSet_union]
          refine Or.inr (Set.mem_iUnion₂.2 ⟨q, ?_, hvAB.resolve_right hnot⟩)
          exact Finset.mem_filter.2 ⟨hℒ.finite.mem_toFinset.2 hq, hqp⟩
    · ext e
      constructor
      · exact fun he ↦ hle_rhs.edgeSet_subset he
      · intro hep
        have heG : e ∈ G.edgeSet := hsep.right_le.edgeSet_subset hep
        by_cases hall : ∀ q ∈ ℒ, e ∈ q.2.edgeSet
        · exact Or.inl ⟨heG, hall⟩
        · push Not at hall
          rcases hall with ⟨q, hq, hnot⟩
          have hqp : q ≠ p := fun heq ↦ hnot (heq ▸ hep)
          have heAB : e ∈ q.1.edgeSet ∪ q.2.edgeSet := by
            rwa [(hℒ.isSeparation hq).edgeSet_union]
          refine Or.inr (Set.mem_iUnion₂.2 ⟨q, ?_, heAB.resolve_right hnot⟩)
          exact Finset.mem_filter.2 ⟨hℒ.finite.mem_toFinset.2 hq, hqp⟩
  refine ⟨hB_eq, ?_⟩
  refine GM10.eq_of_le_of_vertexSet_eq_of_edgeSet_eq
    (GM10.inter_le hsep.left_le (locationCore_le hℒ))
    (GM10.inter_le hsep.left_le hsep.right_le) ?_ ?_
  · ext v
    simp only [GM10.inter_vertexSet, GM10.locationCore, Set.mem_inter_iff, Set.mem_sep_iff]
    constructor
    · rintro ⟨hv₁, _, hall⟩
      exact ⟨hv₁, hall p hp⟩
    · rintro ⟨hv₁, hv₂⟩
      refine ⟨hv₁, hsep.left_le.vertexSet_subset hv₁, fun q hq ↦ ?_⟩
      by_cases hqp : q = p
      · exact hqp ▸ hv₂
      · exact (hℒ.left_le_right hp hq (Ne.symm hqp)).vertexSet_subset hv₁
  · have hdisj := (theorem_2_3_1 hℒ).2.1 hp
    rw [GM10.inter_edgeSet, Set.disjoint_iff_inter_eq_empty.1 hdisj, hsep.edgeSet_inter_eq]

open Classical in
/-- **Graph Minors XVIII, (2.3)** (page 80):
Combined statement of (2.3.1), (2.3.2), and (2.3.3). -/
theorem theorem_2_3_proof {G : Hypergraph α β} {ℒ : Set (Hypergraph α β × Hypergraph α β)}
    (hℒ : GM10.IsLocation G ℒ) :
    ((∀ ⦃p₁⦄, p₁ ∈ ℒ → ∀ ⦃p₂⦄, p₂ ∈ ℒ → p₁ ≠ p₂ → Disjoint p₁.1.edgeSet p₂.1.edgeSet) ∧
      (∀ ⦃p⦄, p ∈ ℒ → Disjoint p.1.edgeSet (GM10.locationCore G ℒ).edgeSet) ∧
      GM10.locationCore G ℒ ∪ Hypergraph.biUnion hℒ.finite.toFinset Prod.fst = G) ∧
    (∀ ⦃p⦄, p ∈ ℒ →
      p.2 = GM10.locationCore G ℒ ∪
        Hypergraph.biUnion (hℒ.finite.toFinset.filter (· ≠ p)) Prod.fst ∧
      p.1 ∩ GM10.locationCore G ℒ = p.1 ∩ p.2) ∧
    (∀ ⦃p₁⦄, p₁ ∈ ℒ → ∀ ⦃p₂⦄, p₂ ∈ ℒ → p₁ ≠ p₂ →
      p₁.1 ∩ p₂.1 ≤ GM10.locationCore G ℒ ∧
      (p₁.1 ∩ p₂.1).vertexSet =
        (p₁.1 ∩ p₁.2).vertexSet ∩ (p₂.1 ∩ p₂.2).vertexSet ∩
          (GM10.locationCore G ℒ).vertexSet) :=
  ⟨theorem_2_3_1 hℒ, fun _ hp ↦ theorem_2_3_2 hℒ hp,
    fun _ hp₁ _ hp₂ hne ↦ theorem_2_3_3 hℒ hp₁ hp₂ hne⟩

/-! ## Tree-Decomposition Separations and (2.4), (2.5) -/

/-- In a tree `T`, for an edge `s(t₁, t₂)` (`T.Adj t₁ t₂`), a vertex `s` is reachable from `t₁` in
`T \ s(t₁, t₂)` if and only if `t₁` lies on the path in `T` between `s` and `t₂`. -/
theorem reachable_deleteEdges_iff_onTreePath {T : SimpleGraph ι} (hT : T.IsTree)
    {t₁ t₂ : ι} (hadj : T.Adj t₁ t₂) (s : ι) :
    (T.deleteEdges {s(t₁, t₂)}).Reachable t₁ s ↔ GM10.OnTreePath T s t₂ t₁ := by
  classical
  have he_self : Thomas.OnTreePathEdge T t₁ t₂ t₁ t₂ := by
    rw [Thomas.onTreePathEdge_iff_mem_treePath hT]
    refine ⟨hadj, ?_⟩
    rw [← Thomas.eq_treePath hT hadj.toWalk hadj.isPath_toWalk]
    simp
  have hnot_t₁_t₂ : ¬ (T.deleteEdges {s(t₁, t₂)}).Reachable t₁ t₂ :=
    (Thomas.onTreePathEdge_iff_not_reachable_deleteEdges.1 he_self).2
  constructor
  · intro hreach
    rcases Thomas.onTreePathEdge_left_or_right s he_self with hleft | hright
    · exfalso
      have hnot_t₁_s : ¬ (T.deleteEdges {s(t₁, t₂)}).Reachable t₁ s :=
        (Thomas.onTreePathEdge_iff_not_reachable_deleteEdges.1 hleft).2
      exact hnot_t₁_s hreach
    · exact hright.onTreePath_left
  · intro hs
    change Thomas.OnTreePath T s t₂ t₁ at hs
    rw [Thomas.onTreePath_iff_exists_append hT] at hs
    obtain ⟨p, q, hp, hq, hpq⟩ := hs
    have hnot_edge : s(t₁, t₂) ∉ p.edges := by
      intro he_mem
      have ht₂_p : t₂ ∈ p.support := p.snd_mem_support_of_mem_edges he_mem
      have ht₂_q : t₂ ∈ q.support := q.end_mem_support
      exact hpq.ne_of_mem_support_of_append hadj.symm.ne ht₂_p ht₂_q rfl
    rw [reachable_comm, reachable_deleteEdges_iff_exists_walk]
    exact ⟨p, by simpa using hnot_edge⟩

theorem reachable_deleteEdges_dichotomy {T : SimpleGraph ι} (hT : T.IsTree)
    {t₁ t₂ : ι} (hadj : T.Adj t₁ t₂) (s : ι) :
    ((T.deleteEdges {s(t₁, t₂)}).Reachable t₁ s ∧
      ¬ (T.deleteEdges {s(t₁, t₂)}).Reachable t₂ s) ∨
    ((T.deleteEdges {s(t₁, t₂)}).Reachable t₂ s ∧
      ¬ (T.deleteEdges {s(t₁, t₂)}).Reachable t₁ s) := by
  have h₁ := reachable_deleteEdges_iff_onTreePath hT hadj s
  have h₂ := reachable_deleteEdges_iff_onTreePath hT hadj.symm s
  rw [Sym2.eq_swap] at h₂
  rw [h₁, h₂]
  exact Thomas.onTreePath_adj_dichotomy hT hadj s

theorem treeDecompSide_le [Fintype ι] {G : Hypergraph α β} {T : SimpleGraph ι}
    {τ : ι → Hypergraph α β} (hD : GM10.IsTreeDecomposition G T τ) (e : Sym2 ι) (u : ι) :
    GM10.treeDecompSide T τ e u ≤ G :=
  biUnion_le fun t _ ↦ hD.le t

theorem isSeparation_treeDecompSide [Fintype ι] {G : Hypergraph α β} {T : SimpleGraph ι}
    {τ : ι → Hypergraph α β} (hD : GM10.IsTreeDecomposition G T τ)
    {u v : ι} (hadj : T.Adj u v) :
    G.IsSeparation (GM10.treeDecompSide T τ s(u, v) u) (GM10.treeDecompSide T τ s(u, v) v) ∧
    (GM10.treeDecompSide T τ s(u, v) u ∩ GM10.treeDecompSide T τ s(u, v) v).vertexSet =
      (τ u ∩ τ v).vertexSet := by
  classical
  have hle_u := treeDecompSide_le hD s(u, v) u
  have hle_v := treeDecompSide_le hD s(u, v) v
  have hsep : G.IsSeparation (GM10.treeDecompSide T τ s(u, v) u)
      (GM10.treeDecompSide T τ s(u, v) v) := by
    rw [GM10.isSeparation_iff_of_le hle_u hle_v]
    refine ⟨?_, ?_, ?_⟩
    · have hVG : (Hypergraph.biUnion Finset.univ τ).vertexSet = G.vertexSet :=
        congrArg Hypergraph.vertexSet hD.biUnion_eq
      ext x
      constructor
      · exact fun hx ↦ Set.union_subset hle_u.vertexSet_subset hle_v.vertexSet_subset hx
      · intro hxG
        simp only [GM10.treeDecompSide, biUnion, Set.mem_union, Set.mem_iUnion, Finset.mem_filter,
          Finset.mem_univ, true_and]
        rw [← hVG, biUnion, Set.mem_iUnion₂] at hxG
        rcases hxG with ⟨s, _, hxs⟩
        rcases reachable_deleteEdges_dichotomy hD.isTree hadj s with ⟨h1, _⟩ | ⟨h2, _⟩
        · exact Or.inl ⟨s, h1, hxs⟩
        · exact Or.inr ⟨s, h2, hxs⟩
    · have hEG : (Hypergraph.biUnion Finset.univ τ).edgeSet = G.edgeSet :=
        congrArg Hypergraph.edgeSet hD.biUnion_eq
      ext f
      constructor
      · exact fun hf ↦ Set.union_subset hle_u.edgeSet_subset hle_v.edgeSet_subset hf
      · intro hfG
        simp only [GM10.treeDecompSide, biUnion, Set.mem_union, Set.mem_iUnion, Finset.mem_filter,
          Finset.mem_univ, true_and]
        rw [← hEG, biUnion, Set.mem_iUnion₂] at hfG
        rcases hfG with ⟨s, _, hfs⟩
        rcases reachable_deleteEdges_dichotomy hD.isTree hadj s with ⟨h1, _⟩ | ⟨h2, _⟩
        · exact Or.inl ⟨s, h1, hfs⟩
        · exact Or.inr ⟨s, h2, hfs⟩
    · ext f
      simp only [GM10.treeDecompSide, biUnion, Set.mem_inter_iff, Set.mem_iUnion,
        Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_empty_iff_false, iff_false]
      rintro ⟨⟨s₁, hs₁, hf₁⟩, ⟨s₂, hs₂, hf₂⟩⟩
      have hne : s₁ ≠ s₂ := by
        rintro rfl
        rcases reachable_deleteEdges_dichotomy hD.isTree hadj s₁ with ⟨_, hnot⟩ | ⟨_, hnot⟩
        · exact hnot hs₂
        · exact hnot hs₁
      exact Set.notMem_empty f (hD.edgeSet_inter_eq hne ▸ ⟨hf₁, hf₂⟩)
  refine ⟨hsep, ?_⟩
  ext x
  simp only [GM10.inter_vertexSet, GM10.treeDecompSide, biUnion, Set.mem_inter_iff,
    Set.mem_iUnion, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨s₁, hs₁, hx₁⟩, ⟨s₂, hs₂, hx₂⟩⟩
    have hon₁ : Thomas.OnTreePath T s₁ v u :=
      (reachable_deleteEdges_iff_onTreePath hD.isTree hadj s₁).1 hs₁
    have hon₂ : Thomas.OnTreePath T s₂ u v := by
      have h := reachable_deleteEdges_iff_onTreePath hD.isTree hadj.symm s₂
      rw [Sym2.eq_swap] at h
      exact h.1 hs₂
    have ⟨hu_on, hv_on⟩ := Thomas.onTreePath_of_sides hD.isTree hadj hon₁ hon₂
    exact ⟨(hD.inter_le hu_on).vertexSet_subset ⟨hx₁, hx₂⟩,
      (hD.inter_le hv_on).vertexSet_subset ⟨hx₁, hx₂⟩⟩
  · rintro ⟨hxu, hxv⟩
    exact ⟨⟨u, Reachable.refl u, hxu⟩, ⟨v, Reachable.refl v, hxv⟩⟩

theorem isSeparation_of_makesSeparation [Fintype ι] {G : Hypergraph α β} {T : SimpleGraph ι}
    {τ : ι → Hypergraph α β} (hD : GM10.IsTreeDecomposition G T τ)
    {e : Sym2 ι} {A B : Hypergraph α β} (hm : GM10.MakesSeparation T τ e A B) :
    G.IsSeparation A B := by
  rcases hm with ⟨u, v, hadj, _, rfl, rfl⟩
  exact (isSeparation_treeDecompSide hD hadj).1

/-- **Graph Minors XVIII, (2.4)** (page 80):
"**2.4.** *Let $(T, \tau)$ be a tree-decomposition of a hypergraph $G$, let $t_0 \in V(T)$ and let
$e_1, \dots, e_k$ be the edges of $T$ incident with $t_0$. For $1 \le i \le k$ let the components
of $T \setminus e_i$ be $T_i, T'_i$, where $t_0 \in V(T'_i)$. Then*
$$\{(\tau \times T_i, \tau \times T'_i): 1 \le i \le k\}$$
*is a location.*" -/
theorem theorem_2_4_proof [Fintype ι] {G : Hypergraph α β} {T : SimpleGraph ι}
    {τ : ι → Hypergraph α β} (hD : GM10.IsTreeDecomposition G T τ) (t₀ : ι) :
    GM10.IsLocation G (vertexLocation T τ t₀) where
  isSeparation := by
    rintro p ⟨u, hadj, rfl⟩
    exact (isSeparation_treeDecompSide hD hadj.symm).1
  left_le_right := by
    classical
    rintro p₁ ⟨u₁, hadj₁, rfl⟩ p₂ ⟨u₂, hadj₂, rfl⟩ hne
    have hu_ne : u₁ ≠ u₂ := fun h ↦ hne (by subst h; rfl)
    refine biUnion_mono (fun t _ ↦ hD.le t) fun s hs ↦ ?_
    rw [Finset.mem_filter] at hs ⊢
    refine ⟨Finset.mem_univ s, ?_⟩
    have hon₁ : Thomas.OnTreePath T s t₀ u₁ :=
      (reachable_deleteEdges_iff_onTreePath hD.isTree hadj₁.symm s).1 hs.2
    have h := reachable_deleteEdges_iff_onTreePath hD.isTree hadj₂ s
    rw [Sym2.eq_swap] at h
    rw [h]
    rcases Thomas.onTreePath_adj_dichotomy hD.isTree hadj₂.symm s with ⟨hon₂, _⟩ | ⟨hon₂, _⟩
    · exfalso
      rcases (Thomas.onTreePath_split_iff hD.isTree hon₁).1 hon₂ with h_left | h_right
      · have hon_u₂_u₁ : Thomas.OnTreePath T s t₀ u₁ := hon₁
        rcases (Thomas.onTreePath_split_iff hD.isTree hon₂).1 hon_u₂_u₁ with h_l2 | h_r2
        · exact hu_ne (Thomas.onTreePath_antisymm hD.isTree h_left h_l2).symm
        · have hp : (Thomas.treePath hD.isTree u₂ t₀) = hadj₂.symm.toWalk :=
            (Thomas.eq_treePath hD.isTree hadj₂.symm.toWalk hadj₂.symm.isPath_toWalk).symm
          have hmem := (Thomas.onTreePath_iff_mem_treePath hD.isTree).1 h_r2
          rw [hp, Walk.support_cons, Walk.support_nil, List.mem_cons, List.mem_singleton] at hmem
          rcases hmem with rfl | rfl
          · exact hu_ne rfl
          · exact hadj₁.ne rfl
      · have hp : (Thomas.treePath hD.isTree u₁ t₀) = hadj₁.symm.toWalk :=
          (Thomas.eq_treePath hD.isTree hadj₁.symm.toWalk hadj₁.symm.isPath_toWalk).symm
        have hmem := (Thomas.onTreePath_iff_mem_treePath hD.isTree).1 h_right
        rw [hp, Walk.support_cons, Walk.support_nil, List.mem_cons, List.mem_singleton] at hmem
        rcases hmem with rfl | rfl
        · exact hu_ne rfl
        · exact hadj₂.ne rfl
    · exact hon₂

/-- **Graph Minors XVIII, (2.5)** (page 80):
"Let $(T, \tau)$ be a tree-decomposition of a hypergraph $G$, and let $t \in V(T)$. Let
$\mathcal{L}$ be the location of $t$ in $(T, \tau)$; then $\tau(t) = M(G, \mathcal{L})$." -/
theorem theorem_2_5_proof [Fintype ι] {G : Hypergraph α β} {T : SimpleGraph ι}
    {τ : ι → Hypergraph α β} (hD : GM10.IsTreeDecomposition G T τ) (t₀ : ι) :
    τ t₀ = GM10.locationCore G (vertexLocation T τ t₀) := by
  classical
  have hℒ := theorem_2_4_proof hD t₀
  have hle_core : τ t₀ ≤ GM10.locationCore G (vertexLocation T τ t₀) := by
    rw [GM10.le_iff_of_le (hD.le t₀) (locationCore_le hℒ)]
    have ht₀_mem : ∀ p ∈ vertexLocation T τ t₀, τ t₀ ≤ p.2 := by
      rintro p ⟨u, _, rfl⟩
      refine le_biUnion_of_mem (fun s _ ↦ hD.le s) ?_
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ t₀, Reachable.refl t₀⟩
    exact ⟨fun v hv ↦ ⟨(hD.le t₀).vertexSet_subset hv, fun p hp ↦ (ht₀_mem p hp).vertexSet_subset
      hv⟩,
      fun e he ↦ ⟨(hD.le t₀).edgeSet_subset he, fun p hp ↦ (ht₀_mem p hp).edgeSet_subset he⟩⟩
  have step_neighbor : ∀ {t' : ι}, t' ≠ t₀ →
      ∃ u : ι, T.Adj t₀ u ∧ (T.deleteEdges {s(u, t₀)}).Reachable u t' := by
    intro t' hne
    obtain ⟨u, t'', he_edge, heq_t₀, hne_t₀⟩ :=
      Thomas.exists_onTreePathEdge_of_prop hD.isTree (· = t₀) rfl hne
    subst heq_t₀
    refine ⟨t'', he_edge.1, ?_⟩
    rw [reachable_deleteEdges_iff_onTreePath hD.isTree he_edge.1.symm t']
    rcases he_edge.orient hD.isTree with ⟨_, h2, _, _⟩ | ⟨h1, _, _, _⟩
    · exact Thomas.onTreePath_symm h2
    · exfalso
      rw [Thomas.onTreePath_self] at h1
      exact hne_t₀ h1
  refine GM10.eq_of_le_of_vertexSet_eq_of_edgeSet_eq (hD.le t₀) (locationCore_le hℒ) ?_ ?_
  · ext v
    constructor
    · exact fun hv ↦ hle_core.vertexSet_subset hv
    · rintro ⟨hvG, hall⟩
      by_contra hnot
      have hVG : (Hypergraph.biUnion Finset.univ τ).vertexSet = G.vertexSet :=
        congrArg Hypergraph.vertexSet hD.biUnion_eq
      rw [← hVG, biUnion, Set.mem_iUnion₂] at hvG
      rcases hvG with ⟨t', _, hvt'⟩
      have ht'_ne : t' ≠ t₀ := fun heq ↦ hnot (heq ▸ hvt')
      obtain ⟨u, hadj, hreach⟩ := step_neighbor ht'_ne
      let A := GM10.treeDecompSide T τ s(u, t₀) u
      let B := GM10.treeDecompSide T τ s(u, t₀) t₀
      have hp_mem : (A, B) ∈ vertexLocation T τ t₀ := ⟨u, hadj, rfl⟩
      have hvB : v ∈ B.vertexSet := hall (A, B) hp_mem
      have hvA : v ∈ A.vertexSet := by
        refine (le_biUnion_of_mem (fun s _ ↦ hD.le s) ?_).vertexSet_subset hvt'
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ t', hreach⟩
      have hAB_eq := (isSeparation_treeDecompSide hD hadj.symm).2
      have hv_inter : v ∈ (τ u ∩ τ t₀).vertexSet := hAB_eq ▸ ⟨hvA, hvB⟩
      exact hnot hv_inter.2
  · ext e
    constructor
    · exact fun he ↦ hle_core.edgeSet_subset he
    · rintro ⟨heG, hall⟩
      by_contra hnot
      have hEG : (Hypergraph.biUnion Finset.univ τ).edgeSet = G.edgeSet :=
        congrArg Hypergraph.edgeSet hD.biUnion_eq
      rw [← hEG, biUnion, Set.mem_iUnion₂] at heG
      rcases heG with ⟨t', _, het'⟩
      have ht'_ne : t' ≠ t₀ := fun heq ↦ hnot (heq ▸ het')
      obtain ⟨u, hadj, hreach⟩ := step_neighbor ht'_ne
      let A := GM10.treeDecompSide T τ s(u, t₀) u
      let B := GM10.treeDecompSide T τ s(u, t₀) t₀
      have hp_mem : (A, B) ∈ vertexLocation T τ t₀ := ⟨u, hadj, rfl⟩
      have heB : e ∈ B.edgeSet := hall (A, B) hp_mem
      have heA : e ∈ A.edgeSet := by
        refine (le_biUnion_of_mem (fun s _ ↦ hD.le s) ?_).edgeSet_subset het'
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ t', hreach⟩
      have hsep := (isSeparation_treeDecompSide hD hadj.symm).1
      exact hsep.notMem_edgeSet_right heA heB

/-! ## (2.6) and (2.7): Standard Decompositions -/

/-- Distinct tangles of the same order `θ` in `G` are distinguishable. -/
theorem areDistinguishable_of_ne_of_same_order {G : Hypergraph α β} {θ : ℕ}
    {𝒯₁ 𝒯₂ : Set (Hypergraph α β × Hypergraph α β)}
    (h₁ : GM10.IsTangle G θ 𝒯₁) (h₂ : GM10.IsTangle G θ 𝒯₂) (hne : 𝒯₁ ≠ 𝒯₂) :
    GM10.AreDistinguishable 𝒯₁ 𝒯₂ := by
  rintro (hsub | hsub)
  · apply hne (Set.Subset.antisymm hsub ?_)
    rintro ⟨A, B⟩ hAB₂
    rcases h₁.axiom1 (h₂.isSeparation hAB₂) (h₂.order_lt hAB₂) with hAB₁ | hBA₁
    · exact hAB₁
    · exact (GM10.theorem_2_1_proof h₂ hAB₂ (hsub hBA₁)).elim
  · apply hne (Set.Subset.antisymm ?_ hsub)
    rintro ⟨A, B⟩ hAB₁
    rcases h₂.axiom1 (h₁.isSeparation hAB₁) (h₁.order_lt hAB₁) with hAB₂ | hBA₂
    · exact hAB₂
    · exact (GM10.theorem_2_1_proof h₁ hAB₁ (hsub hBA₂)).elim

theorem treeDecompSide_symm_edge [Fintype ι] (T : SimpleGraph ι) (τ : ι → Hypergraph α β)
    (u v : ι) :
    GM10.treeDecompSide T τ s(v, u) = GM10.treeDecompSide T τ s(u, v) := by
  rw [Sym2.eq_swap]

theorem makesSeparation_adj_iff [Fintype ι] {T : SimpleGraph ι}
    (τ : ι → Hypergraph α β) {u v : ι} (hadj : T.Adj u v) (A B : Hypergraph α β) :
    GM10.MakesSeparation T τ s(u, v) A B ↔
      (A = GM10.treeDecompSide T τ s(u, v) u ∧ B = GM10.treeDecompSide T τ s(u, v) v) ∨
      (A = GM10.treeDecompSide T τ s(u, v) v ∧ B = GM10.treeDecompSide T τ s(u, v) u) := by
  constructor
  · rintro ⟨u', v', _, heq, rfl, rfl⟩
    rw [Sym2.eq_iff] at heq
    rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨rfl, rfl⟩
    · rw [Sym2.eq_swap]
      exact Or.inr ⟨rfl, rfl⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact ⟨u, v, hadj, rfl, rfl, rfl⟩
    · refine ⟨v, u, hadj.symm, Sym2.eq_swap, ?_, ?_⟩ <;> rw [Sym2.eq_swap]

/-- **Graph Minors XVIII, (2.6)** (page 81):
"Let $\mathscr{T}_1, \dots, \mathscr{T}_n$ be distinct tangles of order $\theta$ in a
hypergraph $G$ with $n \ge 1$, and let $\lambda$ be a tie-breaker. Then there is a
tree-decomposition $(T, \tau)$ of $G$ where $V(T) = \{t_1, \dots, t_n\}$, with the following
properties:* 1. *if $e \in E(T)$ and $T_1, T_2$ are the components of $T \setminus e$ and $1
\le i \le n$ and $t_i \in V(T_2)$ then $(\tau \times T_1, \tau \times T_2) \in
\mathscr{T}_i$,* 2. *for $1 \le i < j \le n$, let $e$ be the edge of the path of $T$ between
$t_i, t_j$ making separations of minimum $\lambda$-order; then these separations are the
$(\mathscr{T}_i, \mathscr{T}_j)$- and $(\mathscr{T}_j, \mathscr{T}_i)$-distinctions." -/
theorem theorem_2_6_proof {Λ : Type w} [LinearOrder Λ] {n : ℕ}
    (G : Hypergraph α β) (lam : Hypergraph α β × Hypergraph α β → Λ)
    (θ : ℕ) (𝒯 : Fin n → Set (Hypergraph α β × Hypergraph α β))
    (hn : 1 ≤ n) (hlam : GM10.IsTieBreaker G lam)
    (h𝒯 : ∀ i : Fin n, GM10.IsTangle G θ (𝒯 i))
    (hdist : Function.Injective 𝒯) :
    ∃ (T : SimpleGraph (Fin n)) (τ : Fin n → Hypergraph α β),
      IsStandardDecomposition G lam 𝒯 T τ := by
  have hmut : ∀ i j : Fin n, i ≠ j → GM10.AreDistinguishable (𝒯 i) (𝒯 j) := fun i j hij ↦
    areDistinguishable_of_ne_of_same_order (h𝒯 i) (h𝒯 j) (hdist.ne hij)
  obtain ⟨T, τ, hstd⟩ := gm10Theorem103 G lam (fun _ ↦ θ) 𝒯 hn hlam h𝒯 hmut
  refine ⟨T, τ, ⟨hstd.isTreeDecomposition, ?_, hstd.path_min_isDistinction⟩⟩
  intro i u v hadj hreach
  obtain ⟨e, _, he_path, _, A, B, hmAB, hdist_uv, _⟩ := hstd.path_min_isDistinction hadj.ne
  have he_eq : e = s(u, v) := by
    have hmem := he_path hadj.toWalk hadj.isPath_toWalk
    simpa using hmem
  subst he_eq
  have hord_AB : separationOrder A B < θ := (h𝒯 u).order_lt hdist_uv.1.1
  have hord_uv : separationOrder (GM10.treeDecompSide T τ s(u, v) u)
      (GM10.treeDecompSide T τ s(u, v) v) < θ := by
    rcases (makesSeparation_adj_iff τ hadj A B).1 hmAB with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hord_AB
    · rwa [GM10.separationOrder_comm]
  have hsep_uv := (isSeparation_treeDecompSide hstd.isTreeDecomposition hadj).1
  have hnot_swap :
      (GM10.treeDecompSide T τ s(u, v) v, GM10.treeDecompSide T τ s(u, v) u) ∉ 𝒯 i := by
    have hhome := hstd.isHome i hadj.symm
    rw [Sym2.eq_swap] at hhome
    exact hhome hreach
  exact ((h𝒯 i).axiom1 hsep_uv hord_uv).resolve_right hnot_swap

theorem isSeparation_left_split {G A B C D : Hypergraph α β}
    (hAB : G.IsSeparation A B) (hCD : A.IsSeparation C D) :
    G.IsSeparation C (B ∪ D) := by
  have hC_G : C ≤ G := hCD.left_le.trans hAB.left_le
  have hD_G : D ≤ G := hCD.right_le.trans hAB.left_le
  rw [GM10.isSeparation_iff_of_le hC_G (GM10.union_le hAB.right_le hD_G)]
  refine ⟨?_, ?_, ?_⟩
  · rw [GM10.union_vertexSet, Set.union_comm B.vertexSet, ← Set.union_assoc,
      hCD.vertexSet_union, hAB.vertexSet_union]
  · rw [GM10.union_edgeSet, Set.union_comm B.edgeSet, ← Set.union_assoc,
      hCD.edgeSet_union, hAB.edgeSet_union]
  · ext e
    simp only [GM10.union_edgeSet, Set.mem_inter_iff, Set.mem_union,
      Set.mem_empty_iff_false, iff_false]
    rintro ⟨heC, heB | heD⟩
    · exact hAB.notMem_edgeSet_right (hCD.left_le.edgeSet_subset heC) heB
    · exact hCD.notMem_edgeSet_right heC heD

/-- Any `λ`-robust separation in `G` (for a tie-breaker `λ`) is robust. -/
theorem isRobust_of_isLambdaRobust {Λ : Type w} [LinearOrder Λ]
    {G A B : Hypergraph α β} {lam : Hypergraph α β × Hypergraph α β → Λ}
    (hlam : GM10.IsTieBreaker G lam) (hrob : GM10.IsLambdaRobust G lam A B) :
    GM10.IsRobust G A B := by
  refine ⟨hrob.1, fun C D hCD ↦ ?_⟩
  have hsep₁ : G.IsSeparation C (B ∪ D) := isSeparation_left_split hrob.1 hCD
  have hsep₂ : G.IsSeparation D (B ∪ C) := isSeparation_left_split hrob.1 hCD.symm
  rcases hrob.2 hCD with hle₁ | hle₂
  · left
    by_contra! hlt
    exact not_lt_of_ge hle₁ (hlam.axiom3 hsep₁ hrob.1 hlt)
  · right
    by_contra! hlt
    exact not_lt_of_ge hle₂ (hlam.axiom3 hsep₂ hrob.1 hlt)

/-- **Graph Minors XVIII, (2.7)** (page 81):
"Let $\mathscr{T}_1, \dots, \mathscr{T}_n$ be distinct tangles of order $\theta$ in a
hypergraph $G$ with $n \ge 1$, and let $\lambda$ be a tie-breaker. Let $(T, \tau)$ be as in
2.6. Then $(T, \tau)$ is proper and rotund, and every separation made by an edge of $T$
under $(T, \tau)$ is robust." -/
theorem theorem_2_7_proof {Λ : Type w} [LinearOrder Λ] {n : ℕ}
    {G : Hypergraph α β} {lam : Hypergraph α β × Hypergraph α β → Λ}
    {θ : ℕ} {𝒯 : Fin n → Set (Hypergraph α β × Hypergraph α β)}
    {T : SimpleGraph (Fin n)} {τ : Fin n → Hypergraph α β}
    (hlam : GM10.IsTieBreaker G lam)
    (h𝒯 : ∀ i : Fin n, GM10.IsTangle G θ (𝒯 i))
    (hstd : IsStandardDecomposition G lam 𝒯 T τ) :
    IsProper G T τ ∧
    IsRotund G T τ ∧
    (∀ ⦃e : Sym2 (Fin n)⦄, e ∈ T.edgeSet → ∀ ⦃A B : Hypergraph α β⦄,
      GM10.MakesSeparation T τ e A B → GM10.IsRobust G A B) := by
  have hD := hstd.isTreeDecomposition
  have edge_isDistinction : ∀ ⦃e : Sym2 (Fin n)⦄, e ∈ T.edgeSet → ∀ ⦃A B : Hypergraph α β⦄,
      GM10.MakesSeparation T τ e A B →
      ∃ i j : Fin n, i ≠ j ∧ GM10.IsDistinction lam (𝒯 i) (𝒯 j) A B ∧
        GM10.IsDistinction lam (𝒯 j) (𝒯 i) B A := by
    rintro e _ A B ⟨u, v, hadj, rfl, rfl, rfl⟩
    obtain ⟨e', _, he'_path, _, A', B', hmA'B', hdist₁, hdist₂⟩ :=
      hstd.path_min_isDistinction hadj.ne
    have he'_eq : e' = s(u, v) := by
      have hmem := he'_path hadj.toWalk hadj.isPath_toWalk
      simpa using hmem
    subst he'_eq
    rcases (makesSeparation_adj_iff τ hadj A' B').1 hmA'B' with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨u, v, hadj.ne, hdist₁, hdist₂⟩
    · exact ⟨v, u, hadj.symm.ne, hdist₂, hdist₁⟩
  have hproper : IsProper G T τ := by
    intro e he A B hm hBG
    obtain ⟨i, j, _, _, hdist_ji⟩ := edge_isDistinction he hm
    exact (h𝒯 j).axiom3 hdist_ji.1.1 (congrArg Hypergraph.vertexSet hBG)
  have hrobust : ∀ ⦃e : Sym2 (Fin n)⦄, e ∈ T.edgeSet → ∀ ⦃A B : Hypergraph α β⦄,
      GM10.MakesSeparation T τ e A B → GM10.IsRobust G A B := by
    intro e he A B hm
    obtain ⟨i, j, _, hdist_ij, _⟩ := edge_isDistinction he hm
    have hdoubly := gm10Theorem102 G lam θ θ (𝒯 i) (𝒯 j) A B hlam (h𝒯 i) (h𝒯 j) hdist_ij
    exact isRobust_of_isLambdaRobust hlam hdoubly.1
  refine ⟨hproper, ?_, hrobust⟩
  intro t₁ t₂ p hp f₁ f₂ _ _ hf₁_p hf₂_p A₁ B₁ A₂ B₂ hm₁ hm₂ hB₂_A₁ hB₁_A₂ hord_eq
    ⟨H₁, H₂, hsepH, hB₁_H₁, hB₂_H₂, hordH⟩
  have edge_mem_t₁_or_t₂ : ∀ ⦃f : Sym2 (Fin n)⦄, f ∈ p.edges → ∀ ⦃A B : Hypergraph α β⦄,
      GM10.MakesSeparation T τ f A B → (A, B) ∈ 𝒯 t₁ ∨ (A, B) ∈ 𝒯 t₂ := by
    rintro f hf_p A B ⟨u, v, hadj, rfl, rfl, rfl⟩
    have hon_edge : Thomas.OnTreePathEdge T t₁ t₂ u v :=
      (Thomas.onTreePathEdge_iff_mem_treePath hD.isTree).2
        ⟨hadj, Thomas.eq_treePath hD.isTree p hp ▸ hf_p⟩
    have hnot_t₁_t₂ : ¬ (T.deleteEdges {s(u, v)}).Reachable t₁ t₂ :=
      (Thomas.onTreePathEdge_iff_not_reachable_deleteEdges.1 hon_edge).2
    rcases reachable_deleteEdges_dichotomy hD.isTree hadj t₁ with ⟨ht₁_u, _⟩ | ⟨ht₁_v, _⟩
    · right
      rcases reachable_deleteEdges_dichotomy hD.isTree hadj t₂ with ⟨ht₂_u, _⟩ | ⟨ht₂_v, _⟩
      · exact (hnot_t₁_t₂ (ht₁_u.symm.trans ht₂_u)).elim
      · exact hstd.side_mem_tangle t₂ u v hadj ht₂_v
    · left
      exact hstd.side_mem_tangle t₁ u v hadj ht₁_v
  have hsep₁ := isSeparation_of_makesSeparation hD hm₁
  have hsep₂ := isSeparation_of_makesSeparation hD hm₂
  have hA₁_A₂_eq_G : A₁ ∪ A₂ = G := by
    have hle : A₁ ∪ A₂ ≤ G := GM10.union_le hsep₁.left_le hsep₂.left_le
    refine GM10.eq_of_le_of_vertexSet_eq_of_edgeSet_eq hle le_rfl
      (Set.Subset.antisymm hle.vertexSet_subset
        (hsep₁.vertexSet_union ▸ Set.union_subset_union_right _ hB₁_A₂.vertexSet_subset))
      (Set.Subset.antisymm hle.edgeSet_subset
        (hsep₁.edgeSet_union ▸ Set.union_subset_union_right _ hB₁_A₂.edgeSet_subset))
  have hnot_same : ∀ i : Fin n, ¬ ((A₁, B₁) ∈ 𝒯 i ∧ (A₂, B₂) ∈ 𝒯 i) := by
    rintro i ⟨h₁, h₂⟩
    apply (h𝒯 i).axiom2 h₁ h₂ h₂
    rw [GM10.union_assoc, GM10.union_self, hA₁_A₂_eq_G]
  have hex_ij : ∃ i j : Fin n, (i = t₁ ∧ j = t₂ ∨ i = t₂ ∧ j = t₁) ∧
      (A₁, B₁) ∈ 𝒯 i ∧ (A₂, B₂) ∈ 𝒯 j := by
    rcases edge_mem_t₁_or_t₂ hf₁_p hm₁ with h₁ | h₁ <;>
      rcases edge_mem_t₁_or_t₂ hf₂_p hm₂ with h₂ | h₂
    · exact (hnot_same t₁ ⟨h₁, h₂⟩).elim
    · exact ⟨t₁, t₂, Or.inl ⟨rfl, rfl⟩, h₁, h₂⟩
    · exact ⟨t₂, t₁, Or.inr ⟨rfl, rfl⟩, h₁, h₂⟩
    · exact (hnot_same t₂ ⟨h₁, h₂⟩).elim
  obtain ⟨i, j, hij_cases, h₁_i, h₂_j⟩ := hex_ij
  have hij_ne : i ≠ j := fun heq ↦ hnot_same i ⟨h₁_i, heq ▸ h₂_j⟩
  have hord₁_lt_θ : separationOrder A₁ B₁ < θ := (h𝒯 i).order_lt h₁_i
  have hordH_lt_θ : separationOrder H₁ H₂ < θ := hordH.trans hord₁_lt_θ
  have hA₁_H₁_eq_G : A₁ ∪ H₁ = G := by
    have hle : A₁ ∪ H₁ ≤ G := GM10.union_le hsep₁.left_le hsepH.left_le
    refine GM10.eq_of_le_of_vertexSet_eq_of_edgeSet_eq hle le_rfl
      (Set.Subset.antisymm hle.vertexSet_subset
        (hsep₁.vertexSet_union ▸ Set.union_subset_union_right _ hB₁_H₁.vertexSet_subset))
      (Set.Subset.antisymm hle.edgeSet_subset
        (hsep₁.edgeSet_union ▸ Set.union_subset_union_right _ hB₁_H₁.edgeSet_subset))
  have hA₂_H₂_eq_G : A₂ ∪ H₂ = G := by
    have hle : A₂ ∪ H₂ ≤ G := GM10.union_le hsep₂.left_le hsepH.right_le
    refine GM10.eq_of_le_of_vertexSet_eq_of_edgeSet_eq hle le_rfl
      (Set.Subset.antisymm hle.vertexSet_subset
        (hsep₂.vertexSet_union ▸ Set.union_subset_union_right _ hB₂_H₂.vertexSet_subset))
      (Set.Subset.antisymm hle.edgeSet_subset
        (hsep₂.edgeSet_union ▸ Set.union_subset_union_right _ hB₂_H₂.edgeSet_subset))
  have hH₁_not_i : (H₁, H₂) ∉ 𝒯 i := fun hm ↦ by
    apply (h𝒯 i).axiom2 h₁_i hm hm
    rw [GM10.union_assoc, GM10.union_self, hA₁_H₁_eq_G]
  have hH₂_i : (H₂, H₁) ∈ 𝒯 i := ((h𝒯 i).axiom1 hsepH hordH_lt_θ).resolve_left hH₁_not_i
  have hH₂_not_j : (H₂, H₁) ∉ 𝒯 j := fun hm ↦ by
    apply (h𝒯 j).axiom2 h₂_j hm hm
    rw [GM10.union_assoc, GM10.union_self, hA₂_H₂_eq_G]
  have hH₁_j : (H₁, H₂) ∈ 𝒯 j := ((h𝒯 j).axiom1 hsepH hordH_lt_θ).resolve_right hH₂_not_j
  have hH_dist : GM10.Distinguishes (𝒯 i) (𝒯 j) H₂ H₁ := ⟨hH₂_i, hH₁_j⟩
  obtain ⟨e, he_T, he_path, _, C, D, hmCD, hdist_CD, _⟩ := hstd.path_min_isDistinction hij_ne
  have he_p : e ∈ p.edges := by
    rcases hij_cases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact he_path p hp
    · have hrev := he_path p.reverse hp.reverse
      rwa [Walk.edges_reverse, List.mem_reverse] at hrev
  have hlam_le : lam (C, D) ≤ lam (H₂, H₁) := hdist_CD.2 hH_dist
  have hsepCD := isSeparation_of_makesSeparation hD hmCD
  have hord_CD_le : separationOrder C D ≤ separationOrder H₂ H₁ := by
    by_contra! hlt
    exact not_lt_of_ge hlam_le (hlam.axiom3 hsepH.symm hsepCD hlt)
  rw [GM10.separationOrder_comm H₂ H₁] at hord_CD_le
  exact ⟨e, he_p, C, D, hmCD, hord_CD_le.trans_lt hordH⟩

end GraphMinor.GM18
