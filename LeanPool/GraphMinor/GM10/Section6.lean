/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM10.Defs2
import LeanPool.GraphMinor.GM10.TangleLemmas
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# Circuits and New Tangles from Old (Graph Minors X, (2.10) and Section 6)

This file formalizes (2.10) and Section 6 of Graph Minors X (pages 158–159 and 170–171):
- `theorem_2_10_claim_1` and `theorem_2_10`: **Graph Minors X, (2.10)** (pages 158–159).
- `subset_iff_truncation` and `subset_iff_exists_truncation`: two tangles in `G` satisfy
  `𝒯' ⊆ 𝒯` if and only if `𝒯'` is a truncation of `𝒯` (Graph Minors X, Section 6, page 170).
- `theorem_6_1`: **Graph Minors X, (6.1)** (page 170), the tangle in `G` induced by a tangle in a
  minor `H` of `G`.
- `theorem_6_2`: **Graph Minors X, (6.2)** (page 171), the tangle `𝒯 / W` in `G / W` of order
  `θ - |W|`.
- `theorem_6_3`: **Graph Minors X, (6.3)** (page 171), characterizing when `(A / W, B / W) ∈ 𝒯 / W`.
-/

public section

namespace GraphMinor.GM10

open Graph SimpleGraph Hypergraph Relation

variable {α β : Type*}

/-! ## Graph Minors X, (2.10) -/

/-- Claim (1) in the proof of **Graph Minors X, (2.10)** (page 159):
"There is no separation $(B_1, B_2)$ of $B$ of order $\le 1$ with $v_1\in V(B_1) - V(B_2)$
and $v_2\in V(B_2) - V(B_1)$." -/
theorem theorem_2_10_claim_1 {G : Hypergraph α β} {θ : ℕ}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} (h𝒯 : IsTangle G θ 𝒯)
    {A B : Hypergraph α β} (hext : IsExtreme 𝒯 A B)
    {v₁ v₂ : α} (hv₁ : v₁ ∈ (A ∩ B).vertexSet) (hv₂ : v₂ ∈ (A ∩ B).vertexSet)
    {B₁ B₂ : Hypergraph α β} (hB : B.IsSeparation B₁ B₂)
    (h₁ : v₁ ∈ B₁.vertexSet \ B₂.vertexSet) (h₂ : v₂ ∈ B₂.vertexSet \ B₁.vertexSet) :
    2 ≤ separationOrder B₁ B₂ := by
  have hB₁_ne_B : B₁ ≠ B := fun h ↦ h₂.2 (h ▸ hv₂.2)
  have hB₂_ne_B : B₂ ≠ B := fun h ↦ h₁.2 (h ▸ hv₁.2)
  rcases theorem_2_8_separation h𝒯 hext hB with ⟨_, h⟩ | ⟨_, h⟩ | hlt
  · exact (hB₂_ne_B h).elim
  · exact (hB₁_ne_B h).elim
  · have h1 : 1 ≤ (A ∩ B₁).vertexSet.ncard := by
      have : {v₁} ⊆ (A ∩ B₁).vertexSet := Set.singleton_subset_iff.2 ⟨hv₁.1, h₁.1⟩
      simpa using Set.ncard_le_ncard this (A ∩ B₁).vertexSet_finite
    have h2 : 1 ≤ (A ∩ B₂).vertexSet.ncard := by
      have : {v₂} ⊆ (A ∩ B₂).vertexSet := Set.singleton_subset_iff.2 ⟨hv₂.1, h₂.1⟩
      simpa using Set.ncard_le_ncard this (A ∩ B₂).vertexSet_finite
    omega

/-- Monotonicity of `HasCircuit` under subhypergraph inclusion. -/
theorem HasCircuit.mono {H G : Hypergraph α β} (hle : H ≤ G) (h : HasCircuit H) :
    HasCircuit G := by
  rcases h with ⟨e, he, hcard⟩ | ⟨e₁, he₁, e₂, he₂, hne, hcard⟩ | hacyc
  · exact Or.inl ⟨e, hle.edgeSet_subset he, by rwa [hle.ends_eq e he]⟩
  · exact Or.inr (Or.inl ⟨e₁, hle.edgeSet_subset he₁, e₂, hle.edgeSet_subset he₂, hne,
      by rwa [hle.ends_eq e₁ he₁, hle.ends_eq e₂ he₂]⟩)
  · refine Or.inr (Or.inr fun hG_acyc ↦ hacyc ?_)
    have hskel_le : H.skeleton ≤ G.skeleton := by
      intro x y ⟨hxy, e, hx, hy⟩
      exact ⟨hxy, e, inc_of_le hle hx, inc_of_le hle hy⟩
    exact hG_acyc.anti hskel_le

private lemma walk_support_subset_vertexSet {G : Hypergraph α β} {u v : α}
    (w : G.skeleton.Walk u v) (hu : u ∈ G.vertexSet) :
    ∀ z ∈ w.support, z ∈ G.vertexSet :=
  Hypergraph.skeleton_walk_support_subset_vertexSet w hu

private def reachableAvoidingVertex (G : Hypergraph α β) (v₁ : α) (S : Set α) : Set α :=
  {u | ∃ w : G.skeleton.Walk v₁ u, ∀ z ∈ w.support, z ∉ S}

private lemma exists_separation_of_vertex_separator {B : Hypergraph α β} {v₁ v₂ : α} {S : Set α}
    (hv₁ : v₁ ∈ B.vertexSet) (hv₂ : v₂ ∈ B.vertexSet) (hS_sub : S ⊆ B.vertexSet)
    (hv₁S : v₁ ∉ S) (hv₂S : v₂ ∉ S)
    (hsep_walk : ∀ p : B.skeleton.Path v₁ v₂, ∃ z ∈ p.1.support, z ∈ S) :
    ∃ B₁ B₂ : Hypergraph α β,
      B.IsSeparation B₁ B₂ ∧
      v₁ ∈ B₁.vertexSet \ B₂.vertexSet ∧
      v₂ ∈ B₂.vertexSet \ B₁.vertexSet ∧
      separationOrder B₁ B₂ = S.ncard := by
  classical
  let R := reachableAvoidingVertex B v₁ S
  have hR_sub : R ⊆ B.vertexSet \ S := by
    rintro u ⟨w, hw⟩
    exact ⟨walk_support_subset_vertexSet w hv₁ u (Walk.end_mem_support w),
      hw u (Walk.end_mem_support w)⟩
  have hv₁R : v₁ ∈ R := by
    refine ⟨.nil, fun z hz ↦ ?_⟩
    simp only [Walk.support_nil, List.mem_cons, List.not_mem_nil, or_false] at hz
    exact hz ▸ hv₁S
  have hv₂R : v₂ ∉ R := by
    rintro ⟨w, hw⟩
    obtain ⟨z, hz, hzS⟩ := hsep_walk ⟨w.bypass, w.bypass_isPath⟩
    exact hw z (w.support_bypass_subset_support hz) hzS
  let V₁ : Set α := R ∪ S
  let E₁ : Set β := {e ∈ B.edgeSet | B.ends e ⊆ V₁}
  let V₂ : Set α := B.vertexSet \ R
  let E₂ : Set β := B.edgeSet \ E₁
  have hV₁_sub : V₁ ⊆ B.vertexSet := Set.union_subset (hR_sub.trans Set.sdiff_subset) hS_sub
  have hV₂_sub : V₂ ⊆ B.vertexSet := Set.sdiff_subset
  have hE₂_ends : ∀ ⦃e : β⦄ ⦃v : α⦄, e ∈ E₂ → B.Inc e v → v ∈ V₂ := by
    intro e v he₂ hinc
    refine ⟨B.vertex_mem_of_inc hinc, fun hvR ↦ he₂.2 ⟨he₂.1, fun u hu ↦ ?_⟩⟩
    by_contra huV₁
    have huR : u ∉ R := fun h ↦ huV₁ (Or.inl h)
    have huS : u ∉ S := fun h ↦ huV₁ (Or.inr h)
    have hvu : v ≠ u := fun h ↦ huR (h ▸ hvR)
    have hadj : B.skeleton.Adj v u := ⟨hvu, e, hinc, hu⟩
    rcases hvR with ⟨w, hw⟩
    refine huR ⟨w.concat hadj, fun z hz ↦ ?_⟩
    simp only [Walk.support_concat, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false] at hz
    rcases hz with hz | rfl
    · exact hw z hz
    · exact huS
  let B₁ : Hypergraph α β :=
    { vertexSet := V₁
      edgeSet := E₁
      Inc := fun e v ↦ e ∈ E₁ ∧ B.Inc e v
      vertex_mem_of_inc := fun _ _ h ↦ h.1.2 h.2
      edge_mem_of_inc := fun _ _ h ↦ h.1
      vertexSet_finite := B.vertexSet_finite.subset hV₁_sub
      edgeSet_finite := B.edgeSet_finite.subset (fun _ h ↦ h.1) }
  let B₂ : Hypergraph α β :=
    { vertexSet := V₂
      edgeSet := E₂
      Inc := fun e v ↦ e ∈ E₂ ∧ B.Inc e v
      vertex_mem_of_inc := fun _ _ h ↦ hE₂_ends h.1 h.2
      edge_mem_of_inc := fun _ _ h ↦ h.1
      vertexSet_finite := B.vertexSet_finite.subset hV₂_sub
      edgeSet_finite := B.edgeSet_finite.subset Set.sdiff_subset }
  have hB₁_le : B₁ ≤ B :=
    ⟨hV₁_sub, fun _ h ↦ h.1, fun e he ↦ Set.ext fun v ↦ ⟨fun h ↦ ⟨he, h⟩, fun h ↦ h.2⟩⟩
  have hB₂_le : B₂ ≤ B :=
    ⟨hV₂_sub, Set.sdiff_subset, fun e he ↦ Set.ext fun v ↦ ⟨fun h ↦ ⟨he, h⟩, fun h ↦ h.2⟩⟩
  refine ⟨B₁, B₂, ?_, ?_, ?_, ?_⟩
  · rw [isSeparation_iff_of_le hB₁_le hB₂_le]
    refine ⟨?_, ?_, ?_⟩
    · ext v
      change v ∈ (R ∪ S) ∪ (B.vertexSet \ R) ↔ v ∈ B.vertexSet
      exact ⟨fun h ↦ h.elim (fun h₁ ↦ hV₁_sub h₁) (fun h₂ ↦ h₂.1),
        fun hv ↦ by by_cases hvR : v ∈ R <;> [exact Or.inl (Or.inl hvR); exact Or.inr ⟨hv, hvR⟩]⟩
    · ext e
      change e ∈ E₁ ∪ (B.edgeSet \ E₁) ↔ e ∈ B.edgeSet
      exact ⟨fun h ↦ h.elim (fun h₁ ↦ h₁.1) (fun h₂ ↦ h₂.1),
        fun he ↦ by by_cases h₁ : e ∈ E₁ <;> [exact Or.inl h₁; exact Or.inr ⟨he, h₁⟩]⟩
    · ext e
      change e ∈ E₁ ∧ e ∈ B.edgeSet \ E₁ ↔ False
      exact ⟨fun ⟨h₁, _, h₂⟩ ↦ h₂ h₁, False.elim⟩
  · exact ⟨Or.inl hv₁R, fun h ↦ h.2 hv₁R⟩
  · exact ⟨⟨hv₂, hv₂R⟩, fun h ↦ h.elim hv₂R hv₂S⟩
  · have h_inter : (B₁ ∩ B₂).vertexSet = S := by
      ext v
      change v ∈ (R ∪ S) ∧ v ∈ B.vertexSet \ R ↔ v ∈ S
      exact ⟨fun ⟨h₁, _, h₂⟩ ↦ h₁.resolve_left h₂,
        fun hvS ↦ ⟨Or.inr hvS, hS_sub hvS, fun hvR ↦ (hR_sub hvR).2 hvS⟩⟩
    rw [separationOrder, h_inter]

/-- **Graph Minors X, (2.10)** (pages 158–159):
"Let $\mathscr{T}$ be a tangle of order $\ge 3$ in a graph $G$, and let $(A, B)\in
\mathscr{T}$. Then $B$ has a circuit." -/
theorem theorem_2_10_proof {G : Hypergraph α β} {θ : ℕ}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} (h𝒯 : IsTangle G θ 𝒯) (hθ : 3 ≤ θ)
    {A₀ B₀ : Hypergraph α β} (hAB₀ : (A₀, B₀) ∈ 𝒯) :
    HasCircuit B₀ := by
  obtain ⟨A, B, hext, _, hBB₀⟩ := h𝒯.exists_isExtreme hAB₀
  apply HasCircuit.mono hBB₀
  refine Or.inr (Or.inr fun hacyc ↦ ?_)
  have hord : separationOrder A B = θ - 1 := theorem_2_8_order h𝒯 hext
  have hcard_ge : 2 ≤ (A ∩ B).vertexSet.ncard := by
    rw [← separationOrder]
    omega
  obtain ⟨v₁, hv₁⟩ :=
    Set.nonempty_of_ncard_ne_zero (by omega : (A ∩ B).vertexSet.ncard ≠ 0)
  obtain ⟨v₂, hv₂, hne₂₁⟩ :=
    Set.exists_ne_of_one_lt_ncard (by omega : 1 < (A ∩ B).vertexSet.ncard) v₁
  have hne : v₁ ≠ v₂ := hne₂₁.symm
  have hnot_adj : ¬ B.skeleton.Adj v₁ v₂ := by
    rintro ⟨_, e, hinc₁, hinc₂⟩
    have heB : e ∈ B.edgeSet := B.edge_mem_of_inc hinc₁
    have hnot_sub : ¬ B.ends e ⊆ A.vertexSet :=
      theorem_2_8_no_edge_ends_subset h𝒯 hext heB
    obtain ⟨v₃, hv₃_ends, hv₃_notA⟩ := Set.not_subset.1 hnot_sub
    have hv₁₃ : v₁ ≠ v₃ := fun h ↦ hv₃_notA (h ▸ hv₁.1)
    have hv₃₂ : v₃ ≠ v₂ := fun h ↦ hv₃_notA (h.symm ▸ hv₂.1)
    have hadj₁₂ : B.skeleton.Adj v₁ v₂ := ⟨hne, e, hinc₁, hinc₂⟩
    have hadj₁₃ : B.skeleton.Adj v₁ v₃ := ⟨hv₁₃, e, hinc₁, hv₃_ends⟩
    have hadj₃₂ : B.skeleton.Adj v₃ v₂ := ⟨hv₃₂, e, hv₃_ends, hinc₂⟩
    let p₁ : B.skeleton.Path v₁ v₂ :=
      ⟨Walk.cons hadj₁₂ .nil, Walk.IsPath.cons .nil (by simp [hne])⟩
    let p₂ : B.skeleton.Path v₁ v₂ :=
      ⟨Walk.cons hadj₁₃ (Walk.cons hadj₃₂ .nil),
        Walk.IsPath.cons (Walk.IsPath.cons .nil (by simp [hv₃₂])) (by simp [hv₁₃, hne])⟩
    have hp_eq : p₁ = p₂ := (hacyc.subsingleton_path v₁ v₂).elim p₁ p₂
    have hlen : p₁.1.length = p₂.1.length :=
      congrArg (fun p : B.skeleton.Path v₁ v₂ ↦ p.1.length) hp_eq
    simp [p₁, p₂] at hlen
  by_cases hreach : B.skeleton.Reachable v₁ v₂
  · obtain ⟨w, hw_path⟩ := hreach.exists_isPath
    let p : B.skeleton.Path v₁ v₂ := ⟨w, hw_path⟩
    rcases w with _ | ⟨hadj₁, rest⟩
    · exact hne rfl
    · rcases rest with _ | ⟨hadj₂, rest'⟩
      · exact hnot_adj hadj₁
      · rename_i u u'
        have huB : u ∈ B.vertexSet := by
          obtain ⟨_, e, _, hu⟩ := id hadj₁
          exact B.vertex_mem_of_inc hu
        have hv₁u : v₁ ≠ u := hadj₁.ne
        have huv₂ : u ≠ v₂ := by
          have hnodup := hw_path.support_nodup
          simp only [Walk.support_cons, List.nodup_cons, List.mem_cons] at hnodup
          intro h
          exact hnodup.2.1 (h.symm ▸ Walk.end_mem_support rest')
        have hsep_walk : ∀ q : B.skeleton.Path v₁ v₂, ∃ z ∈ q.1.support, z ∈ ({u} : Set α) := by
          intro q
          have hqp : q = p := (hacyc.subsingleton_path v₁ v₂).elim q p
          refine ⟨u, ?_, Set.mem_singleton u⟩
          rw [hqp]
          simp [p]
        obtain ⟨B₁, B₂, hB, h₁, h₂, hordB⟩ :=
          exists_separation_of_vertex_separator hv₁.2 hv₂.2 (Set.singleton_subset_iff.2 huB)
            (Set.notMem_singleton_iff.2 hv₁u) (Set.notMem_singleton_iff.2 huv₂.symm) hsep_walk
        have hge2 := theorem_2_10_claim_1 h𝒯 hext hv₁ hv₂ hB h₁ h₂
        rw [hordB, Set.ncard_singleton] at hge2
        omega
  · have hsep_walk : ∀ q : B.skeleton.Path v₁ v₂, ∃ z ∈ q.1.support, z ∈ (∅ : Set α) :=
      fun q ↦ (hreach q.1.reachable).elim
    obtain ⟨B₁, B₂, hB, h₁, h₂, hordB⟩ :=
      exists_separation_of_vertex_separator hv₁.2 hv₂.2 (Set.empty_subset _)
        (Set.notMem_empty v₁) (Set.notMem_empty v₂) hsep_walk
    have hge2 := theorem_2_10_claim_1 h𝒯 hext hv₁ hv₂ hB h₁ h₂
    rw [hordB, Set.ncard_empty] at hge2
    omega

/-! ## Section 6: New Tangles from Old -/

/-! ### Truncations (Graph Minors X, Section 6, page 170) -/

private lemma bot_le (G : Hypergraph α β) : (⊥ : Hypergraph α β) ≤ G where
  vertexSet_subset := Set.empty_subset _
  edgeSet_subset := Set.empty_subset _
  ends_eq _ h := h.elim

private lemma isSeparation_bot_self (G : Hypergraph α β) : G.IsSeparation ⊥ G := by
  rw [isSeparation_iff_of_le (bot_le G) le_rfl]
  simp

private lemma bot_self_mem_tangle {G : Hypergraph α β} {θ : ℕ}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} (h𝒯 : IsTangle G θ 𝒯) :
    (⊥, G) ∈ 𝒯 := by
  have hsep := isSeparation_bot_self G
  have hord : separationOrder (⊥ : Hypergraph α β) G < θ := by
    have : ((⊥ : Hypergraph α β) ∩ G).vertexSet = ∅ := by simp
    rw [separationOrder, this, Set.ncard_empty]
    exact h𝒯.one_le
  exact (h𝒯.axiom1 hsep hord).resolve_right fun hGbot ↦ h𝒯.axiom3 hGbot rfl

/-- In a tangle `𝒯` of order `θ`, there exists a separation `(A, B)` of `G` of order `θ` such that
neither `(A, B)` nor `(B, A)` belongs to `𝒯`. -/
theorem IsTangle.exists_separation_order_eq {G : Hypergraph α β} {θ : ℕ}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} (h𝒯 : IsTangle G θ 𝒯) :
    ∃ A B : Hypergraph α β,
      G.IsSeparation A B ∧ separationOrder A B = θ ∧ (A, B) ∉ 𝒯 ∧ (B, A) ∉ 𝒯 := by
  obtain ⟨A, B, hext, _, _⟩ := h𝒯.exists_isExtreme (bot_self_mem_tangle h𝒯)
  have hAB := hext.1
  have hsep := h𝒯.isSeparation hAB
  have hord := theorem_2_8_order h𝒯 hext
  have hVA_ne := h𝒯.axiom3 hAB
  obtain ⟨v, hvG, hv_notA⟩ := Set.exists_of_ssubset
    (ssubset_of_subset_of_ne hsep.left_le.vertexSet_subset hVA_ne)
  have hvB : v ∈ B.vertexSet :=
    (hsep.vertexSet_union.symm ▸ hvG).resolve_left hv_notA
  let Kv : Hypergraph α β := vertexHypergraph v
  have hKv_le_G : Kv ≤ G := vertexHypergraph_le hvG
  have hsep' : G.IsSeparation (A ∪ Kv) B := by
    rw [isSeparation_iff_of_le (union_le hsep.left_le hKv_le_G) hsep.right_le]
    refine ⟨?_, ?_, ?_⟩
    · change (A.vertexSet ∪ {v}) ∪ B.vertexSet = G.vertexSet
      rw [Set.union_assoc, Set.singleton_union, Set.insert_eq_of_mem hvB, hsep.vertexSet_union]
    · simp [Kv, vertexHypergraph, hsep.edgeSet_union]
    · simpa [union_edgeSet, Kv, vertexHypergraph] using hsep.edgeSet_inter_eq
  have hAK_not : (A ∪ Kv, B) ∉ 𝒯 := by
    intro hm
    have hAK_eq := (hext.2 hm (le_union_left hsep.left_le hKv_le_G) le_rfl).1
    have hvA : v ∈ A.vertexSet := by
      rw [← hAK_eq]
      exact Or.inr (Set.mem_singleton v)
    exact hv_notA hvA
  have hBAK_not : (B, A ∪ Kv) ∉ 𝒯 := by
    intro hm
    apply h𝒯.axiom2 hAB hAB hm
    rw [union_self, hsep.union_eq]
  have hset_eq : ((A ∪ Kv) ∩ B).vertexSet = insert v (A ∩ B).vertexSet := by
    ext x
    simp only [inter_vertexSet, union_vertexSet, Kv, vertexHypergraph, Set.mem_inter_iff,
      Set.mem_union, Set.mem_singleton_iff, Set.mem_insert_iff]
    constructor
    · rintro ⟨hxA | rfl, hxB⟩
      · exact Or.inr ⟨hxA, hxB⟩
      · exact Or.inl rfl
    · rintro (rfl | ⟨hxA, hxB⟩)
      · exact ⟨Or.inr rfl, hvB⟩
      · exact ⟨Or.inl hxA, hxB⟩
  have hv_notAB : v ∉ (A ∩ B).vertexSet := fun h ↦ hv_notA h.1
  have hcard : separationOrder (A ∪ Kv) B = θ := by
    have h1 := h𝒯.one_le
    rw [separationOrder, hset_eq, Set.ncard_insert_of_notMem hv_notAB (A ∩ B).vertexSet_finite,
      ← separationOrder, hord]
    omega
  exact ⟨A ∪ Kv, B, hsep', hcard, hAK_not, hBAK_not⟩

/-- **Graph Minors X, Section 6** (page 170):
"We observe also that if $\mathscr{T}, \mathscr{T}'$ are tangles in $G$ then
$\mathscr{T}' \subseteq \mathscr{T}$ if and only if $\mathscr{T}'$ is a truncation of
$\mathscr{T}$." -/
theorem subset_iff_truncation {G : Hypergraph α β} {θ θ' : ℕ}
    {𝒯 𝒯' : Set (Hypergraph α β × Hypergraph α β)}
    (h𝒯 : IsTangle G θ 𝒯) (h𝒯' : IsTangle G θ' 𝒯') :
    𝒯' ⊆ 𝒯 ↔ θ' ≤ θ ∧ 𝒯' = truncation 𝒯 θ' := by
  constructor
  · intro hsub
    have hle : θ' ≤ θ := by
      by_contra! hlt
      obtain ⟨A, B, hsep, hord, hnotAB, hnotBA⟩ := h𝒯.exists_separation_order_eq
      rcases h𝒯'.axiom1 hsep (hord ▸ hlt) with hm | hm
      · exact hnotAB (hsub hm)
      · exact hnotBA (hsub hm)
    refine ⟨hle, Set.Subset.antisymm (fun p hp ↦ ⟨hsub hp, h𝒯'.order_lt hp⟩) ?_⟩
    rintro ⟨A, B⟩ ⟨hAB, hord⟩
    rcases h𝒯'.axiom1 (h𝒯.isSeparation hAB) hord with hm | hm
    · exact hm
    · exact (theorem_2_1_proof h𝒯 hAB (hsub hm)).elim
  · rintro ⟨_, rfl⟩ p hp
    exact hp.1

/-- Variant of `subset_iff_truncation` existentially quantifying the truncation order. -/
theorem subset_iff_exists_truncation {G : Hypergraph α β} {θ θ' : ℕ}
    {𝒯 𝒯' : Set (Hypergraph α β × Hypergraph α β)}
    (h𝒯 : IsTangle G θ 𝒯) (h𝒯' : IsTangle G θ' 𝒯') :
    𝒯' ⊆ 𝒯 ↔ ∃ θ'', 1 ≤ θ'' ∧ θ'' ≤ θ ∧ 𝒯' = truncation 𝒯 θ'' := by
  rw [subset_iff_truncation h𝒯 h𝒯']
  refine ⟨fun ⟨hle, heq⟩ ↦ ⟨θ', h𝒯'.one_le, hle, heq⟩, ?_⟩
  rintro ⟨θ'', _, _, rfl⟩
  rw [← subset_iff_truncation h𝒯 h𝒯']
  exact fun _ hp ↦ hp.1

/-! ### Induced Tangles in Minors: Graph Minors X, (6.1) (page 170) -/

@[simp]
private lemma ofGraph_vertexSet (G : Graph α β) (hV : V(G).Finite) (hE : E(G).Finite) :
    (Hypergraph.ofGraph G hV hE).vertexSet = V(G) := rfl

@[simp]
private lemma ofGraph_edgeSet (G : Graph α β) (hV : V(G).Finite) (hE : E(G).Finite) :
    (Hypergraph.ofGraph G hV hE).edgeSet = E(G) := rfl

@[simp]
private lemma ofGraph_inc (G : Graph α β) (hV : V(G).Finite) (hE : E(G).Finite) (e : β) (v : α) :
    (Hypergraph.ofGraph G hV hE).Inc e v ↔ G.Inc e v := Iff.rfl

/-- The component of `v` in `(V(G'), C)` used by `contract G' C` (the map `η` in the proof of
(6.1), page 170). -/
abbrev contractComp (G' : Graph α β) (C : Set β) (v : α) : Set α :=
  {w | ReflTransGen (fun x y ↦ ∃ e ∈ C, G'.IsLink e x y) v w}

private lemma mem_contractComp_self (G' : Graph α β) (C : Set β) (v : α) :
    v ∈ contractComp G' C v :=
  ReflTransGen.refl

private lemma contractComp_symm {G' : Graph α β} {C : Set β} {x y : α}
    (h : ReflTransGen (fun a b ↦ ∃ e ∈ C, G'.IsLink e a b) x y) :
    ReflTransGen (fun a b ↦ ∃ e ∈ C, G'.IsLink e a b) y x := by
  induction h with
  | refl => exact .refl
  | tail _ hstep ih =>
    rcases hstep with ⟨e, heC, hl⟩
    exact (ReflTransGen.single ⟨e, heC, hl.symm⟩).trans ih

private lemma contractComp_eq_of_rel {G' : Graph α β} {C : Set β} {x y : α}
    (h : ReflTransGen (fun a b ↦ ∃ e ∈ C, G'.IsLink e a b) x y) :
    contractComp G' C x = contractComp G' C y := by
  ext z
  exact ⟨fun hxz ↦ (contractComp_symm h).trans hxz, fun hyz ↦ h.trans hyz⟩

private lemma contractComp_subset_vertexSet {G' : Graph α β} {C : Set β} {x : α}
    (hx : x ∈ V(G')) : contractComp G' C x ⊆ V(G') := by
  intro y hy
  induction hy with
  | refl => exact hx
  | tail _ hstep _ =>
    rcases hstep with ⟨_, _, hl⟩
    exact hl.right_mem

private lemma vertexSet_contract_eq (G' : Graph α β) (C : Set β) :
    V(contract G' C) = contractComp G' C '' V(G') := by
  simp [contract, contractComp]

private lemma edgeSet_contract_eq (G' : Graph α β) (C : Set β) :
    E(contract G' C) = E(G') \ C := by
  simp [contract]

private lemma contract_isLink_iff (G' : Graph α β) (C : Set β) (e : β) (X Y : Set α) :
    (contract G' C).IsLink e X Y ↔
      e ∉ C ∧ ∃ x y, G'.IsLink e x y ∧ contractComp G' C x = X ∧ contractComp G' C y = Y := by
  simp only [contract, deleteEdges_isLink, map_isLink, Relation.Map, contractComp]
  exact and_comm

private lemma contract_inc_iff (G' : Graph α β) (C : Set β) (e : β) (X : Set α) :
    (contract G' C).Inc e X ↔
      e ∉ C ∧ ∃ x y, G'.IsLink e x y ∧ contractComp G' C x = X := by
  unfold Graph.Inc
  constructor
  · rintro ⟨Y, hl⟩
    rw [contract_isLink_iff] at hl
    rcases hl with ⟨heC, x, y, hl, rfl, rfl⟩
    exact ⟨heC, x, y, hl, rfl⟩
  · rintro ⟨heC, x, y, hl, rfl⟩
    refine ⟨contractComp G' C y, ?_⟩
    rw [contract_isLink_iff]
    exact ⟨heC, x, y, hl, rfl, rfl⟩

/-- The subhypergraph `A'` of `H = contract G' C` associated to a subhypergraph `A` of `G` in the
proof of **Graph Minors X, (6.1)** (page 170):
"First, let $(A, B)$ be a separation of $G$ of order $< \theta$. Then we may choose a separation
$(A', B')$ of $H$ such that $E(A') = E(A) \cap E(H)$, and every vertex of $V(A' \cap B')$ is
incident with an edge of $E(A')$ and with an edge of $E(B')$."
Concretely, we define the image of `A` in `H` to have vertex set
`{η(x) : x ∈ V(A ∩ G')} ∪ {v ∈ V(H) : v is incident in H with an edge in E(A) ∩ E(H)}`
and edge set `E(A) ∩ E(H)`. -/
@[expose] noncomputable def minorImageSubhypergraph (G' : Graph α β) (C : Set β)
    (hVH : V(contract G' C).Finite) (hEH : E(contract G' C).Finite)
    (A : Hypergraph α β) : Hypergraph (Set α) β where
  vertexSet :=
    contractComp G' C '' (A.vertexSet ∩ V(G')) ∪
      {v ∈ V(contract G' C) | ∃ e ∈ A.edgeSet ∩ E(contract G' C), (contract G' C).Inc e v}
  edgeSet := A.edgeSet ∩ E(contract G' C)
  Inc e v := e ∈ A.edgeSet ∩ E(contract G' C) ∧ (contract G' C).Inc e v
  vertex_mem_of_inc _ _ h := Or.inr ⟨h.2.vertex_mem, _, h.1, h.2⟩
  edge_mem_of_inc _ _ h := h.1
  vertexSet_finite := by
    refine hVH.subset ?_
    rintro v (⟨x, ⟨_, hxG'⟩, rfl⟩ | ⟨hvH, _⟩)
    · rw [vertexSet_contract_eq]
      exact ⟨x, hxG', rfl⟩
    · exact hvH
  edgeSet_finite := hEH.subset Set.inter_subset_right

private lemma minorImageSubhypergraph_vertexSet_eq {G G' : Graph α β} {C : Set β}
    (hG' : G' ≤ G) (hV : V(G).Finite) (hE : E(G).Finite)
    (hVH : V(contract G' C).Finite) (hEH : E(contract G' C).Finite)
    {A : Hypergraph α β} (hA : A ≤ Hypergraph.ofGraph G hV hE) :
    (minorImageSubhypergraph G' C hVH hEH A).vertexSet =
      contractComp G' C '' (A.vertexSet ∩ V(G')) := by
  refine Set.union_eq_left.2 ?_
  rintro v ⟨_, e, ⟨heA, _⟩, hincH⟩
  rw [contract_inc_iff] at hincH
  rcases hincH with ⟨_, x, y, hlG', rfl⟩
  have hlG : G.IsLink e x y := hlG'.mono hG'
  have hincG : (Hypergraph.ofGraph G hV hE).Inc e x := hlG.inc_left
  have hincA : A.Inc e x := (inc_iff_of_le hA heA).2 hincG
  exact ⟨x, ⟨A.vertex_mem_of_inc hincA, hlG'.left_mem⟩, rfl⟩

lemma minorImageSubhypergraph_le {G' : Graph α β} {C : Set β}
    (hVH : V(contract G' C).Finite) (hEH : E(contract G' C).Finite)
    (A : Hypergraph α β) :
    minorImageSubhypergraph G' C hVH hEH A ≤
      Hypergraph.ofGraph (contract G' C) hVH hEH where
  vertexSet_subset := by
    rintro v (⟨x, ⟨_, hxG'⟩, rfl⟩ | ⟨hvH, _⟩)
    · rw [ofGraph_vertexSet, vertexSet_contract_eq]
      exact ⟨x, hxG', rfl⟩
    · exact hvH
  edgeSet_subset := Set.inter_subset_right
  ends_eq e he := by
    ext v
    simp only [Hypergraph.ends, Set.mem_ofPred_eq, minorImageSubhypergraph, ofGraph_inc]
    exact ⟨fun h ↦ ⟨he, h⟩, fun h ↦ h.2⟩

lemma minorImageSubhypergraph_isSeparation {G G' : Graph α β} {C : Set β}
    (hG' : G' ≤ G) (hV : V(G).Finite) (hE : E(G).Finite)
    (hVH : V(contract G' C).Finite) (hEH : E(contract G' C).Finite)
    {A B : Hypergraph α β} (hsep : (Hypergraph.ofGraph G hV hE).IsSeparation A B) :
    (Hypergraph.ofGraph (contract G' C) hVH hEH).IsSeparation
      (minorImageSubhypergraph G' C hVH hEH A)
      (minorImageSubhypergraph G' C hVH hEH B) := by
  have hleA := minorImageSubhypergraph_le hVH hEH A
  have hleB := minorImageSubhypergraph_le hVH hEH B
  rw [isSeparation_iff_of_le hleA hleB]
  refine ⟨?_, ?_, ?_⟩
  · rw [minorImageSubhypergraph_vertexSet_eq hG' hV hE hVH hEH hsep.left_le,
      minorImageSubhypergraph_vertexSet_eq hG' hV hE hVH hEH hsep.right_le,
      ← Set.image_union, ← Set.union_inter_distrib_right, hsep.vertexSet_union,
      ofGraph_vertexSet, Set.inter_eq_right.2 hG'.vertexSet_mono,
      ofGraph_vertexSet, vertexSet_contract_eq]
  · change (A.edgeSet ∩ E(contract G' C)) ∪ (B.edgeSet ∩ E(contract G' C)) = E(contract G' C)
    have hEH_sub : E(contract G' C) ⊆ E(G) := by
      rw [edgeSet_contract_eq]
      exact Set.sdiff_subset.trans hG'.edgeSet_mono
    rw [← Set.union_inter_distrib_right, hsep.edgeSet_union, ofGraph_edgeSet,
      Set.inter_eq_right.2 hEH_sub]
  · ext e
    change e ∈ (A.edgeSet ∩ E(contract G' C)) ∩ (B.edgeSet ∩ E(contract G' C)) ↔ e ∈ (∅ : Set β)
    simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
    rintro ⟨⟨heA, _⟩, ⟨heB, _⟩⟩
    exact hsep.notMem_edgeSet_right heA heB

private lemma exists_mem_inter_of_contractComp_eq {G G' : Graph α β} {C : Set β}
    (hG' : G' ≤ G) (hV : V(G).Finite) (hE : E(G).Finite)
    {A B : Hypergraph α β} (hsep : (Hypergraph.ofGraph G hV hE).IsSeparation A B)
    {x y : α} (hxy : ReflTransGen (fun a b ↦ ∃ e ∈ C, G'.IsLink e a b) x y)
    (hxA : x ∈ A.vertexSet) (hxG' : x ∈ V(G')) (hyB : y ∈ B.vertexSet) :
    ∃ z ∈ (A ∩ B).vertexSet ∩ V(G'), contractComp G' C z = contractComp G' C x := by
  induction hxy with
  | refl =>
    exact ⟨x, ⟨⟨hxA, hyB⟩, hxG'⟩, rfl⟩
  | @tail a b hab hstep ih =>
    rcases hstep with ⟨e, heC, hlG'⟩
    have hlG : G.IsLink e a b := hlG'.mono hG'
    have heG : e ∈ (Hypergraph.ofGraph G hV hE).edgeSet := hlG.edge_mem
    have heAB : e ∈ A.edgeSet ∪ B.edgeSet := hsep.edgeSet_union.symm ▸ heG
    rcases heAB with heA | heB
    · have hincB_G : (Hypergraph.ofGraph G hV hE).Inc e b := hlG.inc_right
      have hincA : A.Inc e b := (inc_iff_of_le hsep.left_le heA).2 hincB_G
      have hbA : b ∈ A.vertexSet := A.vertex_mem_of_inc hincA
      have hrel_xb : ReflTransGen (fun u v ↦ ∃ e ∈ C, G'.IsLink e u v) x b :=
        hab.tail ⟨e, heC, hlG'⟩
      exact ⟨b, ⟨⟨hbA, hyB⟩, hlG'.right_mem⟩, (contractComp_eq_of_rel hrel_xb).symm⟩
    · have hincA_G : (Hypergraph.ofGraph G hV hE).Inc e a := hlG.inc_left
      have hincB : B.Inc e a := (inc_iff_of_le hsep.right_le heB).2 hincA_G
      exact ih (B.vertex_mem_of_inc hincB)

private lemma minorImageSubhypergraph_inter_vertexSet_subset {G G' : Graph α β} {C : Set β}
    (hG' : G' ≤ G) (hV : V(G).Finite) (hE : E(G).Finite)
    (hVH : V(contract G' C).Finite) (hEH : E(contract G' C).Finite)
    {A B : Hypergraph α β} (hsep : (Hypergraph.ofGraph G hV hE).IsSeparation A B) :
    (minorImageSubhypergraph G' C hVH hEH A ∩
      minorImageSubhypergraph G' C hVH hEH B).vertexSet ⊆
      contractComp G' C '' ((A ∩ B).vertexSet ∩ V(G')) := by
  intro v hv
  rw [inter_vertexSet,
    minorImageSubhypergraph_vertexSet_eq hG' hV hE hVH hEH hsep.left_le,
    minorImageSubhypergraph_vertexSet_eq hG' hV hE hVH hEH hsep.right_le] at hv
  rcases hv with ⟨⟨x, ⟨hxA, hxG'⟩, rfl⟩, ⟨y, ⟨hyB, _⟩, hyx⟩⟩
  have hxy : y ∈ contractComp G' C x := hyx ▸ mem_contractComp_self G' C y
  obtain ⟨z, hz, hz_eq⟩ := exists_mem_inter_of_contractComp_eq hG' hV hE hsep hxy hxA hxG' hyB
  exact ⟨z, hz, hz_eq⟩

lemma minorImageSubhypergraph_separationOrder_le {G G' : Graph α β} {C : Set β}
    (hG' : G' ≤ G) (hV : V(G).Finite) (hE : E(G).Finite)
    (hVH : V(contract G' C).Finite) (hEH : E(contract G' C).Finite)
    {A B : Hypergraph α β} (hsep : (Hypergraph.ofGraph G hV hE).IsSeparation A B) :
    separationOrder (minorImageSubhypergraph G' C hVH hEH A)
      (minorImageSubhypergraph G' C hVH hEH B) ≤ separationOrder A B := by
  have hsub := minorImageSubhypergraph_inter_vertexSet_subset hG' hV hE hVH hEH hsep
  have hfin1 : (contractComp G' C '' ((A ∩ B).vertexSet ∩ V(G'))).Finite :=
    ((A ∩ B).vertexSet_finite.inter_of_left _).image _
  have h1 : separationOrder (minorImageSubhypergraph G' C hVH hEH A)
      (minorImageSubhypergraph G' C hVH hEH B) ≤
      (contractComp G' C '' ((A ∩ B).vertexSet ∩ V(G'))).ncard :=
    Set.ncard_le_ncard hsub hfin1
  have h2 : (contractComp G' C '' ((A ∩ B).vertexSet ∩ V(G'))).ncard ≤
      ((A ∩ B).vertexSet ∩ V(G')).ncard :=
    Set.ncard_image_le ((A ∩ B).vertexSet_finite.inter_of_left _)
  have h3 : ((A ∩ B).vertexSet ∩ V(G')).ncard ≤ separationOrder A B :=
    Set.ncard_le_ncard Set.inter_subset_left (A ∩ B).vertexSet_finite
  exact (h1.trans h2).trans h3

/-- **Graph Minors X, (6.1)** (page 170):
"(6.1) *Let $H$ be a minor of a graph $G$, and let $\mathscr{T}'$ be a tangle in $H$ of order
$\theta \ge 2$. Let $\mathscr{T}$ be the set of all separations $(A, B)$ of $G$ of order $< \theta$
such that there exists $(A', B') \in \mathscr{T}'$ with $E(A') = E(A) \cap E(H)$. Then $\mathscr{T}$
is a tangle in $G$ of order $\theta$.*" -/
theorem theorem_6_1_proof {G : Graph α β} {H : Graph (Set α) β}
    (hV : V(G).Finite) (hE : E(G).Finite)
    (hVH : V(H).Finite) (hEH : E(H).Finite)
    (hminor : IsMinor H G) {θ : ℕ} (hθ : 2 ≤ θ)
    {𝒯' : Set (Hypergraph (Set α) β × Hypergraph (Set α) β)}
    (h𝒯' : IsTangle (Hypergraph.ofGraph H hVH hEH) θ 𝒯') :
    IsTangle (Hypergraph.ofGraph G hV hE) θ
      (inducedTangle (Hypergraph.ofGraph G hV hE) (Hypergraph.ofGraph H hVH hEH) 𝒯' θ) := by
  rcases hminor with ⟨G', hG', C, _, rfl⟩
  let G_hyp := Hypergraph.ofGraph G hV hE
  let H_hyp := Hypergraph.ofGraph (contract G' C) hVH hEH
  have hEH_sub : H_hyp.edgeSet ⊆ G_hyp.edgeSet := by
    change E(contract G' C) ⊆ E(G)
    rw [edgeSet_contract_eq]
    exact Set.sdiff_subset.trans hG'.edgeSet_mono
  refine ⟨by omega, fun _ _ h ↦ h.1, fun _ _ h ↦ h.2.1, ?_, ?_, ?_⟩
  · intro A B hsep hord
    let ηA := minorImageSubhypergraph G' C hVH hEH A
    let ηB := minorImageSubhypergraph G' C hVH hEH B
    have hsepH := minorImageSubhypergraph_isSeparation hG' hV hE hVH hEH hsep
    have hordH : separationOrder ηA ηB < θ :=
      (minorImageSubhypergraph_separationOrder_le hG' hV hE hVH hEH hsep).trans_lt hord
    rcases h𝒯'.axiom1 hsepH hordH with hm | hm
    · exact Or.inl ⟨hsep, hord, ⟨(ηA, ηB), hm, rfl⟩⟩
    · exact Or.inr ⟨hsep.symm, by rwa [separationOrder_comm], ⟨(ηB, ηA), hm, rfl⟩⟩
  · intro A₁ B₁ A₂ B₂ A₃ B₃ h₁ h₂ h₃ hU
    rcases h₁.2.2 with ⟨⟨A₁', B₁'⟩, hm₁, hE₁⟩
    rcases h₂.2.2 with ⟨⟨A₂', B₂'⟩, hm₂, hE₂⟩
    rcases h₃.2.2 with ⟨⟨A₃', B₃'⟩, hm₃, hE₃⟩
    dsimp only at hE₁ hE₂ hE₃
    apply theorem_2_3_proof h𝒯' hθ hm₁ hm₂ hm₃
    have hEU : (A₁ ∪ A₂ ∪ A₃).edgeSet = G_hyp.edgeSet := congrArg Hypergraph.edgeSet hU
    calc
      (A₁' ∪ A₂' ∪ A₃').edgeSet
        = (A₁.edgeSet ∩ H_hyp.edgeSet) ∪ (A₂.edgeSet ∩ H_hyp.edgeSet) ∪
            (A₃.edgeSet ∩ H_hyp.edgeSet) := by
          simp [hE₁, hE₂, hE₃, H_hyp]
      _ = (A₁ ∪ A₂ ∪ A₃).edgeSet ∩ H_hyp.edgeSet := by
          simp [Set.union_inter_distrib_right]
      _ = G_hyp.edgeSet ∩ H_hyp.edgeSet := by rw [hEU]
      _ = H_hyp.edgeSet := Set.inter_eq_right.2 hEH_sub
  · intro A B hAB hVA
    rcases hAB with ⟨hsep, hord, ⟨⟨A', B'⟩, hm', hEA'⟩⟩
    dsimp only at hsep hord hm' hEA'
    let ηA := minorImageSubhypergraph G' C hVH hEH A
    let ηB := minorImageSubhypergraph G' C hVH hEH B
    have hsepH := minorImageSubhypergraph_isSeparation hG' hV hE hVH hEH hsep
    have hordH : separationOrder ηA ηB < θ :=
      (minorImageSubhypergraph_separationOrder_le hG' hV hE hVH hEH hsep).trans_lt hord
    have hηA_mem : (ηA, ηB) ∈ 𝒯' :=
      theorem_2_9_proof h𝒯' hm' hsepH hordH (Or.inr (Or.inr ⟨hθ, hEA'.symm.subset⟩))
    have hVηA : ηA.vertexSet = H_hyp.vertexSet := by
      rw [minorImageSubhypergraph_vertexSet_eq hG' hV hE hVH hEH hsep.left_le,
        hVA, ofGraph_vertexSet, Set.inter_eq_right.2 hG'.vertexSet_mono,
        ← vertexSet_contract_eq]
      rfl
    exact h𝒯'.axiom3 hηA_mem hVηA

/-! ### Quotient Tangles `𝒯 / W`: Graph Minors X, (6.2) and (6.3) (page 171) -/

private lemma quotientVertices_le {G A : Hypergraph α β} (hA : A ≤ G) (W : Set α) :
    quotientVertices A W ≤ quotientVertices G W where
  vertexSet_subset := Set.sdiff_subset_sdiff hA.vertexSet_subset subset_rfl
  edgeSet_subset := hA.edgeSet_subset
  ends_eq e he := by
    ext v
    simp only [Hypergraph.ends, Set.mem_ofPred_eq, quotientVertices]
    rw [inc_iff_of_le hA he]

/-- If `(A, B)` is a separation of `G`, then `(A / W, B / W)` is a separation of `G / W`
(Graph Minors X, Section 6, page 171). -/
theorem IsSeparation.quotientVertices {G A B : Hypergraph α β}
    (hsep : G.IsSeparation A B) (W : Set α) :
    (GraphMinor.GM10.quotientVertices G W).IsSeparation
      (GraphMinor.GM10.quotientVertices A W)
      (GraphMinor.GM10.quotientVertices B W) := by
  rw [isSeparation_iff_of_le (quotientVertices_le hsep.left_le W)
    (quotientVertices_le hsep.right_le W)]
  refine ⟨?_, hsep.edgeSet_union, hsep.edgeSet_inter_eq⟩
  change (A.vertexSet \ W) ∪ (B.vertexSet \ W) = G.vertexSet \ W
  rw [← Set.union_sdiff_distrib, hsep.vertexSet_union]

/-- The separation order of `(A / W, B / W)` is `|V(A ∩ B) \ W|`. -/
theorem separationOrder_quotientVertices (A B : Hypergraph α β) (W : Set α) :
    separationOrder (quotientVertices A W) (quotientVertices B W) =
      ((A ∩ B).vertexSet \ W).ncard := by
  have : (quotientVertices A W ∩ quotientVertices B W).vertexSet = (A ∩ B).vertexSet \ W := by
    ext v
    simp only [inter_vertexSet, quotientVertices, Set.mem_inter_iff, Set.mem_sdiff]
    tauto
  rw [separationOrder, this]

/-- Lifting a subhypergraph `A'` of `G / W` to a subhypergraph of `G` by adding `W` to its vertex
set, as in the proofs of **Graph Minors X, (6.2) and (6.3)** (page 171). -/
def liftQuotientSubhypergraph (G : Hypergraph α β) (W : Set α) (hW : W ⊆ G.vertexSet)
    (A' : Hypergraph α β) (hA' : A' ≤ quotientVertices G W) : Hypergraph α β where
  vertexSet := A'.vertexSet ∪ W
  edgeSet := A'.edgeSet
  Inc e v := e ∈ A'.edgeSet ∧ G.Inc e v
  vertex_mem_of_inc e v h := by
    by_cases hvW : v ∈ W
    · exact Or.inr hvW
    · have hincGW : (quotientVertices G W).Inc e v := ⟨h.2, hvW⟩
      have hincA' : A'.Inc e v := (inc_iff_of_le hA' h.1).2 hincGW
      exact Or.inl (A'.vertex_mem_of_inc hincA')
  edge_mem_of_inc _ _ h := h.1
  vertexSet_finite := A'.vertexSet_finite.union (G.vertexSet_finite.subset hW)
  edgeSet_finite := A'.edgeSet_finite

private lemma liftQuotientSubhypergraph_le {G : Hypergraph α β} {W : Set α}
    (hW : W ⊆ G.vertexSet) {A' : Hypergraph α β} (hA' : A' ≤ quotientVertices G W) :
    liftQuotientSubhypergraph G W hW A' hA' ≤ G where
  vertexSet_subset :=
    Set.union_subset (hA'.vertexSet_subset.trans Set.sdiff_subset) hW
  edgeSet_subset := hA'.edgeSet_subset
  ends_eq e he := by
    ext v
    simp only [Hypergraph.ends, Set.mem_ofPred_eq, liftQuotientSubhypergraph]
    exact ⟨fun h ↦ ⟨he, h⟩, fun h ↦ h.2⟩

private lemma quotientVertices_liftQuotientSubhypergraph {G : Hypergraph α β} {W : Set α}
    (hW : W ⊆ G.vertexSet) {A' : Hypergraph α β} (hA' : A' ≤ quotientVertices G W) :
    quotientVertices (liftQuotientSubhypergraph G W hW A' hA') W = A' := by
  have hdisj : Disjoint A'.vertexSet W := by
    refine Set.disjoint_left.2 fun v hvA' hvW ↦ ?_
    exact (hA'.vertexSet_subset hvA').2 hvW
  have hV : (A'.vertexSet ∪ W) \ W = A'.vertexSet := by
    rw [Set.union_sdiff_cancel_right (Set.disjoint_iff.1 hdisj)]
  exact eq_of_le_of_vertexSet_eq_of_edgeSet_eq
    (quotientVertices_le (liftQuotientSubhypergraph_le hW hA') W) hA' hV rfl

private lemma eq_liftQuotientSubhypergraph_of_subset {G A : Hypergraph α β} {W : Set α}
    (hW : W ⊆ G.vertexSet) (hA : A ≤ G) (hWA : W ⊆ A.vertexSet) :
    A = liftQuotientSubhypergraph G W hW (quotientVertices A W) (quotientVertices_le hA W) := by
  refine eq_of_le_of_vertexSet_eq_of_edgeSet_eq hA
    (liftQuotientSubhypergraph_le hW (quotientVertices_le hA W)) ?_ rfl
  change A.vertexSet = (A.vertexSet \ W) ∪ W
  exact (Set.sdiff_union_of_subset hWA).symm

private lemma liftQuotientSubhypergraph_isSeparation {G : Hypergraph α β} {W : Set α}
    (hW : W ⊆ G.vertexSet) {A' B' : Hypergraph α β}
    (hsep' : (quotientVertices G W).IsSeparation A' B') :
    G.IsSeparation
      (liftQuotientSubhypergraph G W hW A' hsep'.left_le)
      (liftQuotientSubhypergraph G W hW B' hsep'.right_le) := by
  rw [isSeparation_iff_of_le (liftQuotientSubhypergraph_le hW hsep'.left_le)
    (liftQuotientSubhypergraph_le hW hsep'.right_le)]
  refine ⟨?_, hsep'.edgeSet_union, hsep'.edgeSet_inter_eq⟩
  change (A'.vertexSet ∪ W) ∪ (B'.vertexSet ∪ W) = G.vertexSet
  have h1 : (A'.vertexSet ∪ W) ∪ (B'.vertexSet ∪ W) = (A'.vertexSet ∪ B'.vertexSet) ∪ W := by
    ext v
    simp only [Set.mem_union]
    tauto
  rw [h1, hsep'.vertexSet_union]
  exact Set.sdiff_union_of_subset hW

private lemma liftQuotientSubhypergraph_separationOrder {G : Hypergraph α β} {W : Set α}
    (hW : W ⊆ G.vertexSet) {A' B' : Hypergraph α β}
    (hsep' : (quotientVertices G W).IsSeparation A' B') :
    separationOrder
      (liftQuotientSubhypergraph G W hW A' hsep'.left_le)
      (liftQuotientSubhypergraph G W hW B' hsep'.right_le) =
      separationOrder A' B' + W.ncard := by
  have h_inter :
      ((liftQuotientSubhypergraph G W hW A' hsep'.left_le) ∩
        (liftQuotientSubhypergraph G W hW B' hsep'.right_le)).vertexSet =
      (A' ∩ B').vertexSet ∪ W := by
    ext v
    simp only [inter_vertexSet, liftQuotientSubhypergraph, Set.mem_inter_iff, Set.mem_union]
    tauto
  have hdisj : Disjoint (A' ∩ B').vertexSet W := by
    refine Set.disjoint_left.2 fun v hv hvW ↦ ?_
    exact (hsep'.left_le.vertexSet_subset hv.1).2 hvW
  rw [separationOrder, h_inter,
    Set.ncard_union_eq hdisj (A' ∩ B').vertexSet_finite (G.vertexSet_finite.subset hW),
    separationOrder]

/-- **Graph Minors X, (6.2)** (page 171):
"(6.2) *Let $\mathscr{T}$ be a tangle of order $\theta$ in a hypergraph $G$, and let $W \subseteq
V(G)$ with $|W| < \theta$. Let $\mathscr{T}'$ be the set of all separations $(A', B')$ of $G/W$ such
that there exists $(A, B) \in \mathscr{T}$ with $W \subseteq V(A \cap B)$, $A/W = A'$, and $B/W =
B'$. Then $\mathscr{T}'$ is a tangle in $G/W$ of order $\theta - |W|$.*" -/
theorem theorem_6_2_proof {G : Hypergraph α β} {θ : ℕ}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} (h𝒯 : IsTangle G θ 𝒯)
    {W : Set α} (hW : W ⊆ G.vertexSet) (hW_lt : W.ncard < θ) :
    IsTangle (quotientVertices G W) (θ - W.ncard) (quotientTangle G 𝒯 W) where
  one_le := by omega
  isSeparation _ _ h := h.1
  order_lt A' B' h := by
    rcases h with ⟨_, ⟨A, B⟩, ⟨hAB, hW_sub, hAW, hBW⟩⟩
    dsimp only at hAB hW_sub hAW hBW
    subst hAW hBW
    have hord := h𝒯.order_lt hAB
    rw [separationOrder_quotientVertices,
      Set.ncard_sdiff hW_sub (G.vertexSet_finite.subset hW),
      ← separationOrder]
    omega
  axiom1 A' B' hsep' hord' := by
    let A := liftQuotientSubhypergraph G W hW A' hsep'.left_le
    let B := liftQuotientSubhypergraph G W hW B' hsep'.right_le
    have hsep := liftQuotientSubhypergraph_isSeparation hW hsep'
    have hord : separationOrder A B < θ := by
      rw [liftQuotientSubhypergraph_separationOrder hW hsep']
      omega
    have hW_AB : W ⊆ (A ∩ B).vertexSet :=
      Set.subset_inter Set.subset_union_right Set.subset_union_right
    have hW_BA : W ⊆ (B ∩ A).vertexSet :=
      Set.subset_inter Set.subset_union_right Set.subset_union_right
    have hAW : quotientVertices A W = A' :=
      quotientVertices_liftQuotientSubhypergraph hW hsep'.left_le
    have hBW : quotientVertices B W = B' :=
      quotientVertices_liftQuotientSubhypergraph hW hsep'.right_le
    rcases h𝒯.axiom1 hsep hord with hm | hm
    · exact Or.inl ⟨hsep', ⟨(A, B), hm, hW_AB, hAW, hBW⟩⟩
    · exact Or.inr ⟨hsep'.symm, ⟨(B, A), hm, hW_BA, hBW, hAW⟩⟩
  axiom2 A₁' B₁' A₂' B₂' A₃' B₃' h₁ h₂ h₃ hU' := by
    rcases h₁.2 with ⟨⟨A₁, B₁⟩, hm₁, hW₁, hA₁, hB₁⟩
    rcases h₂.2 with ⟨⟨A₂, B₂⟩, hm₂, hW₂, hA₂, hB₂⟩
    rcases h₃.2 with ⟨⟨A₃, B₃⟩, hm₃, hW₃, hA₃, hB₃⟩
    dsimp only at hm₁ hW₁ hA₁ hB₁ hm₂ hW₂ hA₂ hB₂ hm₃ hW₃ hA₃ hB₃
    subst hA₁ hB₁ hA₂ hB₂ hA₃ hB₃
    apply h𝒯.axiom2 hm₁ hm₂ hm₃
    have hU_le : A₁ ∪ A₂ ∪ A₃ ≤ G :=
      union_le (union_le (h𝒯.isSeparation hm₁).left_le (h𝒯.isSeparation hm₂).left_le)
        (h𝒯.isSeparation hm₃).left_le
    have hVU' : (A₁.vertexSet \ W) ∪ (A₂.vertexSet \ W) ∪ (A₃.vertexSet \ W) =
        G.vertexSet \ W := congrArg Hypergraph.vertexSet hU'
    have hEU' : A₁.edgeSet ∪ A₂.edgeSet ∪ A₃.edgeSet = G.edgeSet :=
      congrArg Hypergraph.edgeSet hU'
    refine eq_of_le_of_vertexSet_eq_of_edgeSet_eq hU_le le_rfl ?_ hEU'
    have hW_U : W ⊆ (A₁ ∪ A₂ ∪ A₃).vertexSet :=
      hW₁.trans (Set.inter_subset_left.trans
        (Set.subset_union_left.trans Set.subset_union_left))
    calc
      (A₁ ∪ A₂ ∪ A₃).vertexSet
        = ((A₁ ∪ A₂ ∪ A₃).vertexSet \ W) ∪ W := (Set.sdiff_union_of_subset hW_U).symm
      _ = ((A₁.vertexSet \ W) ∪ (A₂.vertexSet \ W) ∪ (A₃.vertexSet \ W)) ∪ W := by
          simp [Set.union_sdiff_distrib]
      _ = (G.vertexSet \ W) ∪ W := by rw [hVU']
      _ = G.vertexSet := Set.sdiff_union_of_subset hW
  axiom3 A' B' h hVA' := by
    rcases h.2 with ⟨⟨A, B⟩, hm, hW_AB, hAW, hBW⟩
    dsimp only at hm hW_AB hAW hBW
    subst hAW hBW
    apply h𝒯.axiom3 hm
    have hWA : W ⊆ A.vertexSet := hW_AB.trans Set.inter_subset_left
    have hVA'_eq : A.vertexSet \ W = G.vertexSet \ W := hVA'
    calc
      A.vertexSet = (A.vertexSet \ W) ∪ W := (Set.sdiff_union_of_subset hWA).symm
      _ = (G.vertexSet \ W) ∪ W := by rw [hVA'_eq]
      _ = G.vertexSet := Set.sdiff_union_of_subset hW

/-- **Graph Minors X, (6.3)** (page 171):
"(6.3) *Let $\mathscr{T}, \theta, G, W$ be as in (6.2), and let $(A, B)$ be a separation of $G$.
Then $(A/W, B/W) \in \mathscr{T}/W$ if and only if $(A, B) \in \mathscr{T}$ and
$|V(A \cap B) - W| < \theta - |W|$.*" -/
theorem theorem_6_3_proof {G : Hypergraph α β} {θ : ℕ}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} (h𝒯 : IsTangle G θ 𝒯)
    {W : Set α} (hW : W ⊆ G.vertexSet) (hW_lt : W.ncard < θ)
    {A B : Hypergraph α β} (hsep : G.IsSeparation A B) :
    (quotientVertices A W, quotientVertices B W) ∈ quotientTangle G 𝒯 W ↔
      (A, B) ∈ 𝒯 ∧ ((A ∩ B).vertexSet \ W).ncard < θ - W.ncard := by
  let A' := quotientVertices A W
  let B' := quotientVertices B W
  have hsep' : (quotientVertices G W).IsSeparation A' B' :=
    IsSeparation.quotientVertices hsep W
  let A₁ := liftQuotientSubhypergraph G W hW A' hsep'.left_le
  let B₁ := liftQuotientSubhypergraph G W hW B' hsep'.right_le
  have hsep₁ : G.IsSeparation A₁ B₁ := liftQuotientSubhypergraph_isSeparation hW hsep'
  have hord₁ : separationOrder A₁ B₁ = ((A ∩ B).vertexSet \ W).ncard + W.ncard := by
    rw [liftQuotientSubhypergraph_separationOrder hW hsep',
      separationOrder_quotientVertices]
  have hVA_sub : A.vertexSet ⊆ A₁.vertexSet := by
    intro v hv
    change v ∈ (A.vertexSet \ W) ∪ W
    by_cases hvW : v ∈ W
    · exact Or.inr hvW
    · exact Or.inl ⟨hv, hvW⟩
  have hVB_sub : B.vertexSet ⊆ B₁.vertexSet := by
    intro v hv
    change v ∈ (B.vertexSet \ W) ∪ W
    by_cases hvW : v ∈ W
    · exact Or.inr hvW
    · exact Or.inl ⟨hv, hvW⟩
  have hord_le : separationOrder A B ≤ separationOrder A₁ B₁ :=
    Set.ncard_le_ncard (Set.inter_subset_inter hVA_sub hVB_sub) (A₁ ∩ B₁).vertexSet_finite
  constructor
  · rintro ⟨_, ⟨A₂, B₂⟩, hm₂, hW₂, hA₂, hB₂⟩
    dsimp only at hm₂ hW₂ hA₂ hB₂
    have hsep₂ := h𝒯.isSeparation hm₂
    have hA₂_eq : A₂ = A₁ := by
      have := eq_liftQuotientSubhypergraph_of_subset hW hsep₂.left_le
        (hW₂.trans Set.inter_subset_left)
      simpa [A₁, A', hA₂] using this
    have hB₂_eq : B₂ = B₁ := by
      have := eq_liftQuotientSubhypergraph_of_subset hW hsep₂.right_le
        (hW₂.trans Set.inter_subset_right)
      simpa [B₁, B', hB₂] using this
    have hm₁ : (A₁, B₁) ∈ 𝒯 := hA₂_eq ▸ hB₂_eq ▸ hm₂
    have hlt₁ : separationOrder A₁ B₁ < θ := h𝒯.order_lt hm₁
    have hordAB : separationOrder A B < θ := hord_le.trans_lt hlt₁
    have hmAB : (A, B) ∈ 𝒯 :=
      theorem_2_9_proof h𝒯 hm₁ hsep hordAB (Or.inr (Or.inl hVA_sub))
    exact ⟨hmAB, by omega⟩
  · rintro ⟨hmAB, hlt⟩
    have hlt₁ : separationOrder A₁ B₁ < θ := by omega
    have hm₁ : (A₁, B₁) ∈ 𝒯 :=
      theorem_2_9_proof h𝒯 hmAB hsep₁ hlt₁ (Or.inl hVB_sub)
    refine ⟨hsep', ⟨(A₁, B₁), hm₁,
      Set.subset_inter Set.subset_union_right Set.subset_union_right,
      quotientVertices_liftQuotientSubhypergraph hW hsep'.left_le,
      quotientVertices_liftQuotientSubhypergraph hW hsep'.right_le⟩⟩

end GraphMinor.GM10
