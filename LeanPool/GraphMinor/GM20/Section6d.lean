/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM20.Section6c
public import Mathlib.Data.Nat.Nth

/-!
# Graph Minors XX, Section 6, (6.3)

Using an edge-based tie-breaker, (6.2) turns the hypothesis of (6.3) into the hypothesis of (5.7).
If
some `Gᵢ` has no edges there is no such tie-breaker, and the paper notes that two such patchworks
are
compared by their numbers of vertices, which `simulated_of_edgeless` does.
-/

@[expose] public section

namespace GraphMinor.GM20

open Set GraphMinor.GM18 GraphMinor.GM10 Hypergraph GraphMinor.GM04

universe u v

variable {α : Type u} {β : Type v}

/-- A rootless edgeless patchwork is simulated in one with at least as many vertices. -/
theorem simulated_of_edgeless {Ω : Type*} [Preorder Ω] {P Q : Patchwork Ω α β}
    (hP : IsRootless P) (hQ : IsRootless Q) (hPe : P.G.edgeSet = ∅) (hQe : Q.G.edgeSet = ∅)
    (hcard : P.G.vertexSet.ncard ≤ Q.G.vertexSet.ncard) : Simulated P Q := by
  classical
  have hf₁ : Fintype P.G.vertexSet := P.G.vertexSet_finite.fintype
  have hf₂ : Fintype Q.G.vertexSet := Q.G.vertexSet_finite.fintype
  have hc : Fintype.card P.G.vertexSet ≤ Fintype.card Q.G.vertexSet := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq,
      Nat.card_coe_set_eq]
    exact hcard
  obtain ⟨g⟩ := Function.Embedding.nonempty_of_card_le hc
  let ηv : α → Set α := fun v ↦ if h : v ∈ P.G.vertexSet then {(g ⟨v, h⟩).1} else ∅
  have hη : ∀ {v} (h : v ∈ P.G.vertexSet), ηv v = {(g ⟨v, h⟩).1} := fun h ↦ dite_eq_left h
  have hroots : ∀ {R : Patchwork Ω α β}, IsRootless R → R.G.roots = [] := by
    intro R hR
    refine List.eq_nil_iff_forall_not_mem.mpr fun x hx ↦ ?_
    have : x ∈ R.G.rootSet := hx
    rw [show R.G.rootSet = ∅ from hR] at this
    exact this
  have hdom : ∀ {e}, e ∉ P.dom := fun {e} h ↦ by
    have := P.dom_subset h
    rw [hPe] at this
    exact this
  have hnot : ∀ {e}, e ∉ P.G.edgeSet := fun {e} h ↦ by
    rw [hPe] at h
    exact h
  have hexp : IsExpansion P Q ηv id :=
    { vertex_nonempty := fun v hv ↦ by rw [hη hv]; exact singleton_nonempty _
      vertex_subset := fun v hv ↦ by
        rw [hη hv]
        exact singleton_subset_iff.mpr (g ⟨v, hv⟩).2
      edge_mem := fun e he ↦ absurd he hnot
      vertex_disjoint := fun v₁ h₁ v₂ h₂ hne ↦ by
        rw [hη h₁, hη h₂, Set.disjoint_singleton]
        intro h
        exact hne (congrArg Subtype.val (g.injective (Subtype.ext h)))
      edge_injOn := fun e he ↦ absurd he hnot
      mem_dom_iff := fun e he ↦ absurd he hnot
      ends_nonempty := fun e he ↦ absurd he hnot
      μ_length := fun e he ↦ absurd he hdom
      μ_mem := fun e he ↦ absurd he hdom
      roots_length := by rw [hroots hP, hroots hQ]
      roots_mem := fun i hi ↦ absurd hi (by rw [hroots hP]; simp)
      maps_Δ := fun e he ↦ absurd he hdom
      φ_le := fun e he ↦ absurd he hnot }
  refine ⟨ηv, id, hexp, emptySubgraph Q.G.vertexSet, ?_, fun v hv ↦ ?_⟩
  · have hrem : (Q.deleteEdges (id '' P.G.edgeSet)).IsRemovable := fun e he ↦ by
      have h₁ : e ∈ Q.G.edgeSet := he.1
      rw [hQe] at h₁
      exact h₁.elim
    exact hrem.emptySubgraph_isRealization
  · rw [hη hv]
    have hgv := (g ⟨v, hv⟩).2
    exact (exists_isComponent_verts_eq_iff (singleton_nonempty _)
      (singleton_subset_iff.mpr hgv)).mpr ⟨fun a _ b hab ↦ (not_emptySubgraph_adj hab).elim,
        fun a ha b hb ↦ by
          rw [mem_singleton_iff.mp ha, mem_singleton_iff.mp hb]
          exact sameComponent_iff.mpr ⟨hgv, hgv, SimpleGraph.Reachable.refl _⟩⟩

variable {G : RootedHypergraph α β} {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {W : Set α}
  {ℒ : Set (RootedHypergraph α β)}

theorem quotientTangle_mono {𝒯₁ 𝒯₂ : Set (Hypergraph α β × Hypergraph α β)} (h : 𝒯₁ ⊆ 𝒯₂)
    (G : Hypergraph α β) (W : Set α) : quotientTangle G 𝒯₁ W ⊆ quotientTangle G 𝒯₂ W := by
  rintro p ⟨h₁, q, hq, h₂⟩
  exact ⟨h₁, q, h hq, h₂⟩

theorem rootSet_ncard_le_order {A : RootedHypergraph α β} (hc : IsComplemented G A) :
    A.rootSet.ncard ≤ separationOrder A.toHypergraph (complementHypergraph G A) := by
  refine Set.ncard_le_ncard (fun v hv ↦ ?_) (A.toHypergraph ∩ _).vertexSet_finite
  exact ⟨A.roots_subset v hv, Or.inr ⟨hc.le.vertexSet_subset (A.roots_subset v hv), hv⟩⟩

/-- If `ℒ/W` is linked to the truncation of `𝒯` to order `θ` then the order of `ℒ` is `< θ` and
`ℒ/W` is linked to `𝒯/W`. -/
theorem linked_truncation {θ₀ θ : ℕ} (h𝒯 : IsTangle G.toHypergraph θ₀ (truncation 𝒯 θ))
    (hloc : IsRootedLocation G ℒ) (hW : ∀ A ∈ ℒ, W ⊆ A.rootSet)
    (hlink : IsLinkedTo (G.slash W) (quotientTangle G.toHypergraph (truncation 𝒯 θ) W)
      (locationSlash ℒ W)) :
    (∀ A ∈ ℒ, A.rootSet.ncard < θ) ∧
      IsLinkedTo (G.slash W) (quotientTangle G.toHypergraph 𝒯 W) (locationSlash ℒ W) := by
  have hsub : truncation 𝒯 θ ⊆ 𝒯 := fun _ h ↦ h.1
  have hord : ∀ A ∈ ℒ, A.rootSet.ncard < θ := fun A hA ↦
    (rootSet_ncard_le_order (hloc.isComplemented hA)).trans_lt
      (linked_mem h𝒯 hloc hW hlink hA).2
  refine ⟨hord, (hlink.1.trans (quotientTangle_mono hsub _ _)), ?_⟩
  rintro _ ⟨A, hA, rfl⟩ A' B' ⟨hsep, p, hp, hWp, h₁, h₂⟩ h₃ h₄
  by_cases hlt : separationOrder p.1 p.2 < θ
  · exact hlink.2 ⟨A, hA, rfl⟩ ⟨hsep, p, ⟨hp, hlt⟩, hWp, h₁, h₂⟩ h₃ h₄
  · simp only at h₁ h₂ hlt
    rw [← h₁, ← h₂, separationOrder_quotientVertices]
    have hfW : W.Finite := (p.1 ∩ p.2).vertexSet_finite.subset hWp
    have hroot : (A.slash W).rootSet = A.rootSet \ W := by
      ext v
      exact mem_slash_rootSet
    rw [hroot, Set.ncard_sdiff (hW A hA) hfW, Set.ncard_sdiff hWp hfW]
    have h₅ := hord A hA
    have h₆ : separationOrder p.1 p.2 = (p.1 ∩ p.2).vertexSet.ncard := rfl
    omega

/-- (6.3) when each `Gᵢ` has an edge. -/
theorem theorem_6_3_of_edges [Infinite β] {Ω : Type (max u v)} [Preorder Ω]
  (hΩ : WellQuasiOrderedLE Ω)
    {𝓕 : Set (UnlabeledPatchwork α β)} (h𝓕 : WellBehaved 𝓕) {θ : ℕ} (hθ : 1 ≤ θ)
    (P : ℕ → GM04.Patchwork Ω α β) (hP : ∀ i, IsRootless (P i) ∧ (P i).IsRobust)
    (hE : ∀ i, (P i).G.edgeSet.Nonempty)
    (h : ∀ i (θ' : ℕ) (𝒯 : Set (Hypergraph α β × Hypergraph α β)),
      IsTangle (P i).G.toHypergraph θ' 𝒯 → θ ≤ θ' → ∃ (W : Set α)
        (ℒ : Set (RootedHypergraph α β)), W ⊆ (P i).G.vertexSet ∧ W.ncard < θ ∧
        IsFine (P i).G ℒ ∧ IsRootedLocation (P i).G ℒ ∧ (∀ A ∈ ℒ, W ⊆ A.rootSet) ∧
        IsLinkedTo ((P i).G.slash W) (quotientTangle (P i).G.toHypergraph 𝒯 W)
          (locationSlash ℒ W) ∧
        ∃ Q ∈ 𝓕, HasPatchworkHeart ((P i).relabel fun _ ↦ ()) ℒ Q) :
    ∃ i j, i < j ∧ GM04.Simulated (P i) (P j) := by
  classical
  choose f hf using hE
  choose v hv using fun i ↦ exists_isIndependentWeight (P i).G.toHypergraph
  have hdef : ∀ i, IsDefinedBy (P i).G.toHypergraph (edgeBasedLam (P i).G.toHypergraph (f i) (v i))
      (f i) (v i) := fun i ↦ ⟨hf i, hv i, fun _ _ _ ↦ rfl⟩
  refine theorem_5_7_proof hΩ h𝓕 hθ P hP (fun _ ↦ ℝ ×ₗ ℝ ×ₗ ℝ)
    (fun i ↦ edgeBasedLam (P i).G.toHypergraph (f i) (v i))
    (fun i ↦ isTieBreaker_of_isDefinedBy (hdef i)) ?_
  intro i θ' 𝒯 h𝒯 hθ'
  have h𝒯₀ := h𝒯.truncation hθ hθ'
  obtain ⟨W, ℒ, hWV, hWθ, hfine, hloc, hWA, hlink, hheart⟩ := h i θ _ h𝒯₀ le_rfl
  obtain ⟨hord, hlink'⟩ := linked_truncation h𝒯₀ hloc hWA hlink
  refine ⟨Sum.inl '' W ∪ {Sum.inr (f i)}, ℒ, ?_, ?_, hfine,
    theorem_6_2_proof h𝒯 (hdef i) hloc hord hWA hlink', hheart⟩
  · rintro x (⟨y, hy, rfl⟩ | rfl)
    · exact Or.inl ⟨y, hWV hy, rfl⟩
    · exact Or.inr ⟨f i, hf i, rfl⟩
  · have hfin : W.Finite := (P i).G.vertexSet_finite.subset hWV
    have h₁ := Set.ncard_union_le (Sum.inl '' W : Set (α ⊕ β)) {Sum.inr (f i)}
    have h₂ := Set.ncard_image_le (f := (Sum.inl : α → α ⊕ β)) hfin
    rw [Set.ncard_singleton] at h₁
    omega

/-- Graph Minors XX, (6.3) (page 345): "Let $\Omega$ be a well-quasi-order, let $\mathcal{F}$ be a
well-behaved set of patchworks,
and let $\theta \ge 1$. Let $P_i = (G_i, \mu_i, \Delta_i, \phi_i)$ ($i = 1, 2, \ldots$) be a
countable sequence of rootless robust $\Omega$-patchworks. Suppose that for each tangle
$\mathcal{T}$ in $G_i$ of order $\ge \theta$, there exist $W \subseteq V(G_i)$ with $|W| <
\theta$ and a fine rooted location $\mathcal{L}$ in $G_i$, such that* - *$W \subseteq
\bar{\pi}(A)$ for all $A \in \mathcal{L}$,* - *$\mathcal{L}/W$ is linked to $\mathcal{T}/W$,
and* - *$\mathcal{F}$ contains a heart of $((G_i, \mu_i, \Delta_i), \mathcal{L})$.* *Then
there exist $j > i \ge 1$ such that $P_i$ is simulated in $P_j$."

Lean uses an infinite ambient edge type to provide fresh edge labels.
The simulation is the IV relation described in `WellBehaved`. -/
theorem theorem_6_3_proof [Infinite β] {Ω : Type (max u v)} [Preorder Ω] (hΩ : WellQuasiOrderedLE Ω)
    {𝓕 : Set (UnlabeledPatchwork α β)} (h𝓕 : WellBehaved 𝓕) {θ : ℕ} (hθ : 1 ≤ θ)
    (P : ℕ → GM04.Patchwork Ω α β) (hP : ∀ i, IsRootless (P i) ∧ (P i).IsRobust)
    (h : ∀ i (θ' : ℕ) (𝒯 : Set (Hypergraph α β × Hypergraph α β)),
      IsTangle (P i).G.toHypergraph θ' 𝒯 → θ ≤ θ' → ∃ (W : Set α)
        (ℒ : Set (RootedHypergraph α β)), W ⊆ (P i).G.vertexSet ∧ W.ncard < θ ∧
        IsFine (P i).G ℒ ∧ IsRootedLocation (P i).G ℒ ∧ (∀ A ∈ ℒ, W ⊆ A.rootSet) ∧
        IsLinkedTo ((P i).G.slash W) (quotientTangle (P i).G.toHypergraph 𝒯 W)
          (locationSlash ℒ W) ∧
        ∃ Q ∈ 𝓕, HasPatchworkHeart ((P i).relabel fun _ ↦ ()) ℒ Q) :
    ∃ i j, i < j ∧ GM04.Simulated (P i) (P j) := by
  by_cases hS : {i | (P i).G.edgeSet = ∅}.Infinite
  · -- Two of the edgeless patchworks compare by their numbers of vertices.
    let e := Nat.nth (· ∈ {i | (P i).G.edgeSet = ∅})
    have he : StrictMono e := Nat.nth_strictMono hS
    have hmem : ∀ k, (P (e k)).G.edgeSet = ∅ := fun k ↦ Nat.nth_mem_of_infinite hS k
    have hw : WellQuasiOrderedLE ℕ := inferInstance
    obtain ⟨k, l, hkl, hc⟩ := hw.wqo fun k ↦ (P (e k)).G.vertexSet.ncard
    exact ⟨e k, e l, he hkl, simulated_of_edgeless (hP _).1 (hP _).1 (hmem k) (hmem l) hc⟩
  · have hfin : {i | (P i).G.edgeSet = ∅}.Finite := Set.not_infinite.mp hS
    obtain ⟨N, hN⟩ := hfin.bddAbove
    obtain ⟨i, j, hij, hsim⟩ := theorem_6_3_of_edges hΩ h𝓕 hθ (fun i ↦ P (i + N + 1))
      (fun i ↦ hP _) (fun i ↦ by
        by_contra hn
        have h₁ := hN (Set.not_nonempty_iff_eq_empty.mp hn)
        omega) (fun i ↦ h _)
    exact ⟨i + N + 1, j + N + 1, by omega, hsim⟩

end GraphMinor.GM20
