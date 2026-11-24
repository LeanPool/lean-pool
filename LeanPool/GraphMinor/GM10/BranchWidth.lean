/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM10.TangleLemmas
public import LeanPool.GraphMinor.GM10.Submodular

/-!
# Branch-Width and Tangles: Graph Minors X, Section 4

This file formalizes Section 4 of Robertson and Seymour,
*Graph Minors. X. Obstructions to tree-decomposition*, J. Combin. Theory Ser. B 52 (1991) 153–190
(pages 164–167):
- Basic properties of `maxEdgeSize` (`γ(G)`), `branchEdgeOrder`, `branchDecompWidth`, and
  `branchWidth` (`β(G)`).
- The edge-boundary connectivity function `κ(X) = |∂(X)| - k` on `E(G)` and the singleton edge
  family `𝒜 = {{e} : e ∈ E(G)}`.
- **(4.3)** (`theorem_4_3`, with claims `theorem_4_3_claim_1`, `theorem_4_3_claim_2`,
  `theorem_4_3_claim_3`): `max(β(G), γ(G)) = θ(G)` unless `γ(G) = 0` and `V(G) ≠ ∅`.
- **(4.4)** (`theorem_4_4`): For `n ≥ 0`, `K_n` has tangle number `⌈(2/3)n⌉`, and for `n ≥ 3`, it
  has branch-width `⌈(2/3)n⌉`.
- **(4.5)** (`theorem_4_5`, with claims `theorem_4_5_claim_3` and `theorem_4_5_claim_4`):
  Weakening of the second tangle axiom for `θ ≥ 2`.
-/

public section

namespace GraphMinor.GM10

open SimpleGraph Hypergraph

variable {α β ι : Type*}

/-! ## Basic properties of `maxEdgeSize` and `branchWidth` -/

/-- The set of ends of an edge `e` in `G` is finite. -/
theorem ends_finite (G : Hypergraph α β) (e : β) : (G.ends e).Finite :=
  G.vertexSet_finite.subset fun _ h ↦ G.vertex_mem_of_inc h

/-- Every edge `e ∈ E(G)` has size at most `maxEdgeSize G` (`γ(G)`). -/
theorem edgeSize_le_maxEdgeSize {G : Hypergraph α β} {e : β} (he : e ∈ G.edgeSet) :
    edgeSize G e ≤ maxEdgeSize G :=
  le_csSup ((G.edgeSet_finite.image (edgeSize G)).bddAbove) ⟨e, he, rfl⟩

/-- `maxEdgeSize G ≤ k` if and only if every edge `e ∈ E(G)` has `edgeSize G e ≤ k`. -/
theorem maxEdgeSize_le_iff {G : Hypergraph α β} {k : ℕ} :
    maxEdgeSize G ≤ k ↔ ∀ e ∈ G.edgeSet, edgeSize G e ≤ k := by
  constructor
  · intro hk e he
    exact (edgeSize_le_maxEdgeSize he).trans hk
  · intro h
    by_cases hE : G.edgeSet.Nonempty
    · refine csSup_le (hE.image _) ?_
      rintro _ ⟨e, he, rfl⟩
      exact h e he
    · rw [Set.not_nonempty_iff_eq_empty] at hE
      simp [maxEdgeSize, hE]

/-- `maxEdgeSize G = 0` if and only if no edge of `G` is incident with any vertex. -/
theorem maxEdgeSize_eq_zero_iff {G : Hypergraph α β} :
    maxEdgeSize G = 0 ↔ ∀ e ∈ G.edgeSet, ∀ v, ¬ G.Inc e v := by
  rw [← Nat.le_zero, maxEdgeSize_le_iff]
  refine forall₂_congr fun e _ ↦ ?_
  rw [Nat.le_zero, edgeSize, Set.ncard_eq_zero (ends_finite G e), Set.eq_empty_iff_forall_notMem]
  rfl

/-- If `1 ≤ maxEdgeSize G`, then `E(G)` and `V(G)` are both nonempty. -/
theorem nonempty_of_one_le_maxEdgeSize {G : Hypergraph α β} (hγ : 1 ≤ maxEdgeSize G) :
    G.edgeSet.Nonempty ∧ G.vertexSet.Nonempty := by
  have hnot0 : ¬ maxEdgeSize G = 0 := by omega
  rw [maxEdgeSize_eq_zero_iff] at hnot0
  push Not at hnot0
  obtain ⟨e, he, v, hinc⟩ := hnot0
  exact ⟨⟨e, he⟩, ⟨v, G.vertex_mem_of_inc hinc⟩⟩

/-- Every edge `e ∈ E(G)` has `edgeSize G e ≤ tangleNumber G` (from `(2.4)`). -/
theorem maxEdgeSize_le_tangleNumber (G : Hypergraph α β) :
    maxEdgeSize G ≤ tangleNumber G := by
  rw [maxEdgeSize_le_iff]
  intro e he
  by_cases hsize : 1 ≤ edgeSize G e
  · exact (theorem_2_4_proof hsize he le_rfl).le_tangleNumber
  · omega

/-- In a branch-decomposition `(T, τ)` of `G`, `|E(G)| = |leafSet T| ≥ 2`. -/
theorem IsBranchDecomposition.two_le_ncard_edgeSet [Fintype ι] {G : Hypergraph α β}
    {T : SimpleGraph ι} {τ : ι → β} (h : IsBranchDecomposition G T τ) :
    2 ≤ G.edgeSet.ncard := by
  have himg : τ '' leafSet T = G.edgeSet := h.bijOn.image_eq
  rw [← himg, h.bijOn.injOn.ncard_image]
  exact h.isTernaryTree.two_le_ncard_leafSet

/-- When `|E(G)| ≤ 1`, `G` has no branch-decompositions and `branchWidth G = 0`. -/
theorem branchWidth_eq_zero_of_ncard_edgeSet_le_one {G : Hypergraph α β}
    (h : G.edgeSet.ncard ≤ 1) : branchWidth G = 0 := by
  suffices {w : ℕ | ∃ (ι : Type) (_ : Fintype ι) (T : SimpleGraph ι) (τ : ι → β),
      IsBranchDecomposition G T τ ∧ branchDecompWidth G T τ = w} = ∅ by
    simp [branchWidth, this]
  ext w
  simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨ι, _, T, τ, hbd, _⟩
  have h2 := hbd.two_le_ncard_edgeSet
  omega

/-- Every edge `e ∈ E(T)` has `branchEdgeOrder G T τ e ≤ branchDecompWidth G T τ`. -/
theorem branchEdgeOrder_le_branchDecompWidth [Fintype ι] {G : Hypergraph α β}
    {T : SimpleGraph ι} {τ : ι → β} {e : Sym2 ι} (he : e ∈ T.edgeSet) :
    branchEdgeOrder G T τ e ≤ branchDecompWidth G T τ :=
  le_csSup (((Set.toFinite T.edgeSet).image (branchEdgeOrder G T τ)).bddAbove) ⟨e, he, rfl⟩

/-- `branchDecompWidth G T τ ≤ k` if and only if every edge `e ∈ E(T)` has
`branchEdgeOrder G T τ e ≤ k`. -/
theorem branchDecompWidth_le_iff [Fintype ι] {G : Hypergraph α β}
    {T : SimpleGraph ι} {τ : ι → β} {k : ℕ} :
    branchDecompWidth G T τ ≤ k ↔ ∀ e ∈ T.edgeSet, branchEdgeOrder G T τ e ≤ k := by
  constructor
  · intro hk e he
    exact (branchEdgeOrder_le_branchDecompWidth he).trans hk
  · intro h
    by_cases hE : T.edgeSet.Nonempty
    · refine csSup_le (hE.image _) ?_
      rintro _ ⟨e, he, rfl⟩
      exact h e he
    · rw [Set.not_nonempty_iff_eq_empty] at hE
      simp [branchDecompWidth, hE]

/-- If `γ(G) = 0`, then `β(G) = 0` (Graph Minors X, Section 4, proof of (4.3), page 165). -/
theorem branchWidth_eq_zero_of_maxEdgeSize_eq_zero {G : Hypergraph α β}
    (hγ : maxEdgeSize G = 0) : branchWidth G = 0 := by
  have hno_inc := maxEdgeSize_eq_zero_iff.1 hγ
  have hwidth_zero : ∀ (ι : Type) [Fintype ι] (T : SimpleGraph ι) (τ : ι → β),
      IsBranchDecomposition G T τ → branchDecompWidth G T τ = 0 := by
    intro ι _ T τ hbd
    rw [← Nat.le_zero, branchDecompWidth_le_iff]
    intro e _
    have hfinite : {v ∈ G.vertexSet | ∃ t₁ ∈ leafSet T, ∃ t₂ ∈ leafSet T,
        ¬ (T.deleteEdges {e}).Reachable t₁ t₂ ∧ G.Inc (τ t₁) v ∧ G.Inc (τ t₂) v}.Finite :=
      G.vertexSet_finite.subset fun _ hx ↦ hx.1
    rw [Nat.le_zero, branchEdgeOrder, Set.ncard_eq_zero hfinite,
      Set.eq_empty_iff_forall_notMem]
    rintro v ⟨_, t₁, ht₁, _, _, _, hinc₁, _⟩
    exact hno_inc (τ t₁) (hbd.bijOn.mapsTo ht₁) v hinc₁
  by_cases hS : {w : ℕ | ∃ (ι : Type) (_ : Fintype ι) (T : SimpleGraph ι) (τ : ι → β),
      IsBranchDecomposition G T τ ∧ branchDecompWidth G T τ = w}.Nonempty
  · obtain ⟨w, ι, _, T, τ, hbd, rfl⟩ := hS
    have hw0 : branchDecompWidth G T τ = 0 := hwidth_zero ι T τ hbd
    exact Nat.eq_zero_of_le_zero (hw0 ▸ Nat.sInf_le ⟨ι, inferInstance, T, τ, hbd, rfl⟩)
  · rw [Set.not_nonempty_iff_eq_empty] at hS
    simp [branchWidth, hS]

/-- If `γ(G) = 0`, then `G` has no tangle of order `≥ 2`, so `θ(G) ≤ 1`
(Graph Minors X, Section 4, proof of (4.3), page 165). -/
theorem tangleNumber_le_one_of_maxEdgeSize_eq_zero {G : Hypergraph α β}
    (hγ : maxEdgeSize G = 0) : tangleNumber G ≤ 1 := by
  have hno_inc := maxEdgeSize_eq_zero_iff.1 hγ
  by_contra! hgt
  have h2 : 2 ≤ tangleNumber G := hgt
  obtain ⟨𝒯, h𝒯⟩ := exists_isTangle_of_le_tangleNumber (by omega) h2
  have hsep_bot : G.IsSeparation ⊥ G := by
    rw [isSeparation_iff_of_le bot_le le_rfl]
    simp
  have hord_bot : separationOrder (⊥ : Hypergraph α β) G < 2 := by
    simp [separationOrder]
  have hbot_mem : (⊥, G) ∈ 𝒯 :=
    (h𝒯.axiom1 hsep_bot hord_bot).resolve_right fun hG ↦ h𝒯.axiom3 hG rfl
  obtain ⟨A, B, hext, _, _⟩ := h𝒯.exists_isExtreme hbot_mem
  have hAB := hext.1
  have hB_empty : B.edgeSet = ∅ := by
    ext e
    simp only [Set.mem_empty_iff_false, iff_false]
    intro heB
    have heG : e ∈ G.edgeSet := (h𝒯.isSeparation hAB).right_le.edgeSet_subset heB
    have hends : B.ends e ⊆ A.vertexSet := by
      rintro v hv
      have hincG : G.Inc e v := inc_of_le (h𝒯.isSeparation hAB).right_le hv
      exact (hno_inc e heG v hincG).elim
    exact theorem_2_8_no_edge_ends_subset h𝒯 hext heB hends
  have hA_eq : A.edgeSet = G.edgeSet := by
    have hunion := (h𝒯.isSeparation hAB).edgeSet_union
    rwa [hB_empty, Set.union_empty] at hunion
  have h3 : (A ∪ A ∪ A).edgeSet = G.edgeSet := by
    simp [union_edgeSet, hA_eq]
  exact theorem_2_3_proof h𝒯 (by omega) hAB hAB hAB h3

/-- If `γ(G) = 0` and `V(G) ≠ ∅`, then `θ(G) = 1`
(Graph Minors X, Section 4, proof of (4.3), page 165). -/
theorem tangleNumber_eq_one_of_maxEdgeSize_eq_zero {G : Hypergraph α β}
    (hγ : maxEdgeSize G = 0) (hV : G.vertexSet.Nonempty) :
    tangleNumber G = 1 := by
  have hle := tangleNumber_le_one_of_maxEdgeSize_eq_zero hγ
  obtain ⟨θ, 𝒯, h𝒯⟩ := (theorem_2_5_proof G).2 hV
  have hge : 1 ≤ tangleNumber G := h𝒯.one_le.trans h𝒯.le_tangleNumber
  omega

/-- `θ(G) = 0` if and only if `V(G) = ∅` (from `(2.5)`). -/
theorem tangleNumber_eq_zero_iff {G : Hypergraph α β} :
    tangleNumber G = 0 ↔ G.vertexSet = ∅ := by
  rw [← Set.not_nonempty_iff_eq_empty, ← theorem_2_5_proof]
  constructor
  · rintro h0 ⟨θ, 𝒯, h𝒯⟩
    have h1 := h𝒯.one_le
    have h2 := h𝒯.le_tangleNumber
    omega
  · intro hne
    by_contra! hpos
    obtain ⟨𝒯, h𝒯⟩ := exists_isTangle_of_le_tangleNumber le_rfl (Nat.one_le_iff_ne_zero.2 hpos)
    exact hne ⟨1, 𝒯, h𝒯⟩

/-! ## The edge-boundary connectivity function for (4.3) -/

/-- The vertex boundary `∂(X)` of an edge subset `X ⊆ E(G)`: vertices of `G` incident both with an
edge in `X` and with an edge in `E(G) \ X`
(Graph Minors X, Section 4, proof of (4.3), page 165). -/
@[expose] def branchEdgeBoundary (G : Hypergraph α β) (X : Set β) : Set α :=
  {v ∈ G.vertexSet | (∃ e ∈ X, G.Inc e v) ∧ (∃ e ∈ G.edgeSet \ X, G.Inc e v)}

/-- `κ₀(X) = |∂(X)|`, the number of vertices of `G` incident with both `X` and `E(G) \ X`
(Graph Minors X, Section 4, proof of (4.3), page 165). -/
@[expose] noncomputable def kappa0 (G : Hypergraph α β) (X : Set β) : ℤ :=
  ((branchEdgeBoundary G X).ncard : ℤ)

/-- `κ(X) = κ₀(X) - k` on `E(G)` (Graph Minors X, Section 4, proof of (4.3), page 165). -/
@[expose] noncomputable def edgeConnFunc (G : Hypergraph α β) (k : ℕ) (X : Set β) : ℤ :=
  kappa0 G X - (k : ℤ)

/-- `𝒜 = {{e} : e ∈ E(G)}` (Graph Minors X, Section 4, proof of (4.3), page 165). -/
@[expose] def singletonEdges (G : Hypergraph α β) : Set (Set β) :=
  (fun e : β ↦ ({e} : Set β)) '' G.edgeSet

theorem branchEdgeBoundary_finite (G : Hypergraph α β) (X : Set β) :
    (branchEdgeBoundary G X).Finite :=
  G.vertexSet_finite.subset fun _ h ↦ h.1

theorem branchEdgeBoundary_compl {G : Hypergraph α β} {X : Set β} (hX : X ⊆ G.edgeSet) :
    branchEdgeBoundary G (G.edgeSet \ X) = branchEdgeBoundary G X := by
  ext v
  simp only [branchEdgeBoundary, Set.mem_sep_iff, Set.sdiff_sdiff_right_self, Set.inter_eq_right.2
    hX]
  exact and_congr_right fun _ ↦ and_comm

theorem branchEdgeBoundary_empty (G : Hypergraph α β) :
    branchEdgeBoundary G ∅ = ∅ := by
  ext v
  simp [branchEdgeBoundary]

theorem branchEdgeBoundary_self (G : Hypergraph α β) :
    branchEdgeBoundary G G.edgeSet = ∅ := by
  ext v
  simp [branchEdgeBoundary]

/-- `edgeConnFunc G k` is a connectivity function on `G.edgeSet`
(Graph Minors X, Section 4, proof of (4.3), page 165). -/
theorem isConnectivityFunction_edgeConnFunc (G : Hypergraph α β) (k : ℕ) :
    IsConnectivityFunction G.edgeSet (edgeConnFunc G k) where
  compl_eq {X} hX := by
    simp only [edgeConnFunc, kappa0, branchEdgeBoundary_compl hX]
  submodular {X Y} _ _ := by
    have hsub_union :
        branchEdgeBoundary G (X ∪ Y) ⊆ branchEdgeBoundary G X ∪ branchEdgeBoundary G Y := by
      rintro v ⟨hv, ⟨e₁, he₁, hinc₁⟩, ⟨e₂, ⟨he₂G, he₂XY⟩, hinc₂⟩⟩
      rcases he₁ with he₁X | he₁Y
      · exact Or.inl ⟨hv, ⟨e₁, he₁X, hinc₁⟩, ⟨e₂, ⟨he₂G, fun h ↦ he₂XY (Or.inl h)⟩, hinc₂⟩⟩
      · exact Or.inr ⟨hv, ⟨e₁, he₁Y, hinc₁⟩, ⟨e₂, ⟨he₂G, fun h ↦ he₂XY (Or.inr h)⟩, hinc₂⟩⟩
    have hsub_inter :
        branchEdgeBoundary G (X ∩ Y) ⊆ branchEdgeBoundary G X ∪ branchEdgeBoundary G Y := by
      rintro v ⟨hv, ⟨e₁, ⟨he₁X, he₁Y⟩, hinc₁⟩, ⟨e₂, ⟨he₂G, he₂XY⟩, hinc₂⟩⟩
      by_cases he₂X : e₂ ∈ X
      · have he₂Y : e₂ ∉ Y := fun h ↦ he₂XY ⟨he₂X, h⟩
        exact Or.inr ⟨hv, ⟨e₁, he₁Y, hinc₁⟩, ⟨e₂, ⟨he₂G, he₂Y⟩, hinc₂⟩⟩
      · exact Or.inl ⟨hv, ⟨e₁, he₁X, hinc₁⟩, ⟨e₂, ⟨he₂G, he₂X⟩, hinc₂⟩⟩
    have hsub_both : branchEdgeBoundary G (X ∪ Y) ∩ branchEdgeBoundary G (X ∩ Y) ⊆
        branchEdgeBoundary G X ∩ branchEdgeBoundary G Y := by
      rintro v ⟨⟨hv, _, ⟨e₂, ⟨he₂G, he₂XY⟩, hinc₂⟩⟩, ⟨_, ⟨e₁, ⟨he₁X, he₁Y⟩, hinc₁⟩, _⟩⟩
      refine ⟨⟨hv, ⟨e₁, he₁X, hinc₁⟩, ⟨e₂, ⟨he₂G, fun h ↦ he₂XY (Or.inl h)⟩, hinc₂⟩⟩,
        ⟨hv, ⟨e₁, he₁Y, hinc₁⟩, ⟨e₂, ⟨he₂G, fun h ↦ he₂XY (Or.inr h)⟩, hinc₂⟩⟩⟩
    have h1 : (branchEdgeBoundary G (X ∪ Y) ∪ branchEdgeBoundary G (X ∩ Y)).ncard ≤
        (branchEdgeBoundary G X ∪ branchEdgeBoundary G Y).ncard :=
      Set.ncard_le_ncard (Set.union_subset hsub_union hsub_inter)
        ((branchEdgeBoundary_finite G X).union (branchEdgeBoundary_finite G Y))
    have h2 : (branchEdgeBoundary G (X ∪ Y) ∩ branchEdgeBoundary G (X ∩ Y)).ncard ≤
        (branchEdgeBoundary G X ∩ branchEdgeBoundary G Y).ncard :=
      Set.ncard_le_ncard hsub_both ((branchEdgeBoundary_finite G X).inter_of_left _)
    have heq1 :=
      Set.ncard_union_add_ncard_inter (branchEdgeBoundary G (X ∪ Y)) (branchEdgeBoundary G (X ∩ Y))
        (branchEdgeBoundary_finite G (X ∪ Y)) (branchEdgeBoundary_finite G (X ∩ Y))
    have heq2 := Set.ncard_union_add_ncard_inter (branchEdgeBoundary G X) (branchEdgeBoundary G Y)
      (branchEdgeBoundary_finite G X) (branchEdgeBoundary_finite G Y)
    dsimp [edgeConnFunc, kappa0]
    omega

/-- When `maxEdgeSize G ≤ k`, every singleton `{e}` (`e ∈ E(G)`) is efficient for `edgeConnFunc G k`
(Graph Minors X, Section 4, proof of (4.3), page 165). -/
theorem singletonEdges_isEfficient {G : Hypergraph α β} {k : ℕ} (hk : maxEdgeSize G ≤ k) :
    ∀ A ∈ singletonEdges G, IsEfficient G.edgeSet (edgeConnFunc G k) A := by
  rintro _ ⟨e, he, rfl⟩
  refine ⟨Set.singleton_subset_iff.2 he, ?_⟩
  have hsub : branchEdgeBoundary G {e} ⊆ G.ends e := by
    rintro v ⟨_, ⟨e', he', hinc⟩, _⟩
    rw [Set.mem_singleton_iff] at he'
    exact he' ▸ hinc
  have hle : (branchEdgeBoundary G {e}).ncard ≤ edgeSize G e :=
    Set.ncard_le_ncard hsub (ends_finite G e)
  have hle_k : edgeSize G e ≤ k := (edgeSize_le_maxEdgeSize he).trans hk
  dsimp [edgeConnFunc, kappa0]
  omega

/-- Canonical left subhypergraph for an edge subset `X ⊆ E(G)`, containing all isolated vertices of
`G`. -/
@[expose] def sepLeft (G : Hypergraph α β) (X : Set β) : Hypergraph α β where
  vertexSet := {v ∈ G.vertexSet | (∃ e ∈ X ∩ G.edgeSet, G.Inc e v) ∨ ∀ e ∈ G.edgeSet, ¬ G.Inc e v}
  edgeSet := X ∩ G.edgeSet
  Inc e v := e ∈ X ∧ G.Inc e v
  vertex_mem_of_inc e _ h :=
    ⟨G.vertex_mem_of_inc h.2, Or.inl ⟨e, ⟨h.1, G.edge_mem_of_inc h.2⟩, h.2⟩⟩
  edge_mem_of_inc _ _ h := ⟨h.1, G.edge_mem_of_inc h.2⟩
  vertexSet_finite := G.vertexSet_finite.subset fun _ h ↦ h.1
  edgeSet_finite := G.edgeSet_finite.subset Set.inter_subset_right

/-- Canonical right subhypergraph for an edge subset `X ⊆ E(G)`. -/
@[expose] def sepRight (G : Hypergraph α β) (X : Set β) : Hypergraph α β where
  vertexSet := {v ∈ G.vertexSet | ∃ e ∈ G.edgeSet \ X, G.Inc e v}
  edgeSet := G.edgeSet \ X
  Inc e v := e ∈ G.edgeSet \ X ∧ G.Inc e v
  vertex_mem_of_inc e _ h := ⟨G.vertex_mem_of_inc h.2, e, h.1, h.2⟩
  edge_mem_of_inc _ _ h := h.1
  vertexSet_finite := G.vertexSet_finite.subset fun _ h ↦ h.1
  edgeSet_finite := G.edgeSet_finite.subset Set.sdiff_subset

theorem sepLeft_le (G : Hypergraph α β) (X : Set β) : sepLeft G X ≤ G where
  vertexSet_subset _ h := h.1
  edgeSet_subset := Set.inter_subset_right
  ends_eq e he := by
    ext v
    simp [ends, sepLeft, he.1]

theorem sepRight_le (G : Hypergraph α β) (X : Set β) : sepRight G X ≤ G where
  vertexSet_subset _ h := h.1
  edgeSet_subset := Set.sdiff_subset
  ends_eq e he := by
    ext v
    simp [ends, sepRight, he.1, he.2]

theorem isSeparation_sepLeft_sepRight (G : Hypergraph α β) (X : Set β) :
    G.IsSeparation (sepLeft G X) (sepRight G X) := by
  rw [isSeparation_iff_of_le (sepLeft_le G X) (sepRight_le G X)]
  refine ⟨?_, ?_, ?_⟩
  · ext v
    simp only [sepLeft, sepRight, Set.mem_union, Set.mem_sep_iff]
    constructor
    · rintro (⟨hv, _⟩ | ⟨hv, _⟩) <;> exact hv
    · intro hv
      by_cases hex : ∃ e ∈ G.edgeSet, G.Inc e v
      · obtain ⟨e, heG, hinc⟩ := hex
        by_cases heX : e ∈ X
        · exact Or.inl ⟨hv, Or.inl ⟨e, ⟨heX, heG⟩, hinc⟩⟩
        · exact Or.inr ⟨hv, e, ⟨heG, heX⟩, hinc⟩
      · push Not at hex
        exact Or.inl ⟨hv, Or.inr hex⟩
  · ext e
    simp only [sepLeft, sepRight, Set.mem_union, Set.mem_inter_iff, Set.mem_sdiff]
    tauto
  · ext e
    change e ∈ (X ∩ G.edgeSet) ∩ (G.edgeSet \ X) ↔ e ∈ (∅ : Set β)
    simp only [Set.mem_inter_iff, Set.mem_sdiff, Set.mem_empty_iff_false, iff_false]
    tauto

theorem separationOrder_sepLeft_sepRight (G : Hypergraph α β) {X : Set β}
    (hX : X ⊆ G.edgeSet) :
    separationOrder (sepLeft G X) (sepRight G X) = (branchEdgeBoundary G X).ncard := by
  rw [separationOrder]
  congr 1
  ext v
  change v ∈ (sepLeft G X).vertexSet ∧ v ∈ (sepRight G X).vertexSet ↔ v ∈ branchEdgeBoundary G X
  simp only [sepLeft, sepRight, branchEdgeBoundary, Set.mem_sep_iff,
    Set.inter_eq_self_of_subset_left hX]
  constructor
  · rintro ⟨⟨hv, h1 | hiso⟩, ⟨_, e₂, he₂, hinc₂⟩⟩
    · exact ⟨hv, h1, e₂, he₂, hinc₂⟩
    · exact (hiso e₂ he₂.1 hinc₂).elim
  · rintro ⟨hv, h1, h2⟩
    exact ⟨⟨hv, Or.inl h1⟩, ⟨hv, h2⟩⟩

theorem branchEdgeBoundary_subset_of_isSeparation {G A B : Hypergraph α β}
    (hsep : G.IsSeparation A B) :
    branchEdgeBoundary G A.edgeSet ⊆ (A ∩ B).vertexSet := by
  rintro v ⟨_, ⟨e₁, he₁A, hinc₁⟩, ⟨e₂, ⟨he₂G, he₂notA⟩, hinc₂⟩⟩
  have he₂B : e₂ ∈ B.edgeSet :=
    (hsep.edgeSet_union.symm ▸ he₂G).resolve_left he₂notA
  have hvA : v ∈ A.vertexSet :=
    A.vertex_mem_of_inc ((inc_iff_of_le hsep.left_le he₁A).2 hinc₁)
  have hvB : v ∈ B.vertexSet :=
    B.vertex_mem_of_inc ((inc_iff_of_le hsep.right_le he₂B).2 hinc₂)
  exact ⟨hvA, hvB⟩

theorem isEfficient_edgeSet_of_isSeparation {G A B : Hypergraph α β} {k : ℕ}
    (hsep : G.IsSeparation A B) (hord : separationOrder A B < k + 1) :
    IsEfficient G.edgeSet (edgeConnFunc G k) A.edgeSet := by
  refine ⟨hsep.left_le.edgeSet_subset, ?_⟩
  have hle : (branchEdgeBoundary G A.edgeSet).ncard ≤ separationOrder A B :=
    Set.ncard_le_ncard (branchEdgeBoundary_subset_of_isSeparation hsep) (A ∩ B).vertexSet_finite
  dsimp [edgeConnFunc, kappa0]
  omega

/-! ## Proof of (4.3) -/

/-- Claim (1) in the proof of **Graph Minors X, (4.3)** (page 165):
When `1 ≤ γ(G) ≤ k`, there is a bias extending `𝒜 = {{e} : e ∈ E(G)}` for `κ(X) = |∂(X)| - k`
if and only if `G` has a tangle of order `k + 1`. -/
theorem theorem_4_3_claim_1 {G : Hypergraph α β} {k : ℕ}
    (hγ : 1 ≤ maxEdgeSize G) (hk : maxEdgeSize G ≤ k) :
    (∃ ℬ, BiasExtends G.edgeSet (edgeConnFunc G k) (singletonEdges G) ℬ) ↔
      ∃ 𝒯, IsTangle G (k + 1) 𝒯 := by
  constructor
  · rintro ⟨ℬ, hbias, hsub⟩
    let 𝒯 : Set (Hypergraph α β × Hypergraph α β) :=
      {p | G.IsSeparation p.1 p.2 ∧ separationOrder p.1 p.2 < k + 1 ∧ p.1.edgeSet ∈ ℬ}
    refine ⟨𝒯, (theorem_2_7_proof (𝒯 := 𝒯) (θ := k + 1) (by omega)
      (fun _ _ h ↦ h.1) (fun _ _ h ↦ h.2.1) ?_ ?_).2 ?_⟩
    · intro A B hsep hord
      have heffA : IsEfficient G.edgeSet (edgeConnFunc G k) A.edgeSet :=
        isEfficient_edgeSet_of_isSeparation hsep hord
      rcases hbias.mem_or_compl_mem heffA with hA | hcompl
      · exact Or.inl ⟨hsep, hord, hA⟩
      · have hB_eq : B.edgeSet = G.edgeSet \ A.edgeSet := by
          ext e
          simp only [Set.mem_sdiff]
          exact ⟨fun heB ↦ ⟨hsep.right_le.edgeSet_subset heB, hsep.notMem_edgeSet_left heB⟩,
            fun ⟨heG, henotA⟩ ↦ (hsep.edgeSet_union.symm ▸ heG).resolve_left henotA⟩
        rw [← hB_eq] at hcompl
        exact Or.inr ⟨hsep.symm, by rwa [separationOrder_comm], hcompl⟩
    · intro A₁ B₁ A₂ B₂ A₃ B₃ h1 h2 h3 hU
      have hE : A₁.edgeSet ∪ A₂.edgeSet ∪ A₃.edgeSet = G.edgeSet :=
        congrArg Hypergraph.edgeSet hU
      exact hbias.union_ne h1.2.2 h2.2.2 h3.2.2 hE
    · intro e he hsize
      refine ⟨isSeparation_edgeHypergraph_deleteEdges he, ?_, ?_⟩
      · rwa [separationOrder_edgeHypergraph_deleteEdges]
      · exact hsub ⟨e, he, rfl⟩
  · rintro ⟨𝒯, h𝒯⟩
    let ℬ : Set (Set β) := {X | ∃ A B, (A, B) ∈ 𝒯 ∧ A.edgeSet = X}
    refine ⟨ℬ, ⟨?_, ?_, ?_⟩, ?_⟩
    · rintro X ⟨A, B, hAB, rfl⟩
      exact isEfficient_edgeSet_of_isSeparation (h𝒯.isSeparation hAB) (h𝒯.order_lt hAB)
    · intro X hX
      have hsep := isSeparation_sepLeft_sepRight G X
      have hord : separationOrder (sepLeft G X) (sepRight G X) < k + 1 := by
        rw [separationOrder_sepLeft_sepRight G hX.1]
        have hle := hX.2
        dsimp [edgeConnFunc, kappa0] at hle
        omega
      rcases h𝒯.axiom1 hsep hord with h1 | h2
      · left
        exact ⟨sepLeft G X, sepRight G X, h1, Set.inter_eq_self_of_subset_left hX.1⟩
      · right
        exact ⟨sepRight G X, sepLeft G X, h2, rfl⟩
    · rintro X₁ X₂ X₃ ⟨A₁, B₁, h1, rfl⟩ ⟨A₂, B₂, h2, rfl⟩ ⟨A₃, B₃, h3, rfl⟩
      exact theorem_2_3_proof h𝒯 (by omega) h1 h2 h3
    · rintro _ ⟨e, he, rfl⟩
      have hsize : edgeSize G e < k + 1 := by
        have := (edgeSize_le_maxEdgeSize he).trans hk
        omega
      have hmem := (theorem_2_7_proof (by omega) (fun _ _ h ↦ h𝒯.isSeparation h)
        (fun _ _ h ↦ h𝒯.order_lt h) h𝒯.axiom1 h𝒯.axiom2).1 h𝒯 e he hsize
      exact ⟨edgeHypergraph G e, G.deleteEdges {e}, hmem, rfl⟩

/-- When `2 ≤ |E(G)|` and all `singletonEdges G` are efficient for `edgeConnFunc G k`, any exact
tree-labelling over `singletonEdges G` yields a branch-decomposition of `G` of width `≤ k`
(Graph Minors X, Section 4, proof of (4.3), page 166). -/
theorem exists_branchDecomposition_of_exactTreeLabelling_of_isEfficient [Fintype ι]
    {G : Hypergraph α β} {k : ℕ}
    (h𝒜 : ∀ A ∈ singletonEdges G, IsEfficient G.edgeSet (edgeConnFunc G k) A)
    (hcard : 2 ≤ G.edgeSet.ncard) {T : SimpleGraph ι} {α : ι → Sym2 ι → Set β}
    (hα : IsExactTreeLabelling G.edgeSet (edgeConnFunc G k) (singletonEdges G) T α) :
    ∃ (ι' : Type) (_ : Fintype ι') (T' : SimpleGraph ι') (τ : ι' → β),
      IsBranchDecomposition G T' τ ∧ branchDecompWidth G T' τ ≤ k := by
  classical
  have hE_ne_empty : G.edgeSet ≠ ∅ := by
    intro h
    have : G.edgeSet.ncard = 0 := by simp [h]
    omega
  have hE_not_mem : G.edgeSet ∉ singletonEdges G := by
    rintro ⟨e, _, heq⟩
    have : G.edgeSet.ncard = 1 := by rw [← heq, Set.ncard_singleton]
    omega
  rcases theorem_3_6_proof h𝒜 hα with h1 | h2 | ⟨ι', _, T', α', hα', hneE⟩
  · exact (hE_ne_empty h1).elim
  · exact (hE_not_mem h2).elim
  · have hT' := hα'.isTreeLabelling.isTernaryTree
    have hleaf_singleton : ∀ v ∈ leafSet T', ∃ f ∈ G.edgeSet,
        ∀ e, IsTreeIncidence T' v e → G.edgeSet \ α' v e = {f} := by
      intro v hv
      obtain ⟨w, hadj, hw_uniq⟩ := hT'.exists_adj_of_isLeaf hv
      have hinc : IsTreeIncidence T' v s(v, w) := isTreeIncidence_iff_adj.2 hadj
      rcases hα'.isTreeLabelling.leaf_eq_or_union_eq hinc hv with heq | ⟨A, ⟨f, hf, rfl⟩, hunion⟩
      · exact (hneE v s(v, w) hinc hv heq).elim
      · refine ⟨f, hf, fun e he ↦ ?_⟩
        obtain ⟨w', hadj', rfl⟩ := isTreeIncidence_iff_exists_adj.1 he
        have hw' : w' = w := hw_uniq w' hadj'
        rw [hw']
        have hnot_mem : f ∉ α' v s(v, w) := by
          intro hf_in
          apply hneE v s(v, w) hinc hv
          rw [← hunion, Set.union_eq_left.2 (Set.singleton_subset_iff.2 hf_in)]
        ext x
        simp only [Set.mem_sdiff, Set.mem_singleton_iff]
        constructor
        · rintro ⟨hxE, hx_not⟩
          have hx_u : x ∈ α' v s(v, w) ∪ {f} := hunion.symm ▸ hxE
          exact Set.mem_singleton_iff.1 (hx_u.resolve_left hx_not)
        · rintro rfl
          exact ⟨hf, hnot_mem⟩
    obtain ⟨e_def, _⟩ : G.edgeSet.Nonempty := Set.nonempty_iff_ne_empty.2 hE_ne_empty
    let τ (v : ι') : β :=
      if hv : v ∈ leafSet T' then (hleaf_singleton v hv).choose else e_def
    have hτ_mem : ∀ v ∈ leafSet T', τ v ∈ G.edgeSet := by
      intro v hv
      simp only [τ, hv, ↓reduceDIte]
      exact (hleaf_singleton v hv).choose_spec.1
    have hτ_compl : ∀ v ∈ leafSet T', ∀ e, IsTreeIncidence T' v e →
        G.edgeSet \ α' v e = {τ v} := by
      intro v hv e he
      simp only [τ, hv, ↓reduceDIte]
      exact (hleaf_singleton v hv).choose_spec.2 e he
    have hcomp_img : ∀ u w : ι', T'.Adj u w →
        G.edgeSet \ α' u s(u, w) = τ '' (leafSet T' ∩ treeComponent T' u s(u, w)) := by
      intro u w hadj
      obtain ⟨_, hunion⟩ := theorem_3_3_proof hα' (isTreeIncidence_iff_adj.2 hadj)
      rw [← hunion]
      ext x
      simp only [Set.mem_iUnion, Set.mem_image, Set.mem_inter_iff, exists_prop, Prod.exists]
      constructor
      · rintro ⟨v, e, ⟨hve, hv_leaf, hv_comp⟩, hx⟩
        rw [hτ_compl v hv_leaf e hve, Set.mem_singleton_iff] at hx
        exact ⟨v, ⟨hv_leaf, hv_comp⟩, hx.symm⟩
      · rintro ⟨v, ⟨hv_leaf, hv_comp⟩, rfl⟩
        obtain ⟨z, hadj_z, _⟩ := hT'.exists_adj_of_isLeaf hv_leaf
        have hve : IsTreeIncidence T' v s(v, z) := isTreeIncidence_iff_adj.2 hadj_z
        refine ⟨v, s(v, z), ⟨hve, hv_leaf, hv_comp⟩, ?_⟩
        rw [hτ_compl v hv_leaf s(v, z) hve]
        exact Set.mem_singleton (τ v)
    have hcomp_label : ∀ u w : ι', T'.Adj u w →
        α' u s(u, w) = τ '' (leafSet T' ∩ treeComponent T' w s(w, u)) := by
      intro u w hadj
      have h1 : G.edgeSet \ α' w s(w, u) = α' u s(u, w) := by
        rw [Sym2.eq_swap, ← hα'.isTreeLabelling.compl_eq hadj]
      rw [← h1, hcomp_img w u hadj.symm]
    -- Show `Set.BijOn τ (leafSet T') G.edgeSet`.
    obtain ⟨u₀⟩ := hT'.isTree.connected.nonempty
    have hex_adj₀ : ∃ w₀, T'.Adj u₀ w₀ := by
      by_cases hleaf₀ : IsLeaf T' u₀
      · obtain ⟨w₀, hw₀, _⟩ := hT'.exists_adj_of_isLeaf hleaf₀
        exact ⟨w₀, hw₀⟩
      · obtain ⟨w₀, _, _, _, _, _, hiff⟩ := hT'.exists_three_adj_of_not_isLeaf hleaf₀
        exact ⟨w₀, (hiff w₀).2 (Or.inl rfl)⟩
    obtain ⟨w₀, hadj₀⟩ := hex_adj₀
    have hbij : Set.BijOn τ (leafSet T') G.edgeSet := by
      refine ⟨hτ_mem, ?_, ?_⟩
      · intro v₁ hv₁ v₂ hv₂ hτ_eq
        obtain ⟨z₁, hadj₁, _⟩ := hT'.exists_adj_of_isLeaf hv₁
        obtain ⟨z₂, hadj₂, _⟩ := hT'.exists_adj_of_isLeaf hv₂
        have hinc₁ : IsTreeIncidence T' v₁ s(v₁, z₁) := isTreeIncidence_iff_adj.2 hadj₁
        have hinc₂ : IsTreeIncidence T' v₂ s(v₂, z₂) := isTreeIncidence_iff_adj.2 hadj₂
        have hnot_disj : ¬ Disjoint (G.edgeSet \ α' v₁ s(v₁, z₁)) (G.edgeSet \ α' v₂ s(v₂, z₂))
          := by
          rw [hτ_compl v₁ hv₁ _ hinc₁, hτ_compl v₂ hv₂ _ hinc₂, hτ_eq, Set.disjoint_singleton]
          exact not_ne_iff.2 rfl
        by_cases hv₁_c : v₁ ∈ treeComponent T' u₀ s(u₀, w₀)
        · by_cases hv₂_c : v₂ ∈ treeComponent T' u₀ s(u₀, w₀)
          · obtain ⟨hdisj, _⟩ := theorem_3_3_proof hα' (isTreeIncidence_iff_adj.2 hadj₀)
            have hm₁ : (v₁, s(v₁, z₁)) ∈ leafIncidencesIn T' u₀ s(u₀, w₀) := ⟨hinc₁, hv₁, hv₁_c⟩
            have hm₂ : (v₂, s(v₂, z₂)) ∈ leafIncidencesIn T' u₀ s(u₀, w₀) := ⟨hinc₂, hv₂, hv₂_c⟩
            by_contra hne
            exact hnot_disj (hdisj hm₁ hm₂ (fun h ↦ hne (Prod.mk.inj h).1))
          · have hv₂_w : v₂ ∈ treeComponent T' w₀ s(w₀, u₀) :=
              (notMem_treeComponent_iff hT'.isTree hadj₀).1 hv₂_c
            have h1 : τ v₁ ∈ G.edgeSet \ α' u₀ s(u₀, w₀) := by
              rw [hcomp_img u₀ w₀ hadj₀]
              exact ⟨v₁, ⟨hv₁, hv₁_c⟩, rfl⟩
            have h2 : τ v₁ ∈ α' u₀ s(u₀, w₀) := by
              rw [hτ_eq, hcomp_label u₀ w₀ hadj₀]
              exact ⟨v₂, ⟨hv₂, hv₂_w⟩, rfl⟩
            exact (h1.2 h2).elim
        · have hv₁_w : v₁ ∈ treeComponent T' w₀ s(w₀, u₀) :=
            (notMem_treeComponent_iff hT'.isTree hadj₀).1 hv₁_c
          by_cases hv₂_c : v₂ ∈ treeComponent T' u₀ s(u₀, w₀)
          · have h1 : τ v₂ ∈ G.edgeSet \ α' u₀ s(u₀, w₀) := by
              rw [hcomp_img u₀ w₀ hadj₀]
              exact ⟨v₂, ⟨hv₂, hv₂_c⟩, rfl⟩
            have h2 : τ v₂ ∈ α' u₀ s(u₀, w₀) := by
              rw [← hτ_eq, hcomp_label u₀ w₀ hadj₀]
              exact ⟨v₁, ⟨hv₁, hv₁_w⟩, rfl⟩
            exact (h1.2 h2).elim
          · have hv₂_w : v₂ ∈ treeComponent T' w₀ s(w₀, u₀) :=
              (notMem_treeComponent_iff hT'.isTree hadj₀).1 hv₂_c
            obtain ⟨hdisj, _⟩ := theorem_3_3_proof hα' (isTreeIncidence_iff_adj.2 hadj₀.symm)
            have hm₁ : (v₁, s(v₁, z₁)) ∈ leafIncidencesIn T' w₀ s(w₀, u₀) := ⟨hinc₁, hv₁, hv₁_w⟩
            have hm₂ : (v₂, s(v₂, z₂)) ∈ leafIncidencesIn T' w₀ s(w₀, u₀) := ⟨hinc₂, hv₂, hv₂_w⟩
            by_contra hne
            exact hnot_disj (hdisj hm₁ hm₂ (fun h ↦ hne (Prod.mk.inj h).1))
      · intro x hx
        by_cases hx_in : x ∈ α' u₀ s(u₀, w₀)
        · rw [hcomp_label u₀ w₀ hadj₀] at hx_in
          obtain ⟨v, ⟨hv, _⟩, rfl⟩ := hx_in
          exact ⟨v, hv, rfl⟩
        · have hx_compl : x ∈ G.edgeSet \ α' u₀ s(u₀, w₀) := ⟨hx, hx_in⟩
          rw [hcomp_img u₀ w₀ hadj₀] at hx_compl
          obtain ⟨v, ⟨hv, _⟩, rfl⟩ := hx_compl
          exact ⟨v, hv, rfl⟩
    refine ⟨ι', inferInstance, T', τ, ⟨hT', hbij⟩, ?_⟩
    rw [branchDecompWidth_le_iff]
    intro e he
    induction e using Sym2.ind with
    | _ u w =>
      have hadj : T'.Adj u w := T'.mem_edgeSet.1 he
      have hsub : {v ∈ G.vertexSet | ∃ t₁ ∈ leafSet T', ∃ t₂ ∈ leafSet T',
          ¬ (T'.deleteEdges {s(u, w)}).Reachable t₁ t₂ ∧ G.Inc (τ t₁) v ∧ G.Inc (τ t₂) v} ⊆
          branchEdgeBoundary G (α' u s(u, w)) := by
        rintro v ⟨hv, t₁, ht₁, t₂, ht₂, hnot_reach, hinc₁, hinc₂⟩
        rw [not_reachable_deleteEdges_iff_treeComponent hT'.isTree hadj] at hnot_reach
        rcases hnot_reach with ⟨ht₁_c, ht₂_w⟩ | ⟨ht₁_w, ht₂_c⟩
        · have hτ₂ : τ t₂ ∈ α' u s(u, w) := by
            rw [hcomp_label u w hadj]
            exact ⟨t₂, ⟨ht₂, ht₂_w⟩, rfl⟩
          have hτ₁ : τ t₁ ∈ G.edgeSet \ α' u s(u, w) := by
            rw [hcomp_img u w hadj]
            exact ⟨t₁, ⟨ht₁, ht₁_c⟩, rfl⟩
          exact ⟨hv, ⟨τ t₂, hτ₂, hinc₂⟩, ⟨τ t₁, hτ₁, hinc₁⟩⟩
        · have hτ₁ : τ t₁ ∈ α' u s(u, w) := by
            rw [hcomp_label u w hadj]
            exact ⟨t₁, ⟨ht₁, ht₁_w⟩, rfl⟩
          have hτ₂ : τ t₂ ∈ G.edgeSet \ α' u s(u, w) := by
            rw [hcomp_img u w hadj]
            exact ⟨t₂, ⟨ht₂, ht₂_c⟩, rfl⟩
          exact ⟨hv, ⟨τ t₁, hτ₁, hinc₁⟩, ⟨τ t₂, hτ₂, hinc₂⟩⟩
      have hle_bd : branchEdgeOrder G T' τ s(u, w) ≤ (branchEdgeBoundary G (α' u s(u, w))).ncard :=
        Set.ncard_le_ncard hsub (branchEdgeBoundary_finite G _)
      have heff := (hα'.isTreeLabelling.isEfficient (isTreeIncidence_iff_adj.2 hadj)).2
      dsimp [edgeConnFunc, kappa0] at heff
      omega

/-- Helper for (4.3) Claim (2): when `2 ≤ |E(G)|` and `maxEdgeSize G ≤ k`, any exact tree-labelling
over `singletonEdges G` yields a branch-decomposition of `G` of width `≤ k`
(Graph Minors X, Section 4, proof of (4.3), page 166). -/
theorem exists_branchDecomposition_of_exactTreeLabelling [Fintype ι]
    {G : Hypergraph α β} {k : ℕ} (hk : maxEdgeSize G ≤ k)
    (hcard : 2 ≤ G.edgeSet.ncard) {T : SimpleGraph ι} {α : ι → Sym2 ι → Set β}
    (hα : IsExactTreeLabelling G.edgeSet (edgeConnFunc G k) (singletonEdges G) T α) :
    ∃ (ι' : Type) (_ : Fintype ι') (T' : SimpleGraph ι') (τ : ι' → β),
      IsBranchDecomposition G T' τ ∧ branchDecompWidth G T' τ ≤ k :=
  exists_branchDecomposition_of_exactTreeLabelling_of_isEfficient
    (singletonEdges_isEfficient hk) hcard hα

/-- When `1 ≤ maxEdgeSize G` and `2 ≤ |E(G)|`, `G` has a branch-decomposition achieving width
`branchWidth G`. -/
theorem exists_branchDecomposition_eq_branchWidth {G : Hypergraph α β}
    (hγ : 1 ≤ maxEdgeSize G) (hcard : 2 ≤ G.edgeSet.ncard) :
    ∃ (ι : Type) (_ : Fintype ι) (T : SimpleGraph ι) (τ : ι → β),
      IsBranchDecomposition G T τ ∧ branchDecompWidth G T τ = branchWidth G := by
  let k₀ := max G.vertexSet.ncard (maxEdgeSize G)
  have hk₀ : maxEdgeSize G ≤ k₀ := le_max_right _ _
  have hno_tangle : ¬ ∃ 𝒯, IsTangle G (k₀ + 1) 𝒯 := by
    rintro ⟨𝒯, h𝒯⟩
    have h1 := h𝒯.order_le_ncard_vertexSet
    have h2 : G.vertexSet.ncard ≤ k₀ := le_max_left _ _
    omega
  have hno_bias : ¬ ∃ ℬ, BiasExtends G.edgeSet (edgeConnFunc G k₀) (singletonEdges G) ℬ :=
    (theorem_4_3_claim_1 hγ hk₀).not.2 hno_tangle
  obtain ⟨ι₀, _, T₀, α₀, hα₀⟩ := theorem_3_4_proof G.edgeSet_finite
    (isConnectivityFunction_edgeConnFunc G k₀) (singletonEdges_isEfficient hk₀) hno_bias
  obtain ⟨ι₁, _, T₁, τ₁, hbd₁, _⟩ :=
    exists_branchDecomposition_of_exactTreeLabelling hk₀ hcard hα₀
  have hne : {w : ℕ | ∃ (ι : Type) (_ : Fintype ι) (T : SimpleGraph ι) (τ : ι → β),
      IsBranchDecomposition G T τ ∧ branchDecompWidth G T τ = w}.Nonempty :=
    ⟨branchDecompWidth G T₁ τ₁, ι₁, inferInstance, T₁, τ₁, hbd₁, rfl⟩
  exact Nat.sInf_mem hne

/-- Every branch-decomposition `(T, τ)` of `G` of width `≤ k` yields an exact tree-labelling over
`singletonEdges G` for `edgeConnFunc G k`
(Graph Minors X, Section 4, proof of (4.3), pages 165–166). -/
theorem isExactTreeLabelling_of_isBranchDecomposition [Fintype ι]
    {G : Hypergraph α β} {k : ℕ} {T : SimpleGraph ι} {τ : ι → β}
    (hbd : IsBranchDecomposition G T τ) (hw : branchDecompWidth G T τ ≤ k) :
    IsExactTreeLabelling G.edgeSet (edgeConnFunc G k) (singletonEdges G) T
      (fun v e ↦ τ '' (leafSet T \ treeComponent T v e)) := by
  classical
  have hT := hbd.isTernaryTree
  let α (v : ι) (e : Sym2 ι) : Set β :=
    τ '' (leafSet T \ treeComponent T v e)
  change IsExactTreeLabelling G.edgeSet (edgeConnFunc G k) (singletonEdges G) T α
  have hα_compl : ∀ u w : ι, T.Adj u w →
      α w s(u, w) = τ '' (leafSet T ∩ treeComponent T u s(u, w)) := by
    intro u w hadj
    dsimp [α]
    congr 1
    ext t
    simp only [Set.mem_sdiff, Set.mem_inter_iff]
    refine and_congr_right fun _ ↦ ?_
    have hiff := notMem_treeComponent_iff hT.isTree (x := t) hadj.symm
    simpa [treeComponent, Sym2.eq_swap] using hiff
  have hα_symm : ∀ u w : ι, T.Adj u w →
      α u s(u, w) = G.edgeSet \ α w s(u, w) := by
    intro u w hadj
    rw [hα_compl u w hadj]
    dsimp [α]
    ext x
    simp only [Set.mem_image, Set.mem_sdiff, Set.mem_inter_iff]
    constructor
    · rintro ⟨t, ⟨ht_leaf, ht_not⟩, rfl⟩
      refine ⟨hbd.bijOn.mapsTo ht_leaf, ?_⟩
      rintro ⟨t', ⟨ht'_leaf, ht'_c⟩, heq⟩
      have hteq : t' = t := hbd.bijOn.injOn ht'_leaf ht_leaf heq
      exact ht_not (hteq ▸ ht'_c)
    · rintro ⟨hxE, hnot⟩
      obtain ⟨t, ht_leaf, rfl⟩ := hbd.bijOn.surjOn hxE
      refine ⟨t, ⟨ht_leaf, ?_⟩, rfl⟩
      intro ht_c
      exact hnot ⟨t, ⟨ht_leaf, ht_c⟩, rfl⟩
  refine ⟨⟨hT, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro u e he
    obtain ⟨w, hadj, rfl⟩ := isTreeIncidence_iff_exists_adj.1 he
    have hsubE : α u s(u, w) ⊆ G.edgeSet := by
      rintro _ ⟨t, ⟨ht, _⟩, rfl⟩
      exact hbd.bijOn.mapsTo ht
    refine ⟨hsubE, ?_⟩
    have hbd_sub : branchEdgeBoundary G (α u s(u, w)) ⊆
        {v ∈ G.vertexSet | ∃ t₁ ∈ leafSet T, ∃ t₂ ∈ leafSet T,
          ¬ (T.deleteEdges {s(u, w)}).Reachable t₁ t₂ ∧ G.Inc (τ t₁) v ∧ G.Inc (τ t₂) v} := by
      rintro v ⟨hv, ⟨e₁, he₁, hinc₁⟩, ⟨e₂, he₂, hinc₂⟩⟩
      have he₂' : e₂ ∈ α w s(u, w) := by
        rw [Sym2.eq_swap, hα_symm w u hadj.symm, Sym2.eq_swap]
        exact he₂
      rw [hα_compl u w hadj] at he₂'
      obtain ⟨t₁, ⟨ht₁_leaf, ht₁_not⟩, rfl⟩ := he₁
      obtain ⟨t₂, ⟨ht₂_leaf, ht₂_c⟩, rfl⟩ := he₂'
      have ht₁_w : t₁ ∈ treeComponent T w s(w, u) :=
        (notMem_treeComponent_iff hT.isTree hadj).1 ht₁_not
      refine ⟨hv, t₁, ht₁_leaf, t₂, ht₂_leaf, ?_, hinc₁, hinc₂⟩
      rw [not_reachable_deleteEdges_iff_treeComponent hT.isTree hadj]
      exact Or.inr ⟨ht₁_w, ht₂_c⟩
    have hle_ord : (branchEdgeBoundary G (α u s(u, w))).ncard ≤ branchEdgeOrder G T τ s(u, w) :=
      Set.ncard_le_ncard hbd_sub (G.vertexSet_finite.subset fun _ h ↦ h.1)
    have hle_k : branchEdgeOrder G T τ s(u, w) ≤ k :=
      (branchEdgeOrder_le_branchDecompWidth (T.mem_edgeSet.2 hadj)).trans hw
    dsimp [edgeConnFunc, kappa0]
    omega
  · intro u w hadj
    exact hα_symm u w hadj
  · intro v e he hleaf
    obtain ⟨w, hadj, rfl⟩ := isTreeIncidence_iff_exists_adj.1 he
    right
    refine ⟨{τ v}, ⟨τ v, hbd.bijOn.mapsTo hleaf, rfl⟩, ?_⟩
    have hcomp := treeComponent_eq_singleton_of_isLeaf hT hadj hleaf
    dsimp [α]
    rw [hcomp]
    ext x
    simp only [Set.mem_union, Set.mem_image, Set.mem_sdiff, Set.mem_singleton_iff]
    constructor
    · rintro (⟨t, ⟨ht, _⟩, rfl⟩ | rfl)
      · exact hbd.bijOn.mapsTo ht
      · exact hbd.bijOn.mapsTo hleaf
    · intro hxE
      obtain ⟨t, ht, rfl⟩ := hbd.bijOn.surjOn hxE
      by_cases htv : t = v
      · exact Or.inr (congrArg τ htv)
      · exact Or.inl ⟨t, ⟨ht, htv⟩, rfl⟩
  · intro u f₁ f₂ f₃ hf₁ hf₂ hf₃ h12 h13 h23
    obtain ⟨w₁, hadj₁, rfl⟩ := isTreeIncidence_iff_exists_adj.1 hf₁
    obtain ⟨w₂, hadj₂, rfl⟩ := isTreeIncidence_iff_exists_adj.1 hf₂
    obtain ⟨w₃, hadj₃, rfl⟩ := isTreeIncidence_iff_exists_adj.1 hf₃
    have hw12 : w₁ ≠ w₂ := fun h ↦ h12 (by rw [h])
    have hw13 : w₁ ≠ w₃ := fun h ↦ h13 (by rw [h])
    have hw23 : w₂ ≠ w₃ := fun h ↦ h23 (by rw [h])
    have hu_not_leaf : ¬ IsLeaf T u := hT.not_isLeaf_of_isFork ⟨hf₁, hf₂, h12⟩
    have hiff : ∀ x, T.Adj u x ↔ x = w₁ ∨ x = w₂ ∨ x = w₃ := by
      obtain ⟨z₁, z₂, hwz₁, hwz₂, hz12, hiff₀⟩ := hT.exists_other_two_adj hu_not_leaf hadj₁
      intro x
      refine ⟨fun hx ↦ ?_, ?_⟩
      · by_contra! hnot
        have hsub4 : ({w₁, w₂, w₃, x} : Finset ι) ⊆ T.neighborFinset u := by
          intro y hy
          simp only [Finset.mem_insert, Finset.mem_singleton] at hy
          rw [mem_neighborFinset]
          rcases hy with rfl | rfl | rfl | rfl <;> assumption
        have hcard4 : ({w₁, w₂, w₃, x} : Finset ι).card = 4 := by
          rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
            Finset.card_insert_of_notMem, Finset.card_singleton] <;>
            simp [hw12, hw13, hw23, hnot.1.symm, hnot.2.1.symm, hnot.2.2.symm]
        have hcard3 : (T.neighborFinset u).card = 3 :=
          hT.degree_eq_three_of_not_isLeaf hu_not_leaf
        have := Finset.card_le_card hsub4
        omega
      · rintro (rfl | rfl | rfl) <;> assumption
    obtain ⟨hcomp_eq, _, _, _⟩ :=
      treeComponent_split_of_not_isLeaf hT hadj₁ hw12 hw13 hw23 hiff
    ext x
    simp only [Set.mem_union]
    constructor
    · rintro ((⟨t, ⟨ht, _⟩, rfl⟩ | ⟨t, ⟨ht, _⟩, rfl⟩) | ⟨t, ⟨ht, _⟩, rfl⟩) <;>
        exact hbd.bijOn.mapsTo ht
    · intro hxE
      obtain ⟨t, ht_leaf, rfl⟩ := hbd.bijOn.surjOn hxE
      by_cases ht₁ : t ∈ treeComponent T u s(u, w₁)
      · rw [hcomp_eq] at ht₁
        rcases ht₁ with (rfl | ht₂) | ht₃
        · exact (hu_not_leaf ht_leaf).elim
        · have ht_not₂ : t ∉ treeComponent T u s(u, w₂) := by
            intro hm
            exact (notMem_treeComponent_iff hT.isTree hadj₂).2 ht₂ hm
          exact Or.inl (Or.inr ⟨t, ⟨ht_leaf, ht_not₂⟩, rfl⟩)
        · have ht_not₃ : t ∉ treeComponent T u s(u, w₃) := by
            intro hm
            exact (notMem_treeComponent_iff hT.isTree hadj₃).2 ht₃ hm
          exact Or.inr ⟨t, ⟨ht_leaf, ht_not₃⟩, rfl⟩
      · exact Or.inl (Or.inl ⟨t, ⟨ht_leaf, ht₁⟩, rfl⟩)
  · intro u f₁ f₂ ⟨hf₁, hf₂, hne⟩
    obtain ⟨w₁, hadj₁, rfl⟩ := isTreeIncidence_iff_exists_adj.1 hf₁
    obtain ⟨w₂, hadj₂, rfl⟩ := isTreeIncidence_iff_exists_adj.1 hf₂
    have hw12 : w₁ ≠ w₂ := fun h ↦ hne (by rw [h])
    have hu_not_leaf : ¬ IsLeaf T u := hT.not_isLeaf_of_isFork ⟨hf₁, hf₂, hne⟩
    obtain ⟨z₁, z₂, hw₁z₁, hw₁z₂, hz12, hiff₁⟩ := hT.exists_other_two_adj hu_not_leaf hadj₁
    obtain ⟨hcomp_eq, _, _, _⟩ :=
      treeComponent_split_of_not_isLeaf hT hadj₁ hw₁z₁ hw₁z₂ hz12 hiff₁
    have hw₂_mem : w₂ = z₁ ∨ w₂ = z₂ := by
      rcases (hiff₁ w₂).1 hadj₂ with h | h | h
      · exact (hw12 h.symm).elim
      · exact Or.inl h
      · exact Or.inr h
    have hsub_comp : treeComponent T w₂ s(w₂, u) ⊆ treeComponent T u s(u, w₁) := by
      rw [hcomp_eq]
      rcases hw₂_mem with rfl | rfl
      · exact Set.subset_union_of_subset_left Set.subset_union_right _
      · exact Set.subset_union_right
    ext x
    simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
    rintro ⟨⟨t₁, ⟨ht₁_leaf, ht₁_not⟩, rfl⟩, ⟨t₂, ⟨ht₂_leaf, ht₂_not⟩, hτ_eq⟩⟩
    have hteq : t₁ = t₂ := hbd.bijOn.injOn ht₁_leaf ht₂_leaf hτ_eq.symm
    subst hteq
    have ht₁_w₂ : t₁ ∈ treeComponent T w₂ s(w₂, u) :=
      (notMem_treeComponent_iff hT.isTree hadj₂).1 ht₂_not
    exact ht₁_not (hsub_comp ht₁_w₂)

/-- Claim (2) in the proof of **Graph Minors X, (4.3)** (pages 165–166):
When `1 ≤ γ(G) ≤ k`, there is an exact tree-labelling over `𝒜 = {{e} : e ∈ E(G)}` for
`κ(X) = |∂(X)| - k` if and only if `β(G) ≤ k`. -/
theorem theorem_4_3_claim_2 {G : Hypergraph α β} {k : ℕ}
    (hγ : 1 ≤ maxEdgeSize G) (hk : maxEdgeSize G ≤ k) :
    (∃ (ι : Type) (_ : Fintype ι) (T : SimpleGraph ι) (α : ι → Sym2 ι → Set β),
      IsExactTreeLabelling G.edgeSet (edgeConnFunc G k) (singletonEdges G) T α) ↔
      branchWidth G ≤ k := by
  classical
  constructor
  · rintro ⟨ι, _, T, α, hα⟩
    by_cases hcard : 2 ≤ G.edgeSet.ncard
    · obtain ⟨ι', _, T', τ, hbd, hw⟩ :=
        exists_branchDecomposition_of_exactTreeLabelling hk hcard hα
      have hmem : branchDecompWidth G T' τ ∈
          {w : ℕ | ∃ (ι : Type) (_ : Fintype ι) (T : SimpleGraph ι) (τ : ι → β),
            IsBranchDecomposition G T τ ∧ branchDecompWidth G T τ = w} :=
        ⟨ι', inferInstance, T', τ, hbd, rfl⟩
      exact (Nat.sInf_le hmem).trans hw
    · rw [branchWidth_eq_zero_of_ncard_edgeSet_le_one (by omega)]
      exact Nat.zero_le k
  · intro hbw
    by_cases hcard : 2 ≤ G.edgeSet.ncard
    · obtain ⟨ι, _, T, τ, hbd, hw_eq⟩ := exists_branchDecomposition_eq_branchWidth hγ hcard
      exact ⟨ι, inferInstance, T, _,
        isExactTreeLabelling_of_isBranchDecomposition hbd (hw_eq.trans_le hbw)⟩
    · -- Case `G.edgeSet.ncard ≤ 1`: since `1 ≤ maxEdgeSize G`, `G.edgeSet` is a singleton,
      -- so `G.edgeSet ∈ singletonEdges G` and no bias can extend `singletonEdges G`.
      obtain ⟨⟨e₀, he₀⟩, _⟩ := nonempty_of_one_le_maxEdgeSize hγ
      have hE_eq : G.edgeSet = {e₀} :=
        (Set.eq_of_subset_of_ncard_le (Set.singleton_subset_iff.2 he₀)
          (by rw [Set.ncard_singleton]; omega) G.edgeSet_finite).symm
      have hno_bias : ¬ ∃ ℬ, BiasExtends G.edgeSet (edgeConnFunc G k) (singletonEdges G) ℬ := by
        rintro ⟨ℬ, hbias, hsub⟩
        have hmem : G.edgeSet ∈ ℬ := hsub ⟨e₀, he₀, hE_eq.symm⟩
        exact hbias.union_ne hmem hmem hmem (by simp)
      exact theorem_3_4_proof G.edgeSet_finite (isConnectivityFunction_edgeConnFunc G k)
        (singletonEdges_isEfficient hk) hno_bias

/-- Claim (3) in the proof of **Graph Minors X, (4.3)** (page 166):
"For all $k \ge \gamma(G)$, $G$ has a tangle of order $k + 1$ if and only if $k < \beta(G)$." -/
theorem theorem_4_3_claim_3 {G : Hypergraph α β} {k : ℕ}
    (hγ : 1 ≤ maxEdgeSize G) (hk : maxEdgeSize G ≤ k) :
    (∃ 𝒯, IsTangle G (k + 1) 𝒯) ↔ k < branchWidth G := by
  have h35 := theorem_3_5_proof G.edgeSet_finite (isConnectivityFunction_edgeConnFunc G k)
    (singletonEdges_isEfficient hk)
  have hiff : (∃ ℬ, BiasExtends G.edgeSet (edgeConnFunc G k) (singletonEdges G) ℬ) ↔
      ¬ ∃ (ι : Type) (_ : Fintype ι) (T : SimpleGraph ι) (α : ι → Sym2 ι → Set β),
        IsExactTreeLabelling G.edgeSet (edgeConnFunc G k) (singletonEdges G) T α := by
    rw [← not_iff_not, not_not, h35.1, h35.2]
  rw [← theorem_4_3_claim_1 hγ hk, hiff, theorem_4_3_claim_2 hγ hk, not_le]

/-- **Graph Minors X, (4.3)** (page 165):
"(4.3) *For any hypergraph $G$, $\max(\beta(G), \gamma(G)) = \theta(G)$ unless $\gamma(G) = 0$ and
$V(G) \ne \emptyset$.*" -/
theorem theorem_4_3_proof (G : Hypergraph α β)
    (h : ¬ (maxEdgeSize G = 0 ∧ G.vertexSet.Nonempty)) :
    max (branchWidth G) (maxEdgeSize G) = tangleNumber G := by
  by_cases hγ0 : maxEdgeSize G = 0
  · have hV : G.vertexSet = ∅ :=
      Set.not_nonempty_iff_eq_empty.1 fun hne ↦ h ⟨hγ0, hne⟩
    rw [hγ0, branchWidth_eq_zero_of_maxEdgeSize_eq_zero hγ0, tangleNumber_eq_zero_iff.2 hV,
      max_self]
  · have hγ1 : 1 ≤ maxEdgeSize G := Nat.one_le_iff_ne_zero.2 hγ0
    have hγ_le_θ : maxEdgeSize G ≤ tangleNumber G := maxEdgeSize_le_tangleNumber G
    have hno_tangle_θ : ¬ ∃ 𝒯, IsTangle G (tangleNumber G + 1) 𝒯 := by
      rintro ⟨𝒯, h𝒯⟩
      have := h𝒯.le_tangleNumber
      omega
    have hβ_le_θ : branchWidth G ≤ tangleNumber G := by
      have := (theorem_4_3_claim_3 hγ1 hγ_le_θ).not.1 hno_tangle_θ
      omega
    have hmax_le : max (branchWidth G) (maxEdgeSize G) ≤ tangleNumber G :=
      max_le hβ_le_θ hγ_le_θ
    by_cases hγ_eq : tangleNumber G ≤ maxEdgeSize G
    · exact le_antisymm hmax_le (hγ_eq.trans (le_max_right _ _))
    · push Not at hγ_eq
      have hk : maxEdgeSize G ≤ tangleNumber G - 1 := by omega
      have h1 : 1 ≤ tangleNumber G := hγ1.trans hγ_le_θ
      obtain ⟨𝒯, h𝒯⟩ := exists_isTangle_of_le_tangleNumber h1 le_rfl
      have h𝒯' : IsTangle G ((tangleNumber G - 1) + 1) 𝒯 := by
        rwa [Nat.sub_add_cancel h1]
      have hlt : tangleNumber G - 1 < branchWidth G :=
        (theorem_4_3_claim_3 hγ1 hk).1 ⟨𝒯, h𝒯'⟩
      have hθ_le_β : tangleNumber G ≤ branchWidth G := by omega
      exact le_antisymm hmax_le (hθ_le_β.trans (le_max_left _ _))

/-! ## Weakening the second tangle axiom: (4.5) -/

/-- Submodularity of separation order for two separations `(A₁, B₁)` and `(A₂, B₂)` of `G`
(Graph Minors X, Section 4, proof of (4.5), page 167):
"The sum of the orders of $(A_1 \cap B_2, B_1 \cup A_2)$ and $(A_1 \cup B_2, B_1 \cap A_2)$
equals the sum of the orders of $(A_1, B_1)$ and $(A_2, B_2)$." -/
theorem separationOrder_inter_union_add_union_inter {G A₁ B₁ A₂ B₂ : Hypergraph α β}
    (h₁ : G.IsSeparation A₁ B₁) (h₂ : G.IsSeparation A₂ B₂) :
    separationOrder (A₁ ∩ B₂) (B₁ ∪ A₂) + separationOrder (A₁ ∪ B₂) (B₁ ∩ A₂) =
      separationOrder A₁ B₁ + separationOrder A₂ B₂ := by
  let U₁ := ((A₁ ∩ B₂) ∩ (B₁ ∪ A₂)).vertexSet
  let U₂ := ((A₁ ∪ B₂) ∩ (B₁ ∩ A₂)).vertexSet
  let X := (A₁ ∩ B₁).vertexSet
  let Y := (A₂ ∩ B₂).vertexSet
  have hU_union : U₁ ∪ U₂ = X ∪ Y := by
    ext v
    have hvG_iff : v ∈ G.vertexSet ↔
        (v ∈ A₁.vertexSet ∨ v ∈ B₁.vertexSet) ∧ (v ∈ A₂.vertexSet ∨ v ∈ B₂.vertexSet) := by
      rw [← Set.mem_union, h₁.vertexSet_union, ← Set.mem_union, h₂.vertexSet_union, and_self]
    have h1 : v ∈ A₁.vertexSet → v ∈ G.vertexSet := fun h ↦ h₁.left_le.vertexSet_subset h
    have h2 : v ∈ A₂.vertexSet → v ∈ G.vertexSet := fun h ↦ h₂.left_le.vertexSet_subset h
    simp only [U₁, U₂, X, Y, inter_vertexSet, union_vertexSet, Set.mem_union, Set.mem_inter_iff]
    constructor
    · rintro (⟨⟨ha₁, hb₂⟩, hb₁ | ha₂⟩ | ⟨ha₁ | hb₂, hb₁, ha₂⟩)
      · exact Or.inl ⟨ha₁, hb₁⟩
      · exact Or.inr ⟨ha₂, hb₂⟩
      · exact Or.inl ⟨ha₁, hb₁⟩
      · exact Or.inr ⟨ha₂, hb₂⟩
    · rintro (⟨ha₁, hb₁⟩ | ⟨ha₂, hb₂⟩)
      · obtain ⟨_, ha₂ | hb₂⟩ := hvG_iff.1 (h1 ha₁)
        · exact Or.inr ⟨Or.inl ha₁, hb₁, ha₂⟩
        · exact Or.inl ⟨⟨ha₁, hb₂⟩, Or.inl hb₁⟩
      · obtain ⟨ha₁ | hb₁, _⟩ := hvG_iff.1 (h2 ha₂)
        · exact Or.inl ⟨⟨ha₁, hb₂⟩, Or.inr ha₂⟩
        · exact Or.inr ⟨Or.inr hb₂, hb₁, ha₂⟩
  have hU_inter : U₁ ∩ U₂ = X ∩ Y := by
    ext v
    simp only [U₁, U₂, X, Y, inter_vertexSet, union_vertexSet, Set.mem_inter_iff, Set.mem_union]
    tauto
  have hcard1 := Set.ncard_union_add_ncard_inter U₁ U₂
    (((A₁ ∩ B₂) ∩ (B₁ ∪ A₂)).vertexSet_finite) (((A₁ ∪ B₂) ∩ (B₁ ∩ A₂)).vertexSet_finite)
  have hcard2 := Set.ncard_union_add_ncard_inter X Y
    ((A₁ ∩ B₁).vertexSet_finite) ((A₂ ∩ B₂).vertexSet_finite)
  rw [hU_union, hU_inter] at hcard1
  change U₁.ncard + U₂.ncard = X.ncard + Y.ncard
  omega

/-- Helper for `(4.5)`: if `(A₀, B₀) ∈ 𝒯`, `(X, Y)` is a separation of `G` of order `< θ`, and
`X ≤ A₀`, then `(X, Y) ∈ 𝒯` by the first tangle axiom and condition (i). -/
private theorem mem_of_left_le {G : Hypergraph α β} {θ : ℕ}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)}
    (hax1 : TangleAxiom1 G θ 𝒯)
    (hi : ∀ ⦃A₁ B₁ A₂ B₂ : Hypergraph α β⦄, (A₁, B₁) ∈ 𝒯 → (A₂, B₂) ∈ 𝒯 → ¬ B₁ ≤ A₂)
    {A₀ B₀ X Y : Hypergraph α β} (h₀ : (A₀, B₀) ∈ 𝒯)
    (hsep : G.IsSeparation X Y) (hord : separationOrder X Y < θ) (hle : X ≤ A₀) :
    (X, Y) ∈ 𝒯 := by
  rcases hax1 hsep hord with h | h
  · exact h
  · exact (hi h h₀ hle).elim

/-- Claim (3) in the proof of **Graph Minors X, (4.5)** (page 167):
"For $1 \le i \le 3$, if $v \in V(A_i \cap B_i)$ then $v$ is incident with an edge of $B_i$;
and also with an edge of $A_i$, unless $v$ belongs to no other $A_j$ ($j \ne i$)." -/
theorem theorem_4_5_claim_3 {G : Hypergraph α β} {θ : ℕ}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)}
    (hsep : ∀ ⦃A B : Hypergraph α β⦄, (A, B) ∈ 𝒯 → G.IsSeparation A B)
    (hord : ∀ ⦃A B : Hypergraph α β⦄, (A, B) ∈ 𝒯 → separationOrder A B < θ)
    (hax1 : TangleAxiom1 G θ 𝒯)
    (hi : ∀ ⦃A₁ B₁ A₂ B₂ : Hypergraph α β⦄, (A₁, B₁) ∈ 𝒯 → (A₂, B₂) ∈ 𝒯 → ¬ B₁ ≤ A₂)
    {A₁ B₁ A₂ A₃ : Hypergraph α β} (h₁ : (A₁, B₁) ∈ 𝒯) (hU : A₁ ∪ A₂ ∪ A₃ = G)
    (hmin1 : ∀ ⦃A₁' B₁' : Hypergraph α β⦄, (A₁', B₁') ∈ 𝒯 → A₁' ∪ A₂ ∪ A₃ = G →
      separationOrder A₁ B₁ ≤ separationOrder A₁' B₁')
    {v : α} (hv : v ∈ (A₁ ∩ B₁).vertexSet) :
    (∃ e ∈ B₁.edgeSet, B₁.Inc e v) ∧
    (v ∈ A₂.vertexSet ∪ A₃.vertexSet → ∃ e ∈ A₁.edgeSet, A₁.Inc e v) := by
  have hsep₁ := hsep h₁
  refine ⟨?_, ?_⟩
  · by_contra! hisoB
    have hEB_eq : (B₁.deleteVertices {v}).edgeSet = B₁.edgeSet := by
      ext e
      simp only [deleteVertices, Set.mem_sep_iff, Set.mem_singleton_iff, forall_eq,
        and_iff_left_iff_imp]
      exact hisoB e
    have hsep' : G.IsSeparation A₁ (B₁.deleteVertices {v}) := by
      rw [isSeparation_iff_of_le hsep₁.left_le ((deleteVertices_le B₁ {v}).trans hsep₁.right_le)]
      refine ⟨?_, ?_, ?_⟩
      · ext x
        simp only [deleteVertices, Set.mem_union, Set.mem_sdiff, Set.mem_singleton_iff]
        constructor
        · rintro (hxA | ⟨hxB, _⟩)
          · exact hsep₁.left_le.vertexSet_subset hxA
          · exact hsep₁.right_le.vertexSet_subset hxB
        · intro hxG
          by_cases hxv : x = v
          · exact Or.inl (hxv ▸ hv.1)
          · rcases hsep₁.vertexSet_union.symm ▸ hxG with hxA | hxB
            · exact Or.inl hxA
            · exact Or.inr ⟨hxB, hxv⟩
      · rw [hEB_eq, hsep₁.edgeSet_union]
      · rw [hEB_eq]
        exact hsep₁.edgeSet_inter_eq
    have hinter_eq : (A₁ ∩ B₁.deleteVertices {v}).vertexSet = (A₁ ∩ B₁).vertexSet \ {v} := by
      ext x
      simp only [inter_vertexSet, deleteVertices, Set.mem_inter_iff, Set.mem_sdiff,
        Set.mem_singleton_iff]
      tauto
    have hord_lt : separationOrder A₁ (B₁.deleteVertices {v}) < separationOrder A₁ B₁ := by
      rw [separationOrder, hinter_eq, separationOrder]
      exact Set.ncard_lt_ncard (Set.sdiff_singleton_ssubset.2 hv) (A₁ ∩ B₁).vertexSet_finite
    have hmem' : (A₁, B₁.deleteVertices {v}) ∈ 𝒯 :=
      mem_of_left_le hax1 hi h₁ hsep' (hord_lt.trans (hord h₁)) le_rfl
    have hle := hmin1 hmem' hU
    omega
  · intro hv₂₃
    by_contra! hisoA
    have hEA_eq : (A₁.deleteVertices {v}).edgeSet = A₁.edgeSet := by
      ext e
      simp only [deleteVertices, Set.mem_sep_iff, Set.mem_singleton_iff, forall_eq,
        and_iff_left_iff_imp]
      exact hisoA e
    have hsep' : G.IsSeparation (A₁.deleteVertices {v}) B₁ := by
      rw [isSeparation_iff_of_le ((deleteVertices_le A₁ {v}).trans hsep₁.left_le) hsep₁.right_le]
      refine ⟨?_, ?_, ?_⟩
      · ext x
        simp only [deleteVertices, Set.mem_union, Set.mem_sdiff, Set.mem_singleton_iff]
        constructor
        · rintro (⟨hxA, _⟩ | hxB)
          · exact hsep₁.left_le.vertexSet_subset hxA
          · exact hsep₁.right_le.vertexSet_subset hxB
        · intro hxG
          by_cases hxv : x = v
          · exact Or.inr (hxv ▸ hv.2)
          · rcases hsep₁.vertexSet_union.symm ▸ hxG with hxA | hxB
            · exact Or.inl ⟨hxA, hxv⟩
            · exact Or.inr hxB
      · rw [hEA_eq, hsep₁.edgeSet_union]
      · rw [hEA_eq]
        exact hsep₁.edgeSet_inter_eq
    have hinter_eq : ((A₁.deleteVertices {v}) ∩ B₁).vertexSet = (A₁ ∩ B₁).vertexSet \ {v} := by
      ext x
      simp only [inter_vertexSet, deleteVertices, Set.mem_inter_iff, Set.mem_sdiff,
        Set.mem_singleton_iff]
      tauto
    have hord_lt : separationOrder (A₁.deleteVertices {v}) B₁ < separationOrder A₁ B₁ := by
      rw [separationOrder, hinter_eq, separationOrder]
      exact Set.ncard_lt_ncard (Set.sdiff_singleton_ssubset.2 hv) (A₁ ∩ B₁).vertexSet_finite
    have hmem' : (A₁.deleteVertices {v}, B₁) ∈ 𝒯 :=
      mem_of_left_le hax1 hi h₁ hsep' (hord_lt.trans (hord h₁)) (deleteVertices_le A₁ {v})
    have hU' : (A₁.deleteVertices {v}) ∪ A₂ ∪ A₃ = G := by
      rw [← hU]
      refine Hypergraph.ext ?_ ?_ ?_
      · ext x
        simp only [union_vertexSet, deleteVertices, Set.mem_union, Set.mem_sdiff,
          Set.mem_singleton_iff]
        constructor
        · rintro ((⟨hx₁, _⟩ | hx₂) | hx₃)
          · exact Or.inl (Or.inl hx₁)
          · exact Or.inl (Or.inr hx₂)
          · exact Or.inr hx₃
        · rintro ((hx₁ | hx₂) | hx₃)
          · by_cases hxv : x = v
            · rcases hxv ▸ hv₂₃ with hv₂ | hv₃
              · exact Or.inl (Or.inr hv₂)
              · exact Or.inr hv₃
            · exact Or.inl (Or.inl ⟨hx₁, hxv⟩)
          · exact Or.inl (Or.inr hx₂)
          · exact Or.inr hx₃
      · simp [union_edgeSet, hEA_eq]
      · funext e x
        apply propext
        have hinc_eq : (A₁.deleteVertices {v}).Inc e x ↔ A₁.Inc e x := by
          simp only [deleteVertices, Set.mem_singleton_iff, forall_eq]
          exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, hisoA e (A₁.edge_mem_of_inc h)⟩⟩
        simp [union_inc, hinc_eq]
    have hle := hmin1 hmem' hU'
    omega

/-- Claim (4) in the proof of **Graph Minors X, (4.5)** (page 167):
"For $1 \le i, j \le 3$ with $i \ne j$, $A_i \subseteq B_j$." -/
theorem theorem_4_5_claim_4 {G : Hypergraph α β} {θ : ℕ}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)}
    (hsep : ∀ ⦃A B : Hypergraph α β⦄, (A, B) ∈ 𝒯 → G.IsSeparation A B)
    (hord : ∀ ⦃A B : Hypergraph α β⦄, (A, B) ∈ 𝒯 → separationOrder A B < θ)
    (hax1 : TangleAxiom1 G θ 𝒯)
    (hi : ∀ ⦃A₁ B₁ A₂ B₂ : Hypergraph α β⦄, (A₁, B₁) ∈ 𝒯 → (A₂, B₂) ∈ 𝒯 → ¬ B₁ ≤ A₂)
    {A₁ B₁ A₂ B₂ A₃ : Hypergraph α β}
    (h₁ : (A₁, B₁) ∈ 𝒯) (h₂ : (A₂, B₂) ∈ 𝒯) (hA₃ : A₃ ≤ G) (hU : A₁ ∪ A₂ ∪ A₃ = G)
    (hmin1_1 : ∀ ⦃A₁' B₁' : Hypergraph α β⦄, (A₁', B₁') ∈ 𝒯 → A₁' ∪ A₂ ∪ A₃ = G →
      separationOrder A₁ B₁ ≤ separationOrder A₁' B₁')
    (hmin1_2 : ∀ ⦃A₂' B₂' : Hypergraph α β⦄, (A₂', B₂') ∈ 𝒯 → A₁ ∪ A₂' ∪ A₃ = G →
      separationOrder A₂ B₂ ≤ separationOrder A₂' B₂')
    (hmin2_1 : ∀ ⦃A₁' B₁' : Hypergraph α β⦄, (A₁', B₁') ∈ 𝒯 → A₁' ∪ A₂ ∪ A₃ = G →
      separationOrder A₁' B₁' ≤ separationOrder A₁ B₁ →
      A₁.vertexSet.ncard + A₁.edgeSet.ncard ≤ A₁'.vertexSet.ncard + A₁'.edgeSet.ncard)
    (hmin2_2 : ∀ ⦃A₂' B₂' : Hypergraph α β⦄, (A₂', B₂') ∈ 𝒯 → A₁ ∪ A₂' ∪ A₃ = G →
      separationOrder A₂' B₂' ≤ separationOrder A₂ B₂ →
      A₂.vertexSet.ncard + A₂.edgeSet.ncard ≤ A₂'.vertexSet.ncard + A₂'.edgeSet.ncard) :
    A₁ ≤ B₂ ∧ A₂ ≤ B₁ := by
  have hstep : ∀ {X₁ Y₁ X₂ Y₂ : Hypergraph α β},
      (X₁, Y₁) ∈ 𝒯 → (X₂, Y₂) ∈ 𝒯 → X₁ ∪ X₂ ∪ A₃ = G →
      (∀ ⦃X₂' Y₂' : Hypergraph α β⦄, (X₂', Y₂') ∈ 𝒯 → X₂' ∪ X₁ ∪ A₃ = G →
        separationOrder X₂ Y₂ ≤ separationOrder X₂' Y₂') →
      (∀ ⦃X₁' Y₁' : Hypergraph α β⦄, (X₁', Y₁') ∈ 𝒯 → X₁' ∪ X₂ ∪ A₃ = G →
        separationOrder X₁' Y₁' ≤ separationOrder X₁ Y₁ →
        X₁.vertexSet.ncard + X₁.edgeSet.ncard ≤ X₁'.vertexSet.ncard + X₁'.edgeSet.ncard) →
      separationOrder (X₁ ∩ Y₂) (Y₁ ∪ X₂) ≤ separationOrder X₁ Y₁ →
      X₁ ≤ Y₂ ∧ X₂ ≤ Y₁ := by
    intro X₁ Y₁ X₂ Y₂ hx₁ hx₂ hU_X hmin1_X₂ hmin2_X₁ hle_ord
    have hs₁ := hsep hx₁
    have hs₂ := hsep hx₂
    have hsep_inter : G.IsSeparation (X₁ ∩ Y₂) (Y₁ ∪ X₂) :=
      (hs₁.symm.union_inter hs₂).symm
    have hord_inter : separationOrder (X₁ ∩ Y₂) (Y₁ ∪ X₂) < θ :=
      hle_ord.trans_lt (hord hx₁)
    have hle_X₁ : X₁ ∩ Y₂ ≤ X₁ := inter_le_left hs₁.left_le hs₂.right_le
    have hmem_inter : (X₁ ∩ Y₂, Y₁ ∪ X₂) ∈ 𝒯 :=
      mem_of_left_le hax1 hi hx₁ hsep_inter hord_inter hle_X₁
    have hU_inter : (X₁ ∩ Y₂) ∪ X₂ ∪ A₃ = G := by
      have hle_G : (X₁ ∩ Y₂) ∪ X₂ ∪ A₃ ≤ G :=
        union_le (union_le hsep_inter.left_le hs₂.left_le) hA₃
      refine eq_of_le_of_vertexSet_eq_of_edgeSet_eq hle_G le_rfl ?_ ?_
      · refine Set.Subset.antisymm hle_G.vertexSet_subset ?_
        intro v hvG
        have hvU : v ∈ (X₁ ∪ X₂ ∪ A₃).vertexSet := hU_X.symm ▸ hvG
        rcases hvU with (hv₁ | hv₂) | hv₃
        · rcases hs₂.vertexSet_union.symm ▸ hvG with hvX₂ | hvY₂
          · exact Or.inl (Or.inr hvX₂)
          · exact Or.inl (Or.inl ⟨hv₁, hvY₂⟩)
        · exact Or.inl (Or.inr hv₂)
        · exact Or.inr hv₃
      · refine Set.Subset.antisymm hle_G.edgeSet_subset ?_
        intro e heG
        have heU : e ∈ (X₁ ∪ X₂ ∪ A₃).edgeSet := hU_X.symm ▸ heG
        rcases heU with (he₁ | he₂) | he₃
        · rcases hs₂.edgeSet_union.symm ▸ heG with heX₂ | heY₂
          · exact Or.inl (Or.inr heX₂)
          · exact Or.inl (Or.inl ⟨he₁, heY₂⟩)
        · exact Or.inl (Or.inr he₂)
        · exact Or.inr he₃
    have hcard_le := hmin2_X₁ hmem_inter hU_inter hle_ord
    have hV_le : (X₁ ∩ Y₂).vertexSet.ncard ≤ X₁.vertexSet.ncard :=
      Set.ncard_le_ncard hle_X₁.vertexSet_subset X₁.vertexSet_finite
    have hE_le : (X₁ ∩ Y₂).edgeSet.ncard ≤ X₁.edgeSet.ncard :=
      Set.ncard_le_ncard hle_X₁.edgeSet_subset X₁.edgeSet_finite
    have heq_X₁ : X₁ ∩ Y₂ = X₁ :=
      eq_of_le_of_ncard_eq hle_X₁ (by omega) (by omega)
    have hX₁_le_Y₂ : X₁ ≤ Y₂ := heq_X₁ ▸ inter_le_right hs₁.left_le hs₂.right_le
    refine ⟨hX₁_le_Y₂, ?_⟩
    have hEX₂_sub : X₂.edgeSet ⊆ Y₁.edgeSet := by
      intro e heX₂
      have heG : e ∈ G.edgeSet := hs₂.left_le.edgeSet_subset heX₂
      have he_not_Y₂ : e ∉ Y₂.edgeSet := hs₂.notMem_edgeSet_right heX₂
      have he_not_X₁ : e ∉ X₁.edgeSet := fun h ↦ he_not_Y₂ (hX₁_le_Y₂.edgeSet_subset h)
      exact (hs₁.edgeSet_union.symm ▸ heG).resolve_left he_not_X₁
    have hVX₂_sub : X₂.vertexSet ⊆ Y₁.vertexSet := by
      intro v hvX₂
      by_contra hv_not_Y₁
      have hvG : v ∈ G.vertexSet := hs₂.left_le.vertexSet_subset hvX₂
      have hvX₁ : v ∈ X₁.vertexSet :=
        (hs₁.vertexSet_union.symm ▸ hvG).resolve_right hv_not_Y₁
      have hvY₂ : v ∈ Y₂.vertexSet := hX₁_le_Y₂.vertexSet_subset hvX₁
      have hU_swap : X₂ ∪ X₁ ∪ A₃ = G := by
        rw [union_comm X₂ X₁]
        exact hU_X
      obtain ⟨_, hclaim3⟩ := theorem_4_5_claim_3 hsep hord hax1 hi hx₂ hU_swap hmin1_X₂
        ⟨hvX₂, hvY₂⟩
      obtain ⟨e, heX₂, hincX₂⟩ := hclaim3 (Or.inl hvX₁)
      have heY₁ : e ∈ Y₁.edgeSet := hEX₂_sub heX₂
      have hincG : G.Inc e v := inc_of_le hs₂.left_le hincX₂
      have hincY₁ : Y₁.Inc e v := (inc_iff_of_le hs₁.right_le heY₁).2 hincG
      exact hv_not_Y₁ (Y₁.vertex_mem_of_inc hincY₁)
    exact (le_iff_of_le hs₂.left_le hs₁.right_le).2 ⟨hVX₂_sub, hEX₂_sub⟩
  have hsum := separationOrder_inter_union_add_union_inter (hsep h₁) (hsep h₂)
  have hcomm_ord : separationOrder (A₁ ∪ B₂) (B₁ ∩ A₂) = separationOrder (A₂ ∩ B₁) (B₂ ∪ A₁) := by
    rw [separationOrder_comm, union_comm B₂ A₁, inter_comm A₂ B₁]
  rw [hcomm_ord] at hsum
  by_cases hle1 : separationOrder (A₁ ∩ B₂) (B₁ ∪ A₂) ≤ separationOrder A₁ B₁
  · exact hstep h₁ h₂ hU
      (fun A₂' B₂' hm hU' ↦ hmin1_2 hm (by rwa [union_comm A₁ A₂']))
      hmin2_1 hle1
  · have hle2 : separationOrder (A₂ ∩ B₁) (B₂ ∪ A₁) ≤ separationOrder A₂ B₂ := by omega
    have hU_swap : A₂ ∪ A₁ ∪ A₃ = G := by rw [union_comm A₂ A₁]; exact hU
    obtain ⟨h21, h12⟩ := hstep h₂ h₁ hU_swap
      (fun A₁' B₁' hm hU' ↦ hmin1_1 hm hU')
      (fun A₂' B₂' hm hU' hle ↦ hmin2_2 hm (by rwa [union_comm A₁ A₂']) hle)
      hle2
    exact ⟨h12, h21⟩

/-- **Graph Minors X, (4.5)** (page 167):
"Let $\theta \ge 2$, and let $\mathscr{T}$ be a set of separations of a hypergraph $G$, each
of order $< \theta$. Suppose that the first tangle axiom holds, and* (i) *if $(A_1, B_1),
(A_2, B_2) \in \mathscr{T}$ then $B_1 \not\subseteq A_2$* (ii) *there do not exist
subhypergraphs $A_1, A_2, A_3 \subseteq G$, mutually edge-disjoint, with $A_1 \cup A_2 \cup
A_3 = G$ and with $(A_1, A_2 \cup A_3)$, $(A_2, A_3 \cup A_1)$, $(A_3, A_1 \cup A_2)$ all in
$\mathscr{T}$.* *Then the second tangle axiom holds." -/
theorem theorem_4_5_proof {G : Hypergraph α β} {θ : ℕ} (_hθ : 2 ≤ θ)
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)}
    (hsep : ∀ ⦃A B : Hypergraph α β⦄, (A, B) ∈ 𝒯 → G.IsSeparation A B)
    (hord : ∀ ⦃A B : Hypergraph α β⦄, (A, B) ∈ 𝒯 → separationOrder A B < θ)
    (hax1 : TangleAxiom1 G θ 𝒯)
    (hi : ∀ ⦃A₁ B₁ A₂ B₂ : Hypergraph α β⦄, (A₁, B₁) ∈ 𝒯 → (A₂, B₂) ∈ 𝒯 → ¬ B₁ ≤ A₂)
    (hii : ¬ ∃ A₁ A₂ A₃ : Hypergraph α β,
      A₁ ≤ G ∧ A₂ ≤ G ∧ A₃ ≤ G ∧
      Disjoint A₁.edgeSet A₂.edgeSet ∧
      Disjoint A₁.edgeSet A₃.edgeSet ∧
      Disjoint A₂.edgeSet A₃.edgeSet ∧
      A₁ ∪ A₂ ∪ A₃ = G ∧
      (A₁, A₂ ∪ A₃) ∈ 𝒯 ∧ (A₂, A₃ ∪ A₁) ∈ 𝒯 ∧ (A₃, A₁ ∪ A₂) ∈ 𝒯) :
    TangleAxiom2 G 𝒯 := by
  unfold TangleAxiom2
  by_contra! hnot2
  rcases hnot2 with ⟨A₁₀, B₁₀, A₂₀, B₂₀, A₃₀, B₃₀, h₁₀, h₂₀, h₃₀, hU₀⟩
  let score1 (A₁ B₁ A₂ B₂ A₃ B₃ : Hypergraph α β) : ℕ :=
    separationOrder A₁ B₁ + separationOrder A₂ B₂ + separationOrder A₃ B₃
  let score2 (A₁ A₂ A₃ : Hypergraph α β) : ℕ :=
    (A₁.vertexSet.ncard + A₁.edgeSet.ncard) +
    (A₂.vertexSet.ncard + A₂.edgeSet.ncard) +
    (A₃.vertexSet.ncard + A₃.edgeSet.ncard)
  let S₁ : Set ℕ :=
    {n : ℕ | ∃ A₁ B₁ A₂ B₂ A₃ B₃,
      (A₁, B₁) ∈ 𝒯 ∧ (A₂, B₂) ∈ 𝒯 ∧ (A₃, B₃) ∈ 𝒯 ∧
      A₁ ∪ A₂ ∪ A₃ = G ∧ score1 A₁ B₁ A₂ B₂ A₃ B₃ = n}
  have hS₁_ne : S₁.Nonempty :=
    ⟨score1 A₁₀ B₁₀ A₂₀ B₂₀ A₃₀ B₃₀, A₁₀, B₁₀, A₂₀, B₂₀, A₃₀, B₃₀, h₁₀, h₂₀, h₃₀, hU₀, rfl⟩
  obtain ⟨A₁₁, B₁₁, A₂₁, B₂₁, A₃₁, B₃₁, h₁₁, h₂₁, h₃₁, hU₁, hs₁_min⟩ := Nat.sInf_mem hS₁_ne
  let s₁_opt := sInf S₁
  let S₂ : Set ℕ :=
    {n : ℕ | ∃ A₁ B₁ A₂ B₂ A₃ B₃,
      (A₁, B₁) ∈ 𝒯 ∧ (A₂, B₂) ∈ 𝒯 ∧ (A₃, B₃) ∈ 𝒯 ∧
      A₁ ∪ A₂ ∪ A₃ = G ∧ score1 A₁ B₁ A₂ B₂ A₃ B₃ = s₁_opt ∧ score2 A₁ A₂ A₃ = n}
  have hS₂_ne : S₂.Nonempty :=
    ⟨score2 A₁₁ A₂₁ A₃₁, A₁₁, B₁₁, A₂₁, B₂₁, A₃₁, B₃₁, h₁₁, h₂₁, h₃₁, hU₁, hs₁_min, rfl⟩
  obtain ⟨A₁, B₁, A₂, B₂, A₃, B₃, h₁, h₂, h₃, hU, hs₁_eq, hs₂_min⟩ := Nat.sInf_mem hS₂_ne
  have hmin1_all : ∀ A₁' B₁' A₂' B₂' A₃' B₃',
      (A₁', B₁') ∈ 𝒯 → (A₂', B₂') ∈ 𝒯 → (A₃', B₃') ∈ 𝒯 → A₁' ∪ A₂' ∪ A₃' = G →
      score1 A₁ B₁ A₂ B₂ A₃ B₃ ≤ score1 A₁' B₁' A₂' B₂' A₃' B₃' := by
    intro A₁' B₁' A₂' B₂' A₃' B₃' hm1 hm2 hm3 hU'
    rw [hs₁_eq]
    exact Nat.sInf_le ⟨A₁', B₁', A₂', B₂', A₃', B₃', hm1, hm2, hm3, hU', rfl⟩
  have hmin2_all : ∀ A₁' B₁' A₂' B₂' A₃' B₃',
      (A₁', B₁') ∈ 𝒯 → (A₂', B₂') ∈ 𝒯 → (A₃', B₃') ∈ 𝒯 → A₁' ∪ A₂' ∪ A₃' = G →
      score1 A₁' B₁' A₂' B₂' A₃' B₃' ≤ score1 A₁ B₁ A₂ B₂ A₃ B₃ →
      score2 A₁ A₂ A₃ ≤ score2 A₁' A₂' A₃' := by
    intro A₁' B₁' A₂' B₂' A₃' B₃' hm1 hm2 hm3 hU' hle1
    have hge1 := hmin1_all A₁' B₁' A₂' B₂' A₃' B₃' hm1 hm2 hm3 hU'
    have heq1 : score1 A₁' B₁' A₂' B₂' A₃' B₃' = s₁_opt := by omega
    rw [hs₂_min]
    exact Nat.sInf_le ⟨A₁', B₁', A₂', B₂', A₃', B₃', hm1, hm2, hm3, hU', heq1, rfl⟩
  have hmin1_1 : ∀ ⦃A₁' B₁' : Hypergraph α β⦄, (A₁', B₁') ∈ 𝒯 → A₁' ∪ A₂ ∪ A₃ = G →
      separationOrder A₁ B₁ ≤ separationOrder A₁' B₁' := by
    intro A₁' B₁' hm hU'
    have := hmin1_all A₁' B₁' A₂ B₂ A₃ B₃ hm h₂ h₃ hU'
    dsimp [score1] at this
    omega
  have hmin1_2 : ∀ ⦃A₂' B₂' : Hypergraph α β⦄, (A₂', B₂') ∈ 𝒯 → A₁ ∪ A₂' ∪ A₃ = G →
      separationOrder A₂ B₂ ≤ separationOrder A₂' B₂' := by
    intro A₂' B₂' hm hU'
    have := hmin1_all A₁ B₁ A₂' B₂' A₃ B₃ h₁ hm h₃ hU'
    dsimp [score1] at this
    omega
  have hmin1_3 : ∀ ⦃A₃' B₃' : Hypergraph α β⦄, (A₃', B₃') ∈ 𝒯 → A₁ ∪ A₂ ∪ A₃' = G →
      separationOrder A₃ B₃ ≤ separationOrder A₃' B₃' := by
    intro A₃' B₃' hm hU'
    have := hmin1_all A₁ B₁ A₂ B₂ A₃' B₃' h₁ h₂ hm hU'
    dsimp [score1] at this
    omega
  have hmin2_1 : ∀ ⦃A₁' B₁' : Hypergraph α β⦄, (A₁', B₁') ∈ 𝒯 → A₁' ∪ A₂ ∪ A₃ = G →
      separationOrder A₁' B₁' ≤ separationOrder A₁ B₁ →
      A₁.vertexSet.ncard + A₁.edgeSet.ncard ≤ A₁'.vertexSet.ncard + A₁'.edgeSet.ncard := by
    intro A₁' B₁' hm hU' hle
    have := hmin2_all A₁' B₁' A₂ B₂ A₃ B₃ hm h₂ h₃ hU' (by dsimp [score1]; omega)
    dsimp [score2] at this
    omega
  have hmin2_2 : ∀ ⦃A₂' B₂' : Hypergraph α β⦄, (A₂', B₂') ∈ 𝒯 → A₁ ∪ A₂' ∪ A₃ = G →
      separationOrder A₂' B₂' ≤ separationOrder A₂ B₂ →
      A₂.vertexSet.ncard + A₂.edgeSet.ncard ≤ A₂'.vertexSet.ncard + A₂'.edgeSet.ncard := by
    intro A₂' B₂' hm hU' hle
    have := hmin2_all A₁ B₁ A₂' B₂' A₃ B₃ h₁ hm h₃ hU' (by dsimp [score1]; omega)
    dsimp [score2] at this
    omega
  have hmin2_3 : ∀ ⦃A₃' B₃' : Hypergraph α β⦄, (A₃', B₃') ∈ 𝒯 → A₁ ∪ A₂ ∪ A₃' = G →
      separationOrder A₃' B₃' ≤ separationOrder A₃ B₃ →
      A₃.vertexSet.ncard + A₃.edgeSet.ncard ≤ A₃'.vertexSet.ncard + A₃'.edgeSet.ncard := by
    intro A₃' B₃' hm hU' hle
    have := hmin2_all A₁ B₁ A₂ B₂ A₃' B₃' h₁ h₂ hm hU' (by dsimp [score1]; omega)
    dsimp [score2] at this
    omega
  have hs₁ := hsep h₁
  have hs₂ := hsep h₂
  have hs₃ := hsep h₃
  obtain ⟨h12, h21⟩ := theorem_4_5_claim_4 hsep hord hax1 hi h₁ h₂ hs₃.left_le hU
    hmin1_1 hmin1_2 hmin2_1 hmin2_2
  have hU_132 : A₁ ∪ A₃ ∪ A₂ = G := by
    rw [union_assoc, union_comm A₃ A₂, ← union_assoc, hU]
  obtain ⟨h13, h31⟩ := theorem_4_5_claim_4 hsep hord hax1 hi h₁ h₃ hs₂.left_le hU_132
    (fun A₁' B₁' hm hU' ↦ hmin1_1 hm (by rw [union_assoc, union_comm A₂ A₃, ← union_assoc, hU']))
    (fun A₃' B₃' hm hU' ↦ hmin1_3 hm (by rw [union_assoc, union_comm A₂ A₃', ← union_assoc, hU']))
    (fun A₁' B₁' hm hU' hle ↦ hmin2_1 hm
      (by rw [union_assoc, union_comm A₂ A₃, ← union_assoc, hU']) hle)
    (fun A₃' B₃' hm hU' hle ↦ hmin2_3 hm
      (by rw [union_assoc, union_comm A₂ A₃', ← union_assoc, hU']) hle)
  have hU_231 : A₂ ∪ A₃ ∪ A₁ = G := by
    rw [union_comm A₂ A₃, union_assoc, union_comm A₃ (A₂ ∪ A₁), union_comm A₂ A₁, hU]
  obtain ⟨h23, h32⟩ := theorem_4_5_claim_4 hsep hord hax1 hi h₂ h₃ hs₁.left_le hU_231
    (fun A₂' B₂' hm hU' ↦ hmin1_2 hm (by
      rw [union_comm A₁ A₂', union_assoc, union_comm A₁ A₃, ← union_assoc, hU']))
    (fun A₃' B₃' hm hU' ↦ hmin1_3 hm (by
      rw [union_comm A₁ A₂, union_assoc, union_comm A₁ A₃', ← union_assoc, hU']))
    (fun A₂' B₂' hm hU' hle ↦ hmin2_2 hm (by
      rw [union_comm A₁ A₂', union_assoc, union_comm A₁ A₃, ← union_assoc, hU']) hle)
    (fun A₃' B₃' hm hU' hle ↦ hmin2_3 hm (by
      rw [union_comm A₁ A₂, union_assoc, union_comm A₁ A₃', ← union_assoc, hU']) hle)
  have hdisj12 : Disjoint A₁.edgeSet A₂.edgeSet :=
    hs₂.disjoint_edgeSet.mono_right h12.edgeSet_subset |>.symm
  have hdisj13 : Disjoint A₁.edgeSet A₃.edgeSet :=
    hs₃.disjoint_edgeSet.mono_right h13.edgeSet_subset |>.symm
  have hdisj23 : Disjoint A₂.edgeSet A₃.edgeSet :=
    hs₃.disjoint_edgeSet.mono_right h23.edgeSet_subset |>.symm
  have hmem_pair : ∀ {X Y Z W : Hypergraph α β},
      (X, W) ∈ 𝒯 → Y ≤ W → Z ≤ W → X ∪ (Y ∪ Z) = G → (X, Y ∪ Z) ∈ 𝒯 := by
    intro X Y Z W hXW hYW hZW hXYZ
    have hsXW := hsep hXW
    have hYZ_le_W : Y ∪ Z ≤ W :=
      (le_iff_of_le (union_le (hYW.trans hsXW.right_le) (hZW.trans hsXW.right_le)) hsXW.right_le).2
        ⟨Set.union_subset hYW.vertexSet_subset hZW.vertexSet_subset,
         Set.union_subset hYW.edgeSet_subset hZW.edgeSet_subset⟩
    have hsep_XYZ : G.IsSeparation X (Y ∪ Z) := by
      refine ⟨hsXW.left_le, hYZ_le_W.trans hsXW.right_le, hXYZ, ?_⟩
      exact Set.Subset.antisymm
        ((Set.inter_subset_inter_right _ hYZ_le_W.edgeSet_subset).trans
          hsXW.edgeSet_inter_eq.subset)
        (Set.empty_subset _)
    have hord_XYZ : separationOrder X (Y ∪ Z) < θ := by
      have hsub : (X ∩ (Y ∪ Z)).vertexSet ⊆ (X ∩ W).vertexSet :=
        Set.inter_subset_inter_right _ hYZ_le_W.vertexSet_subset
      exact (Set.ncard_le_ncard hsub (X ∩ W).vertexSet_finite).trans_lt (hord hXW)
    exact mem_of_left_le hax1 hi hXW hsep_XYZ hord_XYZ le_rfl
  have hm1 : (A₁, A₂ ∪ A₃) ∈ 𝒯 :=
    hmem_pair h₁ h21 h31 (by rw [← union_assoc, hU])
  have hm2 : (A₂, A₃ ∪ A₁) ∈ 𝒯 :=
    hmem_pair h₂ h32 h12 (by rw [← union_assoc, hU_231])
  have hm3 : (A₃, A₁ ∪ A₂) ∈ 𝒯 :=
    hmem_pair h₃ h13 h23 (by rw [union_comm A₃ (A₁ ∪ A₂), hU])
  exact hii ⟨A₁, A₂, A₃, hs₁.left_le, hs₂.left_le, hs₃.left_le,
    hdisj12, hdisj13, hdisj23, hU, hm1, hm2, hm3⟩

/-! ## Complete graphs: (4.4) -/

private theorem ncard_univ_fin (n : ℕ) : (Set.univ : Set (Fin n)).ncard = n := by
  rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]

private theorem ncard_le_of_injOn_fin {n θ : ℕ} {W : Set (Fin n)} {f : Fin n → Fin θ}
    (hf : Set.InjOn f W) : W.ncard ≤ θ := by
  rw [← hf.ncard_image]
  exact (Set.ncard_le_ncard (Set.subset_univ _) Set.finite_univ).trans_eq (ncard_univ_fin θ)

private theorem ends_completeGraph_pair {n : ℕ} {u v : Fin n} (hne : u ≠ v) :
    (completeGraph n).ends s(u, v) = {u, v} := by
  ext x
  simp [completeGraph, Hypergraph.ends, Sym2.mk_isDiag_iff, hne]

private theorem edgeSize_completeGraph_pair {n : ℕ} {u v : Fin n} (hne : u ≠ v) :
    edgeSize (completeGraph n) s(u, v) = 2 := by
  rw [edgeSize, ends_completeGraph_pair hne, Set.ncard_pair hne]

private theorem maxEdgeSize_completeGraph_of_le_one {n : ℕ} (hn : n ≤ 1) :
    maxEdgeSize (completeGraph n) = 0 := by
  rw [maxEdgeSize_eq_zero_iff]
  rintro e he v _
  induction e using Sym2.ind with
  | _ u w =>
    have hne : u ≠ w := by simpa [completeGraph, Sym2.mk_isDiag_iff] using he
    omega

private theorem maxEdgeSize_completeGraph_of_two_le {n : ℕ} (hn : 2 ≤ n) :
    maxEdgeSize (completeGraph n) = 2 := by
  have hle : maxEdgeSize (completeGraph n) ≤ 2 := by
    rw [maxEdgeSize_le_iff]
    intro e he
    induction e using Sym2.ind with
    | _ u v =>
      have hne : u ≠ v := by simpa [completeGraph, Sym2.mk_isDiag_iff] using he
      rw [edgeSize_completeGraph_pair hne]
  let u₀ : Fin n := ⟨0, by omega⟩
  let v₀ : Fin n := ⟨1, by omega⟩
  have hne01 : u₀ ≠ v₀ := by simp [u₀, v₀, Fin.ext_iff]
  have he01 : s(u₀, v₀) ∈ (completeGraph n).edgeSet := by
    simp [completeGraph, Sym2.mk_isDiag_iff, hne01]
  have hge : 2 ≤ maxEdgeSize (completeGraph n) := by
    rw [← edgeSize_completeGraph_pair hne01]
    exact edgeSize_le_maxEdgeSize he01
  omega

private def completeLeftOf {n : ℕ} (W : Set (Fin n)) : Hypergraph (Fin n) (Sym2 (Fin n)) where
  vertexSet := W
  edgeSet := {e : Sym2 (Fin n) | ¬ e.IsDiag ∧ ∀ v ∈ e, v ∈ W}
  Inc e v := (¬ e.IsDiag ∧ ∀ u ∈ e, u ∈ W) ∧ v ∈ e
  vertex_mem_of_inc _ _ h := h.1.2 _ h.2
  edge_mem_of_inc _ _ h := h.1
  vertexSet_finite := Set.toFinite _
  edgeSet_finite := Set.toFinite _

private def completeRightOf {n : ℕ} (W : Set (Fin n)) : Hypergraph (Fin n) (Sym2 (Fin n)) where
  vertexSet := Set.univ
  edgeSet := {e : Sym2 (Fin n) | ¬ e.IsDiag ∧ ¬ ∀ v ∈ e, v ∈ W}
  Inc e v := (¬ e.IsDiag ∧ ¬ ∀ u ∈ e, u ∈ W) ∧ v ∈ e
  vertex_mem_of_inc _ _ _ := Set.mem_univ _
  edge_mem_of_inc _ _ h := h.1
  vertexSet_finite := Set.finite_univ
  edgeSet_finite := Set.toFinite _

/-- Upper bound in `(4.4)`: for `n ≥ 2`, `θ(K_n) ≤ ⌈(2/3)n⌉ = (2 * n + 2) / 3`. -/
private theorem tangleNumber_completeGraph_le {n : ℕ} (hn : 2 ≤ n) :
    tangleNumber (completeGraph n) ≤ (2 * n + 2) / 3 := by
  let θ := (2 * n + 2) / 3
  have hθ_pos : 2 ≤ θ := by omega
  by_contra! hgt
  obtain ⟨𝒯, h𝒯⟩ := exists_isTangle_of_le_tangleNumber (by omega) hgt
  have hmem_of_ncard_le : ∀ W : Set (Fin n), W.ncard ≤ θ →
      (completeLeftOf W, completeRightOf W) ∈ 𝒯 := by
    intro W hW
    have hL : completeLeftOf W ≤ completeGraph n :=
      { vertexSet_subset := Set.subset_univ _
        edgeSet_subset := fun _ h ↦ h.1
        ends_eq := fun e he ↦ by
          ext v; exact ⟨fun h ↦ ⟨he, h.2⟩, fun h ↦ ⟨h.1.1, h.2⟩⟩ }
    have hR : completeRightOf W ≤ completeGraph n :=
      { vertexSet_subset := subset_rfl
        edgeSet_subset := fun _ h ↦ h.1
        ends_eq := fun e he ↦ by
          ext v; exact ⟨fun h ↦ ⟨he, h.2⟩, fun h ↦ ⟨h.1.1, h.2⟩⟩ }
    have hsep : (completeGraph n).IsSeparation (completeLeftOf W) (completeRightOf W) := by
      rw [isSeparation_iff_of_le hL hR]
      refine ⟨Set.union_univ W, ?_, ?_⟩
      · ext e
        simp only [completeLeftOf, completeRightOf, completeGraph, Set.mem_union, Set.mem_ofPred_eq]
        tauto
      · ext e
        change (¬ e.IsDiag ∧ ∀ v ∈ e, v ∈ W) ∧ (¬ e.IsDiag ∧ ¬ ∀ v ∈ e, v ∈ W) ↔ False
        tauto
    have hord : separationOrder (completeLeftOf W) (completeRightOf W) < θ + 1 := by
      have : ((completeLeftOf W) ∩ (completeRightOf W)).vertexSet = W := by
        simp [inter_vertexSet, completeLeftOf, completeRightOf]
      rw [separationOrder, this]
      omega
    exact (h𝒯.axiom1 hsep hord).resolve_right fun hR_mem ↦ h𝒯.axiom3 hR_mem rfl
  let a := n / 3
  let W₁ : Set (Fin n) := {i : Fin n | a ≤ i.1}
  let W₂ : Set (Fin n) := {i : Fin n | i.1 < a ∨ 2 * a ≤ i.1}
  let W₃ : Set (Fin n) := {i : Fin n | i.1 < 2 * a}
  have hW₁ : W₁.ncard ≤ θ := by
    let f₁ (i : Fin n) : Fin θ :=
      ⟨if i.1 - a < θ then i.1 - a else 0, by split_ifs with h <;> omega⟩
    refine ncard_le_of_injOn_fin (f := f₁) ?_
    intro i hi j hj heq
    have hi' : i.1 - a < θ := by have := hi; have := i.2; omega
    have hj' : j.1 - a < θ := by have := hj; have := j.2; omega
    have hval : (f₁ i).1 = (f₁ j).1 := congrArg Fin.val heq
    simp only [f₁, hi', hj', ↓reduceIte] at hval
    have : a ≤ i.1 := hi
    have : a ≤ j.1 := hj
    exact Fin.ext (by omega)
  have hW₂ : W₂.ncard ≤ θ := by
    let g₂ (i : Fin n) : ℕ := if i.1 < a then i.1 else i.1 - a
    let f₂ (i : Fin n) : Fin θ :=
      ⟨if g₂ i < θ then g₂ i else 0, by split_ifs with h <;> omega⟩
    refine ncard_le_of_injOn_fin (f := f₂) ?_
    intro i hi j hj heq
    have hi' : g₂ i < θ := by
      dsimp [g₂]
      rcases hi with h | h <;> have := i.2 <;> split_ifs <;> omega
    have hj' : g₂ j < θ := by
      dsimp [g₂]
      rcases hj with h | h <;> have := j.2 <;> split_ifs <;> omega
    have hval : (f₂ i).1 = (f₂ j).1 := congrArg Fin.val heq
    simp only [f₂, hi', hj', ↓reduceIte] at hval
    dsimp [g₂] at hval
    rcases hi with hi1 | hi2 <;> rcases hj with hj1 | hj2 <;>
      split_ifs at hval <;> exact Fin.ext (by omega)
  have hW₃ : W₃.ncard ≤ θ := by
    let f₃ (i : Fin n) : Fin θ :=
      ⟨if i.1 < θ then i.1 else 0, by split_ifs with h <;> omega⟩
    refine ncard_le_of_injOn_fin (f := f₃) ?_
    intro i hi j hj heq
    have hi' : i.1 < θ := by have : i.1 < 2 * a := hi; omega
    have hj' : j.1 < θ := by have : j.1 < 2 * a := hj; omega
    have hval : (f₃ i).1 = (f₃ j).1 := congrArg Fin.val heq
    simp only [f₃, hi', hj', ↓reduceIte] at hval
    exact Fin.ext hval
  have hm₁ := hmem_of_ncard_le W₁ hW₁
  have hm₂ := hmem_of_ncard_le W₂ hW₂
  have hm₃ := hmem_of_ncard_le W₃ hW₃
  apply theorem_2_3_proof h𝒯 (by omega) hm₁ hm₂ hm₃
  ext e
  simp only [union_edgeSet, completeLeftOf, completeGraph, Set.mem_union, Set.mem_ofPred_eq]
  constructor
  · rintro ((⟨h, _⟩ | ⟨h, _⟩) | ⟨h, _⟩) <;> exact h
  · intro he
    induction e using Sym2.ind with
    | _ u v =>
      simp only [Sym2.mem_iff, forall_eq_or_imp, forall_eq]
      have hcov : (u ∈ W₁ ∧ v ∈ W₁) ∨ (u ∈ W₂ ∧ v ∈ W₂) ∨ (u ∈ W₃ ∧ v ∈ W₃) := by
        simp only [W₁, W₂, W₃, Set.mem_ofPred_eq]
        omega
      rcases hcov with h1 | h2 | h3
      · exact Or.inl (Or.inl ⟨he, h1⟩)
      · exact Or.inl (Or.inr ⟨he, h2⟩)
      · exact Or.inr ⟨he, h3⟩

/-- Lower bound in `(4.4)`: for `n ≥ 4`, `K_n` has a tangle of order `⌈(2/3)n⌉ = (2 * n + 2) / 3`
(Graph Minors X, Section 4, proof of (4.4), page 166). -/
private theorem le_tangleNumber_completeGraph_of_four_le {n : ℕ} (hn : 4 ≤ n) :
    (2 * n + 2) / 3 ≤ tangleNumber (completeGraph n) := by
  let G := completeGraph n
  let θ := (2 * n + 2) / 3
  have hθ_ge3 : 3 ≤ θ := by omega
  have hθ_lt_n : θ < n := by omega
  let 𝒯 : Set (Hypergraph (Fin n) (Sym2 (Fin n)) × Hypergraph (Fin n) (Sym2 (Fin n))) :=
    {p | G.IsSeparation p.1 p.2 ∧ p.1.vertexSet.ncard < θ}
  have h𝒯 : IsTangle G θ 𝒯 := by
    refine ⟨by omega, fun _ _ h ↦ h.1, ?_, ?_, ?_, ?_⟩
    · intro A B ⟨hsep, hlt⟩
      have hsub : (A ∩ B).vertexSet ⊆ A.vertexSet := Set.inter_subset_left
      exact (Set.ncard_le_ncard hsub A.vertexSet_finite).trans_lt hlt
    · intro A B hsep hord
      by_cases hVA : A.vertexSet = Set.univ
      · right
        refine ⟨hsep.symm, ?_⟩
        have : (A ∩ B).vertexSet = B.vertexSet := by
          simp [inter_vertexSet, hVA]
        rwa [separationOrder, this] at hord
      by_cases hVB : B.vertexSet = Set.univ
      · left
        refine ⟨hsep, ?_⟩
        have : (A ∩ B).vertexSet = A.vertexSet := by
          simp [inter_vertexSet, hVB]
        rwa [separationOrder, this] at hord
      · exfalso
        obtain ⟨u, _, hu_notA⟩ := Set.exists_of_ssubset
          (ssubset_of_subset_of_ne (Set.subset_univ _) hVA)
        obtain ⟨v, _, hv_notB⟩ := Set.exists_of_ssubset
          (ssubset_of_subset_of_ne (Set.subset_univ _) hVB)
        have huG : u ∈ G.vertexSet := Set.mem_univ u
        have hvG : v ∈ G.vertexSet := Set.mem_univ v
        have huB : u ∈ B.vertexSet :=
          (hsep.vertexSet_union.symm ▸ huG).resolve_left hu_notA
        have hvA : v ∈ A.vertexSet :=
          (hsep.vertexSet_union.symm ▸ hvG).resolve_right hv_notB
        have hne : u ≠ v := fun h ↦ hu_notA (h ▸ hvA)
        have heG : s(u, v) ∈ G.edgeSet := by
          simp [G, completeGraph, Sym2.mk_isDiag_iff, hne]
        rcases hsep.edgeSet_union.symm ▸ heG with heA | heB
        · have hincA : A.Inc s(u, v) u :=
            (inc_iff_of_le hsep.left_le heA).2 ⟨heG, Sym2.mem_mk_left u v⟩
          exact hu_notA (A.vertex_mem_of_inc hincA)
        · have hincB : B.Inc s(u, v) v :=
            (inc_iff_of_le hsep.right_le heB).2 ⟨heG, Sym2.mem_mk_right u v⟩
          exact hv_notB (B.vertex_mem_of_inc hincB)
    · intro A₁ B₁ A₂ B₂ A₃ B₃ ⟨hs₁, hlt₁⟩ ⟨hs₂, hlt₂⟩ ⟨hs₃, hlt₃⟩ hU
      let V₁ := A₁.vertexSet
      let V₂ := A₂.vertexSet
      let V₃ := A₃.vertexSet
      change V₁.ncard < θ at hlt₁
      change V₂.ncard < θ at hlt₂
      change V₃.ncard < θ at hlt₃
      have hV_union : V₁ ∪ V₂ ∪ V₃ = Set.univ := congrArg Hypergraph.vertexSet hU
      have hex_v : ∃ v : Fin n, v ∉ (V₁ ∩ V₂) ∪ ((V₁ ∪ V₂) ∩ V₃) := by
        by_contra! hall
        have huniv : (V₁ ∩ V₂) ∪ ((V₁ ∪ V₂) ∩ V₃) = Set.univ :=
          Set.eq_univ_of_forall hall
        have heq1 := Set.ncard_union_add_ncard_inter V₁ V₂
          (Set.toFinite V₁) (Set.toFinite V₂)
        have heq2 := Set.ncard_union_add_ncard_inter (V₁ ∪ V₂) V₃
          (Set.toFinite (V₁ ∪ V₂)) (Set.toFinite V₃)
        have hle3 := Set.ncard_union_le (V₁ ∩ V₂) ((V₁ ∪ V₂) ∩ V₃)
        rw [hV_union, ncard_univ_fin] at heq2
        rw [huniv, ncard_univ_fin] at hle3
        omega
      obtain ⟨v, hv_not⟩ := hex_v
      have hv_in : v ∈ V₁ ∪ V₂ ∪ V₃ := hV_union.symm ▸ Set.mem_univ v
      have hnot_12 : v ∉ V₁ ∩ V₂ := fun h ↦ hv_not (Or.inl h)
      have hnot_123 : v ∉ (V₁ ∪ V₂) ∩ V₃ := fun h ↦ hv_not (Or.inr h)
      have hcases : (v ∉ V₁ ∧ v ∉ V₂ ∧ v ∈ V₃) ∨
          (v ∉ V₁ ∧ v ∉ V₃ ∧ v ∈ V₂) ∨
          (v ∉ V₂ ∧ v ∉ V₃ ∧ v ∈ V₁) := by
        simp only [Set.mem_union, Set.mem_inter_iff] at hv_in hnot_12 hnot_123
        tauto
      have hno_pair : ∀ {X Y Z : Hypergraph (Fin n) (Sym2 (Fin n))},
          X ≤ G → Y ≤ G → Z ≤ G →
          X.edgeSet ∪ Y.edgeSet ∪ Z.edgeSet = G.edgeSet →
          Z.vertexSet.ncard < θ →
          v ∉ X.vertexSet → v ∉ Y.vertexSet → v ∈ Z.vertexSet → False := by
        intro X Y Z hX hY hZ hE_u hZ_lt hvX hvY hvZ
        have hZ_ne : Z.vertexSet ≠ Set.univ := by
          intro heq
          rw [heq, ncard_univ_fin] at hZ_lt
          omega
        obtain ⟨u, _, hu_notZ⟩ := Set.exists_of_ssubset
          (ssubset_of_subset_of_ne (Set.subset_univ _) hZ_ne)
        have hne : u ≠ v := fun h ↦ hu_notZ (h ▸ hvZ)
        have heG : s(u, v) ∈ G.edgeSet := by
          simp [G, completeGraph, Sym2.mk_isDiag_iff, hne]
        rcases hE_u.symm ▸ heG with (heX | heY) | heZ
        · have hinc : X.Inc s(u, v) v :=
            (inc_iff_of_le hX heX).2 ⟨heG, Sym2.mem_mk_right u v⟩
          exact hvX (X.vertex_mem_of_inc hinc)
        · have hinc : Y.Inc s(u, v) v :=
            (inc_iff_of_le hY heY).2 ⟨heG, Sym2.mem_mk_right u v⟩
          exact hvY (Y.vertex_mem_of_inc hinc)
        · have hinc : Z.Inc s(u, v) u :=
            (inc_iff_of_le hZ heZ).2 ⟨heG, Sym2.mem_mk_left u v⟩
          exact hu_notZ (Z.vertex_mem_of_inc hinc)
      have hE_union : A₁.edgeSet ∪ A₂.edgeSet ∪ A₃.edgeSet = G.edgeSet :=
        congrArg Hypergraph.edgeSet hU
      rcases hcases with ⟨h1, h2, h3⟩ | ⟨h1, h3, h2⟩ | ⟨h2, h3, h1⟩
      · exact hno_pair hs₁.left_le hs₂.left_le hs₃.left_le hE_union hlt₃ h1 h2 h3
      · exact hno_pair hs₁.left_le hs₃.left_le hs₂.left_le
          (by rw [Set.union_assoc, Set.union_comm A₃.edgeSet, ← Set.union_assoc, hE_union])
          hlt₂ h1 h3 h2
      · exact hno_pair hs₂.left_le hs₃.left_le hs₁.left_le
          (by rw [Set.union_comm (A₂.edgeSet ∪ A₃.edgeSet), ← Set.union_assoc, hE_union])
          hlt₁ h2 h3 h1
    · intro A B ⟨_, hlt⟩ hVA
      rw [hVA] at hlt
      change (Set.univ : Set (Fin n)).ncard < θ at hlt
      rw [ncard_univ_fin] at hlt
      omega
  exact h𝒯.le_tangleNumber

/-- For `n ≥ 3`, `branchWidth (completeGraph n) ≥ 2`. -/
private theorem two_le_branchWidth_completeGraph {n : ℕ} (hn : 3 ≤ n) :
    2 ≤ branchWidth (completeGraph n) := by
  let G := completeGraph n
  have hγ : 1 ≤ maxEdgeSize G := by
    rw [maxEdgeSize_completeGraph_of_two_le (by omega)]
    omega
  have hcard : 2 ≤ G.edgeSet.ncard := by
    let u₀ : Fin n := ⟨0, by omega⟩
    let u₁ : Fin n := ⟨1, by omega⟩
    let u₂ : Fin n := ⟨2, by omega⟩
    have h01 : u₀ ≠ u₁ := by simp [u₀, u₁, Fin.ext_iff]
    have h02 : u₀ ≠ u₂ := by simp [u₀, u₂, Fin.ext_iff]
    have h12 : u₁ ≠ u₂ := by simp [u₁, u₂, Fin.ext_iff]
    have hne_e : (s(u₀, u₁) : Sym2 (Fin n)) ≠ s(u₀, u₂) :=
      sym2_mk_eq_left_iff.not.2 h12
    have hsub : ({s(u₀, u₁), s(u₀, u₂)} : Set (Sym2 (Fin n))) ⊆ G.edgeSet := by
      rintro e (rfl | rfl) <;> simp [G, completeGraph, Sym2.mk_isDiag_iff, h01, h02]
    have hpair : ({s(u₀, u₁), s(u₀, u₂)} : Set (Sym2 (Fin n))).ncard = 2 :=
      Set.ncard_pair hne_e
    have hle := Set.ncard_le_ncard hsub G.edgeSet_finite
    omega
  obtain ⟨ι, _, T, τ, hbd, hw_eq⟩ := exists_branchDecomposition_eq_branchWidth hγ hcard
  rw [← hw_eq]
  have hT := hbd.isTernaryTree
  obtain ⟨u₀⟩ := hT.isTree.connected.nonempty
  obtain ⟨w₀, hadj₀⟩ : ∃ w₀, T.Adj u₀ w₀ := by
    by_cases hleaf₀ : IsLeaf T u₀
    · obtain ⟨w₀, hw₀, _⟩ := hT.exists_adj_of_isLeaf hleaf₀
      exact ⟨w₀, hw₀⟩
    · obtain ⟨w₀, _, _, _, _, _, hiff⟩ := hT.exists_three_adj_of_not_isLeaf hleaf₀
      exact ⟨w₀, (hiff w₀).2 (Or.inl rfl)⟩
  obtain ⟨t₀, ht₀_leaf, _⟩ := exists_leaf_in_treeComponent hT hadj₀
  obtain ⟨w, hadj_t₀⟩ := hT.exists_adj_of_isLeaf ht₀_leaf
  have hcomp_t₀ : treeComponent T t₀ s(t₀, w) = {t₀} :=
    treeComponent_eq_singleton_of_isLeaf hT hadj_t₀.1 ht₀_leaf
  have he₀_G : τ t₀ ∈ G.edgeSet := hbd.bijOn.mapsTo ht₀_leaf
  obtain ⟨u, v, huv_ne, hτ_t₀⟩ : ∃ u v : Fin n, u ≠ v ∧ τ t₀ = s(u, v) := by
    rcases Sym2.exists.1 ⟨τ t₀, rfl⟩ with ⟨u, v, heq⟩
    rw [heq] at he₀_G
    exact ⟨u, v, by simpa [G, completeGraph, Sym2.mk_isDiag_iff] using he₀_G, heq⟩
  have hex_z : ∃ z : Fin n, z ≠ u ∧ z ≠ v := by
    have hne_univ : ({u, v} : Set (Fin n)) ≠ Set.univ := by
      intro heq
      have h1 : ({u, v} : Set (Fin n)).ncard = 2 := Set.ncard_pair huv_ne
      rw [heq, ncard_univ_fin] at h1
      omega
    obtain ⟨z, _, hz⟩ := Set.exists_of_ssubset
      (ssubset_of_subset_of_ne (Set.subset_univ _) hne_univ)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hz
    exact ⟨z, hz⟩
  obtain ⟨z, hzu, hzv⟩ := hex_z
  have hsub_uv : ({u, v} : Set (Fin n)) ⊆
      {x ∈ G.vertexSet | ∃ t₁ ∈ leafSet T, ∃ t₂ ∈ leafSet T,
        ¬ (T.deleteEdges {s(t₀, w)}).Reachable t₁ t₂ ∧ G.Inc (τ t₁) x ∧ G.Inc (τ t₂) x} := by
    have hmem_of : ∀ x y : Fin n, x ≠ y → z ≠ x → z ≠ y → τ t₀ = s(x, y) →
        x ∈ {x ∈ G.vertexSet | ∃ t₁ ∈ leafSet T, ∃ t₂ ∈ leafSet T,
          ¬ (T.deleteEdges {s(t₀, w)}).Reachable t₁ t₂ ∧ G.Inc (τ t₁) x ∧ G.Inc (τ t₂) x} := by
      intro x y hxy hzx hzy hτ_xy
      have he_xz : s(x, z) ∈ G.edgeSet := by
        simp [G, completeGraph, Sym2.mk_isDiag_iff, hzx.symm]
      obtain ⟨t₁, ht₁_leaf, hτ_t₁⟩ := hbd.bijOn.surjOn he_xz
      have ht₁_ne : t₁ ≠ t₀ := by
        intro hteq
        have heq_e : (s(x, z) : Sym2 (Fin n)) = s(x, y) := by
          rw [← hτ_t₁, hteq, hτ_xy]
        exact hzy (sym2_mk_eq_left_iff.1 heq_e)
      have ht₁_w : t₁ ∈ treeComponent T w s(w, t₀) := by
        apply (notMem_treeComponent_iff hT.isTree hadj_t₀.1).1
        rw [hcomp_t₀, Set.mem_singleton_iff]
        exact ht₁_ne
      refine ⟨Set.mem_univ x, t₀, ht₀_leaf, t₁, ht₁_leaf, ?_, ?_, ?_⟩
      · rw [not_reachable_deleteEdges_iff_treeComponent hT.isTree hadj_t₀.1]
        exact Or.inl ⟨Reachable.rfl, ht₁_w⟩
      · rw [hτ_xy]
        exact ⟨by simp [Sym2.mk_isDiag_iff, hxy], Sym2.mem_mk_left x y⟩
      · rw [hτ_t₁]
        exact ⟨he_xz, Sym2.mem_mk_left x z⟩
    rintro x (rfl | rfl)
    · exact hmem_of x v huv_ne hzu hzv hτ_t₀
    · exact hmem_of x u huv_ne.symm hzv hzu (hτ_t₀.trans Sym2.eq_swap)
  have hle1 : 2 ≤ branchEdgeOrder G T τ s(t₀, w) := by
    rw [← Set.ncard_pair huv_ne]
    exact Set.ncard_le_ncard hsub_uv (Set.toFinite _)
  exact hle1.trans (branchEdgeOrder_le_branchDecompWidth (T.mem_edgeSet.2 hadj_t₀.1))

/-- **Graph Minors X, (4.4)** (page 166):
"For $n \ge 0$, $K_n$ has tangle number $\lceil(2/3) n\rceil$, and for $n \ge 3$, it has
branch-width $\lceil(2/3) n\rceil$." -/
theorem theorem_4_4_proof (n : ℕ) :
    tangleNumber (completeGraph n) = (2 * n + 2) / 3 ∧
      (3 ≤ n → branchWidth (completeGraph n) = (2 * n + 2) / 3) := by
  have hθ : tangleNumber (completeGraph n) = (2 * n + 2) / 3 := by
    by_cases hn0 : n = 0
    · subst hn0
      have hemp : (completeGraph 0).vertexSet = ∅ := Set.eq_empty_of_isEmpty _
      rw [tangleNumber_eq_zero_iff.2 hemp]
    by_cases hn1 : n = 1
    · subst hn1
      have hne : (completeGraph 1).vertexSet.Nonempty := ⟨⟨0, by omega⟩, Set.mem_univ _⟩
      rw [tangleNumber_eq_one_of_maxEdgeSize_eq_zero
        (maxEdgeSize_completeGraph_of_le_one le_rfl) hne]
    by_cases hn3 : n ≤ 3
    · have hn2 : 2 ≤ n := by omega
      have hle := tangleNumber_completeGraph_le hn2
      have hge : 2 ≤ tangleNumber (completeGraph n) := by
        rw [← maxEdgeSize_completeGraph_of_two_le hn2]
        exact maxEdgeSize_le_tangleNumber (completeGraph n)
      omega
    · have hn4 : 4 ≤ n := by omega
      exact le_antisymm (tangleNumber_completeGraph_le (by omega))
        (le_tangleNumber_completeGraph_of_four_le hn4)
  refine ⟨hθ, fun hn3 ↦ ?_⟩
  have hγ2 : maxEdgeSize (completeGraph n) = 2 :=
    maxEdgeSize_completeGraph_of_two_le (by omega)
  have h43 := theorem_4_3_proof (completeGraph n) (by simp [hγ2])
  have hbw2 : 2 ≤ branchWidth (completeGraph n) :=
    two_le_branchWidth_completeGraph hn3
  rw [hγ2, hθ, max_eq_left hbw2] at h43
  exact h43

end GraphMinor.GM10
