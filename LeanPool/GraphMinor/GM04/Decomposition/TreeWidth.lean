/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM04.Decomposition.SubtreeHelly

/-!
# Tree-width and rotundity (Graph Minors IV, Section 5)

This file proves the main theorems of Graph Minors IV, Section 5 (pages 238–240):
- `theorem_5_2`: Graph Minors IV, (5.2), deduced from Thomas's lemma (5.1) (`ThomasStatement`) via
  claims (1)–(5) (`theorem_5_2_claim_1` through `theorem_5_2_claim_5`).
- `theorem_5_3`: Graph Minors IV, (5.3), deduced from (5.2) and (4.2).
-/

public section

namespace GraphMinor.GM04

open Hypergraph

universe u v

variable {α β ι : Type*}

/-- If `t₂` lies on the path of `T` from `t₁` to `t₁`, then `t₂ = t₁`. -/
private theorem RootedTree.eq_of_onPath_self {T : RootedTree ι} {t₁ t₂ : ι}
    (ht₁ : t₁ ∈ T.verts) (hon : T.OnPath t₁ t₁ t₂) : t₂ = t₁ := by
  have h₁ : T.Reaches t₂ t₁ := hon.1.elim id id
  have h₂ : T.Reaches t₁ t₂ := hon.2 t₁ (T.reaches_refl ht₁) (T.reaches_refl ht₁)
  exact T.reaches_antisymm h₁ h₂

/-- Given vertex bags `V : ι → Set α` on a tree `T` that cover `G.vertexSet`, contain the ends of
every edge of `G`, satisfy the path-interpolation property, and contain `G.rootSet` at `T.root`,
there is a tree-decomposition `(T, τ)` of `G` with `(τ t).vertexSet = V t` for all `t ∈ T.verts`. -/
theorem exists_isTreeDecomposition_of_ends_subset (G : RootedHypergraph α β) (T : RootedTree ι)
    (V : ι → Set α)
    (hV_sub : ∀ t ∈ T.verts, V t ⊆ G.vertexSet)
    (hV_union : (⋃ t ∈ T.verts, V t) = G.vertexSet)
    (hE : ∀ e ∈ G.edgeSet, ∃ t ∈ T.verts, G.ends e ⊆ V t)
    (hpath : ∀ t₁ ∈ T.verts, ∀ t₂ ∈ T.verts, ∀ t₃ ∈ T.verts,
      T.OnPath t₁ t₃ t₂ → V t₁ ∩ V t₃ ⊆ V t₂)
    (hroot : G.rootSet ⊆ V T.root) :
    ∃ τ : ι → RootedHypergraph α β,
      IsTreeDecomposition G T τ ∧ ∀ t ∈ T.verts, (τ t).vertexSet = V t := by
  classical
  have hfin : ∀ t ∈ T.verts, (V t).Finite :=
    fun t ht ↦ G.vertexSet_finite.subset (hV_sub t ht)
  have hex_owner : ∀ e : β, ∃ t : ι, e ∈ G.edgeSet → t ∈ T.verts ∧ G.ends e ⊆ V t := by
    intro e
    by_cases he : e ∈ G.edgeSet
    · obtain ⟨t, ht, hends⟩ := hE e he
      exact ⟨t, fun _ ↦ ⟨ht, hends⟩⟩
    · exact ⟨T.root, fun h ↦ False.elim (he h)⟩
  choose owner howner using hex_owner
  let τ : ι → RootedHypergraph α β := fun t ↦
    if ht : t ∈ T.verts then
      { vertexSet := V t
        edgeSet := {e ∈ G.edgeSet | owner e = t}
        Inc := fun e v ↦ e ∈ G.edgeSet ∧ owner e = t ∧ G.Inc e v
        vertex_mem_of_inc := fun {e v} h ↦ by
          rw [← h.2.1]
          exact (howner e h.1).2 h.2.2
        edge_mem_of_inc := fun {e v} h ↦ ⟨h.1, h.2.1⟩
        vertexSet_finite := hfin t ht
        edgeSet_finite := G.edgeSet_finite.subset (fun _ h ↦ h.1)
        roots := if t = T.root then G.roots else
          ((hfin t ht).subset (Set.inter_subset_left (t := V (T.parent t)))).toFinset.toList
        roots_nodup := by
          split_ifs
          · exact G.roots_nodup
          · exact Finset.nodup_toList _
        roots_subset := by
          intro v hv
          split_ifs at hv with htr
          · subst htr
            exact hroot hv
          · rw [Finset.mem_toList, Set.Finite.mem_toFinset] at hv
            exact hv.1 }
    else G
  have hτ_vert : ∀ t ∈ T.verts, (τ t).vertexSet = V t := by
    intro t ht
    simp [τ, ht]
  have hτ_edge : ∀ t ∈ T.verts, (τ t).edgeSet = {e ∈ G.edgeSet | owner e = t} := by
    intro t ht
    simp [τ, ht]
  have hτ_inc : ∀ t ∈ T.verts, ∀ e v, (τ t).Inc e v ↔ e ∈ G.edgeSet ∧ owner e = t ∧ G.Inc e v := by
    intro t ht e v
    simp [τ, ht]
  have h_inter_edge : ∀ t₁ ∈ T.verts, ∀ t₂ ∈ T.verts, t₁ ≠ t₂ →
      ((τ t₁).toHypergraph ∩ (τ t₂).toHypergraph).edgeSet = ∅ := by
    intro t₁ ht₁ t₂ ht₂ hne
    ext e
    simp only [inter_edgeSet, Set.mem_inter_iff, hτ_edge t₁ ht₁, hτ_edge t₂ ht₂,
      Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨⟨_, rfl⟩, ⟨_, h⟩⟩
    exact hne h
  refine ⟨τ, ?_, hτ_vert⟩
  refine
    { le := fun t ht ↦ ?_
      biUnion_eq := ?_
      edgeSet_inter_eq := h_inter_edge
      inter_le := fun t₁ ht₁ t₂ ht₂ t₃ ht₃ hon ↦ ?_
      roots_root := ?_
      rootSet_edge := fun f hf ↦ ?_ }
  · refine ⟨hτ_vert t ht ▸ hV_sub t ht, ?_, ?_⟩
    · rw [hτ_edge t ht]
      exact fun _ h ↦ h.1
    · intro e he
      rw [hτ_edge t ht] at he
      ext v
      simp only [Hypergraph.ends, Set.mem_ofPred_eq, hτ_inc t ht, he.1, he.2, true_and]
  · refine Hypergraph.ext ?_ ?_ ?_
    · ext v
      rw [← hV_union]
      simp only [biUnion_vertexSet, Set.mem_iUnion]
      refine ⟨fun ⟨t, ht, hv⟩ ↦ ⟨t, ht, hτ_vert t ht ▸ hv⟩,
        fun ⟨t, ht, hv⟩ ↦ ⟨t, ht, (hτ_vert t ht).symm ▸ hv⟩⟩
    · ext e
      simp only [biUnion_edgeSet, Set.mem_iUnion]
      refine ⟨?_, ?_⟩
      · rintro ⟨t, ht, he⟩
        rw [hτ_edge t ht] at he
        exact he.1
      · intro he
        refine ⟨owner e, (howner e he).1, ?_⟩
        rw [hτ_edge _ (howner e he).1]
        exact ⟨he, rfl⟩
    · funext e v
      apply propext
      simp only [biUnion_inc]
      refine ⟨?_, ?_⟩
      · rintro ⟨t, ht, hinc⟩
        rw [hτ_inc t ht] at hinc
        exact hinc.2.2
      · intro hinc
        have he : e ∈ G.edgeSet := G.edge_mem_of_inc hinc
        refine ⟨owner e, (howner e he).1, ?_⟩
        rw [hτ_inc _ (howner e he).1]
        exact ⟨he, rfl, hinc⟩
  · by_cases h₁₃ : t₁ = t₃
    · subst h₁₃
      have h₂₁ : t₂ = t₁ := T.eq_of_onPath_self ht₁ hon
      subst h₂₁
      exact Hypergraph.inter_le_left le_rfl le_rfl
    · refine ⟨?_, ?_, ?_⟩
      · simp only [inter_vertexSet, hτ_vert t₁ ht₁, hτ_vert t₂ ht₂, hτ_vert t₃ ht₃]
        exact hpath t₁ ht₁ t₂ ht₂ t₃ ht₃ hon
      · rw [h_inter_edge t₁ ht₁ t₃ ht₃ h₁₃]
        exact Set.empty_subset _
      · intro e he
        rw [h_inter_edge t₁ ht₁ t₃ ht₃ h₁₃] at he
        exact False.elim (Set.notMem_empty e he)
  · simp [τ, T.root_mem]
  · obtain ⟨hfv, hfr⟩ := T.mem_edges_iff.mp hf
    have hpv : T.parent f ∈ T.verts := T.parent_mem f hfv
    ext v
    simp only [RootedHypergraph.rootSet, Set.mem_ofPred_eq, inter_vertexSet,
      hτ_vert f hfv, hτ_vert (T.parent f) hpv]
    simp only [τ, hfv, ↓reduceDIte, hfr, ↓reduceIte, Finset.mem_toList, Set.Finite.mem_toFinset]

/-- Two vertices `u, v` of `G` are adjacent in the auxiliary simple graph `K` of the proof of
Graph Minors IV, (5.2) when `u ≠ v` and either some edge of `G` is incident with both `u` and `v`,
or `u, v ∈ G.rootSet`. -/
def completeRootAdj (G : RootedHypergraph α β) (u v : α) : Prop :=
  u ≠ v ∧ ((∃ e, G.Inc e u ∧ G.Inc e v) ∨ (u ∈ G.rootSet ∧ v ∈ G.rootSet))

private theorem completeRootAdj_symm {G : RootedHypergraph α β} {u v : α}
    (h : completeRootAdj G u v) : completeRootAdj G v u := by
  refine ⟨h.1.symm, ?_⟩
  rcases h.2 with ⟨e, hu, hv⟩ | ⟨hu, hv⟩
  · exact Or.inl ⟨e, hv, hu⟩
  · exact Or.inr ⟨hv, hu⟩

private theorem completeRootAdj_mem_left {G : RootedHypergraph α β} {u v : α}
    (h : completeRootAdj G u v) : u ∈ G.vertexSet := by
  rcases h.2 with ⟨e, hu, _⟩ | ⟨hu, _⟩
  · exact G.vertex_mem_of_inc hu
  · exact G.roots_subset u hu

private theorem completeRootAdj_mem_right {G : RootedHypergraph α β} {u v : α}
    (h : completeRootAdj G u v) : v ∈ G.vertexSet :=
  completeRootAdj_mem_left (completeRootAdj_symm h)

/-- The auxiliary simple graph `K` in the proof of Graph Minors IV, (5.2) (page 239), represented
as a hypergraph on `α` with edge type `Sym2 α`: its vertex set is `G.vertexSet`, and its edges are
the pairs `s(u, v)` with `completeRootAdj G u v`. -/
def completeRootHypergraph (G : RootedHypergraph α β) : Hypergraph α (Sym2 α) where
  vertexSet := G.vertexSet
  edgeSet := {e | ∃ u v, completeRootAdj G u v ∧ e = s(u, v)}
  Inc e x := (∃ u v, completeRootAdj G u v ∧ e = s(u, v)) ∧ x ∈ e
  vertex_mem_of_inc := by
    rintro e x ⟨⟨u, v, hadj, rfl⟩, hx⟩
    rcases Sym2.mem_iff.mp hx with rfl | rfl
    · exact completeRootAdj_mem_left hadj
    · exact completeRootAdj_mem_right hadj
  edge_mem_of_inc := fun _ _ h ↦ h.1
  vertexSet_finite := G.vertexSet_finite
  edgeSet_finite := by
    refine ((G.vertexSet_finite.prod G.vertexSet_finite).image (fun p : α × α ↦ s(p.1,
      p.2))).subset ?_
    rintro e ⟨u, v, hadj, rfl⟩
    exact ⟨(u, v), ⟨completeRootAdj_mem_left hadj, completeRootAdj_mem_right hadj⟩, rfl⟩

@[simp]
private theorem completeRootHypergraph_vertexSet (G : RootedHypergraph α β) :
    (completeRootHypergraph G).vertexSet = G.vertexSet := rfl

private theorem completeRootHypergraph_ends_of_mem {G : RootedHypergraph α β} {u v : α}
    (hadj : completeRootAdj G u v) :
    (completeRootHypergraph G).ends s(u, v) = {u, v} := by
  ext x
  simp only [Hypergraph.ends, completeRootHypergraph, Set.mem_ofPred_eq, Sym2.mem_iff,
    Set.mem_insert_iff, Set.mem_singleton_iff]
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨⟨u, v, hadj, rfl⟩, h⟩⟩

/-- `completeRootHypergraph G` is a graph (every edge has 1 or 2 ends). -/
theorem completeRootHypergraph_isGraph (G : RootedHypergraph α β) :
    (completeRootHypergraph G).IsGraph := by
  rintro e ⟨u, v, hadj, rfl⟩
  rw [completeRootHypergraph_ends_of_mem hadj]
  refine ⟨⟨u, Set.mem_insert u {v}⟩, ?_⟩
  exact (Set.ncard_insert_le u {v}).trans (by simp)

/-- Two vertices are adjacent in `(completeRootHypergraph G).skeleton` if and only if they satisfy
`completeRootAdj G`. -/
@[simp]
theorem completeRootHypergraph_skeleton_adj (G : RootedHypergraph α β) (x y : α) :
    (completeRootHypergraph G).skeleton.Adj x y ↔ completeRootAdj G x y := by
  refine ⟨?_, ?_⟩
  · rintro ⟨hxy, e, ⟨⟨u, v, hadj, rfl⟩, hx⟩, ⟨_, hy⟩⟩
    rw [Sym2.mem_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact False.elim (hxy rfl)
    · exact hadj
    · exact completeRootAdj_symm hadj
    · exact False.elim (hxy rfl)
  · intro hadj
    refine ⟨hadj.1, s(x, y), ?_, ?_⟩
    · exact ⟨⟨x, y, hadj, rfl⟩, Sym2.mem_mk_left x y⟩
    · exact ⟨⟨x, y, hadj, rfl⟩, Sym2.mem_mk_right x y⟩

/-- Graph Minors IV, (5.2), Claim (1) (page 239): if `G` has tree-width `≤ w`, then `(K, 0)` has
tree-width `≤ w`. -/
theorem theorem_5_2_claim_1 {G : RootedHypergraph α β} {w : ℕ} (h : TreeWidthLE G w) :
    TreeWidthLE (completeRootHypergraph G).toRooted w := by
  obtain ⟨T, τ, hdec, hwidth⟩ := h
  have hE : ∀ e ∈ (completeRootHypergraph G).edgeSet,
      ∃ t ∈ T.verts, (completeRootHypergraph G).ends e ⊆ (τ t).vertexSet := by
    rintro e ⟨u, v, hadj, rfl⟩
    rw [completeRootHypergraph_ends_of_mem hadj]
    rcases hadj.2 with ⟨e', hu, hv⟩ | ⟨hu, hv⟩
    · have he'_mem : e' ∈ G.edgeSet := G.edge_mem_of_inc hu
      rw [← hdec.biUnion_eq, biUnion_edgeSet, Set.mem_iUnion] at he'_mem
      obtain ⟨t, ht_Sub⟩ := he'_mem
      rw [Set.mem_iUnion] at ht_Sub
      obtain ⟨ht, he'_t⟩ := ht_Sub
      have h_ends := (hdec.le t ht).ends_eq e' he'_t
      refine ⟨t, ht, ?_⟩
      rintro x (rfl | rfl)
      · have hx_inc : (τ t).Inc e' x := by
          change x ∈ (τ t).ends e'
          rw [← h_ends]
          exact hu
        exact (τ t).vertex_mem_of_inc hx_inc
      · have hx_inc : (τ t).Inc e' x := by
          change x ∈ (τ t).ends e'
          rw [← h_ends]
          exact hv
        exact (τ t).vertex_mem_of_inc hx_inc
    · refine ⟨T.root, T.root_mem, ?_⟩
      rintro x (rfl | rfl)
      · exact (τ T.root).roots_subset x (hdec.roots_root.symm ▸ hu)
      · exact (τ T.root).roots_subset x (hdec.roots_root.symm ▸ hv)
  obtain ⟨τ', hdec', hV⟩ := exists_isTreeDecomposition_of_ends_subset
    (completeRootHypergraph G).toRooted T (fun t ↦ (τ t).vertexSet)
    (fun t ht ↦ (hdec.le t ht).vertexSet_subset)
    (by
      have h_eq := congrArg Hypergraph.vertexSet hdec.biUnion_eq
      rw [biUnion_vertexSet] at h_eq
      exact h_eq)
    hE
    (fun t₁ ht₁ t₂ ht₂ t₃ ht₃ hon ↦ (hdec.inter_le t₁ ht₁ t₂ ht₂ t₃ ht₃ hon).vertexSet_subset)
    (by simp [RootedHypergraph.rootSet, Hypergraph.toRooted])
  refine ⟨T, τ', hdec', fun t ht ↦ ?_⟩
  rw [hV t ht]
  exact hwidth t ht

/-- Graph Minors IV, (5.2), Claim (2) (page 239): there is a tree-decomposition `(T, τ)` of `(K, 0)`
of width `≤ w` satisfying the Menger-like property of Thomas's lemma (5.1). -/
theorem theorem_5_2_claim_2 (hT : ThomasStatement.{u, u}) {α : Type u} {β : Type v}
    {G : RootedHypergraph α β} {w : ℕ} (h : TreeWidthLE G w) :
    ∃ (T : RootedTree ℕ) (τ : ℕ → RootedHypergraph α (Sym2 α)),
      IsTreeDecomposition (completeRootHypergraph G).toRooted T τ ∧ WidthLE T τ w ∧
      ∀ t₁ ∈ T.verts, ∀ t₂ ∈ T.verts, t₁ ≠ t₂ → ∀ k : ℕ,
        HasDisjointPaths (completeRootHypergraph G).skeleton (τ t₁).vertexSet (τ t₂).vertexSet k ∨
          ∃ f, T.OnPathEdge t₁ t₂ f ∧ edgeOrder T τ f < k :=
  hT (completeRootHypergraph G) (completeRootHypergraph_isGraph G) w (theorem_5_2_claim_1 h)

/-- Graph Minors IV, (5.2), Claim (3) (page 239): for every clique `X ⊆ G.vertexSet` of `K` and
every tree-decomposition `(T, τ)` of `(K, 0)`, there exists `t ∈ T.verts` with
`X ⊆ (τ t).vertexSet`. -/
theorem theorem_5_2_claim_3 {G : RootedHypergraph α β} {T : RootedTree ι}
    {τ : ι → RootedHypergraph α (Sym2 α)}
    (hdec : IsTreeDecomposition (completeRootHypergraph G).toRooted T τ)
    {X : Set α} (hX_sub : X ⊆ G.vertexSet)
    (hclique : ∀ x ∈ X, ∀ y ∈ X, x ≠ y → (completeRootHypergraph G).skeleton.Adj x y) :
    ∃ t ∈ T.verts, X ⊆ (τ t).vertexSet := by
  classical
  let I : Finset α := (G.vertexSet_finite.subset hX_sub).toFinset
  let A : α → Set ι := fun x ↦ {t ∈ T.verts | x ∈ (τ t).vertexSet}
  have hsub : ∀ x ∈ I, T.IsSubtreeSet (A x) := by
    intro x _
    refine ⟨fun _ h ↦ h.1, fun t₁ ht₁ t₃ ht₃ t₂ ht₂ hon ↦ ⟨ht₂, ?_⟩⟩
    exact (hdec.inter_le t₁ ht₁.1 t₂ ht₂ t₃ ht₃.1 hon).vertexSet_subset ⟨ht₁.2, ht₃.2⟩
  have hinter : ∀ x ∈ I, ∀ y ∈ I, (A x ∩ A y).Nonempty := by
    intro x hx y hy
    rw [Set.Finite.mem_toFinset] at hx hy
    by_cases hxy : x = y
    · subst hxy
      have hx_mem : x ∈ (completeRootHypergraph G).toRooted.vertexSet := hX_sub hx
      have h_vert_eq := congrArg Hypergraph.vertexSet hdec.biUnion_eq
      rw [← h_vert_eq, biUnion_vertexSet, Set.mem_iUnion] at hx_mem
      obtain ⟨t, ht_sub⟩ := hx_mem
      rw [Set.mem_iUnion] at ht_sub
      obtain ⟨ht, hxt⟩ := ht_sub
      exact ⟨t, ⟨ht, hxt⟩, ⟨ht, hxt⟩⟩
    · have hadj : completeRootAdj G x y :=
        (completeRootHypergraph_skeleton_adj G x y).mp (hclique x hx y hy hxy)
      have he_mem : s(x, y) ∈ (completeRootHypergraph G).toRooted.edgeSet := ⟨x, y, hadj, rfl⟩
      have h_edge_eq := congrArg Hypergraph.edgeSet hdec.biUnion_eq
      rw [← h_edge_eq, biUnion_edgeSet, Set.mem_iUnion] at he_mem
      obtain ⟨t, ht_sub⟩ := he_mem
      rw [Set.mem_iUnion] at ht_sub
      obtain ⟨ht, het⟩ := ht_sub
      have h_ends := (hdec.le t ht).ends_eq s(x, y) het
      have hxy_ends : (τ t).ends s(x, y) = {x, y} := by
        rw [← h_ends]
        exact completeRootHypergraph_ends_of_mem hadj
      have hx_t : x ∈ (τ t).vertexSet := by
        apply (τ t).vertex_mem_of_inc (e := s(x, y))
        change x ∈ (τ t).ends s(x, y)
        rw [hxy_ends]
        exact Set.mem_insert x {y}
      have hy_t : y ∈ (τ t).vertexSet := by
        apply (τ t).vertex_mem_of_inc (e := s(x, y))
        change y ∈ (τ t).ends s(x, y)
        rw [hxy_ends]
        exact Set.mem_insert_of_mem x (Set.mem_singleton y)
      exact ⟨t, ⟨ht, hx_t⟩, ⟨ht, hy_t⟩⟩
  obtain ⟨t, ht, hmem⟩ := T.helly_isSubtreeSet I A hsub hinter
  refine ⟨t, ht, fun x hx ↦ ?_⟩
  have hxI : x ∈ I := (Set.Finite.mem_toFinset _).mpr hx
  exact (hmem x hxI).2

/-- Graph Minors IV, (5.2), Claim (4) (page 239): we may choose `(T, τ)` satisfying Claim (2) so
that in addition `G.rootSet ⊆ (τ T.root).vertexSet`. -/
theorem theorem_5_2_claim_4 (hT : ThomasStatement.{u, u}) {α : Type u} {β : Type v}
    {G : RootedHypergraph α β} {w : ℕ} (h : TreeWidthLE G w) :
    ∃ (T : RootedTree ℕ) (τ : ℕ → RootedHypergraph α (Sym2 α)),
      IsTreeDecomposition (completeRootHypergraph G).toRooted T τ ∧ WidthLE T τ w ∧
      G.rootSet ⊆ (τ T.root).vertexSet ∧
      ∀ t₁ ∈ T.verts, ∀ t₂ ∈ T.verts, t₁ ≠ t₂ → ∀ k : ℕ,
        HasDisjointPaths (completeRootHypergraph G).skeleton (τ t₁).vertexSet (τ t₂).vertexSet k ∨
          ∃ f, T.OnPathEdge t₁ t₂ f ∧ edgeOrder T τ f < k := by
  obtain ⟨T₀, τ₀, hdec₀, hwidth₀, hthomas₀⟩ := theorem_5_2_claim_2 hT h
  have hroot_sub : G.rootSet ⊆ G.vertexSet := fun x hx ↦ G.roots_subset x hx
  have hroot_clique : ∀ x ∈ G.rootSet, ∀ y ∈ G.rootSet, x ≠ y →
      (completeRootHypergraph G).skeleton.Adj x y := by
    intro x hx y hy hxy
    rw [completeRootHypergraph_skeleton_adj]
    exact ⟨hxy, Or.inr ⟨hx, hy⟩⟩
  obtain ⟨r₀, hr₀, hr₀_sub⟩ := theorem_5_2_claim_3 hdec₀ hroot_sub hroot_clique
  obtain ⟨T, hverts, hroot, honPath, honPathEdge⟩ :=
    T₀.exists_reroot (fun t ↦ (τ₀ t).vertexSet) hr₀
  have hE : ∀ e ∈ (completeRootHypergraph G).toRooted.edgeSet,
      ∃ t ∈ T.verts, (completeRootHypergraph G).toRooted.ends e ⊆ (τ₀ t).vertexSet := by
    intro e he
    have h_edge_eq := congrArg Hypergraph.edgeSet hdec₀.biUnion_eq
    rw [← h_edge_eq, biUnion_edgeSet, Set.mem_iUnion] at he
    obtain ⟨t, ht_sub⟩ := he
    rw [Set.mem_iUnion] at ht_sub
    obtain ⟨ht, het⟩ := ht_sub
    have h_ends := (hdec₀.le t ht).ends_eq e het
    refine ⟨t, hverts.symm ▸ ht, fun x hx ↦ ?_⟩
    have hx_inc : (τ₀ t).Inc e x := by
      change x ∈ (τ₀ t).ends e
      rw [← h_ends]
      exact hx
    exact (τ₀ t).vertex_mem_of_inc hx_inc
  obtain ⟨τ, hdec, hV⟩ := exists_isTreeDecomposition_of_ends_subset
    (completeRootHypergraph G).toRooted T (fun t ↦ (τ₀ t).vertexSet)
    (fun t ht ↦ (hdec₀.le t (hverts ▸ ht)).vertexSet_subset)
    (by
      rw [hverts]
      have h_eq := congrArg Hypergraph.vertexSet hdec₀.biUnion_eq
      rw [biUnion_vertexSet] at h_eq
      exact h_eq)
    hE
    (fun t₁ ht₁ t₂ ht₂ t₃ ht₃ hon ↦ by
      rw [hverts] at ht₁ ht₂ ht₃
      rw [honPath t₁ ht₁ t₂ ht₂ t₃ ht₃] at hon
      exact (hdec₀.inter_le t₁ ht₁ t₂ ht₂ t₃ ht₃ hon).vertexSet_subset)
    (by simp [RootedHypergraph.rootSet, Hypergraph.toRooted])
  refine ⟨T, τ, hdec, ?_, ?_, ?_⟩
  · intro t ht
    rw [hV t ht]
    exact hwidth₀ t (hverts ▸ ht)
  · rw [hV T.root T.root_mem, hroot]
    exact hr₀_sub
  · intro t₁ ht₁ t₂ ht₂ hne k
    have ht₁₀ : t₁ ∈ T₀.verts := hverts ▸ ht₁
    have ht₂₀ : t₂ ∈ T₀.verts := hverts ▸ ht₂
    rw [hV t₁ ht₁, hV t₂ ht₂]
    rcases hthomas₀ t₁ ht₁₀ t₂ ht₂₀ hne k with hpaths | ⟨f, hfon, hford⟩
    · exact Or.inl hpaths
    · right
      have hf_edge : f ∈ T₀.edges := hfon.1
      rw [hdec₀.edgeOrder_eq_ncard_vertexSet_inter hf_edge] at hford
      have hex : ∃ f, T.OnPathEdge t₁ t₂ f ∧
          ((τ₀ f).vertexSet ∩ (τ₀ (T.parent f)).vertexSet).ncard < k :=
        (honPathEdge t₁ ht₁₀ t₂ ht₂₀ k).mpr ⟨f, hfon, hford⟩
      obtain ⟨f', hf'on, hf'ord⟩ := hex
      have hf'_edge : f' ∈ T.edges := hf'on.1
      have hf'_v : f' ∈ T.verts := T.edges_subset_verts hf'_edge
      have hpf'_v : T.parent f' ∈ T.verts := T.parent_mem f' hf'_v
      refine ⟨f', hf'on, ?_⟩
      rw [hdec.edgeOrder_eq_ncard_vertexSet_inter hf'_edge, hV f' hf'_v, hV (T.parent f') hpf'_v]
      exact hf'ord

/-- Graph Minors IV, (5.2), Claim (5) (page 239): for `(T, τ)` as in Claim (4), there is a
tree-decomposition `(T, τ')` of `G` such that `(τ' t).vertexSet = (τ t).vertexSet` for all
`t ∈ T.verts`. -/
theorem theorem_5_2_claim_5 {G : RootedHypergraph α β} {T : RootedTree ι}
    {τ : ι → RootedHypergraph α (Sym2 α)}
    (hdec : IsTreeDecomposition (completeRootHypergraph G).toRooted T τ)
    (hroot : G.rootSet ⊆ (τ T.root).vertexSet) :
    ∃ τ' : ι → RootedHypergraph α β,
      IsTreeDecomposition G T τ' ∧ ∀ t ∈ T.verts, (τ' t).vertexSet = (τ t).vertexSet := by
  have hE : ∀ e ∈ G.edgeSet, ∃ t ∈ T.verts, G.ends e ⊆ (τ t).vertexSet := by
    intro e he
    have hends_sub : G.ends e ⊆ G.vertexSet := fun x hx ↦ G.vertex_mem_of_inc hx
    have hends_clique : ∀ x ∈ G.ends e, ∀ y ∈ G.ends e, x ≠ y →
        (completeRootHypergraph G).skeleton.Adj x y := by
      intro x hx y hy hxy
      rw [completeRootHypergraph_skeleton_adj]
      exact ⟨hxy, Or.inl ⟨e, hx, hy⟩⟩
    exact theorem_5_2_claim_3 hdec hends_sub hends_clique
  exact exists_isTreeDecomposition_of_ends_subset G T (fun t ↦ (τ t).vertexSet)
    (fun t ht ↦ (hdec.le t ht).vertexSet_subset)
    (by
      have h_eq := congrArg Hypergraph.vertexSet hdec.biUnion_eq
      rw [biUnion_vertexSet] at h_eq
      exact h_eq)
    hE
    (fun t₁ ht₁ t₂ ht₂ t₃ ht₃ hon ↦ (hdec.inter_le t₁ ht₁ t₂ ht₂ t₃ ht₃ hon).vertexSet_subset)
    hroot

/-- If `f₂` reaches `f₁` in `T`, then every edge `g` on the path of `T` between `f₁` and
`T.parent f₂` lies in `T.pathEdges f₂ f₁ ∩ T.edges`. -/
private theorem RootedTree.mem_pathEdges_of_onPathEdge_parent {T : RootedTree ι} {f₁ f₂ g : ι}
    (hf₁ : f₁ ∈ T.edges) (hf₂ : f₂ ∈ T.edges) (hreach : T.Reaches f₂ f₁)
    (hon : T.OnPathEdge f₁ (T.parent f₂) g) :
    g ∈ T.pathEdges f₂ f₁ ∩ T.edges := by
  have hf₁v : f₁ ∈ T.verts := T.edges_subset_verts hf₁
  have hf₂v : f₂ ∈ T.verts := T.edges_subset_verts hf₂
  have hp₂v : T.parent f₂ ∈ T.verts := T.parent_mem f₂ hf₂v
  have hp₂_f₂ : T.Reaches (T.parent f₂) f₂ := T.reaches_parent hf₂v
  have hp₂_f₁ : T.Reaches (T.parent f₂) f₁ := T.reaches_trans hp₂_f₂ hreach
  rw [T.onPathEdge_iff hf₁v hp₂v] at hon
  obtain ⟨hg_edge, hcases⟩ := hon
  rcases hcases with ⟨h₁, h₂⟩ | ⟨h₂, h₁⟩
  · have hg_f₁ : T.Reaches g f₁ := T.mem_subtreeAt.mp h₁
    have hnot_g_p₂ : ¬ T.Reaches g (T.parent f₂) := (T.mem_rootSide.mp h₂).2
    have hf₂_g : T.Reaches f₂ g := by
      rcases T.reaches_total_of_reaches hreach hg_f₁ with h | h
      · exact h
      · by_cases hgf₂ : g = f₂
        · subst hgf₂
          exact T.reaches_refl hf₂v
        · exact False.elim (hnot_g_p₂ (T.reaches_parent_of_reaches_of_ne h hgf₂))
    exact ⟨⟨hf₂_g, hg_f₁⟩, hg_edge⟩
  · have hg_p₂ : T.Reaches g (T.parent f₂) := T.mem_subtreeAt.mp h₂
    have hnot_g_f₁ : ¬ T.Reaches g f₁ := (T.mem_rootSide.mp h₁).2
    exact False.elim (hnot_g_f₁ (T.reaches_trans hg_p₂ hp₂_f₁))

/-- If every edge of a simple graph `K` has both ends in `A` or both ends in `B`, then every walk
of `K` from a vertex in `A` to a vertex in `B` visits a vertex in `A ∩ B`. -/
private theorem exists_mem_inter_of_walk {K : SimpleGraph α} {A B : Set α}
    (hedges : ∀ x y, K.Adj x y → (x ∈ A ∧ y ∈ A) ∨ (x ∈ B ∧ y ∈ B))
    {u v : α} (w : K.Walk u v) (hu : u ∈ A) (hv : v ∈ B) :
    ∃ z ∈ w.support, z ∈ A ∩ B := by
  induction w with
  | nil =>
    exact ⟨_, SimpleGraph.Walk.start_mem_support _, ⟨hu, hv⟩⟩
  | @cons u u' v hadj w' ih =>
    by_cases huB : u ∈ B
    · exact ⟨u, SimpleGraph.Walk.start_mem_support _, ⟨hu, huB⟩⟩
    · have hu'A : u' ∈ A := by
        rcases hedges u u' hadj with ⟨_, h⟩ | ⟨h, _⟩
        · exact h
        · exact False.elim (huB h)
      obtain ⟨z, hz_sup, hz_AB⟩ := ih hu'A hv
      refine ⟨z, ?_, hz_AB⟩
      rw [SimpleGraph.Walk.support_cons]
      exact List.mem_cons_of_mem u hz_sup

/-- Graph Minors IV, (5.2) (page 239): "Let $G$ be a rooted hypergraph of tree-width $\le w$. Then
there is a rotund
tree-decomposition of $G$ of width $\le w$." -/
theorem theorem_5_2_proof (hT : ThomasStatement.{u, u}) {α : Type u} {β : Type v}
    (G : RootedHypergraph α β) (w : ℕ) (h : TreeWidthLE G w) :
    ∃ (T : RootedTree ℕ) (τ : ℕ → RootedHypergraph α β),
      IsTreeDecomposition G T τ ∧ WidthLE T τ w ∧ IsRotund T τ T.edges := by
  obtain ⟨T, τ, hdec, hwidth, hroot, hthomas⟩ := theorem_5_2_claim_4 hT h
  obtain ⟨τ', hdec', hV⟩ := theorem_5_2_claim_5 hdec hroot
  have hwidth' : WidthLE T τ' w := by
    intro t ht
    rw [hV t ht]
    exact hwidth t ht
  have hord_eq : ∀ f ∈ T.edges, edgeOrder T τ' f = edgeOrder T τ f := by
    intro f hf
    have hfv : f ∈ T.verts := T.edges_subset_verts hf
    have hpv : T.parent f ∈ T.verts := T.parent_mem f hfv
    rw [hdec'.edgeOrder_eq_ncard_vertexSet_inter hf, hdec.edgeOrder_eq_ncard_vertexSet_inter hf,
      hV f hfv, hV (T.parent f) hpv]
  refine ⟨T, τ', hdec', hwidth', ?_⟩
  intro f₁ hf₁ f₂ hf₂ hreach heq hmin
  rintro ⟨H₁, H₂, hsep, hH₁, hH₂, hord⟩
  rw [hdec'.cross_verts_eq] at hsep
  set k := edgeOrder T τ' f₁
  have hf₁v : f₁ ∈ T.verts := T.edges_subset_verts hf₁
  have hf₂v : f₂ ∈ T.verts := T.edges_subset_verts hf₂
  have hp₂v : T.parent f₂ ∈ T.verts := T.parent_mem f₂ hf₂v
  have hne : f₁ ≠ T.parent f₂ := by
    intro h_eq
    rw [h_eq] at hreach
    exact T.not_reaches_parent hf₂ hreach
  have hnot_lt : ¬ ∃ f, T.OnPathEdge f₁ (T.parent f₂) f ∧ edgeOrder T τ f < k := by
    rintro ⟨g, hgon, hg_lt⟩
    have hg_mem : g ∈ T.pathEdges f₂ f₁ ∩ T.edges :=
      T.mem_pathEdges_of_onPathEdge_parent hf₁ hf₂ hreach hgon
    rw [← hord_eq g hg_mem.2] at hg_lt
    exact Nat.lt_irrefl _ (hg_lt.trans_le (hmin g hg_mem))
  have hpaths : HasDisjointPaths (completeRootHypergraph G).skeleton
      (τ f₁).vertexSet (τ (T.parent f₂)).vertexSet k := by
    rcases hthomas f₁ hf₁v (T.parent f₂) hp₂v hne k with hp | hex
    · exact hp
    · exact False.elim (hnot_lt hex)
  obtain ⟨P, hdisj⟩ := hpaths
  have hV₁_sub : (τ f₁).vertexSet ⊆ H₁.vertexSet := by
    rw [← hV f₁ hf₁v]
    refine Set.Subset.trans ?_ hH₁.vertexSet_subset
    rw [cross_toHypergraph_of_mem τ' (T.self_mem_subtreeAt hf₁v), biUnion_vertexSet]
    exact fun _ hx ↦ Set.mem_biUnion (T.self_mem_subtreeAt hf₁v) hx
  have hV₂_sub : (τ (T.parent f₂)).vertexSet ⊆ H₂.vertexSet := by
    rw [← hV (T.parent f₂) hp₂v]
    refine Set.Subset.trans ?_ hH₂.vertexSet_subset
    rw [cross_toHypergraph_of_mem τ' (T.root_mem_rootSide hf₂), biUnion_vertexSet]
    exact fun _ hx ↦ Set.mem_biUnion (T.parent_mem_rootSide hf₂) hx
  have hroot_H₂ : G.rootSet ⊆ H₂.vertexSet := by
    refine Set.Subset.trans (hV T.root T.root_mem ▸ hroot) ?_
    refine Set.Subset.trans ?_ hH₂.vertexSet_subset
    rw [cross_toHypergraph_of_mem τ' (T.root_mem_rootSide hf₂), biUnion_vertexSet]
    exact fun _ hx ↦ Set.mem_biUnion (T.root_mem_rootSide hf₂) hx
  have hedges : ∀ x y, (completeRootHypergraph G).skeleton.Adj x y →
      (x ∈ H₁.vertexSet ∧ y ∈ H₁.vertexSet) ∨ (x ∈ H₂.vertexSet ∧ y ∈ H₂.vertexSet) := by
    intro x y hadj
    rw [completeRootHypergraph_skeleton_adj] at hadj
    rcases hadj.2 with ⟨e, hx, hy⟩ | ⟨hx, hy⟩
    · have he : e ∈ G.edgeSet := G.edge_mem_of_inc hx
      rw [← hsep.union_eq, union_edgeSet] at he
      rcases he with he₁ | he₂
      · left
        have hends := hsep.left_le.ends_eq e he₁
        have hx₁ : H₁.Inc e x := by change x ∈ H₁.ends e; rw [← hends]; exact hx
        have hy₁ : H₁.Inc e y := by change y ∈ H₁.ends e; rw [← hends]; exact hy
        exact ⟨H₁.vertex_mem_of_inc hx₁, H₁.vertex_mem_of_inc hy₁⟩
      · right
        have hends := hsep.right_le.ends_eq e he₂
        have hx₂ : H₂.Inc e x := by change x ∈ H₂.ends e; rw [← hends]; exact hx
        have hy₂ : H₂.Inc e y := by change y ∈ H₂.ends e; rw [← hends]; exact hy
        exact ⟨H₂.vertex_mem_of_inc hx₂, H₂.vertex_mem_of_inc hy₂⟩
    · exact Or.inr ⟨hroot_H₂ hx, hroot_H₂ hy⟩
  have hex_z : ∀ i : Fin k, ∃ z ∈ (P i).walk.support, z ∈ (H₁ ∩ H₂).vertexSet := by
    intro i
    exact exists_mem_inter_of_walk hedges (P i).walk
      (hV₁_sub (P i).first_mem) (hV₂_sub (P i).last_mem)
  choose z hz_sup hz_mem using hex_z
  have hz_inj : Function.Injective z := by
    intro i j hij
    by_contra hne_ij
    have hdisj_ij := hdisj hne_ij
    exact Set.disjoint_left.mp hdisj_ij (hz_sup i) (hij ▸ hz_sup j)
  have hcard : k ≤ separationOrder H₁ H₂ := by
    have h_range_sub : Set.range z ⊆ (H₁ ∩ H₂).vertexSet := by
      rintro _ ⟨i, rfl⟩
      exact hz_mem i
    have h_ncard_le := Set.ncard_le_ncard h_range_sub (H₁ ∩ H₂).vertexSet_finite
    rwa [Set.ncard_range_of_injective hz_inj, Nat.card_eq_fintype_card, Fintype.card_fin] at
      h_ncard_le
  exact Nat.not_lt.mpr hcard hord

/-- For any `R` satisfying Axiom 1, the class `starClass ι R n` is symmetric. -/
theorem isSymmetric_starClass {R : Set (RootedHypergraph α β)} (hA1 : Axiom1 R) (n : ℕ) :
    IsSymmetric (starClass ι R n) := by
  rintro ⟨S, σ⟩ ⟨hstar, hR, hcard⟩ σ' hstar' hσ'
  refine ⟨hstar', ?_, ?_⟩
  · have h_eq : (cross σ' S.verts S.root).toHypergraph = (cross σ S.verts S.root).toHypergraph :=
      cross_toHypergraph_congr S.root_mem S.root_mem (fun s hs ↦ (hσ' s hs).1)
    exact hA1 _ hR _ (h_eq ▸ le_rfl)
  · have h_vert : (σ' S.root).vertexSet = (σ S.root).vertexSet :=
      congrArg Hypergraph.vertexSet (hσ' S.root S.root_mem).1
    rwa [h_vert]

/-- Graph Minors IV, (5.3) (page 240): assuming Axioms 1–4, every countable sequence of elements of
`R` of tree-width `≤ n` has `i < i'` with `G i` simulated in `G i'`. -/
theorem theorem_5_3_proof (h22 : TreeLemma22Statement.{0}) (hT : ThomasStatement.{u, u}) :
    Theorem53Statement.{u, v} := by
  intro α β R sim hA1 hA2 hA3 hA4 n G hR htw
  have hex : ∀ i, ∃ (T : RootedTree ℕ) (τ : ℕ → RootedHypergraph α β),
      IsTreeDecomposition (G i) T τ ∧ WidthLE T τ n ∧ IsRotund T τ T.edges :=
    fun i ↦ theorem_5_2_proof hT (G i) n (htw i)
  choose T τ hdec hwidth hrot using hex
  have hcross : ∀ i, cross (τ i) (T i).verts (T i).root = G i :=
    fun i ↦ (hdec i).cross_verts_eq
  have hdec' : ∀ i, IsTreeDecomposition (cross (τ i) (T i).verts (T i).root) (T i) (τ i) :=
    fun i ↦ (hcross i).symm ▸ hdec i
  have hbr : ∀ i, ∀ s ∈ (T i).verts,
      ((T i).starAt s, branching (T i) (τ i) s) ∈ starClass ℕ R (n + 1) := by
    intro i s hs
    refine ⟨(hdec i).isStarDecomposition_branching hs, ?_, ?_⟩
    · rw [cross_branching_eq (T i) (τ i) hs]
      have hle : (cross (τ i) ((T i).subtreeAt s) s).toHypergraph ≤ (G i).toHypergraph := by
        rw [cross_toHypergraph_of_mem (τ i) ((T i).self_mem_subtreeAt hs)]
        exact biUnion_le (fun t ht ↦ (hdec i).le t ((T i).subtreeAt_subset_verts s ht))
      exact hA1 (G i) (hR i) _ hle
    · dsimp only
      have hroot_eq : ((T i).starAt s).root = s := rfl
      rw [hroot_eq]
      have hbr_root : branching (T i) (τ i) s s = τ i s := by simp [branching]
      rw [hbr_root]
      exact hwidth i s hs
  obtain ⟨i, i', hii', hsim⟩ := theorem_4_2_proof h22 hA1 hA2 hA3
    (starClass ℕ R (n + 1)) (hA4 (n + 1)) (isSymmetric_starClass hA1 (n + 1))
    T τ hdec' hrot hbr
  rw [hcross i, hcross i'] at hsim
  exact ⟨i, i', hii', hsim⟩

end GraphMinor.GM04
