/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

import LeanPool.GraphMinor.Menger.Basic

public import LeanPool.GraphMinor.Thomas.Amalgamate

/-!
# Vertex separators, Menger's theorem on the 1-skeleton, and reindexing decompositions

This file provides the graph-theoretic separator infrastructure used in the proof of Theorem 3 of
P. Bellenbaum and R. Diestel, *Two short proofs concerning tree-decompositions*, Combin. Probab.
Comput. 11 (2002) 541–547 (Section 3, pages 3–5):

- Reindexing a `TreeDecomp` along an equivalence `ι ≃ ι'` (`TreeDecomp.reindex`).
- Vertex separators `Separates K V₀ Z₁ Z₂ X` in a simple graph `K` on vertex set `V₀`, and the
  partition of `V₀ \ X` into `sepCompLeft K V₀ X Z₁` (`C₁`, the union of components of `G - X`
  meeting `Z₁`) and `sepCompRight K V₀ X Z₁` (`C₂`, the union of the remaining components).
- Equivalence between hypergraph separations `G.IsSeparation G₁ G₂` and vertex separators of
  `G.skeleton`, deducing the vertex-separator form of Menger's theorem from `MengerStatement`.
- Splitting the Menger paths `{P_x | x ∈ X}` of a minimum-order `Z₁`–`Z₂` separator `X` at each
  `x ∈ X` into disjoint `X`–`Z₂` paths `P_x^1` in `G - C₁` and disjoint `X`–`Z₁` paths `P_x^2` in
  `G - C₂`.
-/

@[expose] public section

namespace GraphMinor.Thomas

open SimpleGraph

universe u v

variable {α : Type u} {β : Type v} {ι ι' : Type*}

namespace TreeDecomp

variable [Fintype ι] [Fintype ι'] {G : SimpleGraph α} {V₀ : Set α} (D : TreeDecomp G V₀ ι)

/-- Reindex a tree-decomposition along a bijection `e : ι ≃ ι'`. -/
def reindex (e : ι ≃ ι') : TreeDecomp G V₀ ι' where
  T := D.T.map e.toEmbedding
  isTree := (Iso.map e D.T).isTree_iff.1 D.isTree
  bag t' := D.bag (e.symm t')
  iUnion_bag := by
    ext x
    simp only [Set.mem_iUnion, ← D.iUnion_bag]
    exact ⟨fun ⟨t', ht'⟩ ↦ ⟨e.symm t', ht'⟩, fun ⟨t, ht⟩ ↦ ⟨e t, by simpa using ht⟩⟩
  adj_mem_bag u v hu hv hadj := by
    obtain ⟨t, hut, hvt⟩ := D.adj_mem_bag hu hv hadj
    exact ⟨e t, by simpa using hut, by simpa using hvt⟩
  inter_subset_bag := by
    rintro t₁' t₂' t₃' ht x ⟨h₁, h₃⟩
    have hpath : OnTreePath D.T (e.symm t₁') (e.symm t₃') (e.symm t₂') := by
      rw [onTreePath_iff_forall_walk]
      intro w
      have hu : (Iso.map e D.T).toHom (e.symm t₁') = t₁' := e.apply_symm_apply t₁'
      have hv : (Iso.map e D.T).toHom (e.symm t₃') = t₃' := e.apply_symm_apply t₃'
      have hmem := onTreePath_iff_forall_walk.1 ht ((w.map (Iso.map e D.T).toHom).copy hu hv)
      rw [Walk.support_copy, Walk.support_map, List.mem_map] at hmem
      obtain ⟨s, hs, hs_eq⟩ := hmem
      have : s = e.symm t₂' := by
        apply e.injective
        exact hs_eq.trans (e.apply_symm_apply t₂').symm
      exact this ▸ hs
    exact D.inter_subset_bag hpath ⟨h₁, h₃⟩

@[simp]
theorem reindex_bag (e : ι ≃ ι') (t' : ι') :
    (D.reindex e).bag t' = D.bag (e.symm t') :=
  rfl

theorem reindex_widthLE (e : ι ≃ ι') {w : ℕ} :
    (D.reindex e).WidthLE w ↔ D.WidthLE w := by
  constructor
  · intro h t
    simpa using h (e t)
  · intro h t'
    exact h (e.symm t')

end TreeDecomp

/-! ## Vertex separators and component partitions of `G - X` -/

/-- `X` separates `Z₁` from `Z₂` in `(K, V₀)`: `X ⊆ V₀` and every walk in `K` (within `V₀`) from
`Z₁` to `Z₂` contains a vertex of `X`. -/
def Separates (K : SimpleGraph α) (V₀ Z₁ Z₂ X : Set α) : Prop :=
  X ⊆ V₀ ∧ ∀ ⦃u v : α⦄, u ∈ Z₁ → v ∈ Z₂ → ∀ p : K.Walk u v,
    (∀ z ∈ p.support, z ∈ V₀) → ∃ x ∈ p.support, x ∈ X

theorem separates_symm {K : SimpleGraph α} {V₀ Z₁ Z₂ X : Set α}
    (h : Separates K V₀ Z₁ Z₂ X) : Separates K V₀ Z₂ Z₁ X := by
  refine ⟨h.1, fun u v hu hv p hp ↦ ?_⟩
  obtain ⟨x, hx, hxX⟩ := h.2 hv hu p.reverse (by simpa using hp)
  rw [Walk.support_reverse, List.mem_reverse] at hx
  exact ⟨x, hx, hxX⟩

theorem ncard_le_of_hasDisjointPaths_of_separates {K : SimpleGraph α} {V₀ Z₁ Z₂ X : Set α}
    {k : ℕ} (hV₀ : V₀.Finite) (hZ₁ : Z₁ ⊆ V₀)
    (hK : ∀ ⦃u v : α⦄, K.Adj u v → u ∈ V₀ ∧ v ∈ V₀)
    (hpaths : HasDisjointPaths K Z₁ Z₂ k) (hsep : Separates K V₀ Z₁ Z₂ X) :
    k ≤ X.ncard := by
  classical
  obtain ⟨P, hP⟩ := hpaths
  have hsupp : ∀ (i : Fin k) (z : α), z ∈ (P i).walk.support → z ∈ V₀ := by
    intro i z hz
    have hwalk : ∀ {u v : α} (w : K.Walk u v), u ∈ V₀ → ∀ z ∈ w.support, z ∈ V₀ := by
      intro u v w hu z hz
      induction w with
      | nil =>
        simp only [Walk.support_nil, List.mem_singleton] at hz
        exact hz ▸ hu
      | cons hadj q ih =>
        simp only [Walk.support_cons, List.mem_cons] at hz
        rcases hz with rfl | hz
        · exact hu
        · exact ih (hK hadj).2 hz
    exact hwalk (P i).walk (hZ₁ (P i).first_mem) z hz
  have hex : ∀ i : Fin k, ∃ x ∈ (P i).walk.support, x ∈ X :=
    fun i ↦ hsep.2 (P i).first_mem (P i).last_mem (P i).walk (hsupp i)
  let f : Fin k → α := fun i ↦ (hex i).choose
  have hf_mem : ∀ i ∈ (Set.univ : Set (Fin k)), f i ∈ X :=
    fun i _ ↦ (hex i).choose_spec.2
  have hf_inj : Set.InjOn f Set.univ := by
    intro i _ j _ hij
    by_contra hne
    have h1 : f i ∈ (P i).walk.support := (hex i).choose_spec.1
    have h2 : f i ∈ (P j).walk.support := hij ▸ (hex j).choose_spec.1
    exact Set.disjoint_left.1 (hP hne) h1 h2
  have hcard := Set.ncard_le_ncard_of_injOn f hf_mem hf_inj (hV₀.subset hsep.1)
  rwa [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] at hcard

/-- `C₁`: the union of the components of `(K, V₀) - X` that meet `Z₁` (Bellenbaum and Diestel,
proof of Theorem 3, page 3). -/
def sepCompLeft (K : SimpleGraph α) (V₀ X Z₁ : Set α) : Set α :=
  {v ∈ V₀ \ X | ∃ u ∈ Z₁ \ X, ∃ p : K.Walk u v, ∀ w ∈ p.support, w ∈ V₀ \ X}

/-- `C₂`: the union of all the other components of `(K, V₀) - X` (Bellenbaum and Diestel, proof of
Theorem 3, page 3). -/
def sepCompRight (K : SimpleGraph α) (V₀ X Z₁ : Set α) : Set α :=
  (V₀ \ X) \ sepCompLeft K V₀ X Z₁

theorem sepCompLeft_subset_sdiff (K : SimpleGraph α) (V₀ X Z₁ : Set α) :
    sepCompLeft K V₀ X Z₁ ⊆ V₀ \ X :=
  fun _ h ↦ h.1

theorem sepCompRight_subset_sdiff (K : SimpleGraph α) (V₀ X Z₁ : Set α) :
    sepCompRight K V₀ X Z₁ ⊆ V₀ \ X :=
  Set.sdiff_subset

theorem sepCompLeft_subset (K : SimpleGraph α) (V₀ X Z₁ : Set α) :
    sepCompLeft K V₀ X Z₁ ⊆ V₀ :=
  fun _ h ↦ h.1.1

theorem sepCompRight_subset (K : SimpleGraph α) (V₀ X Z₁ : Set α) :
    sepCompRight K V₀ X Z₁ ⊆ V₀ :=
  fun _ h ↦ h.1.1

theorem disjoint_sepCompLeft_sepCompRight (K : SimpleGraph α) (V₀ X Z₁ : Set α) :
    Disjoint (sepCompLeft K V₀ X Z₁) (sepCompRight K V₀ X Z₁) :=
  disjoint_sdiff_self_right

theorem disjoint_sepCompLeft_sep (K : SimpleGraph α) (V₀ X Z₁ : Set α) :
    Disjoint (sepCompLeft K V₀ X Z₁) X :=
  Set.disjoint_left.2 fun _ h ↦ h.1.2

theorem disjoint_sepCompRight_sep (K : SimpleGraph α) (V₀ X Z₁ : Set α) :
    Disjoint (sepCompRight K V₀ X Z₁) X :=
  Set.disjoint_left.2 fun _ h ↦ h.1.2

theorem subset_sepComp_union (K : SimpleGraph α) {V₀ X : Set α} (Z₁ : Set α) :
    V₀ ⊆ sepCompLeft K V₀ X Z₁ ∪ sepCompRight K V₀ X Z₁ ∪ X := by
  intro v hv
  by_cases hvX : v ∈ X
  · exact Or.inr hvX
  · by_cases hvC : v ∈ sepCompLeft K V₀ X Z₁
    · exact Or.inl (Or.inl hvC)
    · exact Or.inl (Or.inr ⟨⟨hv, hvX⟩, hvC⟩)

theorem not_adj_sepCompLeft_sepCompRight {K : SimpleGraph α} {V₀ X Z₁ : Set α}
    ⦃u v : α⦄ (hu : u ∈ sepCompLeft K V₀ X Z₁) (hv : v ∈ sepCompRight K V₀ X Z₁) :
    ¬ K.Adj u v := by
  intro hadj
  obtain ⟨_, z₁, hz₁, p, hp⟩ := hu
  refine hv.2 ⟨hv.1, z₁, hz₁, p.concat hadj, ?_⟩
  intro w hw
  rw [Walk.support_concat, List.mem_append, List.mem_singleton] at hw
  rcases hw with hw | rfl
  · exact hp w hw
  · exact hv.1

theorem adj_mem_sepComp_or {K : SimpleGraph α} {V₀ X Z₁ : Set α}
    ⦃u v : α⦄ (hu : u ∈ V₀) (hv : v ∈ V₀) (hadj : K.Adj u v) :
    (u ∈ sepCompLeft K V₀ X Z₁ ∪ X ∧ v ∈ sepCompLeft K V₀ X Z₁ ∪ X) ∨
    (u ∈ sepCompRight K V₀ X Z₁ ∪ X ∧ v ∈ sepCompRight K V₀ X Z₁ ∪ X) := by
  rcases subset_sepComp_union K Z₁ hu with (hu1 | hu2) | huX
  · rcases subset_sepComp_union K Z₁ hv with (hv1 | hv2) | hvX
    · exact Or.inl ⟨Or.inl hu1, Or.inl hv1⟩
    · exact (not_adj_sepCompLeft_sepCompRight hu1 hv2 hadj).elim
    · exact Or.inl ⟨Or.inl hu1, Or.inr hvX⟩
  · rcases subset_sepComp_union K Z₁ hv with (hv1 | hv2) | hvX
    · exact (not_adj_sepCompLeft_sepCompRight hv1 hu2 hadj.symm).elim
    · exact Or.inr ⟨Or.inl hu2, Or.inl hv2⟩
    · exact Or.inr ⟨Or.inl hu2, Or.inr hvX⟩
  · rcases subset_sepComp_union K Z₁ hv with (hv1 | hv2) | hvX
    · exact Or.inl ⟨Or.inr huX, Or.inl hv1⟩
    · exact Or.inr ⟨Or.inr huX, Or.inl hv2⟩
    · exact Or.inl ⟨Or.inr huX, Or.inr hvX⟩

theorem subset_sepCompLeft_union (K : SimpleGraph α) {V₀ X Z₁ : Set α} (hZ₁ : Z₁ ⊆ V₀) :
    Z₁ ⊆ sepCompLeft K V₀ X Z₁ ∪ X := by
  intro z hz
  by_cases hzX : z ∈ X
  · exact Or.inr hzX
  · refine Or.inl ⟨⟨hZ₁ hz, hzX⟩, z, ⟨hz, hzX⟩, Walk.nil, ?_⟩
    simp [hZ₁ hz, hzX]

theorem subset_sepCompRight_union {K : SimpleGraph α} {V₀ X Z₁ Z₂ : Set α}
    (hZ₂ : Z₂ ⊆ V₀) (hsep : Separates K V₀ Z₁ Z₂ X) :
    Z₂ ⊆ sepCompRight K V₀ X Z₁ ∪ X := by
  intro z₂ hz₂
  by_cases hz₂X : z₂ ∈ X
  · exact Or.inr hz₂X
  · refine Or.inl ⟨⟨hZ₂ hz₂, hz₂X⟩, ?_⟩
    rintro ⟨_, z₁, ⟨hz₁, _⟩, p, hp⟩
    obtain ⟨x, hx, hxX⟩ := hsep.2 hz₁ hz₂ p (fun w hw ↦ (hp w hw).1)
    exact (hp x hx).2 hxX

/-! ## Hypergraph separations and Menger's theorem for vertex separators -/

theorem separates_of_isSeparation (G : Hypergraph α β) {G₁ G₂ : Hypergraph α β}
    (hsep : G.IsSeparation G₁ G₂) {Z₁ Z₂ : Set α}
    (hZ₁ : Z₁ ⊆ G₁.vertexSet) (hZ₂ : Z₂ ⊆ G₂.vertexSet) :
    Separates G.skeleton G.vertexSet Z₁ Z₂ (G₁ ∩ G₂).vertexSet := by
  refine ⟨fun x hx ↦ hsep.left_le.vertexSet_subset hx.1, ?_⟩
  have hwalk : ∀ {u v : α} (p : G.skeleton.Walk u v), u ∈ G₁.vertexSet → v ∈ G₂.vertexSet →
      ∃ x ∈ p.support, x ∈ G₁.vertexSet ∧ x ∈ G₂.vertexSet := by
    intro u v p
    induction p with
    | nil =>
      intro hu hv
      exact ⟨_, Walk.start_mem_support _, hu, hv⟩
    | @cons u w v hadj q ih =>
      intro hu hv
      obtain ⟨_, e, heu, hew⟩ := hadj
      have he : e ∈ G₁.edgeSet ∪ G₂.edgeSet := by
        have : e ∈ (G₁ ∪ G₂).edgeSet := hsep.union_eq.symm ▸ G.edge_mem_of_inc heu
        exact this
      rcases he with he₁ | he₂
      · have hw₁ : w ∈ G₁.vertexSet := by
          have : w ∈ G₁.ends e := (hsep.left_le.ends_eq e he₁) ▸ hew
          exact G₁.vertex_mem_of_inc this
        obtain ⟨x, hx, hx1, hx2⟩ := ih hw₁ hv
        exact ⟨x, List.mem_cons_of_mem _ hx, hx1, hx2⟩
      · have hu₂ : u ∈ G₂.vertexSet := by
          have : u ∈ G₂.ends e := (hsep.right_le.ends_eq e he₂) ▸ heu
          exact G₂.vertex_mem_of_inc this
        exact ⟨u, List.Mem.head _, hu, hu₂⟩
  intro u v hu hv p _
  exact hwalk p (hZ₁ hu) (hZ₂ hv)

theorem exists_isSeparation_of_separates (G : Hypergraph α β) {Z₁ Z₂ X : Set α}
    (hZ₁ : Z₁ ⊆ G.vertexSet) (hZ₂ : Z₂ ⊆ G.vertexSet)
    (hsep : Separates G.skeleton G.vertexSet Z₁ Z₂ X) :
    ∃ G₁ G₂ : Hypergraph α β,
      G.IsSeparation G₁ G₂ ∧ Z₁ ⊆ G₁.vertexSet ∧ Z₂ ⊆ G₂.vertexSet ∧
        Hypergraph.separationOrder G₁ G₂ = X.ncard := by
  let C₁ := sepCompLeft G.skeleton G.vertexSet X Z₁
  let C₂ := sepCompRight G.skeleton G.vertexSet X Z₁
  have hC₁ : C₁ ⊆ G.vertexSet := sepCompLeft_subset _ _ _ _
  have hC₂ : C₂ ⊆ G.vertexSet := sepCompRight_subset _ _ _ _
  have hX : X ⊆ G.vertexSet := hsep.1
  have hE₂ : ∀ e ∈ G.edgeSet, ¬ (G.ends e ⊆ C₁ ∪ X) → G.ends e ⊆ C₂ ∪ X := by
    intro e he hnot v hv
    have hvV : v ∈ G.vertexSet := G.vertex_mem_of_inc hv
    obtain ⟨u, hu, hunot⟩ := Set.not_subset.1 hnot
    have huV : u ∈ G.vertexSet := G.vertex_mem_of_inc hu
    have huC₂ : u ∈ C₂ := by
      rcases subset_sepComp_union G.skeleton Z₁ huV with (hu1 | hu2) | huX
      · exact (hunot (Or.inl hu1)).elim
      · exact hu2
      · exact (hunot (Or.inr huX)).elim
    by_cases huv : u = v
    · exact Or.inl (huv ▸ huC₂)
    · have hadj : G.skeleton.Adj u v := ⟨huv, e, hu, hv⟩
      rcases subset_sepComp_union G.skeleton Z₁ hvV with (hv1 | hv2) | hvX
      · exact (not_adj_sepCompLeft_sepCompRight hv1 huC₂ hadj.symm).elim
      · exact Or.inl hv2
      · exact Or.inr hvX
  let E₁ : Set β := {e ∈ G.edgeSet | G.ends e ⊆ C₁ ∪ X}
  let G₁ : Hypergraph α β :=
    { vertexSet := C₁ ∪ X
      edgeSet := E₁
      Inc := fun e v ↦ e ∈ E₁ ∧ G.Inc e v
      vertex_mem_of_inc := fun e v ⟨he, hv⟩ ↦ he.2 hv
      edge_mem_of_inc := fun _ _ h ↦ h.1
      vertexSet_finite := G.vertexSet_finite.subset (Set.union_subset hC₁ hX)
      edgeSet_finite := G.edgeSet_finite.subset fun _ h ↦ h.1 }
  let G₂ : Hypergraph α β :=
    { vertexSet := C₂ ∪ X
      edgeSet := G.edgeSet \ E₁
      Inc := fun e v ↦ e ∈ G.edgeSet \ E₁ ∧ G.Inc e v
      vertex_mem_of_inc := fun e v ⟨he, hv⟩ ↦
        hE₂ e he.1 (fun hsub ↦ he.2 ⟨he.1, hsub⟩) hv
      edge_mem_of_inc := fun _ _ h ↦ h.1
      vertexSet_finite := G.vertexSet_finite.subset (Set.union_subset hC₂ hX)
      edgeSet_finite := G.edgeSet_finite.subset Set.sdiff_subset }
  refine ⟨G₁, G₂, ?_, subset_sepCompLeft_union G.skeleton hZ₁,
    subset_sepCompRight_union hZ₂ hsep, ?_⟩
  · refine ⟨⟨Set.union_subset hC₁ hX, fun _ h ↦ h.1, ?_⟩,
      ⟨Set.union_subset hC₂ hX, Set.sdiff_subset, ?_⟩, ?_, ?_⟩
    · intro e he
      ext v
      exact ⟨fun h ↦ ⟨he, h⟩, fun h ↦ h.2⟩
    · intro e he
      ext v
      exact ⟨fun h ↦ ⟨he, h⟩, fun h ↦ h.2⟩
    · refine Hypergraph.ext ?_ ?_ ?_
      · apply Set.Subset.antisymm
        · exact Set.union_subset (Set.union_subset hC₁ hX) (Set.union_subset hC₂ hX)
        · intro v hv
          rcases subset_sepComp_union G.skeleton Z₁ hv with (h1 | h2) | h3
          · exact Or.inl (Or.inl h1)
          · exact Or.inr (Or.inl h2)
          · exact Or.inl (Or.inr h3)
      · change G₁.edgeSet ∪ G₂.edgeSet = G.edgeSet
        ext e
        simp only [G₁, G₂, Set.mem_union, Set.mem_sdiff]
        exact ⟨fun h ↦ h.elim (fun h1 ↦ h1.1) (fun h2 ↦ h2.1),
          fun he ↦ em (e ∈ E₁) |>.imp_right fun hnot ↦ ⟨he, hnot⟩⟩
      · funext e v
        apply propext
        change (G₁.Inc e v ∨ G₂.Inc e v) ↔ G.Inc e v
        exact ⟨fun h ↦ h.elim (fun h1 ↦ h1.2) (fun h2 ↦ h2.2),
          fun hv ↦ em (e ∈ E₁) |>.imp (fun h1 ↦ ⟨h1, hv⟩)
            (fun h2 ↦ ⟨⟨G.edge_mem_of_inc hv, h2⟩, hv⟩)⟩
    · change E₁ ∩ (G.edgeSet \ E₁) = ∅
      ext e
      simp only [Set.mem_inter_iff, Set.mem_sdiff, Set.mem_empty_iff_false,
        iff_false, not_and]
      intro h1 _ h3
      exact h3 h1
  · unfold Hypergraph.separationOrder
    have hinter : (G₁ ∩ G₂).vertexSet = X := by
      change (C₁ ∪ X) ∩ (C₂ ∪ X) = X
      ext v
      simp only [Set.mem_inter_iff, Set.mem_union]
      constructor
      · rintro ⟨h1 | hX1, h2 | hX2⟩
        · exact (Set.disjoint_left.1 (disjoint_sepCompLeft_sepCompRight _ _ _ _) h1 h2).elim
        · exact hX2
        · exact hX1
        · exact hX1
      · intro hv
        exact ⟨Or.inr hv, Or.inr hv⟩
    rw [hinter]

/-- Menger's theorem on `(G.skeleton, G.vertexSet)` in terms of vertex separators `X`. -/
theorem hasDisjointPaths_iff_forall_separates
    (G : Hypergraph α β) {Z₁ Z₂ : Set α} (hZ₁ : Z₁ ⊆ G.vertexSet) (hZ₂ : Z₂ ⊆ G.vertexSet)
    (k : ℕ) :
    HasDisjointPaths G.skeleton Z₁ Z₂ k ↔
      ∀ X, Separates G.skeleton G.vertexSet Z₁ Z₂ X → k ≤ X.ncard := by
  rw [← menger.{u, v} G Z₁ Z₂ hZ₁ hZ₂ k]
  constructor
  · intro h X hsep
    obtain ⟨G₁, G₂, hsepG, h1, h2, hord⟩ := exists_isSeparation_of_separates G hZ₁ hZ₂ hsep
    exact hord ▸ h G₁ G₂ hsepG h1 h2
  · intro h G₁ G₂ hsepG h1 h2
    exact h (G₁ ∩ G₂).vertexSet (separates_of_isSeparation G hsepG h1 h2)

theorem exists_separates_lt_of_not_hasDisjointPaths
    (G : Hypergraph α β) {Z₁ Z₂ : Set α} (hZ₁ : Z₁ ⊆ G.vertexSet) (hZ₂ : Z₂ ⊆ G.vertexSet)
    {k : ℕ} (hnot : ¬ HasDisjointPaths G.skeleton Z₁ Z₂ k) :
    ∃ X, Separates G.skeleton G.vertexSet Z₁ Z₂ X ∧ X.ncard < k := by
  rw [hasDisjointPaths_iff_forall_separates G hZ₁ hZ₂ k, not_forall] at hnot
  obtain ⟨X, hX⟩ := hnot
  rw [not_imp, not_le] at hX
  exact ⟨X, hX.1, hX.2⟩

/-! ## Splitting the Menger paths `{P_x | x ∈ X}` of a minimum-order separator -/

theorem walk_support_subset_of_not_adj {K : SimpleGraph α} {V₀ C₁ C₂ X : Set α}
    (hcov : V₀ ⊆ C₁ ∪ C₂ ∪ X)
    (hno_adj : ∀ ⦃a b : α⦄, a ∈ C₁ → b ∈ C₂ → ¬ K.Adj a b)
    {u v : α} (p : K.Walk u v) (hp : p.IsPath) (hpV : ∀ w ∈ p.support, w ∈ V₀)
    (hpX : ∀ w ∈ p.support, w ∈ X → w = v) (hu : u ∈ C₁ ∪ X) :
    ∀ w ∈ p.support, w ∈ C₁ ∪ {v} := by
  induction p with
  | nil =>
    intro w hw
    simp only [Walk.support_nil, List.mem_singleton] at hw
    exact Or.inr hw
  | @cons u u' v hadj q ih =>
    intro w hw
    simp only [Walk.support_cons, List.mem_cons] at hw
    have huv : u ≠ v := by
      rintro rfl
      rw [Walk.cons_isPath_iff] at hp
      exact hp.2 q.end_mem_support
    have huC₁ : u ∈ C₁ := by
      rcases hu with hu1 | huX
      · exact hu1
      · exact (huv (hpX u (List.Mem.head _) huX)).elim
    rcases hw with rfl | hw
    · exact Or.inl huC₁
    · have hu'V := hpV u' (List.mem_cons_of_mem _ q.start_mem_support)
      have hu' : u' ∈ C₁ ∪ X := by
        rcases hcov hu'V with (hu'1 | hu'2) | hu'X
        · exact Or.inl hu'1
        · exact (hno_adj huC₁ hu'2 hadj).elim
        · exact Or.inr hu'X
      exact ih hp.of_cons (fun z hz ↦ hpV z (List.mem_cons_of_mem _ hz))
        (fun z hz hzX ↦ hpX z (List.mem_cons_of_mem _ hz) hzX) hu' w hw

/-- Given a minimum-order `Z₁`–`Z₂` separator `X` in `(G.skeleton, G.vertexSet)` and any partition
`G.vertexSet \ X = C₁ ∪ C₂` with no edges between `C₁` and `C₂`, `Z₁ ⊆ C₁ ∪ X`, and
`Z₂ ⊆ C₂ ∪ X`, Menger's theorem supplies pairwise disjoint paths `P_x^1` (`x ∈ X`) in
`G.vertexSet \ C₁` from `x` to `Z₂` and pairwise disjoint paths `P_x^2` (`x ∈ X`) in
`G.vertexSet \ C₂` from `x` to `Z₁` (Bellenbaum and Diestel, proof of Theorem 3, page 3). -/
theorem exists_menger_walks_of_min_sep
    (G : Hypergraph α β) {Z₁ Z₂ X C₁ C₂ : Set α}
    (hZ₁ : Z₁ ⊆ G.vertexSet) (hZ₂ : Z₂ ⊆ G.vertexSet)
    (hsep : Separates G.skeleton G.vertexSet Z₁ Z₂ X)
    (hmin : ∀ X', Separates G.skeleton G.vertexSet Z₁ Z₂ X' → X.ncard ≤ X'.ncard)
    (hcov : G.vertexSet ⊆ C₁ ∪ C₂ ∪ X)
    (hdisj : Disjoint C₁ C₂) (hdisj₁ : Disjoint C₁ X) (hdisj₂ : Disjoint C₂ X)
    (hno_adj : ∀ ⦃a b : α⦄, a ∈ C₁ → b ∈ C₂ → ¬ G.skeleton.Adj a b)
    (hZ₁C : Z₁ ⊆ C₁ ∪ X) (hZ₂C : Z₂ ⊆ C₂ ∪ X) :
    ∃ (end₁ end₂ : α → α)
      (_ : ∀ x ∈ X, end₁ x ∈ Z₁)
      (_ : ∀ x ∈ X, end₂ x ∈ Z₂)
      (P₁ : ∀ x ∈ X, G.skeleton.Walk x (end₂ x))
      (P₂ : ∀ x ∈ X, G.skeleton.Walk x (end₁ x)),
      (∀ x (hx : x ∈ X), ∀ z ∈ (P₁ x hx).support, z ∈ G.vertexSet \ C₁) ∧
      (∀ x (hx : x ∈ X) y (hy : y ∈ X), x ≠ y →
        Disjoint {z | z ∈ (P₁ x hx).support} {z | z ∈ (P₁ y hy).support}) ∧
      (∀ x (hx : x ∈ X), ∀ z ∈ (P₂ x hx).support, z ∈ G.vertexSet \ C₂) ∧
      (∀ x (hx : x ∈ X) y (hy : y ∈ X), x ≠ y →
        Disjoint {z | z ∈ (P₂ x hx).support} {z | z ∈ (P₂ y hy).support}) := by
  classical
  have hpaths : HasDisjointPaths G.skeleton Z₁ Z₂ X.ncard :=
    (hasDisjointPaths_iff_forall_separates G hZ₁ hZ₂ X.ncard).2 hmin
  obtain ⟨Q, hQ⟩ := hpaths
  have hQ_V : ∀ (i : Fin X.ncard) (z : α), z ∈ (Q i).walk.support → z ∈ G.vertexSet := by
    intro i z hz
    have hwalk : ∀ {u v : α} (w : G.skeleton.Walk u v), u ∈ G.vertexSet →
        ∀ z ∈ w.support, z ∈ G.vertexSet := by
      intro u v w hu z hz
      induction w with
      | nil =>
        simp only [Walk.support_nil, List.mem_singleton] at hz
        exact hz ▸ hu
      | cons hadj q ih =>
        simp only [Walk.support_cons, List.mem_cons] at hz
        rcases hz with rfl | hz
        · exact hu
        · obtain ⟨_, e, _, hew⟩ := hadj
          exact ih (G.vertex_mem_of_inc hew) hz
    exact hwalk (Q i).walk (hZ₁ (Q i).first_mem) z hz
  have hex : ∀ i : Fin X.ncard, ∃ x ∈ (Q i).walk.support, x ∈ X :=
    fun i ↦ hsep.2 (Q i).first_mem (Q i).last_mem (Q i).walk (hQ_V i)
  have : Fintype X := (G.vertexSet_finite.subset hsep.1).fintype
  let g : Fin X.ncard → X := fun i ↦ ⟨(hex i).choose, (hex i).choose_spec.2⟩
  have hg_inj : Function.Injective g := by
    intro i j hij
    by_contra hne
    have h1 : (g i).1 ∈ (Q i).walk.support := (hex i).choose_spec.1
    have h2 : (g i).1 ∈ (Q j).walk.support :=
      (congrArg Subtype.val hij) ▸ (hex j).choose_spec.1
    exact Set.disjoint_left.1 (hQ hne) h1 h2
  have hcard_eq : Fintype.card (Fin X.ncard) = Fintype.card X := by
    rw [Fintype.card_fin, Set.ncard_eq_toFinset_card X (G.vertexSet_finite.subset hsep.1),
      Set.Finite.card_toFinset]
  have hg_bij : Function.Bijective g :=
    (Fintype.bijective_iff_injective_and_card g).2 ⟨hg_inj, hcard_eq⟩
  have hg_uniq : ∀ (i : Fin X.ncard) (y : α), y ∈ (Q i).walk.support → y ∈ X → y = (g i).1 := by
    intro i y hyQ hyX
    obtain ⟨j, hj⟩ := hg_bij.2 ⟨y, hyX⟩
    have hj' : (g j).1 = y := congrArg Subtype.val hj
    have hyj : y ∈ (Q j).walk.support := hj' ▸ (hex j).choose_spec.1
    have hij : i = j := by
      by_contra hne
      exact Set.disjoint_left.1 (hQ hne) hyQ hyj
    exact hij ▸ hj'.symm
  have hx_idx : ∀ x ∈ X, ∃ i : Fin X.ncard, (g i).1 = x := by
    intro x hx
    obtain ⟨i, hi⟩ := hg_bij.2 ⟨x, hx⟩
    exact ⟨i, congrArg Subtype.val hi⟩
  let idx : ∀ x ∈ X, Fin X.ncard := fun x hx ↦ (hx_idx x hx).choose
  have hidx_eq : ∀ x (hx : x ∈ X), (g (idx x hx)).1 = x :=
    fun x hx ↦ (hx_idx x hx).choose_spec
  have hidx_mem : ∀ x (hx : x ∈ X), x ∈ (Q (idx x hx)).walk.support := by
    intro x hx
    have h1 : (g (idx x hx)).1 ∈ (Q (idx x hx)).walk.support := (hex (idx x hx)).choose_spec.1
    rwa [hidx_eq x hx] at h1
  have hidx_inj : ∀ x (hx : x ∈ X) y (hy : y ∈ X), x ≠ y → idx x hx ≠ idx y hy := by
    intro x hx y hy hne heq
    apply hne
    rw [← hidx_eq x hx, ← hidx_eq y hy, heq]
  let end₁ : α → α := fun x ↦ if hx : x ∈ X then (Q (idx x hx)).first else x
  let end₂ : α → α := fun x ↦ if hx : x ∈ X then (Q (idx x hx)).last else x
  have hend₁_eq : ∀ x (hx : x ∈ X), end₁ x = (Q (idx x hx)).first :=
    fun x hx ↦ dite_eq_left hx
  have hend₂_eq : ∀ x (hx : x ∈ X), end₂ x = (Q (idx x hx)).last :=
    fun x hx ↦ dite_eq_left hx
  refine ⟨end₁, end₂,
    fun x hx ↦ hend₁_eq x hx ▸ (Q (idx x hx)).first_mem,
    fun x hx ↦ hend₂_eq x hx ▸ (Q (idx x hx)).last_mem,
    fun x hx ↦ ((Q (idx x hx)).walk.dropUntil x (hidx_mem x hx)).copy rfl (hend₂_eq x hx).symm,
    fun x hx ↦ ((Q (idx x hx)).walk.takeUntil x (hidx_mem x hx)).reverse.copy rfl
      (hend₁_eq x hx).symm,
    ?_, ?_, ?_, ?_⟩
  · intro x hx z hz
    rw [Walk.support_copy] at hz
    have hzQ : z ∈ (Q (idx x hx)).walk.support :=
      Walk.support_dropUntil_subset_support _ _ hz
    have hcov' : G.vertexSet ⊆ C₂ ∪ C₁ ∪ X := by
      intro w hw
      rcases hcov hw with (h1 | h2) | h3
      · exact Or.inl (Or.inr h1)
      · exact Or.inl (Or.inl h2)
      · exact Or.inr h3
    have hno' : ∀ ⦃a b : α⦄, a ∈ C₂ → b ∈ C₁ → ¬ G.skeleton.Adj a b :=
      fun a b ha hb hadj ↦ hno_adj hb ha hadj.symm
    have hmem := walk_support_subset_of_not_adj hcov' hno'
      ((Q (idx x hx)).walk.dropUntil x (hidx_mem x hx)).reverse
      ((Q (idx x hx)).isPath.dropUntil (hidx_mem x hx)).reverse
      (fun w hw ↦ by
        rw [Walk.support_reverse, List.mem_reverse] at hw
        exact hQ_V _ w (Walk.support_dropUntil_subset_support _ _ hw))
      (fun w hw hwX ↦ by
        rw [Walk.support_reverse, List.mem_reverse] at hw
        have := hg_uniq (idx x hx) w (Walk.support_dropUntil_subset_support _ _ hw) hwX
        exact this.trans (hidx_eq x hx))
      (hZ₂C (Q (idx x hx)).last_mem) z
      (by rwa [Walk.support_reverse, List.mem_reverse])
    refine ⟨hQ_V _ z hzQ, ?_⟩
    rcases hmem with hzC₂ | rfl
    · exact Set.disjoint_right.1 hdisj hzC₂
    · exact Set.disjoint_right.1 hdisj₁ hx
  · intro x hx y hy hne
    rw [Set.disjoint_left]
    intro z hzx hzy
    simp only [Set.mem_ofPred_eq, Walk.support_copy] at hzx hzy
    exact Set.disjoint_left.1 (hQ (hidx_inj x hx y hy hne))
      (Walk.support_dropUntil_subset_support _ _ hzx)
      (Walk.support_dropUntil_subset_support _ _ hzy)
  · intro x hx z hz
    rw [Walk.support_copy, Walk.support_reverse, List.mem_reverse] at hz
    have hzQ : z ∈ (Q (idx x hx)).walk.support :=
      Walk.support_takeUntil_subset_support _ _ hz
    have hmem := walk_support_subset_of_not_adj hcov hno_adj
      ((Q (idx x hx)).walk.takeUntil x (hidx_mem x hx))
      ((Q (idx x hx)).isPath.takeUntil (hidx_mem x hx))
      (fun w hw ↦ hQ_V _ w (Walk.support_takeUntil_subset_support _ _ hw))
      (fun w hw hwX ↦ (hg_uniq (idx x hx) w (Walk.support_takeUntil_subset_support _ _ hw)
        hwX).trans
        (hidx_eq x hx))
      (hZ₁C (Q (idx x hx)).first_mem) z hz
    refine ⟨hQ_V _ z hzQ, ?_⟩
    rcases hmem with hzC₁ | rfl
    · exact Set.disjoint_left.1 hdisj hzC₁
    · exact Set.disjoint_right.1 hdisj₂ hx
  · intro x hx y hy hne
    rw [Set.disjoint_left]
    intro z hzx hzy
    simp only [Set.mem_ofPred_eq, Walk.support_copy, Walk.support_reverse, List.mem_reverse]
      at hzx hzy
    exact Set.disjoint_left.1 (hQ (hidx_inj x hx y hy hne))
      (Walk.support_takeUntil_subset_support _ _ hzx)
      (Walk.support_takeUntil_subset_support _ _ hzy)

end GraphMinor.Thomas
