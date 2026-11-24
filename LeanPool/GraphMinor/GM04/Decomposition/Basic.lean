/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM04.Axioms
public import LeanPool.GraphMinor.GM04.TreeLemma.Basic

/-!
# Basic properties of rooted trees, hypergraphs, and tree-decompositions

This file proves fundamental lemmas about hypergraphs, rooted trees, `cross`, `edgeOrder`, and
tree-decompositions, including Graph Minors IV, (3.1): for every edge `f` of `T`,
`(τ × T^f, τ × T_f)` is a separation of `G`, and its order `edgeOrder T τ f` equals
`|V(τ(f)⁻ ∩ τ(parent f)⁻)| = |πBar(τ(f))|`.
-/

public section

namespace GraphMinor

variable {α β ι : Type*}

namespace Hypergraph

@[simp]
theorem mem_ends_iff (G : Hypergraph α β) (e : β) (v : α) : v ∈ G.ends e ↔ G.Inc e v := Iff.rfl

@[simp]
theorem union_vertexSet (G₁ G₂ : Hypergraph α β) :
    (G₁ ∪ G₂).vertexSet = G₁.vertexSet ∪ G₂.vertexSet := rfl

@[simp]
theorem union_edgeSet (G₁ G₂ : Hypergraph α β) :
    (G₁ ∪ G₂).edgeSet = G₁.edgeSet ∪ G₂.edgeSet := rfl

@[simp]
theorem union_inc (G₁ G₂ : Hypergraph α β) (e : β) (v : α) :
    (G₁ ∪ G₂).Inc e v ↔ G₁.Inc e v ∨ G₂.Inc e v := Iff.rfl

@[simp]
theorem inter_vertexSet (G₁ G₂ : Hypergraph α β) :
    (G₁ ∩ G₂).vertexSet = G₁.vertexSet ∩ G₂.vertexSet := rfl

@[simp]
theorem inter_edgeSet (G₁ G₂ : Hypergraph α β) :
    (G₁ ∩ G₂).edgeSet = G₁.edgeSet ∩ G₂.edgeSet := rfl

@[simp]
theorem inter_inc (G₁ G₂ : Hypergraph α β) (e : β) (v : α) :
    (G₁ ∩ G₂).Inc e v ↔ G₁.Inc e v ∧ G₂.Inc e v := Iff.rfl

@[simp]
theorem biUnion_vertexSet (s : Finset ι) (G : ι → Hypergraph α β) :
    (biUnion s G).vertexSet = ⋃ i ∈ s, (G i).vertexSet := rfl

@[simp]
theorem biUnion_edgeSet (s : Finset ι) (G : ι → Hypergraph α β) :
    (biUnion s G).edgeSet = ⋃ i ∈ s, (G i).edgeSet := rfl

@[simp]
theorem biUnion_inc (s : Finset ι) (G : ι → Hypergraph α β) (e : β) (v : α) :
    (biUnion s G).Inc e v ↔ ∃ i ∈ s, (G i).Inc e v := Iff.rfl

theorem inc_of_le {H G : Hypergraph α β} (h : H ≤ G) {e : β} {v : α} (hev : H.Inc e v) :
    G.Inc e v := by
  have he : e ∈ H.edgeSet := H.edge_mem_of_inc hev
  have h_ends := h.ends_eq e he
  exact (Set.ext_iff.mp h_ends v).mpr hev

theorem inc_iff_of_le {H G : Hypergraph α β} (h : H ≤ G) {e : β} (he : e ∈ H.edgeSet) (v : α) :
    G.Inc e v ↔ H.Inc e v :=
  Set.ext_iff.mp (h.ends_eq e he) v

theorem eq_of_le_of_subset {H G : Hypergraph α β} (h : H ≤ G)
    (hV : G.vertexSet ⊆ H.vertexSet) (hE : G.edgeSet ⊆ H.edgeSet) : H = G :=
  le_antisymm h
    { vertexSet_subset := hV
      edgeSet_subset := hE
      ends_eq := fun e he ↦ (h.ends_eq e (hE he)).symm }

theorem union_le {G₁ G₂ G : Hypergraph α β} (h₁ : G₁ ≤ G) (h₂ : G₂ ≤ G) : G₁ ∪ G₂ ≤ G where
  vertexSet_subset := Set.union_subset h₁.vertexSet_subset h₂.vertexSet_subset
  edgeSet_subset := Set.union_subset h₁.edgeSet_subset h₂.edgeSet_subset
  ends_eq e he := by
    ext v
    simp only [mem_ends_iff, union_inc]
    rcases he with he₁ | he₂
    · exact ⟨fun hv ↦ Or.inl ((inc_iff_of_le h₁ he₁ v).mp hv),
        fun h ↦ h.elim (inc_of_le h₁) (inc_of_le h₂)⟩
    · exact ⟨fun hv ↦ Or.inr ((inc_iff_of_le h₂ he₂ v).mp hv),
        fun h ↦ h.elim (inc_of_le h₁) (inc_of_le h₂)⟩

theorem le_union_left {G₁ G₂ G : Hypergraph α β} (h₁ : G₁ ≤ G) (h₂ : G₂ ≤ G) :
    G₁ ≤ G₁ ∪ G₂ where
  vertexSet_subset := Set.subset_union_left
  edgeSet_subset := Set.subset_union_left
  ends_eq e he := by
    ext v
    simp only [mem_ends_iff, union_inc]
    exact ⟨fun h ↦ h.elim id fun h' ↦ (inc_iff_of_le h₁ he v).mp (inc_of_le h₂ h'), Or.inl⟩

theorem le_union_right {G₁ G₂ G : Hypergraph α β} (h₁ : G₁ ≤ G) (h₂ : G₂ ≤ G) :
    G₂ ≤ G₁ ∪ G₂ where
  vertexSet_subset := Set.subset_union_right
  edgeSet_subset := Set.subset_union_right
  ends_eq e he := by
    ext v
    simp only [mem_ends_iff, union_inc]
    exact ⟨fun h ↦ h.elim (fun h' ↦ (inc_iff_of_le h₂ he v).mp (inc_of_le h₁ h')) id, Or.inr⟩

theorem inter_le_left {G₁ G₂ G : Hypergraph α β} (h₁ : G₁ ≤ G) (h₂ : G₂ ≤ G) :
    G₁ ∩ G₂ ≤ G₁ where
  vertexSet_subset := Set.inter_subset_left
  edgeSet_subset := Set.inter_subset_left
  ends_eq e he := by
    ext v
    simp only [mem_ends_iff, inter_inc]
    exact ⟨fun hv ↦ ⟨hv, (inc_iff_of_le h₂ he.2 v).mp (inc_of_le h₁ hv)⟩, And.left⟩

theorem inter_le_right {G₁ G₂ G : Hypergraph α β} (h₁ : G₁ ≤ G) (h₂ : G₂ ≤ G) :
    G₁ ∩ G₂ ≤ G₂ where
  vertexSet_subset := Set.inter_subset_right
  edgeSet_subset := Set.inter_subset_right
  ends_eq e he := by
    ext v
    simp only [mem_ends_iff, inter_inc]
    exact ⟨fun hv ↦ ⟨(inc_iff_of_le h₁ he.1 v).mp (inc_of_le h₂ hv), hv⟩, And.right⟩

theorem le_inter {H G₁ G₂ : Hypergraph α β} (h₁ : H ≤ G₁) (h₂ : H ≤ G₂) : H ≤ G₁ ∩ G₂ where
  vertexSet_subset := Set.subset_inter h₁.vertexSet_subset h₂.vertexSet_subset
  edgeSet_subset := Set.subset_inter h₁.edgeSet_subset h₂.edgeSet_subset
  ends_eq e he := by
    ext v
    simp only [mem_ends_iff, inter_inc]
    exact ⟨And.left ∘ fun ⟨hv₁, _⟩ ↦ ⟨(inc_iff_of_le h₁ he v).mp hv₁, True.intro⟩,
      fun hv ↦ ⟨inc_of_le h₁ hv, inc_of_le h₂ hv⟩⟩

theorem inter_comm (G₁ G₂ : Hypergraph α β) : G₁ ∩ G₂ = G₂ ∩ G₁ :=
  Hypergraph.ext (Set.inter_comm _ _) (Set.inter_comm _ _) (funext₂ fun _ _ ↦ propext and_comm)

theorem union_comm (G₁ G₂ : Hypergraph α β) : G₁ ∪ G₂ = G₂ ∪ G₁ :=
  Hypergraph.ext (Set.union_comm _ _) (Set.union_comm _ _) (funext₂ fun _ _ ↦ propext or_comm)

theorem biUnion_le {s : Finset ι} {G : ι → Hypergraph α β} {H : Hypergraph α β}
    (h : ∀ i ∈ s, G i ≤ H) : biUnion s G ≤ H where
  vertexSet_subset := Set.iUnion₂_subset fun i hi ↦ (h i hi).vertexSet_subset
  edgeSet_subset := Set.iUnion₂_subset fun i hi ↦ (h i hi).edgeSet_subset
  ends_eq e he := by
    obtain ⟨i, hi, hei⟩ := Set.mem_iUnion₂.mp he
    ext v
    simp only [mem_ends_iff, biUnion_inc]
    refine ⟨fun hv ↦ ⟨i, hi, (inc_iff_of_le (h i hi) hei v).mp hv⟩, ?_⟩
    rintro ⟨j, hj, hv⟩
    exact inc_of_le (h j hj) hv

theorem biUnion_mono {s₁ s₂ : Finset ι} {G : ι → Hypergraph α β} {H : Hypergraph α β}
    (hs : s₁ ⊆ s₂) (h : ∀ i ∈ s₂, G i ≤ H) : biUnion s₁ G ≤ biUnion s₂ G where
  vertexSet_subset := Set.biUnion_subset_biUnion_left hs
  edgeSet_subset := Set.biUnion_subset_biUnion_left hs
  ends_eq e he := by
    obtain ⟨i, hi, hei⟩ := Set.mem_iUnion₂.mp he
    ext v
    simp only [mem_ends_iff, biUnion_inc]
    refine ⟨?_, fun ⟨j, hj, hv⟩ ↦ ⟨j, hs hj, hv⟩⟩
    rintro ⟨j, hj, hv⟩
    exact ⟨i, hi, (inc_iff_of_le (h i (hs hi)) hei v).mp (inc_of_le (h j hj) hv)⟩

theorem le_biUnion {s : Finset ι} {G : ι → Hypergraph α β} {H : Hypergraph α β}
    (h : ∀ i ∈ s, G i ≤ H) {i : ι} (hi : i ∈ s) : G i ≤ biUnion s G where
  vertexSet_subset _ hv := Set.mem_biUnion hi hv
  edgeSet_subset _ he := Set.mem_biUnion hi he
  ends_eq e he := by
    ext v
    simp only [mem_ends_iff, biUnion_inc]
    refine ⟨?_, fun hv ↦ ⟨i, hi, hv⟩⟩
    rintro ⟨j, hj, hv⟩
    exact (inc_iff_of_le (h i hi) he v).mp (inc_of_le (h j hj) hv)

theorem biUnion_insert_of_mem [DecidableEq ι] {s : Finset ι} {r : ι} (hr : r ∈ s)
    (G : ι → Hypergraph α β) : biUnion (insert r s) G = biUnion s G := by
  rw [Finset.insert_eq_of_mem hr]

theorem biUnion_union [DecidableEq ι] (s₁ s₂ : Finset ι) (G : ι → Hypergraph α β) :
    biUnion (s₁ ∪ s₂) G = biUnion s₁ G ∪ biUnion s₂ G := by
  ext x <;> simp [or_and_right, exists_or]

theorem biUnion_congr {s₁ s₂ : Finset ι} (hs : s₁ = s₂) {G₁ G₂ : ι → Hypergraph α β}
    (hG : ∀ i ∈ s₁, G₁ i = G₂ i) : biUnion s₁ G₁ = biUnion s₂ G₂ := by
  subst hs
  ext x
  · simp only [biUnion_vertexSet, Set.mem_iUnion]
    exact exists_congr fun i ↦ exists_congr fun hi ↦ by rw [hG i hi]
  · simp only [biUnion_edgeSet, Set.mem_iUnion]
    exact exists_congr fun i ↦ exists_congr fun hi ↦ by rw [hG i hi]
  · simp only [biUnion_inc]
    exact exists_congr fun i ↦ and_congr_right fun hi ↦ by rw [hG i hi]

theorem separationOrder_comm (G₁ G₂ : Hypergraph α β) :
    separationOrder G₁ G₂ = separationOrder G₂ G₁ := by
  simp only [separationOrder, inter_comm]

theorem IsSeparation.symm {G G₁ G₂ : Hypergraph α β} (h : G.IsSeparation G₁ G₂) :
    G.IsSeparation G₂ G₁ where
  left_le := h.right_le
  right_le := h.left_le
  union_eq := (union_comm G₂ G₁).trans h.union_eq
  edgeSet_inter_eq := by rw [inter_comm, h.edgeSet_inter_eq]

end Hypergraph

namespace RootedHypergraph

@[ext]
theorem ext {G₁ G₂ : RootedHypergraph α β} (h₁ : G₁.toHypergraph = G₂.toHypergraph)
    (h₂ : G₁.roots = G₂.roots) : G₁ = G₂ := by
  cases G₁
  cases G₂
  congr

@[simp]
theorem mem_rootSet_iff (G : RootedHypergraph α β) (v : α) : v ∈ G.rootSet ↔ v ∈ G.roots :=
  Iff.rfl

theorem rootSet_subset_vertexSet (G : RootedHypergraph α β) : G.rootSet ⊆ G.vertexSet :=
  G.roots_subset

theorem rootSet_finite (G : RootedHypergraph α β) : G.rootSet.Finite :=
  G.vertexSet_finite.subset G.rootSet_subset_vertexSet

@[simp]
theorem ncard_rootSet (G : RootedHypergraph α β) : G.rootSet.ncard = G.roots.length := by
  classical
  have h : G.rootSet = (G.roots.toFinset : Set α) := by
    ext v
    simp [rootSet]
  rw [h, Set.ncard_coe_finset, List.toFinset_card_of_nodup G.roots_nodup]

end RootedHypergraph

namespace GM04

namespace RootedTree

variable (T : RootedTree ι)

theorem mem_edges_iff {f : ι} : f ∈ T.edges ↔ f ∈ T.verts ∧ f ≠ T.root := by
  classical
  simp [edges, and_comm]

theorem parent_iterate_mem {v : ι} (hv : v ∈ T.verts) : ∀ n, T.parent^[n] v ∈ T.verts :=
  T.iterate_parent_mem hv

theorem parent_iterate_root : ∀ n, T.parent^[n] T.root = T.root :=
  T.iterate_parent_root

theorem parent_iterate_eq_root_of_le {v : ι} {m n : ℕ} (hm : T.parent^[m] v = T.root)
    (hmn : m ≤ n) : T.parent^[n] v = T.root :=
  T.iterate_parent_eq_root_of_le hm hmn

theorem reaches_mem_left {u v : ι} (h : T.Reaches u v) : u ∈ T.verts :=
  h.verts_left T

theorem reaches_mem_right {u v : ι} (h : T.Reaches u v) : v ∈ T.verts := h.1

theorem reaches_trans {u v w : ι} (huv : T.Reaches u v) (hvw : T.Reaches v w) :
    T.Reaches u w :=
  huv.trans T hvw

theorem reaches_root {v : ι} (hv : v ∈ T.verts) : T.Reaches T.root v :=
  T.root_reaches hv

theorem reaches_antisymm {u v : ι} (huv : T.Reaches u v) (hvu : T.Reaches v u) : u = v :=
  huv.antisymm T hvu

theorem reaches_total_of_reaches {x y v : ι} (hx : T.Reaches x v) (hy : T.Reaches y v) :
    T.Reaches x y ∨ T.Reaches y x :=
  hx.total_of_reaches T hy

theorem reaches_parent_of_reaches_of_ne {u v : ι} (h : T.Reaches u v) (hne : u ≠ v) :
    T.Reaches u (T.parent v) :=
  (h.ne_imp_mem_edges_and_reaches_parent T hne).2

theorem mem_edges_of_reaches_of_ne {u v : ι} (h : T.Reaches u v) (hne : u ≠ v) :
    v ∈ T.edges :=
  (h.ne_imp_mem_edges_and_reaches_parent T hne).1

theorem reaches_iff_eq_or_reaches_parent {u v : ι} (hv : v ∈ T.verts) :
    T.Reaches u v ↔ u = v ∨ T.Reaches u (T.parent v) := by
  refine ⟨fun h ↦ h.eq_or_reaches_parent T, ?_⟩
  rintro (rfl | h)
  · exact T.reaches_refl hv
  · exact T.reaches_trans h (T.reaches_parent hv)

theorem subtreeAt_mono {u v : ι} (h : T.Reaches u v) : T.subtreeAt v ⊆ T.subtreeAt u :=
  T.subtreeAt_subset_of_reaches h

theorem parent_mem_rootSide {f : ι} (hf : f ∈ T.edges) : T.parent f ∈ T.rootSide f :=
  T.mem_rootSide.mpr ⟨T.parent_mem f (T.edges_subset_verts hf), T.not_reaches_parent hf⟩

theorem subtreeAt_union_rootSide [DecidableEq ι] (f : ι) :
    T.subtreeAt f ∪ T.rootSide f = T.verts := by
  ext x
  simp only [Finset.mem_union, T.mem_subtreeAt, T.mem_rootSide]
  exact ⟨fun h ↦ h.elim (fun h ↦ h.1) And.left,
    fun hx ↦ by
      by_cases h : T.Reaches f x
      · exact Or.inl h
      · exact Or.inr ⟨hx, h⟩⟩

theorem onPath_symm {t₁ t₂ t : ι} : T.OnPath t₁ t₂ t ↔ T.OnPath t₂ t₁ t := by
  simp only [OnPath, or_comm]
  exact and_congr_right' ⟨fun h x h₂ h₁ ↦ h x h₁ h₂, fun h x h₁ h₂ ↦ h x h₂ h₁⟩

theorem onPath_left {t₁ t₂ : ι} (ht₁ : t₁ ∈ T.verts) : T.OnPath t₁ t₂ t₁ :=
  ⟨Or.inl (T.reaches_refl ht₁), fun _ hx₁ _ ↦ hx₁⟩

theorem onPath_right {t₁ t₂ : ι} (ht₂ : t₂ ∈ T.verts) : T.OnPath t₁ t₂ t₂ :=
  ⟨Or.inr (T.reaches_refl ht₂), fun _ _ hx₂ ↦ hx₂⟩

theorem onPath_of_reaches {t₁ t₂ t : ι} (h₁ : T.Reaches t₁ t) (h₂ : T.Reaches t t₂) :
    T.OnPath t₁ t₂ t :=
  ⟨Or.inr h₂, fun _ hx₁ _ ↦ T.reaches_trans hx₁ h₁⟩

theorem onPath_head_of_mem_subtreeAt_of_mem_rootSide {f t₁ t₃ : ι}
    (ht₁ : t₁ ∈ T.subtreeAt f) (ht₃ : t₃ ∈ T.rootSide f) : T.OnPath t₁ t₃ f := by
  have hf₁ : T.Reaches f t₁ := T.mem_subtreeAt.mp ht₁
  have hf₃ : ¬ T.Reaches f t₃ := (T.mem_rootSide.mp ht₃).2
  refine ⟨Or.inl hf₁, fun x hx₁ hx₃ ↦ ?_⟩
  rcases T.reaches_total_of_reaches hx₁ hf₁ with hxf | hfx
  · exact hxf
  · exact absurd (T.reaches_trans hfx hx₃) hf₃

theorem onPath_parent_of_mem_subtreeAt_of_mem_rootSide {f t₁ t₃ : ι} (hf : f ∈ T.edges)
    (ht₁ : t₁ ∈ T.subtreeAt f) (ht₃ : t₃ ∈ T.rootSide f) : T.OnPath t₁ t₃ (T.parent f) := by
  have hfv : f ∈ T.verts := T.edges_subset_verts hf
  have hf₁ : T.Reaches f t₁ := T.mem_subtreeAt.mp ht₁
  have hf₃ : ¬ T.Reaches f t₃ := (T.mem_rootSide.mp ht₃).2
  refine ⟨Or.inl (T.reaches_trans (T.reaches_parent hfv) hf₁), fun x hx₁ hx₃ ↦ ?_⟩
  have hxf : T.Reaches x f := (T.onPath_head_of_mem_subtreeAt_of_mem_rootSide ht₁ ht₃).2 x hx₁ hx₃
  rcases (T.reaches_iff_eq_or_reaches_parent hfv).mp hxf with rfl | hxp
  · exact absurd hx₃ hf₃
  · exact hxp

theorem onPathEdge_symm {t₁ t₂ f : ι} : T.OnPathEdge t₁ t₂ f ↔ T.OnPathEdge t₂ t₁ f := by
  simp only [OnPathEdge, T.onPath_symm]

theorem onPathEdge_iff {t₁ t₂ f : ι} (ht₁ : t₁ ∈ T.verts) (ht₂ : t₂ ∈ T.verts) :
    T.OnPathEdge t₁ t₂ f ↔
      f ∈ T.edges ∧ ((t₁ ∈ T.subtreeAt f ∧ t₂ ∈ T.rootSide f) ∨
        (t₂ ∈ T.subtreeAt f ∧ t₁ ∈ T.rootSide f)) := by
  refine ⟨?_, ?_⟩
  · rintro ⟨hf, hhead, hpar⟩
    refine ⟨hf, ?_⟩
    rcases hhead.1 with hf₁ | hf₂
    · left
      refine ⟨T.mem_subtreeAt.mpr hf₁, T.mem_rootSide.mpr ⟨ht₂, fun hf₂ ↦ ?_⟩⟩
      exact T.not_reaches_parent hf (hpar.2 f hf₁ hf₂)
    · right
      refine ⟨T.mem_subtreeAt.mpr hf₂, T.mem_rootSide.mpr ⟨ht₁, fun hf₁ ↦ ?_⟩⟩
      exact T.not_reaches_parent hf (hpar.2 f hf₁ hf₂)
  · rintro ⟨hf, ⟨h₁, h₂⟩ | ⟨h₂, h₁⟩⟩
    · exact ⟨hf, T.onPath_head_of_mem_subtreeAt_of_mem_rootSide h₁ h₂,
        T.onPath_parent_of_mem_subtreeAt_of_mem_rootSide hf h₁ h₂⟩
    · rw [T.onPathEdge_symm]
      exact ⟨hf, T.onPath_head_of_mem_subtreeAt_of_mem_rootSide h₂ h₁,
        T.onPath_parent_of_mem_subtreeAt_of_mem_rootSide hf h₂ h₁⟩

@[simp]
theorem mem_children_iff {s v : ι} : v ∈ T.children s ↔ v ∈ T.edges ∧ T.parent v = s := by
  classical
  simp [children]

theorem children_subset_edges (s : ι) : T.children s ⊆ T.edges := by
  intro v hv
  exact (T.mem_children_iff.mp hv).1

theorem children_subset_verts (s : ι) : T.children s ⊆ T.verts :=
  (T.children_subset_edges s).trans T.edges_subset_verts

theorem self_notMem_children (s : ι) : s ∉ T.children s := by
  rw [T.mem_children_iff]
  rintro ⟨hs, hpar⟩
  exact T.parent_ne_self hs hpar

@[simp]
theorem starAt_root (s : ι) : (T.starAt s).root = s := rfl

@[simp]
theorem starAt_parent (s v : ι) : (T.starAt s).parent v = s := rfl

@[simp]
theorem mem_starAt_verts {s v : ι} : v ∈ (T.starAt s).verts ↔ v = s ∨ v ∈ T.children s := by
  classical
  simp [starAt]

@[simp]
theorem starAt_edges (s : ι) : (T.starAt s).edges = T.children s := by
  ext v
  simp only [mem_edges_iff, mem_starAt_verts, starAt_root]
  refine ⟨?_, fun hv ↦ ⟨Or.inr hv, fun h ↦ T.self_notMem_children s (h ▸ hv)⟩⟩
  rintro ⟨rfl | hv, hne⟩
  · exact absurd rfl hne
  · exact hv

theorem isStar_starAt (s : ι) : (T.starAt s).IsStar :=
  fun _ _ ↦ rfl

theorem reaches_starAt {s u v : ι} (h : (T.starAt s).Reaches u v) : u = v ∨ u = s := by
  obtain ⟨_, n, hn⟩ := h
  cases n with
  | zero => exact Or.inl hn.symm
  | succ k =>
    rw [Function.iterate_succ_apply'] at hn
    exact Or.inr hn.symm

theorem reaches_iff_eq_or_exists_children {s x : ι} (hs : s ∈ T.verts) :
    T.Reaches s x ↔ x = s ∨ ∃ t ∈ T.children s, T.Reaches t x := by
  refine ⟨?_, ?_⟩
  · rintro ⟨hx, n, h⟩
    induction n generalizing x with
    | zero => exact Or.inl h
    | succ k ih =>
      by_cases hxs : x = s
      · exact Or.inl hxs
      · have hxe : x ∈ T.edges := T.mem_edges_of_reaches_of_ne ⟨hx, k + 1, h⟩ (Ne.symm hxs)
        rw [Function.iterate_succ_apply] at h
        rcases ih (T.parent_mem x hx) h with hpar | ⟨t, ht, htx⟩
        · exact Or.inr ⟨x, T.mem_children_iff.mpr ⟨hxe, hpar⟩, T.reaches_refl hx⟩
        · exact Or.inr ⟨t, ht, T.reaches_trans htx (T.reaches_parent hx)⟩
  · rintro (rfl | ⟨t, ht, htx⟩)
    · exact T.reaches_refl hs
    · obtain ⟨hte, hpar⟩ := T.mem_children_iff.mp ht
      have hst : T.Reaches s t := hpar ▸ T.reaches_parent (T.edges_subset_verts hte)
      exact T.reaches_trans hst htx

theorem mem_subtreeAt_iff_eq_or_exists_children {s x : ι} (hs : s ∈ T.verts) :
    x ∈ T.subtreeAt s ↔ x = s ∨ ∃ t ∈ T.children s, x ∈ T.subtreeAt t := by
  simp only [T.mem_subtreeAt, T.reaches_iff_eq_or_exists_children hs]

theorem disjoint_subtreeAt_of_mem_children {s t₁ t₂ : ι} (ht₁ : t₁ ∈ T.children s)
    (ht₂ : t₂ ∈ T.children s) (hne : t₁ ≠ t₂) :
    Disjoint (T.subtreeAt t₁) (T.subtreeAt t₂) := by
  rw [Finset.disjoint_left]
  intro x hx₁ hx₂
  obtain ⟨he₁, hp₁⟩ := T.mem_children_iff.mp ht₁
  obtain ⟨he₂, hp₂⟩ := T.mem_children_iff.mp ht₂
  rcases T.reaches_total_of_reaches (T.mem_subtreeAt.mp hx₁) (T.mem_subtreeAt.mp hx₂) with h₁₂ | h₂₁
  · have h := T.reaches_parent_of_reaches_of_ne h₁₂ hne
    rw [hp₂, ← hp₁] at h
    exact T.not_reaches_parent he₁ h
  · have h := T.reaches_parent_of_reaches_of_ne h₂₁ hne.symm
    rw [hp₁, ← hp₂] at h
    exact T.not_reaches_parent he₂ h

end RootedTree

open Hypergraph

/-- The march of `cross τ S r` is `π(τ(r))`. -/
@[simp]
theorem cross_roots (τ : ι → RootedHypergraph α β) (S : Finset ι) (r : ι) :
    (cross τ S r).roots = (τ r).roots := rfl

/-- The root set of `cross τ S r` is `πBar(τ(r))`. -/
@[simp]
theorem cross_rootSet (τ : ι → RootedHypergraph α β) (S : Finset ι) (r : ι) :
    (cross τ S r).rootSet = (τ r).rootSet := rfl

/-- When `r ∈ S`, `(cross τ S r)⁻` is the union of `τ(t)⁻` over `t ∈ S`. -/
theorem cross_toHypergraph_of_mem (τ : ι → RootedHypergraph α β) {S : Finset ι} {r : ι}
    (hr : r ∈ S) :
    (cross τ S r).toHypergraph = Hypergraph.biUnion S (fun t ↦ (τ t).toHypergraph) := by
  classical
  exact Hypergraph.biUnion_insert_of_mem hr _

/-- `(cross τ S r)⁻` depends only on the values of `τ(t)⁻` for `t ∈ S` when `r ∈ S`. -/
theorem cross_toHypergraph_congr {τ₁ τ₂ : ι → RootedHypergraph α β} {S : Finset ι} {r₁ r₂ : ι}
    (hr₁ : r₁ ∈ S) (hr₂ : r₂ ∈ S)
    (h : ∀ t ∈ S, (τ₁ t).toHypergraph = (τ₂ t).toHypergraph) :
    (cross τ₁ S r₁).toHypergraph = (cross τ₂ S r₂).toHypergraph := by
  rw [cross_toHypergraph_of_mem τ₁ hr₁, cross_toHypergraph_of_mem τ₂ hr₂]
  exact Hypergraph.biUnion_congr rfl h

/-- `cross τ S r` depends only on `τ(r).roots` and the values of `τ(t)⁻` for `t ∈ S` (when `r ∈ S`).
-/
theorem cross_congr {τ₁ τ₂ : ι → RootedHypergraph α β} {S : Finset ι} {r : ι} (hr : r ∈ S)
    (hH : ∀ t ∈ S, (τ₁ t).toHypergraph = (τ₂ t).toHypergraph)
    (hroots : (τ₁ r).roots = (τ₂ r).roots) :
    cross τ₁ S r = cross τ₂ S r :=
  RootedHypergraph.ext (cross_toHypergraph_congr hr hr hH) hroots

/-- The order of an edge `f` depends only on the underlying hypergraphs `τ(t)⁻` for `t ∈ V(T)`. -/
theorem edgeOrder_congr {T : RootedTree ι} {τ₁ τ₂ : ι → RootedHypergraph α β} {f : ι}
    (hf : f ∈ T.edges) (h : ∀ t ∈ T.verts, (τ₁ t).toHypergraph = (τ₂ t).toHypergraph) :
    edgeOrder T τ₁ f = edgeOrder T τ₂ f := by
  have hfv : f ∈ T.verts := T.edges_subset_verts hf
  have hf_mem : f ∈ T.subtreeAt f := T.self_mem_subtreeAt hfv
  have hr_mem : T.root ∈ T.rootSide f := T.root_mem_rootSide hf
  simp only [edgeOrder,
    cross_toHypergraph_congr hf_mem hf_mem (fun t ht ↦ h t (T.subtreeAt_subset_verts f ht)),
    cross_toHypergraph_congr hr_mem hr_mem (fun t ht ↦ h t (T.rootSide_subset_verts f ht))]

theorem cross_subtreeAt_root (T : RootedTree ι) (τ : ι → RootedHypergraph α β) :
    cross τ (T.subtreeAt T.root) T.root = cross τ T.verts T.root := by
  rw [T.subtreeAt_root]

@[simp]
theorem branching_self (T : RootedTree ι) (τ : ι → RootedHypergraph α β) (s : ι) :
    branching T τ s s = τ s := by
  classical
  simp [branching]

theorem branching_of_ne (T : RootedTree ι) (τ : ι → RootedHypergraph α β) {s t : ι} (h : t ≠ s) :
    branching T τ s t = cross τ (T.subtreeAt t) t := by
  classical
  simp [branching, h]

theorem branching_of_mem_children (T : RootedTree ι) (τ : ι → RootedHypergraph α β) {s t : ι}
    (ht : t ∈ T.children s) :
    branching T τ s t = cross τ (T.subtreeAt t) t :=
  branching_of_ne T τ (by rintro rfl; exact T.self_notMem_children t ht)

/-- If `(S, σ)` is the branching of `(T, τ)` at `s ∈ V(T)`, then `σ × S = τ × T^s`. -/
theorem cross_branching_eq (T : RootedTree ι) (τ : ι → RootedHypergraph α β) {s : ι}
    (hs : s ∈ T.verts) :
    cross (branching T τ s) (T.starAt s).verts (T.starAt s).root =
      cross τ (T.subtreeAt s) s := by
  have hs_star : (T.starAt s).root ∈ (T.starAt s).verts := (T.starAt s).root_mem
  have hs_sub : s ∈ T.subtreeAt s := T.self_mem_subtreeAt hs
  apply RootedHypergraph.ext
  · rw [cross_toHypergraph_of_mem _ hs_star, cross_toHypergraph_of_mem _ hs_sub]
    ext x
    · simp only [biUnion_vertexSet, Set.mem_iUnion, T.mem_starAt_verts,
        T.mem_subtreeAt_iff_eq_or_exists_children hs]
      refine ⟨?_, ?_⟩
      · rintro ⟨t, rfl | ht, hx⟩
        · rw [branching_self] at hx
          exact ⟨t, Or.inl rfl, hx⟩
        · rw [branching_of_mem_children T τ ht,
            cross_toHypergraph_of_mem _ (T.self_mem_subtreeAt (T.children_subset_verts s ht)),
            biUnion_vertexSet, Set.mem_iUnion₂] at hx
          obtain ⟨u, hu, hx⟩ := hx
          exact ⟨u, Or.inr ⟨t, ht, hu⟩, hx⟩
      · rintro ⟨u, rfl | ⟨t, ht, hu⟩, hx⟩
        · refine ⟨u, Or.inl rfl, ?_⟩
          rwa [branching_self]
        · refine ⟨t, Or.inr ht, ?_⟩
          rw [branching_of_mem_children T τ ht,
            cross_toHypergraph_of_mem _ (T.self_mem_subtreeAt (T.children_subset_verts s ht)),
            biUnion_vertexSet, Set.mem_iUnion₂]
          exact ⟨u, hu, hx⟩
    · simp only [biUnion_edgeSet, Set.mem_iUnion, T.mem_starAt_verts,
        T.mem_subtreeAt_iff_eq_or_exists_children hs]
      refine ⟨?_, ?_⟩
      · rintro ⟨t, rfl | ht, hx⟩
        · rw [branching_self] at hx
          exact ⟨t, Or.inl rfl, hx⟩
        · rw [branching_of_mem_children T τ ht,
            cross_toHypergraph_of_mem _ (T.self_mem_subtreeAt (T.children_subset_verts s ht)),
            biUnion_edgeSet, Set.mem_iUnion₂] at hx
          obtain ⟨u, hu, hx⟩ := hx
          exact ⟨u, Or.inr ⟨t, ht, hu⟩, hx⟩
      · rintro ⟨u, rfl | ⟨t, ht, hu⟩, hx⟩
        · refine ⟨u, Or.inl rfl, ?_⟩
          rwa [branching_self]
        · refine ⟨t, Or.inr ht, ?_⟩
          rw [branching_of_mem_children T τ ht,
            cross_toHypergraph_of_mem _ (T.self_mem_subtreeAt (T.children_subset_verts s ht)),
            biUnion_edgeSet, Set.mem_iUnion₂]
          exact ⟨u, hu, hx⟩
    · simp only [biUnion_inc, T.mem_starAt_verts,
        T.mem_subtreeAt_iff_eq_or_exists_children hs]
      refine ⟨?_, ?_⟩
      · rintro ⟨t, rfl | ht, hx⟩
        · rw [branching_self] at hx
          exact ⟨t, Or.inl rfl, hx⟩
        · rw [branching_of_mem_children T τ ht,
            cross_toHypergraph_of_mem _ (T.self_mem_subtreeAt (T.children_subset_verts s ht)),
            biUnion_inc] at hx
          obtain ⟨u, hu, hx⟩ := hx
          exact ⟨u, Or.inr ⟨t, ht, hu⟩, hx⟩
      · rintro ⟨u, rfl | ⟨t, ht, hu⟩, hx⟩
        · refine ⟨u, Or.inl rfl, ?_⟩
          rwa [branching_self]
        · refine ⟨t, Or.inr ht, ?_⟩
          rw [branching_of_mem_children T τ ht,
            cross_toHypergraph_of_mem _ (T.self_mem_subtreeAt (T.children_subset_verts s ht)),
            biUnion_inc]
          exact ⟨u, hu, hx⟩
  · simp [branching_self]

namespace IsTreeDecomposition

variable {G : RootedHypergraph α β} {T : RootedTree ι} {τ : ι → RootedHypergraph α β}

/-- If `(T, τ)` is a tree-decomposition of `G`, then `τ × T = G`. -/
theorem cross_verts_eq (h : IsTreeDecomposition G T τ) :
    cross τ T.verts T.root = G := by
  apply RootedHypergraph.ext
  · rw [cross_toHypergraph_of_mem τ T.root_mem, h.biUnion_eq]
  · exact h.roots_root

/-- For `t ∈ S ⊆ V(T)` with `r ∈ S`, `τ(t)⁻` is a subhypergraph of `(cross τ S r)⁻`. -/
theorem le_cross (h : IsTreeDecomposition G T τ) {S : Finset ι} {r t : ι}
    (hS : S ⊆ T.verts) (hr : r ∈ S) (ht : t ∈ S) :
    (τ t).toHypergraph ≤ (cross τ S r).toHypergraph := by
  rw [cross_toHypergraph_of_mem τ hr]
  exact Hypergraph.le_biUnion (fun i hi ↦ h.le i (hS hi)) ht

/-- For `S ⊆ V(T)` with `r ∈ S`, `(cross τ S r)⁻` is a subhypergraph of `G⁻`. -/
theorem cross_le (h : IsTreeDecomposition G T τ) {S : Finset ι} {r : ι}
    (hS : S ⊆ T.verts) (hr : r ∈ S) :
    (cross τ S r).toHypergraph ≤ G.toHypergraph := by
  rw [cross_toHypergraph_of_mem τ hr]
  exact Hypergraph.biUnion_le fun i hi ↦ h.le i (hS hi)

/-- Monotonicity of `(cross τ S r)⁻` in `S ⊆ V(T)`. -/
theorem cross_le_cross (h : IsTreeDecomposition G T τ) {S₁ S₂ : Finset ι} {r₁ r₂ : ι}
    (h₁₂ : S₁ ⊆ S₂) (h₂ : S₂ ⊆ T.verts) (hr₁ : r₁ ∈ S₁) (hr₂ : r₂ ∈ S₂) :
    (cross τ S₁ r₁).toHypergraph ≤ (cross τ S₂ r₂).toHypergraph := by
  rw [cross_toHypergraph_of_mem τ hr₁, cross_toHypergraph_of_mem τ hr₂]
  exact Hypergraph.biUnion_mono h₁₂ fun i hi ↦ h.le i (h₂ hi)

/-- For every edge `f ∈ E(T)`, `(τ × T^f)⁻ ∩ (τ × T_f)⁻ = τ(f)⁻ ∩ τ(parent f)⁻`. -/
theorem subtreeAt_inter_rootSide_eq (h : IsTreeDecomposition G T τ) {f : ι} (hf : f ∈ T.edges) :
    (cross τ (T.subtreeAt f) f).toHypergraph ∩ (cross τ (T.rootSide f) T.root).toHypergraph =
      (τ f).toHypergraph ∩ (τ (T.parent f)).toHypergraph := by
  have hfv : f ∈ T.verts := T.edges_subset_verts hf
  have hsub : T.subtreeAt f ⊆ T.verts := T.subtreeAt_subset_verts f
  have hroot : T.rootSide f ⊆ T.verts := T.rootSide_subset_verts f
  have hf_mem : f ∈ T.subtreeAt f := T.self_mem_subtreeAt hfv
  have hr_mem : T.root ∈ T.rootSide f := T.root_mem_rootSide hf
  have hp_mem : T.parent f ∈ T.rootSide f := T.parent_mem_rootSide hf
  have hle₁ : (τ f).toHypergraph ≤ (cross τ (T.subtreeAt f) f).toHypergraph :=
    h.le_cross hsub hf_mem hf_mem
  have hle₂ : (τ (T.parent f)).toHypergraph ≤ (cross τ (T.rootSide f) T.root).toHypergraph :=
    h.le_cross hroot hr_mem hp_mem
  have h_inter_le : (τ f).toHypergraph ∩ (τ (T.parent f)).toHypergraph ≤
      (cross τ (T.subtreeAt f) f).toHypergraph ∩ (cross τ (T.rootSide f) T.root).toHypergraph :=
    Hypergraph.le_inter
      ((Hypergraph.inter_le_left (h.le f hfv) (h.le _ (T.parent_mem f hfv))).trans hle₁)
      ((Hypergraph.inter_le_right (h.le f hfv) (h.le _ (T.parent_mem f hfv))).trans hle₂)
  refine (Hypergraph.eq_of_le_of_subset h_inter_le ?_ ?_).symm
  · rintro v ⟨hv₁, hv₂⟩
    rw [cross_toHypergraph_of_mem τ hf_mem, biUnion_vertexSet, Set.mem_iUnion₂] at hv₁
    rw [cross_toHypergraph_of_mem τ hr_mem, biUnion_vertexSet, Set.mem_iUnion₂] at hv₂
    obtain ⟨t₁, ht₁, hv₁⟩ := hv₁
    obtain ⟨t₃, ht₃, hv₃⟩ := hv₂
    have h_head := T.onPath_head_of_mem_subtreeAt_of_mem_rootSide ht₁ ht₃
    have h_par := T.onPath_parent_of_mem_subtreeAt_of_mem_rootSide hf ht₁ ht₃
    have hv : v ∈ ((τ t₁).toHypergraph ∩ (τ t₃).toHypergraph).vertexSet := ⟨hv₁, hv₃⟩
    exact ⟨(h.inter_le t₁ (hsub ht₁) f hfv t₃ (hroot ht₃) h_head).vertexSet_subset hv,
      (h.inter_le t₁ (hsub ht₁) (T.parent f) (T.parent_mem f hfv) t₃ (hroot ht₃)
        h_par).vertexSet_subset hv⟩
  · rintro e ⟨he₁, he₂⟩
    rw [cross_toHypergraph_of_mem τ hf_mem, biUnion_edgeSet, Set.mem_iUnion₂] at he₁
    rw [cross_toHypergraph_of_mem τ hr_mem, biUnion_edgeSet, Set.mem_iUnion₂] at he₂
    obtain ⟨t₁, ht₁, he₁⟩ := he₁
    obtain ⟨t₃, ht₃, he₃⟩ := he₂
    have hne : t₁ ≠ t₃ := by
      rintro rfl
      exact Finset.disjoint_left.mp (T.disjoint_subtreeAt_rootSide f) ht₁ ht₃
    have h_empty := h.edgeSet_inter_eq t₁ (hsub ht₁) t₃ (hroot ht₃) hne
    have he : e ∈ ((τ t₁).toHypergraph ∩ (τ t₃).toHypergraph).edgeSet := ⟨he₁, he₃⟩
    rw [h_empty] at he
    exact False.elim he

/-- Graph Minors IV, (3.1): if `(T, τ)` is a tree-decomposition of a rooted hypergraph `G` and
`f ∈ E(T)`, then `(τ × T^f, τ × T_f)` is a separation of `G`. -/
theorem isSeparation_edge {ι : Type*} {G : RootedHypergraph α β}
    {T : RootedTree ι} {τ : ι → RootedHypergraph α β} (h : IsTreeDecomposition G T τ)
    {f : ι} (hf : f ∈ T.edges) :
    G.IsSeparation (cross τ (T.subtreeAt f) f) (cross τ (T.rootSide f) T.root) := by
  classical
  have hfv : f ∈ T.verts := T.edges_subset_verts hf
  have hf_mem : f ∈ T.subtreeAt f := T.self_mem_subtreeAt hfv
  have hr_mem : T.root ∈ T.rootSide f := T.root_mem_rootSide hf
  refine ⟨?_, h.roots_root, ?_⟩
  · refine ⟨h.cross_le (T.subtreeAt_subset_verts f) hf_mem,
      h.cross_le (T.rootSide_subset_verts f) hr_mem, ?_, ?_⟩
    · rw [cross_toHypergraph_of_mem τ hf_mem, cross_toHypergraph_of_mem τ hr_mem,
        ← Hypergraph.biUnion_union, T.subtreeAt_union_rootSide f, h.biUnion_eq]
    · rw [h.subtreeAt_inter_rootSide_eq hf]
      exact h.edgeSet_inter_eq f hfv (T.parent f) (T.parent_mem f hfv) (T.parent_ne_self hf).symm
  · rw [cross_rootSet, h.subtreeAt_inter_rootSide_eq hf, h.rootSet_edge f hf]

/-- The order of an edge `f` in a tree-decomposition `(T, τ)` equals
`|V(τ(f)⁻ ∩ τ(parent f)⁻)|`. -/
theorem edgeOrder_eq_ncard_inter (h : IsTreeDecomposition G T τ) {f : ι} (hf : f ∈ T.edges) :
    edgeOrder T τ f = ((τ f).toHypergraph ∩ (τ (T.parent f)).toHypergraph).vertexSet.ncard := by
  simp only [edgeOrder, separationOrder, h.subtreeAt_inter_rootSide_eq hf]

/-- The order of an edge `f` in a tree-decomposition `(T, τ)` equals
`|V(τ(f)) ∩ V(τ(parent f))|`. -/
theorem edgeOrder_eq_ncard_vertexSet_inter (h : IsTreeDecomposition G T τ) {f : ι}
    (hf : f ∈ T.edges) :
    edgeOrder T τ f = ((τ f).vertexSet ∩ (τ (T.parent f)).vertexSet).ncard :=
  h.edgeOrder_eq_ncard_inter hf

/-- The order of an edge `f` in a tree-decomposition `(T, τ)` equals `|πBar(τ(f))|`. -/
theorem edgeOrder_eq_ncard_rootSet (h : IsTreeDecomposition G T τ) {f : ι} (hf : f ∈ T.edges) :
    edgeOrder T τ f = (τ f).rootSet.ncard := by
  rw [h.edgeOrder_eq_ncard_inter hf, h.rootSet_edge f hf]

/-- The order of an edge `f` in a tree-decomposition `(T, τ)` equals the length of `π(τ(f))`. -/
theorem edgeOrder_eq_length_roots (h : IsTreeDecomposition G T τ) {f : ι} (hf : f ∈ T.edges) :
    edgeOrder T τ f = (τ f).roots.length := by
  rw [h.edgeOrder_eq_ncard_rootSet hf, RootedHypergraph.ncard_rootSet]

/-- For every edge `f ∈ E(T)`, `(τ × T^f)⁻ ∩ τ(parent f)⁻ = τ(f)⁻ ∩ τ(parent f)⁻`. -/
theorem subtreeAt_inter_parent_eq (h : IsTreeDecomposition G T τ) {f : ι} (hf : f ∈ T.edges) :
    (cross τ (T.subtreeAt f) f).toHypergraph ∩ (τ (T.parent f)).toHypergraph =
      (τ f).toHypergraph ∩ (τ (T.parent f)).toHypergraph := by
  have hfv : f ∈ T.verts := T.edges_subset_verts hf
  have hsub : T.subtreeAt f ⊆ T.verts := T.subtreeAt_subset_verts f
  have hf_mem : f ∈ T.subtreeAt f := T.self_mem_subtreeAt hfv
  have hp_mem : T.parent f ∈ T.rootSide f := T.parent_mem_rootSide hf
  have hpv : T.parent f ∈ T.verts := T.parent_mem f hfv
  have hle₁ : (τ f).toHypergraph ≤ (cross τ (T.subtreeAt f) f).toHypergraph :=
    h.le_cross hsub hf_mem hf_mem
  have h_inter_le : (τ f).toHypergraph ∩ (τ (T.parent f)).toHypergraph ≤
      (cross τ (T.subtreeAt f) f).toHypergraph ∩ (τ (T.parent f)).toHypergraph :=
    Hypergraph.le_inter
      ((Hypergraph.inter_le_left (h.le f hfv) (h.le _ hpv)).trans hle₁)
      (Hypergraph.inter_le_right (h.le f hfv) (h.le _ hpv))
  refine (Hypergraph.eq_of_le_of_subset h_inter_le ?_ ?_).symm
  · rintro v ⟨hv₁, hv₂⟩
    rw [cross_toHypergraph_of_mem τ hf_mem, biUnion_vertexSet, Set.mem_iUnion₂] at hv₁
    obtain ⟨t₁, ht₁, hv₁⟩ := hv₁
    have h_head := T.onPath_head_of_mem_subtreeAt_of_mem_rootSide ht₁ hp_mem
    have hv : v ∈ ((τ t₁).toHypergraph ∩ (τ (T.parent f)).toHypergraph).vertexSet := ⟨hv₁, hv₂⟩
    exact ⟨(h.inter_le t₁ (hsub ht₁) f hfv (T.parent f) hpv h_head).vertexSet_subset hv, hv₂⟩
  · rintro e ⟨he₁, he₂⟩
    rw [cross_toHypergraph_of_mem τ hf_mem, biUnion_edgeSet, Set.mem_iUnion₂] at he₁
    obtain ⟨t₁, ht₁, he₁⟩ := he₁
    have hne : t₁ ≠ T.parent f := by
      rintro rfl
      exact Finset.disjoint_left.mp (T.disjoint_subtreeAt_rootSide f) ht₁ hp_mem
    have h_empty := h.edgeSet_inter_eq t₁ (hsub ht₁) (T.parent f) hpv hne
    have he : e ∈ ((τ t₁).toHypergraph ∩ (τ (T.parent f)).toHypergraph).edgeSet := ⟨he₁, he₂⟩
    rw [h_empty] at he
    exact False.elim he

theorem branching_le (h : IsTreeDecomposition G T τ) {s t : ι} (hs : s ∈ T.verts)
    (ht : t ∈ (T.starAt s).verts) :
    (branching T τ s t).toHypergraph ≤ G.toHypergraph := by
  rcases T.mem_starAt_verts.mp ht with rfl | ht_child
  · rw [branching_self]
    exact h.le t hs
  · rw [branching_of_mem_children T τ ht_child]
    have htv : t ∈ T.verts := T.children_subset_verts s ht_child
    exact h.cross_le (T.subtreeAt_subset_verts t) (T.self_mem_subtreeAt htv)

/-- For every `s ∈ V(T)`, the branching of `(T, τ)` at `s` is a star-decomposition of
`τ × T^s`. -/
theorem isStarDecomposition_branching (h : IsTreeDecomposition G T τ) {s : ι} (hs : s ∈ T.verts) :
    IsStarDecomposition (T.starAt s) (branching T τ s) := by
  refine ⟨T.isStar_starAt s, ?_⟩
  have hr_mem : (T.starAt s).root ∈ (T.starAt s).verts := (T.starAt s).root_mem
  refine ⟨?_, (cross_toHypergraph_of_mem _ hr_mem).symm, ?_, ?_, rfl, ?_⟩
  · intro t ht
    rw [cross_toHypergraph_of_mem _ hr_mem]
    exact Hypergraph.le_biUnion (fun i hi ↦ h.branching_le hs hi) ht
  · intro t₁ ht₁ t₂ ht₂ hne
    ext e
    simp only [inter_edgeSet, Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
    intro he₁ he₂
    have mem_verts_of_branching : ∀ {t}, t ∈ (T.starAt s).verts →
        e ∈ (branching T τ s t).edgeSet →
        ∃ u ∈ T.verts, (t = s ∧ u = s ∨ t ∈ T.children s ∧ u ∈ T.subtreeAt t) ∧
          e ∈ (τ u).edgeSet := by
      intro t ht he
      rcases T.mem_starAt_verts.mp ht with rfl | ht_child
      · rw [branching_self] at he
        exact ⟨t, hs, Or.inl ⟨rfl, rfl⟩, he⟩
      · have htv : t ∈ T.verts := T.children_subset_verts s ht_child
        rw [branching_of_mem_children T τ ht_child,
          cross_toHypergraph_of_mem _ (T.self_mem_subtreeAt htv),
          biUnion_edgeSet, Set.mem_iUnion₂] at he
        obtain ⟨u, hu, he⟩ := he
        exact ⟨u, T.subtreeAt_subset_verts t hu, Or.inr ⟨ht_child, hu⟩, he⟩
    obtain ⟨u₁, hu₁v, hcase₁, heu₁⟩ := mem_verts_of_branching ht₁ he₁
    obtain ⟨u₂, hu₂v, hcase₂, heu₂⟩ := mem_verts_of_branching ht₂ he₂
    have hu_ne : u₁ ≠ u₂ := by
      rintro rfl
      rcases hcase₁ with ⟨rfl, rfl⟩ | ⟨ht₁c, hu₁⟩ <;>
        rcases hcase₂ with ⟨rfl, h₂⟩ | ⟨ht₂c, hu₂⟩
      · exact hne rfl
      · obtain ⟨ht₂e, hp₂⟩ := T.mem_children_iff.mp ht₂c
        exact T.not_reaches_parent ht₂e (hp₂ ▸ T.mem_subtreeAt.mp hu₂)
      · obtain ⟨ht₁e, hp₁⟩ := T.mem_children_iff.mp ht₁c
        exact T.not_reaches_parent ht₁e (hp₁ ▸ h₂ ▸ T.mem_subtreeAt.mp hu₁)
      · by_cases ht₁₂ : t₁ = t₂
        · exact hne ht₁₂
        · exact Finset.disjoint_left.mp
            (T.disjoint_subtreeAt_of_mem_children ht₁c ht₂c ht₁₂) hu₁ hu₂
    have h_empty := h.edgeSet_inter_eq u₁ hu₁v u₂ hu₂v hu_ne
    have he : e ∈ ((τ u₁).toHypergraph ∩ (τ u₂).toHypergraph).edgeSet := ⟨heu₁, heu₂⟩
    rw [h_empty] at he
    exact False.elim he
  · intro t₁ ht₁ t₂ ht₂ t₃ ht₃ hon
    have hle₁ := h.branching_le hs ht₁
    have hle₃ := h.branching_le hs ht₃
    by_cases h₂₁ : t₂ = t₁
    · subst h₂₁
      exact Hypergraph.inter_le_left hle₁ hle₃
    · by_cases h₂₃ : t₂ = t₃
      · subst h₂₃
        exact Hypergraph.inter_le_right hle₁ hle₃
      · have ht₂s : t₂ = s := by
          rcases hon.1 with h₁ | h₃
          · exact (T.reaches_starAt h₁).resolve_left h₂₁
          · exact (T.reaches_starAt h₃).resolve_left h₂₃
        subst ht₂s
        have ht₁c : t₁ ∈ T.children t₂ := by
          rcases T.mem_starAt_verts.mp ht₁ with rfl | h1
          · exact absurd rfl h₂₁
          · exact h1
        have ht₃c : t₃ ∈ T.children t₂ := by
          rcases T.mem_starAt_verts.mp ht₃ with rfl | h3
          · exact absurd rfl h₂₃
          · exact h3
        have ht₁₃ : t₁ ≠ t₃ := by
          rintro rfl
          have hr : (T.starAt t₂).Reaches t₁ t₂ :=
            hon.2 t₁ ((T.starAt t₂).reaches_refl ht₁) ((T.starAt t₂).reaches_refl ht₁)
          rcases T.reaches_starAt hr with h | h <;> exact h₂₁ h.symm
        rw [branching_self, branching_of_mem_children T τ ht₁c, branching_of_mem_children T τ ht₃c]
        have ht₁v : t₁ ∈ T.verts := T.children_subset_verts t₂ ht₁c
        have ht₃v : t₃ ∈ T.verts := T.children_subset_verts t₂ ht₃c
        have ht₁_sub : t₁ ∈ T.subtreeAt t₁ := T.self_mem_subtreeAt ht₁v
        have ht₃_sub : t₃ ∈ T.subtreeAt t₃ := T.self_mem_subtreeAt ht₃v
        have h_empty : ((cross τ (T.subtreeAt t₁) t₁).toHypergraph ∩
            (cross τ (T.subtreeAt t₃) t₃).toHypergraph).edgeSet = ∅ := by
          ext e
          simp only [inter_edgeSet, Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
          rw [cross_toHypergraph_of_mem τ ht₁_sub, cross_toHypergraph_of_mem τ ht₃_sub,
            biUnion_edgeSet, biUnion_edgeSet, Set.mem_iUnion₂, Set.mem_iUnion₂]
          rintro ⟨u₁, hu₁, he₁⟩ ⟨u₃, hu₃, he₃⟩
          have hu_ne : u₁ ≠ u₃ := by
            rintro rfl
            exact Finset.disjoint_left.mp
              (T.disjoint_subtreeAt_of_mem_children ht₁c ht₃c ht₁₃) hu₁ hu₃
          have he : e ∈ ((τ u₁).toHypergraph ∩ (τ u₃).toHypergraph).edgeSet := ⟨he₁, he₃⟩
          rw [h.edgeSet_inter_eq u₁ (T.subtreeAt_subset_verts t₁ hu₁) u₃
            (T.subtreeAt_subset_verts t₃ hu₃) hu_ne] at he
          exact False.elim he
        refine ⟨?_, ?_, ?_⟩
        · rintro v ⟨hv₁, hv₃⟩
          rw [cross_toHypergraph_of_mem τ ht₁_sub, biUnion_vertexSet, Set.mem_iUnion₂] at hv₁
          rw [cross_toHypergraph_of_mem τ ht₃_sub, biUnion_vertexSet, Set.mem_iUnion₂] at hv₃
          obtain ⟨u₁, hu₁, hv₁⟩ := hv₁
          obtain ⟨u₃, hu₃, hv₃⟩ := hv₃
          have hu₃_root : u₃ ∈ T.rootSide t₁ := by
            refine T.mem_rootSide.mpr ⟨T.subtreeAt_subset_verts t₃ hu₃, fun h₁ ↦ ?_⟩
            exact Finset.disjoint_left.mp (T.disjoint_subtreeAt_of_mem_children ht₁c ht₃c ht₁₃)
              (T.mem_subtreeAt.mpr h₁) hu₃
          obtain ⟨ht₁e, hp₁⟩ := T.mem_children_iff.mp ht₁c
          have hon_p := T.onPath_parent_of_mem_subtreeAt_of_mem_rootSide ht₁e hu₁ hu₃_root
          rw [hp₁] at hon_p
          have hv : v ∈ ((τ u₁).toHypergraph ∩ (τ u₃).toHypergraph).vertexSet := ⟨hv₁, hv₃⟩
          exact (h.inter_le u₁ (T.subtreeAt_subset_verts t₁ hu₁) t₂ hs u₃
            (T.subtreeAt_subset_verts t₃ hu₃) hon_p).vertexSet_subset hv
        · rw [h_empty]
          exact Set.empty_subset _
        · intro e he
          rw [h_empty] at he
          exact False.elim he
  · intro f hf
    rw [T.starAt_edges] at hf
    obtain ⟨hfe, hfp⟩ := T.mem_children_iff.mp hf
    rw [branching_of_mem_children T τ hf, T.starAt_parent, branching_self, ← hfp]
    rw [cross_rootSet, h.subtreeAt_inter_parent_eq hfe, h.rootSet_edge f hfe]

end IsTreeDecomposition

end GM04

end GraphMinor
