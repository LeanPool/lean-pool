/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM10.Defs

/-!
# Tangle Lemmas (Graph Minors X, Section 2)

This file formalizes Section 2 of Graph Minors X (pages 155–158):
- Basic properties of subhypergraphs, separations, vertex/edge deletion, and extreme separations.
- `IsTangle.order_le_ncard_vertexSet` and `IsTangle.truncation` (Section 1, pages 154–155).
- `theorem_2_1` (Graph Minors X, (2.1), page 155).
- `theorem_2_2` (Graph Minors X, (2.2), page 155).
- `theorem_2_3` (Graph Minors X, (2.3), page 155).
- `theorem_2_4` (Graph Minors X, (2.4), page 156).
- `theorem_2_5` (Graph Minors X, (2.5), page 156).
- `theorem_2_7` (Graph Minors X, (2.7), page 157).
- `theorem_2_8` (Graph Minors X, (2.8), page 157).
- `theorem_2_9` (Graph Minors X, (2.9), page 158).
-/

public section

namespace GraphMinor.GM10

open Hypergraph

variable {α β : Type*}

/-! ## Basic lemmas on hypergraphs and separations -/

@[simp]
theorem bot_vertexSet : (⊥ : Hypergraph α β).vertexSet = ∅ := rfl

@[simp]
theorem bot_edgeSet : (⊥ : Hypergraph α β).edgeSet = ∅ := rfl

@[simp]
theorem bot_inc (e : β) (v : α) : ¬ (⊥ : Hypergraph α β).Inc e v := id

theorem isNonNull_iff_ne_bot (G : Hypergraph α β) : IsNonNull G ↔ G ≠ ⊥ := by
  unfold IsNonNull
  constructor
  · rintro (⟨v, hv⟩ | ⟨e, he⟩) rfl
    · exact hv
    · exact he
  · intro h
    by_contra! hc
    apply h
    refine Hypergraph.ext hc.1 hc.2 ?_
    funext e v
    simp only [bot_inc, eq_iff_iff, iff_false]
    intro hinc
    have he : e ∈ (∅ : Set β) := hc.2 ▸ G.edge_mem_of_inc hinc
    exact he

theorem union_vertexSet (G₁ G₂ : Hypergraph α β) :
    (G₁ ∪ G₂).vertexSet = G₁.vertexSet ∪ G₂.vertexSet :=
  GraphMinor.Hypergraph.union_vertexSet_eq G₁ G₂

theorem union_edgeSet (G₁ G₂ : Hypergraph α β) :
    (G₁ ∪ G₂).edgeSet = G₁.edgeSet ∪ G₂.edgeSet :=
  GraphMinor.Hypergraph.union_edgeSet_eq G₁ G₂

theorem union_inc (G₁ G₂ : Hypergraph α β) (e : β) (v : α) :
    (G₁ ∪ G₂).Inc e v ↔ G₁.Inc e v ∨ G₂.Inc e v :=
  GraphMinor.Hypergraph.union_inc_iff G₁ G₂ e v

theorem inter_vertexSet (G₁ G₂ : Hypergraph α β) :
    (G₁ ∩ G₂).vertexSet = G₁.vertexSet ∩ G₂.vertexSet :=
  GraphMinor.Hypergraph.inter_vertexSet_eq G₁ G₂

theorem inter_edgeSet (G₁ G₂ : Hypergraph α β) :
    (G₁ ∩ G₂).edgeSet = G₁.edgeSet ∩ G₂.edgeSet :=
  GraphMinor.Hypergraph.inter_edgeSet_eq G₁ G₂

theorem inter_inc (G₁ G₂ : Hypergraph α β) (e : β) (v : α) :
    (G₁ ∩ G₂).Inc e v ↔ G₁.Inc e v ∧ G₂.Inc e v :=
  GraphMinor.Hypergraph.inter_inc_iff G₁ G₂ e v

attribute [simp] GraphMinor.Hypergraph.union_vertexSet_eq
  GraphMinor.Hypergraph.union_edgeSet_eq GraphMinor.Hypergraph.inter_vertexSet_eq
  GraphMinor.Hypergraph.inter_edgeSet_eq

theorem union_comm (G₁ G₂ : Hypergraph α β) : G₁ ∪ G₂ = G₂ ∪ G₁ := by
  ext <;> simp [union_inc, Set.union_comm, or_comm]

theorem union_assoc (G₁ G₂ G₃ : Hypergraph α β) : G₁ ∪ G₂ ∪ G₃ = G₁ ∪ (G₂ ∪ G₃) := by
  ext <;> simp [union_inc, Set.union_assoc, or_assoc]

theorem union_self (G : Hypergraph α β) : G ∪ G = G := by
  ext <;> simp [union_inc]

theorem inter_comm (G₁ G₂ : Hypergraph α β) : G₁ ∩ G₂ = G₂ ∩ G₁ := by
  ext <;> simp [inter_inc, Set.inter_comm, and_comm]

theorem inter_assoc (G₁ G₂ G₃ : Hypergraph α β) : G₁ ∩ G₂ ∩ G₃ = G₁ ∩ (G₂ ∩ G₃) := by
  ext <;> simp [inter_inc, Set.inter_assoc, and_assoc]

theorem inter_self (G : Hypergraph α β) : G ∩ G = G := by
  ext <;> simp [inter_inc]

theorem inc_iff_of_le {H G : Hypergraph α β} (h : H ≤ G) {e : β} {v : α} (he : e ∈ H.edgeSet) :
    H.Inc e v ↔ G.Inc e v := by
  have := Set.ext_iff.1 (h.ends_eq e he) v
  exact this.symm

theorem inc_of_le {H G : Hypergraph α β} (h : H ≤ G) {e : β} {v : α} (hinc : H.Inc e v) :
    G.Inc e v :=
  (inc_iff_of_le h (H.edge_mem_of_inc hinc)).1 hinc

theorem eq_of_le_of_vertexSet_eq_of_edgeSet_eq {H₁ H₂ G : Hypergraph α β}
    (h₁ : H₁ ≤ G) (h₂ : H₂ ≤ G) (hV : H₁.vertexSet = H₂.vertexSet)
    (hE : H₁.edgeSet = H₂.edgeSet) : H₁ = H₂ := by
  refine Hypergraph.ext hV hE ?_
  funext e v
  apply propext
  by_cases he : e ∈ H₁.edgeSet
  · rw [inc_iff_of_le h₁ he, inc_iff_of_le h₂ (hE ▸ he)]
  · constructor <;> intro h
    · exact (he (H₁.edge_mem_of_inc h)).elim
    · exact (he (hE.symm ▸ H₂.edge_mem_of_inc h)).elim

theorem le_iff_of_le {H₁ H₂ G : Hypergraph α β} (h₁ : H₁ ≤ G) (h₂ : H₂ ≤ G) :
    H₁ ≤ H₂ ↔ H₁.vertexSet ⊆ H₂.vertexSet ∧ H₁.edgeSet ⊆ H₂.edgeSet := by
  refine ⟨fun h ↦ ⟨h.vertexSet_subset, h.edgeSet_subset⟩, fun ⟨hV, hE⟩ ↦ ⟨hV, hE, fun e he ↦ ?_⟩⟩
  rw [← h₂.ends_eq e (hE he), ← h₁.ends_eq e he]

theorem union_le {H₁ H₂ G : Hypergraph α β} (h₁ : H₁ ≤ G) (h₂ : H₂ ≤ G) : H₁ ∪ H₂ ≤ G where
  vertexSet_subset := Set.union_subset h₁.vertexSet_subset h₂.vertexSet_subset
  edgeSet_subset := Set.union_subset h₁.edgeSet_subset h₂.edgeSet_subset
  ends_eq e he := by
    ext v
    simp only [ends, Set.mem_ofPred_eq, union_inc]
    rcases he with he₁ | he₂
    · exact ⟨fun h ↦ Or.inl ((inc_iff_of_le h₁ he₁).2 h),
        fun h ↦ h.elim (inc_of_le h₁) (inc_of_le h₂)⟩
    · exact ⟨fun h ↦ Or.inr ((inc_iff_of_le h₂ he₂).2 h),
        fun h ↦ h.elim (inc_of_le h₁) (inc_of_le h₂)⟩

theorem le_union_left {H₁ H₂ G : Hypergraph α β} (h₁ : H₁ ≤ G) (h₂ : H₂ ≤ G) :
    H₁ ≤ H₁ ∪ H₂ :=
  (le_iff_of_le h₁ (union_le h₁ h₂)).2 ⟨Set.subset_union_left, Set.subset_union_left⟩

theorem le_union_right {H₁ H₂ G : Hypergraph α β} (h₁ : H₁ ≤ G) (h₂ : H₂ ≤ G) :
    H₂ ≤ H₁ ∪ H₂ :=
  (le_iff_of_le h₂ (union_le h₁ h₂)).2 ⟨Set.subset_union_right, Set.subset_union_right⟩

theorem inter_le {H₁ H₂ G : Hypergraph α β} (h₁ : H₁ ≤ G) (h₂ : H₂ ≤ G) : H₁ ∩ H₂ ≤ G where
  vertexSet_subset := Set.inter_subset_left.trans h₁.vertexSet_subset
  edgeSet_subset := Set.inter_subset_left.trans h₁.edgeSet_subset
  ends_eq e he := by
    ext v
    simp only [ends, Set.mem_ofPred_eq, inter_inc]
    rw [inc_iff_of_le h₁ he.1, inc_iff_of_le h₂ he.2, and_self]

theorem inter_le_left {H₁ H₂ G : Hypergraph α β} (h₁ : H₁ ≤ G) (h₂ : H₂ ≤ G) :
    H₁ ∩ H₂ ≤ H₁ :=
  (le_iff_of_le (inter_le h₁ h₂) h₁).2 ⟨Set.inter_subset_left, Set.inter_subset_left⟩

theorem inter_le_right {H₁ H₂ G : Hypergraph α β} (h₁ : H₁ ≤ G) (h₂ : H₂ ≤ G) :
    H₁ ∩ H₂ ≤ H₂ :=
  (le_iff_of_le (inter_le h₁ h₂) h₂).2 ⟨Set.inter_subset_right, Set.inter_subset_right⟩

theorem eq_of_le_of_ncard_eq {H₁ H₂ : Hypergraph α β} (h : H₁ ≤ H₂)
    (hV : H₂.vertexSet.ncard ≤ H₁.vertexSet.ncard)
    (hE : H₂.edgeSet.ncard ≤ H₁.edgeSet.ncard) : H₁ = H₂ := by
  have hV_eq : H₁.vertexSet = H₂.vertexSet :=
    Set.eq_of_subset_of_ncard_le h.vertexSet_subset hV H₂.vertexSet_finite
  have hE_eq : H₁.edgeSet = H₂.edgeSet :=
    Set.eq_of_subset_of_ncard_le h.edgeSet_subset hE H₂.edgeSet_finite
  exact eq_of_le_of_vertexSet_eq_of_edgeSet_eq h le_rfl hV_eq hE_eq

theorem _root_.GraphMinor.Hypergraph.IsSeparation.symm {G A B : Hypergraph α β}
    (h : G.IsSeparation A B) : G.IsSeparation B A where
  left_le := h.right_le
  right_le := h.left_le
  union_eq := (union_comm B A).trans h.union_eq
  edgeSet_inter_eq := by rw [inter_comm, h.edgeSet_inter_eq]

theorem separationOrder_comm (A B : Hypergraph α β) :
    separationOrder A B = separationOrder B A :=
  congrArg (fun G : Hypergraph α β ↦ G.vertexSet.ncard) (inter_comm A B)

theorem _root_.GraphMinor.Hypergraph.IsSeparation.vertexSet_union {G A B : Hypergraph α β}
    (h : G.IsSeparation A B) : A.vertexSet ∪ B.vertexSet = G.vertexSet :=
  congrArg Hypergraph.vertexSet h.union_eq

theorem _root_.GraphMinor.Hypergraph.IsSeparation.edgeSet_union {G A B : Hypergraph α β}
    (h : G.IsSeparation A B) : A.edgeSet ∪ B.edgeSet = G.edgeSet :=
  congrArg Hypergraph.edgeSet h.union_eq

theorem _root_.GraphMinor.Hypergraph.IsSeparation.disjoint_edgeSet {G A B : Hypergraph α β}
    (h : G.IsSeparation A B) : Disjoint A.edgeSet B.edgeSet :=
  Set.disjoint_iff_inter_eq_empty.2 h.edgeSet_inter_eq

theorem _root_.GraphMinor.Hypergraph.IsSeparation.notMem_edgeSet_left {G A B : Hypergraph α β}
    (h : G.IsSeparation A B) {e : β} (he : e ∈ B.edgeSet) : e ∉ A.edgeSet :=
  Set.disjoint_right.1 h.disjoint_edgeSet he

theorem _root_.GraphMinor.Hypergraph.IsSeparation.notMem_edgeSet_right {G A B : Hypergraph α β}
    (h : G.IsSeparation A B) {e : β} (he : e ∈ A.edgeSet) : e ∉ B.edgeSet :=
  Set.disjoint_left.1 h.disjoint_edgeSet he

theorem isSeparation_iff_of_le {G A B : Hypergraph α β} (hA : A ≤ G) (hB : B ≤ G) :
    G.IsSeparation A B ↔
      A.vertexSet ∪ B.vertexSet = G.vertexSet ∧
      A.edgeSet ∪ B.edgeSet = G.edgeSet ∧
      A.edgeSet ∩ B.edgeSet = ∅ := by
  refine ⟨fun h ↦ ⟨h.vertexSet_union, h.edgeSet_union, h.edgeSet_inter_eq⟩,
    fun ⟨hV, hE, hI⟩ ↦ ⟨hA, hB, ?_, hI⟩⟩
  exact eq_of_le_of_vertexSet_eq_of_edgeSet_eq (union_le hA hB) le_rfl hV hE

theorem _root_.GraphMinor.Hypergraph.IsSeparation.union_inter {G A B A' B' : Hypergraph α β}
    (h : G.IsSeparation A B) (h' : G.IsSeparation A' B') :
    G.IsSeparation (A ∪ A') (B ∩ B') := by
  have h1 : A ∪ A' ≤ G := union_le h.left_le h'.left_le
  have h2 : B ∩ B' ≤ G := inter_le h.right_le h'.right_le
  rw [isSeparation_iff_of_le h1 h2]
  refine ⟨?_, ?_, ?_⟩
  · ext v
    simp only [union_vertexSet, inter_vertexSet, Set.mem_union, Set.mem_inter_iff]
    constructor
    · rintro ((hv | hv) | ⟨hv, _⟩)
      · exact h.left_le.vertexSet_subset hv
      · exact h'.left_le.vertexSet_subset hv
      · exact h.right_le.vertexSet_subset hv
    · intro hv
      have hv1 : v ∈ A.vertexSet ∪ B.vertexSet := by rwa [h.vertexSet_union]
      have hv2 : v ∈ A'.vertexSet ∪ B'.vertexSet := by rwa [h'.vertexSet_union]
      rcases hv1 with hvA | hvB <;> rcases hv2 with hvA' | hvB' <;> tauto
  · ext e
    simp only [union_edgeSet, inter_edgeSet, Set.mem_union, Set.mem_inter_iff]
    constructor
    · rintro ((he | he) | ⟨he, _⟩)
      · exact h.left_le.edgeSet_subset he
      · exact h'.left_le.edgeSet_subset he
      · exact h.right_le.edgeSet_subset he
    · intro he
      have he1 : e ∈ A.edgeSet ∪ B.edgeSet := by rwa [h.edgeSet_union]
      have he2 : e ∈ A'.edgeSet ∪ B'.edgeSet := by rwa [h'.edgeSet_union]
      rcases he1 with heA | heB <;> rcases he2 with heA' | heB' <;> tauto
  · ext e
    change e ∈ (A.edgeSet ∪ A'.edgeSet) ∩ (B.edgeSet ∩ B'.edgeSet) ↔ e ∈ (∅ : Set β)
    simp only [Set.mem_inter_iff, Set.mem_union, Set.mem_empty_iff_false, iff_false]
    rintro ⟨he | he, heB, heB'⟩
    · exact h.notMem_edgeSet_right he heB
    · exact h'.notMem_edgeSet_right he heB'

theorem deleteEdges_le (G : Hypergraph α β) (F : Set β) : G.deleteEdges F ≤ G where
  vertexSet_subset := subset_rfl
  edgeSet_subset := Set.sdiff_subset
  ends_eq e he := by
    ext v
    simp [ends, deleteEdges, he.2]

theorem deleteVertices_le (G : Hypergraph α β) (X : Set α) : G.deleteVertices X ≤ G where
  vertexSet_subset := Set.sdiff_subset
  edgeSet_subset _ h := h.1
  ends_eq e he := by
    ext v
    exact ⟨fun h ↦ ⟨h, he.2⟩, fun h ↦ h.1⟩

theorem edgeHypergraph_le {G : Hypergraph α β} {e : β} (he : e ∈ G.edgeSet) :
    edgeHypergraph G e ≤ G where
  vertexSet_subset _ h := G.vertex_mem_of_inc h
  edgeSet_subset := Set.singleton_subset_iff.2 he
  ends_eq e' he' := by
    rcases Set.mem_singleton_iff.1 he' with rfl
    ext v
    simp [ends, edgeHypergraph]

theorem vertexHypergraph_le {G : Hypergraph α β} {v : α} (hv : v ∈ G.vertexSet) :
    (vertexHypergraph v : Hypergraph α β) ≤ G where
  vertexSet_subset := Set.singleton_subset_iff.2 hv
  edgeSet_subset := Set.empty_subset _
  ends_eq _ h := h.elim

theorem isSeparation_edgeHypergraph_deleteEdges {G : Hypergraph α β} {e : β}
    (he : e ∈ G.edgeSet) :
    G.IsSeparation (edgeHypergraph G e) (G.deleteEdges {e}) := by
  rw [isSeparation_iff_of_le (edgeHypergraph_le he) (deleteEdges_le G {e})]
  refine ⟨?_, ?_, ?_⟩
  · exact Set.union_eq_right.2 fun _ hv ↦ G.vertex_mem_of_inc hv
  · simpa [edgeHypergraph, deleteEdges] using Set.insert_sdiff_self_of_mem he
  · simp [edgeHypergraph, deleteEdges]

theorem separationOrder_edgeHypergraph_deleteEdges (G : Hypergraph α β) (e : β) :
    separationOrder (edgeHypergraph G e) (G.deleteEdges {e}) = edgeSize G e := by
  have : G.ends e ⊆ G.vertexSet := fun _ h ↦ G.vertex_mem_of_inc h
  simp [separationOrder, edgeHypergraph, deleteEdges, edgeSize, Set.inter_eq_left.2 this]

theorem isSeparation_vertexHypergraph_deleteVertices {G : Hypergraph α β} {v : α}
    (hv : v ∈ G.vertexSet) (hiso : ∀ e, ¬ G.Inc e v) :
    G.IsSeparation (vertexHypergraph v) (G.deleteVertices {v}) := by
  rw [isSeparation_iff_of_le (vertexHypergraph_le hv) (deleteVertices_le G {v})]
  refine ⟨?_, ?_, ?_⟩
  · simpa [vertexHypergraph, deleteVertices] using Set.insert_sdiff_self_of_mem hv
  · ext e
    simp [vertexHypergraph, deleteVertices, hiso e]
  · simp [vertexHypergraph, deleteVertices]

theorem separationOrder_vertexHypergraph_deleteVertices (G : Hypergraph α β) (v : α) :
    separationOrder (vertexHypergraph v) (G.deleteVertices {v}) = 0 := by
  simp [separationOrder, vertexHypergraph, deleteVertices]

/-! ## Section 1 remarks: tangle order bound and truncation -/

/-- Every tangle `𝒯` in `G` has order `≤ |V(G)|` (Graph Minors X, Section 1, page 154):
"Every tangle $\mathscr{T}$ has order $\le |V(G)|$, since $(G, G \setminus E(G)), (G
\setminus E(G), G) \notin \mathscr{T}$." -/
theorem IsTangle.order_le_ncard_vertexSet {G : Hypergraph α β} {θ : ℕ}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} (h𝒯 : IsTangle G θ 𝒯) :
    θ ≤ G.vertexSet.ncard := by
  by_contra! hlt
  have hsep : G.IsSeparation G (G.deleteEdges G.edgeSet) := by
    rw [isSeparation_iff_of_le le_rfl (deleteEdges_le G G.edgeSet)]
    simp [deleteEdges]
  have hord : separationOrder G (G.deleteEdges G.edgeSet) < θ := by
    simpa [separationOrder, deleteEdges] using hlt
  rcases h𝒯.axiom1 hsep hord with h1 | h2
  · exact h𝒯.axiom3 h1 rfl
  · exact h𝒯.axiom3 h2 rfl

theorem bddAbove_tangle_orders (G : Hypergraph α β) :
    BddAbove {θ : ℕ | ∃ 𝒯, IsTangle G θ 𝒯} :=
  ⟨G.vertexSet.ncard, fun _ ⟨_, h𝒯⟩ ↦ h𝒯.order_le_ncard_vertexSet⟩

theorem IsTangle.le_tangleNumber {G : Hypergraph α β} {θ : ℕ}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} (h𝒯 : IsTangle G θ 𝒯) :
    θ ≤ tangleNumber G :=
  le_csSup (bddAbove_tangle_orders G) ⟨𝒯, h𝒯⟩

theorem tangleNumber_le_ncard_vertexSet (G : Hypergraph α β) :
    tangleNumber G ≤ G.vertexSet.ncard := by
  unfold tangleNumber
  rcases Set.eq_empty_or_nonempty {θ : ℕ | ∃ 𝒯, IsTangle G θ 𝒯} with h | h
  · simp [h]
  · exact csSup_le h fun _ ⟨_, h𝒯⟩ ↦ h𝒯.order_le_ncard_vertexSet

/-- The truncation of a tangle of order `θ` to order `θ'` (`1 ≤ θ' ≤ θ`) is a tangle of order `θ'`
(Graph Minors X, Section 1, page 155, and Section 6, page 170). -/
theorem IsTangle.truncation {G : Hypergraph α β} {θ θ' : ℕ}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} (h𝒯 : IsTangle G θ 𝒯)
    (h1 : 1 ≤ θ') (hle : θ' ≤ θ) :
    IsTangle G θ' (truncation 𝒯 θ') where
  one_le := h1
  isSeparation _ _ h := h𝒯.isSeparation h.1
  order_lt _ _ h := h.2
  axiom1 A B hsep hord := by
    rcases h𝒯.axiom1 hsep (hord.trans_le hle) with h | h
    · exact Or.inl ⟨h, hord⟩
    · exact Or.inr ⟨h, by rwa [separationOrder_comm]⟩
  axiom2 _ _ _ _ _ _ h1 h2 h3 := h𝒯.axiom2 h1.1 h2.1 h3.1
  axiom3 _ _ h := h𝒯.axiom3 h.1

theorem exists_isTangle_of_le_tangleNumber {G : Hypergraph α β} {θ : ℕ}
    (h1 : 1 ≤ θ) (hle : θ ≤ tangleNumber G) :
    ∃ 𝒯, IsTangle G θ 𝒯 := by
  have hne : {θ' : ℕ | ∃ 𝒯, IsTangle G θ' 𝒯}.Nonempty := by
    by_contra! hemp
    have : tangleNumber G = 0 := by simp [tangleNumber, hemp]
    omega
  obtain ⟨𝒯, h𝒯⟩ := Nat.sSup_mem hne (bddAbove_tangle_orders G)
  exact ⟨truncation 𝒯 θ, h𝒯.truncation h1 hle⟩

/-! ## Section 2: Tangle Lemmas (2.1)–(2.5), (2.7)–(2.9) -/

/-- **Graph Minors X, (2.1)** (page 155):
"If $\mathscr{T}$ is a tangle and $(A, B) \in \mathscr{T}$ then $(B, A) \notin \mathscr{T}$." -/
theorem theorem_2_1_proof {G : Hypergraph α β} {θ : ℕ}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} (h𝒯 : IsTangle G θ 𝒯)
    {A B : Hypergraph α β} (hAB : (A, B) ∈ 𝒯) :
    (B, A) ∉ 𝒯 := by
  intro hBA
  have hsep := h𝒯.isSeparation hAB
  apply h𝒯.axiom2 hAB hAB hBA
  rw [union_self, hsep.union_eq]

/-- **Graph Minors X, (2.2)** (page 155):
"If $\mathscr{T}$ is a tangle of order $\theta$ and $(A, B), (A', B') \in \mathscr{T}$ and
$(A \cup A', B \cap B')$ has order $< \theta$ then $(A \cup A', B \cap B') \in \mathscr{T}$." -/
theorem theorem_2_2_proof {G : Hypergraph α β} {θ : ℕ}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} (h𝒯 : IsTangle G θ 𝒯)
    {A B A' B' : Hypergraph α β} (hAB : (A, B) ∈ 𝒯) (hA'B' : (A', B') ∈ 𝒯)
    (hord : separationOrder (A ∪ A') (B ∩ B') < θ) :
    (A ∪ A', B ∩ B') ∈ 𝒯 := by
  have hsep1 := h𝒯.isSeparation hAB
  have hsep2 := h𝒯.isSeparation hA'B'
  have hsep : G.IsSeparation (A ∪ A') (B ∩ B') := hsep1.union_inter hsep2
  rcases h𝒯.axiom1 hsep hord with h | h
  · exact h
  · exfalso
    exact h𝒯.axiom2 hAB hA'B' h hsep.union_eq

/-- **Graph Minors X, (2.3)** (page 155):
"If $\mathscr{T}$ has order $\ge 2$ and $(A_1, B_1), (A_2, B_2), (A_3, B_3) \in \mathscr{T}$
then $E(A_1 \cup A_2 \cup A_3) \ne E(G)$." -/
theorem theorem_2_3_proof {G : Hypergraph α β} {θ : ℕ}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} (h𝒯 : IsTangle G θ 𝒯) (hθ : 2 ≤ θ)
    {A₁ B₁ A₂ B₂ A₃ B₃ : Hypergraph α β}
    (h₁ : (A₁, B₁) ∈ 𝒯) (h₂ : (A₂, B₂) ∈ 𝒯) (h₃ : (A₃, B₃) ∈ 𝒯) :
    (A₁ ∪ A₂ ∪ A₃).edgeSet ≠ G.edgeSet := by
  intro hE_bad
  let S : Set ℕ :=
    {n : ℕ | ∃ A₁' B₁', (A₁', B₁') ∈ 𝒯 ∧ (A₁' ∪ A₂ ∪ A₃).edgeSet = G.edgeSet ∧
      A₁'.vertexSet.ncard = n}
  have hSne : S.Nonempty := ⟨A₁.vertexSet.ncard, A₁, B₁, h₁, hE_bad, rfl⟩
  have hSbdd : BddAbove S := by
    refine ⟨G.vertexSet.ncard, ?_⟩
    rintro n ⟨A₁', B₁', h1', -, rfl⟩
    exact Set.ncard_le_ncard (h𝒯.isSeparation h1').left_le.vertexSet_subset G.vertexSet_finite
  obtain ⟨A₁', B₁', h₁', hE', hmax⟩ := Nat.sSup_mem hSne hSbdd
  have hle_max : ∀ A₁'' B₁'', (A₁'', B₁'') ∈ 𝒯 → (A₁'' ∪ A₂ ∪ A₃).edgeSet = G.edgeSet →
      A₁''.vertexSet.ncard ≤ A₁'.vertexSet.ncard := by
    intro A₁'' B₁'' hm hE''
    rw [hmax]
    exact le_csSup hSbdd ⟨A₁'', B₁'', hm, hE'', rfl⟩
  have hU_le : A₁' ∪ A₂ ∪ A₃ ≤ G :=
    union_le (union_le (h𝒯.isSeparation h₁').left_le (h𝒯.isSeparation h₂).left_le)
      (h𝒯.isSeparation h₃).left_le
  have hU_ne : A₁' ∪ A₂ ∪ A₃ ≠ G := h𝒯.axiom2 h₁' h₂ h₃
  have hV_ne : (A₁' ∪ A₂ ∪ A₃).vertexSet ≠ G.vertexSet := by
    intro hV'
    exact hU_ne (eq_of_le_of_vertexSet_eq_of_edgeSet_eq hU_le le_rfl hV' hE')
  obtain ⟨v, hvG, hv_not⟩ := Set.exists_of_ssubset
    (ssubset_of_subset_of_ne hU_le.vertexSet_subset hV_ne)
  have hiso : ∀ e, ¬ G.Inc e v := by
    intro e hinc
    have he : e ∈ (A₁' ∪ A₂ ∪ A₃).edgeSet := hE'.symm ▸ G.edge_mem_of_inc hinc
    have hinc' : (A₁' ∪ A₂ ∪ A₃).Inc e v := (inc_iff_of_le hU_le he).2 hinc
    exact hv_not ((A₁' ∪ A₂ ∪ A₃).vertex_mem_of_inc hinc')
  let K : Hypergraph α β := vertexHypergraph v
  have hsepK : G.IsSeparation K (G.deleteVertices {v}) :=
    isSeparation_vertexHypergraph_deleteVertices hvG hiso
  have hordK : separationOrder K (G.deleteVertices {v}) < θ := by
    rw [separationOrder_vertexHypergraph_deleteVertices]
    omega
  have hKG_not : (G.deleteVertices {v}, K) ∉ 𝒯 := by
    intro hGK
    have hsepKG : G.IsSeparation K G := by
      rw [isSeparation_iff_of_le (vertexHypergraph_le hvG) le_rfl]
      simp [vertexHypergraph, Set.insert_eq_of_mem hvG]
    have hordKG : separationOrder K G < θ := by
      have : (K ∩ G).vertexSet = {v} := by
        simp [K, vertexHypergraph, Set.singleton_subset_iff.2 hvG]
      rw [separationOrder, this, Set.ncard_singleton]
      exact hθ
    have hGK_full_not : (G, K) ∉ 𝒯 := by
      intro hGK_full
      apply h𝒯.axiom2 hGK_full hGK_full hGK_full
      simp [union_self]
    have hKG_mem : (K, G) ∈ 𝒯 := (h𝒯.axiom1 hsepKG hordKG).resolve_right hGK_full_not
    apply h𝒯.axiom2 hGK hKG_mem hKG_mem
    rw [union_assoc, union_self, union_comm, hsepK.union_eq]
  have hKG : (K, G.deleteVertices {v}) ∈ 𝒯 :=
    (h𝒯.axiom1 hsepK hordK).resolve_right hKG_not
  have hord_union : separationOrder (K ∪ A₁') ((G.deleteVertices {v}) ∩ B₁') < θ := by
    have hsub : ((K ∪ A₁') ∩ (G.deleteVertices {v} ∩ B₁')).vertexSet ⊆
        (A₁' ∩ B₁').vertexSet := by
      intro x hx
      simp only [inter_vertexSet, union_vertexSet, K, vertexHypergraph, deleteVertices,
        Set.mem_inter_iff, Set.mem_union, Set.mem_singleton_iff, Set.mem_sdiff] at hx ⊢
      rcases hx with ⟨rfl | hxA, ⟨_, hne⟩, hxB⟩
      · exact (hne rfl).elim
      · exact ⟨hxA, hxB⟩
    have hle_ord : separationOrder (K ∪ A₁') ((G.deleteVertices {v}) ∩ B₁') ≤
        separationOrder A₁' B₁' :=
      Set.ncard_le_ncard hsub ((A₁' ∩ B₁').vertexSet_finite)
    exact hle_ord.trans_lt (h𝒯.order_lt h₁')
  have hKA_mem : (K ∪ A₁', (G.deleteVertices {v}) ∩ B₁') ∈ 𝒯 :=
    theorem_2_2_proof h𝒯 hKG h₁' hord_union
  have hKA_edge : ((K ∪ A₁') ∪ A₂ ∪ A₃).edgeSet = G.edgeSet := by
    simpa [K, vertexHypergraph] using hE'
  have hv_not_A₁ : v ∉ A₁'.vertexSet := fun hvA ↦ hv_not (Or.inl (Or.inl hvA))
  have hcard : (K ∪ A₁').vertexSet.ncard = A₁'.vertexSet.ncard + 1 := by
    change ({v} ∪ A₁'.vertexSet).ncard = A₁'.vertexSet.ncard + 1
    rw [Set.singleton_union, Set.ncard_insert_of_notMem hv_not_A₁ A₁'.vertexSet_finite]
  have := hle_max (K ∪ A₁') ((G.deleteVertices {v}) ∩ B₁') hKA_mem hKA_edge
  omega

/-- **Graph Minors X, (2.4)** (page 156):
"Let $\theta \ge 1$, and let $e$ be an edge of $G$ with size $\ge \theta$. Let $\mathscr{T}$
be the set of all separations $(A, B)$ of $G$ of order $< \theta$ with $e \in E(B)$. Then
$\mathscr{T}$ is a tangle of order $\theta$." -/
theorem theorem_2_4_proof {G : Hypergraph α β} {θ : ℕ} (hθ : 1 ≤ θ) {e : β}
    (he : e ∈ G.edgeSet) (hsize : θ ≤ edgeSize G e) :
    IsTangle G θ
      {p | G.IsSeparation p.1 p.2 ∧ separationOrder p.1 p.2 < θ ∧ e ∈ p.2.edgeSet} where
  one_le := hθ
  isSeparation _ _ h := h.1
  order_lt _ _ h := h.2.1
  axiom1 A B hsep hord := by
    have heAB : e ∈ A.edgeSet ∪ B.edgeSet := hsep.edgeSet_union.symm ▸ he
    rcases heAB with heA | heB
    · exact Or.inr ⟨hsep.symm, by rwa [separationOrder_comm], heA⟩
    · exact Or.inl ⟨hsep, hord, heB⟩
  axiom2 A₁ B₁ A₂ B₂ A₃ B₃ h1 h2 h3 hU := by
    have he1 : e ∉ A₁.edgeSet := h1.1.notMem_edgeSet_left h1.2.2
    have he2 : e ∉ A₂.edgeSet := h2.1.notMem_edgeSet_left h2.2.2
    have he3 : e ∉ A₃.edgeSet := h3.1.notMem_edgeSet_left h3.2.2
    have heU : e ∈ (A₁ ∪ A₂ ∪ A₃).edgeSet := hU.symm ▸ he
    simp only [union_edgeSet, Set.mem_union] at heU
    tauto
  axiom3 A B h hVA := by
    rcases h with ⟨hsep, hord, heB⟩
    dsimp only at hsep hord heB
    have hends : G.ends e ⊆ (A ∩ B).vertexSet := by
      intro v hv
      have hvG : v ∈ A.vertexSet := hVA.symm ▸ G.vertex_mem_of_inc hv
      have hvB : v ∈ B.vertexSet := B.vertex_mem_of_inc ((inc_iff_of_le hsep.right_le heB).2 hv)
      exact ⟨hvG, hvB⟩
    have hle : edgeSize G e ≤ separationOrder A B :=
      Set.ncard_le_ncard hends (A ∩ B).vertexSet_finite
    omega

/-- **Graph Minors X, (2.5)** (page 156):
"$G$ has a tangle if and only if $V(G) \ne \emptyset$." -/
theorem theorem_2_5_proof (G : Hypergraph α β) :
    (∃ θ 𝒯, IsTangle G θ 𝒯) ↔ G.vertexSet.Nonempty := by
  constructor
  · rintro ⟨θ, 𝒯, h𝒯⟩
    have h1 := h𝒯.one_le
    have h2 := h𝒯.order_le_ncard_vertexSet
    exact Set.nonempty_of_ncard_ne_zero (by omega)
  · rintro ⟨v, hv⟩
    refine ⟨1, {p | G.IsSeparation p.1 p.2 ∧ separationOrder p.1 p.2 < 1 ∧ v ∈ p.2.vertexSet},
      ⟨le_rfl, fun _ _ h ↦ h.1, fun _ _ h ↦ h.2.1, ?_, ?_, ?_⟩⟩
    · intro A B hsep hord
      have hvAB : v ∈ A.vertexSet ∪ B.vertexSet := hsep.vertexSet_union.symm ▸ hv
      rcases hvAB with hvA | hvB
      · exact Or.inr ⟨hsep.symm, by rwa [separationOrder_comm], hvA⟩
      · exact Or.inl ⟨hsep, hord, hvB⟩
    · intro A₁ B₁ A₂ B₂ A₃ B₃ h1 h2 h3 hU
      have notMem_left : ∀ {A B : Hypergraph α β}, G.IsSeparation A B → separationOrder A B < 1 →
          v ∈ B.vertexSet → v ∉ A.vertexSet := by
        intro A B _ hord hvB hvA
        dsimp only [separationOrder] at hord
        have hemp : (A ∩ B).vertexSet = ∅ :=
          (Set.ncard_eq_zero (A ∩ B).vertexSet_finite).1 (by omega)
        exact Set.notMem_empty v (hemp ▸ ⟨hvA, hvB⟩)
      have hv1 := notMem_left h1.1 h1.2.1 h1.2.2
      have hv2 := notMem_left h2.1 h2.2.1 h2.2.2
      have hv3 := notMem_left h3.1 h3.2.1 h3.2.2
      have hvU : v ∈ (A₁ ∪ A₂ ∪ A₃).vertexSet := hU.symm ▸ hv
      simp only [union_vertexSet, Set.mem_union] at hvU
      tauto
    · intro A B ⟨_, hord, hvB⟩ hVA
      dsimp only [separationOrder] at hord hvB
      have hemp : (A ∩ B).vertexSet = ∅ :=
        (Set.ncard_eq_zero (A ∩ B).vertexSet_finite).1 (by omega)
      exact Set.notMem_empty v (hemp ▸ ⟨hVA.symm ▸ hv, hvB⟩)

/-- **Graph Minors X, (2.7)** (page 157):
"Let $\mathscr{T}$ be a set of separations of a hypergraph $G$, each of order $<\theta$,
satisfying the first and second tangle axioms. Then $\mathscr{T}$ is a tangle if and only if
$(K_e, G\setminus e)\in \mathscr{T}$ for every $e\in E(G)$ of size $<\theta$, where $K_e$ is
the hypergraph formed by $e$ and its ends." -/
theorem theorem_2_7_proof {G : Hypergraph α β} {θ : ℕ} (hθ : 1 ≤ θ)
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)}
    (hsep : ∀ ⦃A B : Hypergraph α β⦄, (A, B) ∈ 𝒯 → G.IsSeparation A B)
    (hord : ∀ ⦃A B : Hypergraph α β⦄, (A, B) ∈ 𝒯 → separationOrder A B < θ)
    (hax1 : TangleAxiom1 G θ 𝒯) (hax2 : TangleAxiom2 G 𝒯) :
    IsTangle G θ 𝒯 ↔
      ∀ e ∈ G.edgeSet, edgeSize G e < θ →
        (edgeHypergraph G e, G.deleteEdges {e}) ∈ 𝒯 := by
  constructor
  · intro h𝒯 e he hsize
    have hs := isSeparation_edgeHypergraph_deleteEdges he
    have ho : separationOrder (edgeHypergraph G e) (G.deleteEdges {e}) < θ := by
      rwa [separationOrder_edgeHypergraph_deleteEdges]
    rcases h𝒯.axiom1 hs ho with h | h
    · exact h
    · exfalso
      exact h𝒯.axiom3 h rfl
  · intro hKe
    refine ⟨hθ, hsep, hord, hax1, hax2, ?_⟩
    unfold TangleAxiom3
    by_contra! hnot3
    rcases hnot3 with ⟨A₀, B₀, hAB₀, hVA₀⟩
    let S : Set ℕ := {n : ℕ | ∃ A B, (A, B) ∈ 𝒯 ∧ A.vertexSet = G.vertexSet ∧ B.edgeSet.ncard = n}
    have hSne : S.Nonempty := ⟨B₀.edgeSet.ncard, A₀, B₀, hAB₀, hVA₀, rfl⟩
    obtain ⟨A, B, hAB, hVA, hmin⟩ := Nat.sInf_mem hSne
    have hle_min : ∀ A' B', (A', B') ∈ 𝒯 → A'.vertexSet = G.vertexSet →
        B.edgeSet.ncard ≤ B'.edgeSet.ncard := by
      intro A' B' hm hV'
      rw [hmin]
      exact Nat.sInf_le ⟨A', B', hm, hV', rfl⟩
    have hsepAB := hsep hAB
    have hA_ne_G : A ≠ G := by
      intro hAG
      apply hax2 hAB hAB hAB
      simp [union_self, hAG]
    have hEB_ne : B.edgeSet.Nonempty := by
      rw [Set.nonempty_iff_ne_empty]
      intro hEB
      apply hA_ne_G
      have hEA : A.edgeSet = G.edgeSet := by
        simpa [hEB] using hsepAB.edgeSet_union
      exact eq_of_le_of_vertexSet_eq_of_edgeSet_eq hsepAB.left_le le_rfl hVA hEA
    obtain ⟨e, heB⟩ := hEB_ne
    have heG : e ∈ G.edgeSet := hsepAB.right_le.edgeSet_subset heB
    have hends_sub : G.ends e ⊆ (A ∩ B).vertexSet := by
      intro v hv
      exact ⟨hVA.symm ▸ G.vertex_mem_of_inc hv,
        B.vertex_mem_of_inc ((inc_iff_of_le hsepAB.right_le heB).2 hv)⟩
    have hsize : edgeSize G e < θ :=
      (Set.ncard_le_ncard hends_sub (A ∩ B).vertexSet_finite).trans_lt (hord hAB)
    let Ke := edgeHypergraph G e
    have hsep' : G.IsSeparation (A ∪ Ke) (B.deleteEdges {e}) := by
      have h1 : A ∪ Ke ≤ G := union_le hsepAB.left_le (edgeHypergraph_le heG)
      have h2 : B.deleteEdges {e} ≤ G := (deleteEdges_le B {e}).trans hsepAB.right_le
      rw [isSeparation_iff_of_le h1 h2]
      refine ⟨?_, ?_, ?_⟩
      · have hVK : Ke.vertexSet ⊆ G.vertexSet := (edgeHypergraph_le heG).vertexSet_subset
        change (A.vertexSet ∪ Ke.vertexSet) ∪ B.vertexSet = G.vertexSet
        rw [hVA, Set.union_eq_left.2 hVK, Set.union_eq_left.2 hsepAB.right_le.vertexSet_subset]
      · ext f
        simp only [union_edgeSet, Ke, edgeHypergraph, deleteEdges, Set.mem_union,
          Set.mem_singleton_iff, Set.mem_sdiff]
        constructor
        · rintro ((hf | rfl) | ⟨hf, _⟩)
          · exact hsepAB.left_le.edgeSet_subset hf
          · exact heG
          · exact hsepAB.right_le.edgeSet_subset hf
        · intro hfG
          by_cases hfe : f = e
          · exact Or.inl (Or.inr hfe)
          · have hfAB : f ∈ A.edgeSet ∪ B.edgeSet := by rwa [hsepAB.edgeSet_union]
            rcases hfAB with hfA | hfB
            · exact Or.inl (Or.inl hfA)
            · exact Or.inr ⟨hfB, hfe⟩
      · ext f
        change f ∈ (A.edgeSet ∪ {e}) ∩ (B.edgeSet \ {e}) ↔ f ∈ (∅ : Set β)
        simp only [Set.mem_inter_iff, Set.mem_union, Set.mem_singleton_iff, Set.mem_sdiff,
          Set.mem_empty_iff_false, iff_false]
        rintro ⟨hfA | rfl, hfB, hne⟩
        · exact hsepAB.notMem_edgeSet_right hfA hfB
        · exact hne rfl
    have hVA' : (A ∪ Ke).vertexSet = G.vertexSet := by
      have hVK : Ke.vertexSet ⊆ G.vertexSet := (edgeHypergraph_le heG).vertexSet_subset
      simp [hVA, Set.union_eq_left.2 hVK]
    have hord' : separationOrder (A ∪ Ke) (B.deleteEdges {e}) < θ := by
      have : ((A ∪ Ke) ∩ B.deleteEdges {e}).vertexSet = (A ∩ B).vertexSet := by
        simp [deleteEdges, hVA', hVA]
      rw [separationOrder, this]
      exact hord hAB
    have hnot_mem : (A ∪ Ke, B.deleteEdges {e}) ∉ 𝒯 := by
      intro hm
      have hle := hle_min (A ∪ Ke) (B.deleteEdges {e}) hm hVA'
      have hlt : (B.deleteEdges {e}).edgeSet.ncard < B.edgeSet.ncard :=
        Set.ncard_lt_ncard (Set.sdiff_singleton_ssubset.2 heB) B.edgeSet_finite
      omega
    have hmem_swap : (B.deleteEdges {e}, A ∪ Ke) ∈ 𝒯 :=
      (hax1 hsep' hord').resolve_left hnot_mem
    have hKe_mem : (Ke, G.deleteEdges {e}) ∈ 𝒯 := hKe e heG hsize
    apply hax2 hAB hmem_swap hKe_mem
    rw [union_assoc, union_comm (B.deleteEdges {e}) Ke, ← union_assoc, hsep'.union_eq]

/-! ### Extreme separations and (2.8), (2.9) -/

/-- Every separation `(A₀, B₀) ∈ 𝒯` can be extended to an extreme separation `(A, B) ∈ 𝒯` with
`A₀ ≤ A` and `B ≤ B₀`. -/
theorem IsTangle.exists_isExtreme {G : Hypergraph α β} {θ : ℕ}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} (h𝒯 : IsTangle G θ 𝒯)
    {A₀ B₀ : Hypergraph α β} (h₀ : (A₀, B₀) ∈ 𝒯) :
    ∃ A B, IsExtreme 𝒯 A B ∧ A₀ ≤ A ∧ B ≤ B₀ := by
  let score (A B : Hypergraph α β) : ℕ :=
    A.vertexSet.ncard + A.edgeSet.ncard +
      (G.vertexSet.ncard - B.vertexSet.ncard) + (G.edgeSet.ncard - B.edgeSet.ncard)
  let S : Set ℕ := {n : ℕ | ∃ A B, (A, B) ∈ 𝒯 ∧ A₀ ≤ A ∧ B ≤ B₀ ∧ score A B = n}
  have hSne : S.Nonempty := ⟨score A₀ B₀, A₀, B₀, h₀, le_rfl, le_rfl, rfl⟩
  have hSbdd : BddAbove S := by
    refine ⟨2 * (G.vertexSet.ncard + G.edgeSet.ncard), ?_⟩
    rintro n ⟨A, B, hAB, -, -, rfl⟩
    have hV : A.vertexSet.ncard ≤ G.vertexSet.ncard :=
      Set.ncard_le_ncard (h𝒯.isSeparation hAB).left_le.vertexSet_subset G.vertexSet_finite
    have hE : A.edgeSet.ncard ≤ G.edgeSet.ncard :=
      Set.ncard_le_ncard (h𝒯.isSeparation hAB).left_le.edgeSet_subset G.edgeSet_finite
    dsimp [score]
    omega
  obtain ⟨A, B, hAB, hA₀, hB₀, hmax⟩ := Nat.sSup_mem hSne hSbdd
  refine ⟨A, B, ⟨hAB, ?_⟩, hA₀, hB₀⟩
  intro A' B' hA'B' hAA' hB'B
  have hle_score : score A' B' ≤ score A B := by
    rw [hmax]
    exact le_csSup hSbdd ⟨A', B', hA'B', hA₀.trans hAA', hB'B.trans hB₀, rfl⟩
  have hAV : A.vertexSet.ncard ≤ A'.vertexSet.ncard :=
    Set.ncard_le_ncard hAA'.vertexSet_subset A'.vertexSet_finite
  have hAE : A.edgeSet.ncard ≤ A'.edgeSet.ncard :=
    Set.ncard_le_ncard hAA'.edgeSet_subset A'.edgeSet_finite
  have hBV : B'.vertexSet.ncard ≤ B.vertexSet.ncard :=
    Set.ncard_le_ncard hB'B.vertexSet_subset B.vertexSet_finite
  have hBE : B'.edgeSet.ncard ≤ B.edgeSet.ncard :=
    Set.ncard_le_ncard hB'B.edgeSet_subset B.edgeSet_finite
  have hBGV : B.vertexSet.ncard ≤ G.vertexSet.ncard :=
    Set.ncard_le_ncard (h𝒯.isSeparation hAB).right_le.vertexSet_subset G.vertexSet_finite
  have hBGE : B.edgeSet.ncard ≤ G.edgeSet.ncard :=
    Set.ncard_le_ncard (h𝒯.isSeparation hAB).right_le.edgeSet_subset G.edgeSet_finite
  dsimp [score] at hle_score
  refine ⟨(eq_of_le_of_ncard_eq hAA' (by omega) (by omega)).symm,
    eq_of_le_of_ncard_eq hB'B (by omega) (by omega)⟩

/-- First part of **Graph Minors X, (2.8)** (page 157):
"Let $\mathscr{T}$ be a tangle of order $\theta$ in a hypergraph $G$, and let $(A, B)\in
\mathscr{T}$ be extreme. Then $(A, B)$ has order $\theta - 1$." -/
theorem theorem_2_8_order {G : Hypergraph α β} {θ : ℕ}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} (h𝒯 : IsTangle G θ 𝒯)
    {A B : Hypergraph α β} (hext : IsExtreme 𝒯 A B) :
    separationOrder A B = θ - 1 := by
  have hAB := hext.1
  have hsep := h𝒯.isSeparation hAB
  have hord := h𝒯.order_lt hAB
  have hVA_ne := h𝒯.axiom3 hAB
  obtain ⟨v, hvG, hv_notA⟩ := Set.exists_of_ssubset
    (ssubset_of_subset_of_ne hsep.left_le.vertexSet_subset hVA_ne)
  have hvB : v ∈ B.vertexSet :=
    (hsep.vertexSet_union.symm ▸ hvG).resolve_left hv_notA
  let Kv : Hypergraph α β := vertexHypergraph v
  have hKv_le_B : Kv ≤ B := vertexHypergraph_le hvB
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
  have hord_ge : θ ≤ separationOrder (A ∪ Kv) B := by
    by_contra! hlt
    rcases h𝒯.axiom1 hsep' hlt with h | h
    · exact hAK_not h
    · exact hBAK_not h
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
  have hcard : separationOrder (A ∪ Kv) B = separationOrder A B + 1 := by
    rw [separationOrder, hset_eq, Set.ncard_insert_of_notMem hv_notAB (A ∩ B).vertexSet_finite,
      separationOrder]
  omega

/-- Second part of **Graph Minors X, (2.8)** (page 157):
"Moreover, if $(B_1, B_2)$ is a separation of $B$, then either $B_1\subseteq A\cap B$ and $B_2 = B$,
or $B_2\subseteq A\cap B$ and $B_1 = B$, or $(B_1, B_2)$ has order strictly greater than
$$\min(|V(A\cap B_1)|, |V(A\cap B_2)|).$$" -/
theorem theorem_2_8_separation {G : Hypergraph α β} {θ : ℕ}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} (h𝒯 : IsTangle G θ 𝒯)
    {A B B₁ B₂ : Hypergraph α β} (hext : IsExtreme 𝒯 A B) (hB : B.IsSeparation B₁ B₂) :
    (B₁ ≤ A ∩ B ∧ B₂ = B) ∨ (B₂ ≤ A ∩ B ∧ B₁ = B) ∨
      min (A ∩ B₁).vertexSet.ncard (A ∩ B₂).vertexSet.ncard < separationOrder B₁ B₂ := by
  have hAB := hext.1
  have hsep := h𝒯.isSeparation hAB
  have hB₁_G : B₁ ≤ G := hB.left_le.trans hsep.right_le
  have hB₂_G : B₂ ≤ G := hB.right_le.trans hsep.right_le
  have hsep1 : G.IsSeparation (A ∪ B₁) B₂ := by
    rw [isSeparation_iff_of_le (union_le hsep.left_le hB₁_G) hB₂_G]
    refine ⟨?_, ?_, ?_⟩
    · rw [union_vertexSet, Set.union_assoc, hB.vertexSet_union, hsep.vertexSet_union]
    · rw [union_edgeSet, Set.union_assoc, hB.edgeSet_union, hsep.edgeSet_union]
    · ext e
      simp only [union_edgeSet, Set.mem_inter_iff, Set.mem_union, Set.mem_empty_iff_false,
        iff_false, not_and]
      rintro (heA | heB₁) heB₂
      · exact hsep.notMem_edgeSet_right heA (hB.right_le.edgeSet_subset heB₂)
      · exact hB.notMem_edgeSet_right heB₁ heB₂
  have hsep2 : G.IsSeparation (A ∪ B₂) B₁ := by
    rw [isSeparation_iff_of_le (union_le hsep.left_le hB₂_G) hB₁_G]
    refine ⟨?_, ?_, ?_⟩
    · rw [union_vertexSet, Set.union_assoc, Set.union_comm B₂.vertexSet, hB.vertexSet_union,
        hsep.vertexSet_union]
    · rw [union_edgeSet, Set.union_assoc, Set.union_comm B₂.edgeSet, hB.edgeSet_union,
        hsep.edgeSet_union]
    · ext e
      simp only [union_edgeSet, Set.mem_inter_iff, Set.mem_union, Set.mem_empty_iff_false,
        iff_false, not_and]
      rintro (heA | heB₂) heB₁
      · exact hsep.notMem_edgeSet_right heA (hB.left_le.edgeSet_subset heB₁)
      · exact hB.notMem_edgeSet_left heB₂ heB₁
  by_cases heq1 : A ∪ B₁ = A ∧ B₂ = B
  · left
    refine ⟨?_, heq1.2⟩
    have hB₁_A : B₁ ≤ A := heq1.1 ▸ le_union_right hsep.left_le hB₁_G
    exact (le_iff_of_le hB₁_G (inter_le hsep.left_le hsep.right_le)).2
      ⟨Set.subset_inter hB₁_A.vertexSet_subset hB.left_le.vertexSet_subset,
       Set.subset_inter hB₁_A.edgeSet_subset hB.left_le.edgeSet_subset⟩
  by_cases heq2 : A ∪ B₂ = A ∧ B₁ = B
  · right; left
    refine ⟨?_, heq2.2⟩
    have hB₂_A : B₂ ≤ A := heq2.1 ▸ le_union_right hsep.left_le hB₂_G
    exact (le_iff_of_le hB₂_G (inter_le hsep.left_le hsep.right_le)).2
      ⟨Set.subset_inter hB₂_A.vertexSet_subset hB.right_le.vertexSet_subset,
       Set.subset_inter hB₂_A.edgeSet_subset hB.right_le.edgeSet_subset⟩
  right; right
  have hnot1 : (A ∪ B₁, B₂) ∉ 𝒯 := fun hm ↦
    heq1 (hext.2 hm (le_union_left hsep.left_le hB₁_G) hB.right_le)
  have hnot2 : (A ∪ B₂, B₁) ∉ 𝒯 := fun hm ↦
    heq2 (hext.2 hm (le_union_left hsep.left_le hB₂_G) hB.left_le)
  have hnot_both : ¬ ((B₂, A ∪ B₁) ∈ 𝒯 ∧ (B₁, A ∪ B₂) ∈ 𝒯) := by
    rintro ⟨hm1, hm2⟩
    apply h𝒯.axiom2 hAB hm1 hm2
    rw [union_assoc, union_comm B₂ B₁, hB.union_eq, hsep.union_eq]
  have hord_AB : separationOrder A B = θ - 1 := theorem_2_8_order h𝒯 hext
  have h1_le : 1 ≤ θ := h𝒯.one_le
  have bound_of_not_swap : ∀ {C D : Hypergraph α β}, B.IsSeparation C D →
      G.IsSeparation (A ∪ C) D → (A ∪ C, D) ∉ 𝒯 → (D, A ∪ C) ∉ 𝒯 →
      (A ∩ C).vertexSet.ncard < separationOrder C D := by
    intro C D hCD hsepCD hnotCD hnotDC
    have hge : θ ≤ separationOrder (A ∪ C) D := by
      by_contra! hlt
      exact (h𝒯.axiom1 hsepCD hlt).elim hnotCD hnotDC
    have hsub : ((A ∪ C) ∩ D).vertexSet ⊆
        (C ∩ D).vertexSet ∪ ((A ∩ B).vertexSet \ (A ∩ C).vertexSet) := by
      intro v hv
      simp only [inter_vertexSet, union_vertexSet, Set.mem_inter_iff, Set.mem_union,
        Set.mem_sdiff] at hv ⊢
      rcases hv with ⟨hvA | hvC, hvD⟩
      · by_cases hvC : v ∈ C.vertexSet
        · exact Or.inl ⟨hvC, hvD⟩
        · exact Or.inr ⟨⟨hvA, hCD.right_le.vertexSet_subset hvD⟩, fun h ↦ hvC h.2⟩
      · exact Or.inl ⟨hvC, hvD⟩
    have hcard_union : ((A ∪ C) ∩ D).vertexSet.ncard ≤
        (C ∩ D).vertexSet.ncard + ((A ∩ B).vertexSet \ (A ∩ C).vertexSet).ncard :=
      (Set.ncard_le_ncard hsub
        ((C ∩ D).vertexSet_finite.union ((A ∩ B).vertexSet_finite.sdiff))).trans
        (Set.ncard_union_le _ _)
    have hAC_sub_AB : (A ∩ C).vertexSet ⊆ (A ∩ B).vertexSet :=
      Set.inter_subset_inter_right _ hCD.left_le.vertexSet_subset
    have hcard_diff : ((A ∩ B).vertexSet \ (A ∩ C).vertexSet).ncard =
        (A ∩ B).vertexSet.ncard - (A ∩ C).vertexSet.ncard :=
      Set.ncard_sdiff hAC_sub_AB (A ∩ C).vertexSet_finite
    have hAC_le : (A ∩ C).vertexSet.ncard ≤ (A ∩ B).vertexSet.ncard :=
      Set.ncard_le_ncard hAC_sub_AB (A ∩ B).vertexSet_finite
    rw [separationOrder] at hge hord_AB ⊢
    omega
  by_cases hm1 : (B₂, A ∪ B₁) ∈ 𝒯
  · have hm2 : (B₁, A ∪ B₂) ∉ 𝒯 := fun h ↦ hnot_both ⟨hm1, h⟩
    have hlt := bound_of_not_swap hB.symm hsep2 hnot2 hm2
    rw [separationOrder_comm] at hlt
    exact (min_le_right _ _).trans_lt hlt
  · have hlt := bound_of_not_swap hB hsep1 hnot1 hm1
    exact (min_le_left _ _).trans_lt hlt

/-- Third part of **Graph Minors X, (2.8)** (page 157):
"In particular, there is no separation $(B_1, B_2)$ of $B$ with $B_1, B_2$ non-null of order $0$" -/
theorem theorem_2_8_no_order_zero {G : Hypergraph α β} {θ : ℕ}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} (h𝒯 : IsTangle G θ 𝒯)
    {A B B₁ B₂ : Hypergraph α β} (hext : IsExtreme 𝒯 A B) (hB : B.IsSeparation B₁ B₂)
    (h1 : IsNonNull B₁) (h2 : IsNonNull B₂) :
    separationOrder B₁ B₂ ≠ 0 := by
  intro hord0
  have hV_inter : (B₁ ∩ B₂).vertexSet = ∅ :=
    (Set.ncard_eq_zero (B₁ ∩ B₂).vertexSet_finite).1 hord0
  rcases theorem_2_8_separation h𝒯 hext hB with ⟨_, rfl⟩ | ⟨_, rfl⟩ | hlt
  · have hV₁ : B₁.vertexSet = ∅ := by
      rw [← Set.inter_eq_left.2 hB.left_le.vertexSet_subset]
      exact hV_inter
    have hE₁ : B₁.edgeSet = ∅ := by
      rw [← Set.inter_eq_left.2 hB.left_le.edgeSet_subset]
      exact hB.edgeSet_inter_eq
    rcases h1 with ⟨v, hv⟩ | ⟨e, he⟩
    · exact Set.notMem_empty v (hV₁ ▸ hv)
    · exact Set.notMem_empty e (hE₁ ▸ he)
  · have hV₂ : B₂.vertexSet = ∅ := by
      rw [← Set.inter_eq_right.2 hB.right_le.vertexSet_subset]
      exact hV_inter
    have hE₂ : B₂.edgeSet = ∅ := by
      rw [← Set.inter_eq_right.2 hB.right_le.edgeSet_subset]
      exact hB.edgeSet_inter_eq
    rcases h2 with ⟨v, hv⟩ | ⟨e, he⟩
    · exact Set.notMem_empty v (hV₂ ▸ hv)
    · exact Set.notMem_empty e (hE₂ ▸ he)
  · omega

/-- Fourth part of **Graph Minors X, (2.8)** (page 157):
"and there is no edge of $B$ with all its ends in $V(A)$." -/
theorem theorem_2_8_no_edge_ends_subset {G : Hypergraph α β} {θ : ℕ}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} (h𝒯 : IsTangle G θ 𝒯)
    {A B : Hypergraph α β} (hext : IsExtreme 𝒯 A B) {e : β} (heB : e ∈ B.edgeSet) :
    ¬ B.ends e ⊆ A.vertexSet := by
  intro hsub
  have hAB := hext.1
  have hsep := h𝒯.isSeparation hAB
  let Ke := edgeHypergraph B e
  have hsepB : B.IsSeparation Ke (B.deleteEdges {e}) :=
    isSeparation_edgeHypergraph_deleteEdges heB
  have hKe_not_le : ¬ Ke ≤ A ∩ B := by
    intro hle
    have heAB : e ∈ (A ∩ B).edgeSet := hle.edgeSet_subset (Set.mem_singleton e)
    exact hsep.notMem_edgeSet_left heB heAB.1
  have hBe_not_le : ¬ B.deleteEdges {e} ≤ A ∩ B := by
    intro hle
    have hVB : B.vertexSet ⊆ A.vertexSet :=
      hle.vertexSet_subset.trans Set.inter_subset_left
    have hVA : A.vertexSet = G.vertexSet := by
      rw [← hsep.vertexSet_union, Set.union_eq_left.2 hVB]
    exact h𝒯.axiom3 hAB hVA
  rcases theorem_2_8_separation h𝒯 hext hsepB with ⟨h1, _⟩ | ⟨h2, _⟩ | hlt
  · exact hKe_not_le h1
  · exact hBe_not_le h2
  · have hord : separationOrder Ke (B.deleteEdges {e}) = (B.ends e).ncard :=
      separationOrder_edgeHypergraph_deleteEdges B e
    have h1 : (A ∩ Ke).vertexSet = B.ends e := by
      simpa [Ke, edgeHypergraph] using Set.inter_eq_right.2 hsub
    have h2 : B.ends e ⊆ (A ∩ B.deleteEdges {e}).vertexSet :=
      Set.subset_inter hsub fun _ hv ↦ B.vertex_mem_of_inc hv
    have hle2 : (B.ends e).ncard ≤ (A ∩ B.deleteEdges {e}).vertexSet.ncard :=
      Set.ncard_le_ncard h2 (A ∩ B.deleteEdges {e}).vertexSet_finite
    rw [hord, h1] at hlt
    omega

/-- **Graph Minors X, (2.8)** (page 157):
"(2.8) *Let $\mathscr{T}$ be a tangle of order $\theta$ in a hypergraph $G$, and let
$(A, B)\in \mathscr{T}$ be extreme. Then $(A, B)$ has order $\theta - 1$. Moreover, if $(B_1, B_2)$
is a separation of $B$, then either $B_1\subseteq A\cap B$ and $B_2 = B$, or $B_2\subseteq A\cap B$
and $B_1 = B$, or $(B_1, B_2)$ has order strictly greater than*
$$\min(|V(A\cap B_1)|, |V(A\cap B_2)|).$$
*In particular, there is no separation $(B_1, B_2)$ of $B$ with $B_1, B_2$ non-null of order $0$,
and there is no edge of $B$ with all its ends in $V(A)$.*" -/
theorem theorem_2_8_proof {G : Hypergraph α β} {θ : ℕ}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} (h𝒯 : IsTangle G θ 𝒯)
    {A B : Hypergraph α β} (hext : IsExtreme 𝒯 A B) :
    separationOrder A B = θ - 1 ∧
    (∀ ⦃B₁ B₂ : Hypergraph α β⦄, B.IsSeparation B₁ B₂ →
      (B₁ ≤ A ∩ B ∧ B₂ = B) ∨ (B₂ ≤ A ∩ B ∧ B₁ = B) ∨
        min (A ∩ B₁).vertexSet.ncard (A ∩ B₂).vertexSet.ncard < separationOrder B₁ B₂) ∧
    (∀ ⦃B₁ B₂ : Hypergraph α β⦄, B.IsSeparation B₁ B₂ →
      IsNonNull B₁ → IsNonNull B₂ → separationOrder B₁ B₂ ≠ 0) ∧
    (∀ e ∈ B.edgeSet, ¬ B.ends e ⊆ A.vertexSet) :=
  ⟨theorem_2_8_order h𝒯 hext,
   fun _ _ hB ↦ theorem_2_8_separation h𝒯 hext hB,
   fun _ _ hB h1 h2 ↦ theorem_2_8_no_order_zero h𝒯 hext hB h1 h2,
   fun _ heB ↦ theorem_2_8_no_edge_ends_subset h𝒯 hext heB⟩

/-- Case 1 of **Graph Minors X, (2.9)** (page 158): if `(A₁, B₁) ∈ 𝒯`, `(A₂, B₂)` is a separation
of order `< θ`, and `V(B₁) ⊆ V(B₂)`, then `(A₂, B₂) ∈ 𝒯`. -/
theorem theorem_2_9_case_1 {G : Hypergraph α β} {θ : ℕ}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} (h𝒯 : IsTangle G θ 𝒯)
    {A₁ B₁ A₂ B₂ : Hypergraph α β} (h₁ : (A₁, B₁) ∈ 𝒯)
    (hsep₂ : G.IsSeparation A₂ B₂) (hord₂ : separationOrder A₂ B₂ < θ)
    (hV : B₁.vertexSet ⊆ B₂.vertexSet) :
    (A₂, B₂) ∈ 𝒯 := by
  by_contra hnot
  have hB₂A₂ : (B₂, A₂) ∈ 𝒯 := (h𝒯.axiom1 hsep₂ hord₂).resolve_left hnot
  obtain ⟨A, B, hext, hB₂A, hBA₂⟩ := h𝒯.exists_isExtreme hB₂A₂
  have hsepAB := h𝒯.isSeparation hext.1
  have hsep₁ := h𝒯.isSeparation h₁
  have hB₁_not_le_A : ¬ B₁ ≤ A := by
    intro hle
    apply h𝒯.axiom2 hext.1 h₁ h₁
    rw [union_assoc, union_self]
    exact eq_of_le_of_vertexSet_eq_of_edgeSet_eq (union_le hsepAB.left_le hsep₁.left_le) le_rfl
      (by
        rw [union_vertexSet, ← Set.union_eq_left.2 hle.vertexSet_subset, Set.union_assoc,
          Set.union_comm B₁.vertexSet A₁.vertexSet, hsep₁.vertexSet_union,
          Set.union_eq_right.2 hsepAB.left_le.vertexSet_subset])
      (by
        rw [union_edgeSet, ← Set.union_eq_left.2 hle.edgeSet_subset, Set.union_assoc,
          Set.union_comm B₁.edgeSet A₁.edgeSet, hsep₁.edgeSet_union,
          Set.union_eq_right.2 hsepAB.left_le.edgeSet_subset])
  have hVB₁_A : B₁.vertexSet ⊆ A.vertexSet := hV.trans hB₂A.vertexSet_subset
  have hEB₁_A : B₁.edgeSet ⊆ A.edgeSet := by
    intro e heB₁
    have heG : e ∈ G.edgeSet := hsep₁.right_le.edgeSet_subset heB₁
    have heAB : e ∈ A.edgeSet ∪ B.edgeSet := by rwa [hsepAB.edgeSet_union]
    rcases heAB with heA | heB
    · exact heA
    · exfalso
      apply theorem_2_8_no_edge_ends_subset h𝒯 hext heB
      rw [← hsepAB.right_le.ends_eq e heB, hsep₁.right_le.ends_eq e heB₁]
      exact Set.Subset.trans (fun _ hv ↦ B₁.vertex_mem_of_inc hv) hVB₁_A
  exact hB₁_not_le_A ((le_iff_of_le hsep₁.right_le hsepAB.left_le).2 ⟨hVB₁_A, hEB₁_A⟩)

/-- **Graph Minors X, (2.9)** (page 158):
"Let $\mathscr{T}$ be a tangle of order $\theta$ in a hypergraph $G$, and let $(A_1, B_1)\in
\mathscr{T}$. Let $(A_2, B_2)$ be a separation of order $<\theta$. If either* (i)
$V(B_1)\subseteq V(B_2)$, or (ii) $V(A_2)\subseteq V(A_1)$, or (iii) $\theta \ge 2$ and
$E(A_2)\subseteq E(A_1)$ (equivalently, $E(B_1)\subseteq E(B_2)$) *then* $(A_2, B_2)\in
\mathscr{T}$." -/
theorem theorem_2_9_proof {G : Hypergraph α β} {θ : ℕ}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} (h𝒯 : IsTangle G θ 𝒯)
    {A₁ B₁ A₂ B₂ : Hypergraph α β} (h₁ : (A₁, B₁) ∈ 𝒯)
    (hsep₂ : G.IsSeparation A₂ B₂) (hord₂ : separationOrder A₂ B₂ < θ)
    (h : B₁.vertexSet ⊆ B₂.vertexSet ∨ A₂.vertexSet ⊆ A₁.vertexSet ∨
      (2 ≤ θ ∧ A₂.edgeSet ⊆ A₁.edgeSet)) :
    (A₂, B₂) ∈ 𝒯 := by
  rcases h with hV | hV | ⟨hθ, hE⟩
  · exact theorem_2_9_case_1 h𝒯 h₁ hsep₂ hord₂ hV
  · by_contra hnot
    have hB₂A₂ : (B₂, A₂) ∈ 𝒯 := (h𝒯.axiom1 hsep₂ hord₂).resolve_left hnot
    have hsep₁ := (h𝒯.isSeparation h₁).symm
    have hord₁ : separationOrder B₁ A₁ < θ := by
      rw [separationOrder_comm]
      exact h𝒯.order_lt h₁
    have hB₁A₁ : (B₁, A₁) ∈ 𝒯 := theorem_2_9_case_1 h𝒯 hB₂A₂ hsep₁ hord₁ hV
    exact theorem_2_1_proof h𝒯 h₁ hB₁A₁
  · by_contra hnot
    have hB₂A₂ : (B₂, A₂) ∈ 𝒯 := (h𝒯.axiom1 hsep₂ hord₂).resolve_left hnot
    obtain ⟨A, B, hext, hB₂A, hBA₂⟩ := h𝒯.exists_isExtreme hB₂A₂
    have hsepAB := h𝒯.isSeparation hext.1
    have hsep₁ := h𝒯.isSeparation h₁
    have hB_not_le_A₁ : ¬ B ≤ A₁ := by
      intro hle
      apply h𝒯.axiom2 hext.1 h₁ h₁
      rw [union_assoc, union_self]
      exact eq_of_le_of_vertexSet_eq_of_edgeSet_eq (union_le hsepAB.left_le hsep₁.left_le) le_rfl
        (by
          rw [union_vertexSet, ← Set.union_eq_right.2 hle.vertexSet_subset, ← Set.union_assoc,
            hsepAB.vertexSet_union, Set.union_eq_left.2 hsep₁.left_le.vertexSet_subset])
        (by
          rw [union_edgeSet, ← Set.union_eq_right.2 hle.edgeSet_subset, ← Set.union_assoc,
            hsepAB.edgeSet_union, Set.union_eq_left.2 hsep₁.left_le.edgeSet_subset])
    have hEB_A₁ : B.edgeSet ⊆ A₁.edgeSet := hBA₂.edgeSet_subset.trans hE
    have hVB_not_sub : ¬ B.vertexSet ⊆ A₁.vertexSet := fun hV ↦
      hB_not_le_A₁ ((le_iff_of_le hsepAB.right_le hsep₁.left_le).2 ⟨hV, hEB_A₁⟩)
    obtain ⟨v, hvB, hv_notA₁⟩ := Set.not_subset.1 hVB_not_sub
    have hisoB : ∀ e, ¬ B.Inc e v := by
      intro e hinc
      have heA₁ : e ∈ A₁.edgeSet := hEB_A₁ (B.edge_mem_of_inc hinc)
      have hincG : G.Inc e v := inc_of_le hsepAB.right_le hinc
      have hincA₁ : A₁.Inc e v := (inc_iff_of_le hsep₁.left_le heA₁).2 hincG
      exact hv_notA₁ (A₁.vertex_mem_of_inc hincA₁)
    let Kv : Hypergraph α β := vertexHypergraph v
    have hsepBv : B.IsSeparation Kv (B.deleteVertices {v}) :=
      isSeparation_vertexHypergraph_deleteVertices hvB hisoB
    have hordBv : separationOrder Kv (B.deleteVertices {v}) = 0 :=
      separationOrder_vertexHypergraph_deleteVertices B v
    have hKv_nn : IsNonNull Kv := Or.inl ⟨v, Set.mem_singleton v⟩
    have hBv_not_nn : ¬ IsNonNull (B.deleteVertices {v}) := fun hnn ↦
      theorem_2_8_no_order_zero h𝒯 hext hsepBv hKv_nn hnn hordBv
    rw [isNonNull_iff_ne_bot, not_not] at hBv_not_nn
    have hVB_eq : B.vertexSet = {v} := by
      have hdiff : B.vertexSet \ {v} = ∅ := congrArg Hypergraph.vertexSet hBv_not_nn
      exact Set.Subset.antisymm (Set.sdiff_eq_empty.1 hdiff) (Set.singleton_subset_iff.2 hvB)
    have hv_notA : v ∉ A.vertexSet := by
      intro hvA
      apply h𝒯.axiom3 hext.1
      rw [← hsepAB.vertexSet_union, hVB_eq, Set.union_eq_left.2 (Set.singleton_subset_iff.2 hvA)]
    have hAB_empty : (A ∩ B).vertexSet = ∅ := by
      simp [hVB_eq, hv_notA]
    have hord0 : separationOrder A B = 0 := by
      simp [separationOrder, hAB_empty]
    have hord_eq := theorem_2_8_order h𝒯 hext
    omega

section

variable {G H A B : Hypergraph α β}

/-- Intersecting both sides of a separation with a subgraph gives a separation
of that subgraph, as used in Graph Minors XII, Section 4, page 248. -/
theorem restrictSeparationToSubgraph (hs : G.IsSeparation A B) (hH : H ≤ G) :
    H.IsSeparation (A ∩ H) (B ∩ H) := by
  refine (isSeparation_iff_of_le (inter_le_right hs.left_le hH)
    (inter_le_right hs.right_le hH)).mpr ⟨?_, ?_, ?_⟩
  · rw [inter_vertexSet, inter_vertexSet, ← Set.union_inter_distrib_right,
      hs.vertexSet_union, Set.inter_eq_right.mpr hH.vertexSet_subset]
  · rw [inter_edgeSet, inter_edgeSet, ← Set.union_inter_distrib_right,
      hs.edgeSet_union, Set.inter_eq_right.mpr hH.edgeSet_subset]
  · apply Set.eq_empty_iff_forall_notMem.mpr
    intro e he
    exact hs.notMem_edgeSet_right he.1.1 he.2.1

/-- Restriction does not increase the order of a separation. -/
theorem separationOrder_restrict_subgraph_le (A B H : Hypergraph α β) :
    separationOrder (A ∩ H) (B ∩ H) ≤ separationOrder A B := by
  exact Set.ncard_le_ncard (fun _ hx => ⟨hx.1.1, hx.2.1⟩)
    (A ∩ B).vertexSet_finite

/-- Graph Minors XII, Section 4, page 248: the tangle induced by a tangle in a
subgraph is a tangle of the same order. Each axiom follows by intersection with
that subgraph. -/
theorem isTangle_inducedTangleFromSubgraph {θ : ℕ}
    {T : Set (Hypergraph α β × Hypergraph α β)}
    (hH : H ≤ G) (hT : IsTangle H θ T) :
    IsTangle G θ (inducedTangleFromSubgraph G H θ T) := by
  refine ⟨hT.one_le, fun _ _ h => h.1, fun _ _ h => h.2.1, ?_, ?_, ?_⟩
  · intro A B hs ho
    have hsH := restrictSeparationToSubgraph hs hH
    have hoH := lt_of_le_of_lt (separationOrder_restrict_subgraph_le A B H) ho
    rcases hT.axiom1 hsH hoH with h | h
    · exact Or.inl ⟨hs, ho, h⟩
    · exact Or.inr ⟨hs.symm, by rwa [separationOrder_comm], h⟩
  · intro A₁ B₁ A₂ B₂ A₃ B₃ h₁ h₂ h₃ heq
    apply hT.axiom2 h₁.2.2 h₂.2.2 h₃.2.2
    have hle := union_le (union_le
      (inter_le_right h₁.1.left_le hH) (inter_le_right h₂.1.left_le hH))
      (inter_le_right h₃.1.left_le hH)
    refine eq_of_le_of_vertexSet_eq_of_edgeSet_eq hle le_rfl ?_ ?_
    · simp only [union_vertexSet, inter_vertexSet]
      rw [← Set.union_inter_distrib_right, ← Set.union_inter_distrib_right]
      change (A₁ ∪ A₂ ∪ A₃).vertexSet ∩ H.vertexSet = H.vertexSet
      rw [heq, Set.inter_eq_right.mpr hH.vertexSet_subset]
    · simp only [union_edgeSet, inter_edgeSet]
      rw [← Set.union_inter_distrib_right, ← Set.union_inter_distrib_right]
      change (A₁ ∪ A₂ ∪ A₃).edgeSet ∩ H.edgeSet = H.edgeSet
      rw [heq, Set.inter_eq_right.mpr hH.edgeSet_subset]
  · intro A B h heq
    apply hT.axiom3 h.2.2
    change A.vertexSet ∩ H.vertexSet = H.vertexSet
    rw [heq, Set.inter_eq_right.mpr hH.vertexSet_subset]

end

end GraphMinor.GM10
