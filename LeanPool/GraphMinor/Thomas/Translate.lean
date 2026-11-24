/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Thomas.LeanDecomp
public import LeanPool.GraphMinor.Thomas.RootedTree

/-!
# Translation between tree-decompositions and Proof of Graph Minors IV, (5.1)

This file translates between the rooted-hypergraph tree-decompositions of Graph Minors IV
(`GraphMinor.GM04.IsTreeDecomposition`) and the tree-decompositions of Bellenbaum and Diestel
(`GraphMinor.Thomas.TreeDecomp`), deduces the Menger-like path/edge-order property of (5.1) from
leanness (condition (T4′)), and proves **Graph Minors IV, (5.1)** (`GraphMinor.GM04.thomas_5_1`).

## Main results

* `GraphMinor.Thomas.TreeDecomp.thomas_of_isLean`: a lean tree-decomposition satisfies Thomas's
  path-or-separator property between any two distinct bags.
* `GraphMinor.Thomas.treeDecompOfGM04`: converts a Graph Minors IV tree-decomposition of
`G.toRooted`
  of width $\le w$ into a `TreeDecomp G.skeleton G.vertexSet T.verts` of width $\le w$.
* `GraphMinor.Thomas.gm04OfTreeDecomp`: converts a lean `TreeDecomp G.skeleton G.vertexSet (Fin m)`
  of width $\le w$ into a Graph Minors IV tree-decomposition of `G.toRooted` on `RootedTree ℕ`
  satisfying the conclusion of `ThomasStatement`.
* `GraphMinor.GM04.thomas_5_1`: **Graph Minors IV, (5.1)** (Thomas's lemma).
-/

namespace GraphMinor.Thomas

open SimpleGraph GraphMinor.GM04

universe u v

public section

variable {α : Type u} {β : Type v}

/-! ## Step 3: Deducing (5.1) on `TreeDecomp` from leanness (T4′) -/

theorem hasDisjointPaths_mono {K : SimpleGraph α} {Z₁ Z₂ W₁ W₂ : Set α} {k : ℕ}
    (h₁ : Z₁ ⊆ W₁) (h₂ : Z₂ ⊆ W₂) (h : HasDisjointPaths K Z₁ Z₂ k) :
    HasDisjointPaths K W₁ W₂ k := by
  obtain ⟨P, hP⟩ := h
  refine ⟨fun i ↦
    { first := (P i).first
      last := (P i).last
      walk := (P i).walk
      isPath := (P i).isPath
      first_mem := h₁ (P i).first_mem
      last_mem := h₂ (P i).last_mem }, hP⟩

namespace TreeDecomp

variable {ι : Type*} [Fintype ι] {K : SimpleGraph α} {V₀ : Set α} (D : TreeDecomp K V₀ ι)

theorem exists_first_onTreePathEdge {t₁ t₂ : ι} (hne : t₁ ≠ t₂) :
    ∃ s : ι, OnTreePathEdge D.T t₁ t₂ t₁ s := by
  generalize hp : treePath D.isTree t₁ t₂ = p
  cases p with
  | nil => exact (hne rfl).elim
  | @cons _ s _ hadj q =>
    refine ⟨s, ?_⟩
    rw [onTreePathEdge_iff_mem_treePath D.isTree, hp]
    exact ⟨hadj, List.Mem.head _⟩

/-- If $\mathcal{D}$ is a lean tree-decomposition of $(K, V_0)$, then for all distinct $t_1, t_2 \in
T$
and all $k \ge 0$, either there are $k$ mutually vertex-disjoint paths in $K$ from $V_{t_1}$ to
$V_{t_2}$, or some edge $s s'$ on $t_1 T t_2$ has $|V_s \cap V_{s'}| < k$
(Bellenbaum and Diestel, Section 1, page 1). If `k` is at most the sizes of both bags, apply
condition (T4′) of leanness to `k`-subsets of the two bags. Otherwise one of the two bags has fewer
than `k` vertices, and the edge of `t₁ T t₂` at that bag has `|V_s ∩ V_{s'}| < k`. -/
theorem thomas_of_isLean (hV₀ : V₀.Finite) (hlean : D.IsLean)
    {t₁ t₂ : ι} (hne : t₁ ≠ t₂) (k : ℕ) :
    HasDisjointPaths K (D.bag t₁) (D.bag t₂) k ∨
      ∃ s s' : ι, OnTreePathEdge D.T t₁ t₂ s s' ∧ (D.bag s ∩ D.bag s').ncard < k := by
  rcases le_or_gt k (D.bag t₁).ncard with hk₁ | hk₁
  · rcases le_or_gt k (D.bag t₂).ncard with hk₂ | hk₂
    · obtain ⟨Z₁, hZ₁_sub, hZ₁_card⟩ := Set.exists_subset_card_eq hk₁
      obtain ⟨Z₂, hZ₂_sub, hZ₂_card⟩ := Set.exists_subset_card_eq hk₂
      rcases hlean t₁ t₂ Z₁ Z₂ k hZ₁_sub hZ₂_sub hZ₁_card hZ₂_card with hpaths | hex
      · exact Or.inl (hasDisjointPaths_mono hZ₁_sub hZ₂_sub hpaths)
      · exact Or.inr hex
    · right
      obtain ⟨s, hs⟩ := D.exists_first_onTreePathEdge hne.symm
      refine ⟨s, t₂, onTreePathEdge_swap (onTreePathEdge_symm_endpoints hs), ?_⟩
      have hle : (D.bag s ∩ D.bag t₂).ncard ≤ (D.bag t₂).ncard :=
        Set.ncard_le_ncard Set.inter_subset_right (D.bag_finite hV₀ t₂)
      omega
  · right
    obtain ⟨s, hs⟩ := D.exists_first_onTreePathEdge hne
    refine ⟨t₁, s, hs, ?_⟩
    have hle : (D.bag t₁ ∩ D.bag s).ncard ≤ (D.bag t₁).ncard :=
      Set.ncard_le_ncard Set.inter_subset_left (D.bag_finite hV₀ t₁)
    omega

end TreeDecomp

/-! ## Step 4A: From Graph Minors IV `IsTreeDecomposition` to `TreeDecomp` -/

/-- Convert a Graph Minors IV tree-decomposition `(T, τ)` of `G.toRooted` into a
Bellenbaum–Diestel tree-decomposition on `T.verts`. -/
noncomputable def treeDecompOfGM04 {ι : Type*} {G : Hypergraph α β} {T : RootedTree ι}
    {τ : ι → RootedHypergraph α β} (hD : IsTreeDecomposition G.toRooted T τ) :
    TreeDecomp G.skeleton G.vertexSet T.verts where
  T := toSimpleGraph T
  isTree := toSimpleGraph_isTree T
  bag t := (τ t.1).vertexSet
  iUnion_bag := by
    have h := congrArg Hypergraph.vertexSet hD.biUnion_eq
    change (⋃ i ∈ T.verts, (τ i).vertexSet) = G.vertexSet at h
    ext v
    rw [← h, Set.mem_iUnion, Set.mem_iUnion₂]
    exact ⟨fun ⟨t, hv⟩ ↦ ⟨t.1, t.2, hv⟩, fun ⟨i, hi, hv⟩ ↦ ⟨⟨i, hi⟩, hv⟩⟩
  adj_mem_bag u v _ _ hadj := by
    obtain ⟨_, e, heu, hev⟩ := hadj
    have hinc : (Hypergraph.biUnion T.verts fun t ↦ (τ t).toHypergraph).Inc e u := by
      rw [hD.biUnion_eq]
      exact heu
    obtain ⟨t, ht, htu⟩ := hinc
    have he_mem : e ∈ (τ t).edgeSet := (τ t).edge_mem_of_inc htu
    have hends := (hD.le t ht).ends_eq e he_mem
    have htv : (τ t).Inc e v := by
      change v ∈ (τ t).ends e
      rw [← hends]
      exact hev
    exact ⟨⟨t, ht⟩, (τ t).vertex_mem_of_inc htu, (τ t).vertex_mem_of_inc htv⟩
  inter_subset_bag t₁ t₂ t₃ hp := by
    have hon : T.OnPath t₁.1 t₃.1 t₂.1 := (onTreePath_toSimpleGraph_iff T t₁ t₃ t₂).1 hp
    exact (hD.inter_le t₁.1 t₁.2 t₂.1 t₂.2 t₃.1 t₃.2 hon).vertexSet_subset

theorem widthLE_treeDecompOfGM04 {ι : Type*} {G : Hypergraph α β} {T : RootedTree ι}
    {τ : ι → RootedHypergraph α β} (hD : IsTreeDecomposition G.toRooted T τ)
    {w : ℕ} (hw : GM04.WidthLE T τ w) :
    (treeDecompOfGM04 hD).WidthLE w :=
  fun t ↦ hw t.1 t.2

/-! ## Step 4B: From `TreeDecomp` on `Fin m` to Graph Minors IV `IsTreeDecomposition` -/

section ToGM04

variable {G : Hypergraph α β} {m : ℕ} (D : TreeDecomp G.skeleton G.vertexSet (Fin m))

/-- Every edge of a graph `G` has all its ends (1 or 2 vertices) contained in some bag of `D`. -/
theorem exists_bag_superset_ends (hG : G.IsGraph) {e : β} (he : e ∈ G.edgeSet) :
    ∃ t : Fin m, G.ends e ⊆ D.bag t := by
  obtain ⟨⟨u, hu⟩, hcard⟩ := hG e he
  by_cases hsub : G.ends e ⊆ {u}
  · obtain ⟨t, hut⟩ := D.exists_mem_bag (G.vertex_mem_of_inc hu)
    exact ⟨t, fun v hv ↦ (Set.mem_singleton_iff.1 (hsub hv)) ▸ hut⟩
  · obtain ⟨v, hv, hvu⟩ := Set.not_subset.1 hsub
    rw [Set.mem_singleton_iff] at hvu
    have hadj : G.skeleton.Adj u v := ⟨Ne.symm hvu, e, hu, hv⟩
    obtain ⟨t, hut, hvt⟩ :=
      D.adj_mem_bag (G.vertex_mem_of_inc hu) (G.vertex_mem_of_inc hv) hadj
    refine ⟨t, fun z hz ↦ ?_⟩
    by_cases hzu : z = u
    · exact hzu ▸ hut
    · by_cases hzv : z = v
      · exact hzv ▸ hvt
      · exfalso
        have h3_sub : ({z, u, v} : Set α) ⊆ G.ends e := by
          intro w hw
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
          rcases hw with rfl | rfl | rfl
          · exact hz
          · exact hu
          · exact hv
        have hends_fin : (G.ends e).Finite :=
          G.vertexSet_finite.subset fun w hw ↦ G.vertex_mem_of_inc hw
        have hle := Set.ncard_le_ncard h3_sub hends_fin
        have hcard3 : ({z, u, v} : Set α).ncard = 3 := by
          rw [Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem, Set.ncard_singleton]
          · simp [Ne.symm hvu]
          · simp [hzu, hzv]
        omega

/-- Choice of a tree node `t : Fin m` whose bag contains the ends of `e`. -/
noncomputable def edgeBag (hG : G.IsGraph) (e : β) : Fin m :=
  open Classical in
  if he : e ∈ G.edgeSet then (exists_bag_superset_ends D hG he).choose
  else treeRootFin D.isTree

theorem ends_subset_bag_edgeBag (hG : G.IsGraph) {e : β} (he : e ∈ G.edgeSet) :
    G.ends e ⊆ D.bag (edgeBag D hG e) := by
  classical
  unfold edgeBag
  rw [dite_eq_left he]
  exact (exists_bag_superset_ends D hG he).choose_spec

/-- The hypergraph `(τ n)⁻` at node `n : ℕ` for the Graph Minors IV tree-decomposition built from
`D`. -/
noncomputable def gm04BagHypergraph (hG : G.IsGraph) (n : ℕ) : Hypergraph α β :=
  open Classical in
  if hn : n < m then
    { vertexSet := D.bag ⟨n, hn⟩
      edgeSet := {e ∈ G.edgeSet | edgeBag D hG e = ⟨n, hn⟩}
      Inc := fun e v ↦ e ∈ G.edgeSet ∧ edgeBag D hG e = ⟨n, hn⟩ ∧ G.Inc e v
      vertex_mem_of_inc := fun _ _ ⟨he, hbag, hinc⟩ ↦
        hbag ▸ ends_subset_bag_edgeBag D hG he hinc
      edge_mem_of_inc := fun _ _ ⟨he, hbag, _⟩ ↦ ⟨he, hbag⟩
      vertexSet_finite := D.bag_finite G.vertexSet_finite ⟨n, hn⟩
      edgeSet_finite := G.edgeSet_finite.subset fun _ h ↦ h.1 }
  else
    { vertexSet := ∅
      edgeSet := ∅
      Inc := fun _ _ ↦ False
      vertex_mem_of_inc := fun _ _ h ↦ h.elim
      edge_mem_of_inc := fun _ _ h ↦ h.elim
      vertexSet_finite := Set.finite_empty
      edgeSet_finite := Set.finite_empty }

/-- The march `π(τ(n))` at node `n : ℕ`: empty at the root `0` (and outside `Finset.range m`), and
an enumeration of `D.bag n ∩ D.bag (parent n)` for `0 < n < m`. -/
noncomputable def gm04BagRoots (n : ℕ) : List α :=
  open Classical in
  if hn : n < m then
    if n = 0 then []
    else
      ((D.bag_finite G.vertexSet_finite ⟨n, hn⟩).subset Set.inter_subset_left :
        (D.bag ⟨n, hn⟩ ∩ D.bag (parentFin D.isTree ⟨n, hn⟩)).Finite).toFinset.toList
  else []

/-- The rooted hypergraph `τ(n)` at node `n : ℕ`. -/
noncomputable def gm04Bags (hG : G.IsGraph) (n : ℕ) : RootedHypergraph α β where
  toHypergraph := gm04BagHypergraph D hG n
  roots := gm04BagRoots D n
  roots_nodup := by
    classical
    unfold gm04BagRoots
    split_ifs with hn h0
    · exact List.nodup_nil
    · exact Finset.nodup_toList _
    · exact List.nodup_nil
  roots_subset v hv := by
    classical
    unfold gm04BagRoots at hv
    unfold gm04BagHypergraph
    split_ifs at hv with hn h0
    · exact absurd hv List.not_mem_nil
    · rw [dite_eq_left hn]
      rw [Finset.mem_toList, Set.Finite.mem_toFinset] at hv
      exact hv.1
    · exact absurd hv List.not_mem_nil

theorem gm04Bags_vertexSet_of_lt (hG : G.IsGraph) {n : ℕ} (hn : n < m) :
    (gm04Bags D hG n).vertexSet = D.bag ⟨n, hn⟩ := by
  classical
  change (gm04BagHypergraph D hG n).vertexSet = D.bag ⟨n, hn⟩
  unfold gm04BagHypergraph
  rw [dite_eq_left hn]

theorem gm04Bags_edgeSet_of_lt (hG : G.IsGraph) {n : ℕ} (hn : n < m) :
    (gm04Bags D hG n).edgeSet = {e ∈ G.edgeSet | edgeBag D hG e = ⟨n, hn⟩} := by
  classical
  change (gm04BagHypergraph D hG n).edgeSet = _
  unfold gm04BagHypergraph
  rw [dite_eq_left hn]

theorem gm04Bags_inc_of_lt (hG : G.IsGraph) {n : ℕ} (hn : n < m) (e : β) (v : α) :
    (gm04Bags D hG n).Inc e v ↔ e ∈ G.edgeSet ∧ edgeBag D hG e = ⟨n, hn⟩ ∧ G.Inc e v := by
  classical
  change (gm04BagHypergraph D hG n).Inc e v ↔ _
  unfold gm04BagHypergraph
  rw [dite_eq_left hn]

theorem isTreeDecomposition_gm04Bags (hG : G.IsGraph) :
    IsTreeDecomposition G.toRooted (rootedTreeOfIsTree D.isTree) (gm04Bags D hG) where
  le t ht := by
    have ht_lt : t < m := Finset.mem_range.1 ht
    refine ⟨?_, ?_, ?_⟩
    · rw [gm04Bags_vertexSet_of_lt D hG ht_lt]
      exact D.bag_subset ⟨t, ht_lt⟩
    · rw [gm04Bags_edgeSet_of_lt D hG ht_lt]
      exact fun _ h ↦ h.1
    · intro e he
      rw [gm04Bags_edgeSet_of_lt D hG ht_lt] at he
      ext v
      change G.Inc e v ↔ (gm04Bags D hG t).Inc e v
      rw [gm04Bags_inc_of_lt D hG ht_lt]
      exact ⟨fun h ↦ ⟨he.1, he.2, h⟩, fun h ↦ h.2.2⟩
  biUnion_eq := by
    refine Hypergraph.ext ?_ ?_ ?_
    · change (⋃ t ∈ Finset.range m, (gm04Bags D hG t).vertexSet) = G.vertexSet
      ext v
      rw [Set.mem_iUnion₂, ← D.iUnion_bag, Set.mem_iUnion]
      constructor
      · rintro ⟨t, ht, hv⟩
        have ht_lt : t < m := Finset.mem_range.1 ht
        rw [gm04Bags_vertexSet_of_lt D hG ht_lt] at hv
        exact ⟨⟨t, ht_lt⟩, hv⟩
      · rintro ⟨⟨t, ht_lt⟩, hv⟩
        refine ⟨t, Finset.mem_range.2 ht_lt, ?_⟩
        rw [gm04Bags_vertexSet_of_lt D hG ht_lt]
        exact hv
    · change (⋃ t ∈ Finset.range m, (gm04Bags D hG t).edgeSet) = G.edgeSet
      ext e
      rw [Set.mem_iUnion₂]
      constructor
      · rintro ⟨t, ht, he⟩
        have ht_lt : t < m := Finset.mem_range.1 ht
        rw [gm04Bags_edgeSet_of_lt D hG ht_lt] at he
        exact he.1
      · intro he
        let t := edgeBag D hG e
        refine ⟨t.val, Finset.mem_range.2 t.isLt, ?_⟩
        rw [gm04Bags_edgeSet_of_lt D hG t.isLt]
        exact ⟨he, rfl⟩
    · funext e v
      apply propext
      change (∃ t ∈ Finset.range m, (gm04Bags D hG t).Inc e v) ↔ G.Inc e v
      constructor
      · rintro ⟨t, ht, hinc⟩
        have ht_lt : t < m := Finset.mem_range.1 ht
        rw [gm04Bags_inc_of_lt D hG ht_lt] at hinc
        exact hinc.2.2
      · intro hinc
        have he : e ∈ G.edgeSet := G.edge_mem_of_inc hinc
        let t := edgeBag D hG e
        refine ⟨t.val, Finset.mem_range.2 t.isLt, ?_⟩
        rw [gm04Bags_inc_of_lt D hG t.isLt]
        exact ⟨he, rfl, hinc⟩
  edgeSet_inter_eq t₁ ht₁ t₂ ht₂ hne := by
    have h₁ : t₁ < m := Finset.mem_range.1 ht₁
    have h₂ : t₂ < m := Finset.mem_range.1 ht₂
    change (gm04Bags D hG t₁).edgeSet ∩ (gm04Bags D hG t₂).edgeSet = ∅
    rw [gm04Bags_edgeSet_of_lt D hG h₁, gm04Bags_edgeSet_of_lt D hG h₂]
    ext e
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
    rintro ⟨_, he₁⟩ _ he₂
    exact hne (congrArg Fin.val (he₁.symm.trans he₂))
  inter_le t₁ ht₁ t₂ ht₂ t₃ ht₃ hon := by
    have h₁ : t₁ < m := Finset.mem_range.1 ht₁
    have h₂ : t₂ < m := Finset.mem_range.1 ht₂
    have h₃ : t₃ < m := Finset.mem_range.1 ht₃
    have hon_D : OnTreePath D.T ⟨t₁, h₁⟩ ⟨t₃, h₃⟩ ⟨t₂, h₂⟩ :=
      (onPath_rootedTreeOfIsTree_iff D.isTree ⟨t₁, ht₁⟩ ⟨t₃, ht₃⟩ ⟨t₂, ht₂⟩).1 hon
    refine ⟨?_, ?_, ?_⟩
    · change (gm04Bags D hG t₁).vertexSet ∩ (gm04Bags D hG t₃).vertexSet ⊆
        (gm04Bags D hG t₂).vertexSet
      rw [gm04Bags_vertexSet_of_lt D hG h₁, gm04Bags_vertexSet_of_lt D hG h₂,
        gm04Bags_vertexSet_of_lt D hG h₃]
      exact D.inter_subset_bag hon_D
    · change (gm04Bags D hG t₁).edgeSet ∩ (gm04Bags D hG t₃).edgeSet ⊆
        (gm04Bags D hG t₂).edgeSet
      rw [gm04Bags_edgeSet_of_lt D hG h₁, gm04Bags_edgeSet_of_lt D hG h₂,
        gm04Bags_edgeSet_of_lt D hG h₃]
      rintro e ⟨⟨he, he₁⟩, ⟨_, he₃⟩⟩
      have h13 : (⟨t₁, h₁⟩ : Fin m) = ⟨t₃, h₃⟩ := he₁.symm.trans he₃
      have h21 : (⟨t₂, h₂⟩ : Fin m) = ⟨t₃, h₃⟩ := (onTreePath_self D.T _ _).1 (h13 ▸ hon_D)
      exact ⟨he, he₃.trans h21.symm⟩
    · intro e he
      change e ∈ (gm04Bags D hG t₁).edgeSet ∩ (gm04Bags D hG t₃).edgeSet at he
      rw [gm04Bags_edgeSet_of_lt D hG h₁, gm04Bags_edgeSet_of_lt D hG h₃] at he
      have h13 : (⟨t₁, h₁⟩ : Fin m) = ⟨t₃, h₃⟩ := he.1.2.symm.trans he.2.2
      have h21 : (⟨t₂, h₂⟩ : Fin m) = ⟨t₃, h₃⟩ := (onTreePath_self D.T _ _).1 (h13 ▸ hon_D)
      ext v
      change (gm04Bags D hG t₂).Inc e v ↔ (gm04Bags D hG t₁).Inc e v ∧ (gm04Bags D hG t₃).Inc e v
      rw [gm04Bags_inc_of_lt D hG h₁, gm04Bags_inc_of_lt D hG h₂, gm04Bags_inc_of_lt D hG h₃]
      exact ⟨fun h ↦ ⟨⟨h.1, (h.2.1.trans h21).trans h13.symm, h.2.2⟩, ⟨h.1, h.2.1.trans h21,
        h.2.2⟩⟩,
        fun h ↦ ⟨h.1.1, h.2.2.1.trans h21.symm, h.1.2.2⟩⟩
  roots_root := by
    classical
    change gm04BagRoots D 0 = []
    unfold gm04BagRoots
    rw [dite_eq_left (pos_of_isTree D.isTree), ite_eq_left rfl]
  rootSet_edge f hf := by
    classical
    have hf_verts : f ∈ (rootedTreeOfIsTree D.isTree).verts :=
      mem_verts_of_mem_edges (rootedTreeOfIsTree D.isTree) hf
    have hf_ne_0 : f ≠ 0 :=
      ne_root_of_mem_edges (rootedTreeOfIsTree D.isTree) hf
    have hf_lt : f < m := Finset.mem_range.1 hf_verts
    have hpar_lt : (rootedTreeOfIsTree D.isTree).parent f < m :=
      Finset.mem_range.1 ((rootedTreeOfIsTree D.isTree).parent_mem f hf_verts)
    have hpar_eq : (⟨(rootedTreeOfIsTree D.isTree).parent f, hpar_lt⟩ : Fin m) =
        parentFin D.isTree ⟨f, hf_lt⟩ := by
      ext
      change (if hn : f < m then (parentFin D.isTree ⟨f, hn⟩).val else 0) = _
      rw [dite_eq_left hf_lt]
    change {v | v ∈ gm04BagRoots D f} =
      (gm04Bags D hG f).vertexSet ∩
        (gm04Bags D hG ((rootedTreeOfIsTree D.isTree).parent f)).vertexSet
    rw [gm04Bags_vertexSet_of_lt D hG hf_lt, gm04Bags_vertexSet_of_lt D hG hpar_lt, hpar_eq]
    unfold gm04BagRoots
    rw [dite_eq_left hf_lt, ite_eq_right hf_ne_0]
    ext v
    simp only [Set.mem_ofPred_eq, Finset.mem_toList, Set.Finite.mem_toFinset]

theorem widthLE_gm04Bags (hG : G.IsGraph) {w : ℕ} (hw : D.WidthLE w) :
    GM04.WidthLE (rootedTreeOfIsTree D.isTree) (gm04Bags D hG) w := by
  intro t ht
  have ht_lt : t < m := Finset.mem_range.1 ht
  rw [gm04Bags_vertexSet_of_lt D hG ht_lt]
  exact hw ⟨t, ht_lt⟩

end ToGM04

end

end GraphMinor.Thomas

namespace GraphMinor.GM04

open GraphMinor.Thomas

universe u v

public section

/-- Graph Minors IV, (5.1): Thomas's lemma. -/
theorem thomas_5_1 : ThomasStatement.{u, v} := by
  intro α β G hG w ⟨T₀, τ₀, hD₀, hw₀⟩
  let D₀ := treeDecompOfGM04 hD₀
  have hw_D₀ : D₀.WidthLE w := widthLE_treeDecompOfGM04 hD₀ hw₀
  obtain ⟨m, D, hlean, hw_D⟩ := theorem_3 G D₀ hw_D₀
  let T := rootedTreeOfIsTree D.isTree
  let τ := gm04Bags D hG
  have hD : IsTreeDecomposition G.toRooted T τ := isTreeDecomposition_gm04Bags D hG
  have hw : WidthLE T τ w := widthLE_gm04Bags D hG hw_D
  refine ⟨T, τ, hD, hw, ?_⟩
  intro t₁ ht₁ t₂ ht₂ hne k
  have h₁ : t₁ < m := Finset.mem_range.1 ht₁
  have h₂ : t₂ < m := Finset.mem_range.1 ht₂
  let u₁ : T.verts := ⟨t₁, ht₁⟩
  let u₂ : T.verts := ⟨t₂, ht₂⟩
  have hne_fin : equivFinOfIsTree D.isTree u₁ ≠ equivFinOfIsTree D.isTree u₂ :=
    fun h ↦ hne (congrArg Fin.val h)
  rcases D.thomas_of_isLean G.vertexSet_finite hlean hne_fin k with hpaths | ⟨i₁, i₂, he, hlt⟩
  · left
    rw [gm04Bags_vertexSet_of_lt D hG h₁, gm04Bags_vertexSet_of_lt D hG h₂]
    exact hpaths
  · right
    let s : T.verts := (equivFinOfIsTree D.isTree).symm i₁
    let s' : T.verts := (equivFinOfIsTree D.isTree).symm i₂
    have he_T : OnTreePathEdge (toSimpleGraph T) u₁ u₂ s s' := by
      apply onTreePathEdge_of_isTree_imp D.isTree
      rwa [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    obtain ⟨f, hf_edges, hf_on, h_orient⟩ := exists_onPathEdge_of_onTreePathEdge T he_T
    refine ⟨f.1, hf_on, ?_⟩
    rw [edgeOrder_eq_ncard_inter T hD hf_edges]
    have hf_lt : f.1 < m := Finset.mem_range.1 f.2
    have hpar_lt : T.parent f.1 < m := Finset.mem_range.1 (T.parent_mem f.1 f.2)
    rw [gm04Bags_vertexSet_of_lt D hG hf_lt, gm04Bags_vertexSet_of_lt D hG hpar_lt]
    rcases h_orient with ⟨hs_eq, hs'_eq⟩ | ⟨hs'_eq, hs_eq⟩
    · have hi₁ : (⟨f.1, hf_lt⟩ : Fin m) = i₁ := by
        have := congrArg (equivFinOfIsTree D.isTree) hs_eq.symm
        rwa [Equiv.apply_symm_apply] at this
      have hi₂ : (⟨T.parent f.1, hpar_lt⟩ : Fin m) = i₂ := by
        have := congrArg (equivFinOfIsTree D.isTree) hs'_eq.symm
        rwa [Equiv.apply_symm_apply] at this
      rwa [hi₁, hi₂]
    · have hi₂ : (⟨f.1, hf_lt⟩ : Fin m) = i₂ := by
        have := congrArg (equivFinOfIsTree D.isTree) hs'_eq.symm
        rwa [Equiv.apply_symm_apply] at this
      have hi₁ : (⟨T.parent f.1, hpar_lt⟩ : Fin m) = i₁ := by
        have := congrArg (equivFinOfIsTree D.isTree) hs_eq.symm
        rwa [Equiv.apply_symm_apply] at this
      rw [hi₂, hi₁, Set.inter_comm]
      exact hlt

end

end GraphMinor.GM04
