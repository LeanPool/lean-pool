/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM10.BranchWidth

/-!
# Tree-Width Basics and Branch-to-Tree Conversion: Graph Minors X, Section 5 (Part 1)

This file develops the basic theory of tree-decompositions and proves the second inequality of
**(5.1)** of Robertson and Seymour,
*Graph Minors. X. Obstructions to tree-decomposition*, J. Combin. Theory Ser. B 52 (1991) 153–190
(pages 168–170):
- Basic properties of `OnTreePath` and convexity of `treeComponent` with respect to paths in trees.
- Basic properties of `IsTreeDecomposition`, `treeDecompWidthPlusOne`, and `treeWidthPlusOne`.
- Attaching a pendant leaf (`attachLeaf`) to a tree and reducing `treeWidthPlusOne` to hypergraphs
  without isolated vertices (`isoSet`).
- Constructing a tree-decomposition from a branch-decomposition and proving the upper bound
  `2 * treeWidthPlusOne G ≤ 3 * max (branchWidth G) (maxEdgeSize G)` when `1 ≤ maxEdgeSize G`.
-/

public section

namespace GraphMinor.GM10

open SimpleGraph Hypergraph

variable {α β ι ι' : Type*}

/-! ## Basic properties of `OnTreePath` and `treeComponent` -/

/-- The start vertex `t₁` lies on every path from `t₁` to `t₂`. -/
theorem onTreePath_refl_left (T : SimpleGraph ι) (t₁ t₂ : ι) : OnTreePath T t₁ t₂ t₁ :=
  fun p _ ↦ p.start_mem_support

/-- The end vertex `t₂` lies on every path from `t₁` to `t₂`. -/
theorem onTreePath_refl_right (T : SimpleGraph ι) (t₁ t₂ : ι) : OnTreePath T t₁ t₂ t₂ :=
  fun p _ ↦ p.end_mem_support

/-- `OnTreePath T t₁ t₂ t` is symmetric in `t₁` and `t₂`. -/
theorem onTreePath_comm {T : SimpleGraph ι} {t₁ t₂ t : ι} :
    OnTreePath T t₁ t₂ t ↔ OnTreePath T t₂ t₁ t := by
  constructor <;> intro h p hp
  · have hm := h p.reverse ((Walk.isPath_reverse_iff p).2 hp)
    rwa [Walk.support_reverse, List.mem_reverse] at hm
  · have hm := h p.reverse ((Walk.isPath_reverse_iff p).2 hp)
    rwa [Walk.support_reverse, List.mem_reverse] at hm

/-- Only `t` lies on the path from `t` to `t`. -/
theorem onTreePath_self_iff {T : SimpleGraph ι} {t t' : ι} :
    OnTreePath T t t t' ↔ t' = t := by
  constructor
  · intro h
    have hm := h Walk.nil Walk.IsPath.nil
    simpa using hm
  · rintro rfl
    exact onTreePath_refl_left T t' t'

/-- If `OnTreePath T t₁ t₂ t`, then `t` belongs to the support of every walk from `t₁` to `t₂`. -/
theorem mem_support_of_onTreePath {T : SimpleGraph ι} {t₁ t₂ t : ι}
    (h : OnTreePath T t₁ t₂ t) (w : T.Walk t₁ t₂) : t ∈ w.support := by
  classical
  exact Walk.support_bypass_subset_support w (h w.bypass (Walk.bypass_isPath w))

/-- In a tree `T`, `OnTreePath T t₁ t₂ t` holds if and only if `t ∈ p.support` for a given path `p`
from `t₁` to `t₂`. -/
theorem onTreePath_iff_of_isPath {T : SimpleGraph ι} (hT : T.IsTree)
    {t₁ t₂ t : ι} {p : T.Walk t₁ t₂} (hp : p.IsPath) :
    OnTreePath T t₁ t₂ t ↔ t ∈ p.support := by
  constructor
  · intro h
    exact h p hp
  · intro ht q hq
    have hqp : q = p :=
      congrArg Subtype.val ((hT.isAcyclic.subsingleton_path t₁ t₂).elim ⟨q, hq⟩ ⟨p, hp⟩)
    rwa [hqp]

/-- If `v` has at most one neighbor in `G`, then any path containing `v` has `v` as an endpoint. -/
theorem eq_fst_or_eq_snd_of_mem_support_of_unique_adj {G : SimpleGraph ι} {v : ι}
    (huniq : ∀ w₁ w₂, G.Adj v w₁ → G.Adj v w₂ → w₁ = w₂)
    {a b : ι} {p : G.Walk a b} (hp : p.IsPath) (hv : v ∈ p.support) :
    v = a ∨ v = b := by
  induction p with
  | nil =>
    left
    simpa using hv
  | @cons a x b h₁ q ih =>
    rw [Walk.cons_isPath_iff] at hp
    rw [Walk.support_cons, List.mem_cons] at hv
    rcases hv with rfl | hv_q
    · exact Or.inl rfl
    · rcases ih hp.1 hv_q with rfl | rfl
      · cases q with
        | nil => exact Or.inr rfl
        | @cons _ y _ h₂ r =>
          have hay : a = y := huniq a y h₁.symm h₂
          subst hay
          exact (hp.2 (Walk.support_subset_support_cons r h₂ r.start_mem_support)).elim
      · exact Or.inr rfl

/-- In a connected graph `T`, if `v` has at most one neighbor and `OnTreePath T a b v`, then
`v = a ∨ v = b`. -/
theorem eq_or_eq_of_onTreePath_of_unique_adj {T : SimpleGraph ι} (hconn : T.Connected) {v : ι}
    (huniq : ∀ w₁ w₂, T.Adj v w₁ → T.Adj v w₂ → w₁ = w₂)
    {a b : ι} (h : OnTreePath T a b v) : v = a ∨ v = b := by
  obtain ⟨p, hp⟩ := hconn.exists_isPath a b
  exact eq_fst_or_eq_snd_of_mem_support_of_unique_adj huniq hp (h p hp)

/-- Any component `treeComponent T u e` of `T \ e` is convex with respect to `OnTreePath`. -/
theorem mem_treeComponent_of_onTreePath {T : SimpleGraph ι} {u : ι} {e : Sym2 ι}
    {a b x : ι} (ha : a ∈ treeComponent T u e) (hb : b ∈ treeComponent T u e)
    (h : OnTreePath T a b x) : x ∈ treeComponent T u e := by
  classical
  have hab : (T.deleteEdges {e}).Reachable a b := ha.symm.trans hb
  obtain ⟨w⟩ := hab
  have hx_map : x ∈ (w.mapLe (SimpleGraph.deleteEdges_le _)).support :=
    mem_support_of_onTreePath h _
  rw [Walk.support_map, List.mem_map] at hx_map
  obtain ⟨z, hz, rfl⟩ := hx_map
  exact ha.trans (Walk.reachable (w.takeUntil z hz))

/-- If `x ∈ treeComponent T u s(u, w)` and `OnTreePath T a b x`, then at least one of `a, b` lies
in `treeComponent T u s(u, w)`. -/
theorem mem_treeComponent_left_or_right_of_onTreePath {T : SimpleGraph ι} (hT : T.IsTree)
    {u w a b x : ι} (hadj : T.Adj u w)
    (hx : x ∈ treeComponent T u s(u, w)) (h : OnTreePath T a b x) :
    a ∈ treeComponent T u s(u, w) ∨ b ∈ treeComponent T u s(u, w) := by
  by_contra! hnot
  have ha' : a ∈ treeComponent T w s(w, u) := (notMem_treeComponent_iff hT hadj).1 hnot.1
  have hb' : b ∈ treeComponent T w s(w, u) := (notMem_treeComponent_iff hT hadj).1 hnot.2
  have hx' : x ∈ treeComponent T w s(w, u) := mem_treeComponent_of_onTreePath ha' hb' h
  exact (notMem_treeComponent_iff hT hadj).2 hx' hx

/-- If `a ∈ treeComponent T u s(u, w)` and `b ∈ treeComponent T w s(w, u)`, then `u` lies on the
path of `T` between `a` and `b`. -/
theorem onTreePath_of_mem_treeComponent {T : SimpleGraph ι} (hT : T.IsTree)
    {u w a b : ι} (hadj : T.Adj u w)
    (ha : a ∈ treeComponent T u s(u, w)) (hb : b ∈ treeComponent T w s(w, u)) :
    OnTreePath T a b u := by
  intro p hp
  have hnot_reach : ¬ (T.deleteEdges {s(u, w)}).Reachable a b :=
    (not_reachable_deleteEdges_iff_treeComponent hT hadj).2 (Or.inl ⟨ha, hb⟩)
  have he_mem : s(u, w) ∈ p.edges := by
    by_contra he_not
    apply hnot_reach
    exact ⟨p.toDeleteEdges {s(u, w)} fun e he hmem ↦ by
      rw [Set.mem_singleton_iff] at hmem
      exact he_not (hmem ▸ he)⟩
  exact Walk.fst_mem_support_of_mem_edges p he_mem

/-- For any subset `S : Set ι`, the set of vertices `x` lying on the path between two elements of
`S` is convex with respect to `OnTreePath`. -/
theorem isConvex_exists_onTreePath {T : SimpleGraph ι} (hT : T.IsTree) {S : Set ι}
    {a b c : ι}
    (ha : ∃ t₁ ∈ S, ∃ t₂ ∈ S, OnTreePath T t₁ t₂ a)
    (hb : ∃ t₁ ∈ S, ∃ t₂ ∈ S, OnTreePath T t₁ t₂ b)
    (hc : OnTreePath T a b c) :
    ∃ t₁ ∈ S, ∃ t₂ ∈ S, OnTreePath T t₁ t₂ c := by
  by_cases hca : c = a
  · subst hca; exact ha
  · obtain ⟨p, hp⟩ := hT.connected.exists_isPath c a
    cases p with
    | nil => exact (hca rfl).elim
    | @cons _ w _ hadj q =>
      obtain ⟨hq, hc_not_q⟩ := (Walk.cons_isPath_iff hadj q).1 hp
      have ha_comp : a ∈ treeComponent T w s(w, c) :=
        (mem_treeComponent_iff_notMem_support hT hadj.symm hq).2 hc_not_q
      have hb_comp : b ∈ treeComponent T c s(c, w) := by
        rw [← notMem_treeComponent_iff hT hadj.symm]
        intro hb_w
        have hc_w : c ∈ treeComponent T w s(w, c) :=
          mem_treeComponent_of_onTreePath ha_comp hb_w hc
        exact (notMem_treeComponent_iff hT hadj).2 hc_w Reachable.rfl
      obtain ⟨t₁, ht₁S, t₂, ht₂S, ht12⟩ := ha
      obtain ⟨t₃, ht₃S, t₄, ht₄S, ht34⟩ := hb
      obtain ⟨s₁, hs₁S, hs₁_w⟩ : ∃ s₁ ∈ S, s₁ ∈ treeComponent T w s(w, c) := by
        rcases mem_treeComponent_left_or_right_of_onTreePath hT hadj.symm ha_comp ht12 with h1 | h2
        · exact ⟨t₁, ht₁S, h1⟩
        · exact ⟨t₂, ht₂S, h2⟩
      obtain ⟨s₂, hs₂S, hs₂_c⟩ : ∃ s₂ ∈ S, s₂ ∈ treeComponent T c s(c, w) := by
        rcases mem_treeComponent_left_or_right_of_onTreePath hT hadj hb_comp ht34 with h3 | h4
        · exact ⟨t₃, ht₃S, h3⟩
        · exact ⟨t₄, ht₄S, h4⟩
      exact ⟨s₂, hs₂S, s₁, hs₁S, onTreePath_of_mem_treeComponent hT hadj hs₂_c hs₁_w⟩

/-! ## Basic properties of `IsTreeDecomposition` and `treeWidthPlusOne` -/

/-- The index type of a tree-decomposition is nonempty. -/
theorem IsTreeDecomposition.nonempty [Fintype ι] {G : Hypergraph α β}
    {T : SimpleGraph ι} {τ : ι → Hypergraph α β} (h : IsTreeDecomposition G T τ) :
    Nonempty ι :=
  h.isTree.connected.nonempty

/-- A vertex `v` belongs to `V(G)` if and only if `v ∈ V(τ(t))` for some `t : ι`. -/
theorem IsTreeDecomposition.vertex_mem_iff [Fintype ι] {G : Hypergraph α β}
    {T : SimpleGraph ι} {τ : ι → Hypergraph α β} (h : IsTreeDecomposition G T τ) {v : α} :
    v ∈ G.vertexSet ↔ ∃ t : ι, v ∈ (τ t).vertexSet := by
  rw [← h.biUnion_eq]
  simp [Hypergraph.biUnion]

/-- An edge `e` belongs to `E(G)` if and only if `e ∈ E(τ(t))` for some `t : ι`. -/
theorem IsTreeDecomposition.edge_mem_iff [Fintype ι] {G : Hypergraph α β}
    {T : SimpleGraph ι} {τ : ι → Hypergraph α β} (h : IsTreeDecomposition G T τ) {e : β} :
    e ∈ G.edgeSet ↔ ∃ t : ι, e ∈ (τ t).edgeSet := by
  rw [← h.biUnion_eq]
  simp [Hypergraph.biUnion]

/-- `G.Inc e v` holds if and only if `(τ t).Inc e v` for some `t : ι`. -/
theorem IsTreeDecomposition.inc_iff [Fintype ι] {G : Hypergraph α β}
    {T : SimpleGraph ι} {τ : ι → Hypergraph α β} (h : IsTreeDecomposition G T τ) {e : β} {v : α} :
    G.Inc e v ↔ ∃ t : ι, (τ t).Inc e v := by
  rw [← h.biUnion_eq]
  simp [Hypergraph.biUnion]

/-- Each edge `e ∈ E(G)` belongs to `E(τ(t))` for at most one `t : ι`. -/
theorem IsTreeDecomposition.eq_of_edge_mem [Fintype ι] {G : Hypergraph α β}
    {T : SimpleGraph ι} {τ : ι → Hypergraph α β} (h : IsTreeDecomposition G T τ)
    {t t' : ι} {e : β} (ht : e ∈ (τ t).edgeSet) (ht' : e ∈ (τ t').edgeSet) :
    t = t' := by
  by_contra hne
  have hemp := h.edgeSet_inter_eq hne
  have hmem : e ∈ (τ t ∩ τ t').edgeSet := ⟨ht, ht'⟩
  rw [hemp] at hmem
  exact hmem

/-- If `e ∈ E(τ(t))`, then `(τ t).Inc e v ↔ G.Inc e v`, and `G.ends e ⊆ V(τ(t))`. -/
theorem IsTreeDecomposition.inc_iff_of_edge_mem [Fintype ι] {G : Hypergraph α β}
    {T : SimpleGraph ι} {τ : ι → Hypergraph α β} (h : IsTreeDecomposition G T τ)
    {t : ι} {e : β} (ht : e ∈ (τ t).edgeSet) {v : α} :
    (τ t).Inc e v ↔ G.Inc e v :=
  inc_iff_of_le (h.le t) ht

/-- If `e ∈ E(τ(t))`, then all ends of `e` in `G` belong to `V(τ(t))`. -/
theorem IsTreeDecomposition.ends_subset_vertexSet_of_edge_mem [Fintype ι] {G : Hypergraph α β}
    {T : SimpleGraph ι} {τ : ι → Hypergraph α β} (h : IsTreeDecomposition G T τ)
    {t : ι} {e : β} (ht : e ∈ (τ t).edgeSet) :
    G.ends e ⊆ (τ t).vertexSet :=
  fun _ hv ↦ (τ t).vertex_mem_of_inc ((h.inc_iff_of_edge_mem ht).2 hv)

/-- For every `t : ι`, `(τ t).vertexSet.ncard ≤ treeDecompWidthPlusOne τ`. -/
theorem ncard_vertexSet_le_treeDecompWidthPlusOne [Finite ι]
    (τ : ι → Hypergraph α β) (t : ι) :
    (τ t).vertexSet.ncard ≤ treeDecompWidthPlusOne τ :=
  le_csSup (Set.finite_range _).bddAbove ⟨t, rfl⟩

/-- `treeDecompWidthPlusOne τ ≤ k` if and only if `(τ t).vertexSet.ncard ≤ k` for all `t : ι`. -/
theorem treeDecompWidthPlusOne_le_iff [Finite ι] [Nonempty ι]
    {τ : ι → Hypergraph α β} {k : ℕ} :
    treeDecompWidthPlusOne τ ≤ k ↔ ∀ t : ι, (τ t).vertexSet.ncard ≤ k := by
  constructor
  · intro hk t
    exact (ncard_vertexSet_le_treeDecompWidthPlusOne τ t).trans hk
  · intro h
    refine csSup_le (Set.range_nonempty _) ?_
    rintro _ ⟨t, rfl⟩
    exact h t

/-- The trivial 1-vertex tree-decomposition `(⊥ : SimpleGraph (Fin 1), fun _ ↦ G)` of `G`. -/
theorem isTreeDecomposition_trivial (G : Hypergraph α β) :
    IsTreeDecomposition G (⊥ : SimpleGraph (Fin 1)) (fun _ ↦ G) where
  isTree := by
    refine ⟨Connected.mk fun u v ↦ Subsingleton.elim u v ▸ Reachable.rfl, ?_⟩
    intro v p hp
    cases p with
    | nil => exact hp.ne_nil rfl
    | cons hadj _ => exact hadj
  le _ := le_rfl
  biUnion_eq := by
    ext x <;> simp [Hypergraph.biUnion]
  edgeSet_inter_eq t₁ t₂ hne := (hne (Subsingleton.elim t₁ t₂)).elim
  inter_le _ _ _ _ := inter_le_left le_rfl le_rfl

/-- The trivial 1-vertex tree-decomposition of `G` has `treeDecompWidthPlusOne = |V(G)|`. -/
theorem treeDecompWidthPlusOne_trivial (G : Hypergraph α β) :
    treeDecompWidthPlusOne (fun _ : Fin 1 ↦ G) = G.vertexSet.ncard := by
  refine le_antisymm ?_
    (ncard_vertexSet_le_treeDecompWidthPlusOne (fun _ : Fin 1 ↦ G) (0 : Fin 1))
  rw [treeDecompWidthPlusOne_le_iff]
  intro _
  exact le_rfl

/-- Every hypergraph `G` has a tree-decomposition `(T, τ)` achieving `treeWidthPlusOne G`. -/
theorem exists_treeDecomposition_eq_treeWidthPlusOne (G : Hypergraph α β) :
    ∃ (ι : Type) (_ : Fintype ι) (T : SimpleGraph ι) (τ : ι → Hypergraph α β),
      IsTreeDecomposition G T τ ∧ treeDecompWidthPlusOne τ = treeWidthPlusOne G := by
  let S : Set ℕ := {w : ℕ | ∃ (ι : Type) (_ : Fintype ι) (T : SimpleGraph ι)
    (τ : ι → Hypergraph α β), IsTreeDecomposition G T τ ∧ treeDecompWidthPlusOne τ = w}
  have hne : S.Nonempty := ⟨G.vertexSet.ncard, Fin 1, inferInstance, ⊥, fun _ ↦ G,
    isTreeDecomposition_trivial G, treeDecompWidthPlusOne_trivial G⟩
  exact Nat.sInf_mem hne

/-- `treeWidthPlusOne G ≤ G.vertexSet.ncard` for every hypergraph `G`. -/
theorem treeWidthPlusOne_le_ncard_vertexSet (G : Hypergraph α β) :
    treeWidthPlusOne G ≤ G.vertexSet.ncard := by
  simpa [treeDecompWidthPlusOne_trivial] using
    treeWidthPlusOne_le_of_isTreeDecomposition (isTreeDecomposition_trivial G)

/-- For any tree-decomposition `(T, τ)` of `G`, `maxEdgeSize G ≤ treeDecompWidthPlusOne τ`. -/
theorem maxEdgeSize_le_treeDecompWidthPlusOne [Fintype ι] {G : Hypergraph α β}
    {T : SimpleGraph ι} {τ : ι → Hypergraph α β} (h : IsTreeDecomposition G T τ) :
    maxEdgeSize G ≤ treeDecompWidthPlusOne τ := by
  rw [maxEdgeSize_le_iff]
  intro e he
  obtain ⟨t, ht⟩ := h.edge_mem_iff.1 he
  have hsub := h.ends_subset_vertexSet_of_edge_mem ht
  exact (Set.ncard_le_ncard hsub (τ t).vertexSet_finite).trans
    (ncard_vertexSet_le_treeDecompWidthPlusOne τ t)

/-- `maxEdgeSize G ≤ treeWidthPlusOne G` (`γ(G) ≤ ω(G) + 1`) for every hypergraph `G`. -/
theorem maxEdgeSize_le_treeWidthPlusOne (G : Hypergraph α β) :
    maxEdgeSize G ≤ treeWidthPlusOne G := by
  obtain ⟨ι, _, T, τ, h, hw⟩ := exists_treeDecomposition_eq_treeWidthPlusOne G
  rw [← hw]
  exact maxEdgeSize_le_treeDecompWidthPlusOne h

/-- `treeWidthPlusOne G = 0` (`ω(G) = -1`) if and only if `G.vertexSet = ∅`. -/
theorem treeWidthPlusOne_eq_zero_iff {G : Hypergraph α β} :
    treeWidthPlusOne G = 0 ↔ G.vertexSet = ∅ := by
  constructor
  · intro h0
    obtain ⟨ι, _, T, τ, h, hw⟩ := exists_treeDecomposition_eq_treeWidthPlusOne G
    rw [h0] at hw
    ext v
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hv
    obtain ⟨t, ht⟩ := h.vertex_mem_iff.1 hv
    have hle := (ncard_vertexSet_le_treeDecompWidthPlusOne τ t).trans hw.le
    have hemp : (τ t).vertexSet = ∅ :=
      (Set.ncard_eq_zero (τ t).vertexSet_finite).1 (Nat.le_zero.1 hle)
    rw [hemp] at ht
    exact ht
  · intro hemp
    have hle := treeWidthPlusOne_le_ncard_vertexSet G
    rw [hemp, Set.ncard_empty, Nat.le_zero] at hle
    exact hle

/-- If `G.vertexSet` is nonempty, then `1 ≤ treeWidthPlusOne G` (`0 ≤ ω(G)`). -/
theorem one_le_treeWidthPlusOne_of_nonempty {G : Hypergraph α β} (h : G.vertexSet.Nonempty) :
    1 ≤ treeWidthPlusOne G := by
  have hne : treeWidthPlusOne G ≠ 0 := by
    rw [ne_eq, treeWidthPlusOne_eq_zero_iff]
    exact h.ne_empty
  omega

/-! ## Attaching a pendant leaf to a tree (`attachLeaf`) -/

/-- Attach a new leaf `none : Option ι` adjacent only to `some t₀` in `T : SimpleGraph ι`. -/
@[expose] def attachLeaf (T : SimpleGraph ι) (t₀ : ι) : SimpleGraph (Option ι) where
  Adj a b :=
    match a, b with
    | some x, some y => T.Adj x y
    | some x, none => x = t₀
    | none, some y => y = t₀
    | none, none => False
  symm := ⟨by
    intro a b h
    cases a <;> cases b
    · exact h
    · exact h
    · exact h
    · exact h.symm⟩
  loopless := ⟨by rintro (_ | x) <;> simp⟩

instance [DecidableEq ι] (T : SimpleGraph ι) [DecidableRel T.Adj] (t₀ : ι) :
    DecidableRel (attachLeaf T t₀).Adj := fun a b ↦
  match a, b with
  | some x, some y => inferInstanceAs (Decidable (T.Adj x y))
  | some x, none => inferInstanceAs (Decidable (x = t₀))
  | none, some y => inferInstanceAs (Decidable (y = t₀))
  | none, none => isFalse id

/-- The embedding of `T` into `attachLeaf T t₀` via `Option.some`. -/
@[expose] def attachLeafSomeHom (T : SimpleGraph ι) (t₀ : ι) : T →g attachLeaf T t₀ where
  toFun := Option.some
  map_rel' h := h

/-- The retraction `Option ι → ι` sending `some x` to `x` and `none` to `t₀`. -/
@[expose] def projAttach (t₀ : ι) : Option ι → ι
  | some x => x
  | none => t₀

/-- `none` has `some t₀` as its unique neighbor in `attachLeaf T t₀`. -/
theorem adj_attachLeaf_none_iff {T : SimpleGraph ι} {t₀ : ι} {w : Option ι} :
    (attachLeaf T t₀).Adj none w ↔ w = some t₀ := by
  cases w <;> simp [attachLeaf]

/-- Attaching a leaf to a tree yields a tree. -/
theorem isTree_attachLeaf [Finite ι] {T : SimpleGraph ι} (hT : T.IsTree) (t₀ : ι) :
    (attachLeaf T t₀).IsTree := by
  classical
  let := Fintype.ofFinite ι
  have hconn : (attachLeaf T t₀).Connected := by
    refine Connected.mk fun a b ↦ ?_
    have hreach : ∀ x : Option ι, (attachLeaf T t₀).Reachable (some t₀) x := by
      rintro (_ | x)
      · exact Adj.reachable (show (attachLeaf T t₀).Adj (some t₀) none from rfl)
      · obtain ⟨w⟩ := hT.connected t₀ x
        exact ⟨w.map (attachLeafSomeHom T t₀)⟩
    exact (hreach a).symm.trans (hreach b)
  let equivEdge : (attachLeaf T t₀).edgeSet ≃ Option T.edgeSet :=
    { toFun := fun e ↦
        if h : none ∈ e.1 then none
        else some ⟨e.1.map (fun x ↦ x.getD t₀), by
          rcases e with ⟨e, he⟩
          induction e using Sym2.ind with | _ a b =>
          cases a with
          | none => exact (h (Sym2.mem_mk_left _ _)).elim
          | some x =>
            cases b with
            | none => exact (h (Sym2.mem_mk_right _ _)).elim
            | some y => exact he⟩
      invFun := fun o ↦
        match o with
        | none => ⟨s(some t₀, none), show (attachLeaf T t₀).Adj (some t₀) none from rfl⟩
        | some e => ⟨e.1.map Option.some, by
            rcases e with ⟨e, he⟩
            induction e using Sym2.ind with | _ x y =>
            exact he⟩
      left_inv := by
        rintro ⟨e, he⟩
        ext
        induction e using Sym2.ind with | _ a b =>
        cases a with
        | none =>
          cases b with
          | none => exact he.elim
          | some y =>
            have hy : y = t₀ := he
            subst hy
            simp [Sym2.eq_swap]
        | some x =>
          cases b with
          | none =>
            have hx : x = t₀ := he
            subst hx
            simp
          | some y =>
            have hnot : ¬ (none : Option ι) ∈ s(some x, some y) := by simp
            simp [hnot]
      right_inv := by
        rintro (_ | ⟨e, he⟩)
        · simp
        · ext
          induction e using Sym2.ind with | _ x y =>
          have hnot : ¬ (none : Option ι) ∈ s(some x, some y) := by simp
          simp [hnot] }
  have hedge : Nat.card (attachLeaf T t₀).edgeSet = Nat.card T.edgeSet + 1 := by
    rw [Nat.card_congr equivEdge, Nat.card_eq_fintype_card, Fintype.card_option,
      ← Nat.card_eq_fintype_card]
  have hcardT : Nat.card T.edgeSet + 1 = Nat.card ι :=
    (isTree_iff_connected_and_card.1 hT).2
  refine isTree_iff_connected_and_card.2 ⟨hconn, ?_⟩
  rw [hedge, hcardT, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_option]

/-- A short walk in `attachLeaf T t₀` from `a` to `some (projAttach t₀ a)` whose support maps into
`{projAttach t₀ a}`. -/
@[expose] def toSomeWalk (T : SimpleGraph ι) (t₀ : ι) :
    ∀ a : Option ι, (attachLeaf T t₀).Walk a (some (projAttach t₀ a))
  | some _ => Walk.nil
  | none => Walk.cons (show (attachLeaf T t₀).Adj none (some t₀) from rfl) Walk.nil

theorem projAttach_mem_toSomeWalk {T : SimpleGraph ι} {t₀ : ι} {a z : Option ι}
    (hz : z ∈ (toSomeWalk T t₀ a).support) :
    projAttach t₀ z = projAttach t₀ a := by
  cases a with
  | none =>
    dsimp only [toSomeWalk, projAttach] at hz ⊢
    rw [Walk.support_cons, Walk.support_nil, List.mem_cons, List.mem_singleton] at hz
    rcases hz with rfl | rfl <;> rfl
  | some x =>
    dsimp only [toSomeWalk, projAttach] at hz ⊢
    rw [Walk.support_nil, List.mem_singleton] at hz
    subst hz
    rfl

/-- If `some t` lies on the path in `attachLeaf T t₀` between `a` and `b`, then `t` lies on the
path in `T` between `projAttach t₀ a` and `projAttach t₀ b`. -/
theorem onTreePath_projAttach_of_some {T : SimpleGraph ι} {t₀ : ι} {a b : Option ι} {t : ι}
    (h : OnTreePath (attachLeaf T t₀) a b (some t)) :
    OnTreePath T (projAttach t₀ a) (projAttach t₀ b) t := by
  intro p hp
  let w : (attachLeaf T t₀).Walk a b :=
    (toSomeWalk T t₀ a).append
      ((p.map (attachLeafSomeHom T t₀)).append (toSomeWalk T t₀ b).reverse)
  have hm : some t ∈ w.support := mem_support_of_onTreePath h w
  rcases (Walk.mem_support_append_iff _ _).1 hm with h1 | h2
  · have heq := projAttach_mem_toSomeWalk h1
    change t = projAttach t₀ a at heq
    rw [heq]
    exact p.start_mem_support
  · rcases (Walk.mem_support_append_iff _ _).1 h2 with h3 | h4
    · have h3' : some t ∈ List.map (attachLeafSomeHom T t₀) p.support :=
        Walk.support_map (attachLeafSomeHom T t₀) p ▸ h3
      obtain ⟨z, hz, hzeq⟩ := List.mem_map.1 h3'
      exact Option.some.inj hzeq ▸ hz
    · have h4' : some t ∈ (toSomeWalk T t₀ b).support.reverse :=
        Walk.support_reverse (toSomeWalk T t₀ b) ▸ h4
      have heq := projAttach_mem_toSomeWalk (List.mem_reverse.1 h4')
      change t = projAttach t₀ b at heq
      rw [heq]
      exact p.end_mem_support

/-- `none` is always a leaf of `attachLeaf T t₀`. -/
theorem isLeaf_attachLeaf_none [Fintype ι] (T : SimpleGraph ι) (t₀ : ι) :
    IsLeaf (attachLeaf T t₀) none := by
  classical
  unfold IsLeaf
  rw [← ncard_neighborSet]
  have hset : (attachLeaf T t₀).neighborSet none = {some t₀} := by
    ext w
    simp [mem_neighborSet, adj_attachLeaf_none_iff]
  rw [hset, Set.ncard_singleton]

/-- For `x ≠ t₀`, `some x` is a leaf of `attachLeaf T t₀` if and only if `x` is a leaf of `T`. -/
theorem isLeaf_attachLeaf_some_iff [Fintype ι] {T : SimpleGraph ι} {t₀ x : ι} (hne : x ≠ t₀) :
    IsLeaf (attachLeaf T t₀) (some x) ↔ IsLeaf T x := by
  classical
  unfold IsLeaf
  rw [← ncard_neighborSet, ← ncard_neighborSet]
  have hset : (attachLeaf T t₀).neighborSet (some x) = Option.some '' T.neighborSet x := by
    ext w
    cases w with
    | none =>
      simp [mem_neighborSet, attachLeaf, hne]
    | some y =>
      simp [mem_neighborSet, attachLeaf]
  rw [hset, Set.ncard_image_of_injective _ (Option.some_injective ι)]

/-! ## Isolated vertices (`isoSet`) and `deleteVertices` -/

/-- The set of isolated vertices of `G` (vertices incident with no edge of `G`). -/
@[expose] def isoSet (G : Hypergraph α β) : Set α :=
  {v ∈ G.vertexSet | ∀ e, ¬ G.Inc e v}

theorem isoSet_finite (G : Hypergraph α β) : (isoSet G).Finite :=
  G.vertexSet_finite.subset fun _ h ↦ h.1

theorem deleteVertices_deleteVertices_singleton (G : Hypergraph α β) (X : Set α) (v : α) :
    (G.deleteVertices X).deleteVertices {v} = G.deleteVertices (insert v X) := by
  ext x <;> simp [Hypergraph.deleteVertices] <;> tauto

/-- Deleting a set `X` of isolated vertices does not change `edgeSet` or `Inc`. -/
theorem deleteVertices_edgeSet_of_isolated {G : Hypergraph α β} {X : Set α}
    (hX : ∀ v ∈ X, ∀ e, ¬ G.Inc e v) :
    (G.deleteVertices X).edgeSet = G.edgeSet := by
  ext e
  simp only [Hypergraph.deleteVertices, Set.mem_sep_iff, and_iff_left_iff_imp]
  intro _ v hv
  exact hX v hv e

theorem deleteVertices_inc_of_isolated {G : Hypergraph α β} {X : Set α}
    (hX : ∀ v ∈ X, ∀ e, ¬ G.Inc e v) (e : β) (u : α) :
    (G.deleteVertices X).Inc e u ↔ G.Inc e u := by
  simp only [Hypergraph.deleteVertices, and_iff_left_iff_imp]
  intro _ w hw
  exact hX w hw e

theorem deleteVertices_ends_of_isolated {G : Hypergraph α β} {X : Set α}
    (hX : ∀ v ∈ X, ∀ e, ¬ G.Inc e v) (e : β) :
    (G.deleteVertices X).ends e = G.ends e := by
  ext u
  exact deleteVertices_inc_of_isolated hX e u

/-- Deleting a set `X` of isolated vertices preserves `maxEdgeSize`. -/
theorem maxEdgeSize_deleteVertices_of_isolated {G : Hypergraph α β} {X : Set α}
    (hX : ∀ v ∈ X, ∀ e, ¬ G.Inc e v) :
    maxEdgeSize (G.deleteVertices X) = maxEdgeSize G := by
  have hedge : ∀ e, edgeSize (G.deleteVertices X) e = edgeSize G e := by
    intro e
    simp only [edgeSize, deleteVertices_ends_of_isolated hX]
  simp only [maxEdgeSize, deleteVertices_edgeSet_of_isolated hX]
  congr 1
  ext n
  simp [hedge]

/-- Deleting a set `X` of isolated vertices preserves `IsBranchDecomposition`. -/
theorem isBranchDecomposition_deleteVertices_iff [Fintype ι] {G : Hypergraph α β} {X : Set α}
    (hX : ∀ v ∈ X, ∀ e, ¬ G.Inc e v) {T : SimpleGraph ι} {τ : ι → β} :
    IsBranchDecomposition (G.deleteVertices X) T τ ↔ IsBranchDecomposition G T τ := by
  constructor <;> rintro ⟨hT, hbij⟩ <;> refine ⟨hT, ?_⟩
  · rwa [deleteVertices_edgeSet_of_isolated hX] at hbij
  · rwa [deleteVertices_edgeSet_of_isolated hX]

/-- Deleting a set `X` of isolated vertices preserves `branchEdgeOrder`. -/
theorem branchEdgeOrder_deleteVertices_of_isolated [Fintype ι] {G : Hypergraph α β} {X : Set α}
    (hX : ∀ v ∈ X, ∀ e, ¬ G.Inc e v) (T : SimpleGraph ι) (τ : ι → β) (e : Sym2 ι) :
    branchEdgeOrder (G.deleteVertices X) T τ e = branchEdgeOrder G T τ e := by
  simp only [branchEdgeOrder]
  congr 1
  ext v
  simp only [Set.mem_sep_iff]
  constructor
  · rintro ⟨⟨hv, _⟩, t₁, ht₁, t₂, ht₂, hnr, hinc₁, hinc₂⟩
    exact ⟨hv, t₁, ht₁, t₂, ht₂, hnr,
      (deleteVertices_inc_of_isolated hX _ _).1 hinc₁,
      (deleteVertices_inc_of_isolated hX _ _).1 hinc₂⟩
  · rintro ⟨hv, t₁, ht₁, t₂, ht₂, hnr, hinc₁, hinc₂⟩
    exact ⟨⟨hv, fun hvX ↦ hX v hvX (τ t₁) hinc₁⟩, t₁, ht₁, t₂, ht₂, hnr,
      (deleteVertices_inc_of_isolated hX _ _).2 hinc₁,
      (deleteVertices_inc_of_isolated hX _ _).2 hinc₂⟩

/-- Deleting a set `X` of isolated vertices preserves `branchDecompWidth`. -/
theorem branchDecompWidth_deleteVertices_of_isolated [Fintype ι] {G : Hypergraph α β} {X : Set α}
    (hX : ∀ v ∈ X, ∀ e, ¬ G.Inc e v) (T : SimpleGraph ι) (τ : ι → β) :
    branchDecompWidth (G.deleteVertices X) T τ = branchDecompWidth G T τ := by
  simp only [branchDecompWidth]
  congr 1
  ext n
  simp [branchEdgeOrder_deleteVertices_of_isolated hX]

/-- Deleting a set `X` of isolated vertices preserves `branchWidth`. -/
theorem branchWidth_deleteVertices_of_isolated {G : Hypergraph α β} {X : Set α}
    (hX : ∀ v ∈ X, ∀ e, ¬ G.Inc e v) :
    branchWidth (G.deleteVertices X) = branchWidth G := by
  simp only [branchWidth, isBranchDecomposition_deleteVertices_iff hX,
    branchDecompWidth_deleteVertices_of_isolated hX]

/-- Every vertex of `G.deleteVertices (isoSet G)` is incident with an edge of
`G.deleteVertices (isoSet G)`. -/
theorem exists_inc_deleteVertices_isoSet {G : Hypergraph α β} {v : α}
    (hv : v ∈ (G.deleteVertices (isoSet G)).vertexSet) :
    ∃ e, (G.deleteVertices (isoSet G)).Inc e v := by
  rcases hv with ⟨hvG, hv_not_iso⟩
  rw [isoSet, Set.mem_sep_iff, not_and_or] at hv_not_iso
  rcases hv_not_iso with hnot | hinc
  · exact (hnot hvG).elim
  · push Not at hinc
    obtain ⟨e, he⟩ := hinc
    exact ⟨e, (deleteVertices_inc_of_isolated (X := {v ∈ G.vertexSet | ∀ e, ¬ G.Inc e v})
      (fun _ h ↦ h.2) e v).2 he⟩

/-- Restricting a tree-decomposition `(T, τ)` of `G` by deleting a set `X` of isolated vertices
gives a tree-decomposition of `G.deleteVertices X`. -/
theorem IsTreeDecomposition.deleteVertices_of_isolated [Fintype ι] {G : Hypergraph α β}
    {X : Set α} (hX : ∀ v ∈ X, ∀ e, ¬ G.Inc e v)
    {T : SimpleGraph ι} {τ : ι → Hypergraph α β} (h : IsTreeDecomposition G T τ) :
    IsTreeDecomposition (G.deleteVertices X) T (fun t ↦ (τ t).deleteVertices X) := by
  have hX_sub : ∀ t, ∀ v ∈ X, ∀ e, ¬ (τ t).Inc e v :=
    fun t v hv e hinc ↦ hX v hv e (inc_of_le (h.le t) hinc)
  have hle_del : ∀ t : ι, (τ t).deleteVertices X ≤ G.deleteVertices X := by
    intro t
    refine (le_iff_of_le ((deleteVertices_le (τ t) X).trans (h.le t)) (deleteVertices_le G X)).2
      ⟨Set.sdiff_subset_sdiff (h.le t).vertexSet_subset subset_rfl, ?_⟩
    rw [deleteVertices_edgeSet_of_isolated (hX_sub t), deleteVertices_edgeSet_of_isolated hX]
    exact (h.le t).edgeSet_subset
  refine ⟨h.isTree, hle_del, ?_, ?_, ?_⟩
  · ext x
    · simp only [Hypergraph.biUnion, Finset.mem_univ, Set.iUnion_true, Set.mem_iUnion]
      change (∃ i, x ∈ (τ i).vertexSet ∧ x ∉ X) ↔ x ∈ G.vertexSet ∧ x ∉ X
      rw [exists_and_right, ← h.vertex_mem_iff]
    · simp only [Hypergraph.biUnion, Finset.mem_univ, Set.iUnion_true, Set.mem_iUnion,
        deleteVertices_edgeSet_of_isolated hX, deleteVertices_edgeSet_of_isolated (hX_sub _),
        ← h.edge_mem_iff]
    · simp only [Hypergraph.biUnion, Finset.mem_univ, true_and,
        deleteVertices_inc_of_isolated hX, deleteVertices_inc_of_isolated (hX_sub _),
        ← h.inc_iff]
  · intro t₁ t₂ hne
    change ((τ t₁).deleteVertices X).edgeSet ∩ ((τ t₂).deleteVertices X).edgeSet = ∅
    rw [deleteVertices_edgeSet_of_isolated (hX_sub t₁),
      deleteVertices_edgeSet_of_isolated (hX_sub t₂)]
    exact h.edgeSet_inter_eq hne
  · intro t₁ t₃ t₂ hp
    have hle := h.inter_le hp
    refine (le_iff_of_le (GM10.inter_le (hle_del t₁) (hle_del t₂)) (hle_del t₃)).2 ⟨?_, ?_⟩
    · intro v ⟨⟨hv1, hvX⟩, ⟨hv2, _⟩⟩
      exact ⟨hle.vertexSet_subset ⟨hv1, hv2⟩, hvX⟩
    · change ((τ t₁).deleteVertices X).edgeSet ∩ ((τ t₂).deleteVertices X).edgeSet ⊆
        ((τ t₃).deleteVertices X).edgeSet
      rw [deleteVertices_edgeSet_of_isolated (hX_sub t₁),
        deleteVertices_edgeSet_of_isolated (hX_sub t₂),
        deleteVertices_edgeSet_of_isolated (hX_sub t₃)]
      exact hle.edgeSet_subset

/-- Deleting a set `X` of isolated vertices does not increase `treeWidthPlusOne`. -/
theorem treeWidthPlusOne_deleteVertices_le_of_isolated {G : Hypergraph α β} {X : Set α}
    (hX : ∀ v ∈ X, ∀ e, ¬ G.Inc e v) :
    treeWidthPlusOne (G.deleteVertices X) ≤ treeWidthPlusOne G := by
  obtain ⟨ι, _, T, τ, h, hw⟩ := exists_treeDecomposition_eq_treeWidthPlusOne G
  have : Nonempty ι := h.nonempty
  refine (treeWidthPlusOne_le_of_isTreeDecomposition (h.deleteVertices_of_isolated hX)).trans ?_
  rw [← hw, treeDecompWidthPlusOne_le_iff]
  intro t
  refine (Set.ncard_le_ncard Set.sdiff_subset (τ t).vertexSet_finite).trans
    (ncard_vertexSet_le_treeDecompWidthPlusOne τ t)

/-- Attaching a single isolated vertex `v ∈ V(G)` to a tree-decomposition of `G \ {v}` increases
`treeWidthPlusOne` by at most `max _ 1`. -/
theorem treeWidthPlusOne_le_max_deleteVertices_singleton {G : Hypergraph α β} {v : α}
    (hvG : v ∈ G.vertexSet) (hiso : ∀ e, ¬ G.Inc e v) :
    treeWidthPlusOne G ≤ max (treeWidthPlusOne (G.deleteVertices {v})) 1 := by
  obtain ⟨ι, _, T, τ, h, hw⟩ :=
    exists_treeDecomposition_eq_treeWidthPlusOne (G.deleteVertices {v})
  obtain ⟨t₀⟩ := h.nonempty
  let τ' : Option ι → Hypergraph α β
    | some t => τ t
    | none => vertexHypergraph v
  have hX : ∀ w ∈ ({v} : Set α), ∀ e, ¬ G.Inc e w := by
    rintro w rfl e; exact hiso e
  have hv_not_τ : ∀ t : ι, v ∉ (τ t).vertexSet := by
    intro t hv_mem
    exact (h.le t).vertexSet_subset hv_mem |>.2 (Set.mem_singleton v)
  have hle_G : ∀ x : Option ι, τ' x ≤ G := by
    rintro (_ | t)
    · exact vertexHypergraph_le hvG
    · exact (h.le t).trans (deleteVertices_le G {v})
  have hτ' : IsTreeDecomposition G (attachLeaf T t₀) τ' := by
    refine ⟨isTree_attachLeaf h.isTree t₀, hle_G, ?_, ?_, ?_⟩
    · ext x
      · simp only [Hypergraph.biUnion, Finset.mem_univ, Set.iUnion_true, Set.mem_iUnion]
        constructor
        · rintro ⟨a, hx⟩
          exact (hle_G a).vertexSet_subset hx
        · intro hxG
          by_cases hxv : x = v
          · exact ⟨none, by simp [τ', vertexHypergraph, hxv]⟩
          · have hx' : x ∈ (G.deleteVertices {v}).vertexSet := ⟨hxG, hxv⟩
            obtain ⟨t, ht⟩ := h.vertex_mem_iff.1 hx'
            exact ⟨some t, ht⟩
      · simp only [Hypergraph.biUnion, Finset.mem_univ, Set.iUnion_true, Set.mem_iUnion]
        constructor
        · rintro ⟨a, he⟩
          exact (hle_G a).edgeSet_subset he
        · intro heG
          rw [← deleteVertices_edgeSet_of_isolated hX] at heG
          obtain ⟨t, ht⟩ := h.edge_mem_iff.1 heG
          exact ⟨some t, ht⟩
      · simp only [Hypergraph.biUnion, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨a, hinc⟩
          exact inc_of_le (hle_G a) hinc
        · intro hincG
          rw [← deleteVertices_inc_of_isolated hX] at hincG
          obtain ⟨t, ht⟩ := h.inc_iff.1 hincG
          exact ⟨some t, ht⟩
    · rintro (_ | t₁) (_ | t₂) hne
      · exact (hne rfl).elim
      · exact Set.empty_inter _
      · exact Set.inter_empty _
      · exact h.edgeSet_inter_eq (fun h ↦ hne (congrArg Option.some h))
    · rintro (_ | t₁) c (_ | t₂) hp
      · have hc : c = none := onTreePath_self_iff.1 hp
        subst hc
        exact GM10.inter_le_left (hle_G none) (hle_G none)
      · have hbot : τ' none ∩ τ' (some t₂) = ⊥ := by
          ext x
          · simp only [τ', vertexHypergraph, inter_vertexSet, Set.mem_inter_iff,
              Set.mem_singleton_iff, bot_vertexSet, Set.mem_empty_iff_false, iff_false]
            rintro ⟨rfl, hx⟩
            exact hv_not_τ t₂ hx
          · simp [τ', vertexHypergraph]
          · simp [τ', vertexHypergraph, inter_inc]
        rw [hbot]
        exact bot_le
      · have hbot : τ' (some t₁) ∩ τ' none = ⊥ := by
          ext x
          · simp only [τ', vertexHypergraph, inter_vertexSet, Set.mem_inter_iff,
              Set.mem_singleton_iff, bot_vertexSet, Set.mem_empty_iff_false, iff_false]
            rintro ⟨hx, rfl⟩
            exact hv_not_τ t₁ hx
          · simp [τ', vertexHypergraph]
          · simp [τ', vertexHypergraph, inter_inc]
        rw [hbot]
        exact bot_le
      · cases c with
        | none =>
          rcases eq_or_eq_of_onTreePath_of_unique_adj (isTree_attachLeaf h.isTree t₀).connected
            (fun w₁ w₂ h₁ h₂ ↦ (adj_attachLeaf_none_iff.1 h₁).trans
              (adj_attachLeaf_none_iff.1 h₂).symm) hp with h1 | h2
          · exact nomatch h1
          · exact nomatch h2
        | some t₃ =>
          exact h.inter_le (onTreePath_projAttach_of_some hp)
  refine (treeWidthPlusOne_le_of_isTreeDecomposition hτ').trans ?_
  rw [← hw, treeDecompWidthPlusOne_le_iff]
  rintro (_ | t)
  · simp [τ', vertexHypergraph]
  · exact (ncard_vertexSet_le_treeDecompWidthPlusOne τ t).trans (le_max_left _ _)

/-- Deleting all isolated vertices `isoSet G` changes `treeWidthPlusOne G` by at most `max _ 1`. -/
theorem treeWidthPlusOne_le_max_deleteVertices_isoSet (G : Hypergraph α β) :
    treeWidthPlusOne G ≤ max (treeWidthPlusOne (G.deleteVertices (isoSet G))) 1 := by
  suffices ∀ (X : Set α), X.Finite → X ⊆ isoSet G →
      treeWidthPlusOne G ≤ max (treeWidthPlusOne (G.deleteVertices X)) 1 from
    this (isoSet G) (isoSet_finite G) subset_rfl
  intro X hXfin
  induction X, hXfin using Set.Finite.induction_on with
  | empty =>
    intro _
    have heq : G.deleteVertices ∅ = G := by
      ext x <;> simp [Hypergraph.deleteVertices]
    rw [heq]
    exact le_max_left _ _
  | @insert v S hvS _ ih =>
    intro hsub
    have hS_sub : S ⊆ isoSet G := (Set.subset_insert v S).trans hsub
    have hv_iso : v ∈ isoSet G := hsub (Set.mem_insert v S)
    have hstep1 := ih hS_sub
    have hv_mem : v ∈ (G.deleteVertices S).vertexSet := ⟨hv_iso.1, hvS⟩
    have hv_iso' : ∀ e, ¬ (G.deleteVertices S).Inc e v := fun e hinc ↦ hv_iso.2 e hinc.1
    have hstep2 := treeWidthPlusOne_le_max_deleteVertices_singleton hv_mem hv_iso'
    rw [deleteVertices_deleteVertices_singleton] at hstep2
    omega

/-- When `maxEdgeSize G = 0` and `G.vertexSet` is nonempty, `branchWidth G = 0` and
`treeWidthPlusOne G = 1` (`ω(G) = 0`)
(Graph Minors X, Section 5, (5.1), page 168). -/
theorem branchWidth_and_treeWidthPlusOne_of_maxEdgeSize_eq_zero {G : Hypergraph α β}
    (hγ : maxEdgeSize G = 0) (hne : G.vertexSet.Nonempty) :
    branchWidth G = 0 ∧ treeWidthPlusOne G = 1 := by
  refine ⟨branchWidth_eq_zero_of_maxEdgeSize_eq_zero hγ, ?_⟩
  have hge : 1 ≤ treeWidthPlusOne G := one_le_treeWidthPlusOne_of_nonempty hne
  have hiso_eq : isoSet G = G.vertexSet := by
    ext v
    simp only [isoSet, Set.mem_sep_iff, and_iff_left_iff_imp]
    intro _ e hinc
    exact maxEdgeSize_eq_zero_iff.1 hγ e (G.edge_mem_of_inc hinc) v hinc
  have hemp : (G.deleteVertices (isoSet G)).vertexSet = ∅ := by
    change G.vertexSet \ isoSet G = ∅
    rw [hiso_eq, Set.sdiff_self]
  have htw0 : treeWidthPlusOne (G.deleteVertices (isoSet G)) = 0 :=
    treeWidthPlusOne_eq_zero_iff.2 hemp
  have hle := treeWidthPlusOne_le_max_deleteVertices_isoSet G
  rw [htw0] at hle
  omega

/-- When `1 ≤ maxEdgeSize G` and `G.edgeSet.ncard ≤ 1`, `treeWidthPlusOne G ≤ maxEdgeSize G`. -/
theorem treeWidthPlusOne_le_maxEdgeSize_of_ncard_edgeSet_le_one {G : Hypergraph α β}
    (hγ : 1 ≤ maxEdgeSize G) (hcard : G.edgeSet.ncard ≤ 1) :
    treeWidthPlusOne G ≤ maxEdgeSize G := by
  obtain ⟨⟨e₀, he₀⟩, _⟩ := nonempty_of_one_le_maxEdgeSize hγ
  have he_eq : ∀ e ∈ G.edgeSet, e = e₀ := by
    intro e he
    by_contra hne
    have hsub : ({e, e₀} : Set β) ⊆ G.edgeSet := by
      rintro x (rfl | rfl) <;> assumption
    have h2 : ({e, e₀} : Set β).ncard = 2 := Set.ncard_pair hne
    have hle := Set.ncard_le_ncard hsub G.edgeSet_finite
    omega
  have hsub_ends : (G.deleteVertices (isoSet G)).vertexSet ⊆ G.ends e₀ := by
    intro v hv
    obtain ⟨e, hinc⟩ := exists_inc_deleteVertices_isoSet hv
    have he_mem : e ∈ G.edgeSet := G.edge_mem_of_inc hinc.1
    rw [← he_eq e he_mem]
    exact hinc.1
  have htw_del : treeWidthPlusOne (G.deleteVertices (isoSet G)) ≤ maxEdgeSize G :=
    (treeWidthPlusOne_le_ncard_vertexSet _).trans
      ((Set.ncard_le_ncard hsub_ends (ends_finite G e₀)).trans (edgeSize_le_maxEdgeSize he₀))
  have hle := treeWidthPlusOne_le_max_deleteVertices_isoSet G
  omega

/-! ## Second inequality of (5.1): tree-decomposition from a branch-decomposition -/

/-- The vertex set of the bag `σ(t)` constructed from a branch-decomposition `(T, τ)` of `G`
(Graph Minors X, Section 5, proof of (5.1), page 169):
all `v ∈ V(G)` such that there exist leaves `t₁, t₂` of `T` with `τ(t₁), τ(t₂)` incident with `v`
and `t` on the path of `T` between `t₁` and `t₂`. -/
@[expose] def branchInternalBag [Fintype ι] (G : Hypergraph α β) (T : SimpleGraph ι) (τ : ι → β)
    (t : ι) : Set α :=
  {v ∈ G.vertexSet | ∃ t₁ ∈ leafSet T, ∃ t₂ ∈ leafSet T,
    G.Inc (τ t₁) v ∧ G.Inc (τ t₂) v ∧ OnTreePath T t₁ t₂ t}

/-- For a leaf `t ∈ leafSet T`, `branchInternalBag G T τ t` is exactly `G.ends (τ t)`. -/
theorem branchInternalBag_eq_ends_of_isLeaf [Fintype ι] {G : Hypergraph α β}
    {T : SimpleGraph ι} {τ : ι → β} (hT : IsTernaryTree T) {t : ι} (ht : IsLeaf T t) :
    branchInternalBag G T τ t = G.ends (τ t) := by
  ext v
  simp only [branchInternalBag, Hypergraph.ends, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨_, t₁, _, t₂, _, hinc₁, hinc₂, hp⟩
    obtain ⟨w₀, _, hw₀_uniq⟩ := hT.exists_adj_of_isLeaf ht
    have huniq : ∀ w₁ w₂, T.Adj t w₁ → T.Adj t w₂ → w₁ = w₂ :=
      fun w₁ w₂ h₁ h₂ ↦ (hw₀_uniq w₁ h₁).trans (hw₀_uniq w₂ h₂).symm
    rcases eq_or_eq_of_onTreePath_of_unique_adj hT.isTree.connected huniq hp with rfl | rfl
    · exact hinc₁
    · exact hinc₂
  · intro hinc
    exact ⟨G.vertex_mem_of_inc hinc, t, ht, t, ht, hinc, hinc, onTreePath_refl_left T t t⟩

/-- The subhypergraph `σ(t)` of `G` constructed from a branch-decomposition `(T, τ)` of `G`
(Graph Minors X, Section 5, proof of (5.1), page 169):
- if `t` is a leaf of `T`, `σ(t) = K_{τ(t)}` (`edgeHypergraph G (τ t)`),
- if `t` is not a leaf of `T`, `E(σ(t)) = ∅` and `V(σ(t)) = branchInternalBag G T τ t`. -/
@[expose] noncomputable def branchToTreeBag [Fintype ι] (G : Hypergraph α β) (T : SimpleGraph ι)
    (τ : ι → β) (t : ι) : Hypergraph α β where
  vertexSet := branchInternalBag G T τ t
  edgeSet := {e ∈ G.edgeSet | IsLeaf T t ∧ e = τ t}
  Inc e v := IsLeaf T t ∧ e = τ t ∧ G.Inc e v
  vertex_mem_of_inc e v h := by
    rcases h with ⟨ht, rfl, hinc⟩
    exact ⟨G.vertex_mem_of_inc hinc, t, ht, t, ht, hinc, hinc, onTreePath_refl_left T t t⟩
  edge_mem_of_inc e v h := ⟨G.edge_mem_of_inc h.2.2, h.1, h.2.1⟩
  vertexSet_finite := G.vertexSet_finite.subset fun _ h ↦ h.1
  edgeSet_finite := G.edgeSet_finite.subset fun _ h ↦ h.1

theorem branchToTreeBag_le [Fintype ι] {G : Hypergraph α β} {T : SimpleGraph ι} {τ : ι → β}
    (t : ι) : branchToTreeBag G T τ t ≤ G where
  vertexSet_subset _ h := h.1
  edgeSet_subset _ he := he.1
  ends_eq e he := by
    rcases he with ⟨_, ht, rfl⟩
    ext v
    simp [Hypergraph.ends, branchToTreeBag, ht]

/-- If every vertex of `G` is incident with an edge and `(T, τ)` is a branch-decomposition of `G`,
then `(T, branchToTreeBag G T τ)` is a tree-decomposition of `G`
(Graph Minors X, Section 5, proof of (5.1), page 169). -/
theorem isTreeDecomposition_branchToTreeBag [Fintype ι] {G : Hypergraph α β}
    {T : SimpleGraph ι} {τ : ι → β}
    (hno_iso : ∀ v ∈ G.vertexSet, ∃ e, G.Inc e v)
    (hbd : IsBranchDecomposition G T τ) :
    IsTreeDecomposition G T (branchToTreeBag G T τ) where
  isTree := hbd.isTernaryTree.isTree
  le := branchToTreeBag_le
  biUnion_eq := by
    ext x
    · simp only [Hypergraph.biUnion, Finset.mem_univ, Set.iUnion_true, Set.mem_iUnion]
      constructor
      · rintro ⟨t, ht⟩
        exact ht.1
      · intro hxG
        obtain ⟨e, hinc⟩ := hno_iso x hxG
        obtain ⟨t, ht_leaf, rfl⟩ := hbd.bijOn.surjOn (G.edge_mem_of_inc hinc)
        exact ⟨t, hxG, t, ht_leaf, t, ht_leaf, hinc, hinc, onTreePath_refl_left T t t⟩
    · simp only [Hypergraph.biUnion, Finset.mem_univ, Set.iUnion_true, Set.mem_iUnion]
      constructor
      · rintro ⟨t, ht⟩
        exact ht.1
      · intro heG
        obtain ⟨t, ht_leaf, rfl⟩ := hbd.bijOn.surjOn heG
        exact ⟨t, heG, ht_leaf, rfl⟩
    · simp only [Hypergraph.biUnion, Finset.mem_univ, true_and, branchToTreeBag]
      constructor
      · rintro ⟨_, _, _, hinc⟩
        exact hinc
      · intro hincG
        obtain ⟨t, ht_leaf, rfl⟩ := hbd.bijOn.surjOn (G.edge_mem_of_inc hincG)
        exact ⟨t, ht_leaf, rfl, hincG⟩
  edgeSet_inter_eq t₁ t₂ hne := by
    ext e
    simp only [inter_edgeSet, Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
    rintro ⟨⟨_, h₁, rfl⟩, ⟨_, h₂, heq⟩⟩
    exact hne (hbd.bijOn.injOn h₁ h₂ heq)
  inter_le {a c b} hp := by
    refine (le_iff_of_le (GM10.inter_le (branchToTreeBag_le a) (branchToTreeBag_le b))
      (branchToTreeBag_le c)).2 ⟨?_, ?_⟩
    · intro v ⟨hva, hvb⟩
      have hconv := isConvex_exists_onTreePath hbd.isTernaryTree.isTree
        (S := {t ∈ leafSet T | G.Inc (τ t) v})
        (by obtain ⟨_, t₁, ht₁, t₂, ht₂, hi₁, hi₂, hpa⟩ := hva
            exact ⟨t₁, ⟨ht₁, hi₁⟩, t₂, ⟨ht₂, hi₂⟩, hpa⟩)
        (by obtain ⟨_, t₃, ht₃, t₄, ht₄, hi₃, hi₄, hpb⟩ := hvb
            exact ⟨t₃, ⟨ht₃, hi₃⟩, t₄, ⟨ht₄, hi₄⟩, hpb⟩)
        hp
      obtain ⟨s₁, ⟨hs₁, his₁⟩, s₂, ⟨hs₂, his₂⟩, hpc⟩ := hconv
      exact ⟨hva.1, s₁, hs₁, s₂, hs₂, his₁, his₂, hpc⟩
    · rintro e ⟨⟨heG, ha, rfl⟩, ⟨_, hb, heq⟩⟩
      have hab : a = b := hbd.bijOn.injOn ha hb heq
      subst hab
      have hca : c = a := onTreePath_self_iff.1 hp
      subst hca
      exact ⟨heG, ha, rfl⟩

/-- For any internal vertex `t ∉ leafSet T` of a branch-decomposition `(T, τ)` of `G`,
`2 * (branchInternalBag G T τ t).ncard ≤ 3 * branchDecompWidth G T τ`
(Graph Minors X, Section 5, proof of (5.1), page 169). -/
theorem two_mul_ncard_branchInternalBag_le [Fintype ι] {G : Hypergraph α β}
    {T : SimpleGraph ι} {τ : ι → β} (hbd : IsBranchDecomposition G T τ)
    {t : ι} (ht : ¬ IsLeaf T t) :
    2 * (branchInternalBag G T τ t).ncard ≤ 3 * branchDecompWidth G T τ := by
  have hT := hbd.isTernaryTree
  obtain ⟨w₁, w₂, w₃, hw12, hw13, hw23, hiff⟩ := hT.exists_three_adj_of_not_isLeaf ht
  have hadj₁ : T.Adj t w₁ := (hiff w₁).2 (Or.inl rfl)
  have hadj₂ : T.Adj t w₂ := (hiff w₂).2 (Or.inr (Or.inl rfl))
  have hadj₃ : T.Adj t w₃ := (hiff w₃).2 (Or.inr (Or.inr rfl))
  let E_edge : Sym2 ι → Set α := fun e ↦
    {v ∈ G.vertexSet | ∃ t₁ ∈ leafSet T, ∃ t₂ ∈ leafSet T,
      ¬ (T.deleteEdges {e}).Reachable t₁ t₂ ∧ G.Inc (τ t₁) v ∧ G.Inc (τ t₂) v}
  let B₁ := E_edge s(t, w₁)
  let B₂ := E_edge s(t, w₂)
  let B₃ := E_edge s(t, w₃)
  have hB_fin : ∀ e, (E_edge e).Finite :=
    fun _ ↦ G.vertexSet_finite.subset fun _ h ↦ h.1
  have hB₁_le : B₁.ncard ≤ branchDecompWidth G T τ :=
    branchEdgeOrder_le_branchDecompWidth ((T.mem_edgeSet).2 hadj₁)
  have hB₂_le : B₂.ncard ≤ branchDecompWidth G T τ :=
    branchEdgeOrder_le_branchDecompWidth ((T.mem_edgeSet).2 hadj₂)
  have hB₃_le : B₃.ncard ≤ branchDecompWidth G T τ :=
    branchEdgeOrder_le_branchDecompWidth ((T.mem_edgeSet).2 hadj₃)
  -- Partition `V(T) \ {t}` into the three components `treeComponent T w_i s(w_i, t)`.
  obtain ⟨hsplit₁, _, _, _⟩ := treeComponent_split_of_not_isLeaf hT hadj₁ hw12 hw13 hw23 hiff
  obtain ⟨hsplit₂, _, _, _⟩ := treeComponent_split_of_not_isLeaf hT hadj₂ hw12.symm hw23 hw13
    (fun x ↦ by rw [hiff]; tauto)
  obtain ⟨hsplit₃, _, _, _⟩ := treeComponent_split_of_not_isLeaf hT hadj₃ hw13.symm hw23.symm hw12
    (fun x ↦ by rw [hiff]; tauto)
  have hmem_three : ∀ x : ι, x ≠ t →
      x ∈ treeComponent T w₁ s(w₁, t) ∨
      x ∈ treeComponent T w₂ s(w₂, t) ∨
      x ∈ treeComponent T w₃ s(w₃, t) := by
    intro x hxt
    by_cases hx₁ : x ∈ treeComponent T w₁ s(w₁, t)
    · exact Or.inl hx₁
    · have hx_in : x ∈ treeComponent T t s(t, w₁) :=
        (notMem_treeComponent_iff hT.isTree hadj₁.symm).1 hx₁
      rw [hsplit₁] at hx_in
      rcases hx_in with (rfl | hx₂) | hx₃
      · exact (hxt rfl).elim
      · exact Or.inr (Or.inl hx₂)
      · exact Or.inr (Or.inr hx₃)
  have hmem_B : ∀ {w : ι} (hadj : T.Adj t w) {v : α} {t₁ t₂ : ι},
      v ∈ G.vertexSet → t₁ ∈ leafSet T → t₂ ∈ leafSet T →
      G.Inc (τ t₁) v → G.Inc (τ t₂) v →
      t₁ ∈ treeComponent T w s(w, t) → t₂ ∈ treeComponent T t s(t, w) →
      v ∈ E_edge s(t, w) := by
    intro w hadj v t₁ t₂ hvG ht₁ ht₂ hi₁ hi₂ hcomp₁ hcomp₂
    refine ⟨hvG, t₁, ht₁, t₂, ht₂, ?_, hi₁, hi₂⟩
    exact (not_reachable_deleteEdges_iff_treeComponent hT.isTree hadj).2 (Or.inr ⟨hcomp₁, hcomp₂⟩)
  have hsub_two : branchInternalBag G T τ t ⊆ (B₁ ∩ B₂) ∪ (B₁ ∩ B₃) ∪ (B₂ ∩ B₃) := by
    rintro v ⟨hvG, t₁, ht₁, t₂, ht₂, hi₁, hi₂, hp⟩
    have ht₁_ne : t₁ ≠ t := fun h ↦ ht (h ▸ ht₁)
    have ht₂_ne : t₂ ≠ t := fun h ↦ ht (h ▸ ht₂)
    have hnot_same : ∀ {w : ι}, T.Adj t w →
        ¬ (t₁ ∈ treeComponent T w s(w, t) ∧ t₂ ∈ treeComponent T w s(w, t)) := by
      rintro w hadj ⟨h1, h2⟩
      have ht_mem : t ∈ treeComponent T w s(w, t) := mem_treeComponent_of_onTreePath h1 h2 hp
      exact (notMem_treeComponent_iff hT.isTree hadj).2 ht_mem Reachable.rfl
    have hc₁_in_2 : treeComponent T w₁ s(w₁, t) ⊆ treeComponent T t s(t, w₂) := by
      rw [hsplit₂]; exact Set.subset_union_of_subset_left Set.subset_union_right _
    have hc₁_in_3 : treeComponent T w₁ s(w₁, t) ⊆ treeComponent T t s(t, w₃) := by
      rw [hsplit₃]; exact Set.subset_union_of_subset_left Set.subset_union_right _
    have hc₂_in_1 : treeComponent T w₂ s(w₂, t) ⊆ treeComponent T t s(t, w₁) := by
      rw [hsplit₁]; exact Set.subset_union_of_subset_left Set.subset_union_right _
    have hc₂_in_3 : treeComponent T w₂ s(w₂, t) ⊆ treeComponent T t s(t, w₃) := by
      rw [hsplit₃]; exact Set.subset_union_right
    have hc₃_in_1 : treeComponent T w₃ s(w₃, t) ⊆ treeComponent T t s(t, w₁) := by
      rw [hsplit₁]; exact Set.subset_union_right
    have hc₃_in_2 : treeComponent T w₃ s(w₃, t) ⊆ treeComponent T t s(t, w₂) := by
      rw [hsplit₂]; exact Set.subset_union_right
    rcases hmem_three t₁ ht₁_ne with h1_1 | h1_2 | h1_3 <;>
      rcases hmem_three t₂ ht₂_ne with h2_1 | h2_2 | h2_3
    · exact (hnot_same hadj₁ ⟨h1_1, h2_1⟩).elim
    · exact Or.inl (Or.inl ⟨hmem_B hadj₁ hvG ht₁ ht₂ hi₁ hi₂ h1_1 (hc₂_in_1 h2_2),
        hmem_B hadj₂ hvG ht₂ ht₁ hi₂ hi₁ h2_2 (hc₁_in_2 h1_1)⟩)
    · exact Or.inl (Or.inr ⟨hmem_B hadj₁ hvG ht₁ ht₂ hi₁ hi₂ h1_1 (hc₃_in_1 h2_3),
        hmem_B hadj₃ hvG ht₂ ht₁ hi₂ hi₁ h2_3 (hc₁_in_3 h1_1)⟩)
    · exact Or.inl (Or.inl ⟨hmem_B hadj₁ hvG ht₂ ht₁ hi₂ hi₁ h2_1 (hc₂_in_1 h1_2),
        hmem_B hadj₂ hvG ht₁ ht₂ hi₁ hi₂ h1_2 (hc₁_in_2 h2_1)⟩)
    · exact (hnot_same hadj₂ ⟨h1_2, h2_2⟩).elim
    · exact Or.inr ⟨hmem_B hadj₂ hvG ht₁ ht₂ hi₁ hi₂ h1_2 (hc₃_in_2 h2_3),
        hmem_B hadj₃ hvG ht₂ ht₁ hi₂ hi₁ h2_3 (hc₂_in_3 h1_2)⟩
    · exact Or.inl (Or.inr ⟨hmem_B hadj₁ hvG ht₂ ht₁ hi₂ hi₁ h2_1 (hc₃_in_1 h1_3),
        hmem_B hadj₃ hvG ht₁ ht₂ hi₁ hi₂ h1_3 (hc₁_in_3 h2_1)⟩)
    · exact Or.inr ⟨hmem_B hadj₂ hvG ht₂ ht₁ hi₂ hi₁ h2_2 (hc₃_in_2 h1_3),
        hmem_B hadj₃ hvG ht₁ ht₂ hi₁ hi₂ h1_3 (hc₂_in_3 h2_2)⟩
    · exact (hnot_same hadj₃ ⟨h1_3, h2_3⟩).elim
  let U₂ := (B₁ ∩ B₂) ∪ (B₁ ∩ B₃) ∪ (B₂ ∩ B₃)
  have hB₁_fin := hB_fin s(t, w₁)
  have hB₂_fin := hB_fin s(t, w₂)
  have hB₃_fin := hB_fin s(t, w₃)
  have hU₂_fin : U₂.Finite :=
    ((hB₁_fin.inter_of_left B₂).union (hB₁_fin.inter_of_left B₃)).union
      (hB₂_fin.inter_of_left B₃)
  have hbag_le_U₂ : (branchInternalBag G T τ t).ncard ≤ U₂.ncard :=
    Set.ncard_le_ncard hsub_two hU₂_fin
  have h12 := Set.ncard_union_add_ncard_inter B₁ B₂ hB₁_fin hB₂_fin
  have h123 := Set.ncard_union_add_ncard_inter (B₁ ∪ B₂) B₃ (hB₁_fin.union hB₂_fin) hB₃_fin
  have hinter_distrib : (B₁ ∪ B₂) ∩ B₃ = (B₁ ∩ B₃) ∪ (B₂ ∩ B₃) :=
    Set.union_inter_distrib_right B₁ B₂ B₃
  rw [hinter_distrib] at h123
  have hU₂_split := Set.ncard_union_add_ncard_inter (B₁ ∩ B₂) ((B₁ ∩ B₃) ∪ (B₂ ∩ B₃))
    (hB₁_fin.inter_of_left B₂) ((hB₁_fin.inter_of_left B₃).union (hB₂_fin.inter_of_left B₃))
  have hU₂_eq : (B₁ ∩ B₂) ∪ ((B₁ ∩ B₃) ∪ (B₂ ∩ B₃)) = U₂ := (Set.union_assoc _ _ _).symm
  rw [hU₂_eq] at hU₂_split
  have h3_split := Set.ncard_union_add_ncard_inter (B₁ ∩ B₃) (B₂ ∩ B₃)
    (hB₁_fin.inter_of_left B₃) (hB₂_fin.inter_of_left B₃)
  have hsub_union : U₂ ⊆ (B₁ ∪ B₂) ∪ B₃ := by
    rintro x ((⟨hx1, _⟩ | ⟨hx1, _⟩) | ⟨hx2, _⟩)
    · exact Or.inl (Or.inl hx1)
    · exact Or.inl (Or.inl hx1)
    · exact Or.inl (Or.inr hx2)
  have hU₂_le_union : U₂.ncard ≤ ((B₁ ∪ B₂) ∪ B₃).ncard :=
    Set.ncard_le_ncard hsub_union ((hB₁_fin.union hB₂_fin).union hB₃_fin)
  omega

/-- For any branch-decomposition `(T, τ)` of `G`,
`treeDecompWidthPlusOne (branchToTreeBag G T τ) ≤ max (3 * branchDecompWidth G T τ / 2) (maxEdgeSize
G)`
(Graph Minors X, Section 5, proof of (5.1), page 169). -/
theorem treeDecompWidthPlusOne_branchToTreeBag_le [Fintype ι] {G : Hypergraph α β}
    {T : SimpleGraph ι} {τ : ι → β} (hbd : IsBranchDecomposition G T τ) :
    treeDecompWidthPlusOne (branchToTreeBag G T τ) ≤
      max (3 * branchDecompWidth G T τ / 2) (maxEdgeSize G) := by
  have : Nonempty ι := hbd.isTernaryTree.isTree.connected.nonempty
  rw [treeDecompWidthPlusOne_le_iff]
  intro t
  change (branchInternalBag G T τ t).ncard ≤
    max (3 * branchDecompWidth G T τ / 2) (maxEdgeSize G)
  by_cases ht : IsLeaf T t
  · rw [branchInternalBag_eq_ends_of_isLeaf hbd.isTernaryTree ht]
    have he_mem : τ t ∈ G.edgeSet := hbd.bijOn.mapsTo ht
    exact (edgeSize_le_maxEdgeSize he_mem).trans (le_max_right _ _)
  · have hle := two_mul_ncard_branchInternalBag_le hbd ht
    have hdiv : (branchInternalBag G T τ t).ncard ≤ 3 * branchDecompWidth G T τ / 2 := by omega
    exact hdiv.trans (le_max_left _ _)

/-- For any branch-decomposition `(T, τ)` of `G`,
`2 * treeDecompWidthPlusOne (branchToTreeBag G T τ) ≤ 3 * max (branchDecompWidth G T τ) (maxEdgeSize
G)`
(Graph Minors X, Section 5, proof of (5.1), page 169). -/
theorem two_mul_treeDecompWidthPlusOne_branchToTreeBag_le [Fintype ι] {G : Hypergraph α β}
    {T : SimpleGraph ι} {τ : ι → β} (hbd : IsBranchDecomposition G T τ) :
    2 * treeDecompWidthPlusOne (branchToTreeBag G T τ) ≤
      3 * max (branchDecompWidth G T τ) (maxEdgeSize G) := by
  have hle := treeDecompWidthPlusOne_branchToTreeBag_le hbd
  have h1 : 3 * branchDecompWidth G T τ / 2 ≤ 3 * max (branchDecompWidth G T τ) (maxEdgeSize G) / 2
    := by
    have : branchDecompWidth G T τ ≤ max (branchDecompWidth G T τ) (maxEdgeSize G)
      := le_max_left _ _
    omega
  have h2 : maxEdgeSize G ≤ max (branchWidth G) (maxEdgeSize G) ∨
      maxEdgeSize G ≤ max (branchDecompWidth G T τ) (maxEdgeSize G) :=
    Or.inr (le_max_right _ _)
  rcases h2 with _ | h2'
  · omega
  · omega

/-- Second inequality of **(5.1)** in `max(⌊(3/2) β(G)⌋, γ(G), 1)` form
(Graph Minors X, Section 5, (5.1), pages 168–169):
For any hypergraph `G`, `treeWidthPlusOne G ≤ max (max (3 * branchWidth G / 2) (maxEdgeSize G)) 1`.
-/
theorem treeWidthPlusOne_le_max_branchWidth_maxEdgeSize (G : Hypergraph α β) :
    treeWidthPlusOne G ≤ max (max (3 * branchWidth G / 2) (maxEdgeSize G)) 1 := by
  by_cases hγ : maxEdgeSize G = 0
  · by_cases hV : G.vertexSet.Nonempty
    · rw [(branchWidth_and_treeWidthPlusOne_of_maxEdgeSize_eq_zero hγ hV).2]
      exact le_max_right _ _
    · rw [Set.not_nonempty_iff_eq_empty] at hV
      rw [treeWidthPlusOne_eq_zero_iff.2 hV]
      exact Nat.zero_le _
  · have hγ1 : 1 ≤ maxEdgeSize G := Nat.one_le_iff_ne_zero.2 hγ
    by_cases hcard : G.edgeSet.ncard ≤ 1
    · exact (treeWidthPlusOne_le_maxEdgeSize_of_ncard_edgeSet_le_one hγ1 hcard).trans
        ((le_max_right _ _).trans (le_max_left _ _))
    · push Not at hcard
      let H := G.deleteVertices (isoSet G)
      have hiso : ∀ v ∈ isoSet G, ∀ e, ¬ G.Inc e v := fun _ hv ↦ hv.2
      have hγH : maxEdgeSize H = maxEdgeSize G := maxEdgeSize_deleteVertices_of_isolated hiso
      have hbwH : branchWidth H = branchWidth G := branchWidth_deleteVertices_of_isolated hiso
      have hcardH : H.edgeSet.ncard = G.edgeSet.ncard := by
        rw [deleteVertices_edgeSet_of_isolated hiso]
      obtain ⟨ι, _, T, τ, hbd, hw⟩ :=
        exists_branchDecomposition_eq_branchWidth (hγH.symm ▸ hγ1) (hcardH.symm ▸ hcard)
      have htdH : IsTreeDecomposition H T (branchToTreeBag H T τ) :=
        isTreeDecomposition_branchToTreeBag (fun _ hv ↦ exists_inc_deleteVertices_isoSet hv) hbd
      have hleH : treeWidthPlusOne H ≤ max (3 * branchWidth G / 2) (maxEdgeSize G) := by
        have hbound := (treeWidthPlusOne_le_of_isTreeDecomposition htdH).trans
          (treeDecompWidthPlusOne_branchToTreeBag_le hbd)
        rwa [hw, hbwH, hγH] at hbound
      exact (treeWidthPlusOne_le_max_deleteVertices_isoSet G).trans
        (max_le_max hleH le_rfl)

/-- Second inequality of **(5.1)** (Graph Minors X, Section 5, (5.1), pages 168–169):
If `1 ≤ maxEdgeSize G` (`γ(G) ≥ 1`) or `G.vertexSet = ∅`, then
`2 * treeWidthPlusOne G ≤ 3 * max (branchWidth G) (maxEdgeSize G)`. -/
theorem two_mul_treeWidthPlusOne_le_three_mul_max {G : Hypergraph α β}
    (h : 1 ≤ maxEdgeSize G ∨ G.vertexSet = ∅) :
    2 * treeWidthPlusOne G ≤ 3 * max (branchWidth G) (maxEdgeSize G) := by
  rcases h with hγ | hemp
  · by_cases hcard : G.edgeSet.ncard ≤ 1
    · have hle := treeWidthPlusOne_le_maxEdgeSize_of_ncard_edgeSet_le_one hγ hcard
      have hmax : maxEdgeSize G ≤ max (branchWidth G) (maxEdgeSize G) := le_max_right _ _
      omega
    · push Not at hcard
      let H := G.deleteVertices (isoSet G)
      have hiso : ∀ v ∈ isoSet G, ∀ e, ¬ G.Inc e v := fun _ hv ↦ hv.2
      have hγH : maxEdgeSize H = maxEdgeSize G := maxEdgeSize_deleteVertices_of_isolated hiso
      have hbwH : branchWidth H = branchWidth G := branchWidth_deleteVertices_of_isolated hiso
      have hcardH : H.edgeSet.ncard = G.edgeSet.ncard := by
        rw [deleteVertices_edgeSet_of_isolated hiso]
      obtain ⟨ι, _, T, τ, hbd, hw⟩ :=
        exists_branchDecomposition_eq_branchWidth (hγH.symm ▸ hγ) (hcardH.symm ▸ hcard)
      have htdH : IsTreeDecomposition H T (branchToTreeBag H T τ) :=
        isTreeDecomposition_branchToTreeBag (fun _ hv ↦ exists_inc_deleteVertices_isoSet hv) hbd
      have hleH : treeWidthPlusOne H ≤ treeDecompWidthPlusOne (branchToTreeBag H T τ) :=
        treeWidthPlusOne_le_of_isTreeDecomposition htdH
      have hboundH := two_mul_treeDecompWidthPlusOne_branchToTreeBag_le hbd
      rw [hw, hbwH, hγH] at hboundH
      have hleG : treeWidthPlusOne G ≤ max (treeWidthPlusOne H) 1 :=
        treeWidthPlusOne_le_max_deleteVertices_isoSet G
      have hmax : maxEdgeSize G ≤ max (branchWidth G) (maxEdgeSize G) := le_max_right _ _
      omega
  · rw [treeWidthPlusOne_eq_zero_iff.2 hemp]
    omega

end GraphMinor.GM10
