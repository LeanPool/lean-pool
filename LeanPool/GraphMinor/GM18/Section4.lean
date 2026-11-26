/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM10.TangleLemmas
public import LeanPool.GraphMinor.GM18.Section3
public import LeanPool.GraphMinor.Thomas.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Order.Field.Rat

/-!
# Graph Minors XVIII, Section 4: Isolating Locations

This file formalizes Section 4 of Robertson and Seymour, *Graph Minors. XVIII. Tree-decompositions
and well-quasi-ordering*, J. Combin. Theory Ser. B 89 (2003) 77–108 (pages 85–89):
- `theorem_4_1`: Saks's lemma on partitioning a tree `T` with linearly ordered edges into vertex-
  disjoint subtrees `T_t` (`t ∈ I`).
- `theorem_4_2`: Given distinct tangles `𝒯_j` (`j ∈ J`) of order `θ` and `θ`-isolating locations
  `ℒ_j ⊆ 𝒯_j`, there exists `I ⊆ J` such that for every `j ∈ J` there is a unique `i ∈ I` with
  `ℒ_i ⊆ 𝒯_j` (with Claims (1)–(4): `lemma_4_2_claim_1` through `lemma_4_2_claim_4`).
- `theorem_4_3`: In a standard tree-decomposition relative to `𝒯₁, …, 𝒯ₙ` of order `θ ≥ 2`, where
  each `ℒᵢ ⊆ 𝒯ᵢ` is a `θ`-isolating location of order `≤ (3/4) θ` and every tangle of order `θ`
  includes a unique `ℒᵢ`, the location of `tᵢ` is an enlargement of `ℒᵢ` by tree-width
  `≤ (9/4) θ` (with Claims (1)–(4): `lemma_4_3_claim_1` through `lemma_4_3_claim_4`).
- `theorem_4_4`: The main structure theorem of Section 4, producing a proper, rotund, robust
  tree-decomposition `(T, τ)` of `G` whose vertex locations are enlargements of isolating locations
  `ℒ(𝒯)` by tree-width `≤ 3 θ + 1`.
-/

public section

namespace GraphMinor.GM18

open Hypergraph SimpleGraph

universe u v w

variable {α : Type u} {β : Type v} {ι : Type*}

/-! ## (4.1): Saks's Lemma on Subtrees of a Tree -/

/-- A subset `S : Set ι` of vertices of a tree `T` is a subtree (connected in the induced subgraph):
for any `u, v ∈ S`, every vertex on the path in `T` between `u` and `v` belongs to `S`. -/
def IsTreeConvex (T : SimpleGraph ι) (S : Set ι) : Prop :=
  ∀ ⦃u v : ι⦄, u ∈ S → v ∈ S → ∀ ⦃x : ι⦄, Thomas.OnTreePath T u v x → x ∈ S

private theorem eq_singleton_of_no_internal_edge {T : SimpleGraph ι} (hT : T.IsTree)
    {U : Set ι} (hU : IsTreeConvex T U) {t : ι} (ht : t ∈ U)
    (hno : ∀ ⦃u v : ι⦄, u ∈ U → v ∈ U → ¬ T.Adj u v) : U = {t} := by
  ext x
  simp only [Set.mem_singleton_iff]
  refine ⟨fun hx => ?_, fun he => he ▸ ht⟩
  by_contra hne
  obtain ⟨u, v, he, hu, _⟩ := Thomas.exists_onTreePathEdge_of_prop hT (· = t) rfl hne
  subst hu
  exact hno ht (hU ht hx he.onTreePath_right) he.1

private theorem partition_of_singleton {U : Set ι} {t : ι} {sub : ι → Set ι}
    (hU : U = {t}) (hsub : sub t ⊆ U) (ht : t ∈ sub t) :
    ∃ I ⊆ U, (∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (sub i) (sub j)) ∧
      (⋃ i ∈ I, sub i) = U := by
  subst U
  refine ⟨{t}, Set.Subset.rfl, ?_, ?_⟩
  · intro i hi j hj hne
    exact (hne ((Set.mem_singleton_iff.1 hi).trans (Set.mem_singleton_iff.1 hj).symm)).elim
  · ext x
    simp only [Set.mem_iUnion, Set.mem_singleton_iff, exists_prop, exists_eq_left]
    exact ⟨fun hx => hsub hx, fun hx => hx.symm ▸ ht⟩

private theorem partition_of_crossing_member {I U V : Set ι} {sub : ι → Set ι}
    {boundary r : ι} (hb : boundary ∈ U) (hsub : ∀ i ∈ I, sub i ⊆ U ∪ V)
    (hdisj : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (sub i ∩ U) (sub j ∩ U))
    (hcover : (⋃ i ∈ I, sub i ∩ U) = U)
    (hcross : ∀ i ∈ I, ¬ sub i ⊆ U → boundary ∈ sub i ∧ V ⊆ sub i)
    (hr : r ∈ I) (hnot : ¬ sub r ⊆ U) :
    (∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (sub i) (sub j)) ∧
      (⋃ i ∈ I, sub i) = U ∪ V := by
  refine ⟨?_, Set.Subset.antisymm (Set.iUnion₂_subset hsub) ?_⟩
  · intro i hi j hj hne
    refine Set.disjoint_left.2 fun x hx hy => ?_
    by_cases hxU : x ∈ U
    · exact Set.disjoint_left.1 (hdisj i hi j hj hne) ⟨hx, hxU⟩ ⟨hy, hxU⟩
    · have hbi := (hcross i hi (fun hs => hxU (hs hx))).1
      have hbj := (hcross j hj (fun hs => hxU (hs hy))).1
      exact Set.disjoint_left.1 (hdisj i hi j hj hne) ⟨hbi, hb⟩ ⟨hbj, hb⟩
  · refine Set.union_subset ?_ ((hcross r hr hnot).2.trans (Set.subset_biUnion_of_mem hr))
    rw [← hcover]
    exact Set.biUnion_mono subset_rfl fun i _ => Set.inter_subset_left

private theorem isTreeConvex_side {T : SimpleGraph ι} (hT : T.IsTree)
    {U : Set ι} (hU_conv : IsTreeConvex T U) {a b : ι} (hadj : T.Adj a b) :
    IsTreeConvex T {x ∈ U | Thomas.OnTreePath T x b a} := by
  intro x y ⟨hxU, hx⟩ ⟨hyU, hy⟩ z hz
  refine ⟨hU_conv hxU hyU hz, ?_⟩
  change GM10.OnTreePath T x b a at hx
  change GM10.OnTreePath T y b a at hy
  change GM10.OnTreePath T z b a
  rw [← reachable_deleteEdges_iff_onTreePath hT hadj] at hx hy ⊢
  have hzy : (T.deleteEdges {s(a, b)}).Reachable z y := by
    rw [reachable_deleteEdges_iff_exists_walk]
    have hp_isPath := Thomas.treePath_isPath hT x y
    have hz_mem : z ∈ (Thomas.treePath hT x y).support :=
      (Thomas.onTreePath_iff_mem_treePath hT).1 hz
    have hnot_ab : s(a, b) ∉ (Thomas.treePath hT x y).edges := by
      intro hab
      have he_xy : Thomas.OnTreePathEdge T x y a b :=
        (Thomas.onTreePathEdge_iff_mem_treePath hT).2 ⟨hadj, hab⟩
      have hnot_reach := (Thomas.onTreePathEdge_iff_not_reachable_deleteEdges.1 he_xy).2
      exact hnot_reach (hx.symm.trans hy)
    obtain ⟨p₁, p₂, _, _, heq⟩ := hp_isPath.mem_support_iff_exists_append.1 hz_mem
    refine ⟨p₂, fun hmem ↦ hnot_ab ?_⟩
    rw [heq, Walk.edges_append, List.mem_append]
    exact Or.inr hmem
  exact hy.trans hzy.symm

/-- **Graph Minors XVIII, (4.1)** (page 85, M. Saks):
"Let $T$ be a tree and let $\le$ be some linear order on $E(T)$. For each $t \in V(T)$, let
$T_t$ be a subtree of $T$ such that* - *$t \in V(T_t)$,* - *if $e \in E(T)$ has one end in
$V(T_t)$ and the other end in $V(T) \setminus V(T_t)$ and $f$ is an edge of the path of $T$
with first vertex $t$ and last edge $e$, then $e \le f$.* *Then there exists $I \subseteq
V(T)$ such that the sets $V(T_t)$ ($t \in I$) form a partition of $V(T)$."

We prove this for any tree-convex subset `U ⊆ V(T)` by strong induction on `|U|`, taking `U =
Set.univ`
to obtain (4.1). -/
private theorem saks_lemma_aux [Finite ι] {T : SimpleGraph ι} (hT : T.IsTree)
    {Λ : Type*} [LinearOrder Λ] (μ : Sym2 ι → Λ)
    (he_inj : ∀ ⦃e₁ e₂ : Sym2 ι⦄, e₁ ∈ T.edgeSet → e₂ ∈ T.edgeSet → μ e₁ = μ e₂ → e₁ = e₂)
    (U : Set ι) (hU_ne : U.Nonempty) (hU_conv : IsTreeConvex T U)
    (sub : ι → Set ι)
    (hsub_U : ∀ t ∈ U, sub t ⊆ U)
    (ht_mem : ∀ t ∈ U, t ∈ sub t)
    (hsub_conv : ∀ t ∈ U, IsTreeConvex T (sub t))
    (hsub_ord : ∀ t ∈ U, ∀ u ∈ sub t, ∀ v ∈ U \ sub t, T.Adj u v →
      ∀ x y : ι, Thomas.OnTreePathEdge T t v x y → μ s(u, v) ≤ μ s(x, y)) :
    ∃ I ⊆ U, (∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (sub i) (sub j)) ∧
      (⋃ i ∈ I, sub i) = U := by
  classical
  let fintypeVertices := Fintype.ofFinite ι
  revert U sub
  suffices hmain : ∀ n : ℕ, ∀ U : Set ι, U.ncard = n → U.Nonempty → IsTreeConvex T U →
      ∀ sub : ι → Set ι,
      (∀ t ∈ U, sub t ⊆ U) →
      (∀ t ∈ U, t ∈ sub t) →
      (∀ t ∈ U, IsTreeConvex T (sub t)) →
      (∀ t ∈ U, ∀ u ∈ sub t, ∀ v ∈ U \ sub t, T.Adj u v →
        ∀ x y : ι, Thomas.OnTreePathEdge T t v x y → μ s(u, v) ≤ μ s(x, y)) →
      ∃ I ⊆ U, (∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (sub i) (sub j)) ∧
        (⋃ i ∈ I, sub i) = U by
    intro U hU_ne hU_conv sub hsub_U ht_mem hsub_conv hsub_ord
    exact hmain U.ncard U rfl hU_ne hU_conv sub hsub_U ht_mem hsub_conv hsub_ord
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro U hcard hU_ne hU_conv sub hsub_U ht_mem hsub_conv hsub_ord
    let E_U : Finset (Sym2 ι) :=
      Finset.univ.filter fun e ↦ e ∈ T.edgeSet ∧ ∀ x ∈ e, x ∈ U
    by_cases hE_empty : E_U = ∅
    · -- No edges in `U`: since `U` is tree-convex and nonempty, `U` has a single vertex `t₀`.
      obtain ⟨t₀, ht₀⟩ := hU_ne
      have hU_eq : U = {t₀} := eq_singleton_of_no_internal_edge hT hU_conv ht₀ (by
        intro u v hu hv hadj
        exact Finset.notMem_empty s(u, v) (hE_empty ▸ Finset.mem_filter.2
          ⟨Finset.mem_univ _, T.mem_edgeSet.2 hadj, fun z hz => by
            rcases Sym2.mem_iff.1 hz with rfl | rfl
            · exact hu
            · exact hv⟩))
      exact partition_of_singleton hU_eq (hsub_U t₀ ht₀) (ht_mem t₀ ht₀)
    · -- Choose `f ∈ E_U` minimizing `μ f`
      have hE_ne : E_U.Nonempty := Finset.nonempty_iff_ne_empty.2 hE_empty
      obtain ⟨f, hf_mem, hf_min⟩ := E_U.exists_min_image μ hE_ne
      have hf_filter := (Finset.mem_filter.1 hf_mem).2
      rcases f with ⟨u₁, u₂⟩
      have hadj_f : T.Adj u₁ u₂ := T.mem_edgeSet.1 hf_filter.1
      have hu₁_U : u₁ ∈ U := hf_filter.2 u₁ (Sym2.mem_mk_left u₁ u₂)
      have hu₂_U : u₂ ∈ U := hf_filter.2 u₂ (Sym2.mem_mk_right u₁ u₂)
      let U₁ : Set ι := {x ∈ U | Thomas.OnTreePath T x u₂ u₁}
      let U₂ : Set ι := {x ∈ U | Thomas.OnTreePath T x u₁ u₂}
      have hu₁_U₁ : u₁ ∈ U₁ := ⟨hu₁_U, Thomas.onTreePath_left T u₁ u₂⟩
      have hu₂_U₂ : u₂ ∈ U₂ := ⟨hu₂_U, Thomas.onTreePath_left T u₂ u₁⟩
      have hu₁_not_U₂ : u₁ ∉ U₂ := fun h ↦
        hadj_f.ne (Thomas.onTreePath_self T u₁ u₂ |>.1 h.2).symm
      have hu₂_not_U₁ : u₂ ∉ U₁ := fun h ↦
        hadj_f.ne (Thomas.onTreePath_self T u₂ u₁ |>.1 h.2)
      have hU₁_sub : U₁ ⊆ U := fun _ h ↦ h.1
      have hU₂_sub : U₂ ⊆ U := fun _ h ↦ h.1
      have hU_union : U₁ ∪ U₂ = U := by
        ext x
        refine ⟨fun h ↦ h.elim (fun h1 ↦ h1.1) (fun h2 ↦ h2.1), fun hx ↦ ?_⟩
        rcases Thomas.onTreePath_adj_dichotomy hT hadj_f x with ⟨h1, _⟩ | ⟨h2, _⟩
        · exact Or.inl ⟨hx, h1⟩
        · exact Or.inr ⟨hx, h2⟩
      have hU_disj : Disjoint U₁ U₂ := by
        rw [Set.disjoint_iff]
        rintro x ⟨⟨_, h1⟩, ⟨_, h2⟩⟩
        exact (Thomas.onTreePath_adj_dichotomy hT hadj_f x).elim
          (fun h ↦ h.2 h2) (fun h ↦ h.2 h1)
      have hcard₁ : U₁.ncard < n := by
        rw [← hcard]
        exact Set.ncard_lt_ncard ⟨hU₁_sub, fun h ↦ hu₂_not_U₁ (h hu₂_U)⟩ (Set.toFinite U)
      have hcard₂ : U₂.ncard < n := by
        rw [← hcard]
        exact Set.ncard_lt_ncard ⟨hU₂_sub, fun h ↦ hu₁_not_U₂ (h hu₁_U)⟩ (Set.toFinite U)
      have hU₁_conv : IsTreeConvex T U₁ := isTreeConvex_side hT hU_conv hadj_f
      have hU₂_conv : IsTreeConvex T U₂ := isTreeConvex_side hT hU_conv hadj_f.symm
      let sub₁ : ι → Set ι := fun t ↦ sub t ∩ U₁
      let sub₂ : ι → Set ι := fun t ↦ sub t ∩ U₂
      have side_ord : ∀ {a b : ι} (hadj : T.Adj a b),
          let Ua := {x ∈ U | Thomas.OnTreePath T x b a}
          ∀ t ∈ Ua, ∀ u ∈ sub t ∩ Ua, ∀ v ∈ Ua \ (sub t ∩ Ua), T.Adj u v →
            ∀ x y : ι, Thomas.OnTreePathEdge T t v x y → μ s(u, v) ≤ μ s(x, y) := by
        intro a b hadj Ua t ht u ⟨hu_sub, _⟩ v ⟨hv_Ua, hv_not⟩ hadj_uv x y hxy
        exact hsub_ord t ht.1 u hu_sub v ⟨hv_Ua.1, fun hv_sub ↦ hv_not ⟨hv_sub, hv_Ua⟩⟩
          hadj_uv x y hxy
      obtain ⟨I₁, hI₁_U₁, hI₁_disj, hI₁_union⟩ :=
        ih U₁.ncard hcard₁ U₁ rfl ⟨u₁, hu₁_U₁⟩ hU₁_conv sub₁
          (fun _ _ ↦ Set.inter_subset_right)
          (fun t ht ↦ ⟨ht_mem t ht.1, ht⟩)
          (fun t ht x y hx hy z hz ↦ ⟨hsub_conv t ht.1 hx.1 hy.1 hz, hU₁_conv hx.2 hy.2 hz⟩)
          (side_ord hadj_f)
      obtain ⟨I₂, hI₂_U₂, hI₂_disj, hI₂_union⟩ :=
        ih U₂.ncard hcard₂ U₂ rfl ⟨u₂, hu₂_U₂⟩ hU₂_conv sub₂
          (fun _ _ ↦ Set.inter_subset_right)
          (fun t ht ↦ ⟨ht_mem t ht.1, ht⟩)
          (fun t ht x y hx hy z hz ↦ ⟨hsub_conv t ht.1 hx.1 hy.1 hz, hU₂_conv hx.2 hy.2 hz⟩)
          (side_ord hadj_f.symm)
      -- Key helper: if `s ∈ Ua` and `sub s` is not contained in `Ua`, then `a ∈ sub s`, `b ∈ sub
      -- s`,
      -- and `Ub ⊆ sub s`.
      have cross_helper : ∀ {a b : ι} (hadj : T.Adj a b) (heq_f : s(a, b) = s(u₁, u₂))
          (hb_U : b ∈ U),
          let Ua := {x ∈ U | Thomas.OnTreePath T x b a}
          let Ub := {x ∈ U | Thomas.OnTreePath T x a b}
          ∀ s ∈ Ua, ¬ (sub s ⊆ Ua) → a ∈ sub s ∧ b ∈ sub s ∧ Ub ⊆ sub s := by
        intro a b hadj heq_f hb_U Ua Ub s hs hnot_sub
        have hUa_Ub : Ua ∪ Ub = U := by
          rcases Sym2.eq_iff.1 heq_f with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact hU_union
          · rw [Set.union_comm]
            exact hU_union
        obtain ⟨w, hw_sub, hw_not_Ua⟩ := Set.not_subset.1 hnot_sub
        have hw_U : w ∈ U := hsub_U s hs.1 hw_sub
        have hw_Ub : w ∈ Ub := (hUa_Ub ▸ hw_U).resolve_left hw_not_Ua
        have ⟨ha_on, hb_on⟩ := Thomas.onTreePath_of_sides hT hadj hs.2 hw_Ub.2
        have ha_sub : a ∈ sub s := hsub_conv s hs.1 (ht_mem s hs.1) hw_sub ha_on
        have hb_sub : b ∈ sub s := hsub_conv s hs.1 (ht_mem s hs.1) hw_sub hb_on
        refine ⟨ha_sub, hb_sub, fun z hz ↦ ?_⟩
        by_contra hz_not
        obtain ⟨u, v, huv_edge, hu_in, hv_not⟩ :=
          Thomas.exists_onTreePathEdge_of_prop hT (· ∈ sub s) hb_sub hz_not
        have hb_Ub : b ∈ Ub := ⟨hb_U, Thomas.onTreePath_left T b a⟩
        have hu_Ub : u ∈ Ub := isTreeConvex_side hT hU_conv hadj.symm hb_Ub hz
          huv_edge.onTreePath_left
        have hv_Ub : v ∈ Ub := isTreeConvex_side hT hU_conv hadj.symm hb_Ub hz
          huv_edge.onTreePath_right
        have hab_sv : Thomas.OnTreePathEdge T s v a b := by
          rw [Thomas.onTreePathEdge_iff_not_reachable_deleteEdges]
          refine ⟨hadj, fun hreach ↦ ?_⟩
          have hsa : (T.deleteEdges {s(a, b)}).Reachable a s :=
            (reachable_deleteEdges_iff_onTreePath hT hadj s).2 hs.2
          have hvb : (T.deleteEdges {s(a, b)}).Reachable b v := by
            have h := (reachable_deleteEdges_iff_onTreePath hT hadj.symm v).2 hv_Ub.2
            rwa [Sym2.eq_swap] at h
          have he_ab : Thomas.OnTreePathEdge T a b a b := by
            rw [Thomas.onTreePathEdge_iff_mem_treePath hT]
            refine ⟨hadj, ?_⟩
            rw [← Thomas.eq_treePath hT hadj.toWalk hadj.isPath_toWalk]
            simp
          exact (Thomas.onTreePathEdge_iff_not_reachable_deleteEdges.1 he_ab).2
            (hsa.trans (hreach.trans hvb.symm))
        have hle_μ : μ s(u, v) ≤ μ s(a, b) :=
          hsub_ord s hs.1 u hu_in v ⟨hv_Ub.1, hv_not⟩ huv_edge.1 a b hab_sv
        have huv_EU : s(u, v) ∈ E_U := by
          rw [Finset.mem_filter]
          refine ⟨Finset.mem_univ _, T.mem_edgeSet.2 huv_edge.1, fun x hx ↦ ?_⟩
          rcases Sym2.mem_iff.1 hx with rfl | rfl
          · exact hu_Ub.1
          · exact hv_Ub.1
        have hmin_uv : μ s(u₁, u₂) ≤ μ s(u, v) := hf_min s(u, v) huv_EU
        rw [← heq_f] at hmin_uv
        have heq_μ : μ s(u, v) = μ s(a, b) := le_antisymm hle_μ hmin_uv
        have heq_e : s(u, v) = s(a, b) :=
          he_inj (T.mem_edgeSet.2 huv_edge.1) (T.mem_edgeSet.2 hadj) heq_μ
        have ha_not_Ub : a ∉ Ub := fun h ↦
          hadj.ne (Thomas.onTreePath_self T a b |>.1 h.2).symm
        rcases Sym2.eq_iff.1 heq_e with ⟨rfl, _⟩ | ⟨_, rfl⟩
        · exact ha_not_Ub hu_Ub
        · exact ha_not_Ub hv_Ub
      by_cases h1 : ∀ t ∈ I₁, sub t ⊆ U₁
      · by_cases h2 : ∀ t ∈ I₂, sub t ⊆ U₂
        · -- Both `I₁` and `I₂` have `sub t = subᵢ t`; take `I = I₁ ∪ I₂`.
          refine ⟨I₁ ∪ I₂, Set.union_subset (hI₁_U₁.trans hU₁_sub) (hI₂_U₂.trans hU₂_sub), ?_, ?_⟩
          · intro i hi j hj hne
            rcases hi with hi₁ | hi₂ <;> rcases hj with hj₁ | hj₂
            · have hi_eq : sub₁ i = sub i := Set.inter_eq_left.2 (h1 i hi₁)
              have hj_eq : sub₁ j = sub j := Set.inter_eq_left.2 (h1 j hj₁)
              rw [← hi_eq, ← hj_eq]
              exact hI₁_disj i hi₁ j hj₁ hne
            · exact Disjoint.mono (h1 i hi₁) (h2 j hj₂) hU_disj
            · exact Disjoint.mono (h2 i hi₂) (h1 j hj₁) hU_disj.symm
            · have hi_eq : sub₂ i = sub i := Set.inter_eq_left.2 (h2 i hi₂)
              have hj_eq : sub₂ j = sub j := Set.inter_eq_left.2 (h2 j hj₂)
              rw [← hi_eq, ← hj_eq]
              exact hI₂_disj i hi₂ j hj₂ hne
          · rw [Set.biUnion_union]
            have hU₁_eq : (⋃ i ∈ I₁, sub i) = U₁ := by
              rw [← hI₁_union]
              exact Set.iUnion₂_congr fun i hi ↦ (Set.inter_eq_left.2 (h1 i hi)).symm
            have hU₂_eq : (⋃ i ∈ I₂, sub i) = U₂ := by
              rw [← hI₂_union]
              exact Set.iUnion₂_congr fun i hi ↦ (Set.inter_eq_left.2 (h2 i hi)).symm
            rw [hU₁_eq, hU₂_eq, hU_union]
        · push Not at h2
          obtain ⟨s, hs, hnot⟩ := h2
          refine ⟨I₂, hI₂_U₂.trans hU₂_sub, ?_⟩
          rw [← hU_union, Set.union_comm]
          exact partition_of_crossing_member hu₂_U₂
            (fun t ht => by
              rw [Set.union_comm, hU_union]
              exact hsub_U t (hI₂_U₂.trans hU₂_sub ht))
            hI₂_disj hI₂_union (fun t ht hnot => by
              obtain ⟨ha, _, hcover⟩ :=
                cross_helper hadj_f.symm Sym2.eq_swap hu₁_U t (hI₂_U₂ ht) hnot
              exact ⟨ha, hcover⟩) hs hnot
      · push Not at h1
        obtain ⟨s, hs, hnot⟩ := h1
        refine ⟨I₁, hI₁_U₁.trans hU₁_sub, ?_⟩
        rw [← hU_union]
        exact partition_of_crossing_member hu₁_U₁
          (fun t ht => hU_union ▸ hsub_U t (hI₁_U₁.trans hU₁_sub ht))
          hI₁_disj hI₁_union (fun t ht hnot => by
            obtain ⟨ha, _, hcover⟩ := cross_helper hadj_f rfl hu₂_U t (hI₁_U₁ ht) hnot
            exact ⟨ha, hcover⟩) hs hnot

/-- **Graph Minors XVIII, (4.1)** (page 85, M. Saks):
"Let $T$ be a tree and let $\le$ be some linear order on $E(T)$. For each $t \in V(T)$, let
$T_t$ be a subtree of $T$ such that* - *$t \in V(T_t)$,* - *if $e \in E(T)$ has one end in
$V(T_t)$ and the other end in $V(T) \setminus V(T_t)$ and $f$ is an edge of the path of $T$
with first vertex $t$ and last edge $e$, then $e \le f$.* *Then there exists $I \subseteq
V(T)$ such that the sets $V(T_t)$ ($t \in I$) form a partition of $V(T)$." -/
theorem theorem_4_1_proof [Finite ι] [Nonempty ι] {T : SimpleGraph ι} (hT : T.IsTree)
    {Λ : Type*} [LinearOrder Λ] (μ : Sym2 ι → Λ)
    (he_inj : ∀ ⦃e₁ e₂ : Sym2 ι⦄, e₁ ∈ T.edgeSet → e₂ ∈ T.edgeSet → μ e₁ = μ e₂ → e₁ = e₂)
    (sub : ι → Set ι)
    (ht_mem : ∀ t : ι, t ∈ sub t)
    (hsub_conv : ∀ t : ι, IsTreeConvex T (sub t))
    (hsub_ord : ∀ (t u v : ι), u ∈ sub t → v ∉ sub t → T.Adj u v →
      ∀ x y : ι, Thomas.OnTreePathEdge T t v x y → μ s(u, v) ≤ μ s(x, y)) :
    ∃ I : Set ι, (∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (sub i) (sub j)) ∧
      (⋃ i ∈ I, sub i) = Set.univ := by
  obtain ⟨I, _, hdisj, hunion⟩ :=
    saks_lemma_aux hT μ he_inj Set.univ Set.univ_nonempty (fun _ _ _ _ _ _ ↦ Set.mem_univ _)
      sub (fun _ _ _ _ ↦ Set.mem_univ _) (fun t _ ↦ ht_mem t) (fun t _ ↦ hsub_conv t)
      (fun t _ u hu v hv ↦ hsub_ord t u v hu hv.2)
  exact ⟨I, hdisj, hunion⟩

/-! ## (4.2): Selecting a Basis of Isolating Locations -/

/-- For an edge `s(u, v)` of a standard decomposition `(T, τ)`, the separation
`(treeDecompSide T τ s(u, v) v, treeDecompSide T τ s(u, v) u)` is the `(𝒯 u, 𝒯 v)`-distinction. -/
theorem isDistinction_treeDecompSide_of_adj {Λ : Type w} [LinearOrder Λ] {n : ℕ}
    {G : Hypergraph α β} {lam : Hypergraph α β × Hypergraph α β → Λ}
    {θ : ℕ} {𝒯 : Fin n → Set (Hypergraph α β × Hypergraph α β)}
    {T : SimpleGraph (Fin n)} {τ : Fin n → Hypergraph α β}
    (h𝒯 : ∀ i : Fin n, GM10.IsTangle G θ (𝒯 i))
    (hstd : IsStandardDecomposition G lam 𝒯 T τ)
    {u v : Fin n} (hadj : T.Adj u v) :
    GM10.IsDistinction lam (𝒯 u) (𝒯 v)
      (GM10.treeDecompSide T τ s(u, v) v) (GM10.treeDecompSide T τ s(u, v) u) := by
  obtain ⟨e, _, he_path, _, A, B, hmAB, hdist_uv, _⟩ := hstd.path_min_isDistinction hadj.ne
  have he_eq : e = s(u, v) := by
    have hmem := he_path hadj.toWalk hadj.isPath_toWalk
    simpa using hmem
  subst he_eq
  rcases (makesSeparation_adj_iff τ hadj A B).1 hmAB with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exfalso
    have hu_in : (GM10.treeDecompSide T τ s(u, v) v, GM10.treeDecompSide T τ s(u, v) u) ∈ 𝒯 u := by
      have h := hstd.side_mem_tangle u v u hadj.symm (Reachable.refl u)
      rwa [Sym2.eq_swap] at h
    exact GM10.theorem_2_1_proof (h𝒯 u) hdist_uv.1.1 hu_in
  · exact hdist_uv

/-- For any two separations `(A, B)` and `(A', B')` made by the same edge `e` under `(T, τ)`,
`lam (A, B) = lam (A', B')`. -/
theorem lam_eq_of_makesSeparation {Λ : Type w} [LinearOrder Λ] [Fintype ι]
    {G : Hypergraph α β} {lam : Hypergraph α β × Hypergraph α β → Λ}
    {T : SimpleGraph ι} {τ : ι → Hypergraph α β}
    (hD : GM10.IsTreeDecomposition G T τ) (hlam : GM10.IsTieBreaker G lam)
    {e : Sym2 ι} {A B A' B' : Hypergraph α β}
    (hm : GM10.MakesSeparation T τ e A B) (hm' : GM10.MakesSeparation T τ e A' B') :
    lam (A, B) = lam (A', B') := by
  have hsep := isSeparation_of_makesSeparation hD hm
  have hsep' := isSeparation_of_makesSeparation hD hm'
  rcases hm with ⟨u, v, hadj, rfl, rfl, rfl⟩
  rw [(hlam.axiom1 hsep hsep')]
  rcases (makesSeparation_adj_iff τ hadj A' B').1 hm' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩

/-- **Claim (1)** in the proof of Graph Minors XVIII, (4.2) (pages 85–86):
If `e, e' ∈ E(T)` are distinct and make separations `(A, B), (A', B')` of `G`, then
`(A, B), (B, A) ≠ (A', B'), (B', A')`. -/
theorem lemma_4_2_claim_1 {Λ : Type w} [LinearOrder Λ] {n : ℕ}
    {G : Hypergraph α β} {lam : Hypergraph α β × Hypergraph α β → Λ}
    {θ : ℕ} {𝒯 : Fin n → Set (Hypergraph α β × Hypergraph α β)}
    {T : SimpleGraph (Fin n)} {τ : Fin n → Hypergraph α β}
    (h𝒯 : ∀ i : Fin n, GM10.IsTangle G θ (𝒯 i))
    (hstd : IsStandardDecomposition G lam 𝒯 T τ)
    {e e' : Sym2 (Fin n)} (hne : e ≠ e')
    {A B A' B' : Hypergraph α β}
    (hm : GM10.MakesSeparation T τ e A B)
    (hm' : GM10.MakesSeparation T τ e' A' B') :
    (A, B) ≠ (A', B') ∧ (B, A) ≠ (A', B') := by
  have hD := hstd.isTreeDecomposition
  rcases hm with ⟨i, j, hadj, rfl, rfl, rfl⟩
  rcases hm' with ⟨u, v, hadj', rfl, rfl, rfl⟩
  have hdist_ij := isDistinction_treeDecompSide_of_adj h𝒯 hstd hadj
  have hdist_ji : GM10.IsDistinction lam (𝒯 j) (𝒯 i)
      (GM10.treeDecompSide T τ s(i, j) i) (GM10.treeDecompSide T τ s(i, j) j) := by
    have h := isDistinction_treeDecompSide_of_adj h𝒯 hstd hadj.symm
    rwa [Sym2.eq_swap] at h
  have hnot_i : (GM10.treeDecompSide T τ s(i, j) i, GM10.treeDecompSide T τ s(i, j) j) ∉ 𝒯 i :=
    GM10.theorem_2_1_proof (h𝒯 i) hdist_ij.1.1
  have hnot_j : (GM10.treeDecompSide T τ s(i, j) j, GM10.treeDecompSide T τ s(i, j) i) ∉ 𝒯 j :=
    GM10.theorem_2_1_proof (h𝒯 j) hdist_ji.1.1
  -- Since `s(i, j) ≠ s(u, v)`, `i` and `j` are adjacent in `T \ s(u, v)`, hence in the same
  -- component of `T \ s(u, v)`.
  have hadj_del : (T.deleteEdges {s(u, v)}).Adj i j := by
    rw [deleteEdges_adj, Set.mem_singleton_iff]
    exact ⟨hadj, hne⟩
  have hboth :
      ((GM10.treeDecompSide T τ s(u, v) u, GM10.treeDecompSide T τ s(u, v) v) ∈ 𝒯 i ∧
        (GM10.treeDecompSide T τ s(u, v) u, GM10.treeDecompSide T τ s(u, v) v) ∈ 𝒯 j) ∨
      ((GM10.treeDecompSide T τ s(u, v) v, GM10.treeDecompSide T τ s(u, v) u) ∈ 𝒯 i ∧
        (GM10.treeDecompSide T τ s(u, v) v, GM10.treeDecompSide T τ s(u, v) u) ∈ 𝒯 j) := by
    rcases reachable_deleteEdges_dichotomy hD.isTree hadj' i with ⟨hi_u, _⟩ | ⟨hi_v, _⟩
    · right
      have hj_u : (T.deleteEdges {s(u, v)}).Reachable u j := hi_u.trans hadj_del.reachable
      have h1 := hstd.side_mem_tangle i v u hadj'.symm (by rwa [Sym2.eq_swap])
      have h2 := hstd.side_mem_tangle j v u hadj'.symm (by rwa [Sym2.eq_swap])
      rw [Sym2.eq_swap] at h1 h2
      exact ⟨h1, h2⟩
    · left
      have hj_v : (T.deleteEdges {s(u, v)}).Reachable v j := hi_v.trans hadj_del.reachable
      exact ⟨hstd.side_mem_tangle i u v hadj' hi_v, hstd.side_mem_tangle j u v hadj' hj_v⟩
  rcases hboth with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine ⟨fun heq ↦ hnot_i (heq.symm ▸ h1), fun heq ↦ hnot_j (heq.symm ▸ h2)⟩
  · refine ⟨fun heq ↦ hnot_j ?_, fun heq ↦ hnot_i ?_⟩
    · rcases Prod.ext_iff.1 heq with ⟨hA, hB⟩
      change (GM10.treeDecompSide T τ s(i, j) i = GM10.treeDecompSide T τ s(u, v) u) at hA
      change (GM10.treeDecompSide T τ s(i, j) j = GM10.treeDecompSide T τ s(u, v) v) at hB
      rw [hB, hA]
      exact h2
    · rcases Prod.ext_iff.1 heq with ⟨hA, hB⟩
      change (GM10.treeDecompSide T τ s(i, j) j = GM10.treeDecompSide T τ s(u, v) u) at hA
      change (GM10.treeDecompSide T τ s(i, j) i = GM10.treeDecompSide T τ s(u, v) v) at hB
      rw [hB, hA]
      exact h1

/-- **Claim (2)** in the proof of Graph Minors XVIII, (4.2) (page 86):
Let `t_i ∈ V(S_h)` be adjacent in `T` to `t_j ∈ V(T) \ V(S_h)`, and let `(A, B)` be the
`(𝒯_h, 𝒯_j)`-distinction; then `(A, B) ∈ 𝒯_k` for every `t_k ∈ V(T_h)`, and `(A, B)` is the
`(𝒯_i, 𝒯_j)`-distinction. -/
theorem lemma_4_2_claim_2 {Λ : Type w} [LinearOrder Λ] {n : ℕ}
    {G : Hypergraph α β} {lam : Hypergraph α β × Hypergraph α β → Λ}
    {θ : ℕ} {𝒯 L : Fin n → Set (Hypergraph α β × Hypergraph α β)}
    {T : SimpleGraph (Fin n)} {τ : Fin n → Hypergraph α β}
    (hlam : GM10.IsTieBreaker G lam)
    (h𝒯 : ∀ i : Fin n, GM10.IsTangle G θ (𝒯 i))
    (hiso : ∀ i : Fin n, Isolates G lam θ (𝒯 i) (L i))
    (hstd : IsStandardDecomposition G lam 𝒯 T τ)
    {h i j : Fin n}
    (hi_Th : L h ⊆ 𝒯 i) (hj_not_Th : ¬ L h ⊆ 𝒯 j)
    (hi_on_hj : Thomas.OnTreePath T h j i)
    (hadj : T.Adj i j)
    {A B : Hypergraph α β} (hdist_hj : GM10.IsDistinction lam (𝒯 h) (𝒯 j) A B) :
    (∀ k : Fin n, L h ⊆ 𝒯 k → (A, B) ∈ 𝒯 k) ∧
    GM10.IsDistinction lam (𝒯 i) (𝒯 j) A B := by
  have hD := hstd.isTreeDecomposition
  obtain ⟨⟨C, D⟩, hCD_Lh, hCD_not_j⟩ := Set.not_subset.1 hj_not_Th
  have hsep_CD : G.IsSeparation C D := (hiso h).isLocation.isSeparation hCD_Lh
  have hord_CD : separationOrder C D < θ := (hiso h).order_lt hCD_Lh
  have hDC_j : (D, C) ∈ 𝒯 j := ((h𝒯 j).axiom1 hsep_CD hord_CD).resolve_left hCD_not_j
  have ⟨hA_le_C, hD_le_B⟩ := (hiso h).distinction_le hCD_Lh (h𝒯 j) le_rfl hDC_j hdist_hj
  have hsep_AB : G.IsSeparation A B := (h𝒯 h).isSeparation hdist_hj.1.1
  have hord_AB : separationOrder A B < θ := (h𝒯 h).order_lt hdist_hj.1.1
  have hB_C_eq_G : B ∪ C = G := by
    have hle : B ∪ C ≤ G := GM10.union_le hsep_AB.right_le hsep_CD.left_le
    refine GM10.eq_of_le_of_vertexSet_eq_of_edgeSet_eq hle le_rfl
      (Set.Subset.antisymm hle.vertexSet_subset
        (hsep_CD.symm.vertexSet_union ▸ Set.union_subset_union_left _ hD_le_B.vertexSet_subset))
      (Set.Subset.antisymm hle.edgeSet_subset
        (hsep_CD.symm.edgeSet_union ▸ Set.union_subset_union_left _ hD_le_B.edgeSet_subset))
  have hall_k : ∀ k : Fin n, L h ⊆ 𝒯 k → (A, B) ∈ 𝒯 k := by
    intro k hk_Th
    have hCD_k : (C, D) ∈ 𝒯 k := hk_Th hCD_Lh
    have hBA_not_k : (B, A) ∉ 𝒯 k := fun hm ↦ by
      apply (h𝒯 k).axiom2 hm hCD_k hCD_k
      rw [GM10.union_assoc, GM10.union_self, hB_C_eq_G]
    exact ((h𝒯 k).axiom1 hsep_AB hord_AB).resolve_right hBA_not_k
  refine ⟨hall_k, ?_⟩
  have hAB_i : (A, B) ∈ 𝒯 i := hall_k i hi_Th
  have hAB_dist_ij : GM10.Distinguishes (𝒯 i) (𝒯 j) A B := ⟨hAB_i, hdist_hj.1.2⟩
  let A' := GM10.treeDecompSide T τ s(i, j) j
  let B' := GM10.treeDecompSide T τ s(i, j) i
  have hdist_ij : GM10.IsDistinction lam (𝒯 i) (𝒯 j) A' B' :=
    isDistinction_treeDecompSide_of_adj h𝒯 hstd hadj
  have hlam_1 : lam (A', B') ≤ lam (A, B) := hdist_ij.2 hAB_dist_ij
  -- Since `i` lies on `h T j` and `T.Adj i j`, `h` is reachable from `i` in `T \ s(i, j)`.
  have hh_reach_i : (T.deleteEdges {s(i, j)}).Reachable i h := by
    rw [reachable_deleteEdges_iff_onTreePath hD.isTree hadj]
    exact hi_on_hj
  have hA'B'_h : (A', B') ∈ 𝒯 h := by
    have hm := hstd.side_mem_tangle h j i hadj.symm (by rwa [Sym2.eq_swap])
    rwa [Sym2.eq_swap] at hm
  have hA'B'_dist_hj : GM10.Distinguishes (𝒯 h) (𝒯 j) A' B' := ⟨hA'B'_h, hdist_ij.1.2⟩
  have hlam_2 : lam (A, B) ≤ lam (A', B') := hdist_hj.2 hA'B'_dist_hj
  have hlam_eq : lam (A, B) = lam (A', B') := le_antisymm hlam_2 hlam_1
  have hsep_A'B' : G.IsSeparation A' B' := (h𝒯 i).isSeparation hdist_ij.1.1
  rcases (hlam.axiom1 hsep_AB hsep_A'B').1 hlam_eq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hdist_ij
  · exact (GM10.theorem_2_1_proof (h𝒯 j) hdist_hj.1.2 hdist_ij.1.2).elim

/-- **Claim (3)** in the proof of Graph Minors XVIII, (4.2) (page 86):
`T_h = {i : L h ⊆ 𝒯 i}` is a subtree of `T` (`IsTreeConvex T {i | L h ⊆ 𝒯 i}`). -/
theorem lemma_4_2_claim_3 {Λ : Type w} [LinearOrder Λ] {n : ℕ}
    {G : Hypergraph α β} {lam : Hypergraph α β × Hypergraph α β → Λ}
    {θ : ℕ} {𝒯 L : Fin n → Set (Hypergraph α β × Hypergraph α β)}
    {T : SimpleGraph (Fin n)} {τ : Fin n → Hypergraph α β}
    (hlam : GM10.IsTieBreaker G lam)
    (h𝒯 : ∀ i : Fin n, GM10.IsTangle G θ (𝒯 i))
    (hiso : ∀ i : Fin n, Isolates G lam θ (𝒯 i) (L i))
    (hstd : IsStandardDecomposition G lam 𝒯 T τ)
    (h : Fin n) :
    IsTreeConvex T {i : Fin n | L h ⊆ 𝒯 i} := by
  have hD := hstd.isTreeDecomposition
  let Th : Set (Fin n) := {i : Fin n | L h ⊆ 𝒯 i}
  let Sh : Set (Fin n) := {k : Fin n | ∀ x : Fin n, Thomas.OnTreePath T h k x → x ∈ Th}
  have hh_Sh : h ∈ Sh := by
    intro x hx
    have hxh : x = h := (Thomas.onTreePath_self T h x).1 hx
    exact hxh ▸ (hiso h).subset
  -- Show `Th ⊆ Sh`, hence `Sh = Th` and `Th` is tree-convex.
  have hTh_sub_Sh : ∀ k : Fin n, k ∉ Sh → k ∉ Th := by
    intro k hk_not_Sh hk_Th
    obtain ⟨i, j, hij_edge, hi_Sh, hj_not_Sh⟩ :=
      Thomas.exists_onTreePathEdge_of_prop hD.isTree (· ∈ Sh) hh_Sh hk_not_Sh
    have hi_Th : L h ⊆ 𝒯 i := hi_Sh i (Thomas.onTreePath_right T h i)
    have ⟨hi_on_hj, hj_on_ik, _, _⟩ :
        Thomas.OnTreePath T h j i ∧ Thomas.OnTreePath T i k j ∧
        ¬ Thomas.OnTreePath T h i j ∧ ¬ Thomas.OnTreePath T j k i := by
      rcases hij_edge.orient hD.isTree with h1 | ⟨h1, _, _, _⟩
      · exact h1
      · exact (hj_not_Sh fun x hx ↦ hi_Sh x (Thomas.onTreePath_trans_left hD.isTree h1 hx)).elim
    have hj_not_Th : ¬ L h ⊆ 𝒯 j := by
      intro hj_Th
      apply hj_not_Sh
      intro x hx
      rcases (Thomas.onTreePath_split_iff hD.isTree hi_on_hj).1 hx with hx_hi | hx_ij
      · exact hi_Sh x hx_hi
      · have hp : Thomas.treePath hD.isTree i j = hij_edge.1.toWalk :=
          (Thomas.eq_treePath hD.isTree hij_edge.1.toWalk hij_edge.1.isPath_toWalk).symm
        have hmem := (Thomas.onTreePath_iff_mem_treePath hD.isTree).1 hx_ij
        rw [hp, Walk.support_cons, Walk.support_nil, List.mem_cons, List.mem_singleton] at hmem
        rcases hmem with rfl | rfl
        · exact hi_Th
        · exact hj_Th
    have hhj_ne : h ≠ j := fun heq ↦ hj_not_Th (heq ▸ (hiso h).subset)
    obtain ⟨e₀, _, _, _, A₀, B₀, _, hdist_hj, _⟩ := hstd.path_min_isDistinction hhj_ne
    have ⟨hall_k, hdist_ij⟩ :=
      lemma_4_2_claim_2 hlam h𝒯 hiso hstd hi_Th hj_not_Th hi_on_hj hij_edge.1 hdist_hj
    have hAB_k : (A₀, B₀) ∈ 𝒯 k := hall_k k hk_Th
    -- On the other hand, `(A₀, B₀)` is the `(𝒯_i, 𝒯_j)`-distinction, so `(A₀, B₀)` is
    -- `(treeDecompSide T τ s(i, j) j, treeDecompSide T τ s(i, j) i)` and `k` is on the `j`-side!
    have hdist_ij' := isDistinction_treeDecompSide_of_adj h𝒯 hstd hij_edge.1
    have hlam_eq : lam (A₀, B₀) =
        lam (GM10.treeDecompSide T τ s(i, j) j, GM10.treeDecompSide T τ s(i, j) i) :=
      le_antisymm (hdist_ij.2 hdist_ij'.1) (hdist_ij'.2 hdist_ij.1)
    have hsep_AB₀ := (h𝒯 i).isSeparation hdist_ij.1.1
    have hsep_ij := (h𝒯 i).isSeparation hdist_ij'.1.1
    have heq_AB₀ : A₀ = GM10.treeDecompSide T τ s(i, j) j ∧
        B₀ = GM10.treeDecompSide T τ s(i, j) i := by
      rcases (hlam.axiom1 hsep_AB₀ hsep_ij).1 hlam_eq with h1 | ⟨rfl, rfl⟩
      · exact h1
      · exact (GM10.theorem_2_1_proof (h𝒯 j) hdist_ij.1.2 hdist_ij'.1.2).elim
    have hk_reach_j : (T.deleteEdges {s(i, j)}).Reachable j k := by
      have h := reachable_deleteEdges_iff_onTreePath hD.isTree hij_edge.1.symm k
      rw [Sym2.eq_swap] at h
      exact h.2 (Thomas.onTreePath_symm hj_on_ik)
    have hBA_k : (B₀, A₀) ∈ 𝒯 k := by
      rw [heq_AB₀.1, heq_AB₀.2]
      exact hstd.side_mem_tangle k i j hij_edge.1 hk_reach_j
    exact GM10.theorem_2_1_proof (h𝒯 k) hAB_k hBA_k
  intro u v hu hv x hx
  have hu_Sh : u ∈ Sh := by
    by_contra hu_not
    exact hTh_sub_Sh u hu_not hu
  have hv_Sh : v ∈ Sh := by
    by_contra hv_not
    exact hTh_sub_Sh v hv_not hv
  rcases Thomas.onTreePath_left_or_right hD.isTree h hx with hx_uh | hx_hv
  · exact hu_Sh x (Thomas.onTreePath_symm hx_uh)
  · exact hv_Sh x hx_hv

/-- **Claim (4)** in the proof of Graph Minors XVIII, (4.2) (page 86):
For each `e ∈ E(T)` with ends `t_i, t_j`, let `μ(e)` be the `λ`-order of the `(𝒯_i,
𝒯_j)`-distinction.
If `e ∈ E(T)` has one end `t_i ∈ V(T_h)` and the other `t_j ∈ V(T) \ V(T_h)`, and `f` is an edge of
the path of `T` between `t_h` and `t_j`, then `μ(e) ≤ μ(f)` (with strict inequality unless `e = f`).
-/
theorem lemma_4_2_claim_4 {Λ : Type w} [LinearOrder Λ] {n : ℕ}
    {G : Hypergraph α β} {lam : Hypergraph α β × Hypergraph α β → Λ}
    {θ : ℕ} {𝒯 L : Fin n → Set (Hypergraph α β × Hypergraph α β)}
    {T : SimpleGraph (Fin n)} {τ : Fin n → Hypergraph α β}
    (hlam : GM10.IsTieBreaker G lam)
    (h𝒯 : ∀ i : Fin n, GM10.IsTangle G θ (𝒯 i))
    (hiso : ∀ i : Fin n, Isolates G lam θ (𝒯 i) (L i))
    (hstd : IsStandardDecomposition G lam 𝒯 T τ)
    (h i j : Fin n) (hi_Th : L h ⊆ 𝒯 i) (hj_not_Th : ¬ L h ⊆ 𝒯 j) (hadj : T.Adj i j)
    (x y : Fin n) (hf_path : Thomas.OnTreePathEdge T h j x y) :
    lam (GM10.treeDecompSide T τ s(i, j) j, GM10.treeDecompSide T τ s(i, j) i) ≤
      lam (GM10.treeDecompSide T τ s(x, y) x, GM10.treeDecompSide T τ s(x, y) y) := by
  have hD := hstd.isTreeDecomposition
  have hconv := lemma_4_2_claim_3 hlam h𝒯 hiso hstd h
  have hi_on_hj : Thomas.OnTreePath T h j i := by
    rcases Thomas.onTreePath_adj_dichotomy hD.isTree hadj h with ⟨hon, _⟩ | ⟨hon, _⟩
    · exact hon
    · exfalso
      exact hj_not_Th (hconv (hiso h).subset hi_Th hon)
  have hhj_ne : h ≠ j := fun heq ↦ hj_not_Th (heq ▸ (hiso h).subset)
  obtain ⟨e₀, he₀_T, he₀_path, he₀_min, A₀, B₀, hm₀, hdist_hj, _⟩ :=
    hstd.path_min_isDistinction hhj_ne
  have ⟨_, hdist_ij⟩ :=
    lemma_4_2_claim_2 hlam h𝒯 hiso hstd hi_Th hj_not_Th hi_on_hj hadj hdist_hj
  have hdist_ij' := isDistinction_treeDecompSide_of_adj h𝒯 hstd hadj
  have hlam_eq : lam (GM10.treeDecompSide T τ s(i, j) j, GM10.treeDecompSide T τ s(i, j) i) =
      lam (A₀, B₀) :=
    le_antisymm (hdist_ij'.2 hdist_ij.1) (hdist_ij.2 hdist_ij'.1)
  rw [hlam_eq]
  exact he₀_min s(x, y) (T.mem_edgeSet.2 hf_path.1) hf_path.2 A₀ B₀
    (GM10.treeDecompSide T τ s(x, y) x) (GM10.treeDecompSide T τ s(x, y) y) hm₀
    ⟨x, y, hf_path.1, rfl, rfl, rfl⟩

/-- **Graph Minors XVIII, (4.2)** (page 85):
"Let $\mathcal{T}_j$ ($j \in J$) be distinct tangles of order $\theta$ in a hypergraph $G$,
let $\lambda$ be a tie-breaker in $G$, and for each $j \in J$ let $\mathcal{L}_j \subseteq
\mathcal{T}_j$ be a location which $\theta$-isolates $\mathcal{T}_j$ with respect to
$\lambda$. Then there exists $I \subseteq J$ such that for every $j \in J$ there is a unique
$i \in I$ with $\mathcal{L}_i \subseteq \mathcal{T}_j$." -/
theorem theorem_4_2_proof {Λ : Type w} [LinearOrder Λ] {n : ℕ}
    {G : Hypergraph α β} {lam : Hypergraph α β × Hypergraph α β → Λ}
    {θ : ℕ} {𝒯 L : Fin n → Set (Hypergraph α β × Hypergraph α β)}
    (hlam : GM10.IsTieBreaker G lam)
    (h𝒯 : ∀ i : Fin n, GM10.IsTangle G θ (𝒯 i))
    (hdist : Function.Injective 𝒯)
    (hiso : ∀ i : Fin n, Isolates G lam θ (𝒯 i) (L i)) :
    ∃ I : Set (Fin n), ∀ j : Fin n, ∃! i : Fin n, i ∈ I ∧ L i ⊆ 𝒯 j := by
  classical
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨∅, fun j ↦ j.elim0⟩
  · have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    obtain ⟨T, τ, hstd⟩ := theorem_2_6_proof G lam θ 𝒯 hn hlam h𝒯 hdist
    have hD := hstd.isTreeDecomposition
    let μ : Sym2 (Fin n) → Λ := fun e ↦
      if he : ∃ u v : Fin n, T.Adj u v ∧ e = s(u, v) then
        let u := he.choose
        let v := he.choose_spec.choose
        lam (GM10.treeDecompSide T τ s(u, v) u, GM10.treeDecompSide T τ s(u, v) v)
      else
        lam (G, G)
    have hμ_adj : ∀ {u v : Fin n}, T.Adj u v →
        μ s(u, v) = lam (GM10.treeDecompSide T τ s(u, v) u, GM10.treeDecompSide T τ s(u, v) v) := by
      intro u v hadj
      have hex : ∃ u' v' : Fin n, T.Adj u' v' ∧ s(u, v) = s(u', v') := ⟨u, v, hadj, rfl⟩
      have hμ_def : μ s(u, v) =
          lam (GM10.treeDecompSide T τ s(hex.choose, hex.choose_spec.choose) hex.choose,
            GM10.treeDecompSide T τ s(hex.choose, hex.choose_spec.choose) hex.choose_spec.choose)
              := by
        dsimp only [μ]
        split_ifs
        rfl
      rw [hμ_def]
      exact lam_eq_of_makesSeparation hD hlam
        ⟨hex.choose, hex.choose_spec.choose, hex.choose_spec.choose_spec.1,
          hex.choose_spec.choose_spec.2, rfl, rfl⟩
        ⟨u, v, hadj, rfl, rfl, rfl⟩
    have hμ_symm : ∀ {u v : Fin n}, T.Adj u v →
        lam (GM10.treeDecompSide T τ s(u, v) v, GM10.treeDecompSide T τ s(u, v) u) =
        lam (GM10.treeDecompSide T τ s(u, v) u, GM10.treeDecompSide T τ s(u, v) v) := by
      intro u v hadj
      exact lam_eq_of_makesSeparation hD hlam
        (makesSeparation_adj_iff τ hadj _ _ |>.2 (Or.inr ⟨rfl, rfl⟩))
        (makesSeparation_adj_iff τ hadj _ _ |>.2 (Or.inl ⟨rfl, rfl⟩))
    have he_inj : ∀ ⦃e₁ e₂ : Sym2 (Fin n)⦄,
        e₁ ∈ T.edgeSet → e₂ ∈ T.edgeSet → μ e₁ = μ e₂ → e₁ = e₂ := by
      intro e₁ e₂ he₁ he₂ hμ_eq
      rcases e₁ with ⟨u₁, v₁⟩
      rcases e₂ with ⟨u₂, v₂⟩
      have hadj₁ : T.Adj u₁ v₁ := T.mem_edgeSet.1 he₁
      have hadj₂ : T.Adj u₂ v₂ := T.mem_edgeSet.1 he₂
      rw [hμ_adj hadj₁, hμ_adj hadj₂] at hμ_eq
      have hsep₁ := (isSeparation_treeDecompSide hD hadj₁).1
      have hsep₂ := (isSeparation_treeDecompSide hD hadj₂).1
      by_contra hne
      have ⟨hne1, hne2⟩ := lemma_4_2_claim_1 h𝒯 hstd hne
        ⟨u₁, v₁, hadj₁, rfl, rfl, rfl⟩ ⟨u₂, v₂, hadj₂, rfl, rfl, rfl⟩
      rcases (hlam.axiom1 hsep₁ hsep₂).1 hμ_eq with ⟨hA, hB⟩ | ⟨hA, hB⟩
      · exact hne1 (Prod.ext hA hB)
      · exact hne2 (Prod.ext hB hA)
    let sub : Fin n → Set (Fin n) := fun h ↦ {i : Fin n | L h ⊆ 𝒯 i}
    obtain ⟨I, hdisj, hunion⟩ := theorem_4_1_proof hD.isTree μ he_inj sub
      (fun h ↦ (hiso h).subset)
      (lemma_4_2_claim_3 hlam h𝒯 hiso hstd)
      (fun h i j hi hj hadj x y hf ↦ by
        rw [hμ_adj hadj, ← hμ_symm hadj, hμ_adj hf.1]
        exact lemma_4_2_claim_4 hlam h𝒯 hiso hstd h i j hi hj hadj x y hf)
    refine ⟨I, fun j ↦ ?_⟩
    have hj_mem : j ∈ ⋃ i ∈ I, sub i := hunion.symm ▸ Set.mem_univ j
    rw [Set.mem_iUnion₂] at hj_mem
    obtain ⟨i, hi_I, hj_sub⟩ := hj_mem
    refine ⟨i, ⟨hi_I, hj_sub⟩, fun i' ⟨hi'_I, hj_sub'⟩ ↦ ?_⟩
    by_contra hne
    exact Set.disjoint_left.1 (hdisj i' hi'_I i hi_I hne) hj_sub' hj_sub

/-! ## (4.3): Enlargement of Isolating Locations in a Standard Decomposition -/

/-- **Claim (1)** in the proof of Graph Minors XVIII, (4.3) (page 87):
If `(A, B) ∈ vertexLocation T τ i`, then `(A, B)` has order `≤ (3/4) θ` and there exists
`(C_h, D_h) ∈ L i` such that `A ≤ C_h` and `D_h ≤ B`. -/
theorem lemma_4_3_claim_1 {Λ : Type w} [LinearOrder Λ] {n : ℕ}
    {G : Hypergraph α β} {lam : Hypergraph α β × Hypergraph α β → Λ}
    {θ : ℕ} {𝒯 L : Fin n → Set (Hypergraph α β × Hypergraph α β)}
    {T : SimpleGraph (Fin n)} {τ : Fin n → Hypergraph α β}
    (hlam : GM10.IsTieBreaker G lam)
    (h𝒯 : ∀ i : Fin n, GM10.IsTangle G θ (𝒯 i))
    (hiso : ∀ i : Fin n, Isolates G lam θ (𝒯 i) (L i))
    (hord_L : ∀ i : Fin n, 4 * locationOrder (L i) ≤ 3 * θ)
    (huniq : ∀ 𝒯' : Set (Hypergraph α β × Hypergraph α β),
      GM10.IsTangle G θ 𝒯' → ∃! i : Fin n, L i ⊆ 𝒯')
    (hstd : IsStandardDecomposition G lam 𝒯 T τ)
    (i : Fin n) {A B : Hypergraph α β}
    (hAB : (A, B) ∈ vertexLocation T τ i) :
    4 * separationOrder A B ≤ 3 * θ ∧
    ∃ p ∈ L i, A ≤ p.1 ∧ p.2 ≤ B := by
  have hD := hstd.isTreeDecomposition
  obtain ⟨j, hadj, heq_AB⟩ := hAB
  have hA_eq : A = GM10.treeDecompSide T τ s(j, i) j := congrArg Prod.fst heq_AB
  have hB_eq : B = GM10.treeDecompSide T τ s(j, i) i := congrArg Prod.snd heq_AB
  have hdist_ij : GM10.IsDistinction lam (𝒯 i) (𝒯 j) A B := by
    rw [hA_eq, hB_eq, Sym2.eq_swap]
    exact isDistinction_treeDecompSide_of_adj h𝒯 hstd hadj
  have hij_ne : i ≠ j := hadj.ne
  have hLi_not_Tj : ¬ L i ⊆ 𝒯 j := by
    intro hsub
    have h_eq := (huniq (𝒯 j) (h𝒯 j)).unique hsub (hiso j).subset
    exact hij_ne h_eq
  obtain ⟨⟨C, D⟩, hCD_Li, hCD_not_j⟩ := Set.not_subset.1 hLi_not_Tj
  have hsep_CD := (hiso i).isLocation.isSeparation hCD_Li
  have hord_CD_lt : separationOrder C D < θ := (hiso i).order_lt hCD_Li
  have hDC_j : (D, C) ∈ 𝒯 j := ((h𝒯 j).axiom1 hsep_CD hord_CD_lt).resolve_left hCD_not_j
  have ⟨hA_le_C, hD_le_B⟩ := (hiso i).distinction_le hCD_Li (h𝒯 j) le_rfl hDC_j hdist_ij
  have hCD_dist : GM10.Distinguishes (𝒯 i) (𝒯 j) C D := ⟨(hiso i).subset hCD_Li, hDC_j⟩
  have hlam_le : lam (A, B) ≤ lam (C, D) := hdist_ij.2 hCD_dist
  have hsep_AB := (h𝒯 i).isSeparation hdist_ij.1.1
  have hord_AB_le_CD : separationOrder A B ≤ separationOrder C D := by
    by_contra! hlt
    exact not_lt_of_ge hlam_le (hlam.axiom3 hsep_CD hsep_AB hlt)
  have hord_CD_le_loc : separationOrder C D ≤ locationOrder (L i) :=
    separationOrder_le_locationOrder (hiso i).isLocation hCD_Li
  have hord_bound : 4 * separationOrder A B ≤ 3 * θ := by
    have := hord_L i
    omega
  exact ⟨hord_bound, ⟨(C, D), hCD_Li, hA_le_C, hD_le_B⟩⟩

/-- **Claim (2)** in the proof of Graph Minors XVIII, (4.3) (page 87):
Each member `(A, B)` of `vertexLocation T τ i` is titanic in `G`. -/
theorem lemma_4_3_claim_2 {Λ : Type w} [LinearOrder Λ] {n : ℕ}
    {G : Hypergraph α β} {lam : Hypergraph α β × Hypergraph α β → Λ}
    {θ : ℕ} {𝒯 L : Fin n → Set (Hypergraph α β × Hypergraph α β)}
    {T : SimpleGraph (Fin n)} {τ : Fin n → Hypergraph α β}
    (hlam : GM10.IsTieBreaker G lam)
    (h𝒯 : ∀ i : Fin n, GM10.IsTangle G θ (𝒯 i))
    (hiso : ∀ i : Fin n, Isolates G lam θ (𝒯 i) (L i))
    (hord_L : ∀ i : Fin n, 4 * locationOrder (L i) ≤ 3 * θ)
    (huniq : ∀ 𝒯' : Set (Hypergraph α β × Hypergraph α β),
      GM10.IsTangle G θ 𝒯' → ∃! i : Fin n, L i ⊆ 𝒯')
    (hstd : IsStandardDecomposition G lam 𝒯 T τ)
    (i : Fin n) {A B : Hypergraph α β}
    (hAB : (A, B) ∈ vertexLocation T τ i) :
    GM10.IsTitanic G A B := by
  have ⟨hord_AB, _⟩ := lemma_4_3_claim_1 hlam h𝒯 hiso hord_L huniq hstd i hAB
  obtain ⟨j, hadj, heq_AB⟩ := hAB
  have hA_eq : A = GM10.treeDecompSide T τ s(j, i) j := congrArg Prod.fst heq_AB
  have hB_eq : B = GM10.treeDecompSide T τ s(j, i) i := congrArg Prod.snd heq_AB
  have hdist_ij : GM10.IsDistinction lam (𝒯 i) (𝒯 j) A B := by
    rw [hA_eq, hB_eq, Sym2.eq_swap]
    exact isDistinction_treeDecompSide_of_adj h𝒯 hstd hadj
  have hsep_AB := (h𝒯 i).isSeparation hdist_ij.1.1
  -- Show `(B, A)` is linked to `𝒯 j`.
  have hlink : IsLinkedTo (𝒯 j) B A := by
    refine ⟨hdist_ij.1.2, fun B' A' hB'A'_j hB_le_B' hA'_le_A ↦ ?_⟩
    by_contra! hlt
    have hsep_B'A' := (h𝒯 j).isSeparation hB'A'_j
    have hord_B'A'_lt : separationOrder B' A' < θ := (h𝒯 j).order_lt hB'A'_j
    have hord_A'B'_lt : separationOrder A' B' < θ := by
      rwa [GM10.separationOrder_comm]
    have hA'B'_i : (A', B') ∈ 𝒯 i :=
      GM10.theorem_2_9_proof (h𝒯 i) hdist_ij.1.1 hsep_B'A'.symm hord_A'B'_lt
        (Or.inr (Or.inl hA'_le_A.vertexSet_subset))
    have hdist_A'B' : GM10.Distinguishes (𝒯 i) (𝒯 j) A' B' := ⟨hA'B'_i, hB'A'_j⟩
    have hlam_le : lam (A, B) ≤ lam (A', B') := hdist_ij.2 hdist_A'B'
    have hlt_A'B' : separationOrder A' B' < separationOrder A B := by
      rwa [GM10.separationOrder_comm A' B', GM10.separationOrder_comm A B]
    exact not_lt_of_ge hlam_le (hlam.axiom3 hsep_B'A'.symm hsep_AB hlt_A'B')
  have hord_BA : 4 * separationOrder B A ≤ 3 * θ := by
    rwa [GM10.separationOrder_comm]
  exact theorem_3_3_proof (h𝒯 j) hlink hord_BA

/-- **Claim (3)** in the proof of Graph Minors XVIII, (4.3) (pages 87–88):
Let `part` be a partition of `ℒ* = vertexLocation T τ i` indexed by `p ∈ L i` such that every
`(A, B) ∈ part p` satisfies `A ≤ p.1` and `p.2 ≤ B`. Then for each `p = (C_h, D_h) ∈ L i`, there is
no tangle `𝒯` of order `θ` in `G` with `part p ∪ {(D_h, C_h)} ⊆ 𝒯`. -/
theorem lemma_4_3_claim_3 {Λ : Type w} [LinearOrder Λ] {n : ℕ}
    {G : Hypergraph α β} {lam : Hypergraph α β × Hypergraph α β → Λ}
    {θ : ℕ} {𝒯 L : Fin n → Set (Hypergraph α β × Hypergraph α β)}
    {T : SimpleGraph (Fin n)} {τ : Fin n → Hypergraph α β}
    (h𝒯 : ∀ i : Fin n, GM10.IsTangle G θ (𝒯 i))
    (hiso : ∀ i : Fin n, Isolates G lam θ (𝒯 i) (L i))
    (huniq : ∀ 𝒯' : Set (Hypergraph α β × Hypergraph α β),
      GM10.IsTangle G θ 𝒯' → ∃! i : Fin n, L i ⊆ 𝒯')
    (hstd : IsStandardDecomposition G lam 𝒯 T τ)
    (i : Fin n)
    {part : Hypergraph α β × Hypergraph α β → Set (Hypergraph α β × Hypergraph α β)}
    (henl : IsLocationEnlargementVia G (L i) (vertexLocation T τ i) part)
    {p : Hypergraph α β × Hypergraph α β} (hp : p ∈ L i)
    {𝒯' : Set (Hypergraph α β × Hypergraph α β)} (h𝒯' : GM10.IsTangle G θ 𝒯') :
    ¬ (part p ∪ {(p.2, p.1)} ⊆ 𝒯') := by
  have hD := hstd.isTreeDecomposition
  intro hsub_T'
  have hDC_T' : (p.2, p.1) ∈ 𝒯' := hsub_T' (Or.inr (Set.mem_singleton _))
  have hpart_T' : part p ⊆ 𝒯' := Set.Subset.trans Set.subset_union_left hsub_T'
  obtain ⟨j, ⟨hj_sub, _⟩⟩ := huniq 𝒯' h𝒯'
  have hij_ne : i ≠ j := by
    rintro rfl
    have hCD_T' : (p.1, p.2) ∈ 𝒯' := hj_sub hp
    exact GM10.theorem_2_1_proof h𝒯' hCD_T' hDC_T'
  obtain ⟨e₀, he₀_T, he₀_path, _, A₀, B₀, hm₀, hdist_ij, hdist_ji⟩ :=
    hstd.path_min_isDistinction hij_ne
  -- Since `i ≠ j`, `L j` is not a subset of `𝒯 i`.
  have hLj_not_Ti : ¬ L j ⊆ 𝒯 i := by
    intro hsub
    exact hij_ne ((huniq (𝒯 i) (h𝒯 i)).unique (hiso i).subset hsub)
  obtain ⟨⟨C, D⟩, hCD_Lj, hCD_not_i⟩ := Set.not_subset.1 hLj_not_Ti
  have hsep_CD := (hiso j).isLocation.isSeparation hCD_Lj
  have hord_CD : separationOrder C D < θ := (hiso j).order_lt hCD_Lj
  have hDC_i : (D, C) ∈ 𝒯 i := ((h𝒯 i).axiom1 hsep_CD hord_CD).resolve_left hCD_not_i
  -- Since `(B₀, A₀)` is the `(𝒯_j, 𝒯_i)`-distinction and `L j` `θ`-isolates `𝒯_j`, `D ≤ A₀`.
  have ⟨_, hD_le_A₀⟩ := (hiso j).distinction_le hCD_Lj (h𝒯 i) le_rfl hDC_i hdist_ji
  have hCD_T' : (C, D) ∈ 𝒯' := hj_sub hCD_Lj
  have hsep_B₀A₀ := (h𝒯 j).isSeparation hdist_ji.1.1
  have hord_B₀A₀ : separationOrder B₀ A₀ < θ := (h𝒯 j).order_lt hdist_ji.1.1
  have hB₀A₀_T' : (B₀, A₀) ∈ 𝒯' :=
    GM10.theorem_2_9_proof h𝒯' hCD_T' hsep_B₀A₀ hord_B₀A₀
      (Or.inl hD_le_A₀.vertexSet_subset)
  -- Let `j'` be the first neighbor of `i` on the path from `i` to `j` in `T`.
  obtain ⟨i₀, j', hij'_edge, hi₀_eq, hj'_ne_i⟩ :=
    Thomas.exists_onTreePathEdge_of_prop hD.isTree (i = ·) rfl hij_ne
  subst i₀
  have hadj_ij' : T.Adj i j' := hij'_edge.1
  let A' := GM10.treeDecompSide T τ s(j', i) j'
  let B' := GM10.treeDecompSide T τ s(j', i) i
  have hA'B'_loc : (A', B') ∈ vertexLocation T τ i := ⟨j', hadj_ij', rfl⟩
  -- Show `B' ≤ B₀`: the edge `e₀` lies on the path `i T j`.
  rcases hm₀ with ⟨u, v, hadj_uv, rfl, hA₀_def, hB₀_def⟩
  have he₀_edge : Thomas.OnTreePathEdge T i j u v := ⟨hadj_uv, he₀_path⟩
  -- In `T`, `i` is reachable from `v` in `T \ s(u, v)` (since `(A₀, B₀) ∈ 𝒯 i`).
  have hi_reach_v : (T.deleteEdges {s(u, v)}).Reachable v i := by
    rcases reachable_deleteEdges_dichotomy hD.isTree hadj_uv i with ⟨hi_u, _⟩ | ⟨hi_v, _⟩
    · exfalso
      have hBA_i : (B₀, A₀) ∈ 𝒯 i := by
        rw [hA₀_def, hB₀_def]
        have hm := hstd.side_mem_tangle i v u hadj_uv.symm (by rwa [Sym2.eq_swap])
        rwa [Sym2.eq_swap] at hm
      exact GM10.theorem_2_1_proof (h𝒯 i) hdist_ij.1.1 hBA_i
    · exact hi_v
  have hi_on_v : Thomas.OnTreePath T i u v :=
    (reachable_deleteEdges_iff_onTreePath hD.isTree hadj_uv.symm i).1
      (by rwa [Sym2.eq_swap] at hi_reach_v)
  have hu_ne_i : u ≠ i := by
    rintro rfl
    exact hadj_uv.ne ((Thomas.onTreePath_self T u v).1 hi_on_v).symm
  -- Also `j` is on the `j'`-side of `s(i, j')`:
  have hj_on_j' : Thomas.OnTreePath T j i j' := by
    rcases hij'_edge.orient hD.isTree with ⟨_, h2, _, _⟩ | ⟨h1, _, _, _⟩
    · exact Thomas.onTreePath_symm h2
    · exact (hj'_ne_i ((Thomas.onTreePath_self T i j').1 h1).symm).elim
  have hu_on_j' : Thomas.OnTreePath T u i j' := by
    rcases Thomas.onTreePath_adj_dichotomy hD.isTree hadj_ij' u with ⟨hu_i, _⟩ | ⟨hu_j', _⟩
    · exfalso
      have hu_ji := (Thomas.onTreePath_of_sides hD.isTree hadj_ij' hu_i hj_on_j').1
      exact hu_ne_i (Thomas.onTreePath_antisymm hD.isTree
        (Thomas.onTreePath_symm he₀_edge.onTreePath_left) (Thomas.onTreePath_symm hu_ji))
    · exact hu_j'
  have hB'_le_B₀ : B' ≤ B₀ := by
    classical
    dsimp only [B', GM10.treeDecompSide]
    rw [hB₀_def]
    dsimp only [GM10.treeDecompSide]
    refine biUnion_mono (fun s _ ↦ hD.le s) fun s hs ↦ ?_
    rw [Finset.mem_filter] at hs ⊢
    refine ⟨Finset.mem_univ s, ?_⟩
    rw [Sym2.eq_swap, reachable_deleteEdges_iff_onTreePath hD.isTree hadj_uv.symm]
    have hs_on : Thomas.OnTreePath T s j' i :=
      (reachable_deleteEdges_iff_onTreePath hD.isTree hadj_ij' s).1
        (by have hs2 := hs.2; rwa [Sym2.eq_swap] at hs2)
    rcases Thomas.onTreePath_adj_dichotomy hD.isTree hadj_uv.symm s with ⟨hs_v, _⟩ | ⟨hs_u, _⟩
    · exact hs_v
    · exfalso
      have h_si_u := (Thomas.onTreePath_of_sides hD.isTree hadj_uv hs_u hi_on_v).1
      have h_su_i := (Thomas.onTreePath_of_sides hD.isTree hadj_ij' hs_on hu_on_j').1
      exact hu_ne_i (Thomas.onTreePath_antisymm hD.isTree h_si_u h_su_i)
  have hsep_A'B' := (isSeparation_treeDecompSide hD hadj_ij'.symm).1
  have hdist_ij' : GM10.IsDistinction lam (𝒯 i) (𝒯 j') A' B' := by
    dsimp [A', B']
    rw [Sym2.eq_swap]
    exact isDistinction_treeDecompSide_of_adj h𝒯 hstd hadj_ij'
  have hord_B'A' : separationOrder B' A' < θ := by
    rw [GM10.separationOrder_comm]
    exact (h𝒯 i).order_lt hdist_ij'.1.1
  have hB'A'_T' : (B', A') ∈ 𝒯' :=
    GM10.theorem_2_9_proof h𝒯' hB₀A₀_T' hsep_A'B'.symm hord_B'A'
      (Or.inr (Or.inl hB'_le_B₀.vertexSet_subset))
  -- Now choose `q ∈ L i` such that `(A', B') ∈ part q`.
  have hA'B'_in_union : (A', B') ∈ ⋃ q ∈ L i, part q := henl.biUnion_eq.symm ▸ hA'B'_loc
  rw [Set.mem_iUnion₂] at hA'B'_in_union
  obtain ⟨q, hq_Li, hA'B'_part_q⟩ := hA'B'_in_union
  have ⟨hA'_le_q1, hq2_le_B'⟩ := henl.le_of_mem_part hq_Li hA'B'_part_q
  have hsep_q := (hiso i).isLocation.isSeparation hq_Li
  have hord_q : separationOrder q.1 q.2 < θ := (hiso i).order_lt hq_Li
  have hB'_q1_eq_G : B' ∪ q.1 = G := by
    have hle : B' ∪ q.1 ≤ G := GM10.union_le hsep_A'B'.right_le hsep_q.left_le
    refine GM10.eq_of_le_of_vertexSet_eq_of_edgeSet_eq hle le_rfl
      (Set.Subset.antisymm hle.vertexSet_subset
        (hsep_A'B'.symm.vertexSet_union ▸
          Set.union_subset_union_right _ hA'_le_q1.vertexSet_subset))
      (Set.Subset.antisymm hle.edgeSet_subset
        (hsep_A'B'.symm.edgeSet_union ▸
          Set.union_subset_union_right _ hA'_le_q1.edgeSet_subset))
  have hq12_not_T' : (q.1, q.2) ∉ 𝒯' := fun hm ↦ by
    apply h𝒯'.axiom2 hB'A'_T' hm hm
    rw [GM10.union_assoc, GM10.union_self, hB'_q1_eq_G]
  have hq21_T' : (q.2, q.1) ∈ 𝒯' := (h𝒯'.axiom1 hsep_q hord_q).resolve_left hq12_not_T'
  have hqp_eq : q = p := by
    by_contra hne
    have hq1_le_p2 : q.1 ≤ p.2 := (hiso i).isLocation.left_le_right hq_Li hp hne
    have hq2_p2_eq_G : q.2 ∪ p.2 = G := by
      have hle : q.2 ∪ p.2 ≤ G :=
        GM10.union_le hsep_q.right_le ((hiso i).isLocation.isSeparation hp).right_le
      refine GM10.eq_of_le_of_vertexSet_eq_of_edgeSet_eq hle le_rfl
        (Set.Subset.antisymm hle.vertexSet_subset
          (hsep_q.symm.vertexSet_union ▸
            Set.union_subset_union_right _ hq1_le_p2.vertexSet_subset))
        (Set.Subset.antisymm hle.edgeSet_subset
          (hsep_q.symm.edgeSet_union ▸
            Set.union_subset_union_right _ hq1_le_p2.edgeSet_subset))
    apply h𝒯'.axiom2 hq21_T' hDC_T' hDC_T'
    rw [GM10.union_assoc, GM10.union_self, hq2_p2_eq_G]
  subst hqp_eq
  have hA'B'_T' : (A', B') ∈ 𝒯' := hpart_T' hA'B'_part_q
  exact GM10.theorem_2_1_proof h𝒯' hA'B'_T' hB'A'_T'

/-- **Claim (4)** in the proof of Graph Minors XVIII, (4.3) (page 88):
Let `ℒ' = {(A, B ∩ C_h) : (A, B) ∈ part p}` for `p = (C_h, D_h) ∈ L i`. There is no tangle in
`C_h` of order `θ` including `ℒ'`. -/
theorem lemma_4_3_claim_4 {Λ : Type w} [LinearOrder Λ] {n : ℕ}
    {G : Hypergraph α β} {lam : Hypergraph α β × Hypergraph α β → Λ}
    {θ : ℕ} {𝒯 L : Fin n → Set (Hypergraph α β × Hypergraph α β)}
    {T : SimpleGraph (Fin n)} {τ : Fin n → Hypergraph α β}
    (h𝒯 : ∀ i : Fin n, GM10.IsTangle G θ (𝒯 i))
    (hiso : ∀ i : Fin n, Isolates G lam θ (𝒯 i) (L i))
    (huniq : ∀ 𝒯' : Set (Hypergraph α β × Hypergraph α β),
      GM10.IsTangle G θ 𝒯' → ∃! i : Fin n, L i ⊆ 𝒯')
    (hstd : IsStandardDecomposition G lam 𝒯 T τ)
    (i : Fin n)
    {part : Hypergraph α β × Hypergraph α β → Set (Hypergraph α β × Hypergraph α β)}
    (henl : IsLocationEnlargementVia G (L i) (vertexLocation T τ i) part)
    {p : Hypergraph α β × Hypergraph α β} (hp : p ∈ L i)
    {𝒯' : Set (Hypergraph α β × Hypergraph α β)} (h𝒯' : GM10.IsTangle p.1 θ 𝒯') :
    ¬ ((fun q ↦ (q.1, q.2 ∩ p.1)) '' part p ⊆ 𝒯') := by
  intro hsub_T'
  have hsep_p := (hiso i).isLocation.isSeparation hp
  have hord_p : separationOrder p.1 p.2 < θ := (hiso i).order_lt hp
  let 𝒯_G : Set (Hypergraph α β × Hypergraph α β) :=
    {q | G.IsSeparation q.1 q.2 ∧ separationOrder q.1 q.2 < θ ∧
      (q.1 ∩ p.1, q.2 ∩ p.1) ∈ 𝒯'}
  have h𝒯_G : GM10.IsTangle G θ 𝒯_G := theorem_2_1_proof hsep_p.left_le h𝒯'
  refine lemma_4_3_claim_3 h𝒯 hiso huniq hstd i henl hp h𝒯_G ?_
  rintro q (hq_part | hq_eq)
  · have hq_loc : q ∈ vertexLocation T τ i := henl.part_subset hp hq_part
    obtain ⟨j, hadj, heq_q⟩ := hq_loc
    have hq_sep : G.IsSeparation q.1 q.2 := by
      rw [congrArg Prod.fst heq_q, congrArg Prod.snd heq_q]
      exact (isSeparation_treeDecompSide hstd.isTreeDecomposition hadj.symm).1
    have hq_ord : separationOrder q.1 q.2 < θ := by
      rw [congrArg Prod.fst heq_q, congrArg Prod.snd heq_q, Sym2.eq_swap]
      exact (h𝒯 i).order_lt (isDistinction_treeDecompSide_of_adj h𝒯 hstd hadj).1.1
    have ⟨hq1_le_p1, _⟩ := henl.le_of_mem_part hp hq_part
    have hq1_inter : q.1 ∩ p.1 = q.1 := by
      rw [GM10.inter_comm, inter_self_of_le hq1_le_p1]
    refine ⟨hq_sep, hq_ord, ?_⟩
    rw [hq1_inter]
    exact hsub_T' ⟨q, hq_part, rfl⟩
  · rw [Set.mem_singleton_iff] at hq_eq
    subst hq_eq
    have hsep_DC : G.IsSeparation p.2 p.1 := hsep_p.symm
    have hord_DC : separationOrder p.2 p.1 < θ := by
      rwa [GM10.separationOrder_comm]
    refine ⟨hsep_DC, hord_DC, ?_⟩
    have hsep_inter : p.1.IsSeparation (p.2 ∩ p.1) (p.1 ∩ p.1) :=
      isSeparation_inter_of_le hsep_p.left_le hsep_DC
    have hord_inter : separationOrder (p.2 ∩ p.1) (p.1 ∩ p.1) < θ :=
      separationOrder_inter_le.trans_lt hord_DC
    have hnot_swap : (p.1 ∩ p.1, p.2 ∩ p.1) ∉ 𝒯' := fun hm ↦
      h𝒯'.axiom3 hm (by rw [GM10.inter_self])
    exact (h𝒯'.axiom1 hsep_inter hord_inter).resolve_right hnot_swap

private theorem isLocation_inter_part {G : Hypergraph α β}
    {ℒ ℒ_star : Set (Hypergraph α β × Hypergraph α β)}
    {part : Hypergraph α β × Hypergraph α β → Set (Hypergraph α β × Hypergraph α β)}
    (henl : IsLocationEnlargementVia G ℒ ℒ_star part)
    {p : Hypergraph α β × Hypergraph α β} (hp : p ∈ ℒ) :
    GM10.IsLocation p.1 ((fun q ↦ (q.1, q.2 ∩ p.1)) '' part p) ∧
    (∀ ⦃q⦄, q ∈ part p → (q.1 ∩ (q.2 ∩ p.1)) = q.1 ∩ q.2) ∧
    locationOrder ((fun q ↦ (q.1, q.2 ∩ p.1)) '' part p) ≤ locationOrder ℒ_star := by
  have hsep_p := henl.isLocation_left.isSeparation hp
  have hinter_eq : ∀ ⦃q⦄, q ∈ part p → (q.1 ∩ (q.2 ∩ p.1)) = q.1 ∩ q.2 := by
    intro q hq
    have hq1_le_p1 := (henl.le_of_mem_part hp hq).1
    rw [← GM10.inter_assoc, GM10.inter_comm q.1 q.2, GM10.inter_assoc,
      GM10.inter_comm q.1 p.1, inter_self_of_le hq1_le_p1, GM10.inter_comm]
  have hloc : GM10.IsLocation p.1 ((fun q ↦ (q.1, q.2 ∩ p.1)) '' part p) := by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨q, hq, rfl⟩
      have hq_sep := henl.isLocation_right.isSeparation (henl.part_subset hp hq)
      have hq1_le_p1 := (henl.le_of_mem_part hp hq).1
      have hq1_inter : q.1 ∩ p.1 = q.1 := by
        rw [GM10.inter_comm, inter_self_of_le hq1_le_p1]
      simpa [hq1_inter] using isSeparation_inter_of_le hsep_p.left_le hq_sep
    · rintro _ ⟨q₁, hq₁, rfl⟩ _ ⟨q₂, hq₂, rfl⟩ hne
      have hq_ne : q₁ ≠ q₂ :=
        fun heq ↦ hne (congrArg (fun q : Hypergraph α β × Hypergraph α β ↦ (q.1, q.2 ∩ p.1)) heq)
      have hq₁_le_q₂ := henl.isLocation_right.left_le_right
        (henl.part_subset hp hq₁) (henl.part_subset hp hq₂) hq_ne
      have hq₁_le_p1 := (henl.le_of_mem_part hp hq₁).1
      have hq₂_p1_le : q₂.2 ∩ p.1 ≤ G :=
        GM10.inter_le (henl.isLocation_right.isSeparation (henl.part_subset hp hq₂)).right_le
          hsep_p.left_le
      rw [GM10.le_iff_of_le (henl.isLocation_right.isSeparation (henl.part_subset hp hq₁)).left_le
        hq₂_p1_le]
      exact ⟨Set.subset_inter hq₁_le_q₂.vertexSet_subset hq₁_le_p1.vertexSet_subset,
        Set.subset_inter hq₁_le_q₂.edgeSet_subset hq₁_le_p1.edgeSet_subset⟩
  refine ⟨hloc, hinter_eq, ?_⟩
  unfold locationOrder
  by_cases hne : (((fun p ↦ separationOrder p.1 p.2) '' ((fun q ↦ (q.1, q.2 ∩ p.1)) '' part
    p))).Nonempty
  · refine csSup_le hne ?_
    rintro _ ⟨_, ⟨q, hq, rfl⟩, rfl⟩
    have hord_eq : separationOrder q.1 (q.2 ∩ p.1) = separationOrder q.1 q.2 :=
      congrArg (fun H : Hypergraph α β ↦ H.vertexSet.ncard) (hinter_eq hq)
    dsimp only
    rw [hord_eq]
    exact separationOrder_le_locationOrder henl.isLocation_right (henl.part_subset hp hq)
  · rw [Set.not_nonempty_iff_eq_empty.1 hne, csSup_empty]
    exact Nat.zero_le _

private theorem isLocation_part_union_swap {G : Hypergraph α β}
    {ℒ ℒ_star : Set (Hypergraph α β × Hypergraph α β)}
    {part : Hypergraph α β × Hypergraph α β → Set (Hypergraph α β × Hypergraph α β)}
    (henl : IsLocationEnlargementVia G ℒ ℒ_star part)
    {p : Hypergraph α β × Hypergraph α β} (hp : p ∈ ℒ) :
    GM10.IsLocation G (part p ∪ {(p.2, p.1)}) := by
  have hsep_p := henl.isLocation_left.isSeparation hp
  refine ⟨?_, ?_⟩
  · rintro q (hq | hq)
    · exact henl.isLocation_right.isSeparation (henl.part_subset hp hq)
    · rw [Set.mem_singleton_iff] at hq
      subst hq
      exact hsep_p.symm
  · rintro q₁ (hq₁ | hq₁) q₂ (hq₂ | hq₂) hne
    · exact henl.isLocation_right.left_le_right
        (henl.part_subset hp hq₁) (henl.part_subset hp hq₂) hne
    · rw [Set.mem_singleton_iff] at hq₂
      subst hq₂
      exact (henl.le_of_mem_part hp hq₁).1
    · rw [Set.mem_singleton_iff] at hq₁
      subst hq₁
      exact (henl.le_of_mem_part hp hq₂).2
    · rw [Set.mem_singleton_iff] at hq₁ hq₂
      exact (hne (hq₁.trans hq₂.symm)).elim

private theorem locationCore_part_union_swap {G : Hypergraph α β}
    {ℒ ℒ_star : Set (Hypergraph α β × Hypergraph α β)}
    {part : Hypergraph α β × Hypergraph α β → Set (Hypergraph α β × Hypergraph α β)}
    (henl : IsLocationEnlargementVia G ℒ ℒ_star part)
    {p : Hypergraph α β × Hypergraph α β} (hp : p ∈ ℒ) :
    GM10.locationCore G (part p ∪ {(p.2, p.1)}) =
      GM10.locationCore p.1 ((fun q ↦ (q.1, q.2 ∩ p.1)) '' part p) := by
  have hsep_p := henl.isLocation_left.isSeparation hp
  have hloc₁ := isLocation_part_union_swap henl hp
  have hloc₂ := (isLocation_inter_part henl hp).1
  refine GM10.eq_of_le_of_vertexSet_eq_of_edgeSet_eq (locationCore_le hloc₁)
    ((locationCore_le hloc₂).trans hsep_p.left_le) ?_ ?_
  · ext v
    simp only [GM10.locationCore, Set.mem_sep_iff, Set.mem_union,
      Set.mem_singleton_iff, Set.mem_image]
    constructor
    · rintro ⟨_, hq⟩
      refine ⟨hq (p.2, p.1) (Or.inr rfl), ?_⟩
      rintro _ ⟨q, hq_mem, rfl⟩
      exact ⟨hq q (Or.inl hq_mem), hq (p.2, p.1) (Or.inr rfl)⟩
    · rintro ⟨hvp₁, hq⟩
      refine ⟨hsep_p.left_le.vertexSet_subset hvp₁, ?_⟩
      rintro q (hq_mem | rfl)
      · exact (hq (q.1, q.2 ∩ p.1) ⟨q, hq_mem, rfl⟩).1
      · exact hvp₁
  · ext e
    simp only [GM10.locationCore, Set.mem_sep_iff, Set.mem_union,
      Set.mem_singleton_iff, Set.mem_image]
    constructor
    · rintro ⟨_, hq⟩
      refine ⟨hq (p.2, p.1) (Or.inr rfl), ?_⟩
      rintro _ ⟨q, hq_mem, rfl⟩
      exact ⟨hq q (Or.inl hq_mem), hq (p.2, p.1) (Or.inr rfl)⟩
    · rintro ⟨hep₁, hq⟩
      refine ⟨hsep_p.left_le.edgeSet_subset hep₁, ?_⟩
      rintro q (hq_mem | rfl)
      · exact (hq (q.1, q.2 ∩ p.1) ⟨q, hq_mem, rfl⟩).1
      · exact hep₁

private theorem locationTreeWidth_part_union_swap_le {G : Hypergraph α β}
    {ℒ ℒ_star : Set (Hypergraph α β × Hypergraph α β)}
    {part : Hypergraph α β × Hypergraph α β → Set (Hypergraph α β × Hypergraph α β)}
    (henl : IsLocationEnlargementVia G ℒ ℒ_star part)
    {p : Hypergraph α β × Hypergraph α β} (hp : p ∈ ℒ) :
    locationTreeWidth G (part p ∪ {(p.2, p.1)}) ≤
      locationTreeWidth p.1 ((fun q ↦ (q.1, q.2 ∩ p.1)) '' part p) +
        (separationOrder p.1 p.2 : ℤ) := by
  classical
  let ℒ₁ := part p ∪ {(p.2, p.1)}
  let ℒ₂ := (fun q ↦ (q.1, q.2 ∩ p.1)) '' part p
  let H₁ := locationHeart G ℒ₁
  let H₂ := locationHeart p.1 ℒ₂
  have hloc₁ : GM10.IsLocation G ℒ₁ := isLocation_part_union_swap henl hp
  have ⟨hloc₂, hinter_eq, _⟩ := isLocation_inter_part henl hp
  have hcore_eq : GM10.locationCore G ℒ₁ = GM10.locationCore p.1 ℒ₂ :=
    locationCore_part_union_swap henl hp
  have hVH : H₁.vertexSet = H₂.vertexSet := by
    change (GM10.locationCore G ℒ₁).vertexSet = (GM10.locationCore p.1 ℒ₂).vertexSet
    rw [hcore_eq]
  have hsep_p := henl.isLocation_left.isSeparation hp
  -- `V(p.1 ∩ p.2) ⊆ H₁.vertexSet` since `(p.2, p.1) ∈ ℒ₁`.
  have hZ_sub : (p.1 ∩ p.2).vertexSet ⊆ H₁.vertexSet := by
    change (p.1 ∩ p.2).vertexSet ⊆ (GM10.locationCore G ℒ₁).vertexSet
    rw [GM10.inter_comm, ← (theorem_2_3_2 hloc₁ (Or.inr (Set.mem_singleton _))).2]
    exact Set.inter_subset_right
  -- Take a tree-decomposition `(T', τ')` of `H₂` attaining `treeWidthPlusOne H₂`.
  have hex_D₂ : {w : ℕ | ∃ (γ : Type) (_ : Fintype γ) (T' : SimpleGraph γ)
      (τ' : γ → Hypergraph α (β ⊕ (Hypergraph α β × Hypergraph α β))),
      GM10.IsTreeDecomposition H₂ T' τ' ∧ GM10.treeDecompWidthPlusOne τ' = w}.Nonempty := by
    refine ⟨GM10.treeDecompWidthPlusOne (fun _ : Unit ↦ H₂), Unit, inferInstance, ⊥,
      fun _ ↦ H₂, ?_, rfl⟩
    refine ⟨⟨⟨fun _ _ ↦ Reachable.refl _⟩, fun u p hp ↦ ?_⟩, fun _ ↦ le_rfl, ?_,
      fun u v hne ↦ (hne (Subsingleton.elim u v)).elim, fun _ _ _ _ ↦ GM10.inter_le le_rfl le_rfl⟩
    · cases p with
      | nil => exact (Walk.not_isCycle_nil hp).elim
      | cons h _ => exact h.elim
    · refine GM10.eq_of_le_of_vertexSet_eq_of_edgeSet_eq (biUnion_le fun _ _ ↦ le_rfl) le_rfl ?_ ?_
      · ext v; simp [biUnion]
      · ext e; simp [biUnion]
  obtain ⟨γ, hfin_γ, T', τ', hD', hw'⟩ := Nat.sInf_mem hex_D₂
  let _ : Fintype γ := hfin_γ
  have hγ_ne : Nonempty γ := hD'.isTree.connected.nonempty
  let t₀ : γ := Classical.arbitrary γ
  let Z : Set α := (p.1 ∩ p.2).vertexSet
  -- Define bags `τ₁ t` of `H₁` by adding `Z` to every bag and `Sum.inr (p.2, p.1)` to `τ₁ t₀`
  -- (if `(p.2, p.1) ∉ part p`).
  let edgeCond : γ → β ⊕ (Hypergraph α β × Hypergraph α β) → Prop := fun t e ↦
    match e with
    | Sum.inl b => Sum.inl b ∈ (τ' t).edgeSet
    | Sum.inr q =>
        if q ∈ part p then Sum.inr (q.1, q.2 ∩ p.1) ∈ (τ' t).edgeSet
        else q = (p.2, p.1) ∧ t = t₀
  let τ₁ : γ → Hypergraph α (β ⊕ (Hypergraph α β × Hypergraph α β)) := fun t ↦
    { vertexSet := (τ' t).vertexSet ∪ Z
      edgeSet := {e ∈ H₁.edgeSet | edgeCond t e}
      Inc e v := e ∈ {e ∈ H₁.edgeSet | edgeCond t e} ∧ H₁.Inc e v
      vertex_mem_of_inc e v h := by
        rcases h with ⟨⟨he_H₁, he_cond⟩, hinc⟩
        cases e with
        | inl b =>
          left
          have hinc₂ : H₂.Inc (Sum.inl b) v := by
            change (GM10.locationCore p.1 ℒ₂).Inc b v
            rw [← hcore_eq]
            exact hinc
          exact (τ' t).vertex_mem_of_inc
            ((GM10.inc_iff_of_le (hD'.le t) he_cond).2 hinc₂)
        | inr q =>
          dsimp only [edgeCond] at he_cond
          split_ifs at he_cond with hq_part
          · left
            have hq_mem₂ : (q.1, q.2 ∩ p.1) ∈ ℒ₂ := ⟨q, hq_part, rfl⟩
            have hsep₂ := hloc₂.isSeparation hq_mem₂
            have hsub₂ : ((q.1, q.2 ∩ p.1).1 ∩ (q.1, q.2 ∩ p.1).2).vertexSet ⊆
                (GM10.locationCore p.1 ℒ₂).vertexSet := by
              rw [← (theorem_2_3_2 hloc₂ hq_mem₂).2]
              exact Set.inter_subset_right
            have hinc₂ : H₂.Inc (Sum.inr (q.1, q.2 ∩ p.1)) v := by
              refine ⟨hq_mem₂, hsep₂, hsub₂, ?_⟩
              dsimp only
              rw [hinter_eq hq_part]
              exact hinc.2.2.2
            exact (τ' t).vertex_mem_of_inc
              ((GM10.inc_iff_of_le (hD'.le t) he_cond).2 hinc₂)
          · right
            rcases he_cond with ⟨rfl, rfl⟩
            have hv : v ∈ (p.2 ∩ p.1).vertexSet := hinc.2.2.2
            rwa [GM10.inter_comm] at hv
      edge_mem_of_inc _ _ h := h.1
      vertexSet_finite := (τ' t).vertexSet_finite.union (p.1 ∩ p.2).vertexSet_finite
      edgeSet_finite := H₁.edgeSet_finite.subset fun _ h ↦ h.1 }
  have hle_τ₁ : ∀ t : γ, τ₁ t ≤ H₁ := fun t ↦
    ⟨Set.union_subset ((hD'.le t).vertexSet_subset.trans hVH.symm.subset) hZ_sub,
      fun _ h ↦ h.1, fun e he ↦ Set.ext fun v ↦ ⟨fun h ↦ ⟨he, h⟩, fun h ↦ h.2⟩⟩
  have hdisj_τ₁ : ∀ ⦃t t' : γ⦄, t ≠ t' → (τ₁ t ∩ τ₁ t').edgeSet = ∅ := by
    intro t t' hne
    ext e
    simp only [GM10.inter_edgeSet, τ₁, Set.mem_inter_iff, Set.mem_sep_iff,
      Set.mem_empty_iff_false, iff_false]
    rintro ⟨⟨_, hc₁⟩, ⟨_, hc₂⟩⟩
    cases e with
    | inl b =>
      have hmem : Sum.inl b ∈ (τ' t ∩ τ' t').edgeSet := ⟨hc₁, hc₂⟩
      rw [hD'.edgeSet_inter_eq hne] at hmem
      exact hmem
    | inr q =>
      dsimp only [edgeCond] at hc₁ hc₂
      split_ifs at hc₁ hc₂ with hq_part
      · have hmem : Sum.inr (q.1, q.2 ∩ p.1) ∈ (τ' t ∩ τ' t').edgeSet := ⟨hc₁, hc₂⟩
        rw [hD'.edgeSet_inter_eq hne] at hmem
        exact hmem
      · exact hne (hc₁.2.trans hc₂.2.symm)
  have hD₁ : GM10.IsTreeDecomposition H₁ T' τ₁ := by
    refine ⟨hD'.isTree, hle_τ₁, ?_, hdisj_τ₁, fun t₁ t₂ t₃ hon ↦ ?_⟩
    · refine GM10.eq_of_le_of_vertexSet_eq_of_edgeSet_eq
        (biUnion_le fun t _ ↦ hle_τ₁ t) le_rfl ?_ ?_
      · ext v
        simp only [biUnion, Set.mem_iUnion, Finset.mem_univ, exists_true_left, τ₁, Set.mem_union]
        constructor
        · rintro ⟨t, hvt | hvZ⟩
          · exact hVH.symm ▸ (hD'.le t).vertexSet_subset hvt
          · exact hZ_sub hvZ
        · intro hv₁
          have hv₂ : v ∈ (Hypergraph.biUnion Finset.univ τ').vertexSet := by
            rw [hD'.biUnion_eq, ← hVH]
            exact hv₁
          simp only [biUnion, Set.mem_iUnion, Finset.mem_univ, exists_true_left] at hv₂
          rcases hv₂ with ⟨t, hvt⟩
          exact ⟨t, Or.inl hvt⟩
      · ext e
        simp only [biUnion, Set.mem_iUnion, Finset.mem_univ, exists_true_left, τ₁, Set.mem_sep_iff]
        constructor
        · rintro ⟨_, he₁, _⟩
          exact he₁
        · intro he₁
          rcases he₁ with ⟨b, hb, rfl⟩ | ⟨q, ⟨hq_mem, hq_sep, hq_sub⟩, rfl⟩
          · have hb₂ : Sum.inl b ∈ (Hypergraph.biUnion Finset.univ τ').edgeSet := by
              rw [hD'.biUnion_eq]
              exact Or.inl ⟨b, hcore_eq ▸ hb, rfl⟩
            simp only [biUnion, Set.mem_iUnion, Finset.mem_univ, exists_true_left] at hb₂
            rcases hb₂ with ⟨t, hbt⟩
            exact ⟨t, ⟨Or.inl ⟨b, hb, rfl⟩, hbt⟩⟩
          · by_cases hq_part : q ∈ part p
            · have hq_mem₂ : (q.1, q.2 ∩ p.1) ∈ ℒ₂ := ⟨q, hq_part, rfl⟩
              have hsub₂ : ((q.1, q.2 ∩ p.1).1 ∩ (q.1, q.2 ∩ p.1).2).vertexSet ⊆
                  (GM10.locationCore p.1 ℒ₂).vertexSet := by
                rw [← (theorem_2_3_2 hloc₂ hq_mem₂).2]
                exact Set.inter_subset_right
              have hq₂ : Sum.inr (q.1, q.2 ∩ p.1) ∈
                  (Hypergraph.biUnion Finset.univ τ').edgeSet := by
                rw [hD'.biUnion_eq]
                exact Or.inr ⟨(q.1, q.2 ∩ p.1),
                  ⟨hq_mem₂, hloc₂.isSeparation hq_mem₂, hsub₂⟩, rfl⟩
              simp only [biUnion, Set.mem_iUnion, Finset.mem_univ, exists_true_left] at hq₂
              rcases hq₂ with ⟨t, hqt⟩
              refine ⟨t, ⟨Or.inr ⟨q, ⟨hq_mem, hq_sep, hq_sub⟩, rfl⟩, ?_⟩⟩
              dsimp only [edgeCond]
              split_ifs
              exact hqt
            · have hq_eq : q = (p.2, p.1) := by
                rcases hq_mem with h1 | h2
                · exact (hq_part h1).elim
                · exact Set.mem_singleton_iff.1 h2
              refine ⟨t₀, ⟨Or.inr ⟨q, ⟨hq_mem, hq_sep, hq_sub⟩, rfl⟩, ?_⟩⟩
              dsimp only [edgeCond]
              split_ifs
              exact ⟨hq_eq, rfl⟩
    · rw [GM10.le_iff_of_le (GM10.inter_le (hle_τ₁ t₁) (hle_τ₁ t₃)) (hle_τ₁ t₂)]
      refine ⟨?_, ?_⟩
      · intro v ⟨hv₁, hv₃⟩
        rcases hv₁ with hv₁ | hvZ
        · rcases hv₃ with hv₃ | hvZ
          · exact Or.inl ((hD'.inter_le hon).vertexSet_subset ⟨hv₁, hv₃⟩)
          · exact Or.inr hvZ
        · exact Or.inr hvZ
      · by_cases hne : t₁ = t₃
        · subst hne
          have ht₂_eq : t₂ = t₁ := (Thomas.onTreePath_self T' t₁ t₂).1 hon
          subst ht₂_eq
          rw [GM10.inter_self]
        · rw [hdisj_τ₁ hne]
          exact Set.empty_subset _
  have htw₁_le : GM10.treeWidthPlusOne H₁ ≤ GM10.treeDecompWidthPlusOne τ₁ :=
    GM10.treeWidthPlusOne_le_of_isTreeDecomposition hD₁
  have hwidth_le : GM10.treeDecompWidthPlusOne τ₁ ≤
      GM10.treeDecompWidthPlusOne τ' + separationOrder p.1 p.2 := by
    unfold GM10.treeDecompWidthPlusOne
    refine csSup_le (Set.range_nonempty _) ?_
    rintro _ ⟨t, rfl⟩
    have hcard_union : ((τ' t).vertexSet ∪ Z).ncard ≤
        (τ' t).vertexSet.ncard + Z.ncard :=
      Set.ncard_union_le (τ' t).vertexSet Z
    have h_le_t : (τ' t).vertexSet.ncard ≤
        sSup (Set.range fun u : γ ↦ (τ' u).vertexSet.ncard) :=
      le_csSup (Set.finite_range _).bddAbove ⟨t, rfl⟩
    exact hcard_union.trans (Nat.add_le_add_right h_le_t _)
  have hplus_le : GM10.treeWidthPlusOne H₁ ≤
      GM10.treeWidthPlusOne H₂ + separationOrder p.1 p.2 := by
    have hw'_eq : GM10.treeDecompWidthPlusOne τ' = GM10.treeWidthPlusOne H₂ := hw'
    rw [← hw'_eq]
    exact htw₁_le.trans hwidth_le
  unfold locationTreeWidth GM10.treeWidth
  change (GM10.treeWidthPlusOne H₁ : ℤ) - 1 ≤
    (GM10.treeWidthPlusOne H₂ : ℤ) - 1 + (separationOrder p.1 p.2 : ℤ)
  omega

/-- **Graph Minors XVIII, (4.3)** (page 87):
"4.3. *Let $\lambda$ be a tie-breaker in a hypergraph $G$, let $\theta \ge 2$, and let
$\mathcal{T}_1, \dots, \mathcal{T}_n$ be distinct tangles in $G$, each of order $\theta$, where
$n \ge 1$. For $1 \le i \le n$ let $\mathcal{L}_i \subseteq \mathcal{T}_i$ be a location of order
$\le \frac{3}{4}\theta$ which $\theta$-isolates $\mathcal{T}_i$; and suppose that for every tangle
$\mathcal{T}$ in $G$ of order $\theta$, there is a unique $i$ with $1 \le i \le n$ such that
$\mathcal{L}_i \subseteq \mathcal{T}$. Let $(T, \tau)$ be a standard tree-decomposition of $G$
relative to $\mathcal{T}_1, \dots, \mathcal{T}_n$, where $V(T) = \{t_1, \dots, t_n\}$ and $t_i$
represents $\mathcal{T}_i$ for $1 \le i \le n$. Then for $1 \le i \le n$, the location of $t_i$ in
$(T, \tau)$ is an enlargement of $\mathcal{L}_i$ by tree-width $\le \frac{9}{4}\theta$.*" -/
theorem theorem_4_3_proof {Λ : Type w} [LinearOrder Λ] {n : ℕ}
    {G : Hypergraph α β} {lam : Hypergraph α β × Hypergraph α β → Λ}
    {θ : ℕ} (hθ : 2 ≤ θ)
    {𝒯 L : Fin n → Set (Hypergraph α β × Hypergraph α β)}
    {T : SimpleGraph (Fin n)} {τ : Fin n → Hypergraph α β}
    (hlam : GM10.IsTieBreaker G lam)
    (h𝒯 : ∀ i : Fin n, GM10.IsTangle G θ (𝒯 i))
    (hiso : ∀ i : Fin n, Isolates G lam θ (𝒯 i) (L i))
    (hord_L : ∀ i : Fin n, 4 * locationOrder (L i) ≤ 3 * θ)
    (huniq : ∀ 𝒯' : Set (Hypergraph α β × Hypergraph α β),
      GM10.IsTangle G θ 𝒯' → ∃! i : Fin n, L i ⊆ 𝒯')
    (hstd : IsStandardDecomposition G lam 𝒯 T τ)
    (i : Fin n) :
    IsLocationEnlargementByTreeWidth G (L i) (vertexLocation T τ i) ((9 / 4 : ℚ) * θ) := by
  classical
  have hD := hstd.isTreeDecomposition
  have hloc_star : GM10.IsLocation G (vertexLocation T τ i) := theorem_2_4_proof hD i
  -- Use Claim (1) to assign each `q ∈ vertexLocation T τ i` to a unique `p ∈ L i`.
  have hex_p : ∀ q, ∃ p, q ∈ vertexLocation T τ i → p ∈ L i ∧ q.1 ≤ p.1 ∧ p.2 ≤ q.2 := by
    intro q
    by_cases hq : q ∈ vertexLocation T τ i
    · obtain ⟨p, hp, h1, h2⟩ := (lemma_4_3_claim_1 hlam h𝒯 hiso hord_L huniq hstd i hq).2
      exact ⟨p, fun _ ↦ ⟨hp, h1, h2⟩⟩
    · exact ⟨(G, G), fun h ↦ (hq h).elim⟩
  let pick : Hypergraph α β × Hypergraph α β → Hypergraph α β × Hypergraph α β :=
    fun q ↦ (hex_p q).choose
  let part : Hypergraph α β × Hypergraph α β → Set (Hypergraph α β × Hypergraph α β) :=
    fun p ↦ {q ∈ vertexLocation T τ i | pick q = p}
  have henl : IsLocationEnlargementVia G (L i) (vertexLocation T τ i) part := by
    refine ⟨(hiso i).isLocation, hloc_star, fun p _ q hq ↦ hq.1,
      fun p₁ _ p₂ _ hne ↦ Set.disjoint_left.2 fun q hq₁ hq₂ ↦ hne (hq₁.2.symm.trans hq₂.2),
      ?_, fun p _ q ⟨hq_loc, hq_pick⟩ ↦ ?_⟩
    · ext q
      simp only [Set.mem_iUnion, part, Set.mem_sep_iff]
      exact ⟨fun ⟨_, _, hq, _⟩ ↦ hq, fun hq ↦ ⟨pick q, ((hex_p q).choose_spec hq).1, hq, rfl⟩⟩
    · subst hq_pick
      exact ((hex_p q).choose_spec hq_loc).2
  have hnonneg : (0 : ℚ) ≤ (9 / 4 : ℚ) * θ := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (by decide : (0 : ℚ) < 4), zero_mul]
    exact_mod_cast Nat.zero_le (9 * θ)
  refine ⟨hnonneg, part, henl, fun p hp ↦ ?_⟩
  let ℒ' := (fun q ↦ (q.1, q.2 ∩ p.1)) '' part p
  have ⟨hloc', hinter_eq, hord'_le⟩ := isLocation_inter_part henl hp
  have hord_star_lt : locationOrder (vertexLocation T τ i) < θ := by
    rw [locationOrder_lt_iff hloc_star (by omega)]
    intro q hq
    have h4 := (lemma_4_3_claim_1 hlam h𝒯 hiso hord_L huniq hstd i hq).1
    omega
  have hord'_lt : locationOrder ℒ' < θ := hord'_le.trans_lt hord_star_lt
  have htitanic' : ∀ ⦃r⦄, r ∈ ℒ' → GM10.IsTitanic p.1 r.1 r.2 := by
    rintro _ ⟨q, hq_part, rfl⟩
    have hq_tit : GM10.IsTitanic G q.1 q.2 :=
      lemma_4_3_claim_2 hlam h𝒯 hiso hord_L huniq hstd i (henl.part_subset hp hq_part)
    have hsep' : p.1.IsSeparation q.1 (q.2 ∩ p.1) :=
      hloc'.isSeparation (p := (q.1, q.2 ∩ p.1)) ⟨q, hq_part, rfl⟩
    exact (theorem_3_1_proof hq_tit.1 hsep' (hinter_eq hq_part).symm).1 hq_tit
  have h34 := theorem_3_4_proof hloc' htitanic' hθ hord'_lt
  rcases h34 with ⟨𝒯', h𝒯', hsub'⟩ | htw'_bound
  · exact (lemma_4_3_claim_4 h𝒯 hiso huniq hstd i henl hp h𝒯' hsub').elim
  · have htw_le := locationTreeWidth_part_union_swap_le henl hp
    have hp_ord_le : 4 * separationOrder p.1 p.2 ≤ 3 * θ := by
      have h1 := separationOrder_le_locationOrder (hiso i).isLocation hp
      have h2 := hord_L i
      omega
    have htw_int : locationTreeWidth G (part p ∪ {(p.2, p.1)}) * 4 ≤ 9 * (θ : ℤ) := by
      omega
    have htw_rat : (locationTreeWidth G (part p ∪ {(p.2, p.1)}) : ℚ) * 4 ≤ 9 * (θ : ℚ) := by
      exact_mod_cast htw_int
    rw [div_mul_eq_mul_div, le_div_iff₀ (by decide : (0 : ℚ) < 4)]
    exact htw_rat

/-! ## (4.4): Main Structure Theorem of Section 4 -/

private theorem tangles_finite (G : Hypergraph α β) (θ : ℕ) :
    {𝒯 : Set (Hypergraph α β × Hypergraph α β) | GM10.IsTangle G θ 𝒯}.Finite := by
  refine ((separations_finite G).powerset).subset fun 𝒯 h𝒯 p hp ↦ h𝒯.isSeparation hp

private theorem isTangle_truncate {G : Hypergraph α β} {θ θ' : ℕ}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)}
    (h𝒯 : GM10.IsTangle G θ 𝒯) (hθ' : 1 ≤ θ') (hle : θ' ≤ θ) :
    GM10.IsTangle G θ' {p ∈ 𝒯 | separationOrder p.1 p.2 < θ'} where
  one_le := hθ'
  isSeparation _ _ h := h𝒯.isSeparation h.1
  order_lt _ _ h := h.2
  axiom1 A B hsep hord := by
    rcases h𝒯.axiom1 hsep (hord.trans_le hle) with h1 | h2
    · exact Or.inl ⟨h1, hord⟩
    · exact Or.inr ⟨h2, by rwa [GM10.separationOrder_comm]⟩
  axiom2 _ _ _ _ _ _ h1 h2 h3 := h𝒯.axiom2 h1.1 h2.1 h3.1
  axiom3 _ _ h := h𝒯.axiom3 h.1

private theorem isolates_mono {Λ : Type*} [LE Λ] {G : Hypergraph α β}
    {lam : Hypergraph α β × Hypergraph α β → Λ} {θ θ' : ℕ}
    {𝒯 ℒ : Set (Hypergraph α β × Hypergraph α β)}
    (hiso : Isolates G lam θ 𝒯 ℒ) (hle : θ ≤ θ') :
    Isolates G lam θ' 𝒯 ℒ where
  isLocation := hiso.isLocation
  subset := hiso.subset
  locationOrder_lt := hiso.locationOrder_lt.trans_le hle
  order_lt _ _ h := (hiso.order_lt h).trans_le hle
  distinction_le _ _ hCD _ _ h𝒯' hle' hDC _ _ hdist :=
    hiso.distinction_le hCD h𝒯' (hle.trans hle') hDC hdist

/-- **Graph Minors XVIII, (4.4)** (page 88):
"4.4. *Let $\lambda$ be a tie-breaker in a hypergraph $G$, and let $\theta \ge 1$ be an integer.
For each tangle $\mathcal{T}$ in $G$ of order $\ge \theta$ let
$\mathcal{L}(\mathcal{T}) \subseteq \mathcal{T}$ be a location which $\theta$-isolates
$\mathcal{T}$, and let $G$ have a tangle of order $\ge \frac{4}{3}\theta$. Then there is a
tree-decomposition $(T, \tau)$ of $G$ with the following properties:*
- *(T, \tau) is proper and rotund,*
- *for each $e \in E(T)$, the separations made by $e$ under $(T, \tau)$ are robust,*
- *for each $t \in V(T)$, let $\mathcal{L}$ be the location of $t$ in $(T, \tau)$; then there is a
  tangle $\mathcal{T}$ in $G$ of order $\ge \frac{4}{3}\theta$ with
  $\mathcal{L} \subseteq \mathcal{T}$, such that $\mathcal{L}$ is an enlargement of
  $\mathcal{L}(\mathcal{T})$ by tree-width $\le 3\theta + 1$.*" -/
theorem theorem_4_4_proof {Λ : Type w} [LinearOrder Λ]
    (G : Hypergraph α β) (lam : Hypergraph α β × Hypergraph α β → Λ)
    (hlam : GM10.IsTieBreaker G lam)
    (θ : ℕ) (hθ : 1 ≤ θ)
    (L : Set (Hypergraph α β × Hypergraph α β) → Set (Hypergraph α β × Hypergraph α β))
    (hiso : ∀ ⦃θ' : ℕ⦄ ⦃𝒯 : Set (Hypergraph α β × Hypergraph α β)⦄,
      θ ≤ θ' → GM10.IsTangle G θ' 𝒯 → Isolates G lam θ 𝒯 (L 𝒯))
    (hex_tangle : ∃ (θ₀ : ℕ) (𝒯₀ : Set (Hypergraph α β × Hypergraph α β)),
      4 * θ ≤ 3 * θ₀ ∧ GM10.IsTangle G θ₀ 𝒯₀) :
    ∃ (n : ℕ) (T : SimpleGraph (Fin n)) (τ : Fin n → Hypergraph α β),
      1 ≤ n ∧
      GM10.IsTreeDecomposition G T τ ∧
      IsProper G T τ ∧
      IsRotund G T τ ∧
      (∀ ⦃e : Sym2 (Fin n)⦄, e ∈ T.edgeSet → ∀ ⦃A B : Hypergraph α β⦄,
        GM10.MakesSeparation T τ e A B → GM10.IsRobust G A B) ∧
      (∀ i : Fin n, ∃ (θ' : ℕ) (𝒯 : Set (Hypergraph α β × Hypergraph α β)),
        4 * θ ≤ 3 * θ' ∧
        GM10.IsTangle G θ' 𝒯 ∧
        vertexLocation T τ i ⊆ 𝒯 ∧
        IsLocationEnlargementByTreeWidth G (L 𝒯) (vertexLocation T τ i) (3 * θ + 1)) := by
  classical
  -- Let `θ'` be the least integer with `3 * θ' ≥ 4 * θ`, namely `(4 * θ + 2) / 3`.
  let θ' : ℕ := (4 * θ + 2) / 3
  have hθ'_ge : 4 * θ ≤ 3 * θ' := by omega
  have hθ'_le : 3 * θ' ≤ 4 * θ + 2 := by omega
  have hθ'_two : 2 ≤ θ' := by omega
  have hθ_le_θ' : θ ≤ θ' := by omega
  -- Construct a tangle of order `θ'` in `G` by truncating `𝒯₀`.
  obtain ⟨θ₀, 𝒯₀, hθ₀_ge, h𝒯₀⟩ := hex_tangle
  have hθ'_le_θ₀ : θ' ≤ θ₀ := by omega
  let 𝒯₁ := {p ∈ 𝒯₀ | separationOrder p.1 p.2 < θ'}
  have h𝒯₁ : GM10.IsTangle G θ' 𝒯₁ := isTangle_truncate h𝒯₀ (by omega) hθ'_le_θ₀
  -- Enumerate all tangles of order `θ'` in `G`.
  let S := {𝒯 : Set (Hypergraph α β × Hypergraph α β) | GM10.IsTangle G θ' 𝒯}
  have hS_fin : S.Finite := tangles_finite G θ'
  let S_fin := hS_fin.toFinset
  let m := Fintype.card S_fin
  have hm_pos : 1 ≤ m := Fintype.card_pos_iff.2 ⟨⟨𝒯₁, hS_fin.mem_toFinset.2 h𝒯₁⟩⟩
  let eS : Fin m ≃ S_fin := (Fintype.equivFin S_fin).symm
  let 𝒯_all : Fin m → Set (Hypergraph α β × Hypergraph α β) := fun j ↦ (eS j).1
  have h𝒯_all : ∀ j : Fin m, GM10.IsTangle G θ' (𝒯_all j) :=
    fun j ↦ (hS_fin.mem_toFinset.1 (eS j).2)
  have hinj_all : Function.Injective 𝒯_all :=
    fun j₁ j₂ heq ↦ eS.injective (Subtype.ext heq)
  have hiso_all : ∀ j : Fin m, Isolates G lam θ' (𝒯_all j) (L (𝒯_all j)) :=
    fun j ↦ isolates_mono (hiso hθ_le_θ' (h𝒯_all j)) hθ_le_θ'
  -- Apply (4.2) to obtain `I ⊆ Fin m`.
  obtain ⟨I, hI_uniq⟩ := theorem_4_2_proof hlam h𝒯_all hinj_all hiso_all
  let I_fin := I.toFinset
  let n := Fintype.card I_fin
  have hn_pos : 1 ≤ n := by
    obtain ⟨j₀, _⟩ := eS.surjective ⟨𝒯₁, hS_fin.mem_toFinset.2 h𝒯₁⟩
    obtain ⟨i₀, ⟨hi₀_I, _⟩, _⟩ := hI_uniq j₀
    exact Fintype.card_pos_iff.2 ⟨⟨i₀, Set.mem_toFinset.2 hi₀_I⟩⟩
  let eI : Fin n ≃ I_fin := (Fintype.equivFin I_fin).symm
  let 𝒯_sub : Fin n → Set (Hypergraph α β × Hypergraph α β) := fun i ↦ 𝒯_all (eI i).1
  have h𝒯_sub : ∀ i : Fin n, GM10.IsTangle G θ' (𝒯_sub i) := fun i ↦ h𝒯_all (eI i).1
  have hinj_sub : Function.Injective 𝒯_sub :=
    fun i₁ i₂ heq ↦ eI.injective (Subtype.ext (hinj_all heq))
  have hiso_sub : ∀ i : Fin n, Isolates G lam θ' (𝒯_sub i) (L (𝒯_sub i)) :=
    fun i ↦ hiso_all (eI i).1
  have hord_L_sub : ∀ i : Fin n, 4 * locationOrder (L (𝒯_sub i)) ≤ 3 * θ' := by
    intro i
    have hlt : locationOrder (L (𝒯_sub i)) < θ :=
      (hiso hθ_le_θ' (h𝒯_sub i)).locationOrder_lt
    omega
  have huniq_sub : ∀ 𝒯' : Set (Hypergraph α β × Hypergraph α β),
      GM10.IsTangle G θ' 𝒯' → ∃! i : Fin n, L (𝒯_sub i) ⊆ 𝒯' := by
    intro 𝒯' h𝒯'
    obtain ⟨j, hj⟩ := eS.surjective ⟨𝒯', hS_fin.mem_toFinset.2 h𝒯'⟩
    have hj_eq : 𝒯_all j = 𝒯' := congrArg Subtype.val hj
    rw [← hj_eq]
    obtain ⟨i_m, ⟨hi_I, hi_sub⟩, hi_uniq⟩ := hI_uniq j
    obtain ⟨i, hi_eq⟩ := eI.surjective ⟨i_m, Set.mem_toFinset.2 hi_I⟩
    have hi_val : (eI i).1 = i_m := congrArg Subtype.val hi_eq
    refine ⟨i, ?_, fun i' hi'_sub ↦ ?_⟩
    · dsimp only [𝒯_sub]
      rwa [hi_val]
    · have hi'_I : (eI i').1 ∈ I := Set.mem_toFinset.1 (eI i').2
      have heq_m : (eI i').1 = i_m := hi_uniq (eI i').1 ⟨hi'_I, hi'_sub⟩
      exact eI.injective (Subtype.ext (heq_m.trans hi_val.symm))
  -- Apply (2.6) and (2.7) to get a standard decomposition `(T, τ)` relative to `𝒯_sub`.
  obtain ⟨T, τ, hstd⟩ := theorem_2_6_proof G lam θ' 𝒯_sub hn_pos hlam h𝒯_sub hinj_sub
  have ⟨hproper, hrotund, hrobust⟩ := theorem_2_7_proof hlam h𝒯_sub hstd
  refine ⟨n, T, τ, hn_pos, hstd.isTreeDecomposition, hproper, hrotund, hrobust, fun i ↦ ?_⟩
  have henl_i := theorem_4_3_proof hθ'_two hlam h𝒯_sub hiso_sub hord_L_sub huniq_sub hstd i
  rcases henl_i with ⟨_, part, henl, htw_part⟩
  refine ⟨θ', 𝒯_sub i, hθ'_ge, h𝒯_sub i, ?_, ?_⟩
  · rintro _ ⟨j, hadj, rfl⟩
    rw [Sym2.eq_swap]
    exact (isDistinction_treeDecompSide_of_adj h𝒯_sub hstd hadj).1.1
  · have hnonneg : (0 : ℚ) ≤ 3 * (θ : ℚ) + 1 := by
      exact_mod_cast Nat.zero_le (3 * θ + 1)
    refine ⟨hnonneg, part, henl, fun p hp ↦ ?_⟩
    have h_rat := htw_part hp
    -- Convert `(locationTreeWidth ... : ℚ) ≤ (9 / 4 : ℚ) * θ'` to integer arithmetic.
    have h_mul : (locationTreeWidth G (part p ∪ {(p.2, p.1)}) : ℚ) * 4 ≤
        9 * (θ' : ℚ) := by
      rwa [div_mul_eq_mul_div, le_div_iff₀ (by decide : (0 : ℚ) < 4)] at h_rat
    have h_int : locationTreeWidth G (part p ∪ {(p.2, p.1)}) * 4 ≤ 9 * (θ' : ℤ) := by
      exact_mod_cast h_mul
    have h_le : locationTreeWidth G (part p ∪ {(p.2, p.1)}) ≤ 3 * (θ : ℤ) + 1 := by omega
    exact_mod_cast h_le

end GraphMinor.GM18
