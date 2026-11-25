/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM04.Decomposition.Basic

/-!
# Contraction of a tree-decomposition (Graph Minors IV, (3.2))

This file proves Graph Minors IV, (3.2) (page 234): if `(T, τ)` is a tree-decomposition of a rooted
hypergraph `G`, `F ⊆ E(T)`, `S` is the contraction of `T` onto `F`, and `σ(s) = τ × T_s` where
`T_s` is the component of `T \ F` with root `s`, then `(S, σ)` is a tree-decomposition of `G`.
-/

public section

namespace GraphMinor.GM04

open Hypergraph

variable {α β ι : Type*}

namespace RootedTree

variable (T : RootedTree ι)

/-- Every vertex `x` of `T` has a lowest common ancestor `a` with any other vertex `y` of `T`. -/
theorem exists_lca {x y : ι} (hx : x ∈ T.verts) (hy : y ∈ T.verts) :
    ∃ a ∈ T.verts, T.Reaches a x ∧ T.Reaches a y ∧
      ∀ z, T.Reaches z x → T.Reaches z y → T.Reaches z a := by
  obtain ⟨n, hn⟩ := T.exists_iterate_eq_root x hx
  have hroot : T.Reaches T.root y := T.reaches_root hy
  revert hx hn
  generalize T.root = u at hroot
  intro hx hn
  induction n generalizing x with
  | zero =>
    rw [Function.iterate_zero_apply] at hn
    subst hn
    exact ⟨x, hx, T.reaches_refl hx, hroot, fun _ hzx _ ↦ hzx⟩
  | succ k ih =>
    by_cases hxy : T.Reaches x y
    · exact ⟨x, hx, T.reaches_refl hx, hxy, fun _ hzx _ ↦ hzx⟩
    · rw [Function.iterate_succ_apply] at hn
      obtain ⟨a, hav, hap, hay, ha⟩ := ih (T.parent_mem x hx) hn
      refine ⟨a, hav, T.reaches_trans hap (T.reaches_parent hx), hay, fun z hzx hzy ↦ ?_⟩
      have hzx_ne : z ≠ x := by
        rintro rfl
        exact hxy hzy
      exact ha z (T.reaches_parent_of_reaches_of_ne hzx hzx_ne) hzy

private theorem isComponentRoot_unique {F : Set ι} {s₁ s₂ x : ι}
    (h₁ : T.IsComponentRoot F s₁ x) (h₂ : T.IsComponentRoot F s₂ x) : s₁ = s₂ := by
  by_contra hne
  rcases T.reaches_total_of_reaches h₁.1 h₂.1 with h₁₂ | h₂₁
  · rcases h₂.2.1 with rfl | hs₂F
    · exact hne (T.reaches_root_iff.mp h₁₂)
    · exact h₁.2.2 s₂ (Ne.symm hne) h₁₂ h₂.1 hs₂F
  · rcases h₁.2.1 with rfl | hs₁F
    · exact hne (T.reaches_root_iff.mp h₂₁).symm
    · exact h₂.2.2 s₁ hne h₂₁ h₁.1 hs₁F

private theorem exists_isComponentRoot_mem (F : Set ι) {x : ι} (hx : x ∈ T.verts) :
    ∃ s ∈ T.verts, T.IsComponentRoot F s x := by
  obtain ⟨n, hn⟩ := T.exists_iterate_eq_root x hx
  induction n generalizing x with
  | zero =>
    rw [Function.iterate_zero_apply] at hn
    exact ⟨x, hx, T.isComponentRoot_self hx (Or.inl hn)⟩
  | succ k ih =>
    by_cases hxF : x = T.root ∨ x ∈ F
    · exact ⟨x, hx, T.isComponentRoot_self hx hxF⟩
    · push Not at hxF
      rw [Function.iterate_succ_apply] at hn
      obtain ⟨s, hsv, hs⟩ := ih (T.parent_mem x hx) hn
      refine ⟨s, hsv, T.reaches_trans hs.1 (T.reaches_parent hx), hs.2.1, fun g hne hsg hgx ↦ ?_⟩
      rcases (T.reaches_iff_eq_or_reaches_parent hx).mp hgx with rfl | hgp
      · exact hxF.2
      · exact hs.2.2 g hne hsg hgp

theorem componentAt_subset_subtreeAt (F : Set ι) (s : ι) :
    T.componentAt F s ⊆ T.subtreeAt s := by
  intro x hx
  exact T.mem_subtreeAt.mpr (T.mem_componentAt.mp hx).1

section IsContraction

variable {T} {F : Set ι} {S : RootedTree ι}

private theorem IsContraction.mem_verts_iff_of_subset (hF : F ⊆ T.edges)
    (hS : T.IsContraction F S) {s : ι} :
    s ∈ S.verts ↔ s = T.root ∨ s ∈ F := by
  have h := Set.ext_iff.mp hS.verts_eq s
  rw [Finset.mem_coe, Set.mem_insert_iff, Set.mem_inter_iff] at h
  exact h.trans (or_congr_right ⟨And.left, fun hs ↦ ⟨hs, hF hs⟩⟩)

private theorem IsContraction.verts_subset_of_subset (hF : F ⊆ T.edges)
    (hS : T.IsContraction F S) :
    S.verts ⊆ T.verts := by
  intro s hs
  rcases hS.mem_verts_iff_of_subset hF |>.mp hs with rfl | hsF
  · exact T.root_mem
  · exact T.edges_subset_verts (hF hsF)

private theorem IsContraction.mem_edges_iff_of_subset (hF : F ⊆ T.edges)
    (hS : T.IsContraction F S) {f : ι} :
    f ∈ S.edges ↔ f ∈ F := by
  rw [S.mem_edges_iff, hS.mem_verts_iff_of_subset hF, hS.root_eq]
  refine ⟨?_, fun hf ↦ ⟨Or.inr hf, (T.mem_edges_iff.mp (hF hf)).2⟩⟩
  rintro ⟨rfl | hf, hne⟩
  · exact absurd rfl hne
  · exact hf

private theorem IsContraction.edges_subset (hF : F ⊆ T.edges) (hS : T.IsContraction F S) :
    S.edges ⊆ T.edges := by
  intro f hf
  exact hF ((hS.mem_edges_iff_of_subset hF).mp hf)

private theorem IsContraction.self_mem_componentAt (hF : F ⊆ T.edges) (hS : T.IsContraction F S)
    {s : ι} (hs : s ∈ S.verts) : s ∈ T.componentAt F s :=
  T.mem_componentAt.mpr
    (T.isComponentRoot_self (hS.verts_subset_of_subset hF hs)
      ((hS.mem_verts_iff_of_subset hF).mp hs))

theorem IsContraction.reaches_of_reaches (hF : F ⊆ T.edges) (hS : T.IsContraction F S)
    {s₁ s₂ : ι} (h : S.Reaches s₁ s₂) : T.Reaches s₁ s₂ := by
  obtain ⟨hs₂, n, rfl⟩ := h
  induction n generalizing s₂ with
  | zero => exact T.reaches_refl (hS.verts_subset_of_subset hF hs₂)
  | succ k ih =>
    rw [Function.iterate_succ_apply]
    have hstep : T.Reaches (S.parent s₂) s₂ := by
      by_cases hs₂r : s₂ = S.root
      · rw [hs₂r, S.parent_root]
        exact T.reaches_refl (hS.verts_subset_of_subset hF S.root_mem)
      · have hs₂e : s₂ ∈ S.edges := S.mem_edges_iff.mpr ⟨hs₂, hs₂r⟩
        have hcomp := hS.parent_eq s₂ hs₂e
        exact T.reaches_trans hcomp.1 (T.reaches_parent (hS.verts_subset_of_subset hF hs₂))
    exact T.reaches_trans (ih (S.parent_mem s₂ hs₂)) hstep

theorem IsContraction.reaches_of_isComponentRoot (hF : F ⊆ T.edges) (hS : T.IsContraction F S)
    {u s x : ι} (hu : u ∈ S.verts) (hsx : T.IsComponentRoot F s x) (hux : T.Reaches u x) :
    T.Reaches u s := by
  rcases T.reaches_total_of_reaches hux hsx.1 with hus | hsu
  · exact hus
  · by_cases h_eq : u = s
    · subst h_eq
      exact T.reaches_refl (hS.verts_subset_of_subset hF hu)
    · rcases (hS.mem_verts_iff_of_subset hF).mp hu with rfl | huF
      · rw [T.reaches_root_iff] at hsu
        exact absurd hsu.symm h_eq
      · exact absurd huF (hsx.2.2 u h_eq hsu hux)

theorem IsContraction.reaches_iff (hF : F ⊆ T.edges) (hS : T.IsContraction F S)
    {s₁ s₂ : ι} (hs₁ : s₁ ∈ S.verts) (hs₂ : s₂ ∈ S.verts) :
    S.Reaches s₁ s₂ ↔ T.Reaches s₁ s₂ := by
  refine ⟨hS.reaches_of_reaches hF, fun h ↦ ?_⟩
  obtain ⟨n, hn⟩ := S.exists_iterate_eq_root s₂ hs₂
  induction n generalizing s₂ with
  | zero =>
    rw [Function.iterate_zero_apply, hS.root_eq] at hn
    subst hn
    rw [T.reaches_root_iff] at h
    subst h
    exact S.reaches_refl hs₂
  | succ k ih =>
    by_cases h₁₂ : s₁ = s₂
    · subst h₁₂
      exact S.reaches_refl hs₁
    · have hs₂e : s₂ ∈ S.edges := by
        refine S.mem_edges_iff.mpr ⟨hs₂, ?_⟩
        rw [hS.root_eq]
        rintro rfl
        exact h₁₂ (T.reaches_root_iff.mp h)
      have h_par_T : T.Reaches s₁ (T.parent s₂) := T.reaches_parent_of_reaches_of_ne h h₁₂
      have hcomp := hS.parent_eq s₂ hs₂e
      have h_par_S : T.Reaches s₁ (S.parent s₂) :=
        hS.reaches_of_isComponentRoot hF hs₁ hcomp h_par_T
      rw [Function.iterate_succ_apply] at hn
      exact S.reaches_trans (ih (S.parent_mem s₂ hs₂) h_par_S hn) (S.reaches_parent hs₂)

theorem IsContraction.reaches_iff_of_mem_componentAt (hF : F ⊆ T.edges) (hS : T.IsContraction F S)
    {u s x : ι} (hu : u ∈ S.verts) (hs : s ∈ S.verts) (hx : x ∈ T.componentAt F s) :
    T.Reaches u x ↔ S.Reaches u s := by
  rw [hS.reaches_iff hF hu hs]
  have hsx := T.mem_componentAt.mp hx
  exact ⟨hS.reaches_of_isComponentRoot hF hu hsx, fun hus ↦ T.reaches_trans hus hsx.1⟩

theorem IsContraction.componentAt_parent_subset_rootSide (hF : F ⊆ T.edges)
    (hS : T.IsContraction F S) {f : ι} (hf : f ∈ S.edges) :
    T.componentAt F (S.parent f) ⊆ T.rootSide f := by
  intro x hx
  have hxv : x ∈ T.verts := T.componentAt_subset_verts F (S.parent f) hx
  refine T.mem_rootSide.mpr ⟨hxv, fun hfx ↦ ?_⟩
  have hf_verts : f ∈ S.verts := S.edges_subset_verts hf
  have hp_verts : S.parent f ∈ S.verts := S.parent_mem f hf_verts
  have hS_reach : S.Reaches f (S.parent f) :=
    (hS.reaches_iff_of_mem_componentAt hF hf_verts hp_verts hx).mp hfx
  exact S.not_reaches_parent hf hS_reach

theorem IsContraction.exists_mem_componentAt_onPath (hF : F ⊆ T.edges) (hS : T.IsContraction F S)
    {s₁ s₂ s₃ x₁ x₃ : ι} (hs₁ : s₁ ∈ S.verts) (hs₂ : s₂ ∈ S.verts) (hs₃ : s₃ ∈ S.verts)
    (hon : S.OnPath s₁ s₃ s₂) (hx₁ : x₁ ∈ T.componentAt F s₁) (hx₃ : x₃ ∈ T.componentAt F s₃) :
    ∃ x₂ ∈ T.componentAt F s₂, T.OnPath x₁ x₃ x₂ := by
  have hx₁v : x₁ ∈ T.verts := T.componentAt_subset_verts F s₁ hx₁
  have hx₃v : x₃ ∈ T.verts := T.componentAt_subset_verts F s₃ hx₃
  obtain ⟨a, hav, ha₁, ha₃, ha_lca⟩ := T.exists_lca hx₁v hx₃v
  have hs₂_reach : T.Reaches s₂ x₁ ∨ T.Reaches s₂ x₃ := by
    rcases hon.1 with h₂₁ | h₂₃
    · exact Or.inl ((hS.reaches_iff_of_mem_componentAt hF hs₂ hs₁ hx₁).mpr h₂₁)
    · exact Or.inr ((hS.reaches_iff_of_mem_componentAt hF hs₂ hs₃ hx₃).mpr h₂₃)
  by_cases has₂ : T.Reaches a s₂
  · refine ⟨s₂, hS.self_mem_componentAt hF hs₂, hs₂_reach, fun z hz₁ hz₃ ↦ ?_⟩
    exact T.reaches_trans (ha_lca z hz₁ hz₃) has₂
  · have hs₂a : T.Reaches s₂ a := by
      rcases hs₂_reach with hs₂₁ | hs₂₃
      · exact (T.reaches_total_of_reaches hs₂₁ ha₁).resolve_right has₂
      · exact (T.reaches_total_of_reaches hs₂₃ ha₃).resolve_right has₂
    obtain ⟨u, huv, hua⟩ := T.exists_isComponentRoot_mem F hav
    have huS : u ∈ S.verts := (hS.mem_verts_iff_of_subset hF).mpr hua.2.1
    have hu_mem : a ∈ T.componentAt F u := T.mem_componentAt.mpr hua
    have hu₁ : S.Reaches u s₁ :=
      (hS.reaches_iff_of_mem_componentAt hF huS hs₁ hx₁).mp (T.reaches_trans hua.1 ha₁)
    have hu₃ : S.Reaches u s₃ :=
      (hS.reaches_iff_of_mem_componentAt hF huS hs₃ hx₃).mp (T.reaches_trans hua.1 ha₃)
    have hu₂ : S.Reaches u s₂ := hon.2 u hu₁ hu₃
    have hs₂_u : S.Reaches s₂ u :=
      (hS.reaches_iff_of_mem_componentAt hF hs₂ huS hu_mem).mp hs₂a
    have heq : u = s₂ := S.reaches_antisymm hu₂ hs₂_u
    subst heq
    exact ⟨a, hu_mem, Or.inl ha₁, ha_lca⟩

end IsContraction

end RootedTree

namespace IsTreeDecomposition

variable {G : RootedHypergraph α β} {T : RootedTree ι} {τ : ι → RootedHypergraph α β}

/-- Graph Minors IV, (3.2): contracting a tree-decomposition `(T, τ)` of `G` onto `F ⊆ E(T)` yields
a tree-decomposition `(S, σ)` of `G`. -/
theorem contraction {ι : Type*} {G : RootedHypergraph α β}
    {T : RootedTree ι} {τ : ι → RootedHypergraph α β} (h : IsTreeDecomposition G T τ)
    {F : Set ι} (hF : F ⊆ T.edges) {S : RootedTree ι} (hS : T.IsContraction F S)
    (σ : ι → RootedHypergraph α β) (hσ : ∀ s ∈ S.verts, σ s = cross τ (T.componentAt F s) s) :
    IsTreeDecomposition G S σ where
  le s hs := by
    rw [hσ s hs]
    exact h.cross_le (T.componentAt_subset_verts F s) (hS.self_mem_componentAt hF hs)
  biUnion_eq := by
    have hle : Hypergraph.biUnion S.verts (fun s ↦ (σ s).toHypergraph) ≤ G.toHypergraph := by
      refine Hypergraph.biUnion_le fun s hs ↦ ?_
      rw [hσ s hs]
      exact h.cross_le (T.componentAt_subset_verts F s) (hS.self_mem_componentAt hF hs)
    refine Hypergraph.eq_of_le_of_subset hle ?_ ?_
    · intro v hv
      rw [← h.biUnion_eq, biUnion_vertexSet, Set.mem_iUnion₂] at hv
      obtain ⟨x, hx, hv⟩ := hv
      obtain ⟨s, _, hsx⟩ := T.exists_isComponentRoot_mem F hx
      have hs : s ∈ S.verts := (hS.mem_verts_iff_of_subset hF).mpr hsx.2.1
      rw [biUnion_vertexSet, Set.mem_iUnion₂]
      refine ⟨s, hs, ?_⟩
      rw [hσ s hs, cross_toHypergraph_of_mem τ (hS.self_mem_componentAt hF hs),
        biUnion_vertexSet, Set.mem_iUnion₂]
      exact ⟨x, T.mem_componentAt.mpr hsx, hv⟩
    · intro e he
      rw [← h.biUnion_eq, biUnion_edgeSet, Set.mem_iUnion₂] at he
      obtain ⟨x, hx, he⟩ := he
      obtain ⟨s, _, hsx⟩ := T.exists_isComponentRoot_mem F hx
      have hs : s ∈ S.verts := (hS.mem_verts_iff_of_subset hF).mpr hsx.2.1
      rw [biUnion_edgeSet, Set.mem_iUnion₂]
      refine ⟨s, hs, ?_⟩
      rw [hσ s hs, cross_toHypergraph_of_mem τ (hS.self_mem_componentAt hF hs),
        biUnion_edgeSet, Set.mem_iUnion₂]
      exact ⟨x, T.mem_componentAt.mpr hsx, he⟩
  edgeSet_inter_eq s₁ hs₁ s₂ hs₂ hne := by
    rw [hσ s₁ hs₁, hσ s₂ hs₂,
      cross_toHypergraph_of_mem τ (hS.self_mem_componentAt hF hs₁),
      cross_toHypergraph_of_mem τ (hS.self_mem_componentAt hF hs₂)]
    ext e
    simp only [inter_edgeSet, Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and,
      biUnion_edgeSet, Set.mem_iUnion₂]
    rintro ⟨x₁, hx₁, he₁⟩ ⟨x₂, hx₂, he₂⟩
    have hx_ne : x₁ ≠ x₂ := by
      rintro rfl
      exact Finset.disjoint_left.mp (T.disjoint_componentAt (F := F) hne) hx₁ hx₂
    have he : e ∈ ((τ x₁).toHypergraph ∩ (τ x₂).toHypergraph).edgeSet := ⟨he₁, he₂⟩
    rw [h.edgeSet_inter_eq x₁ (T.componentAt_subset_verts F s₁ hx₁)
      x₂ (T.componentAt_subset_verts F s₂ hx₂) hx_ne] at he
    exact False.elim he
  inter_le s₁ hs₁ s₂ hs₂ s₃ hs₃ hon := by
    have hle₁ : (σ s₁).toHypergraph ≤ G.toHypergraph := by
      rw [hσ s₁ hs₁]
      exact h.cross_le (T.componentAt_subset_verts F s₁) (hS.self_mem_componentAt hF hs₁)
    have hle₃ : (σ s₃).toHypergraph ≤ G.toHypergraph := by
      rw [hσ s₃ hs₃]
      exact h.cross_le (T.componentAt_subset_verts F s₃) (hS.self_mem_componentAt hF hs₃)
    by_cases h₂₁ : s₂ = s₁
    · subst h₂₁
      exact Hypergraph.inter_le_left hle₁ hle₃
    · by_cases h₂₃ : s₂ = s₃
      · subst h₂₃
        exact Hypergraph.inter_le_right hle₁ hle₃
      · have h₁₃ : s₁ ≠ s₃ := by
          rintro rfl
          have hr : S.Reaches s₁ s₂ := hon.2 s₁ (S.reaches_refl hs₁) (S.reaches_refl hs₁)
          rcases hon.1 with h1 | h1 <;> exact h₂₁ (S.reaches_antisymm h1 hr)
        have h_empty : ((σ s₁).toHypergraph ∩ (σ s₃).toHypergraph).edgeSet = ∅ := by
          rw [hσ s₁ hs₁, hσ s₃ hs₃,
            cross_toHypergraph_of_mem τ (hS.self_mem_componentAt hF hs₁),
            cross_toHypergraph_of_mem τ (hS.self_mem_componentAt hF hs₃)]
          ext e
          simp only [inter_edgeSet, Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and,
            biUnion_edgeSet, Set.mem_iUnion₂]
          rintro ⟨x₁, hx₁, he₁⟩ ⟨x₃, hx₃, he₃⟩
          have hx_ne : x₁ ≠ x₃ := by
            rintro rfl
            exact Finset.disjoint_left.mp (T.disjoint_componentAt (F := F) h₁₃) hx₁ hx₃
          have he : e ∈ ((τ x₁).toHypergraph ∩ (τ x₃).toHypergraph).edgeSet := ⟨he₁, he₃⟩
          rw [h.edgeSet_inter_eq x₁ (T.componentAt_subset_verts F s₁ hx₁)
            x₃ (T.componentAt_subset_verts F s₃ hx₃) hx_ne] at he
          exact False.elim he
        refine ⟨?_, ?_, ?_⟩
        · rintro v ⟨hv₁, hv₃⟩
          rw [hσ s₁ hs₁, cross_toHypergraph_of_mem τ (hS.self_mem_componentAt hF hs₁),
            biUnion_vertexSet, Set.mem_iUnion₂] at hv₁
          rw [hσ s₃ hs₃, cross_toHypergraph_of_mem τ (hS.self_mem_componentAt hF hs₃),
            biUnion_vertexSet, Set.mem_iUnion₂] at hv₃
          obtain ⟨x₁, hx₁, hv₁⟩ := hv₁
          obtain ⟨x₃, hx₃, hv₃⟩ := hv₃
          obtain ⟨x₂, hx₂, hon_T⟩ :=
            hS.exists_mem_componentAt_onPath hF hs₁ hs₂ hs₃ hon hx₁ hx₃
          have hv : v ∈ ((τ x₁).toHypergraph ∩ (τ x₃).toHypergraph).vertexSet := ⟨hv₁, hv₃⟩
          have hv₂ := (h.inter_le x₁ (T.componentAt_subset_verts F s₁ hx₁)
            x₂ (T.componentAt_subset_verts F s₂ hx₂)
            x₃ (T.componentAt_subset_verts F s₃ hx₃) hon_T).vertexSet_subset hv
          rw [hσ s₂ hs₂, cross_toHypergraph_of_mem τ (hS.self_mem_componentAt hF hs₂)]
          exact Set.mem_biUnion hx₂ hv₂
        · rw [h_empty]
          exact Set.empty_subset _
        · intro e he
          rw [h_empty] at he
          exact False.elim he
  roots_root := by
    rw [hσ S.root S.root_mem, cross_roots, hS.root_eq, h.roots_root]
  rootSet_edge f hf := by
    have hf_verts : f ∈ S.verts := S.edges_subset_verts hf
    have hp_verts : S.parent f ∈ S.verts := S.parent_mem f hf_verts
    have hfe : f ∈ T.edges := hS.edges_subset hF hf
    have hfv : f ∈ T.verts := T.edges_subset_verts hfe
    have hpv : T.parent f ∈ T.verts := T.parent_mem f hfv
    rw [hσ f hf_verts, hσ (S.parent f) hp_verts, cross_rootSet, h.rootSet_edge f hfe]
    have hf_comp : f ∈ T.componentAt F f := hS.self_mem_componentAt hF hf_verts
    have hp_comp : T.parent f ∈ T.componentAt F (S.parent f) :=
      T.mem_componentAt.mpr (hS.parent_eq f hf)
    have hle₁ : (τ f).toHypergraph ≤ (cross τ (T.componentAt F f) f).toHypergraph :=
      h.le_cross (T.componentAt_subset_verts F f) hf_comp hf_comp
    have hle₂ : (τ (T.parent f)).toHypergraph ≤
        (cross τ (T.componentAt F (S.parent f)) (S.parent f)).toHypergraph :=
      h.le_cross (T.componentAt_subset_verts F (S.parent f))
        (hS.self_mem_componentAt hF hp_verts) hp_comp
    have hle₃ : (cross τ (T.componentAt F f) f).toHypergraph ≤
        (cross τ (T.subtreeAt f) f).toHypergraph :=
      h.cross_le_cross (T.componentAt_subset_subtreeAt F f) (T.subtreeAt_subset_verts f)
        hf_comp (T.self_mem_subtreeAt hfv)
    have hle₄ : (cross τ (T.componentAt F (S.parent f)) (S.parent f)).toHypergraph ≤
        (cross τ (T.rootSide f) T.root).toHypergraph :=
      h.cross_le_cross (hS.componentAt_parent_subset_rootSide hF hf) (T.rootSide_subset_verts f)
        (hS.self_mem_componentAt hF hp_verts) (T.root_mem_rootSide hfe)
    apply Set.Subset.antisymm
    · exact Set.subset_inter (hle₁.vertexSet_subset.trans' Set.inter_subset_left)
        (hle₂.vertexSet_subset.trans' Set.inter_subset_right)
    · have hsub : ((cross τ (T.componentAt F f) f).toHypergraph ∩
          (cross τ (T.componentAt F (S.parent f)) (S.parent f)).toHypergraph).vertexSet ⊆
          ((cross τ (T.subtreeAt f) f).toHypergraph ∩
          (cross τ (T.rootSide f) T.root).toHypergraph).vertexSet :=
        Set.inter_subset_inter hle₃.vertexSet_subset hle₄.vertexSet_subset
      rwa [h.subtreeAt_inter_rootSide_eq hfe] at hsub

/-- Contracting a tree-decomposition `(T, τ)` onto `F ⊆ E(T)` preserves the order of every edge in
`F`. -/
theorem edgeOrder_contraction (h : IsTreeDecomposition G T τ)
    {F : Set ι} (hF : F ⊆ T.edges) {S : RootedTree ι} (hS : T.IsContraction F S)
    {σ : ι → RootedHypergraph α β} (hσ : ∀ s ∈ S.verts, σ s = cross τ (T.componentAt F s) s)
    {f : ι} (hf : f ∈ S.edges) :
    edgeOrder S σ f = edgeOrder T τ f := by
  have hdecS := h.contraction hF hS σ hσ
  have hfe : f ∈ T.edges := hS.edges_subset hF hf
  rw [hdecS.edgeOrder_eq_ncard_rootSet hf, h.edgeOrder_eq_ncard_rootSet hfe,
    hσ f (S.edges_subset_verts hf), cross_rootSet]

end IsTreeDecomposition

end GraphMinor.GM04
