/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM04.Decomposition.Rotund
import LeanPool.GraphMinor.GM04.Decomposition.Contraction

/-!
# Helly property of subtrees and re-rooting of trees

This file proves two tree-theoretic ingredients for Graph Minors IV, (5.2):
1. The Helly property for vertex sets of subtrees of a rooted tree
(`RootedTree.helly_isSubtreeSet`).
2. Re-rooting a `RootedTree ι` at any vertex `r₀ ∈ T.verts` (`RootedTree.exists_reroot`), preserving
   the vertex set, the `OnPath` relation, and the separation pairs `{T.subtreeAt f, T.rootSide f}`
   of the edges.
-/

public section

namespace GraphMinor.GM04.RootedTree

variable {ι : Type*} (T : RootedTree ι)

/-- `A` is the vertex set of a subtree of `T`: `A ⊆ T.verts` and `A` is closed under paths in `T`.
-/
@[expose] def IsSubtreeSet (A : Set ι) : Prop :=
  A ⊆ T.verts ∧ ∀ t₁ ∈ A, ∀ t₃ ∈ A, ∀ t₂ ∈ T.verts, T.OnPath t₁ t₃ t₂ → t₂ ∈ A

/-- Every nonempty subtree vertex set `A` has a root `r ∈ A` that reaches every vertex in `A`. -/
theorem IsSubtreeSet.exists_root {T : RootedTree ι} {A : Set ι} (hA : T.IsSubtreeSet A)
    (hne : A.Nonempty) :
    ∃ r ∈ A, ∀ t ∈ A, T.Reaches r t := by
  obtain ⟨t₀, ht₀⟩ := hne
  have ht₀v : t₀ ∈ T.verts := hA.1 ht₀
  obtain ⟨r, hrA, _, _, hr_min⟩ :=
    T.exists_furthest_ancestor (T.reaches_root ht₀v)
      ⟨t₀, ht₀, T.reaches_root ht₀v, T.reaches_refl ht₀v⟩
  refine ⟨r, hrA, fun t htA ↦ ?_⟩
  have hrv : r ∈ T.verts := hA.1 hrA
  have htv : t ∈ T.verts := hA.1 htA
  obtain ⟨a, hav, har, hat, ha_lca⟩ := T.exists_lca hrv htv
  have ha_on : T.OnPath r t a := ⟨Or.inl har, ha_lca⟩
  have haA : a ∈ A := hA.2 r hrA t htA a hav ha_on
  have ha_eq : a = r := hr_min a haA (T.reaches_root hav) har
  rwa [← ha_eq]

/-- If two subtree vertex sets `A` and `B` with roots `r_A, r_B` meet, then `r_A` reaches `r_B`
(so `r_B ∈ A`) or `r_B` reaches `r_A` (so `r_A ∈ B`). -/
theorem IsSubtreeSet.reaches_root_or_symm {T : RootedTree ι} {A B : Set ι}
    (hA : T.IsSubtreeSet A) {rA rB : ι} (hrA : rA ∈ A) (hA_reach : ∀ t ∈ A, T.Reaches rA t)
    (hB_reach : ∀ t ∈ B, T.Reaches rB t) (hinter : (A ∩ B).Nonempty) :
    (T.Reaches rA rB ∧ rB ∈ A) ∨ T.Reaches rB rA := by
  obtain ⟨t, htA, htB⟩ := hinter
  rcases T.reaches_total_of_reaches (hA_reach t htA) (hB_reach t htB) with hAB | hBA
  · left
    have hrBv : rB ∈ T.verts := T.reaches_mem_left (hB_reach t htB)
    exact ⟨hAB, hA.2 rA hrA t htA rB hrBv (T.onPath_of_reaches hAB (hB_reach t htB))⟩
  · exact Or.inr hBA

/-- In a finite nonempty set `I`, a relation `R` that is reflexive and total on `I` and transitive
has a maximum element in `I`. -/
private theorem exists_max_of_total {α : Type*} {I : Finset α} (hne : I.Nonempty)
    {R : α → α → Prop} (hrefl : ∀ x ∈ I, R x x)
    (htrans : ∀ x y z, R x y → R y z → R x z)
    (htotal : ∀ x ∈ I, ∀ y ∈ I, R x y ∨ R y x) :
    ∃ m ∈ I, ∀ x ∈ I, R x m := by
  classical
  induction I using Finset.induction with
  | empty => exact absurd hne Finset.not_nonempty_empty
  | @insert a s ha ih =>
    by_cases hs : s.Nonempty
    · obtain ⟨m, hm_s, hm⟩ := ih hs
        (fun x hx ↦ hrefl x (Finset.mem_insert_of_mem hx))
        (fun x hx y hy ↦ htotal x (Finset.mem_insert_of_mem hx) y (Finset.mem_insert_of_mem hy))
      rcases htotal a (Finset.mem_insert_self a s) m (Finset.mem_insert_of_mem hm_s) with ham | hma
      · refine ⟨m, Finset.mem_insert_of_mem hm_s, fun x hx ↦ ?_⟩
        rcases Finset.mem_insert.mp hx with rfl | hxs
        · exact ham
        · exact hm x hxs
      · refine ⟨a, Finset.mem_insert_self a s, fun x hx ↦ ?_⟩
        rcases Finset.mem_insert.mp hx with rfl | hxs
        · exact hrefl x (Finset.mem_insert_self x s)
        · exact htrans x m a (hm x hxs) hma
    · rw [Finset.not_nonempty_iff_eq_empty] at hs
      subst hs
      refine ⟨a, Finset.mem_singleton_self a, fun x hx ↦ ?_⟩
      rw [Finset.mem_singleton.mp hx]
      exact hrefl a (Finset.mem_singleton_self a)

/-- The **Helly property for subtrees of a tree**: if `I` is a finite index set and `A i` (`i ∈ I`)
are nonempty subtree vertex sets of `T` that intersect pairwise, then there is a vertex `t ∈
T.verts`
belonging to `A i` for all `i ∈ I`. -/
theorem helly_isSubtreeSet {α : Type*} (I : Finset α) (A : α → Set ι)
    (hsub : ∀ i ∈ I, T.IsSubtreeSet (A i))
    (hinter : ∀ i ∈ I, ∀ j ∈ I, (A i ∩ A j).Nonempty) :
    ∃ t ∈ T.verts, ∀ i ∈ I, t ∈ A i := by
  by_cases hne : I.Nonempty
  · have hex_root : ∀ i : α, ∃ r, i ∈ I → r ∈ A i ∧ ∀ t ∈ A i, T.Reaches r t := by
      intro i
      by_cases hi : i ∈ I
      · obtain ⟨r, hr₁, hr₂⟩ := (hsub i hi).exists_root (by simpa using hinter i hi i hi)
        exact ⟨r, fun _ ↦ ⟨hr₁, hr₂⟩⟩
      · exact ⟨T.root, fun h ↦ False.elim (hi h)⟩
    choose r hr using hex_root
    obtain ⟨i₀, hi₀, hmax⟩ := exists_max_of_total hne
      (R := fun i j ↦ T.Reaches (r i) (r j))
      (fun i hi ↦ T.reaches_refl ((hsub i hi).1 (hr i hi).1))
      (fun _ _ _ h₁ h₂ ↦ T.reaches_trans h₁ h₂)
      (fun i hi j hj ↦ by
        rcases (hsub i hi).reaches_root_or_symm (hr i hi).1 (hr i hi).2 (hr j hj).2
          (hinter i hi j hj) with ⟨h, _⟩ | h
        · exact Or.inl h
        · exact Or.inr h)
    refine ⟨r i₀, (hsub i₀ hi₀).1 (hr i₀ hi₀).1, fun i hi ↦ ?_⟩
    rcases (hsub i hi).reaches_root_or_symm (hr i hi).1 (hr i hi).2 (hr i₀ hi₀).2
      (hinter i hi i₀ hi₀) with ⟨_, hmem⟩ | h_rev
    · exact hmem
    · have heq : r i₀ = r i := T.reaches_antisymm h_rev (hmax i hi)
      rw [heq]
      exact (hr i hi).1
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    subst hne
    exact ⟨T.root, T.root_mem, fun _ h ↦ False.elim (Finset.notMem_empty _ h)⟩

/-- Characterization of `T.OnPath t₁ t₃ t₂` in terms of the half-trees `{T.subtreeAt f, T.rootSide
f}`
for `f ∈ T.edges`. -/
theorem onPath_iff_edges {t₁ t₂ t₃ : ι} (ht₁ : t₁ ∈ T.verts) (ht₂ : t₂ ∈ T.verts)
    (ht₃ : t₃ ∈ T.verts) :
    T.OnPath t₁ t₃ t₂ ↔
      ∀ f ∈ T.edges,
        (t₂ ∈ T.subtreeAt f → t₁ ∈ T.subtreeAt f ∨ t₃ ∈ T.subtreeAt f) ∧
        (t₂ ∈ T.rootSide f → t₁ ∈ T.rootSide f ∨ t₃ ∈ T.rootSide f) := by
  refine ⟨?_, ?_⟩
  · intro hon f _
    simp only [T.mem_subtreeAt, T.mem_rootSide, ht₁, ht₂, ht₃, true_and]
    refine ⟨fun hf₂ ↦ ?_, fun hf₂ ↦ ?_⟩
    · rcases hon.1 with h₂₁ | h₂₃
      · exact Or.inl (T.reaches_trans hf₂ h₂₁)
      · exact Or.inr (T.reaches_trans hf₂ h₂₃)
    · by_contra h_not
      push Not at h_not
      exact hf₂ (hon.2 f h_not.1 h_not.2)
  · intro h
    refine ⟨?_, fun x hx₁ hx₃ ↦ ?_⟩
    · by_cases ht₂r : t₂ = T.root
      · subst ht₂r
        exact Or.inl (T.reaches_root ht₁)
      · have ht₂e : t₂ ∈ T.edges := T.mem_edges_iff.mpr ⟨ht₂, ht₂r⟩
        have h_sub := (h t₂ ht₂e).1 (T.self_mem_subtreeAt ht₂)
        simpa only [T.mem_subtreeAt] using h_sub
    · by_cases hxr : x = T.root
      · subst hxr
        exact T.reaches_root ht₂
      · have hxe : x ∈ T.edges := T.mem_edges_iff.mpr ⟨T.reaches_mem_left hx₁, hxr⟩
        by_contra h_not
        have ht₂_root : t₂ ∈ T.rootSide x := T.mem_rootSide.mpr ⟨ht₂, h_not⟩
        rcases (h x hxe).2 ht₂_root with h₁ | h₃
        · exact (T.mem_rootSide.mp h₁).2 hx₁
        · exact (T.mem_rootSide.mp h₃).2 hx₃

/-- Re-rooting `T` by moving the root one step to a child `c ∈ T.children T.root`. -/
noncomputable def rerootChild {c : ι} (hc : c ∈ T.children T.root) : RootedTree ι where
  verts := T.verts
  root := c
  parent v := by classical exact if v = T.root ∨ v = c then c else T.parent v
  root_mem := T.children_subset_verts T.root hc
  parent_mem v hv := by
    classical
    split_ifs
    · exact T.children_subset_verts T.root hc
    · exact T.parent_mem v hv
  parent_root := by
    classical
    simp
  exists_iterate_eq_root v hv := by
    classical
    obtain ⟨n, hn⟩ := T.exists_iterate_eq_root v hv
    induction n generalizing v with
    | zero =>
      rw [Function.iterate_zero_apply] at hn
      subst hn
      exact ⟨1, by simp⟩
    | succ k ih =>
      by_cases hvc : v = T.root ∨ v = c
      · exact ⟨1, by simp [hvc]⟩
      · rw [Function.iterate_succ_apply] at hn
        obtain ⟨m, hm⟩ := ih (T.parent v) (T.parent_mem v hv) hn
        refine ⟨m + 1, ?_⟩
        simp only [Function.iterate_succ_apply, hvc, ↓reduceIte, hm]

@[simp]
private theorem rerootChild_verts {c : ι} (hc : c ∈ T.children T.root) :
    (T.rerootChild hc).verts = T.verts := rfl

private theorem rerootChild_reaches_old_root {c : ι} (hc : c ∈ T.children T.root) (x : ι) :
    (T.rerootChild hc).Reaches T.root x ↔ x ∈ T.rootSide c := by
  classical
  obtain ⟨hce, hcp⟩ := T.mem_children_iff.mp hc
  refine ⟨?_, ?_⟩
  · rintro ⟨hx, n, hn⟩
    induction n generalizing x with
    | zero =>
      rw [Function.iterate_zero_apply] at hn
      subst hn
      exact T.root_mem_rootSide hce
    | succ k ih =>
      rw [Function.iterate_succ_apply] at hn
      have hp_mem : (T.rerootChild hc).parent x ∈ T.verts :=
        (T.rerootChild hc).parent_mem x hx
      have hp_rootSide : (T.rerootChild hc).parent x ∈ T.rootSide c :=
        ih ((T.rerootChild hc).parent x) hp_mem hn
      have hxc : ¬ (x = T.root ∨ x = c) := by
        intro h_or
        have hp_eq : (T.rerootChild hc).parent x = c := by simp [rerootChild, h_or]
        rw [hp_eq, T.mem_rootSide] at hp_rootSide
        exact hp_rootSide.2 (T.reaches_refl (T.edges_subset_verts hce))
      have hp_eq : (T.rerootChild hc).parent x = T.parent x := by simp [rerootChild, hxc]
      rw [hp_eq, T.mem_rootSide] at hp_rootSide
      refine T.mem_rootSide.mpr ⟨hx, fun hcx ↦ ?_⟩
      have hx_ne_c : c ≠ x := fun h ↦ hxc (Or.inr h.symm)
      exact hp_rootSide.2 (T.reaches_parent_of_reaches_of_ne hcx hx_ne_c)
  · intro hx
    obtain ⟨hxv, hnot_cx⟩ := T.mem_rootSide.mp hx
    obtain ⟨n, hn⟩ := T.exists_iterate_eq_root x hxv
    induction n generalizing x with
    | zero =>
      rw [Function.iterate_zero_apply] at hn
      subst hn
      exact (T.rerootChild hc).reaches_refl T.root_mem
    | succ k ih =>
      by_cases hxr : x = T.root
      · subst hxr
        exact (T.rerootChild hc).reaches_refl T.root_mem
      · have hxc : ¬ (x = T.root ∨ x = c) := by
          rintro (rfl | rfl)
          · exact hxr rfl
          · exact hnot_cx (T.reaches_refl hxv)
        have hp_eq : (T.rerootChild hc).parent x = T.parent x := by simp [rerootChild, hxc]
        have hnot_cp : ¬ T.Reaches c (T.parent x) :=
          fun hcp' ↦ hnot_cx (T.reaches_trans hcp' (T.reaches_parent hxv))
        rw [Function.iterate_succ_apply] at hn
        have hp_reach := ih (T.parent x) (T.mem_rootSide.mpr ⟨T.parent_mem x hxv, hnot_cp⟩)
          (T.parent_mem x hxv) hnot_cp hn
        exact (T.rerootChild hc).reaches_trans hp_reach
          (hp_eq ▸ (T.rerootChild hc).reaches_parent hxv)

private theorem rerootChild_reaches_of_ne {c f : ι} (hc : c ∈ T.children T.root)
    (hf : f ∈ T.edges) (hfc : f ≠ c) (x : ι) :
    (T.rerootChild hc).Reaches f x ↔ T.Reaches f x := by
  classical
  obtain ⟨hce, hcp⟩ := T.mem_children_iff.mp hc
  have hfr : f ≠ T.root := (T.mem_edges_iff.mp hf).2
  have h_not_fc : ¬ T.Reaches f c := by
    intro hfc_reach
    have hfp := T.reaches_parent_of_reaches_of_ne hfc_reach hfc
    rw [hcp, T.reaches_root_iff] at hfp
    exact hfr hfp
  refine ⟨?_, ?_⟩
  · rintro ⟨hx, n, hn⟩
    induction n generalizing x with
    | zero =>
      rw [Function.iterate_zero_apply] at hn
      subst hn
      exact T.reaches_refl hx
    | succ k ih =>
      rw [Function.iterate_succ_apply] at hn
      have hp_reach : T.Reaches f ((T.rerootChild hc).parent x) :=
        ih ((T.rerootChild hc).parent x) ((T.rerootChild hc).parent_mem x hx) hn
      have hxc : ¬ (x = T.root ∨ x = c) := by
        intro h_or
        have hp_eq : (T.rerootChild hc).parent x = c := by simp [rerootChild, h_or]
        rw [hp_eq] at hp_reach
        exact h_not_fc hp_reach
      have hp_eq : (T.rerootChild hc).parent x = T.parent x := by simp [rerootChild, hxc]
      rw [hp_eq] at hp_reach
      exact T.reaches_trans hp_reach (T.reaches_parent hx)
  · rintro ⟨hx, n, hn⟩
    induction n generalizing x with
    | zero =>
      rw [Function.iterate_zero_apply] at hn
      subst hn
      exact (T.rerootChild hc).reaches_refl hx
    | succ k ih =>
      by_cases hxf : x = f
      · subst hxf
        exact (T.rerootChild hc).reaches_refl hx
      · have hfx : T.Reaches f x := ⟨hx, k + 1, hn⟩
        have hxc : ¬ (x = T.root ∨ x = c) := by
          rintro (rfl | rfl)
          · exact hfr (T.reaches_root_iff.mp hfx)
          · exact h_not_fc hfx
        have hp_eq : (T.rerootChild hc).parent x = T.parent x := by simp [rerootChild, hxc]
        rw [Function.iterate_succ_apply] at hn
        have hp_reach := ih (T.parent x) (T.parent_mem x hx) hn
        exact (T.rerootChild hc).reaches_trans hp_reach
          (hp_eq ▸ (T.rerootChild hc).reaches_parent hx)

@[simp]
private theorem rerootChild_subtreeAt_old_root {c : ι} (hc : c ∈ T.children T.root) :
    (T.rerootChild hc).subtreeAt T.root = T.rootSide c := by
  ext x
  rw [(T.rerootChild hc).mem_subtreeAt, T.rerootChild_reaches_old_root hc]

@[simp]
private theorem rerootChild_rootSide_old_root {c : ι} (hc : c ∈ T.children T.root) :
    (T.rerootChild hc).rootSide T.root = T.subtreeAt c := by
  ext x
  rw [(T.rerootChild hc).mem_rootSide, T.rerootChild_verts hc, T.rerootChild_reaches_old_root hc,
    T.mem_rootSide, T.mem_subtreeAt]
  exact ⟨fun ⟨hx, hnot⟩ ↦ by tauto, fun h ↦ ⟨T.reaches_mem_right h, fun hnot ↦ hnot.2 h⟩⟩

private theorem rerootChild_subtreeAt_of_ne {c f : ι} (hc : c ∈ T.children T.root)
    (hf : f ∈ T.edges) (hfc : f ≠ c) :
    (T.rerootChild hc).subtreeAt f = T.subtreeAt f := by
  ext x
  rw [(T.rerootChild hc).mem_subtreeAt, T.mem_subtreeAt,
    T.rerootChild_reaches_of_ne hc hf hfc]

private theorem rerootChild_rootSide_of_ne {c f : ι} (hc : c ∈ T.children T.root)
    (hf : f ∈ T.edges) (hfc : f ≠ c) :
    (T.rerootChild hc).rootSide f = T.rootSide f := by
  ext x
  rw [(T.rerootChild hc).mem_rootSide, T.rerootChild_verts hc,
    T.rerootChild_reaches_of_ne hc hf hfc, T.mem_rootSide]

private theorem mem_rerootChild_edges_iff {c f : ι} (hc : c ∈ T.children T.root) :
    f ∈ (T.rerootChild hc).edges ↔ f = T.root ∨ (f ∈ T.edges ∧ f ≠ c) := by
  obtain ⟨hce, _⟩ := T.mem_children_iff.mp hc
  have hcr : c ≠ T.root := (T.mem_edges_iff.mp hce).2
  rw [(T.rerootChild hc).mem_edges_iff, T.mem_edges_iff]
  change (f ∈ T.verts ∧ f ≠ c) ↔ f = T.root ∨ (f ∈ T.verts ∧ f ≠ T.root) ∧ f ≠ c
  refine ⟨fun ⟨hfv, hfc⟩ ↦ ?_, ?_⟩
  · by_cases hfr : f = T.root
    · exact Or.inl hfr
    · exact Or.inr ⟨⟨hfv, hfr⟩, hfc⟩
  · rintro (rfl | ⟨⟨hfv, _⟩, hfc⟩)
    · exact ⟨T.root_mem, hcr.symm⟩
    · exact ⟨hfv, hfc⟩

private theorem rerootChild_onPath_iff {c t₁ t₂ t₃ : ι} (hc : c ∈ T.children T.root)
    (ht₁ : t₁ ∈ T.verts) (ht₂ : t₂ ∈ T.verts) (ht₃ : t₃ ∈ T.verts) :
    (T.rerootChild hc).OnPath t₁ t₃ t₂ ↔ T.OnPath t₁ t₃ t₂ := by
  obtain ⟨hce, _⟩ := T.mem_children_iff.mp hc
  rw [(T.rerootChild hc).onPath_iff_edges ht₁ ht₂ ht₃, T.onPath_iff_edges ht₁ ht₂ ht₃]
  refine ⟨fun h f hf ↦ ?_, fun h f hf ↦ ?_⟩
  · by_cases hfc : f = c
    · subst hfc
      have hr_edge : T.root ∈ (T.rerootChild hc).edges :=
        (T.mem_rerootChild_edges_iff hc).mpr (Or.inl rfl)
      have h_root := h T.root hr_edge
      rw [T.rerootChild_subtreeAt_old_root hc, T.rerootChild_rootSide_old_root hc] at h_root
      exact h_root.symm
    · have hf_edge : f ∈ (T.rerootChild hc).edges :=
        (T.mem_rerootChild_edges_iff hc).mpr (Or.inr ⟨hf, hfc⟩)
      have h_f := h f hf_edge
      rwa [T.rerootChild_subtreeAt_of_ne hc hf hfc,
        T.rerootChild_rootSide_of_ne hc hf hfc] at h_f
  · rcases (T.mem_rerootChild_edges_iff hc).mp hf with rfl | ⟨hfe, hfc⟩
    · rw [T.rerootChild_subtreeAt_old_root hc, T.rerootChild_rootSide_old_root hc]
      exact (h c hce).symm
    · rw [T.rerootChild_subtreeAt_of_ne hc hfe hfc, T.rerootChild_rootSide_of_ne hc hfe hfc]
      exact h f hfe

private theorem rerootChild_onPathEdge_exists_iff {α : Type*} {c t₁ t₂ : ι}
    (hc : c ∈ T.children T.root) (V : ι → Set α) (ht₁ : t₁ ∈ T.verts) (ht₂ : t₂ ∈ T.verts)
    (k : ℕ) :
    (∃ f, (T.rerootChild hc).OnPathEdge t₁ t₂ f ∧
        (V f ∩ V ((T.rerootChild hc).parent f)).ncard < k) ↔
      ∃ f, T.OnPathEdge t₁ t₂ f ∧ (V f ∩ V (T.parent f)).ncard < k := by
  classical
  obtain ⟨hce, hcp⟩ := T.mem_children_iff.mp hc
  refine ⟨?_, ?_⟩
  · rintro ⟨f, hon, hcard⟩
    rw [(T.rerootChild hc).onPathEdge_iff ht₁ ht₂] at hon
    rcases (T.mem_rerootChild_edges_iff hc).mp hon.1 with rfl | ⟨hfe, hfc⟩
    · rw [T.rerootChild_subtreeAt_old_root hc, T.rerootChild_rootSide_old_root hc] at hon
      have hp_eq : (T.rerootChild hc).parent T.root = c := by simp [rerootChild]
      rw [hp_eq, Set.inter_comm] at hcard
      rw [← hcp] at hcard
      refine ⟨c, ?_, hcard⟩
      rw [T.onPathEdge_iff ht₁ ht₂]
      exact ⟨hce, hon.2.symm.imp And.symm And.symm⟩
    · rw [T.rerootChild_subtreeAt_of_ne hc hfe hfc,
        T.rerootChild_rootSide_of_ne hc hfe hfc] at hon
      have hfr : f ≠ T.root := (T.mem_edges_iff.mp hfe).2
      have hp_eq : (T.rerootChild hc).parent f = T.parent f := by
        simp [rerootChild, hfr, hfc]
      rw [hp_eq] at hcard
      refine ⟨f, ?_, hcard⟩
      rw [T.onPathEdge_iff ht₁ ht₂]
      exact ⟨hfe, hon.2⟩
  · rintro ⟨f, hon, hcard⟩
    rw [T.onPathEdge_iff ht₁ ht₂] at hon
    by_cases hfc : f = c
    · subst hfc
      have hp_eq : (T.rerootChild hc).parent T.root = f := by simp [rerootChild]
      refine ⟨T.root, ?_, ?_⟩
      · rw [(T.rerootChild hc).onPathEdge_iff ht₁ ht₂,
          T.rerootChild_subtreeAt_old_root hc, T.rerootChild_rootSide_old_root hc]
        exact ⟨(T.mem_rerootChild_edges_iff hc).mpr (Or.inl rfl),
          hon.2.symm.imp And.symm And.symm⟩
      · rw [hp_eq, Set.inter_comm, ← hcp]
        exact hcard
    · have hfr : f ≠ T.root := (T.mem_edges_iff.mp hon.1).2
      have hp_eq : (T.rerootChild hc).parent f = T.parent f := by
        simp [rerootChild, hfr, hfc]
      refine ⟨f, ?_, hp_eq.symm ▸ hcard⟩
      rw [(T.rerootChild hc).onPathEdge_iff ht₁ ht₂,
        T.rerootChild_subtreeAt_of_ne hc hon.1 hfc,
        T.rerootChild_rootSide_of_ne hc hon.1 hfc]
      exact ⟨(T.mem_rerootChild_edges_iff hc).mpr (Or.inr ⟨hon.1, hfc⟩), hon.2⟩

/-- Re-rooting `T` at any vertex `r₀ ∈ T.verts` produces a `RootedTree ι` with the same vertex set,
root `r₀`, the same `OnPath` relation, and the same edge-separation orders for any vertex-bag
assignment `V`. -/
theorem exists_reroot {α : Type*} (V : ι → Set α) {r₀ : ι} (hr₀ : r₀ ∈ T.verts) :
    ∃ T' : RootedTree ι,
      T'.verts = T.verts ∧
      T'.root = r₀ ∧
      (∀ t₁ ∈ T.verts, ∀ t₂ ∈ T.verts, ∀ t₃ ∈ T.verts, T'.OnPath t₁ t₃ t₂ ↔ T.OnPath t₁ t₃ t₂) ∧
      ∀ t₁ ∈ T.verts, ∀ t₂ ∈ T.verts, ∀ k : ℕ,
        (∃ f, T'.OnPathEdge t₁ t₂ f ∧ (V f ∩ V (T'.parent f)).ncard < k) ↔
          ∃ f, T.OnPathEdge t₁ t₂ f ∧ (V f ∩ V (T.parent f)).ncard < k := by
  classical
  obtain ⟨n, hn⟩ := T.exists_iterate_eq_root r₀ hr₀
  induction n generalizing T with
  | zero =>
    rw [Function.iterate_zero_apply] at hn
    exact ⟨T, rfl, hn.symm, fun _ _ _ _ _ _ ↦ Iff.rfl, fun _ _ _ _ _ ↦ Iff.rfl⟩
  | succ k ih =>
    by_cases h_already : T.parent^[k] r₀ = T.root
    · exact ih T hr₀ h_already
    · let c := T.parent^[k] r₀
      have hcv : c ∈ T.verts := T.parent_iterate_mem hr₀ k
      have hce : c ∈ T.edges := T.mem_edges_iff.mpr ⟨hcv, h_already⟩
      have hcp : T.parent c = T.root := by
        rw [← hn, Function.iterate_succ_apply']
      have hc : c ∈ T.children T.root := T.mem_children_iff.mpr ⟨hce, hcp⟩
      let T₁ := T.rerootChild hc
      have h_iter : ∀ j ≤ k, T₁.parent^[j] r₀ = T.parent^[j] r₀ := by
        intro j hj
        induction j with
        | zero => rfl
        | succ m ihm =>
          have hm_le : m ≤ k := Nat.le_of_succ_le hj
          rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ihm hm_le]
          set x := T.parent^[m] r₀
          have hxv : x ∈ T.verts := T.parent_iterate_mem hr₀ m
          have hcx : T.Reaches c x := by
            have hd : k - m + m = k := Nat.sub_add_cancel hm_le
            refine ⟨hxv, k - m, ?_⟩
            change T.parent^[k - m] (T.parent^[m] r₀) = T.parent^[k] r₀
            rw [← Function.iterate_add_apply, hd]
          have hxc_ne : x ≠ c := by
            intro h_eq
            have h_loop : T.parent^[k - m] x = x := by
              change T.parent^[k - m] (T.parent^[m] r₀) = x
              rw [← Function.iterate_add_apply, Nat.sub_add_cancel hm_le]
              exact h_eq.symm
            have h_pos : 0 < k - m := by omega
            have hx_root := T.eq_root_of_iterate_eq_self hxv h_pos h_loop
            exact h_already (h_eq.symm.trans hx_root)
          have hxr_ne : x ≠ T.root := by
            intro hxr
            rw [hxr] at hcx
            exact (T.mem_edges_iff.mp hce).2 (T.reaches_root_iff.mp hcx)
          simp [T₁, rerootChild, hxr_ne, hxc_ne]
      have hT₁_k : T₁.parent^[k] r₀ = T₁.root := by
        rw [h_iter k (le_refl k)]
        rfl
      obtain ⟨T', hverts, hroot, honPath, honPathEdge⟩ := ih T₁ hr₀ hT₁_k
      refine ⟨T', hverts, hroot, fun t₁ ht₁ t₂ ht₂ t₃ ht₃ ↦ ?_, fun t₁ ht₁ t₂ ht₂ m ↦ ?_⟩
      · rw [honPath t₁ ht₁ t₂ ht₂ t₃ ht₃, T.rerootChild_onPath_iff hc ht₁ ht₂ ht₃]
      · rw [honPathEdge t₁ ht₁ t₂ ht₂ m, T.rerootChild_onPathEdge_exists_iff hc V ht₁ ht₂ m]

end GraphMinor.GM04.RootedTree
