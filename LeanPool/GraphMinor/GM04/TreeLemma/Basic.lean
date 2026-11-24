/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM04.Tree
import Mathlib.Data.Finset.Card
import Mathlib.Data.Set.Finite.Basic

/-!
# Basic properties of rooted trees (Graph Minors IV, Section 2)

This file develops the basic theory of `RootedTree` from `GraphMinor/GM04/Tree.lean` needed in
Section 2 and later sections of Graph Minors IV:

* Acyclicity of `parent` iterates outside the root, and the partial order `Reaches` (reflexive on
  `verts`, transitive, antisymmetric, with `root` as minimum and linear ancestor chains).
* Properties of vertex sets of subtrees (`subtreeAt`) and root-side components (`rootSide`), and the
  construction `RootedTree.subtree` of `T^v` as a `RootedTree`.
* Existence and uniqueness of component roots (`IsComponentRoot`) in `T \ F`, the construction
  `RootedTree.componentTree` of a component of `T \ F` as a `RootedTree`, and the existence of the
  contraction of `T` onto `F` (`RootedTree.exists_isContraction`).
* Closure of `IsRich` under subsets and binary unions.
-/

public section

namespace GraphMinor.GM04

variable {ι : Type*}

namespace RootedTree

variable (T : RootedTree ι)

/-! ### Edges and iterates of `parent` -/

@[simp]
theorem mem_edges {v : ι} : v ∈ T.edges ↔ v ≠ T.root ∧ v ∈ T.verts := by
  classical exact Finset.mem_erase

theorem edges_subset_verts : T.edges ⊆ T.verts := by
  intro v hv
  exact (T.mem_edges.1 hv).2

theorem ne_root_of_mem_edges {v : ι} (hv : v ∈ T.edges) : v ≠ T.root :=
  (T.mem_edges.1 hv).1

theorem mem_verts_of_mem_edges {v : ι} (hv : v ∈ T.edges) : v ∈ T.verts :=
  (T.mem_edges.1 hv).2

theorem root_notMem_edges : T.root ∉ T.edges := by
  simp [mem_edges]

/-- Iterating `parent` preserves membership in `T.verts`. -/
theorem iterate_parent_mem {v : ι} (hv : v ∈ T.verts) : ∀ n : ℕ, T.parent^[n] v ∈ T.verts
  | 0 => hv
  | n + 1 => by
    rw [Function.iterate_succ_apply']
    exact T.parent_mem _ (iterate_parent_mem hv n)

/-- Iterating `parent` at the root stays at the root. -/
@[simp]
theorem iterate_parent_root (n : ℕ) : T.parent^[n] T.root = T.root :=
  Function.iterate_fixed T.parent_root n

/-- Once an iterate of `parent` reaches the root, all higher iterates stay at the root. -/
theorem iterate_parent_eq_root_of_le {v : ι} {m n : ℕ} (h : T.parent^[m] v = T.root)
    (hmn : m ≤ n) : T.parent^[n] v = T.root := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  rw [add_comm, Function.iterate_add_apply, h, T.iterate_parent_root]

private theorem iterate_mul_eq_self {u : ι} {k : ℕ} (hk : T.parent^[k] u = u) :
    ∀ m : ℕ, T.parent^[m * k] u = u
  | 0 => by simp
  | m + 1 => by
    rw [Nat.succ_mul, Function.iterate_add_apply, hk, iterate_mul_eq_self hk m]

/-- The root is the only vertex fixed by a positive iterate of `parent`. -/
theorem eq_root_of_iterate_eq_self {u : ι} (hu : u ∈ T.verts) {k : ℕ} (hk : 0 < k)
    (h : T.parent^[k] u = u) : u = T.root := by
  obtain ⟨n, hn⟩ := T.exists_iterate_eq_root u hu
  have h1 : T.parent^[n * k] u = T.root :=
    T.iterate_parent_eq_root_of_le hn (Nat.le_mul_of_pos_right n hk)
  rw [iterate_mul_eq_self T h n] at h1
  exact h1

/-- No non-root vertex is its own parent. -/
theorem parent_ne_self {v : ι} (hv : v ∈ T.edges) : T.parent v ≠ v := by
  intro h
  exact T.ne_root_of_mem_edges hv
    (T.eq_root_of_iterate_eq_self (T.mem_verts_of_mem_edges hv) Nat.one_pos h)

/-! ### Reachability (`Reaches`) -/

theorem Reaches.verts_right {u v : ι} (h : T.Reaches u v) : v ∈ T.verts :=
  h.1

theorem Reaches.verts_left {u v : ι} (h : T.Reaches u v) : u ∈ T.verts := by
  obtain ⟨hv, n, rfl⟩ := h
  exact T.iterate_parent_mem hv n

/-- `Reaches` is reflexive on `T.verts`. -/
@[simp]
theorem reaches_refl {v : ι} (hv : v ∈ T.verts) : T.Reaches v v :=
  ⟨hv, 0, rfl⟩

/-- `Reaches` is transitive. -/
theorem Reaches.trans {u v w : ι} (huv : T.Reaches u v) (hvw : T.Reaches v w) :
    T.Reaches u w := by
  obtain ⟨_, n, rfl⟩ := huv
  obtain ⟨hw, m, rfl⟩ := hvw
  exact ⟨hw, n + m, by rw [Function.iterate_add_apply]⟩

/-- `Reaches` is antisymmetric. -/
theorem Reaches.antisymm {u v : ι} (huv : T.Reaches u v) (hvu : T.Reaches v u) : u = v := by
  obtain ⟨hv, n, rfl⟩ := huv
  obtain ⟨hu, m, hmu⟩ := hvu
  have hnm : T.parent^[m + n] v = v := by
    rw [Function.iterate_add_apply]
    exact hmu
  rcases Nat.eq_zero_or_pos (m + n) with h0 | hpos
  · have hn : n = 0 := by omega
    simp [hn]
  · have hvroot : v = T.root := T.eq_root_of_iterate_eq_self hv hpos hnm
    rw [hvroot, T.iterate_parent_root]

/-- The root reaches every vertex of `T`. -/
theorem root_reaches {v : ι} (hv : v ∈ T.verts) : T.Reaches T.root v :=
  ⟨hv, T.exists_iterate_eq_root v hv⟩

/-- Only the root reaches the root. -/
@[simp]
theorem reaches_root_iff {u : ι} : T.Reaches u T.root ↔ u = T.root := by
  constructor
  · rintro ⟨_, n, rfl⟩
    exact T.iterate_parent_root n
  · rintro rfl
    exact T.reaches_refl T.root_mem

/-- The parent of a vertex reaches that vertex. -/
theorem reaches_parent {v : ι} (hv : v ∈ T.verts) : T.Reaches (T.parent v) v :=
  ⟨hv, 1, rfl⟩

/-- A non-root vertex does not reach its own parent. -/
theorem not_reaches_parent {v : ι} (hv : v ∈ T.edges) : ¬ T.Reaches v (T.parent v) := by
  intro h
  exact T.parent_ne_self hv (h.antisymm T (T.reaches_parent (T.mem_verts_of_mem_edges hv))).symm

/-- If `u` reaches `v`, then `u = v` or `u` reaches `T.parent v`. -/
theorem Reaches.eq_or_reaches_parent {u v : ι} (h : T.Reaches u v) :
    u = v ∨ T.Reaches u (T.parent v) := by
  obtain ⟨hv, n, rfl⟩ := h
  rcases n with _ | n
  · exact Or.inl rfl
  · exact Or.inr ⟨T.parent_mem v hv, n, Function.iterate_succ_apply T.parent n v⟩

/-- If `u` properly reaches `v`, then `v` is a non-root vertex and `u` reaches `T.parent v`. -/
theorem Reaches.ne_imp_mem_edges_and_reaches_parent {u v : ι} (h : T.Reaches u v) (hne : u ≠ v) :
    v ∈ T.edges ∧ T.Reaches u (T.parent v) := by
  refine ⟨T.mem_edges.2 ⟨?_, h.verts_right⟩, ?_⟩
  · rintro rfl
    exact hne (T.reaches_root_iff.1 h)
  · exact (h.eq_or_reaches_parent T).resolve_left hne

/-- The ancestors of any vertex form a chain under `Reaches`. -/
theorem Reaches.total_of_reaches {x y w : ι} (hx : T.Reaches x w) (hy : T.Reaches y w) :
    T.Reaches x y ∨ T.Reaches y x := by
  obtain ⟨hw, n, rfl⟩ := hx
  obtain ⟨_, m, rfl⟩ := hy
  rcases le_total n m with hnm | hmn
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
    refine Or.inr ⟨T.iterate_parent_mem hw n, k, ?_⟩
    rw [add_comm, Function.iterate_add_apply]
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
    refine Or.inl ⟨T.iterate_parent_mem hw m, k, ?_⟩
    rw [add_comm, Function.iterate_add_apply]

/-! ### Subtrees (`subtreeAt`, `rootSide`, `subtree`) -/

@[simp]
theorem mem_subtreeAt {v w : ι} : w ∈ T.subtreeAt v ↔ T.Reaches v w := by
  classical
  simp only [subtreeAt, Finset.mem_filter, and_iff_right_iff_imp]
  exact Reaches.verts_right T

theorem subtreeAt_subset_verts (v : ι) : T.subtreeAt v ⊆ T.verts := by
  intro w hw
  exact (T.mem_subtreeAt.1 hw).verts_right T

theorem self_mem_subtreeAt {v : ι} (hv : v ∈ T.verts) : v ∈ T.subtreeAt v :=
  T.mem_subtreeAt.2 (T.reaches_refl hv)

@[simp]
theorem subtreeAt_root : T.subtreeAt T.root = T.verts := by
  ext v
  simp only [mem_subtreeAt]
  exact ⟨Reaches.verts_right T, T.root_reaches⟩

/-- If `u` reaches `v`, the subtree at `v` is contained in the subtree at `u`. -/
theorem subtreeAt_subset_of_reaches {u v : ι} (h : T.Reaches u v) :
    T.subtreeAt v ⊆ T.subtreeAt u := by
  intro w hw
  exact T.mem_subtreeAt.2 (h.trans T (T.mem_subtreeAt.1 hw))

/-- If `u` properly reaches `v`, the subtree at `v` is a strict subset of the subtree at `u`. -/
theorem subtreeAt_ssubset_of_reaches_of_ne {u v : ι} (h : T.Reaches u v) (hne : u ≠ v) :
    T.subtreeAt v ⊂ T.subtreeAt u := by
  refine Finset.ssubset_iff_subset_ne.2 ⟨T.subtreeAt_subset_of_reaches h, ?_⟩
  intro heq
  have hu : u ∈ T.subtreeAt v := heq ▸ T.self_mem_subtreeAt (h.verts_left T)
  exact hne (h.antisymm T (T.mem_subtreeAt.1 hu))

/-- If `u` properly reaches `v`, the subtree at `v` has strictly fewer vertices than that at `u`. -/
theorem subtreeAt_card_lt_of_reaches_of_ne {u v : ι} (h : T.Reaches u v) (hne : u ≠ v) :
    (T.subtreeAt v).card < (T.subtreeAt u).card :=
  Finset.card_lt_card (T.subtreeAt_ssubset_of_reaches_of_ne h hne)

@[simp]
theorem mem_rootSide {f w : ι} : w ∈ T.rootSide f ↔ w ∈ T.verts ∧ ¬ T.Reaches f w := by
  classical simp [rootSide, mem_subtreeAt]

theorem rootSide_subset_verts (f : ι) : T.rootSide f ⊆ T.verts := by
  intro w hw
  exact (T.mem_rootSide.1 hw).1

theorem disjoint_subtreeAt_rootSide (f : ι) : Disjoint (T.subtreeAt f) (T.rootSide f) := by
  classical exact Finset.disjoint_sdiff

theorem coe_subtreeAt_union_rootSide (f : ι) :
    (T.subtreeAt f : Set ι) ∪ (T.rootSide f : Set ι) = T.verts := by
  ext x
  simp only [Set.mem_union, Finset.mem_coe, mem_subtreeAt, mem_rootSide]
  exact ⟨fun h ↦ h.elim (Reaches.verts_right T) And.left,
    fun hx ↦ by
      by_cases h : T.Reaches f x
      · exact Or.inl h
      · exact Or.inr ⟨hx, h⟩⟩

theorem root_mem_rootSide {f : ι} (hf : f ∈ T.edges) : T.root ∈ T.rootSide f := by
  rw [mem_rootSide, reaches_root_iff]
  exact ⟨T.root_mem, T.ne_root_of_mem_edges hf⟩

private theorem iterate_update_root {v : ι} [DecidableEq ι] (p : ι → ι) :
    ∀ {n : ℕ} {x : ι}, p^[n] x = v → (fun w ↦ if w = v then v else p w)^[n] x = v
  | 0, _, rfl => rfl
  | n + 1, x, h => by
    rw [Function.iterate_succ_apply]
    by_cases hxv : x = v
    · subst hxv
      simp only [↓reduceIte]
      exact Function.iterate_fixed (by simp) n
    · simp only [hxv, ↓reduceIte]
      rw [Function.iterate_succ_apply] at h
      exact iterate_update_root p h

/-- The maximal subtree `T^v` of `T` with root `v` as a `RootedTree`. -/
@[expose] noncomputable def subtree (v : ι) (hv : v ∈ T.verts) : RootedTree ι where
  verts := T.subtreeAt v
  root := v
  parent := by classical exact fun w ↦ if w = v then v else T.parent w
  root_mem := T.self_mem_subtreeAt hv
  parent_mem w hw := by
    classical
    split_ifs with hwv
    · exact T.self_mem_subtreeAt hv
    · exact T.mem_subtreeAt.2
        (((T.mem_subtreeAt.1 hw).ne_imp_mem_edges_and_reaches_parent T (Ne.symm hwv)).2)
  parent_root := by classical simp
  exists_iterate_eq_root w hw := by
    classical
    obtain ⟨_, n, hn⟩ := T.mem_subtreeAt.1 hw
    exact ⟨n, iterate_update_root T.parent hn⟩

@[simp]
theorem subtree_verts (v : ι) (hv : v ∈ T.verts) : (T.subtree v hv).verts = T.subtreeAt v := rfl

@[simp]
theorem subtree_root (v : ι) (hv : v ∈ T.verts) : (T.subtree v hv).root = v := rfl

theorem subtree_parent_of_ne (v : ι) (hv : v ∈ T.verts) {w : ι} (hw : w ≠ v) :
    (T.subtree v hv).parent w = T.parent w := by
  classical simp [subtree, hw]

theorem mem_subtree_edges {v f : ι} (hv : v ∈ T.verts) :
    f ∈ (T.subtree v hv).edges ↔ f ≠ v ∧ T.Reaches v f := by
  rw [mem_edges, subtree_root, subtree_verts, mem_subtreeAt]

/-! ### Component roots, components of `T \ F`, and contractions -/

theorem IsComponentRoot.reaches {F : Set ι} {y x : ι} (h : T.IsComponentRoot F y x) :
    T.Reaches y x :=
  h.1

theorem IsComponentRoot.verts_left {F : Set ι} {y x : ι} (h : T.IsComponentRoot F y x) :
    y ∈ T.verts :=
  h.1.verts_left T

theorem IsComponentRoot.verts_right {F : Set ι} {y x : ι} (h : T.IsComponentRoot F y x) :
    x ∈ T.verts :=
  h.1.verts_right T

theorem IsComponentRoot.root_or_mem {F : Set ι} {y x : ι} (h : T.IsComponentRoot F y x) :
    y = T.root ∨ y ∈ F :=
  h.2.1

theorem IsComponentRoot.notMem_of_reaches {F : Set ι} {y x g : ι} (h : T.IsComponentRoot F y x)
    (hgy : g ≠ y) (hyg : T.Reaches y g) (hgx : T.Reaches g x) : g ∉ F :=
  h.2.2 g hgy hyg hgx

/-- Each vertex of `T` has at most one component root in `T \ F`. -/
theorem IsComponentRoot.unique {F : Set ι} {y₁ y₂ x : ι}
    (h₁ : T.IsComponentRoot F y₁ x) (h₂ : T.IsComponentRoot F y₂ x) : y₁ = y₂ := by
  rcases h₁.reaches.total_of_reaches T h₂.reaches with h12 | h21
  · by_contra hne
    have hy₂_not_F : y₂ ∉ F := h₁.notMem_of_reaches T (Ne.symm hne) h12 h₂.reaches
    have hy₂_ne_root : y₂ ≠ T.root := by
      rintro rfl
      exact hne (T.reaches_root_iff.1 h12)
    rcases h₂.root_or_mem with hroot | hF
    · exact hy₂_ne_root hroot
    · exact hy₂_not_F hF
  · by_contra hne
    have hy₁_not_F : y₁ ∉ F := h₂.notMem_of_reaches T hne h21 h₁.reaches
    have hy₁_ne_root : y₁ ≠ T.root := by
      rintro rfl
      exact hne (T.reaches_root_iff.1 h21).symm
    rcases h₁.root_or_mem with hroot | hF
    · exact hy₁_ne_root hroot
    · exact hy₁_not_F hF

/-- Any vertex `y ∈ T.verts` with `y = T.root ∨ y ∈ F` is the root of its own component. -/
theorem isComponentRoot_self {F : Set ι} {y : ι} (hy : y ∈ T.verts) (hyF : y = T.root ∨ y ∈ F) :
    T.IsComponentRoot F y y := by
  refine ⟨T.reaches_refl hy, hyF, fun g hgy hyg hgy' ↦ ?_⟩
  exact absurd (hyg.antisymm T hgy').symm hgy

@[simp]
theorem isComponentRoot_root (F : Set ι) : T.IsComponentRoot F T.root T.root :=
  T.isComponentRoot_self T.root_mem (Or.inl rfl)

/-- If `x` is neither the root nor in `F`, it lies in the same component of `T \ F` as its
parent. -/
theorem IsComponentRoot.of_parent {F : Set ι} {y x : ι} (hx : x ∈ T.verts) (hxF : x ∉ F)
    (hxr : x ≠ T.root) (hp : T.IsComponentRoot F y (T.parent x)) :
    T.IsComponentRoot F y x := by
  refine ⟨hp.reaches.trans T (T.reaches_parent hx), hp.root_or_mem, fun g hgy hyg hgx ↦ ?_⟩
  rcases hgx.eq_or_reaches_parent T with rfl | hgp
  · exact hxF
  · exact hp.notMem_of_reaches T hgy hyg hgp

/-- If `x` has component root `y` and `x ≠ y`, then `x` is an edge not in `F` and `T.parent x`
has the same component root `y`. -/
theorem IsComponentRoot.parent {F : Set ι} {y x : ι} (h : T.IsComponentRoot F y x) (hne : x ≠ y) :
    x ∈ T.edges ∧ x ∉ F ∧ T.IsComponentRoot F y (T.parent x) := by
  obtain ⟨hxe, hyp⟩ := h.reaches.ne_imp_mem_edges_and_reaches_parent T hne.symm
  refine ⟨hxe, h.notMem_of_reaches T hne h.reaches (T.reaches_refl (h.verts_right T)), ?_⟩
  refine ⟨hyp, h.root_or_mem, fun g hgy hyg hgp ↦ ?_⟩
  exact h.notMem_of_reaches T hgy hyg (hgp.trans T (T.reaches_parent (h.verts_right T)))

/-- Any vertex on the directed path from a component root `y` to `x` also has component root `y`. -/
theorem IsComponentRoot.intermediate {F : Set ι} {y g x : ι} (h : T.IsComponentRoot F y x)
    (hyg : T.Reaches y g) (hgx : T.Reaches g x) : T.IsComponentRoot F y g :=
  ⟨hyg, h.root_or_mem, fun _ hzy hyz hzg ↦ h.notMem_of_reaches T hzy hyz (hzg.trans T hgx)⟩

private theorem exists_isComponentRoot_aux (F : Set ι) :
    ∀ (n : ℕ) {x : ι}, x ∈ T.verts → T.parent^[n] x = T.root → ∃ y, T.IsComponentRoot F y x
  | 0, x, _, h0 => ⟨T.root, h0 ▸ T.isComponentRoot_root F⟩
  | n + 1, x, hx, hn => by
    by_cases hxF : x = T.root ∨ x ∈ F
    · exact ⟨x, T.isComponentRoot_self hx hxF⟩
    · push Not at hxF
      rw [Function.iterate_succ_apply] at hn
      obtain ⟨y, hy⟩ := exists_isComponentRoot_aux F n (T.parent_mem x hx) hn
      exact ⟨y, hy.of_parent T hx hxF.2 hxF.1⟩

/-- Every vertex of `T` has a component root in `T \ F`. -/
theorem exists_isComponentRoot (F : Set ι) {x : ι} (hx : x ∈ T.verts) :
    ∃ y, T.IsComponentRoot F y x := by
  obtain ⟨n, hn⟩ := T.exists_iterate_eq_root x hx
  exact exists_isComponentRoot_aux T F n hx hn

@[simp]
theorem mem_componentAt {F : Set ι} {y x : ι} :
    x ∈ T.componentAt F y ↔ T.IsComponentRoot F y x := by
  classical
  simp only [componentAt, Finset.mem_filter, and_iff_right_iff_imp]
  exact IsComponentRoot.verts_right T

theorem componentAt_subset_verts (F : Set ι) (y : ι) : T.componentAt F y ⊆ T.verts := by
  intro x hx
  exact (T.mem_componentAt.1 hx).verts_right T

theorem self_mem_componentAt {F : Set ι} {y : ι} (hy : y ∈ T.verts) (hyF : y = T.root ∨ y ∈ F) :
    y ∈ T.componentAt F y :=
  T.mem_componentAt.2 (T.isComponentRoot_self hy hyF)

theorem disjoint_componentAt {F : Set ι} {y₁ y₂ : ι} (hne : y₁ ≠ y₂) :
    Disjoint (T.componentAt F y₁) (T.componentAt F y₂) := by
  classical
  rw [Finset.disjoint_left]
  intro x hx₁ hx₂
  exact hne ((T.mem_componentAt.1 hx₁).unique T (T.mem_componentAt.1 hx₂))

/-- The component of `T \ F` with root `y` as a `RootedTree`. -/
@[expose] noncomputable def componentTree (F : Set ι) (y : ι) (hy : y ∈ T.verts)
    (hyF : y = T.root ∨ y ∈ F) : RootedTree ι where
  verts := T.componentAt F y
  root := y
  parent := by classical exact fun x ↦ if x = y then y else T.parent x
  root_mem := T.self_mem_componentAt hy hyF
  parent_mem x hx := by
    classical
    split_ifs with hxy
    · exact T.self_mem_componentAt hy hyF
    · exact T.mem_componentAt.2 (((T.mem_componentAt.1 hx).parent T hxy).2.2)
  parent_root := by classical simp
  exists_iterate_eq_root x hx := by
    classical
    obtain ⟨_, n, hn⟩ := (T.mem_componentAt.1 hx).reaches
    exact ⟨n, iterate_update_root T.parent hn⟩

@[simp]
theorem componentTree_verts (F : Set ι) (y : ι) (hy : y ∈ T.verts) (hyF : y = T.root ∨ y ∈ F) :
    (T.componentTree F y hy hyF).verts = T.componentAt F y := rfl

@[simp]
theorem componentTree_root (F : Set ι) (y : ι) (hy : y ∈ T.verts) (hyF : y = T.root ∨ y ∈ F) :
    (T.componentTree F y hy hyF).root = y := rfl

theorem componentTree_parent_of_ne (F : Set ι) (y : ι) (hy : y ∈ T.verts)
    (hyF : y = T.root ∨ y ∈ F) {x : ι} (hx : x ≠ y) :
    (T.componentTree F y hy hyF).parent x = T.parent x := by
  classical simp [componentTree, hx]

/-- A vertex `f` is an edge of `T.componentTree F y` if and only if `f ∈ T.edges`, `f ∉ F`, and
`T.parent f` belongs to the component at `y`. -/
theorem mem_componentTree_edges_iff (F : Set ι) (y : ι) (hy : y ∈ T.verts)
    (hyF : y = T.root ∨ y ∈ F) {f : ι} :
    f ∈ (T.componentTree F y hy hyF).edges ↔
      f ∈ T.edges ∧ f ∉ F ∧ T.parent f ∈ (T.componentTree F y hy hyF).verts := by
  rw [mem_edges, componentTree_root, componentTree_verts, mem_componentAt, mem_componentAt]
  constructor
  · rintro ⟨hfy, hf⟩
    exact hf.parent T hfy
  · rintro ⟨hfe, hfF, hfp⟩
    have hfy : f ≠ y := by
      rintro rfl
      rcases hyF with hroot | hF
      · exact T.ne_root_of_mem_edges hfe hroot
      · exact hfF hF
    exact ⟨hfy, hfp.of_parent T (T.mem_verts_of_mem_edges hfe) hfF (T.ne_root_of_mem_edges hfe)⟩

private theorem iterate_componentTree_parent_reaches (F : Set ι) (y : ι) (hy : y ∈ T.verts)
    (hyF : y = T.root ∨ y ∈ F) {w : ι} (hw : w ∈ T.verts) :
    ∀ n : ℕ, T.Reaches ((T.componentTree F y hy hyF).parent^[n] w) w
  | 0 => T.reaches_refl hw
  | n + 1 => by
    rw [Function.iterate_succ_apply]
    classical
    change T.Reaches ((fun x ↦ if x = y then y else T.parent x)^[n]
      (if w = y then y else T.parent w)) w
    split_ifs with hwy
    · subst hwy
      have hfix : (fun x ↦ if x = w then w else T.parent x)^[n] w = w :=
        Function.iterate_fixed (by simp) n
      rw [hfix]
      exact T.reaches_refl hw
    · exact (iterate_componentTree_parent_reaches F y hy hyF (T.parent_mem w hw) n).trans T
        (T.reaches_parent hw)

private theorem iterate_parent_eq_in_componentTree (F : Set ι) (y : ι) (hy : y ∈ T.verts)
    (hyF : y = T.root ∨ y ∈ F) :
    ∀ {n : ℕ} {v w : ι}, T.IsComponentRoot F y v → T.parent^[n] w = v →
      (T.componentTree F y hy hyF).parent^[n] w = v
  | 0, _, _, _, rfl => rfl
  | n + 1, v, w, hv, h => by
    rw [Function.iterate_succ_apply] at h ⊢
    by_cases hwy : w = y
    · have hvy : v = y := by
        refine (hv.reaches.antisymm T ⟨hv.verts_left T, n + 1, ?_⟩).symm
        rw [← hwy, Function.iterate_succ_apply, h]
      rw [hwy, hvy]
      have hfix := Function.iterate_fixed (T.componentTree F y hy hyF).parent_root (n + 1)
      rw [Function.iterate_succ_apply] at hfix
      exact hfix
    · rw [T.componentTree_parent_of_ne F y hy hyF hwy]
      exact iterate_parent_eq_in_componentTree F y hy hyF hv h

/-- Within a component of `T \ F`, reachability in the component tree agrees with reachability in
`T`. -/
theorem componentTree_reaches_iff (F : Set ι) (y : ι) (hy : y ∈ T.verts)
    (hyF : y = T.root ∨ y ∈ F) {v w : ι}
    (hv : v ∈ (T.componentTree F y hy hyF).verts) :
    (T.componentTree F y hy hyF).Reaches v w ↔
      w ∈ (T.componentTree F y hy hyF).verts ∧ T.Reaches v w := by
  constructor
  · rintro ⟨hw, n, rfl⟩
    have hwT : w ∈ T.verts := T.componentAt_subset_verts F y hw
    exact ⟨hw, iterate_componentTree_parent_reaches T F y hy hyF hwT n⟩
  · rintro ⟨hw, _, n, rfl⟩
    refine ⟨hw, n, ?_⟩
    exact iterate_parent_eq_in_componentTree T F y hy hyF (T.mem_componentAt.1 hv) rfl

/-- If `v` precedes `w` in `T.componentTree F y` with respect to `e ↦ φ e - 1`, where `F` is the
set of edges with `φ e = 0`, then `v` precedes `w` in `T` with respect to `φ`. -/
theorem componentTree_precedes {φ : ι → ℕ} {F : Set ι}
    (hF : ∀ e ∈ T.edges, e ∈ F ↔ φ e = 0) (y : ι) (hy : y ∈ T.verts)
    (hyF : y = T.root ∨ y ∈ F) {v w : ι} (hv : v ∈ (T.componentTree F y hy hyF).verts) :
    (T.componentTree F y hy hyF).Precedes (fun e ↦ φ e - 1) v w → T.Precedes φ v w := by
  rintro ⟨hvy, hvwR, hφvw, hpath⟩
  dsimp only at hφvw
  have hve_comp : v ∈ (T.componentTree F y hy hyF).edges :=
    (T.componentTree F y hy hyF).mem_edges.2 ⟨hvy, hv⟩
  obtain ⟨hve, hvF, -⟩ := (T.mem_componentTree_edges_iff F y hy hyF).1 hve_comp
  obtain ⟨hw_comp, hvwT⟩ := (T.componentTree_reaches_iff F y hy hyF hv).1 hvwR
  have hwy : w ≠ y := by
    intro hwy_eq
    rw [hwy_eq] at hvwR
    exact hvy ((T.componentTree F y hy hyF).reaches_root_iff.1 hvwR)
  have hwe_comp : w ∈ (T.componentTree F y hy hyF).edges :=
    (T.componentTree F y hy hyF).mem_edges.2 ⟨hwy, hw_comp⟩
  obtain ⟨hwe, hwF, -⟩ := (T.mem_componentTree_edges_iff F y hy hyF).1 hwe_comp
  have hφv : φ v ≠ 0 := mt (hF v hve).2 hvF
  have hφw : φ w ≠ 0 := mt (hF w hwe).2 hwF
  refine ⟨T.ne_root_of_mem_edges hve, hvwT, by omega, fun g hgv hvg hgw ↦ ?_⟩
  have hg_comp : g ∈ (T.componentTree F y hy hyF).verts := by
    rw [componentTree_verts, mem_componentAt]
    exact (T.mem_componentAt.1 hw_comp).intermediate T
      (((T.mem_componentAt.1 hv).reaches).trans T hvg) hgw
  have hvgR : (T.componentTree F y hy hyF).Reaches v g :=
    (T.componentTree_reaches_iff F y hy hyF hv).2 ⟨hg_comp, hvg⟩
  have hgy : g ≠ y := by
    intro hgy_eq
    rw [hgy_eq] at hvgR
    exact hvy ((T.componentTree F y hy hyF).reaches_root_iff.1 hvgR)
  have hge_comp : g ∈ (T.componentTree F y hy hyF).edges :=
    (T.componentTree F y hy hyF).mem_edges.2 ⟨hgy, hg_comp⟩
  obtain ⟨hge, hgF, -⟩ := (T.mem_componentTree_edges_iff F y hy hyF).1 hge_comp
  have hφg : φ g ≠ 0 := mt (hF g hge).2 hgF
  have hgwR : (T.componentTree F y hy hyF).Reaches g w :=
    (T.componentTree_reaches_iff F y hy hyF hg_comp).2 ⟨hw_comp, hgw⟩
  have hle := hpath g hgv hvgR hgwR
  dsimp only at hle
  omega

/-- The root of the component of `T \ F` containing `x` (or `T.root` if `x ∉ T.verts`). -/
noncomputable def compRoot (F : Set ι) (x : ι) : ι := by
  classical exact if hx : x ∈ T.verts then (T.exists_isComponentRoot F hx).choose else T.root

theorem compRoot_spec (F : Set ι) {x : ι} (hx : x ∈ T.verts) :
    T.IsComponentRoot F (T.compRoot F x) x := by
  classical
  simp only [compRoot, hx, ↓reduceDIte]
  exact (T.exists_isComponentRoot F hx).choose_spec

theorem compRoot_eq_iff (F : Set ι) {x y : ι} (hx : x ∈ T.verts) :
    T.compRoot F x = y ↔ T.IsComponentRoot F y x :=
  ⟨fun h ↦ h ▸ T.compRoot_spec F hx, fun h ↦ (T.compRoot_spec F hx).unique T h⟩

@[simp]
theorem compRoot_root (F : Set ι) : T.compRoot F T.root = T.root :=
  (T.compRoot_eq_iff F T.root_mem).2 (T.isComponentRoot_root F)

theorem compRoot_mem (F : Set ι) {x : ι} (hx : x ∈ T.verts) :
    T.compRoot F x = T.root ∨ T.compRoot F x ∈ F ∩ T.edges := by
  have h := T.compRoot_spec F hx
  rcases h.root_or_mem with hroot | hF
  · exact Or.inl hroot
  · by_cases hr : T.compRoot F x = T.root
    · exact Or.inl hr
    · exact Or.inr ⟨hF, T.mem_edges.2 ⟨hr, h.verts_left T⟩⟩

private theorem iterate_compRoot_parent_eq_root (F : Set ι) :
    ∀ (n : ℕ) {v : ι}, v ∈ T.verts → T.parent^[n] v = T.root →
      (fun x ↦ T.compRoot F (T.parent x))^[n] v = T.root
  | 0, _, _, h0 => h0
  | n + 1, v, hv, hn => by
    rw [Function.iterate_succ_apply]
    have hpv : T.parent v ∈ T.verts := T.parent_mem v hv
    have hspec := T.compRoot_spec F hpv
    have hw : T.compRoot F (T.parent v) ∈ T.verts := hspec.verts_left T
    obtain ⟨_, k, hk⟩ := hspec.reaches
    have hnw : T.parent^[n] (T.compRoot F (T.parent v)) = T.root := by
      rw [← hk, ← Function.iterate_add_apply, add_comm, Function.iterate_add_apply,
        ← Function.iterate_succ_apply T.parent n v, hn, T.iterate_parent_root]
    exact iterate_compRoot_parent_eq_root F n hw hnw

/-- The contraction of `T` onto `F` exists. -/
theorem exists_isContraction (F : Set ι) (_hF : F ⊆ T.edges) :
    ∃ S : RootedTree ι, T.IsContraction F S := by
  classical
  refine ⟨{
    verts := insert T.root (T.edges.filter (· ∈ F))
    root := T.root
    parent := fun x ↦ T.compRoot F (T.parent x)
    root_mem := Finset.mem_insert_self T.root _
    parent_mem := fun v hv ↦ by
      have hvT : v ∈ T.verts := by
        rcases Finset.mem_insert.1 hv with rfl | hv'
        · exact T.root_mem
        · exact T.edges_subset_verts (Finset.mem_of_mem_filter v hv')
      rcases T.compRoot_mem F (T.parent_mem v hvT) with hr | ⟨hF', hE'⟩
      · exact Finset.mem_insert.2 (Or.inl hr)
      · exact Finset.mem_insert.2 (Or.inr (Finset.mem_filter.2 ⟨hE', hF'⟩))
    parent_root := by rw [T.parent_root, T.compRoot_root]
    exists_iterate_eq_root := fun v hv ↦ by
      have hvT : v ∈ T.verts := by
        rcases Finset.mem_insert.1 hv with rfl | hv'
        · exact T.root_mem
        · exact T.edges_subset_verts (Finset.mem_of_mem_filter v hv')
      obtain ⟨n, hn⟩ := T.exists_iterate_eq_root v hvT
      exact ⟨n, iterate_compRoot_parent_eq_root T F n hvT hn⟩
  }, ?_⟩
  refine ⟨?_, rfl, fun f hf ↦ ?_⟩
  · ext x
    simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_filter, Set.mem_insert_iff,
      Set.mem_inter_iff, and_comm]
  · have hfT : f ∈ T.verts := by
      rcases Finset.mem_insert.1 (Finset.mem_of_mem_erase hf) with rfl | hf'
      · exact T.root_mem
      · exact T.edges_subset_verts (Finset.mem_of_mem_filter f hf')
    exact T.compRoot_spec F (T.parent_mem f hfT)

/-! ### Lemmas about `IsContraction` -/

theorem IsContraction.mem_verts_iff {F : Set ι} {S : RootedTree ι} (hS : T.IsContraction F S)
    {v : ι} : v ∈ S.verts ↔ v = T.root ∨ v ∈ F ∧ v ∈ T.edges := by
  rw [← Finset.mem_coe, hS.verts_eq, Set.mem_insert_iff, Set.mem_inter_iff, Finset.mem_coe]

theorem IsContraction.verts_subset {F : Set ι} {S : RootedTree ι} (hS : T.IsContraction F S) :
    S.verts ⊆ T.verts := by
  intro v hv
  rcases hS.mem_verts_iff.1 hv with rfl | ⟨-, hve⟩
  · exact T.root_mem
  · exact T.edges_subset_verts hve

theorem IsContraction.mem_edges_iff {F : Set ι} {S : RootedTree ι} (hS : T.IsContraction F S)
    {v : ι} : v ∈ S.edges ↔ v ∈ F ∧ v ∈ T.edges := by
  rw [S.mem_edges, hS.root_eq, hS.mem_verts_iff]
  constructor
  · rintro ⟨hne, rfl | h⟩
    · exact absurd rfl hne
    · exact h
  · rintro ⟨hvF, hve⟩
    exact ⟨T.ne_root_of_mem_edges hve, Or.inr ⟨hvF, hve⟩⟩

theorem IsContraction.reaches_parent_in_tree {F : Set ι} {S : RootedTree ι}
    (hS : T.IsContraction F S) {v : ι} (hv : v ∈ S.verts) : T.Reaches (S.parent v) v := by
  by_cases hvr : v = S.root
  · rw [hvr, S.parent_root, hS.root_eq]
    exact T.reaches_refl T.root_mem
  · have hve : v ∈ S.edges := S.mem_edges.2 ⟨hvr, hv⟩
    exact (hS.parent_eq v hve).reaches.trans T (T.reaches_parent (hS.verts_subset T hv))

private theorem IsContraction.iterate_reaches {F : Set ι} {S : RootedTree ι}
    (hS : T.IsContraction F S) {w : ι} (hw : w ∈ S.verts) :
    ∀ n : ℕ, T.Reaches (S.parent^[n] w) w
  | 0 => T.reaches_refl (hS.verts_subset T hw)
  | n + 1 => by
    rw [Function.iterate_succ_apply']
    exact (hS.reaches_parent_in_tree T (S.iterate_parent_mem hw n)).trans T
      (hS.iterate_reaches hw n)

/-- Reachability in a contraction `S` of `T` implies reachability in `T`. -/
theorem IsContraction.reaches_imp {F : Set ι} {S : RootedTree ι} (hS : T.IsContraction F S)
    {v w : ι} (h : S.Reaches v w) : T.Reaches v w := by
  obtain ⟨hw, n, rfl⟩ := h
  exact hS.iterate_reaches T hw n

end RootedTree

/-! ### Lemmas about `IsRich` -/

/-- A subset of an `M`-rich set is `M`-rich. -/
theorem IsRich.mono {M : SimpleGraph ι} {X X' : Set ι} (h : IsRich M X) (hsub : X' ⊆ X) :
    IsRich M X' :=
  fun Y hY hInd ↦ h Y (hY.trans hsub) hInd

/-- The union of two `M`-rich sets is `M`-rich. -/
theorem IsRich.union {M : SimpleGraph ι} {A B : Set ι} (hA : IsRich M A) (hB : IsRich M B) :
    IsRich M (A ∪ B) := by
  intro Y hY hInd
  have hYA : (Y ∩ A).Finite := hA (Y ∩ A) Set.inter_subset_right (hInd.mono Set.inter_subset_left)
  have hYB : (Y ∩ B).Finite := hB (Y ∩ B) Set.inter_subset_right (hInd.mono Set.inter_subset_left)
  have hYeq : Y = (Y ∩ A) ∪ (Y ∩ B) := by
    ext x
    simp only [Set.mem_union, Set.mem_inter_iff]
    exact ⟨fun hx ↦ (hY hx).imp (fun ha ↦ ⟨hx, ha⟩) (fun hb ↦ ⟨hx, hb⟩),
      fun h ↦ h.elim And.left And.left⟩
  rw [hYeq]
  exact hYA.union hYB

end GraphMinor.GM04
