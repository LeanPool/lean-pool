/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM04.TreeDecomposition
public import LeanPool.GraphMinor.Thomas.Claims
import LeanPool.GraphMinor.GM04.TreeLemma.Basic

/-!
# Translation between `GM04.RootedTree` and undirected trees

This file connects the directed rooted trees `GraphMinor.GM04.RootedTree` of Graph Minors IV
(Section 2) with the undirected trees (`SimpleGraph.IsTree`) used in Bellenbaum and Diestel's
proof of Thomas's lemma.

## Main definitions and results

* `GraphMinor.Thomas.cross_subtreeAt_inter_rootSide_vertexSet` and
  `GraphMinor.Thomas.edgeOrder_eq_ncard_inter`: for any tree-decomposition `(T, τ)` of `G` and any
  edge `f ∈ T.edges`, `edgeOrder T τ f = ((τ f).vertexSet ∩ (τ (T.parent f)).vertexSet).ncard`.
* `GraphMinor.Thomas.toSimpleGraph`: the underlying undirected graph of `T : RootedTree ι` on
  `T.verts`.
* `GraphMinor.Thomas.toSimpleGraph_isTree`: `toSimpleGraph T` is an undirected tree.
* `GraphMinor.Thomas.onTreePath_toSimpleGraph_iff`: `OnTreePath (toSimpleGraph T) t₁ t₂ t`
  agrees with `T.OnPath t₁.1 t₂.1 t.1`.
* `GraphMinor.Thomas.rootedTreeOfIsTree`: constructs a `RootedTree ℕ` on `Finset.range m` from an
  undirected tree on `Fin m`.
-/

namespace GraphMinor.Thomas

open SimpleGraph GraphMinor.GM04

universe u

@[expose] public section

/-! ## Elementary properties of `GM04.RootedTree` -/

section RootedTreeProps

variable {ι : Type u} (T : RootedTree ι)

theorem mem_verts_of_mem_edges {f : ι} (hf : f ∈ T.edges) : f ∈ T.verts :=
  GM04.RootedTree.mem_verts_of_mem_edges T hf

theorem ne_root_of_mem_edges {f : ι} (hf : f ∈ T.edges) : f ≠ T.root :=
  GM04.RootedTree.ne_root_of_mem_edges T hf

theorem mem_edges_iff {f : ι} : f ∈ T.edges ↔ f ∈ T.verts ∧ f ≠ T.root :=
  (GM04.RootedTree.mem_edges T).trans and_comm

theorem iterate_parent_mem {v : ι} (hv : v ∈ T.verts) (n : ℕ) :
    T.parent^[n] v ∈ T.verts :=
  GM04.RootedTree.iterate_parent_mem T hv n

theorem iterate_parent_root (n : ℕ) : T.parent^[n] T.root = T.root :=
  GM04.RootedTree.iterate_parent_root T n

theorem iterate_parent_eq_root_of_le {v : ι} {n m : ℕ}
    (hn : T.parent^[n] v = T.root) (hle : n ≤ m) :
    T.parent^[m] v = T.root :=
  GM04.RootedTree.iterate_parent_eq_root_of_le T hn hle

theorem not_iterate_succ_eq_self {v : ι} (hv : v ∈ T.verts) (hne : v ≠ T.root) (n : ℕ) :
    T.parent^[n + 1] v ≠ v :=
  fun h => hne (GM04.RootedTree.eq_root_of_iterate_eq_self T hv (Nat.succ_pos n) h)

theorem reaches_refl {v : ι} (hv : v ∈ T.verts) : T.Reaches v v :=
  GM04.RootedTree.reaches_refl T hv

theorem reaches_mem_left {u v : ι} (h : T.Reaches u v) : u ∈ T.verts :=
  GM04.RootedTree.Reaches.verts_left T h

theorem reaches_trans {u v w : ι} (huv : T.Reaches u v) (hvw : T.Reaches v w) :
    T.Reaches u w :=
  GM04.RootedTree.Reaches.trans T huv hvw

theorem reaches_antisymm {u v : ι} (huv : T.Reaches u v) (hvu : T.Reaches v u) :
    u = v :=
  GM04.RootedTree.Reaches.antisymm T huv hvu

theorem reaches_total_of_reaches {u v w : ι} (hu : T.Reaches u w) (hv : T.Reaches v w) :
    T.Reaches u v ∨ T.Reaches v u :=
  GM04.RootedTree.Reaches.total_of_reaches T hu hv

theorem reaches_root_iff {u : ι} : T.Reaches u T.root ↔ u = T.root :=
  GM04.RootedTree.reaches_root_iff T

theorem onPath_subtreeAt_rootSide {f t s : ι} (hf : f ∈ T.edges)
    (ht : t ∈ T.subtreeAt f) (hs : s ∈ T.rootSide f) :
    T.OnPath t s f ∧ T.OnPath t s (T.parent f) := by
  classical
  unfold RootedTree.subtreeAt at ht
  unfold RootedTree.rootSide RootedTree.subtreeAt at hs
  rw [Finset.mem_filter] at ht
  rw [Finset.mem_sdiff, Finset.mem_filter, not_and] at hs
  have hft : T.Reaches f t := ht.2
  have hs_verts : s ∈ T.verts := hs.1
  have hnot_fs : ¬ T.Reaches f s := hs.2 hs_verts
  have hf_parent : T.Reaches (T.parent f) f := ⟨mem_verts_of_mem_edges T hf, 1, rfl⟩
  have h_common : ∀ x, T.Reaches x t → T.Reaches x s → T.Reaches x f := by
    intro x hxt hxs
    rcases reaches_total_of_reaches T hxt hft with hxf | hfx
    · exact hxf
    · exact (hnot_fs (reaches_trans T hfx hxs)).elim
  refine ⟨⟨Or.inl hft, h_common⟩, ⟨Or.inl (reaches_trans T hf_parent hft), ?_⟩⟩
  intro x hxt hxs
  have hxf := h_common x hxt hxs
  obtain ⟨_, n, rfl⟩ := hxf
  rcases n with _ | n
  · exact (hnot_fs hxs).elim
  · refine ⟨T.parent_mem f (mem_verts_of_mem_edges T hf), n, ?_⟩
    rw [← Function.iterate_succ_apply]

/-! ## `edgeOrder` of an edge in any `GM04.IsTreeDecomposition` -/

/-- For any tree-decomposition `(T, τ)` of `G` and any edge `f ∈ T.edges`, the intersection of
`τ × T^f` and `τ × T_f` has vertex set `V(τ(f)) ∩ V(τ(parent f))`. -/
theorem cross_subtreeAt_inter_rootSide_vertexSet {α β : Type*} {G : RootedHypergraph α β}
    {τ : ι → RootedHypergraph α β} (hD : IsTreeDecomposition G T τ)
    {f : ι} (hf : f ∈ T.edges) :
    ((cross τ (T.subtreeAt f) f).toHypergraph ∩
      (cross τ (T.rootSide f) T.root).toHypergraph).vertexSet =
      (τ f).vertexSet ∩ (τ (T.parent f)).vertexSet := by
  classical
  have hf_verts : f ∈ T.verts := mem_verts_of_mem_edges T hf
  have hf_ne_root : f ≠ T.root := ne_root_of_mem_edges T hf
  have hparent_verts : T.parent f ∈ T.verts := T.parent_mem f hf_verts
  have hf_sub : f ∈ T.subtreeAt f := by
    unfold RootedTree.subtreeAt
    exact Finset.mem_filter.2 ⟨hf_verts, reaches_refl T hf_verts⟩
  have hroot_side : T.root ∈ T.rootSide f := by
    unfold RootedTree.rootSide RootedTree.subtreeAt
    rw [Finset.mem_sdiff, Finset.mem_filter]
    refine ⟨T.root_mem, fun h ↦ hf_ne_root ((reaches_root_iff T).1 h.2)⟩
  have hparent_side : T.parent f ∈ T.rootSide f := by
    unfold RootedTree.rootSide RootedTree.subtreeAt
    rw [Finset.mem_sdiff, Finset.mem_filter]
    refine ⟨hparent_verts, fun h ↦ ?_⟩
    have hf_par : T.Reaches (T.parent f) f := ⟨hf_verts, 1, rfl⟩
    have heq := reaches_antisymm T h.2 hf_par
    exact not_iterate_succ_eq_self T hf_verts hf_ne_root 0 heq.symm
  have hins_f : insert f (T.subtreeAt f) = T.subtreeAt f := Finset.insert_eq_of_mem hf_sub
  have hins_r : insert T.root (T.rootSide f) = T.rootSide f := Finset.insert_eq_of_mem hroot_side
  ext v
  change (v ∈ ⋃ t ∈ insert f (T.subtreeAt f), (τ t).vertexSet) ∧
      (v ∈ ⋃ s ∈ insert T.root (T.rootSide f), (τ s).vertexSet) ↔
    v ∈ (τ f).vertexSet ∧ v ∈ (τ (T.parent f)).vertexSet
  rw [hins_f, hins_r, Set.mem_iUnion₂, Set.mem_iUnion₂]
  constructor
  · rintro ⟨⟨t, ht, hvt⟩, ⟨s, hs, hvs⟩⟩
    have ht_verts : t ∈ T.verts := by
      unfold RootedTree.subtreeAt at ht
      exact (Finset.mem_filter.1 ht).1
    have hs_verts : s ∈ T.verts := by
      unfold RootedTree.rootSide at hs
      exact (Finset.mem_sdiff.1 hs).1
    have ⟨hon_f, hon_p⟩ := onPath_subtreeAt_rootSide T hf ht hs
    have hvf : v ∈ (τ f).vertexSet :=
      (hD.inter_le t ht_verts f hf_verts s hs_verts hon_f).vertexSet_subset ⟨hvt, hvs⟩
    have hvp : v ∈ (τ (T.parent f)).vertexSet :=
      (hD.inter_le t ht_verts (T.parent f) hparent_verts s hs_verts hon_p).vertexSet_subset ⟨hvt,
        hvs⟩
    exact ⟨hvf, hvp⟩
  · rintro ⟨hvf, hvp⟩
    exact ⟨⟨f, hf_sub, hvf⟩, ⟨T.parent f, hparent_side, hvp⟩⟩

/-- For any tree-decomposition `(T, τ)` of `G` and any edge `f ∈ T.edges`, the order of `f` is
`|V(τ(f)) ∩ V(τ(parent f))|`. -/
theorem edgeOrder_eq_ncard_inter {α β : Type*} {G : RootedHypergraph α β}
    {τ : ι → RootedHypergraph α β} (hD : IsTreeDecomposition G T τ)
    {f : ι} (hf : f ∈ T.edges) :
    edgeOrder T τ f = ((τ f).vertexSet ∩ (τ (T.parent f)).vertexSet).ncard := by
  unfold edgeOrder Hypergraph.separationOrder
  rw [cross_subtreeAt_inter_rootSide_vertexSet T hD hf]

/-! ## Underlying `SimpleGraph` of a `RootedTree` -/

/-- The underlying undirected simple graph of a `RootedTree` on the subtype `T.verts`. -/
def toSimpleGraph : SimpleGraph T.verts where
  Adj u v := (u.1 ≠ T.root ∧ T.parent u.1 = v.1) ∨ (v.1 ≠ T.root ∧ T.parent v.1 = u.1)
  symm := ⟨fun _ _ h ↦ h.symm⟩
  loopless := ⟨fun u h ↦ by
    rcases h with ⟨hne, heq⟩ | ⟨hne, heq⟩ <;>
      exact not_iterate_succ_eq_self T u.2 hne 0 heq⟩

/-- The root of `T` as an element of `T.verts`. -/
def rootVert : T.verts := ⟨T.root, T.root_mem⟩

/-- The parent of `v : T.verts` as an element of `T.verts`. -/
def parentVert (v : T.verts) : T.verts := ⟨T.parent v.1, T.parent_mem v.1 v.2⟩

/-- The distance of `v : T.verts` to the root: the smallest `n` with `T.parent^[n] v.1 = T.root`. -/
noncomputable def depth (v : T.verts) : ℕ :=
  open Classical in
  Nat.find (T.exists_iterate_eq_root v.1 v.2)

theorem iterate_parent_depth (v : T.verts) :
    T.parent^[depth T v] v.1 = T.root := by
  classical
  exact Nat.find_spec (T.exists_iterate_eq_root v.1 v.2)

theorem depth_le_of_iterate_eq_root {v : T.verts} {n : ℕ} (h : T.parent^[n] v.1 = T.root) :
    depth T v ≤ n := by
  classical
  exact Nat.find_min' (T.exists_iterate_eq_root v.1 v.2) h

theorem depth_eq_zero_iff (v : T.verts) : depth T v = 0 ↔ v = rootVert T := by
  constructor
  · intro h0
    ext
    have h := iterate_parent_depth T v
    rw [h0] at h
    exact h
  · rintro rfl
    exact Nat.le_zero.1 (depth_le_of_iterate_eq_root T (n := 0) rfl)

theorem depth_parentVert (v : T.verts) (hne : v.1 ≠ T.root) :
    depth T (parentVert T v) + 1 = depth T v := by
  have hpos : 0 < depth T v := by
    by_contra h0
    have := (depth_eq_zero_iff T v).1 (Nat.le_zero.1 (not_lt.1 h0))
    exact hne (congrArg Subtype.val this)
  apply le_antisymm
  · have h1 : T.parent^[depth T v - 1] (parentVert T v).1 = T.root := by
      change T.parent^[depth T v - 1] (T.parent v.1) = T.root
      rw [← Function.iterate_succ_apply]
      have hsub : (depth T v - 1).succ = depth T v := Nat.sub_add_cancel hpos
      rw [hsub]
      exact iterate_parent_depth T v
    have hle := depth_le_of_iterate_eq_root T h1
    omega
  · have h2 : T.parent^[depth T (parentVert T v) + 1] v.1 = T.root := by
      rw [Function.iterate_succ_apply]
      exact iterate_parent_depth T (parentVert T v)
    exact depth_le_of_iterate_eq_root T h2

theorem adj_parentVert {v : T.verts} (hne : v.1 ≠ T.root) :
    (toSimpleGraph T).Adj v (parentVert T v) :=
  Or.inl ⟨hne, rfl⟩

theorem toSimpleGraph_adj_iff_parentVert {u v : T.verts} :
    (toSimpleGraph T).Adj u v ↔
      (u.1 ≠ T.root ∧ v = parentVert T u ∧ depth T v + 1 = depth T u) ∨
      (v.1 ≠ T.root ∧ u = parentVert T v ∧ depth T u + 1 = depth T v) := by
  constructor
  · rintro (⟨hne, heq⟩ | ⟨hne, heq⟩)
    · have hv : v = parentVert T u := Subtype.ext heq.symm
      subst hv
      exact Or.inl ⟨hne, rfl, depth_parentVert T u hne⟩
    · have hu : u = parentVert T v := Subtype.ext heq.symm
      subst hu
      exact Or.inr ⟨hne, rfl, depth_parentVert T v hne⟩
  · rintro (⟨hne, rfl, _⟩ | ⟨hne, rfl, _⟩)
    · exact Or.inl ⟨hne, rfl⟩
    · exact Or.inr ⟨hne, rfl⟩

/-- Auxiliary walk in `toSimpleGraph T` from `v` (with `depth T v ≤ n`) to `rootVert T`. -/
noncomputable def walkToRootAux : ∀ (n : ℕ) (v : T.verts), depth T v ≤ n →
    (toSimpleGraph T).Walk v (rootVert T)
  | 0, v, hn => Walk.nil.copy rfl ((depth_eq_zero_iff T v).1 (Nat.le_zero.1 hn))
  | n + 1, v, hn =>
    open Classical in
    if hv : v.1 = T.root then
      Walk.nil.copy rfl (Subtype.ext hv)
    else
      Walk.cons (adj_parentVert T hv)
        (walkToRootAux n (parentVert T v) (by have := depth_parentVert T v hv; omega))

/-- Canonical walk in `toSimpleGraph T` from `v` to `rootVert T`. -/
noncomputable def walkToRoot (v : T.verts) : (toSimpleGraph T).Walk v (rootVert T) :=
  walkToRootAux T (depth T v) v le_rfl

theorem mem_walkToRootAux_support_iff (n : ℕ) (v : T.verts) (hn : depth T v ≤ n) (w : T.verts) :
    w ∈ (walkToRootAux T n v hn).support ↔ T.Reaches w.1 v.1 := by
  classical
  induction n generalizing v with
  | zero =>
    have hv : v = rootVert T := (depth_eq_zero_iff T v).1 (Nat.le_zero.1 hn)
    dsimp [walkToRootAux]
    rw [Walk.support_copy, Walk.support_nil, List.mem_singleton]
    constructor
    · rintro rfl
      exact reaches_refl T w.2
    · intro h
      have hv_val : v.1 = T.root := congrArg Subtype.val hv
      rw [hv_val, reaches_root_iff T] at h
      exact Subtype.ext (h.trans hv_val.symm)
  | succ n ih =>
    dsimp [walkToRootAux]
    split_ifs with hv
    · rw [Walk.support_copy, Walk.support_nil, List.mem_singleton]
      constructor
      · rintro rfl
        exact reaches_refl T w.2
      · intro h
        rw [hv, reaches_root_iff T] at h
        exact Subtype.ext (h.trans hv.symm)
    · rw [Walk.support_cons, List.mem_cons, ih (parentVert T v)]
      constructor
      · rintro (rfl | ⟨_, k, hk⟩)
        · exact reaches_refl T w.2
        · exact ⟨v.2, k + 1, by rw [Function.iterate_succ_apply]; exact hk⟩
      · rintro ⟨_, k, hk⟩
        rcases k with _ | k
        · exact Or.inl (Subtype.ext hk.symm)
        · exact Or.inr ⟨(parentVert T v).2, k, by rw [Function.iterate_succ_apply] at hk; exact hk⟩

theorem mem_walkToRoot_support_iff (v w : T.verts) :
    w ∈ (walkToRoot T v).support ↔ T.Reaches w.1 v.1 :=
  mem_walkToRootAux_support_iff T (depth T v) v le_rfl w

theorem walkToRootAux_isPath (n : ℕ) (v : T.verts) (hn : depth T v ≤ n) :
    (walkToRootAux T n v hn).IsPath := by
  classical
  induction n generalizing v with
  | zero =>
    dsimp [walkToRootAux]
    rw [Walk.isPath_copy]
    exact Walk.IsPath.nil
  | succ n ih =>
    dsimp [walkToRootAux]
    split_ifs with hv
    · rw [Walk.isPath_copy]
      exact Walk.IsPath.nil
    · rw [Walk.cons_isPath_iff]
      refine ⟨ih (parentVert T v) _, ?_⟩
      rw [mem_walkToRootAux_support_iff T]
      intro hreach
      have h1 : T.Reaches (T.parent v.1) v.1 := ⟨v.2, 1, rfl⟩
      have heq := reaches_antisymm T hreach h1
      exact not_iterate_succ_eq_self T v.2 hv 0 heq.symm

theorem walkToRoot_isPath (v : T.verts) : (walkToRoot T v).IsPath :=
  walkToRootAux_isPath T (depth T v) v le_rfl

/-- Along any walk `Walk.cons hadj r` with `Nodup` support where the first step increases `depth`,
every subsequent step also increases `depth`. -/
private theorem depth_lt_of_cons_nodup {u x v : T.verts}
    (hadj : (toSimpleGraph T).Adj u x) (r : (toSimpleGraph T).Walk x v)
    (hnodup : (Walk.cons hadj r).support.Nodup) (hlt : depth T u < depth T x) :
    depth T u < depth T v := by
  induction r generalizing u with
  | nil => exact hlt
  | @cons x y v hadj₂ r' ih =>
    have hu_parent : u = parentVert T x := by
      rcases (toSimpleGraph_adj_iff_parentVert T).1 hadj with ⟨_, _, h⟩ | ⟨_, heq, _⟩
      · omega
      · exact heq
    have huy_ne : u ≠ y := by
      rw [Walk.support_cons, Walk.support_cons, List.nodup_cons] at hnodup
      intro heq
      exact hnodup.1 (by simp [heq])
    have hlt₂ : depth T x < depth T y := by
      rcases (toSimpleGraph_adj_iff_parentVert T).1 hadj₂ with ⟨_, heq, _⟩ | ⟨_, _, h⟩
      · exfalso
        exact huy_ne (hu_parent.trans heq.symm)
      · omega
    have hnodup' : (Walk.cons hadj₂ r').support.Nodup := by
      rw [Walk.support_cons, List.nodup_cons] at hnodup
      exact hnodup.2
    exact lt_trans hlt (ih hadj₂ hnodup' hlt₂)

theorem toSimpleGraph_isTree : (toSimpleGraph T).IsTree where
  connected :=
    { preconnected := fun u v ↦ (walkToRoot T u).reachable.trans (walkToRoot T v).reachable.symm
      nonempty := ⟨rootVert T⟩ }
  isAcyclic := by
    intro u c hc
    have hlen : 3 ≤ c.length := hc.three_le_length
    have h_no_up : ∀ {a : T.verts} (w : (toSimpleGraph T).Walk a a),
        w.IsCycle → ∀ {x : T.verts} (hadj : (toSimpleGraph T).Adj a x)
        (r : (toSimpleGraph T).Walk x a), w = Walk.cons hadj r → ¬ depth T a < depth T x := by
      intro a w hw x hadj r hw_eq hlt
      have hlen_w := hw.three_le_length
      rw [hw_eq] at hw hlen_w
      have hr_nodup : r.support.Nodup := hw.support_nodup
      cases r with
      | nil => simp at hlen_w
      | @cons x y a hadj₂ r' =>
        rw [Walk.length_cons, Walk.length_cons] at hlen_w
        have hr'_ne : ¬ r'.Nil := by
          cases r' with
          | nil => simp at hlen_w
          | cons _ _ => exact Walk.not_nil_cons
        have hay_ne : a ≠ y := by
          intro hya
          subst hya
          rw [Walk.support_cons, List.nodup_cons] at hr_nodup
          cases r' with
          | nil => exact hr'_ne Walk.Nil.nil
          | @cons a z a hadj₃ r'' =>
            rw [Walk.support_cons, List.nodup_cons] at hr_nodup
            exact hr_nodup.2.1 r''.end_mem_support
        have ha_parent : a = parentVert T x := by
          rcases (toSimpleGraph_adj_iff_parentVert T).1 hadj with ⟨_, _, h⟩ | ⟨_, heq, _⟩
          · omega
          · exact heq
        have hlt₂ : depth T x < depth T y := by
          rcases (toSimpleGraph_adj_iff_parentVert T).1 hadj₂ with ⟨_, heq, _⟩ | ⟨_, _, h⟩
          · exact (hay_ne (ha_parent.trans heq.symm)).elim
          · omega
        have hlt_xa := depth_lt_of_cons_nodup T hadj₂ r' hr_nodup hlt₂
        omega
    cases c with
    | nil => simp at hlen
    | @cons u x _ hadj r =>
      rcases (toSimpleGraph_adj_iff_parentVert T).1 hadj with ⟨_, hx_par, hdepth⟩ | ⟨_, _, hdepth⟩
      · -- u -> x goes down, so look at c.reverse
        have hrev_cycle : (Walk.cons hadj r).reverse.IsCycle := hc.reverse
        have hrev_len : 3 ≤ (Walk.cons hadj r).reverse.length := hrev_cycle.three_le_length
        generalize hcr : (Walk.cons hadj r).reverse = cr at hrev_cycle hrev_len
        cases cr with
        | nil => simp at hrev_len
        | @cons u z _ hadj_rev r_rev =>
          rcases (toSimpleGraph_adj_iff_parentVert T).1 hadj_rev with ⟨_, hz_par, _⟩ | ⟨_, _,
            hdepth_z⟩
          · -- Both x and z equal parentVert T u, so first and last edges of c are equal
            have hxz : x = z := hx_par.trans hz_par.symm
            subst hxz
            have hedges : (Walk.cons hadj r).reverse.edges = (Walk.cons hadj_rev r_rev).edges :=
              congrArg Walk.edges hcr
            rw [Walk.edges_reverse, Walk.edges_cons, List.reverse_cons, Walk.edges_cons] at hedges
            have hnodup := hc.edges_nodup
            rw [Walk.edges_cons, List.nodup_cons] at hnodup
            have hlen_r : 0 < r.edges.reverse.length := by
              rw [List.length_reverse, Walk.length_edges]
              rw [Walk.length_cons] at hlen
              omega
            cases hrev_list : r.edges.reverse with
            | nil =>
              rw [hrev_list] at hlen_r
              exact absurd hlen_r (lt_irrefl 0)
            | cons e es =>
              rw [hrev_list, List.cons_append, List.cons.injEq] at hedges
              have he_mem : e ∈ r.edges.reverse := by
                rw [hrev_list]
                exact List.Mem.head _
              rw [List.mem_reverse, hedges.1] at he_mem
              exact hnodup.1 he_mem
          · exact h_no_up (Walk.cons hadj_rev r_rev) hrev_cycle hadj_rev r_rev rfl (by omega)
      · exact h_no_up (Walk.cons hadj r) hc hadj r rfl (by omega)

theorem walkToRoot_eq_treePath (v : T.verts) :
    walkToRoot T v = treePath (toSimpleGraph_isTree T) v (rootVert T) :=
  eq_treePath (toSimpleGraph_isTree T) (walkToRoot T v) (walkToRoot_isPath T v)

theorem onTreePath_toSimpleGraph_rootVert_iff (v w : T.verts) :
    OnTreePath (toSimpleGraph T) v (rootVert T) w ↔ T.Reaches w.1 v.1 := by
  rw [onTreePath_iff_mem_treePath (toSimpleGraph_isTree T), ← walkToRoot_eq_treePath T,
    mem_walkToRoot_support_iff T]

theorem onTreePath_imp_onPath {t₁ t₂ t : T.verts}
    (ht : OnTreePath (toSimpleGraph T) t₁ t₂ t) :
    T.OnPath t₁.1 t₂.1 t.1 := by
  have hK := toSimpleGraph_isTree T
  refine ⟨?_, ?_⟩
  · rcases onTreePath_left_or_right hK (rootVert T) ht with h1 | h2
    · exact Or.inl ((onTreePath_toSimpleGraph_rootVert_iff T t₁ t).1 h1)
    · exact Or.inr ((onTreePath_toSimpleGraph_rootVert_iff T t₂ t).1 (onTreePath_symm h2))
  · intro x hx₁ hx₂
    let xv : T.verts := ⟨x, reaches_mem_left T hx₁⟩
    have hx₁' : OnTreePath (toSimpleGraph T) t₁ (rootVert T) xv :=
      (onTreePath_toSimpleGraph_rootVert_iff T t₁ xv).2 hx₁
    have hx₂' : OnTreePath (toSimpleGraph T) t₂ (rootVert T) xv :=
      (onTreePath_toSimpleGraph_rootVert_iff T t₂ xv).2 hx₂
    rcases onTreePath_left_or_right hK t hx₁' with h1 | h1
    · rcases onTreePath_left_or_right hK t hx₂' with h2 | h2
      · have hxv_t : xv = t :=
          onTreePath_inter_eq_of_onTreePath hK ht h1 (onTreePath_symm h2)
        have hxv_val : x = t.1 := congrArg Subtype.val hxv_t
        rw [hxv_val]
        exact reaches_refl T t.2
      · exact (onTreePath_toSimpleGraph_rootVert_iff T t xv).1 h2
    · exact (onTreePath_toSimpleGraph_rootVert_iff T t xv).1 h1

theorem exists_common_reaches_onTreePath (t₁ t₂ : T.verts) :
    ∃ x : T.verts, OnTreePath (toSimpleGraph T) t₁ t₂ x ∧
      T.Reaches x.1 t₁.1 ∧ T.Reaches x.1 t₂.1 := by
  have hK := toSimpleGraph_isTree T
  by_cases ht₂ : T.Reaches t₂.1 t₁.1
  · exact ⟨t₂, onTreePath_right _ t₁ t₂, ht₂, reaches_refl T t₂.2⟩
  · obtain ⟨x, y, he, hx_r, hy_not_r⟩ :=
      exists_onTreePathEdge_of_prop hK (fun s : T.verts ↦ T.Reaches s.1 t₁.1)
        (reaches_refl T t₁.2) ht₂
    have hx_par_y : x = parentVert T y := by
      rcases (toSimpleGraph_adj_iff_parentVert T).1 he.1 with ⟨_, hy_par, _⟩ | ⟨_, hx_par, _⟩
      · exfalso
        have hyx : T.Reaches y.1 x.1 := ⟨x.2, 1, (congrArg Subtype.val hy_par).symm⟩
        exact hy_not_r (reaches_trans T hyx hx_r)
      · exact hx_par
    have hxy : T.Reaches x.1 y.1 := ⟨y.2, 1, (congrArg Subtype.val hx_par_y).symm⟩
    have hy_on : T.OnPath t₁.1 t₂.1 y.1 := onTreePath_imp_onPath T he.onTreePath_right
    rcases hy_on.1 with hyt₁ | hyt₂
    · exact (hy_not_r hyt₁).elim
    · exact ⟨x, he.onTreePath_left, hx_r, reaches_trans T hxy hyt₂⟩

theorem onTreePath_toSimpleGraph_iff (t₁ t₂ t : T.verts) :
    OnTreePath (toSimpleGraph T) t₁ t₂ t ↔ T.OnPath t₁.1 t₂.1 t.1 := by
  have hK := toSimpleGraph_isTree T
  refine ⟨onTreePath_imp_onPath T, fun ht ↦ ?_⟩
  obtain ⟨x, hx_path, hx₁, hx₂⟩ := exists_common_reaches_onTreePath T t₁ t₂
  have hxt : OnTreePath (toSimpleGraph T) t (rootVert T) x :=
    (onTreePath_toSimpleGraph_rootVert_iff T t x).2 (ht.2 x.1 hx₁ hx₂)
  rcases ht.1 with ht₁ | ht₂
  · have ht₁' : OnTreePath (toSimpleGraph T) t₁ (rootVert T) t :=
      (onTreePath_toSimpleGraph_rootVert_iff T t₁ t).2 ht₁
    rcases onTreePath_left_or_right hK x ht₁' with h1 | h2
    · exact onTreePath_trans_left hK hx_path h1
    · have htx : t = x :=
        onTreePath_antisymm hK (onTreePath_symm h2) (onTreePath_symm hxt)
      exact htx ▸ hx_path
  · have ht₂' : OnTreePath (toSimpleGraph T) t₂ (rootVert T) t :=
      (onTreePath_toSimpleGraph_rootVert_iff T t₂ t).2 ht₂
    rcases onTreePath_left_or_right hK x ht₂' with h1 | h2
    · exact onTreePath_symm (onTreePath_trans_left hK (onTreePath_symm hx_path) h1)
    · have htx : t = x :=
        onTreePath_antisymm hK (onTreePath_symm h2) (onTreePath_symm hxt)
      exact htx ▸ hx_path

theorem exists_onPathEdge_of_onTreePathEdge {t₁ t₂ s s' : T.verts}
    (he : OnTreePathEdge (toSimpleGraph T) t₁ t₂ s s') :
    ∃ f : T.verts, f.1 ∈ T.edges ∧ T.OnPathEdge t₁.1 t₂.1 f.1 ∧
      (s = f ∧ s' = parentVert T f ∨ s' = f ∧ s = parentVert T f) := by
  have hs_on : T.OnPath t₁.1 t₂.1 s.1 :=
    (onTreePath_toSimpleGraph_iff T t₁ t₂ s).1 he.onTreePath_left
  have hs'_on : T.OnPath t₁.1 t₂.1 s'.1 :=
    (onTreePath_toSimpleGraph_iff T t₁ t₂ s').1 he.onTreePath_right
  rcases (toSimpleGraph_adj_iff_parentVert T).1 he.1 with ⟨hne, hs', _⟩ | ⟨hne, hs, _⟩
  · refine ⟨s, (mem_edges_iff T).2 ⟨s.2, hne⟩, ⟨(mem_edges_iff T).2 ⟨s.2, hne⟩, hs_on, ?_⟩,
      Or.inl ⟨rfl, hs'⟩⟩
    have hps : T.parent s.1 = s'.1 := (congrArg Subtype.val hs').symm
    rwa [hps]
  · refine ⟨s', (mem_edges_iff T).2 ⟨s'.2, hne⟩, ⟨(mem_edges_iff T).2 ⟨s'.2, hne⟩, hs'_on, ?_⟩,
      Or.inr ⟨rfl, hs⟩⟩
    have hps' : T.parent s'.1 = s.1 := (congrArg Subtype.val hs).symm
    rwa [hps']

end RootedTreeProps

/-! ## Constructing a `RootedTree ℕ` from an undirected tree on `Fin m` -/

section FromIsTree

variable {m : ℕ} {K : SimpleGraph (Fin m)}

theorem pos_of_isTree (hK : K.IsTree) : 0 < m := by
  obtain ⟨x⟩ := hK.connected.nonempty
  exact x.pos

/-- The chosen root `⟨0, hm⟩ : Fin m` of an undirected tree on `Fin m`. -/
def treeRootFin (hK : K.IsTree) : Fin m :=
  ⟨0, pos_of_isTree hK⟩

/-- The parent of `u : Fin m` in `(K, hK)` with respect to `treeRootFin hK`: the second vertex on
the unique path from `u` to the root (and the root itself if `u` is the root). -/
noncomputable def parentFin (hK : K.IsTree) (u : Fin m) : Fin m :=
  if u = treeRootFin hK then treeRootFin hK
  else (treePath hK u (treeRootFin hK)).getVert 1

theorem treePath_eq_cons_parentFin (hK : K.IsTree) {u : Fin m} (hu : u ≠ treeRootFin hK) :
    ∃ (hadj : K.Adj u (parentFin hK u)),
      treePath hK u (treeRootFin hK) =
        Walk.cons hadj (treePath hK (parentFin hK u) (treeRootFin hK)) := by
  generalize hp : treePath hK u (treeRootFin hK) = p
  cases p with
  | nil => exact (hu rfl).elim
  | @cons _ v _ hadj q =>
    have hpar : parentFin hK u = v := by
      unfold parentFin
      rw [ite_eq_right hu, hp, Walk.getVert_cons_succ, Walk.getVert_zero]
    subst hpar
    refine ⟨hadj, ?_⟩
    have hpath : (Walk.cons hadj q).IsPath := hp ▸ treePath_isPath hK u (treeRootFin hK)
    have hq_path : q.IsPath := hpath.of_cons
    rw [eq_treePath hK q hq_path]

theorem treeDist_parentFin (hK : K.IsTree) {u : Fin m} (hu : u ≠ treeRootFin hK) :
    treeDist hK (parentFin hK u) (treeRootFin hK) + 1 = treeDist hK u (treeRootFin hK) := by
  obtain ⟨hadj, heq⟩ := treePath_eq_cons_parentFin hK hu
  unfold treeDist
  rw [heq, Walk.length_cons]

theorem iterate_parentFin_treeDist (hK : K.IsTree) (u : Fin m) :
    (parentFin hK)^[treeDist hK u (treeRootFin hK)] u = treeRootFin hK := by
  generalize hd : treeDist hK u (treeRootFin hK) = d
  induction d generalizing u with
  | zero =>
    by_contra hne
    exact absurd hd (ne_of_gt (treeDist_pos_of_ne hK hne))
  | succ d ih =>
    have hu : u ≠ treeRootFin hK := by
      rintro rfl
      rw [treeDist_self] at hd
      exact Nat.noConfusion hd
    have hpar_d : treeDist hK (parentFin hK u) (treeRootFin hK) = d := by
      have := treeDist_parentFin hK hu
      omega
    rw [Function.iterate_succ_apply]
    exact ih (parentFin hK u) hpar_d

private theorem parentFin_eq_of_not_onTreePath (hK : K.IsTree) {u v : Fin m}
    (hadj : K.Adj u v) (hnot : ¬ OnTreePath K v (treeRootFin hK) u) :
    u ≠ treeRootFin hK ∧ parentFin hK u = v := by
  have hu_not_supp : u ∉ (treePath hK v (treeRootFin hK)).support := by
    rwa [← onTreePath_iff_mem_treePath hK]
  have hpath : (Walk.cons hadj (treePath hK v (treeRootFin hK))).IsPath := by
    rw [Walk.cons_isPath_iff]
    exact ⟨treePath_isPath hK v (treeRootFin hK), hu_not_supp⟩
  have heq := eq_treePath hK _ hpath
  have hu_ne : u ≠ treeRootFin hK := by
    rintro rfl
    exact hnot (onTreePath_right K v (treeRootFin hK))
  refine ⟨hu_ne, ?_⟩
  unfold parentFin
  rw [ite_eq_right hu_ne, ← heq, Walk.getVert_cons_succ, Walk.getVert_zero]

theorem adj_iff_parentFin (hK : K.IsTree) (u v : Fin m) :
    K.Adj u v ↔
      (u ≠ treeRootFin hK ∧ parentFin hK u = v) ∨
      (v ≠ treeRootFin hK ∧ parentFin hK v = u) := by
  constructor
  · intro hadj
    by_cases hnot : ¬ OnTreePath K v (treeRootFin hK) u
    · exact Or.inl (parentFin_eq_of_not_onTreePath hK hadj hnot)
    · push Not at hnot
      have hnot' : ¬ OnTreePath K u (treeRootFin hK) v := by
        intro hv
        exact hadj.ne (onTreePath_antisymm hK (onTreePath_symm hnot) (onTreePath_symm hv))
      exact Or.inr (parentFin_eq_of_not_onTreePath hK hadj.symm hnot')
  · rintro (⟨hu, rfl⟩ | ⟨hv, rfl⟩)
    · obtain ⟨hadj, _⟩ := treePath_eq_cons_parentFin hK hu
      exact hadj
    · obtain ⟨hadj, _⟩ := treePath_eq_cons_parentFin hK hv
      exact hadj.symm

/-- Construct a `RootedTree ℕ` on `Finset.range m` from an undirected tree `K` on `Fin m`. -/
noncomputable def rootedTreeOfIsTree (hK : K.IsTree) : RootedTree ℕ where
  verts := Finset.range m
  root := 0
  parent n := if hn : n < m then (parentFin hK ⟨n, hn⟩).val else 0
  root_mem := Finset.mem_range.2 (pos_of_isTree hK)
  parent_mem n hn := by
    rw [Finset.mem_range] at hn ⊢
    rw [dite_eq_left hn]
    exact (parentFin hK ⟨n, hn⟩).isLt
  parent_root := by
    have hm := pos_of_isTree hK
    rw [dite_eq_left hm]
    unfold parentFin treeRootFin
    rw [ite_eq_left rfl]
  exists_iterate_eq_root n hn := by
    rw [Finset.mem_range] at hn
    have hit : ∀ (k : ℕ) (u : Fin m),
        ((fun x : ℕ ↦ if hx : x < m then (parentFin hK ⟨x, hx⟩).val else 0)^[k] u.val) =
          ((parentFin hK)^[k] u).val := by
      intro k
      induction k with
      | zero => intro _; rfl
      | succ k ih =>
        intro u
        rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
        rw [dite_eq_left u.isLt]
        exact ih (parentFin hK u)
    refine ⟨treeDist hK ⟨n, hn⟩ (treeRootFin hK), ?_⟩
    rw [hit _ ⟨n, hn⟩, iterate_parentFin_treeDist hK ⟨n, hn⟩]
    rfl

/-- Canonical equivalence `(rootedTreeOfIsTree hK).verts ≃ Fin m`. -/
abbrev equivFinOfIsTree (hK : K.IsTree) : (rootedTreeOfIsTree hK).verts ≃ Fin m where
  toFun u := ⟨u.1, Finset.mem_range.1 u.2⟩
  invFun i := ⟨i.val, Finset.mem_range.2 i.isLt⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Fin.ext rfl

theorem toSimpleGraph_rootedTreeOfIsTree_adj_iff (hK : K.IsTree)
    (u v : (rootedTreeOfIsTree hK).verts) :
    (toSimpleGraph (rootedTreeOfIsTree hK)).Adj u v ↔
      K.Adj (equivFinOfIsTree hK u) (equivFinOfIsTree hK v) := by
  rw [adj_iff_parentFin hK]
  unfold toSimpleGraph rootedTreeOfIsTree treeRootFin equivFinOfIsTree
  have hu : u.1 < m := Finset.mem_range.1 u.2
  have hv : v.1 < m := Finset.mem_range.1 v.2
  change ((u.1 ≠ 0 ∧ (if hn : u.1 < m then (parentFin hK ⟨u.1, hn⟩).val else 0) = v.1) ∨
      (v.1 ≠ 0 ∧ (if hn : v.1 < m then (parentFin hK ⟨v.1, hn⟩).val else 0) = u.1)) ↔
    ((⟨u.1, hu⟩ : Fin m) ≠ ⟨0, pos_of_isTree hK⟩ ∧ parentFin hK ⟨u.1, hu⟩ = ⟨v.1, hv⟩) ∨
      ((⟨v.1, hv⟩ : Fin m) ≠ ⟨0, pos_of_isTree hK⟩ ∧ parentFin hK ⟨v.1, hv⟩ = ⟨u.1, hu⟩)
  rw [dite_eq_left hu, dite_eq_left hv]
  simp only [Fin.ext_iff, ne_eq]

/-- Graph homomorphism `toSimpleGraph (rootedTreeOfIsTree hK) →g K`. -/
abbrev homOfIsTree (hK : K.IsTree) : toSimpleGraph (rootedTreeOfIsTree hK) →g K where
  toFun u := equivFinOfIsTree hK u
  map_rel' h := (toSimpleGraph_rootedTreeOfIsTree_adj_iff hK _ _).1 h

theorem onTreePath_of_isTree_iff (hK : K.IsTree) (u v w : (rootedTreeOfIsTree hK).verts) :
    OnTreePath K (equivFinOfIsTree hK u) (equivFinOfIsTree hK v) (equivFinOfIsTree hK w) ↔
      OnTreePath (toSimpleGraph (rootedTreeOfIsTree hK)) u v w := by
  have hp : ((treePath (toSimpleGraph_isTree (rootedTreeOfIsTree hK)) u v).map
      (homOfIsTree hK)).IsPath :=
    (treePath_isPath (toSimpleGraph_isTree (rootedTreeOfIsTree hK)) u v).map
      (equivFinOfIsTree hK).injective
  have heq : ((treePath (toSimpleGraph_isTree (rootedTreeOfIsTree hK)) u v).map
      (homOfIsTree hK)) = treePath hK (equivFinOfIsTree hK u) (equivFinOfIsTree hK v) :=
    eq_treePath hK _ hp
  rw [onTreePath_iff_mem_treePath hK, ← heq,
    onTreePath_iff_mem_treePath (toSimpleGraph_isTree (rootedTreeOfIsTree hK)),
    Walk.support_map, List.mem_map]
  constructor
  · rintro ⟨z, hz, hzw⟩
    have hzw' : z = w := (equivFinOfIsTree hK).injective hzw
    exact hzw' ▸ hz
  · intro hw
    exact ⟨w, hw, rfl⟩

theorem onPath_rootedTreeOfIsTree_iff (hK : K.IsTree) (u v w : (rootedTreeOfIsTree hK).verts) :
    (rootedTreeOfIsTree hK).OnPath u.1 v.1 w.1 ↔
      OnTreePath K (equivFinOfIsTree hK u) (equivFinOfIsTree hK v) (equivFinOfIsTree hK w) := by
  rw [← onTreePath_toSimpleGraph_iff (rootedTreeOfIsTree hK), onTreePath_of_isTree_iff]

theorem onTreePathEdge_of_isTree_imp (hK : K.IsTree)
    {u v s s' : (rootedTreeOfIsTree hK).verts}
    (he : OnTreePathEdge K (equivFinOfIsTree hK u) (equivFinOfIsTree hK v)
      (equivFinOfIsTree hK s) (equivFinOfIsTree hK s')) :
    OnTreePathEdge (toSimpleGraph (rootedTreeOfIsTree hK)) u v s s' := by
  have hp : ((treePath (toSimpleGraph_isTree (rootedTreeOfIsTree hK)) u v).map
      (homOfIsTree hK)).IsPath :=
    (treePath_isPath (toSimpleGraph_isTree (rootedTreeOfIsTree hK)) u v).map
      (equivFinOfIsTree hK).injective
  have heq : ((treePath (toSimpleGraph_isTree (rootedTreeOfIsTree hK)) u v).map
      (homOfIsTree hK)) = treePath hK (equivFinOfIsTree hK u) (equivFinOfIsTree hK v) :=
    eq_treePath hK _ hp
  rw [onTreePathEdge_iff_mem_treePath hK, ← heq] at he
  rw [onTreePathEdge_iff_mem_treePath (toSimpleGraph_isTree (rootedTreeOfIsTree hK))]
  refine ⟨(toSimpleGraph_rootedTreeOfIsTree_adj_iff hK s s').2 he.1, ?_⟩
  have hedges := he.2
  rw [Walk.edges_map, List.mem_map] at hedges
  obtain ⟨e, he_mem, he_eq⟩ := hedges
  have hmap_inj : Function.Injective (Sym2.map (homOfIsTree hK)) :=
    Sym2.map.injective (equivFinOfIsTree hK).injective
  have he_ss' : e = s(s, s') := hmap_inj he_eq
  exact he_ss' ▸ he_mem

end FromIsTree

end

end GraphMinor.Thomas
