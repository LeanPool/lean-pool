/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.TreePath
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Set.Card
public import LeanPool.GraphMinor.Hypergraph.Basic

/-!
# Undirected trees and Bellenbaum–Diestel tree-decompositions

This file defines tree-decompositions in the sense of R. Diestel, *Graph Theory*, as used by
P. Bellenbaum and R. Diestel, *Two short proofs concerning tree-decompositions*, Combin. Probab.
Comput. 11 (2002) 541–547, Sections 1–3, and proves the basic properties of paths in trees and
Lemma 1 of that paper.

In a tree `T : SimpleGraph ι` (`hT : T.IsTree`), for any two vertices `t₁, t₂ : ι`, there is a
unique path between `t₁` and `t₂`. We denote by `treePath hT t₁ t₂` this path, by
`OnTreePath T t₁ t₂ t` the relation that `t` lies on `t₁ T t₂` (which for a tree is equivalent to
every path from `t₁` to `t₂` passing through `t`), and by `OnTreePathEdge T t₁ t₂ t t'` that the
edge `t t'` lies on `t₁ T t₂`.

A tree-decomposition `D : TreeDecomp G V₀` of a graph `(G, V₀)` (a `SimpleGraph α` on vertex set
`V₀ : Set α`) consists of an index type `ι` (`[Fintype ι]`), a tree `T : SimpleGraph ι`, and bags
` bag : ι → Set α` satisfying:
- (T1) `⋃ t, bag t = V₀` (`iUnion_bag`)
- (T2) every edge of `G` with both ends in `V₀` has both ends in some `bag t` (`adj_mem_bag`)
- (T3) if `t₂` lies on the path `t₁ T t₃`, then `bag t₁ ∩ bag t₃ ⊆ bag t₂` (`inter_subset_bag`).
-/

@[expose] public section

namespace GraphMinor.Thomas

open SimpleGraph

variable {α ι : Type*}

/-! ## Paths in trees -/

/-- `t` lies on the path of `T` between `t₁` and `t₂`: every path in `T` from `t₁` to `t₂` contains
`t`. In a tree there is a unique such path (`IsTree.existsUnique_path`). -/
abbrev OnTreePath (T : SimpleGraph ι) (t₁ t₂ t : ι) : Prop :=
  GraphMinor.TreePath.OnTreePath T t₁ t₂ t

/-- The edge `t t'` lies on the path of `T` between `t₁` and `t₂`: `t` and `t'` are adjacent in `T`
and every path in `T` from `t₁` to `t₂` traverses the edge `s(t, t')`. -/
def OnTreePathEdge (T : SimpleGraph ι) (t₁ t₂ t t' : ι) : Prop :=
  T.Adj t t' ∧ ∀ p : T.Walk t₁ t₂, p.IsPath → s(t, t') ∈ p.edges

/-- The unique path in a tree `T` between `t₁` and `t₂`. -/
noncomputable def treePath {T : SimpleGraph ι} (hT : T.IsTree) (t₁ t₂ : ι) : T.Walk t₁ t₂ :=
  (hT.existsUnique_path t₁ t₂).choose

theorem treePath_isPath {T : SimpleGraph ι} (hT : T.IsTree) (t₁ t₂ : ι) :
    (treePath hT t₁ t₂).IsPath :=
  (hT.existsUnique_path t₁ t₂).choose_spec.1

theorem eq_treePath {T : SimpleGraph ι} (hT : T.IsTree) {t₁ t₂ : ι} (p : T.Walk t₁ t₂)
    (hp : p.IsPath) : p = treePath hT t₁ t₂ :=
  (hT.existsUnique_path t₁ t₂).choose_spec.2 p hp

theorem onTreePath_iff_mem_treePath {T : SimpleGraph ι} (hT : T.IsTree) {t₁ t₂ t : ι} :
    OnTreePath T t₁ t₂ t ↔ t ∈ (treePath hT t₁ t₂).support :=
  ⟨fun h ↦ h _ (treePath_isPath hT t₁ t₂),
   fun h p hp ↦ eq_treePath hT p hp ▸ h⟩

theorem onTreePathEdge_iff_mem_treePath {T : SimpleGraph ι} (hT : T.IsTree) {t₁ t₂ t t' : ι} :
    OnTreePathEdge T t₁ t₂ t t' ↔ T.Adj t t' ∧ s(t, t') ∈ (treePath hT t₁ t₂).edges :=
  ⟨fun ⟨ha, h⟩ ↦ ⟨ha, h _ (treePath_isPath hT t₁ t₂)⟩,
   fun ⟨ha, h⟩ ↦ ⟨ha, fun p hp ↦ eq_treePath hT p hp ▸ h⟩⟩

@[simp]
theorem onTreePath_left (T : SimpleGraph ι) (t₁ t₂ : ι) : OnTreePath T t₁ t₂ t₁ :=
  GraphMinor.TreePath.left T t₁ t₂

@[simp]
theorem onTreePath_right (T : SimpleGraph ι) (t₁ t₂ : ι) : OnTreePath T t₁ t₂ t₂ :=
  GraphMinor.TreePath.right T t₁ t₂

theorem onTreePath_symm {T : SimpleGraph ι} {t₁ t₂ t : ι} (h : OnTreePath T t₁ t₂ t) :
    OnTreePath T t₂ t₁ t :=
  GraphMinor.TreePath.symm h

theorem onTreePath_comm (T : SimpleGraph ι) (t₁ t₂ t : ι) :
    OnTreePath T t₁ t₂ t ↔ OnTreePath T t₂ t₁ t :=
  ⟨onTreePath_symm, onTreePath_symm⟩

@[simp]
theorem onTreePath_self (T : SimpleGraph ι) (t₁ t : ι) :
    OnTreePath T t₁ t₁ t ↔ t = t₁ :=
  GraphMinor.TreePath.self_iff

theorem onTreePathEdge_symm_endpoints {T : SimpleGraph ι} {t₁ t₂ t t' : ι}
    (h : OnTreePathEdge T t₁ t₂ t t') : OnTreePathEdge T t₂ t₁ t t' := by
  refine ⟨h.1, fun p hp ↦ ?_⟩
  have := h.2 p.reverse hp.reverse
  rwa [Walk.edges_reverse, List.mem_reverse] at this

theorem onTreePathEdge_swap {T : SimpleGraph ι} {t₁ t₂ t t' : ι}
    (h : OnTreePathEdge T t₁ t₂ t t') : OnTreePathEdge T t₁ t₂ t' t := by
  refine ⟨h.1.symm, fun p hp ↦ ?_⟩
  rw [Sym2.eq_swap]
  exact h.2 p hp

theorem OnTreePathEdge.onTreePath_left {T : SimpleGraph ι} {t₁ t₂ t t' : ι}
    (h : OnTreePathEdge T t₁ t₂ t t') : OnTreePath T t₁ t₂ t :=
  fun p hp ↦ p.fst_mem_support_of_mem_edges (h.2 p hp)

theorem OnTreePathEdge.onTreePath_right {T : SimpleGraph ι} {t₁ t₂ t t' : ι}
    (h : OnTreePathEdge T t₁ t₂ t t') : OnTreePath T t₁ t₂ t' :=
  fun p hp ↦ p.snd_mem_support_of_mem_edges (h.2 p hp)

/-- In a tree, a vertex `t` lies on the path between `t₁` and `t₂` if and only if
there are paths from `t₁` to `t` and from `t` to `t₂` whose concatenation is a path. -/
theorem onTreePath_iff_exists_append {T : SimpleGraph ι} (hT : T.IsTree) {t₁ t₂ t : ι} :
    OnTreePath T t₁ t₂ t ↔
      ∃ (p : T.Walk t₁ t) (q : T.Walk t t₂), p.IsPath ∧ q.IsPath ∧ (p.append q).IsPath := by
  rw [onTreePath_iff_mem_treePath hT, (treePath_isPath hT t₁ t₂).mem_support_iff_exists_append]
  constructor
  · rintro ⟨p, q, hp, hq, heq⟩
    exact ⟨p, q, hp, hq, heq ▸ treePath_isPath hT t₁ t₂⟩
  · rintro ⟨p, q, hp, hq, hpq⟩
    exact ⟨p, q, hp, hq, (eq_treePath hT (p.append q) hpq).symm⟩

/-- `t` lies on `t₁ T t₂` if and only if every walk (not necessarily a path) from `t₁` to `t₂`
contains `t`. -/
theorem onTreePath_iff_forall_walk {T : SimpleGraph ι} {t₁ t₂ t : ι} :
    OnTreePath T t₁ t₂ t ↔ ∀ w : T.Walk t₁ t₂, t ∈ w.support :=
  ⟨GraphMinor.TreePath.mem_support, fun h p _ ↦ h p⟩

/-- `t t'` is an edge of `t₁ T t₂` if and only if `T.Adj t t'` and `t₁, t₂` are not
reachable in `T - t t'`, that is, every walk in `T` from `t₁` to `t₂` uses the edge `s(t, t')`. -/
theorem onTreePathEdge_iff_not_reachable_deleteEdges {T : SimpleGraph ι} {t₁ t₂ t t' : ι} :
    OnTreePathEdge T t₁ t₂ t t' ↔
      T.Adj t t' ∧ ¬ (T.deleteEdges {s(t, t')}).Reachable t₁ t₂ := by
  classical
  rw [reachable_deleteEdges_iff_exists_walk, not_exists_not]
  refine and_congr_right fun _ ↦ ⟨fun h w ↦ ?_, fun h p _ ↦ h p⟩
  exact w.edges_bypass_subset_edges (h w.bypass w.bypass_isPath)

/-- If `s` lies on `t₁ T t₃` and `t₂` lies on `t₁ T s` or `s T t₃`, then `t₂` lies on `t₁ T t₃`. -/
theorem onTreePath_trans_left {T : SimpleGraph ι} (hT : T.IsTree) {t₁ t₂ s t₃ : ι}
    (hs : OnTreePath T t₁ t₃ s) (ht₂ : OnTreePath T t₁ s t₂) :
    OnTreePath T t₁ t₃ t₂ := by
  rw [onTreePath_iff_exists_append hT] at hs
  obtain ⟨p, q, hp, hq, hpq⟩ := hs
  rw [onTreePath_iff_mem_treePath hT, ← eq_treePath hT _ hpq, Walk.mem_support_append_iff]
  exact Or.inl (ht₂ p hp)

theorem onTreePath_trans_right {T : SimpleGraph ι} (hT : T.IsTree) {t₁ t₂ s t₃ : ι}
    (hs : OnTreePath T t₁ t₃ s) (ht₂ : OnTreePath T s t₃ t₂) :
    OnTreePath T t₁ t₃ t₂ := by
  exact onTreePath_symm (onTreePath_trans_left hT (onTreePath_symm hs) (onTreePath_symm ht₂))

/-- For any walk `w` from `t₁` to `t₂` in `T`, every vertex of `t₁ T t₂` is in `w.support`;
if `s` is on a walk from `t₁` to `t₂` then `t₁ T t₂` is contained in `(t₁ T s) ∪ (s T t₂)`. -/
theorem onTreePath_left_or_right {T : SimpleGraph ι} (hT : T.IsTree) {t₁ t₂ t : ι} (s : ι)
    (ht : OnTreePath T t₁ t₂ t) :
    OnTreePath T t₁ s t ∨ OnTreePath T s t₂ t := by
  rw [onTreePath_iff_forall_walk] at ht
  have := ht ((treePath hT t₁ s).append (treePath hT s t₂))
  rw [Walk.mem_support_append_iff] at this
  rcases this with h | h
  · exact Or.inl ((onTreePath_iff_mem_treePath hT).2 h)
  · exact Or.inr ((onTreePath_iff_mem_treePath hT).2 h)

theorem onTreePathEdge_left_or_right {T : SimpleGraph ι} {t₁ t₂ t t' : ι} (s : ι)
    (h : OnTreePathEdge T t₁ t₂ t t') :
    OnTreePathEdge T t₁ s t t' ∨ OnTreePathEdge T s t₂ t t' := by
  rw [onTreePathEdge_iff_not_reachable_deleteEdges] at h ⊢
  rw [onTreePathEdge_iff_not_reachable_deleteEdges]
  by_contra! hc
  exact h.2 ((hc.1 h.1).trans (hc.2 h.1))

/-- If `s` lies on `t₁ T t₂`, then `t` lies on `t₁ T t₂` if and only if `t` lies on `t₁ T s` or
`s T t₂`. -/
theorem onTreePath_split_iff {T : SimpleGraph ι} (hT : T.IsTree) {t₁ t₂ s t : ι}
    (hs : OnTreePath T t₁ t₂ s) :
    OnTreePath T t₁ t₂ t ↔ OnTreePath T t₁ s t ∨ OnTreePath T s t₂ t :=
  ⟨onTreePath_left_or_right hT s,
   fun h ↦ h.elim (onTreePath_trans_left hT hs) (onTreePath_trans_right hT hs)⟩

/-- If `s` lies on `t₁ T t₂`, then `t₁` and `t₂` are separated by `s` in `T`: the only common
vertex of `t₁ T s` and `s T t₂` is `s`. -/
theorem onTreePath_inter_eq_of_onTreePath {T : SimpleGraph ι} (hT : T.IsTree) {t₁ t₂ s t : ι}
    (hs : OnTreePath T t₁ t₂ s) (h₁ : OnTreePath T t₁ s t) (h₂ : OnTreePath T s t₂ t) :
    t = s := by
  rw [onTreePath_iff_exists_append hT] at hs
  obtain ⟨p, q, hp, hq, hpq⟩ := hs
  by_contra hts
  exact hpq.ne_of_mem_support_of_append hts (h₁ p hp) (h₂ q hq) rfl

/-- Antisymmetry of `OnTreePath`: if `s` lies on `t₁ T t₂` and `t₂` lies on `t₁ T s`, then `s = t₂`.
-/
theorem onTreePath_antisymm {T : SimpleGraph ι} (hT : T.IsTree) {t₁ t₂ s : ι}
    (h₁ : OnTreePath T t₁ t₂ s) (h₂ : OnTreePath T t₁ s t₂) :
    s = t₂ :=
  (onTreePath_inter_eq_of_onTreePath hT h₁ h₂ (onTreePath_right T s t₂)).symm

/-- In a tree, for an adjacent pair `t, t'`, every vertex `s` is on the `t`-side (meaning `t` lies
on `s T t'`) or on the `t'`-side (meaning `t'` lies on `s T t`), and not both. -/
theorem onTreePath_adj_dichotomy {T : SimpleGraph ι} (hT : T.IsTree) {t t' : ι}
    (hadj : T.Adj t t') (s : ι) :
    (OnTreePath T s t' t ∧ ¬ OnTreePath T s t t') ∨
    (OnTreePath T s t t' ∧ ¬ OnTreePath T s t' t) := by
  have he : OnTreePathEdge T t t' t t' := by
    rw [onTreePathEdge_iff_mem_treePath hT]
    refine ⟨hadj, ?_⟩
    rw [← eq_treePath hT hadj.toWalk hadj.isPath_toWalk]
    simp
  have hdisj : ¬ (OnTreePath T s t' t ∧ OnTreePath T s t t') := by
    rintro ⟨h1, h2⟩
    exact hadj.ne (onTreePath_antisymm hT h1 h2)
  rcases onTreePathEdge_left_or_right s he with h | h
  · exact Or.inr ⟨onTreePath_symm h.onTreePath_right, fun h' ↦ hdisj ⟨h', onTreePath_symm
    h.onTreePath_right⟩⟩
  · exact Or.inl ⟨h.onTreePath_left, fun h' ↦ hdisj ⟨h.onTreePath_left, h'⟩⟩

/-- If `t t'` is an edge of `t₁ T t₂`, then either (`t` lies on `t₁ T t'` and `t'` lies on `t T t₂`)
or (`t'` lies on `t₁ T t` and `t` lies on `t' T t₂`). -/
theorem OnTreePathEdge.orient {T : SimpleGraph ι} (hT : T.IsTree) {t₁ t₂ t t' : ι}
    (h : OnTreePathEdge T t₁ t₂ t t') :
    (OnTreePath T t₁ t' t ∧ OnTreePath T t t₂ t' ∧ ¬ OnTreePath T t₁ t t' ∧ ¬ OnTreePath T t' t₂ t)
      ∨
    (OnTreePath T t₁ t t' ∧ OnTreePath T t' t₂ t ∧ ¬ OnTreePath T t₁ t' t ∧ ¬ OnTreePath T t t₂ t')
      := by
  have ht : OnTreePath T t₁ t₂ t := h.onTreePath_left
  have ht' : OnTreePath T t₁ t₂ t' := h.onTreePath_right
  rcases (onTreePath_split_iff hT ht).1 ht' with h1 | h2
  · right
    have h2' : OnTreePath T t' t₂ t := by
      rcases (onTreePath_split_iff hT ht').1 ht with h3 | h4
      · exfalso; exact h.1.ne (onTreePath_antisymm hT h3 h1)
      · exact h4
    refine ⟨h1, h2', fun hc ↦ h.1.ne (onTreePath_antisymm hT hc h1),
      fun hc ↦ h.1.ne (onTreePath_antisymm hT (onTreePath_symm h2') (onTreePath_symm hc))⟩
  · left
    have h1' : OnTreePath T t₁ t' t := by
      rcases (onTreePath_split_iff hT ht').1 ht with h3 | h4
      · exact h3
      · exfalso; exact h.1.ne (onTreePath_antisymm hT (onTreePath_symm h4) (onTreePath_symm h2))
    refine ⟨h1', h2, fun hc ↦ h.1.ne (onTreePath_antisymm hT h1' hc),
      fun hc ↦ h.1.ne (onTreePath_antisymm hT (onTreePath_symm hc) (onTreePath_symm h2))⟩

/-- Given a walk `p : t₁ → t₂` in `T`, if a predicate `P` holds at `t₁` and fails at `t₂`, there is
an edge `t t'` on `p` (and if `p` is a path, on `t₁ T t₂`) where `P t` holds and `P t'` fails. -/
theorem exists_onTreePathEdge_of_prop {T : SimpleGraph ι} (hT : T.IsTree) {t₁ t₂ : ι}
    (P : ι → Prop) (h₁ : P t₁) (h₂ : ¬ P t₂) :
    ∃ t t', OnTreePathEdge T t₁ t₂ t t' ∧ P t ∧ ¬ P t' := by
  have walk_lem : ∀ {u v : ι} (p : T.Walk u v), p.IsPath → P u → ¬ P v →
      ∃ t t', T.Adj t t' ∧ s(t, t') ∈ p.edges ∧ P t ∧ ¬ P t' := by
    intro u v p
    induction p with
    | nil => intros _ hu hv; exact (hv hu).elim
    | @cons u w v hadj q ih =>
      intro hp hu hv
      by_cases hw : P w
      · obtain ⟨t, t', ha, he, ht, ht'⟩ := ih hp.of_cons hw hv
        exact ⟨t, t', ha, List.mem_cons_of_mem _ he, ht, ht'⟩
      · exact ⟨u, w, hadj, List.Mem.head _, hu, hw⟩
  obtain ⟨t, t', ha, he, ht, ht'⟩ := walk_lem (treePath hT t₁ t₂) (treePath_isPath hT t₁ t₂) h₁ h₂
  exact ⟨t, t', (onTreePathEdge_iff_mem_treePath hT).2 ⟨ha, he⟩, ht, ht'⟩

/-- If `s₁` is on the `t₁`-side of an edge `t₁ t₂` (that is, `OnTreePath T s₁ t₂ t₁`) and `s₂` is on
the `t₂`-side (`OnTreePath T s₂ t₁ t₂`), then both `t₁` and `t₂` lie on `s₁ T s₂`. -/
theorem onTreePath_of_sides {T : SimpleGraph ι} (hT : T.IsTree) {t₁ t₂ s₁ s₂ : ι}
    (hadj : T.Adj t₁ t₂) (hs₁ : OnTreePath T s₁ t₂ t₁) (hs₂ : OnTreePath T s₂ t₁ t₂) :
    OnTreePath T s₁ s₂ t₁ ∧ OnTreePath T s₁ s₂ t₂ := by
  have ht₂ : OnTreePath T s₁ s₂ t₂ := by
    rcases onTreePath_left_or_right hT s₁ (onTreePath_symm hs₂) with h | h
    · exfalso; exact hadj.ne (onTreePath_antisymm hT hs₁ (onTreePath_symm h))
    · exact h
  have ht₁ : OnTreePath T s₁ s₂ t₁ := by
    rcases onTreePath_left_or_right hT s₂ hs₁ with h | h
    · exact h
    · exfalso; exact hadj.ne (onTreePath_antisymm hT h hs₂)
  exact ⟨ht₁, ht₂⟩

/-! ## Tree-decompositions (Bellenbaum–Diestel) -/

/-- A tree-decomposition of `(G, V₀)` in the sense of R. Diestel, *Graph Theory* (as used in
Bellenbaum and Diestel, Section 1): a finite tree `T` on an index type `ι` and a family of vertex
sets `bag : ι → Set α` satisfying:
- (T1) `⋃ t, bag t = V₀` (`iUnion_bag`)
- (T2) every edge of `G` with both ends in `V₀` has both ends in some `bag t` (`adj_mem_bag`)
- (T3) if `t₂` lies on the path `t₁ T t₃`, then `bag t₁ ∩ bag t₃ ⊆ bag t₂` (`inter_subset_bag`). -/
structure TreeDecomp (G : SimpleGraph α) (V₀ : Set α) (ι : Type*) [Fintype ι] where
  /-- The decomposition tree `T`. -/
  T : SimpleGraph ι
  /-- `T` is a tree. -/
  isTree : T.IsTree
  /-- The parts `(V_t)_{t ∈ T}`. -/
  bag : ι → Set α
  /-- (T1): `V(G) = ⋃_{t ∈ T} V_t`. -/
  iUnion_bag : ⋃ t, bag t = V₀
  /-- (T2): every edge of `G` (within `V₀`) has both ends in some `V_t`. -/
  adj_mem_bag : ∀ ⦃u v : α⦄, u ∈ V₀ → v ∈ V₀ → G.Adj u v → ∃ t, u ∈ bag t ∧ v ∈ bag t
  /-- (T3): `V_{t₁} ∩ V_{t₃} ⊆ V_{t₂}` whenever `t₂ ∈ t₁ T t₃`. -/
  inter_subset_bag : ∀ ⦃t₁ t₂ t₃ : ι⦄, OnTreePath T t₁ t₃ t₂ → bag t₁ ∩ bag t₃ ⊆ bag t₂

namespace TreeDecomp

variable {G : SimpleGraph α} {V₀ : Set α} [Fintype ι] (D : TreeDecomp G V₀ ι)

theorem bag_subset (t : ι) : D.bag t ⊆ V₀ :=
  fun _ hx ↦ D.iUnion_bag ▸ Set.mem_iUnion.2 ⟨t, hx⟩

theorem exists_mem_bag {x : α} (hx : x ∈ V₀) : ∃ t, x ∈ D.bag t := by
  rw [← D.iUnion_bag, Set.mem_iUnion] at hx
  exact hx

theorem bag_finite (hV₀ : V₀.Finite) (t : ι) : (D.bag t).Finite :=
  hV₀.subset (D.bag_subset t)

theorem mem_bag_of_onTreePath {t₁ t₂ t₃ : ι} {x : α} (ht : OnTreePath D.T t₁ t₃ t₂)
    (h₁ : x ∈ D.bag t₁) (h₃ : x ∈ D.bag t₃) : x ∈ D.bag t₂ :=
  D.inter_subset_bag ht ⟨h₁, h₃⟩

/-- The width of `D` is at most `w`: `|V_t| ≤ w + 1` for all `t ∈ T`. -/
def WidthLE (w : ℕ) : Prop :=
  ∀ t : ι, (D.bag t).encard ≤ (w + 1 : ℕ)

/-- For a finite vertex set the width bound can be checked with natural cardinalities. -/
theorem widthLE_iff_ncard_le (hV₀ : V₀.Finite) {w : ℕ} :
    D.WidthLE w ↔ ∀ t, (D.bag t).ncard ≤ w + 1 := by
  constructor
  · exact fun h t ↦ (Set.encard_le_coe_iff_finite_ncard_le.mp (h t)).2
  · exact fun h t ↦ Set.encard_le_coe_iff_finite_ncard_le.mpr ⟨D.bag_finite hV₀ t, h t⟩

/-- **Lemma 1** of Bellenbaum and Diestel (page 2), edge-removal form:
Let `(V_t)_{t ∈ T}` be a tree-decomposition of a graph `G`, let `t₁ t₂` be an edge of `T`, and let
`T₁` and `T₂` be the components of `T - t₁ t₂`. Then `V_{t₁} ∩ V_{t₂}` separates `⋃_{t ∈ T₁} V_t`
from `⋃_{t ∈ T₂} V_t` in `G`.

Here the two components of `T - t₁ t₂` are `{s | OnTreePath T s t₂ t₁}` (the `t₁`-side) and
`{s | OnTreePath T s t₁ t₂}` (the `t₂`-side), and any walk `p` in `G` (within `V₀`) from `bag s₁`
(with `s₁` on the `t₁`-side) to `bag s₂` (with `s₂` on the `t₂`-side) meets `bag t₁ ∩ bag t₂`. -/
theorem lemma_1_edge {t₁ t₂ s₁ s₂ : ι} (hadj : D.T.Adj t₁ t₂)
    (hs₁ : OnTreePath D.T s₁ t₂ t₁) (hs₂ : OnTreePath D.T s₂ t₁ t₂)
    {u v : α} (hu : u ∈ D.bag s₁) (hv : v ∈ D.bag s₂)
    (p : G.Walk u v) (hp : ∀ x ∈ p.support, x ∈ V₀) :
    ∃ x ∈ p.support, x ∈ D.bag t₁ ∩ D.bag t₂ := by
  induction p generalizing s₁ with
  | @nil u =>
    have ⟨ht₁, ht₂⟩ := onTreePath_of_sides D.isTree hadj hs₁ hs₂
    exact ⟨u, Walk.start_mem_support _,
      D.mem_bag_of_onTreePath ht₁ hu hv, D.mem_bag_of_onTreePath ht₂ hu hv⟩
  | @cons u w v hadjG q ih =>
    have huV : u ∈ V₀ := hp u (List.Mem.head _)
    have hwV : w ∈ V₀ := hp w (List.mem_cons_of_mem _ q.start_mem_support)
    obtain ⟨s', hus', hws'⟩ := D.adj_mem_bag huV hwV hadjG
    rcases onTreePath_adj_dichotomy D.isTree hadj s' with ⟨hs'₁, _⟩ | ⟨hs'₂, _⟩
    · obtain ⟨x, hx, hxbag⟩ := ih hs'₁ hws' hv (fun z hz ↦ hp z (List.mem_cons_of_mem _ hz))
      exact ⟨x, List.mem_cons_of_mem _ hx, hxbag⟩
    · have ⟨ht₁, ht₂⟩ := onTreePath_of_sides D.isTree hadj hs₁ hs'₂
      exact ⟨u, List.Mem.head _,
        D.mem_bag_of_onTreePath ht₁ hu hus', D.mem_bag_of_onTreePath ht₂ hu hus'⟩

/-- **Lemma 1** of Bellenbaum and Diestel (page 2), for an edge `t₁ t₂` lying on a path `s₁ T s₂`:
every walk in `G` (within `V₀`) from `bag s₁` to `bag s₂` contains a vertex of `bag t₁ ∩ bag t₂`. -/
theorem lemma_1_onTreePathEdge {s₁ s₂ t₁ t₂ : ι} (he : OnTreePathEdge D.T s₁ s₂ t₁ t₂)
    {u v : α} (hu : u ∈ D.bag s₁) (hv : v ∈ D.bag s₂)
    (p : G.Walk u v) (hp : ∀ x ∈ p.support, x ∈ V₀) :
    ∃ x ∈ p.support, x ∈ D.bag t₁ ∩ D.bag t₂ := by
  rcases he.orient D.isTree with ⟨h1, h2, _, _⟩ | ⟨h1, h2, _, _⟩
  · exact D.lemma_1_edge he.1 h1 (onTreePath_symm h2) hu hv p hp
  · obtain ⟨x, hx, hx2, hx1⟩ := D.lemma_1_edge he.1.symm h1 (onTreePath_symm h2) hu hv p hp
    exact ⟨x, hx, hx1, hx2⟩

/-- Vertex-separator consequence of **Lemma 1** (used in the proof of Lemma 2 and Claim (1) of
Theorem 3): if `t` lies on `s₁ T s₂`, then `bag t` separates `bag s₁` from `bag s₂` in `G`, that is,
every walk in `G` (within `V₀`) from `bag s₁` to `bag s₂` contains a vertex of `bag t`. -/
theorem lemma_1_vertex {s₁ s₂ t : ι} (ht : OnTreePath D.T s₁ s₂ t)
    {u v : α} (hu : u ∈ D.bag s₁) (hv : v ∈ D.bag s₂)
    (p : G.Walk u v) (hp : ∀ x ∈ p.support, x ∈ V₀) :
    ∃ x ∈ p.support, x ∈ D.bag t := by
  by_cases hts₁ : t = s₁
  · subst hts₁
    exact ⟨u, p.start_mem_support, hu⟩
  · obtain ⟨t₁, t₂, he, h1, h2⟩ :=
      exists_onTreePathEdge_of_prop D.isTree (fun s ↦ ¬ OnTreePath D.T s₁ s t)
        (fun h ↦ hts₁ ((onTreePath_self D.T s₁ t).1 h))
        (not_not.2 ht)
    obtain ⟨x, hx, hx1, hx2⟩ := D.lemma_1_onTreePathEdge he hu hv p hp
    have ht_on : OnTreePath D.T t₁ t₂ t := by
      rcases onTreePath_left_or_right D.isTree t₁ (not_not.1 h2) with h | h
      · exact (h1 h).elim
      · exact h
    exact ⟨x, hx, D.mem_bag_of_onTreePath ht_on hx1 hx2⟩

end TreeDecomp

end GraphMinor.Thomas
