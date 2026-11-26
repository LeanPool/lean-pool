/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM10.Defs2
public import Mathlib.Order.Prod.Lex.Basic
import LeanPool.GraphMinor.GM10.TangleLemmas
import LeanPool.GraphMinor.GM10.Section8
import LeanPool.GraphMinor.GM10.TreeWidthBasic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps

/-!
# Laminar Separations and Tie-Breakers (Graph Minors X, Section 9)

This file formalizes Section 9 of N. Robertson and P. D. Seymour,
*Graph Minors. X. Obstructions to tree-decomposition*, J. Combin. Theory Ser. B 52 (1991) 153–190
(pages 177–180):

- `MakesSeparation.isSeparation`: every pair `(G₁^e, G₂^e)` made by an edge `e` of a
  tree-decomposition `(T, τ)` of `G` is a separation of `G`.
- `theorem_9_1_laminar` and `theorem_9_1` (**Graph Minors X, (9.1)**, page 177): the set of
  separations made by edges of a tree-decomposition is laminar, and conversely every laminar set
  of separations of `G` is made by a tree-decomposition of `G`.
- `theorem_9_2_claim_1`, `theorem_9_2_claim_2`, and `theorem_9_2` (**Graph Minors X, (9.2)**,
  page 178): in every hypergraph there is a tie-breaker.
- `theorem_9_3` (**Graph Minors X, (9.3)**, page 179): strengthening of the second tie-breaker
  axiom.
- `theorem_9_4` (**Graph Minors X, (9.4)**, page 180): two doubly `λ`-robust separations of `G`
  do not cross.
-/

public section

namespace GraphMinor.GM10

open SimpleGraph Hypergraph

variable {α β ι : Type*}

/-! ## Basic symmetries of `SeparationsCross` and `MakesSeparation` -/

theorem separationsCross_comm {A₁ B₁ A₂ B₂ : Hypergraph α β} :
    SeparationsCross A₁ B₁ A₂ B₂ ↔ SeparationsCross A₂ B₂ A₁ B₁ := by
  unfold SeparationsCross
  tauto

theorem separationsCross_swap_left {A₁ B₁ A₂ B₂ : Hypergraph α β} :
    SeparationsCross B₁ A₁ A₂ B₂ ↔ SeparationsCross A₁ B₁ A₂ B₂ := by
  unfold SeparationsCross
  tauto

theorem separationsCross_swap_right {A₁ B₁ A₂ B₂ : Hypergraph α β} :
    SeparationsCross A₁ B₁ B₂ A₂ ↔ SeparationsCross A₁ B₁ A₂ B₂ := by
  unfold SeparationsCross
  tauto

theorem makesSeparation_symm [Fintype ι] {T : SimpleGraph ι} {τ : ι → Hypergraph α β}
    {e : Sym2 ι} {A B : Hypergraph α β} :
    MakesSeparation T τ e A B ↔ MakesSeparation T τ e B A := by
  constructor <;> rintro ⟨u, v, hadj, he, hA, hB⟩
  · refine ⟨v, u, hadj.symm, he.trans (Sym2.eq_swap), ?_, ?_⟩
    · simpa [Sym2.eq_swap] using hB
    · simpa [Sym2.eq_swap] using hA
  · refine ⟨v, u, hadj.symm, he.trans (Sym2.eq_swap), ?_, ?_⟩
    · simpa [Sym2.eq_swap] using hB
    · simpa [Sym2.eq_swap] using hA

/-! ## Tree component lemmas and Part 1 of (9.1) -/

/-- In a tree `T`, deleting an edge `s(u, v)` disconnects `u` and `v`. -/
theorem not_reachable_deleteEdges {T : SimpleGraph ι} (hT : T.IsTree)
    {u v : ι} (hadj : T.Adj u v) :
    ¬ (T.deleteEdges {s(u, v)}).Reachable u v :=
  isAcyclic_iff_forall_adj_isBridge.1 hT.isAcyclic hadj

/-- In a connected graph `T`, deleting an edge `s(u, v)` leaves every vertex `t` reachable from
either `u` or `v`. -/
private theorem reachable_deleteEdges_or_of_walk {T : SimpleGraph ι} {u v a b : ι}
    (w : T.Walk a b)
    (hb : (T.deleteEdges {s(u, v)}).Reachable u b ∨ (T.deleteEdges {s(u, v)}).Reachable v b) :
    (T.deleteEdges {s(u, v)}).Reachable u a ∨ (T.deleteEdges {s(u, v)}).Reachable v a := by
  induction w with
  | nil => exact hb
  | @cons x y z hxy _ ih =>
    by_cases he : s(x, y) = s(u, v)
    · rcases Sym2.eq_iff.1 he with ⟨rfl, _⟩ | ⟨rfl, _⟩
      · exact Or.inl (Reachable.refl _)
      · exact Or.inr (Reachable.refl _)
    · have hadj' : (T.deleteEdges {s(u, v)}).Adj y x :=
        deleteEdges_adj.mpr ⟨hxy.symm, by simpa [Sym2.eq_swap] using he⟩
      exact (ih hb).imp (fun h ↦ h.trans hadj'.reachable) (fun h ↦ h.trans hadj'.reachable)

theorem reachable_deleteEdges_or {T : SimpleGraph ι} (hT : T.Connected)
    {u v : ι} (t : ι) :
    (T.deleteEdges {s(u, v)}).Reachable u t ∨ (T.deleteEdges {s(u, v)}).Reachable v t := by
  obtain ⟨w⟩ := hT.preconnected t u
  exact reachable_deleteEdges_or_of_walk w (Or.inl (Reachable.refl _))

/-- If `b` is reachable from `a` in `T \ e₁` and `x` is not reachable from `a` in `T \ e₁`, then
any walk in `T \ e₁` from `a` to `b` avoids `x` and hence avoids the edge `s(x, y)`. -/
theorem reachable_deleteEdges_of_not_reachable {T : SimpleGraph ι} {e₁ : Sym2 ι}
    {a b x y : ι} (hab : (T.deleteEdges {e₁}).Reachable a b)
    (hnx : ¬ (T.deleteEdges {e₁}).Reachable a x) :
    (T.deleteEdges {s(x, y)}).Reachable a b := by
  obtain ⟨p⟩ := hab
  induction p with
  | nil => exact Reachable.refl _
  | @cons u c w huc p' ih =>
    have hux : u ≠ x := by
      rintro rfl
      exact hnx (Reachable.refl _)
    have hncx : ¬ (T.deleteEdges {e₁}).Reachable c x :=
      fun hcx ↦ hnx (huc.reachable.trans hcx)
    have hcx : c ≠ x := by
      rintro rfl
      exact hncx (Reachable.refl _)
    have hne : s(u, c) ≠ s(x, y) := by
      intro heq
      have hx : x ∈ s(u, c) := heq ▸ Sym2.mem_mk_left x y
      rcases Sym2.mem_iff.1 hx with rfl | rfl
      · exact hux rfl
      · exact hcx rfl
    have hadj' : (T.deleteEdges {s(x, y)}).Adj u c :=
      deleteEdges_adj.mpr ⟨(deleteEdges_adj.mp huc).1, hne⟩
    exact hadj'.reachable.trans (ih hncx)

theorem biUnion_le_of_le {G : Hypergraph α β} {s : Finset ι} {τ : ι → Hypergraph α β}
    (hτ : ∀ t ∈ s, τ t ≤ G) :
    Hypergraph.biUnion s τ ≤ G where
  vertexSet_subset := by
    intro v hv
    simp only [biUnion, Set.mem_iUnion] at hv
    obtain ⟨t, ht, hvt⟩ := hv
    exact (hτ t ht).vertexSet_subset hvt
  edgeSet_subset := by
    intro e he
    simp only [biUnion, Set.mem_iUnion] at he
    obtain ⟨t, ht, het⟩ := he
    exact (hτ t ht).edgeSet_subset het
  ends_eq e he := by
    simp only [biUnion, Set.mem_iUnion] at he
    obtain ⟨t₀, ht₀, het₀⟩ := he
    ext v
    simp only [ends, Set.mem_ofPred_eq, biUnion]
    refine ⟨fun hinc ↦ ⟨t₀, ht₀, (inc_iff_of_le (hτ t₀ ht₀) het₀).2 hinc⟩, ?_⟩
    rintro ⟨t, ht, hinc⟩
    exact inc_of_le (hτ t ht) hinc

theorem biUnion_mono {G : Hypergraph α β} {s₁ s₂ : Finset ι} {τ : ι → Hypergraph α β}
    (hτ : ∀ t, τ t ≤ G) (hsub : s₁ ⊆ s₂) :
    Hypergraph.biUnion s₁ τ ≤ Hypergraph.biUnion s₂ τ := by
  rw [le_iff_of_le (biUnion_le_of_le fun t _ ↦ hτ t) (biUnion_le_of_le fun t _ ↦ hτ t)]
  refine ⟨?_, ?_⟩ <;>
  · intro x hx
    simp only [biUnion, Set.mem_iUnion] at hx ⊢
    obtain ⟨t, ht, hxt⟩ := hx
    exact ⟨t, hsub ht, hxt⟩

/-- For any edge `e = s(u, v)` of `T` in a tree-decomposition `(T, τ)` of `G`,
`(treeDecompSide T τ s(u, v) u, treeDecompSide T τ s(u, v) v)` is a separation of `G`
(Graph Minors X, Section 9, page 177). -/
theorem IsTreeDecomposition.isSeparation_treeDecompSide [Fintype ι] {G : Hypergraph α β}
    {T : SimpleGraph ι} {τ : ι → Hypergraph α β} (hTD : IsTreeDecomposition G T τ)
    {u v : ι} (hadj : T.Adj u v) :
    G.IsSeparation (treeDecompSide T τ s(u, v) u) (treeDecompSide T τ s(u, v) v) := by
  classical
  have h1 : treeDecompSide T τ s(u, v) u ≤ G :=
    biUnion_le_of_le fun t _ ↦ hTD.le t
  have h2 : treeDecompSide T τ s(u, v) v ≤ G :=
    biUnion_le_of_le fun t _ ↦ hTD.le t
  rw [isSeparation_iff_of_le h1 h2]
  have hnot_uv : ¬ (T.deleteEdges {s(u, v)}).Reachable u v :=
    not_reachable_deleteEdges hTD.isTree hadj
  have hor : ∀ t : ι, (T.deleteEdges {s(u, v)}).Reachable u t ∨
      (T.deleteEdges {s(u, v)}).Reachable v t :=
    reachable_deleteEdges_or hTD.isTree.connected
  refine ⟨?_, ?_, ?_⟩
  · rw [← hTD.biUnion_eq]
    ext x
    simp only [treeDecompSide, biUnion, Set.mem_union, Set.mem_iUnion,
      Finset.mem_filter, Finset.mem_univ, true_and, exists_true_left]
    constructor
    · rintro (⟨t, _, hxt⟩ | ⟨t, _, hxt⟩) <;> exact ⟨t, hxt⟩
    · rintro ⟨t, hxt⟩
      rcases hor t with hut | hvt
      · exact Or.inl ⟨t, hut, hxt⟩
      · exact Or.inr ⟨t, hvt, hxt⟩
  · rw [← hTD.biUnion_eq]
    ext e
    simp only [treeDecompSide, biUnion, Set.mem_union, Set.mem_iUnion,
      Finset.mem_filter, Finset.mem_univ, true_and, exists_true_left]
    constructor
    · rintro (⟨t, _, het⟩ | ⟨t, _, het⟩) <;> exact ⟨t, het⟩
    · rintro ⟨t, het⟩
      rcases hor t with hut | hvt
      · exact Or.inl ⟨t, hut, het⟩
      · exact Or.inr ⟨t, hvt, het⟩
  · ext e
    simp only [treeDecompSide, biUnion, Set.mem_inter_iff, Set.mem_iUnion,
      Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_empty_iff_false, iff_false, not_and]
    rintro ⟨t₁, hut₁, het₁⟩ ⟨t₂, hvt₂, het₂⟩
    have hne : t₁ ≠ t₂ := by
      rintro rfl
      exact hnot_uv (hut₁.trans hvt₂.symm)
    have hemp := hTD.edgeSet_inter_eq hne
    exact Set.notMem_empty e (hemp ▸ ⟨het₁, het₂⟩)

/-- Every pair `(A, B)` made by an edge `e` of `T` in a tree-decomposition `(T, τ)` of `G` is a
separation of `G` (Graph Minors X, Section 9, page 177). -/
theorem MakesSeparation.isSeparation [Fintype ι] {G : Hypergraph α β}
    {T : SimpleGraph ι} {τ : ι → Hypergraph α β} (hTD : IsTreeDecomposition G T τ)
    {e : Sym2 ι} {A B : Hypergraph α β} (h : MakesSeparation T τ e A B) :
    G.IsSeparation A B := by
  obtain ⟨u, v, hadj, _, rfl, rfl⟩ := h
  exact hTD.isSeparation_treeDecompSide hadj

/-- If `e₁ = s(u₁, v₁)` and `e₂ = s(u₂, v₂)` are distinct edges of a tree `T`, and `u₂` is in the
`v₁`-component of `T \ e₁` while `u₁` is in the `u₂`-component of `T \ e₂`, then
`treeDecompSide T τ e₁ u₁ ≤ treeDecompSide T τ e₂ u₂` and
`treeDecompSide T τ e₂ v₂ ≤ treeDecompSide T τ e₁ v₁`. -/
theorem treeDecompSide_le_of_distinct_edges [Fintype ι] {G : Hypergraph α β}
    {T : SimpleGraph ι} {τ : ι → Hypergraph α β} (hTD : IsTreeDecomposition G T τ)
    {u₁ v₁ u₂ v₂ : ι} (hadj₁ : T.Adj u₁ v₁) (hadj₂ : T.Adj u₂ v₂)
    (hv₁u₂ : (T.deleteEdges {s(u₁, v₁)}).Reachable v₁ u₂)
    (hu₂u₁ : (T.deleteEdges {s(u₂, v₂)}).Reachable u₂ u₁) :
    treeDecompSide T τ s(u₁, v₁) u₁ ≤ treeDecompSide T τ s(u₂, v₂) u₂ ∧
      treeDecompSide T τ s(u₂, v₂) v₂ ≤ treeDecompSide T τ s(u₁, v₁) v₁ := by
  classical
  have hnot₁ : ¬ (T.deleteEdges {s(u₁, v₁)}).Reachable u₁ v₁ :=
    not_reachable_deleteEdges hTD.isTree hadj₁
  have hnot₂ : ¬ (T.deleteEdges {s(u₂, v₂)}).Reachable u₂ v₂ :=
    not_reachable_deleteEdges hTD.isTree hadj₂
  have hnu₁u₂ : ¬ (T.deleteEdges {s(u₁, v₁)}).Reachable u₁ u₂ :=
    fun h ↦ hnot₁ (h.trans hv₁u₂.symm)
  have hnv₂u₁ : ¬ (T.deleteEdges {s(u₂, v₂)}).Reachable v₂ u₁ :=
    fun h ↦ hnot₂ (hu₂u₁.trans h.symm)
  constructor
  · apply biUnion_mono hTD.le
    intro t ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
    exact hu₂u₁.trans (reachable_deleteEdges_of_not_reachable ht hnu₁u₂)
  · apply biUnion_mono hTD.le
    intro t ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
    have h1 : (T.deleteEdges {s(u₁, v₁)}).Reachable v₂ t :=
      reachable_deleteEdges_of_not_reachable ht hnv₂u₁
    have hne : s(u₂, v₂) ≠ s(u₁, v₁) := by
      intro heq
      rcases Sym2.eq_iff.1 heq with ⟨h1', h2'⟩ | ⟨h1', h2'⟩
      · subst h1' h2'
        exact hnu₁u₂ (Reachable.refl _)
      · subst h1' h2'
        exact hnv₂u₁ (Reachable.refl _)
    have hadj_u₂v₂ : (T.deleteEdges {s(u₁, v₁)}).Adj u₂ v₂ :=
      deleteEdges_adj.mpr ⟨hadj₂, hne⟩
    exact hv₁u₂.trans (hadj_u₂v₂.reachable.trans h1)

/-- First part of **Graph Minors X, (9.1)** (page 177):
"If $(T, \tau)$ is a tree-decomposition of $G$, then the set of all separations of $G$ made
by edges of $T$ is laminar." -/
theorem theorem_9_1_laminar [Fintype ι] {G : Hypergraph α β}
    {T : SimpleGraph ι} {τ : ι → Hypergraph α β} (hTD : IsTreeDecomposition G T τ) :
    IsLaminar (separationsMadeBy T τ) := by
  rintro ⟨A₁, B₁⟩ ⟨e₁, _, u₁, v₁, hadj₁, rfl, rfl, rfl⟩
    ⟨A₂, B₂⟩ ⟨e₂, _, u₂, v₂, hadj₂, rfl, rfl, rfl⟩
  unfold SeparationsCross
  rw [not_not]
  by_cases he : s(u₁, v₁) = s(u₂, v₂)
  · rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨le_rfl, le_rfl⟩
    · right; left
      simp [Sym2.eq_swap]
  · have hor₁ : (T.deleteEdges {s(u₁, v₁)}).Reachable u₁ u₂ ∨
        (T.deleteEdges {s(u₁, v₁)}).Reachable v₁ u₂ :=
      reachable_deleteEdges_or hTD.isTree.connected u₂
    have hor₂ : (T.deleteEdges {s(u₂, v₂)}).Reachable u₂ u₁ ∨
        (T.deleteEdges {s(u₂, v₂)}).Reachable v₂ u₁ :=
      reachable_deleteEdges_or hTD.isTree.connected u₁
    have hadj₂_in_1 : (T.deleteEdges {s(u₁, v₁)}).Adj u₂ v₂ :=
      deleteEdges_adj.mpr ⟨hadj₂, Ne.symm he⟩
    have hadj₁_in_2 : (T.deleteEdges {s(u₂, v₂)}).Adj u₁ v₁ :=
      deleteEdges_adj.mpr ⟨hadj₁, he⟩
    rcases hor₁ with hu₁u₂ | hv₁u₂ <;> rcases hor₂ with hu₂u₁ | hv₂u₁
    · right; right; left
      have hv₂v₁ : (T.deleteEdges {s(u₂, v₂)}).Reachable u₂ v₁ :=
        hu₂u₁.trans hadj₁_in_2.reachable
      have h := treeDecompSide_le_of_distinct_edges hTD hadj₁.symm hadj₂
        (by simpa [Sym2.eq_swap] using hu₁u₂) hv₂v₁
      simpa [Sym2.eq_swap] using h
    · right; right; right
      have hv₂v₁ : (T.deleteEdges {s(u₂, v₂)}).Reachable v₂ v₁ :=
        hv₂u₁.trans hadj₁_in_2.reachable
      have hu₁v₂ : (T.deleteEdges {s(u₁, v₁)}).Reachable u₁ v₂ :=
        hu₁u₂.trans hadj₂_in_1.reachable
      have h := treeDecompSide_le_of_distinct_edges hTD hadj₁.symm hadj₂.symm
        (by simpa [Sym2.eq_swap] using hu₁v₂) (by simpa [Sym2.eq_swap] using hv₂v₁)
      simpa [Sym2.eq_swap] using h
    · left
      exact treeDecompSide_le_of_distinct_edges hTD hadj₁ hadj₂ hv₁u₂ hu₂u₁
    · right; left
      have hv₁v₂ : (T.deleteEdges {s(u₁, v₁)}).Reachable v₁ v₂ :=
        hv₁u₂.trans hadj₂_in_1.reachable
      have h := treeDecompSide_le_of_distinct_edges hTD hadj₁ hadj₂.symm
        hv₁v₂ (by simpa [Sym2.eq_swap] using hv₂u₁)
      simpa [Sym2.eq_swap] using h

/-! ## Converse of (9.1): Tree-decomposition for a laminar set of separations -/

/-- In a finite tree `T`, if every edge `s(u, v)` has at least one valid orientation `R u v` or
`R v u`, then there is a vertex `u₀` such that `R u₀ w` holds for all neighbors `w` of `u₀`. -/
theorem exists_sink_of_adj_or [Finite ι] {T : SimpleGraph ι} (hT : T.IsTree)
    {R : ι → ι → Prop} (hR : ∀ ⦃u v : ι⦄, T.Adj u v → R u v ∨ R v u) :
    ∃ u₀ : ι, ∀ w : ι, T.Adj u₀ w → R u₀ w := by
  let fintypeVertices := Fintype.ofFinite ι
  by_contra! hno
  let D : ι → ι → Prop := fun u v ↦ T.Adj u v ∧ ¬ R v u
  have hD_ex : ∀ v : ι, ∃ u : ι, D u v := by
    intro v
    obtain ⟨u, huv, hnR⟩ := hno v
    exact ⟨u, huv.symm, hnR⟩
  have hD_asym : ∀ ⦃u v : ι⦄, D u v → ¬ D v u := by
    rintro u v ⟨huv, hnR⟩ ⟨_, hnR'⟩
    rcases hR huv with h1 | h2
    · exact hnR' h1
    · exact hnR h2
  have hchain : ∀ k : ℕ, ∃ (u v w : ι) (huv : T.Adj u v) (p : T.Walk v w),
      D u v ∧ (Walk.cons huv p).length = k + 1 ∧
        List.IsChain (· ≠ ·) (Walk.cons huv p).edges := by
    intro k
    induction k with
    | zero =>
      obtain ⟨v⟩ := hT.connected.nonempty
      obtain ⟨u, hDuv⟩ := hD_ex v
      refine ⟨u, v, v, hDuv.1, .nil, hDuv, rfl, ?_⟩
      simp
    | succ k ih =>
      obtain ⟨u, v, w, huv, p, hDuv, hlen, hch⟩ := ih
      obtain ⟨x, hDxu⟩ := hD_ex u
      refine ⟨x, u, w, hDxu.1, Walk.cons huv p, hDxu, ?_, ?_⟩
      · simp [hlen]
      · simp only [Walk.edges_cons] at hch ⊢
        refine List.isChain_cons_cons.2 ⟨?_, hch⟩
        intro heq
        rcases Sym2.eq_iff.1 heq with ⟨h1, _⟩ | ⟨h1, _⟩
        · exact hDxu.1.ne h1
        · subst h1; exact hD_asym hDuv hDxu
  obtain ⟨u, v, w, huv, p, _, hlen, hch⟩ := hchain (Fintype.card ι)
  let q := Walk.cons huv p
  have hq : q.IsPath := (hT.isAcyclic.isPath_iff_isChain q).2 hch
  have hle : q.support.length ≤ Fintype.card ι := hq.support_nodup.length_le_card
  rw [Walk.length_support, hlen] at hle
  omega

/-- Any walk `p` in `T` whose support does not contain `u₀` avoids the edge `s(u₀, w)`. -/
theorem reachable_deleteEdges_of_notMem_support {T : SimpleGraph ι} {u₀ w a b : ι}
    (p : T.Walk a b) (hu₀ : u₀ ∉ p.support) :
    (T.deleteEdges {s(u₀, w)}).Reachable a b := by
  induction p with
  | nil => exact Reachable.refl _
  | @cons x y z hxy q ih =>
    simp only [Walk.support_cons, List.mem_cons, not_or] at hu₀
    have hy : y ≠ u₀ := by rintro rfl; exact hu₀.2 q.start_mem_support
    have hne : s(x, y) ≠ s(u₀, w) := by
      intro heq
      have : u₀ ∈ s(x, y) := heq ▸ Sym2.mem_mk_left u₀ w
      rcases Sym2.mem_iff.1 this with rfl | rfl
      · exact hu₀.1 rfl
      · exact hy rfl
    exact (deleteEdges_adj.mpr ⟨hxy, hne⟩).reachable.trans (ih hu₀.2)

/-- In a tree `T`, if `t₁` is in the `u₀`-component of `T \ s(u₀, w)` and `t₂` is in the
`w`-component of `T \ s(u₀, w)`, then `u₀` lies on every path between `t₁` and `t₂`. -/
theorem onTreePath_of_reachable_deleteEdges {T : SimpleGraph ι} (hT : T.IsTree)
    {u₀ w t₁ t₂ : ι} (hadj : T.Adj u₀ w)
    (ht₁ : (T.deleteEdges {s(u₀, w)}).Reachable u₀ t₁)
    (ht₂ : (T.deleteEdges {s(u₀, w)}).Reachable w t₂) :
    OnTreePath T t₁ t₂ u₀ := by
  intro p _
  by_contra hu₀
  have hp : (T.deleteEdges {s(u₀, w)}).Reachable t₁ t₂ :=
    reachable_deleteEdges_of_notMem_support p hu₀
  exact not_reachable_deleteEdges hT hadj (ht₁.trans (hp.trans ht₂.symm))

theorem le_treeDecompSide [Fintype ι] {G : Hypergraph α β}
    {T : SimpleGraph ι} {τ : ι → Hypergraph α β} (hTD : IsTreeDecomposition G T τ)
    {e : Sym2 ι} {u t : ι} (hr : (T.deleteEdges {e}).Reachable u t) :
    τ t ≤ treeDecompSide T τ e u := by
  classical
  unfold treeDecompSide
  rw [le_iff_of_le (hTD.le t) (biUnion_le_of_le fun x _ ↦ hTD.le x)]
  refine ⟨?_, ?_⟩ <;>
  · intro x hx
    simp only [biUnion, Set.mem_iUnion, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨t, hr, hx⟩

/-- If `u₀` is a sink for `(A₀, B₀)` in `(T, τ)`, then `τ t ≤ B₀` for all `t ≠ u₀`. -/
private theorem tau_le_right_of_sink [Fintype ι] {G : Hypergraph α β}
    {T : SimpleGraph ι} {τ : ι → Hypergraph α β} (hTD : IsTreeDecomposition G T τ)
    {A₀ B₀ : Hypergraph α β} {u₀ : ι}
    (hu₀ : ∀ w : ι, T.Adj u₀ w →
      A₀ ≤ treeDecompSide T τ s(u₀, w) u₀ ∧ treeDecompSide T τ s(u₀, w) w ≤ B₀)
    {t : ι} (hne : t ≠ u₀) :
    τ t ≤ B₀ := by
  obtain ⟨p, hp, _⟩ := hTD.isTree.existsUnique_path u₀ t
  cases p with
  | nil => exact (hne rfl).elim
  | @cons _ w _ hadj q =>
    rw [Walk.cons_isPath_iff] at hp
    have hreach : (T.deleteEdges {s(u₀, w)}).Reachable w t :=
      reachable_deleteEdges_of_notMem_support q hp.2
    exact (le_treeDecompSide hTD hreach).trans (hu₀ w hadj).2

/-- If `u₀` is a sink for `(A₀, B₀)` in `(T, τ)`, then `A₀ ≤ τ u₀`. -/
private theorem left_le_tau_of_sink [Fintype ι] {G : Hypergraph α β}
    {T : SimpleGraph ι} {τ : ι → Hypergraph α β} (hTD : IsTreeDecomposition G T τ)
    {A₀ B₀ : Hypergraph α β} (hAB : G.IsSeparation A₀ B₀) {u₀ : ι}
    (hu₀ : ∀ w : ι, T.Adj u₀ w →
      A₀ ≤ treeDecompSide T τ s(u₀, w) u₀ ∧ treeDecompSide T τ s(u₀, w) w ≤ B₀) :
    A₀ ≤ τ u₀ := by
  rw [le_iff_of_le hAB.left_le (hTD.le u₀)]
  refine ⟨?_, ?_⟩
  · intro v hvA
    have hvG : v ∈ G.vertexSet := hAB.left_le.vertexSet_subset hvA
    rw [← hTD.biUnion_eq] at hvG
    simp only [biUnion, Set.mem_iUnion, Finset.mem_univ, true_and, exists_true_left] at hvG
    obtain ⟨t, hvt⟩ := hvG
    by_cases htu : t = u₀
    · exact htu ▸ hvt
    · obtain ⟨p, hp, _⟩ := hTD.isTree.existsUnique_path u₀ t
      cases p with
      | nil => exact (htu rfl).elim
      | @cons _ w _ hadj q =>
        rw [Walk.cons_isPath_iff] at hp
        have hwt : (T.deleteEdges {s(u₀, w)}).Reachable w t :=
          reachable_deleteEdges_of_notMem_support q hp.2
        have hv_side : v ∈ (treeDecompSide T τ s(u₀, w) u₀).vertexSet :=
          (hu₀ w hadj).1.vertexSet_subset hvA
        simp only [treeDecompSide, biUnion, Set.mem_iUnion, Finset.mem_filter, Finset.mem_univ,
          true_and] at hv_side
        obtain ⟨t₁, hut₁, hvt₁⟩ := hv_side
        have hon : OnTreePath T t₁ t u₀ :=
          onTreePath_of_reachable_deleteEdges hTD.isTree hadj hut₁ hwt
        exact (hTD.inter_le hon).vertexSet_subset ⟨hvt₁, hvt⟩
  · intro e heA
    have heG : e ∈ G.edgeSet := hAB.left_le.edgeSet_subset heA
    rw [← hTD.biUnion_eq] at heG
    simp only [biUnion, Set.mem_iUnion, Finset.mem_univ, true_and, exists_true_left] at heG
    obtain ⟨t, het⟩ := heG
    by_cases htu : t = u₀
    · exact htu ▸ het
    · exfalso
      have heB : e ∈ B₀.edgeSet :=
        (tau_le_right_of_sink hTD hu₀ htu).edgeSet_subset het
      have hemp := hAB.edgeSet_inter_eq
      exact Set.notMem_empty e (hemp ▸ ⟨heA, heB⟩)

private theorem union_inter_eq_tau_of_sink [Fintype ι] {G : Hypergraph α β}
    {T : SimpleGraph ι} {τ : ι → Hypergraph α β} (hTD : IsTreeDecomposition G T τ)
    {A₀ B₀ : Hypergraph α β} (hAB : G.IsSeparation A₀ B₀) {u₀ : ι}
    (hu₀ : ∀ w : ι, T.Adj u₀ w →
      A₀ ≤ treeDecompSide T τ s(u₀, w) u₀ ∧ treeDecompSide T τ s(u₀, w) w ≤ B₀) :
    A₀ ∪ (τ u₀ ∩ B₀) = τ u₀ := by
  have hA₀ : A₀ ≤ τ u₀ := left_le_tau_of_sink hTD hAB hu₀
  refine eq_of_le_of_vertexSet_eq_of_edgeSet_eq
    (union_le hAB.left_le (inter_le (hTD.le u₀) hAB.right_le)) (hTD.le u₀) ?_ ?_
  · ext v
    simp only [union_vertexSet, inter_vertexSet, Set.mem_union, Set.mem_inter_iff]
    refine ⟨fun h ↦ h.elim (fun hv ↦ hA₀.vertexSet_subset hv) And.left, fun hvu ↦ ?_⟩
    have hvAB : v ∈ A₀.vertexSet ∪ B₀.vertexSet :=
      hAB.vertexSet_union.symm ▸ (hTD.le u₀).vertexSet_subset hvu
    rcases hvAB with hvA | hvB
    · exact Or.inl hvA
    · exact Or.inr ⟨hvu, hvB⟩
  · ext e
    simp only [union_edgeSet, inter_edgeSet, Set.mem_union, Set.mem_inter_iff]
    refine ⟨fun h ↦ h.elim (fun he ↦ hA₀.edgeSet_subset he) And.left, fun heu ↦ ?_⟩
    have heAB : e ∈ A₀.edgeSet ∪ B₀.edgeSet :=
      hAB.edgeSet_union.symm ▸ (hTD.le u₀).edgeSet_subset heu
    rcases heAB with heA | heB
    · exact Or.inl heA
    · exact Or.inr ⟨heu, heB⟩

open Classical in
/-- Bag assignment on `Option ι` splitting `τ u₀` into `A₀` at `none` and `τ u₀ ∩ B₀` at `some u₀`.
-/
private noncomputable def leafBag (τ : ι → Hypergraph α β) (u₀ : ι)
    (A₀ B₀ : Hypergraph α β) : Option ι → Hypergraph α β
  | none => A₀
  | some t => if t = u₀ then τ u₀ ∩ B₀ else τ t

private theorem leafBag_le [Fintype ι] {G : Hypergraph α β}
    {T : SimpleGraph ι} {τ : ι → Hypergraph α β} (hTD : IsTreeDecomposition G T τ)
    {A₀ B₀ : Hypergraph α β} (hAB : G.IsSeparation A₀ B₀) (u₀ : ι) (a : Option ι) :
    leafBag τ u₀ A₀ B₀ a ≤ G := by
  classical
  rcases a with _ | t
  · exact hAB.left_le
  · simp only [leafBag]
    split_ifs
    · exact inter_le (hTD.le u₀) hAB.right_le
    · exact hTD.le t

private theorem leafBag_le_proj [Fintype ι] {G : Hypergraph α β}
    {T : SimpleGraph ι} {τ : ι → Hypergraph α β} (hTD : IsTreeDecomposition G T τ)
    {A₀ B₀ : Hypergraph α β} (hAB : G.IsSeparation A₀ B₀) {u₀ : ι}
    (hu₀ : ∀ w : ι, T.Adj u₀ w →
      A₀ ≤ treeDecompSide T τ s(u₀, w) u₀ ∧ treeDecompSide T τ s(u₀, w) w ≤ B₀)
    (a : Option ι) :
    leafBag τ u₀ A₀ B₀ a ≤ τ (projAttach u₀ a) := by
  classical
  rcases a with _ | t
  · exact left_le_tau_of_sink hTD hAB hu₀
  · simp only [leafBag, projAttach]
    split_ifs with htu
    · subst t
      exact inter_le_left (hTD.le u₀) hAB.right_le
    · exact le_rfl

private theorem leafBag_some_le_right [Fintype ι] {G : Hypergraph α β}
    {T : SimpleGraph ι} {τ : ι → Hypergraph α β} (hTD : IsTreeDecomposition G T τ)
    {A₀ B₀ : Hypergraph α β} (hAB : G.IsSeparation A₀ B₀) {u₀ : ι}
    (hu₀ : ∀ w : ι, T.Adj u₀ w →
      A₀ ≤ treeDecompSide T τ s(u₀, w) u₀ ∧ treeDecompSide T τ s(u₀, w) w ≤ B₀)
    (t : ι) :
    leafBag τ u₀ A₀ B₀ (some t) ≤ B₀ := by
  classical
  simp only [leafBag]
  split_ifs with htu
  · exact inter_le_right (hTD.le u₀) hAB.right_le
  · exact tau_le_right_of_sink hTD hu₀ htu

private theorem isTreeDecomposition_leafGraph [Fintype ι] {G : Hypergraph α β}
    {T : SimpleGraph ι} {τ : ι → Hypergraph α β} (hTD : IsTreeDecomposition G T τ)
    {A₀ B₀ : Hypergraph α β} (hAB : G.IsSeparation A₀ B₀) {u₀ : ι}
    (hu₀ : ∀ w : ι, T.Adj u₀ w →
      A₀ ≤ treeDecompSide T τ s(u₀, w) u₀ ∧ treeDecompSide T τ s(u₀, w) w ≤ B₀) :
    IsTreeDecomposition G (attachLeaf T u₀) (leafBag τ u₀ A₀ B₀) where
  isTree := isTree_attachLeaf hTD.isTree u₀
  le := leafBag_le hTD hAB u₀
  biUnion_eq := by
    classical
    have hu₀_eq := union_inter_eq_tau_of_sink hTD hAB hu₀
    have hle1 : Hypergraph.biUnion Finset.univ (leafBag τ u₀ A₀ B₀) ≤ G :=
      biUnion_le_of_le fun a _ ↦ leafBag_le hTD hAB u₀ a
    refine eq_of_le_of_vertexSet_eq_of_edgeSet_eq hle1 le_rfl ?_ ?_
    · rw [← hTD.biUnion_eq]
      ext v
      simp only [biUnion, Set.mem_iUnion, Finset.mem_univ, true_and, exists_true_left]
      constructor
      · rintro ⟨a, hva⟩
        exact ⟨projAttach u₀ a, (leafBag_le_proj hTD hAB hu₀ a).vertexSet_subset hva⟩
      · rintro ⟨t, hvt⟩
        by_cases htu : t = u₀
        · subst t
          rw [← hu₀_eq] at hvt
          rcases hvt with hvA | hvB
          · exact ⟨none, hvA⟩
          · refine ⟨some u₀, ?_⟩
            simpa [leafBag] using hvB
        · refine ⟨some t, ?_⟩
          simp [leafBag, htu, hvt]
    · rw [← hTD.biUnion_eq]
      ext e
      simp only [biUnion, Set.mem_iUnion, Finset.mem_univ, true_and, exists_true_left]
      constructor
      · rintro ⟨a, hea⟩
        exact ⟨projAttach u₀ a, (leafBag_le_proj hTD hAB hu₀ a).edgeSet_subset hea⟩
      · rintro ⟨t, het⟩
        by_cases htu : t = u₀
        · subst t
          rw [← hu₀_eq] at het
          rcases het with heA | heB
          · exact ⟨none, heA⟩
          · refine ⟨some u₀, ?_⟩
            simpa [leafBag] using heB
        · refine ⟨some t, ?_⟩
          simp [leafBag, htu, het]
  edgeSet_inter_eq a₁ a₂ hne := by
    classical
    ext e
    simp only [inter_edgeSet, Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
    intro he1 he2
    rcases a₁ with _ | t₁ <;> rcases a₂ with _ | t₂
    · exact hne rfl
    · have heB : e ∈ B₀.edgeSet := (leafBag_some_le_right hTD hAB hu₀ t₂).edgeSet_subset he2
      exact Set.notMem_empty e (hAB.edgeSet_inter_eq ▸ ⟨he1, heB⟩)
    · have heB : e ∈ B₀.edgeSet := (leafBag_some_le_right hTD hAB hu₀ t₁).edgeSet_subset he1
      exact Set.notMem_empty e (hAB.edgeSet_inter_eq ▸ ⟨he2, heB⟩)
    · have htne : t₁ ≠ t₂ := by rintro rfl; exact hne rfl
      have he1' : e ∈ (τ t₁).edgeSet := (leafBag_le_proj hTD hAB hu₀ (some t₁)).edgeSet_subset he1
      have he2' : e ∈ (τ t₂).edgeSet := (leafBag_le_proj hTD hAB hu₀ (some t₂)).edgeSet_subset he2
      exact Set.notMem_empty e (hTD.edgeSet_inter_eq htne ▸ ⟨he1', he2'⟩)
  inter_le {a₁ a₂ a₃} hon := by
    classical
    by_cases h13 : a₁ = a₃
    · subst a₃
      have hmem := hon .nil Walk.IsPath.nil
      simp only [Walk.support_nil, List.mem_singleton] at hmem
      subst a₂
      exact inter_le_left (leafBag_le hTD hAB u₀ a₁) (leafBag_le hTD hAB u₀ a₁)
    · rcases a₂ with _ | w
      · rcases a₁ with _ | x₁
        · exact inter_le_left (leafBag_le hTD hAB u₀ none) (leafBag_le hTD hAB u₀ a₃)
        · rcases a₃ with _ | x₃
          · exact inter_le_right (leafBag_le hTD hAB u₀ (some x₁)) (leafBag_le hTD hAB u₀ none)
          · exfalso
            obtain ⟨q, hq, _⟩ := hTD.isTree.existsUnique_path x₁ x₃
            have hq_map : (q.map (attachLeafSomeHom T u₀)).IsPath :=
              hq.map (Option.some_injective ι)
            have hmem : none ∈ (q.map (attachLeafSomeHom T u₀)).support := hon _ hq_map
            rw [Walk.support_map, List.mem_map] at hmem
            obtain ⟨w, -, hw⟩ := hmem
            change some w = none at hw
            cases hw
      · have hon' : OnTreePath T (projAttach u₀ a₁) (projAttach u₀ a₃) w :=
          onTreePath_projAttach_of_some hon
        have hle_w : leafBag τ u₀ A₀ B₀ a₁ ∩ leafBag τ u₀ A₀ B₀ a₃ ≤ τ w := by
          have h1 := leafBag_le_proj hTD hAB hu₀ a₁
          have h3 := leafBag_le_proj hTD hAB hu₀ a₃
          have h13_le : leafBag τ u₀ A₀ B₀ a₁ ∩ leafBag τ u₀ A₀ B₀ a₃ ≤
              τ (projAttach u₀ a₁) ∩ τ (projAttach u₀ a₃) := by
            rw [le_iff_of_le
              (inter_le (leafBag_le hTD hAB u₀ a₁) (leafBag_le hTD hAB u₀ a₃))
              (inter_le (hTD.le _) (hTD.le _))]
            exact ⟨Set.inter_subset_inter h1.vertexSet_subset h3.vertexSet_subset,
              Set.inter_subset_inter h1.edgeSet_subset h3.edgeSet_subset⟩
          exact h13_le.trans (hTD.inter_le hon')
        change leafBag τ u₀ A₀ B₀ a₁ ∩ leafBag τ u₀ A₀ B₀ a₃ ≤
          if w = u₀ then τ u₀ ∩ B₀ else τ w
        split_ifs with hwu
        · subst w
          have hle_B₀ : leafBag τ u₀ A₀ B₀ a₁ ∩ leafBag τ u₀ A₀ B₀ a₃ ≤ B₀ := by
            rcases a₁ with _ | x₁
            · rcases a₃ with _ | x₃
              · exact (h13 rfl).elim
              · exact (inter_le_right (leafBag_le hTD hAB u₀ none)
                  (leafBag_le hTD hAB u₀ (some x₃))).trans
                  (leafBag_some_le_right hTD hAB hu₀ x₃)
            · exact (inter_le_left (leafBag_le hTD hAB u₀ (some x₁))
                (leafBag_le hTD hAB u₀ a₃)).trans
                (leafBag_some_le_right hTD hAB hu₀ x₁)
          rw [le_iff_of_le
            (inter_le (leafBag_le hTD hAB u₀ a₁) (leafBag_le hTD hAB u₀ a₃))
            (inter_le (hTD.le u₀) hAB.right_le)]
          exact ⟨Set.subset_inter hle_w.vertexSet_subset hle_B₀.vertexSet_subset,
            Set.subset_inter hle_w.edgeSet_subset hle_B₀.edgeSet_subset⟩
        · exact hle_w

private theorem treeDecompSide_leafGraph_new_none [Fintype ι] {G : Hypergraph α β}
    {T : SimpleGraph ι} {τ : ι → Hypergraph α β} (hTD : IsTreeDecomposition G T τ)
    {A₀ B₀ : Hypergraph α β} (hAB : G.IsSeparation A₀ B₀) (u₀ : ι) :
    treeDecompSide (attachLeaf T u₀) (leafBag τ u₀ A₀ B₀) s(none, some u₀) none = A₀ := by
  classical
  have hle1 : treeDecompSide (attachLeaf T u₀) (leafBag τ u₀ A₀ B₀) s(none, some u₀) none ≤ G :=
    biUnion_le_of_le fun a _ ↦ leafBag_le hTD hAB u₀ a
  refine eq_of_le_of_vertexSet_eq_of_edgeSet_eq hle1 hAB.left_le ?_ ?_ <;>
  · ext x
    simp [treeDecompSide, biUnion, attachLeaf_delete_new_reachable_none, leafBag]

private theorem treeDecompSide_leafGraph_new_some [Fintype ι] {G : Hypergraph α β}
    {T : SimpleGraph ι} {τ : ι → Hypergraph α β} (hTD : IsTreeDecomposition G T τ)
    {A₀ B₀ : Hypergraph α β} (hAB : G.IsSeparation A₀ B₀) {u₀ : ι}
    (hu₀ : ∀ w : ι, T.Adj u₀ w →
      A₀ ≤ treeDecompSide T τ s(u₀, w) u₀ ∧ treeDecompSide T τ s(u₀, w) w ≤ B₀) :
    treeDecompSide (attachLeaf T u₀) (leafBag τ u₀ A₀ B₀) s(none, some u₀) (some u₀) = B₀ := by
  classical
  have hle1 :
      treeDecompSide (attachLeaf T u₀) (leafBag τ u₀ A₀ B₀) s(none, some u₀) (some u₀) ≤ G :=
    biUnion_le_of_le fun a _ ↦ leafBag_le hTD hAB u₀ a
  refine eq_of_le_of_vertexSet_eq_of_edgeSet_eq hle1 hAB.right_le ?_ ?_
  · ext v
    simp only [treeDecompSide, biUnion, Set.mem_iUnion, Finset.mem_filter, Finset.mem_univ,
      true_and, attachLeaf_delete_new_reachable_some hTD.isTree.connected]
    constructor
    · rintro ⟨a, ⟨t, rfl⟩, hva⟩
      exact (leafBag_some_le_right hTD hAB hu₀ t).vertexSet_subset hva
    · intro hvB
      have hvG : v ∈ G.vertexSet := hAB.right_le.vertexSet_subset hvB
      rw [← hTD.biUnion_eq] at hvG
      simp only [biUnion, Set.mem_iUnion, Finset.mem_univ, true_and, exists_true_left] at hvG
      obtain ⟨t, hvt⟩ := hvG
      refine ⟨some t, ⟨t, rfl⟩, ?_⟩
      by_cases htu : t = u₀
      · subst t
        simpa [leafBag] using And.intro hvt hvB
      · simp [leafBag, htu, hvt]
  · ext e
    simp only [treeDecompSide, biUnion, Set.mem_iUnion, Finset.mem_filter, Finset.mem_univ,
      true_and, attachLeaf_delete_new_reachable_some hTD.isTree.connected]
    constructor
    · rintro ⟨a, ⟨t, rfl⟩, hea⟩
      exact (leafBag_some_le_right hTD hAB hu₀ t).edgeSet_subset hea
    · intro heB
      have heG : e ∈ G.edgeSet := hAB.right_le.edgeSet_subset heB
      rw [← hTD.biUnion_eq] at heG
      simp only [biUnion, Set.mem_iUnion, Finset.mem_univ, true_and, exists_true_left] at heG
      obtain ⟨t, het⟩ := heG
      refine ⟨some t, ⟨t, rfl⟩, ?_⟩
      by_cases htu : t = u₀
      · subst t
        simpa [leafBag] using And.intro het heB
      · simp [leafBag, htu, het]

private theorem treeDecompSide_leafGraph_old [Fintype ι] {G : Hypergraph α β}
    {T : SimpleGraph ι} {τ : ι → Hypergraph α β} (hTD : IsTreeDecomposition G T τ)
    {A₀ B₀ : Hypergraph α β} (hAB : G.IsSeparation A₀ B₀) {u₀ : ι}
    (hu₀ : ∀ w : ι, T.Adj u₀ w →
      A₀ ≤ treeDecompSide T τ s(u₀, w) u₀ ∧ treeDecompSide T τ s(u₀, w) w ≤ B₀)
    (x y : ι) (z : Option ι) :
    treeDecompSide (attachLeaf T u₀) (leafBag τ u₀ A₀ B₀) s(some x, some y) z =
      treeDecompSide T τ s(x, y) (projAttach u₀ z) := by
  classical
  have hu₀_eq := union_inter_eq_tau_of_sink hTD hAB hu₀
  have hle1 : treeDecompSide (attachLeaf T u₀) (leafBag τ u₀ A₀ B₀) s(some x, some y) z ≤ G :=
    biUnion_le_of_le fun a _ ↦ leafBag_le hTD hAB u₀ a
  have hle2 : treeDecompSide T τ s(x, y) (projAttach u₀ z) ≤ G :=
    biUnion_le_of_le fun t _ ↦ hTD.le t
  refine eq_of_le_of_vertexSet_eq_of_edgeSet_eq hle1 hle2 ?_ ?_
  · ext v
    simp only [treeDecompSide, biUnion, Set.mem_iUnion, Finset.mem_filter, Finset.mem_univ,
      true_and, attachLeaf_delete_old_reachable_iff]
    constructor
    · rintro ⟨a, hr, hva⟩
      exact ⟨projAttach u₀ a, hr, (leafBag_le_proj hTD hAB hu₀ a).vertexSet_subset hva⟩
    · rintro ⟨t, hr, hvt⟩
      by_cases htu : t = u₀
      · subst t
        rw [← hu₀_eq] at hvt
        rcases hvt with hvA | hvB
        · exact ⟨none, hr, hvA⟩
        · refine ⟨some u₀, hr, ?_⟩
          simpa [leafBag] using hvB
      · refine ⟨some t, hr, ?_⟩
        simp [leafBag, htu, hvt]
  · ext e
    simp only [treeDecompSide, biUnion, Set.mem_iUnion, Finset.mem_filter, Finset.mem_univ,
      true_and, attachLeaf_delete_old_reachable_iff]
    constructor
    · rintro ⟨a, hr, hea⟩
      exact ⟨projAttach u₀ a, hr, (leafBag_le_proj hTD hAB hu₀ a).edgeSet_subset hea⟩
    · rintro ⟨t, hr, het⟩
      by_cases htu : t = u₀
      · subst t
        rw [← hu₀_eq] at het
        rcases het with heA | heB
        · exact ⟨none, hr, heA⟩
        · refine ⟨some u₀, hr, ?_⟩
          simpa [leafBag] using heB
      · refine ⟨some t, hr, ?_⟩
        simp [leafBag, htu, het]

private theorem makesSeparation_leafGraph_new_iff [Fintype ι] {G : Hypergraph α β}
    {T : SimpleGraph ι} {τ : ι → Hypergraph α β} (hTD : IsTreeDecomposition G T τ)
    {A₀ B₀ : Hypergraph α β} (hAB : G.IsSeparation A₀ B₀) {u₀ : ι}
    (hu₀ : ∀ w : ι, T.Adj u₀ w →
      A₀ ≤ treeDecompSide T τ s(u₀, w) u₀ ∧ treeDecompSide T τ s(u₀, w) w ≤ B₀)
    {C D : Hypergraph α β} :
    MakesSeparation (attachLeaf T u₀) (leafBag τ u₀ A₀ B₀) s(none, some u₀) C D ↔
      (C = A₀ ∧ D = B₀) ∨ (C = B₀ ∧ D = A₀) := by
  have hnone := treeDecompSide_leafGraph_new_none hTD hAB u₀
  have hsome := treeDecompSide_leafGraph_new_some hTD hAB hu₀
  constructor
  · rintro ⟨a, b, _, heq, rfl, rfl⟩
    rcases Sym2.eq_iff.1 heq.symm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨hnone, hsome⟩
    · refine Or.inr ⟨?_, ?_⟩
      · simpa [Sym2.eq_swap] using hsome
      · simpa [Sym2.eq_swap] using hnone
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact ⟨none, some u₀, rfl, rfl, hnone.symm, hsome.symm⟩
    · refine ⟨some u₀, none, rfl, Sym2.eq_swap, ?_, ?_⟩
      · simpa [Sym2.eq_swap] using hsome.symm
      · simpa [Sym2.eq_swap] using hnone.symm

private theorem makesSeparation_leafGraph_old_iff [Fintype ι] {G : Hypergraph α β}
    {T : SimpleGraph ι} {τ : ι → Hypergraph α β} (hTD : IsTreeDecomposition G T τ)
    {A₀ B₀ : Hypergraph α β} (hAB : G.IsSeparation A₀ B₀) {u₀ : ι}
    (hu₀ : ∀ w : ι, T.Adj u₀ w →
      A₀ ≤ treeDecompSide T τ s(u₀, w) u₀ ∧ treeDecompSide T τ s(u₀, w) w ≤ B₀)
    {x y : ι} {C D : Hypergraph α β} :
    MakesSeparation (attachLeaf T u₀) (leafBag τ u₀ A₀ B₀) s(some x, some y) C D ↔
      MakesSeparation T τ s(x, y) C D := by
  constructor
  · rintro ⟨a, b, hadj, heq, rfl, rfl⟩
    rcases Sym2.eq_iff.1 heq.symm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · refine ⟨x, y, hadj, rfl, ?_, ?_⟩
      · exact treeDecompSide_leafGraph_old hTD hAB hu₀ x y (some x)
      · exact treeDecompSide_leafGraph_old hTD hAB hu₀ x y (some y)
    · refine ⟨y, x, hadj, Sym2.eq_swap, ?_, ?_⟩
      · exact treeDecompSide_leafGraph_old hTD hAB hu₀ y x (some y)
      · exact treeDecompSide_leafGraph_old hTD hAB hu₀ y x (some x)
  · rintro ⟨u, v, hadj, heq, rfl, rfl⟩
    rcases Sym2.eq_iff.1 heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · refine ⟨some x, some y, hadj, rfl, ?_, ?_⟩
      · exact (treeDecompSide_leafGraph_old hTD hAB hu₀ x y (some x)).symm
      · exact (treeDecompSide_leafGraph_old hTD hAB hu₀ x y (some y)).symm
    · refine ⟨some y, some x, hadj, Sym2.eq_swap, ?_, ?_⟩
      · exact (treeDecompSide_leafGraph_old hTD hAB hu₀ y x (some y)).symm
      · exact (treeDecompSide_leafGraph_old hTD hAB hu₀ y x (some x)).symm

/-! ## Proof of (9.2): Existence of a tie-breaker -/

/-- Sum of powers of 2 over a subset of `{0, ..., n - 1}` is strictly less than `2 ^ n`. -/
private theorem sum_two_pow_lt {n : ℕ} (S : Finset ℕ) (hS : ∀ i ∈ S, i < n) :
    ∑ i ∈ S, 2 ^ i < 2 ^ n := by
  have hsub : S ⊆ Finset.range n := fun i hi ↦ Finset.mem_range.2 (hS i hi)
  have hle : ∑ i ∈ S, 2 ^ i ≤ ∑ i ∈ Finset.range n, 2 ^ i :=
    Finset.sum_le_sum_of_subset hsub
  have hgeom : ∀ m, (∑ i ∈ Finset.range m, 2 ^ i) + 1 = 2 ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ihm =>
      rw [Finset.sum_range_succ, pow_succ]
      omega
  have := hgeom n
  omega

/-- Distinct subsets of `{0, ..., n - 1}` have distinct sums of `2 ^ i`. -/
private theorem eq_of_sum_two_pow_eq :
    ∀ (n : ℕ) {S₁ S₂ : Finset ℕ}, (∀ i ∈ S₁, i < n) → (∀ i ∈ S₂, i < n) →
      ∑ i ∈ S₁, 2 ^ i = ∑ i ∈ S₂, 2 ^ i → S₁ = S₂
  | 0, S₁, S₂, h₁, h₂, _ => by
    ext i
    constructor <;> intro hi
    · have := h₁ i hi; omega
    · have := h₂ i hi; omega
  | n + 1, S₁, S₂, h₁, h₂, hsum => by
    have hmem : n ∈ S₁ ↔ n ∈ S₂ := by
      constructor <;> intro hn
      · by_contra hn₂
        have hlt₂ : ∑ i ∈ S₂, 2 ^ i < 2 ^ n := by
          refine sum_two_pow_lt S₂ fun i hi ↦ ?_
          have hlt := h₂ i hi
          have hne : i ≠ n := by rintro rfl; exact hn₂ hi
          omega
        have hge₁ : 2 ^ n ≤ ∑ i ∈ S₁, 2 ^ i :=
          Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) hn
        omega
      · by_contra hn₁
        have hlt₁ : ∑ i ∈ S₁, 2 ^ i < 2 ^ n := by
          refine sum_two_pow_lt S₁ fun i hi ↦ ?_
          have hlt := h₁ i hi
          have hne : i ≠ n := by rintro rfl; exact hn₁ hi
          omega
        have hge₂ : 2 ^ n ≤ ∑ i ∈ S₂, 2 ^ i :=
          Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) hn
        omega
    have h₁' : ∀ i ∈ S₁.erase n, i < n := by
      intro i hi
      have hne := (Finset.mem_erase.1 hi).1
      have hlt := h₁ i (Finset.mem_erase.1 hi).2
      omega
    have h₂' : ∀ i ∈ S₂.erase n, i < n := by
      intro i hi
      have hne := (Finset.mem_erase.1 hi).1
      have hlt := h₂ i (Finset.mem_erase.1 hi).2
      omega
    have hsum' : ∑ i ∈ S₁.erase n, 2 ^ i = ∑ i ∈ S₂.erase n, 2 ^ i := by
      by_cases hn₁ : n ∈ S₁
      · have hn₂ : n ∈ S₂ := hmem.1 hn₁
        have hs₁ := Finset.add_sum_erase S₁ (fun i ↦ 2 ^ i) hn₁
        have hs₂ := Finset.add_sum_erase S₂ (fun i ↦ 2 ^ i) hn₂
        omega
      · have hn₂ : n ∉ S₂ := mt hmem.2 hn₁
        rwa [Finset.erase_eq_of_notMem hn₁, Finset.erase_eq_of_notMem hn₂]
    have heq := eq_of_sum_two_pow_eq n h₁' h₂' hsum'
    ext i
    by_cases hin : i = n
    · subst hin; exact hmem
    · constructor <;> intro hi
      · exact (Finset.mem_erase.1 (heq ▸ Finset.mem_erase.2 ⟨hin, hi⟩)).2
      · exact (Finset.mem_erase.1 (heq.symm ▸ Finset.mem_erase.2 ⟨hin, hi⟩)).2

private theorem eq_of_sum_two_pow_equiv {γ : Type*} {n : ℕ} (e : γ ≃ Fin n)
    {S₁ S₂ : Finset γ}
    (hsum : ∑ x ∈ S₁, 2 ^ (e x).val = ∑ x ∈ S₂, 2 ^ (e x).val) : S₁ = S₂ := by
  let emb : γ ↪ ℕ := ⟨fun x ↦ (e x).val, fun x y h ↦ e.injective (Fin.ext h)⟩
  have h1 : ∀ S : Finset γ, ∑ i ∈ S.map emb, 2 ^ i = ∑ x ∈ S, 2 ^ (e x).val :=
    fun S ↦ Finset.sum_map S emb (fun i ↦ 2 ^ i)
  have h2 : ∀ S : Finset γ, ∀ i ∈ S.map emb, i < n := by
    intro S i hi
    rcases Finset.mem_map.1 hi with ⟨x, _, rfl⟩
    exact (e x).isLt
  have hmap := eq_of_sum_two_pow_eq n (h2 S₁) (h2 S₂) (by rw [h1, h1, hsum])
  exact Finset.map_injective emb hmap

/-- The disjoint union `L(G) = V(G) ⊔ E(G)` used in the proof of (9.2) (page 178). -/
abbrev LType (G : Hypergraph α β) : Type _ := ↥G.vertexSet ⊕ ↥G.edgeSet

noncomputable instance (G : Hypergraph α β) : Fintype (LType G) := by
  classical
  haveI : Fintype ↥G.vertexSet := G.vertexSet_finite.fintype
  haveI : Fintype ↥G.edgeSet := G.edgeSet_finite.fintype
  infer_instance

open Classical in
/-- The subset `L(A) ⊆ L(G)` for a subhypergraph `A` of `G`. -/
noncomputable def LFinset (G A : Hypergraph α β) : Finset (LType G) :=
  Finset.univ.filter fun x ↦
    match x with
    | .inl v => v.val ∈ A.vertexSet
    | .inr e => e.val ∈ A.edgeSet

@[simp]
private theorem mem_LFinset_inl {G A : Hypergraph α β} (v : ↥G.vertexSet) :
    Sum.inl v ∈ LFinset G A ↔ v.val ∈ A.vertexSet := by
  simp [LFinset]

@[simp]
private theorem mem_LFinset_inr {G A : Hypergraph α β} (e : ↥G.edgeSet) :
    Sum.inr e ∈ LFinset G A ↔ e.val ∈ A.edgeSet := by
  simp [LFinset]

private theorem LFinset_self (G : Hypergraph α β) : LFinset G G = Finset.univ := by
  ext x
  rcases x with ⟨v, hv⟩ | ⟨e, he⟩
  · simp [LFinset, hv]
  · simp [LFinset, he]

open Classical in
private theorem LFinset_union (G A B : Hypergraph α β) :
    LFinset G (A ∪ B) = LFinset G A ∪ LFinset G B := by
  ext x
  rcases x with v | e <;> simp [LFinset]

open Classical in
private theorem LFinset_inter (G A B : Hypergraph α β) :
    LFinset G (A ∩ B) = LFinset G A ∩ LFinset G B := by
  ext x
  rcases x with v | e <;> simp [LFinset]

private theorem eq_of_LFinset_eq {G A B : Hypergraph α β} (hA : A ≤ G) (hB : B ≤ G)
    (h : LFinset G A = LFinset G B) : A = B := by
  refine eq_of_le_of_vertexSet_eq_of_edgeSet_eq hA hB ?_ ?_
  · ext v
    constructor <;> intro hv
    · have hvG := hA.vertexSet_subset hv
      have hmem : (Sum.inl ⟨v, hvG⟩ : LType G) ∈ LFinset G A := (mem_LFinset_inl _).2 hv
      exact (mem_LFinset_inl _).1 (h ▸ hmem)
    · have hvG := hB.vertexSet_subset hv
      have hmem : (Sum.inl ⟨v, hvG⟩ : LType G) ∈ LFinset G B := (mem_LFinset_inl _).2 hv
      exact (mem_LFinset_inl _).1 (h.symm ▸ hmem)
  · ext e
    constructor <;> intro he
    · have heG := hA.edgeSet_subset he
      have hmem : (Sum.inr ⟨e, heG⟩ : LType G) ∈ LFinset G A := (mem_LFinset_inr _).2 he
      exact (mem_LFinset_inr _).1 (h ▸ hmem)
    · have heG := hB.edgeSet_subset he
      have hmem : (Sum.inr ⟨e, heG⟩ : LType G) ∈ LFinset G B := (mem_LFinset_inr _).2 he
      exact (mem_LFinset_inr _).1 (h.symm ▸ hmem)

private theorem LFinset_mono {G A B : Hypergraph α β} (h : A ≤ B) :
    LFinset G A ⊆ LFinset G B := by
  intro x hx
  rcases x with v | e
  · exact (mem_LFinset_inl v).2 (h.vertexSet_subset ((mem_LFinset_inl v).1 hx))
  · exact (mem_LFinset_inr e).2 (h.edgeSet_subset ((mem_LFinset_inr e).1 hx))

open Classical in
private noncomputable def sepScore (G A B : Hypergraph α β) : ℕ :=
  (LFinset G A).card + (Finset.univ \ LFinset G B).card

private theorem eq_of_le_of_sepScore_le {G A B C D : Hypergraph α β}
    (hAB : G.IsSeparation A B) (hCD : G.IsSeparation C D)
    (hCA : C ≤ A) (hBD : B ≤ D) (hscore : sepScore G A B ≤ sepScore G C D) :
    C = A ∧ D = B := by
  classical
  have hsub1 : LFinset G C ⊆ LFinset G A := LFinset_mono hCA
  have hsub2 : Finset.univ \ LFinset G D ⊆ Finset.univ \ LFinset G B :=
    Finset.sdiff_subset_sdiff (Finset.Subset.refl _) (LFinset_mono hBD)
  have hc1 : (LFinset G C).card ≤ (LFinset G A).card := Finset.card_le_card hsub1
  have hc2 : (Finset.univ \ LFinset G D).card ≤ (Finset.univ \ LFinset G B).card :=
    Finset.card_le_card hsub2
  unfold sepScore at hscore
  have heq1 : LFinset G C = LFinset G A :=
    Finset.eq_of_subset_of_card_le hsub1 (by omega)
  have heq2 : Finset.univ \ LFinset G D = Finset.univ \ LFinset G B :=
    Finset.eq_of_subset_of_card_le hsub2 (by omega)
  have heq2' : LFinset G D = LFinset G B := by
    ext x
    have := Finset.ext_iff.1 heq2 x
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, not_iff_not] at this
    exact this
  exact ⟨eq_of_LFinset_eq hCD.left_le hAB.left_le heq1,
    eq_of_LFinset_eq hCD.right_le hAB.right_le heq2'⟩

theorem finite_of_forall_isSeparation {G : Hypergraph α β}
    {𝒮 : Set (Hypergraph α β × Hypergraph α β)}
    (hsep : ∀ p ∈ 𝒮, G.IsSeparation p.1 p.2) : 𝒮.Finite := by
  classical
  have : Finite 𝒮 := by
    refine Finite.of_injective
      (fun (p : 𝒮) ↦ (LFinset G p.val.1, LFinset G p.val.2)) ?_
    rintro ⟨⟨A₁, B₁⟩, h1⟩ ⟨⟨A₂, B₂⟩, h2⟩ heq
    simp only [Prod.mk.injEq] at heq
    have hs1 := hsep _ h1
    have hs2 := hsep _ h2
    refine Subtype.ext (Prod.ext ?_ ?_)
    · exact eq_of_LFinset_eq hs1.left_le hs2.left_le heq.1
    · exact eq_of_LFinset_eq hs1.right_le hs2.right_le heq.2
  exact Set.toFinite 𝒮

private theorem mem_leafGraph_edgeSet_iff {T : SimpleGraph ι} {u₀ : ι} {e : Sym2 (Option ι)} :
    e ∈ (attachLeaf T u₀).edgeSet ↔
      e = s(none, some u₀) ∨ ∃ x y : ι, T.Adj x y ∧ e = s(some x, some y) := by
  induction e using Sym2.ind with | _ a b =>
  rcases a with _ | x <;> rcases b with _ | y
  · simp [attachLeaf]
  · constructor
    · intro h
      have hy : y = u₀ := h
      exact Or.inl (by rw [hy])
    · rintro (h | ⟨x', y', _, h⟩)
      · rcases Sym2.eq_iff.1 h with ⟨_, hy⟩ | ⟨hy, _⟩
        · exact Option.some.inj hy
        · cases hy
      · rcases Sym2.eq_iff.1 h with ⟨hx, _⟩ | ⟨hx, _⟩ <;> cases hx
  · constructor
    · intro h
      have hx : x = u₀ := h
      exact Or.inl (by rw [hx]; exact Sym2.eq_swap)
    · rintro (h | ⟨x', y', _, h⟩)
      · rcases Sym2.eq_iff.1 h with ⟨hx, _⟩ | ⟨hx, _⟩
        · cases hx
        · exact Option.some.inj hx
      · rcases Sym2.eq_iff.1 h with ⟨_, hy⟩ | ⟨_, hy⟩ <;> cases hy
  · constructor
    · intro hadj
      exact Or.inr ⟨x, y, hadj, rfl⟩
    · rintro (h | ⟨x', y', hadj, h⟩)
      · rcases Sym2.eq_iff.1 h with ⟨hx, _⟩ | ⟨_, hy⟩
        · cases hx
        · cases hy
      · rcases Sym2.eq_iff.1 h with ⟨hx, hy⟩ | ⟨hx, hy⟩
        · cases hx; cases hy; exact hadj
        · cases hx; cases hy; exact hadj.symm

/-- Inductive construction of a tree-decomposition for a finite symmetric laminar set of
separations of `G`. -/
private theorem exists_treeDecomposition_of_symm_laminar (G : Hypergraph α β) :
    ∀ (n : ℕ) (𝒮 : Finset (Hypergraph α β × Hypergraph α β)),
      𝒮.card = n →
      (∀ p ∈ 𝒮, G.IsSeparation p.1 p.2) →
      (∀ p ∈ 𝒮, p.swap ∈ 𝒮) →
      IsLaminar (𝒮 : Set (Hypergraph α β × Hypergraph α β)) →
      ∃ (ι : Type) (_ : Fintype ι) (T : SimpleGraph ι) (τ : ι → Hypergraph α β),
        IsTreeDecomposition G T τ ∧
        (∀ p ∈ 𝒮, ∃! e : Sym2 ι, e ∈ T.edgeSet ∧ MakesSeparation T τ e p.1 p.2) ∧
        separationsMadeBy T τ = (𝒮 : Set (Hypergraph α β × Hypergraph α β)) := by
  classical
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro 𝒮 hcard hsep hsym hlam
    rcases 𝒮.eq_empty_or_nonempty with rfl | hne
    · refine ⟨Unit, inferInstance, ⊥, fun _ ↦ G, ?_, ?_, ?_⟩
      · refine ⟨IsTree.of_subsingleton, fun _ ↦ le_rfl, ?_, fun _ _ h ↦ (h rfl).elim,
          fun _ _ _ _ ↦ inter_le_left le_rfl le_rfl⟩
        ext x <;> simp [biUnion]
      · intro p hp
        exact (Finset.notMem_empty p hp).elim
      · ext p
        simp [separationsMadeBy]
    · obtain ⟨⟨A₀, B₀⟩, hAB₀_mem, hmin⟩ :=
        𝒮.exists_min_image (fun p ↦ sepScore G p.1 p.2) hne
      have hAB₀ : G.IsSeparation A₀ B₀ := hsep (A₀, B₀) hAB₀_mem
      let 𝒮' : Finset (Hypergraph α β × Hypergraph α β) :=
        (𝒮.erase (A₀, B₀)).erase (B₀, A₀)
      have hsub : 𝒮' ⊆ 𝒮 :=
        (Finset.erase_subset _ _).trans (Finset.erase_subset _ _)
      have hlt : 𝒮'.card < n := by
        rw [← hcard]
        exact (Finset.card_erase_le).trans_lt (Finset.card_erase_lt_of_mem hAB₀_mem)
      have hsep' : ∀ p ∈ 𝒮', G.IsSeparation p.1 p.2 := fun p hp ↦ hsep p (hsub hp)
      have hsym' : ∀ p ∈ 𝒮', p.swap ∈ 𝒮' := by
        rintro ⟨C, D⟩ hp
        simp only [𝒮', Finset.mem_erase, ne_eq, Prod.swap_prod_mk, Prod.mk.injEq] at hp ⊢
        refine ⟨fun h ↦ hp.2.1 ⟨h.2, h.1⟩, fun h ↦ hp.1 ⟨h.2, h.1⟩, ?_⟩
        exact hsym (C, D) hp.2.2
      have hlam' : IsLaminar (𝒮' : Set (Hypergraph α β × Hypergraph α β)) := by
        intro p₁ hp₁ p₂ hp₂
        exact hlam (hsub (Finset.mem_coe.1 hp₁)) (hsub (Finset.mem_coe.1 hp₂))
      obtain ⟨ι', hfin', T', τ', hTD', huniq', hmade'⟩ :=
        ih 𝒮'.card hlt 𝒮' rfl hsep' hsym' hlam'
      have horient : ∀ ⦃C D : Hypergraph α β⦄, (C, D) ∈ 𝒮' →
          (A₀ ≤ C ∧ D ≤ B₀) ∨ (A₀ ≤ D ∧ C ≤ B₀) := by
        intro C D hCD_mem
        have hCD_in : (C, D) ∈ 𝒮 := hsub hCD_mem
        have hDC_in : (D, C) ∈ 𝒮 := hsym (C, D) hCD_in
        have hCD : G.IsSeparation C D := hsep (C, D) hCD_in
        have hncross : ¬ SeparationsCross A₀ B₀ C D := hlam hAB₀_mem hCD_in
        unfold SeparationsCross at hncross
        rw [not_not] at hncross
        rcases hncross with h1 | h2 | ⟨hBC, hDA⟩ | ⟨hBD, hCA⟩
        · exact Or.inl h1
        · exact Or.inr h2
        · exfalso
          have heq := eq_of_le_of_sepScore_le hAB₀ hCD.symm hDA hBC (hmin (D, C) hDC_in)
          simp only [𝒮', Finset.mem_erase, ne_eq, Prod.mk.injEq] at hCD_mem
          exact hCD_mem.1 ⟨heq.2, heq.1⟩
        · exfalso
          have heq := eq_of_le_of_sepScore_le hAB₀ hCD hCA hBD (hmin (C, D) hCD_in)
          simp only [𝒮', Finset.mem_erase, ne_eq, Prod.mk.injEq] at hCD_mem
          exact hCD_mem.2.1 heq
      have hR : ∀ ⦃u v : ι'⦄, T'.Adj u v →
          (A₀ ≤ treeDecompSide T' τ' s(u, v) u ∧ treeDecompSide T' τ' s(u, v) v ≤ B₀) ∨
          (A₀ ≤ treeDecompSide T' τ' s( v, u) v ∧ treeDecompSide T' τ' s(v, u) u ≤ B₀) := by
        intro u v hadj
        have hmem_made :
            (treeDecompSide T' τ' s(u, v) u, treeDecompSide T' τ' s(u, v) v) ∈
              separationsMadeBy T' τ' :=
          ⟨s(u, v), hadj, u, v, hadj, rfl, rfl, rfl⟩
        rw [hmade'] at hmem_made
        rcases horient hmem_made with h1 | h2
        · exact Or.inl h1
        · right
          simpa [Sym2.eq_swap] using h2
      obtain ⟨u₀, hu₀⟩ := exists_sink_of_adj_or hTD'.isTree hR
      let T := attachLeaf T' u₀
      let τ := leafBag τ' u₀ A₀ B₀
      have hTD : IsTreeDecomposition G T τ := isTreeDecomposition_leafGraph hTD' hAB₀ hu₀
      have hmade : separationsMadeBy T τ = (𝒮 : Set (Hypergraph α β × Hypergraph α β)) := by
        ext ⟨C, D⟩
        simp only [separationsMadeBy, Set.mem_ofPred_eq, Finset.mem_coe]
        constructor
        · rintro ⟨e, he, hmk⟩
          rcases mem_leafGraph_edgeSet_iff.1 he with rfl | ⟨x, y, hadj, rfl⟩
          · rcases (makesSeparation_leafGraph_new_iff hTD' hAB₀ hu₀).1 hmk with
              ⟨hC, hD⟩ | ⟨hC, hD⟩
            · rw [hC, hD]; exact hAB₀_mem
            · rw [hC, hD]; exact hsym (A₀, B₀) hAB₀_mem
          · have hmk' := (makesSeparation_leafGraph_old_iff hTD' hAB₀ hu₀).1 hmk
            have hmem' : (C, D) ∈ separationsMadeBy T' τ' := ⟨s(x, y), hadj, hmk'⟩
            rw [hmade'] at hmem'
            exact hsub hmem'
        · intro hCD
          by_cases h1 : (C, D) = (A₀, B₀) ∨ (C, D) = (B₀, A₀)
          · refine ⟨s(none, some u₀), ?_,
              (makesSeparation_leafGraph_new_iff hTD' hAB₀ hu₀).2 ?_⟩
            · rfl
            · rcases h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
              · exact Or.inl ⟨rfl, rfl⟩
              · exact Or.inr ⟨rfl, rfl⟩
          · have hCD' : (C, D) ∈ 𝒮' := by
              simp only [𝒮', Finset.mem_erase]
              exact ⟨fun h ↦ h1 (Or.inr h), fun h ↦ h1 (Or.inl h), hCD⟩
            have hCD_made : (C, D) ∈ separationsMadeBy T' τ' := by
              rw [hmade']
              exact hCD'
            obtain ⟨e', he', hmk'⟩ := hCD_made
            induction e' using Sym2.ind with | _ x y =>
            have hadj : T'.Adj x y := he'
            exact ⟨s(some x, some y),
              mem_leafGraph_edgeSet_iff.2 (Or.inr ⟨x, y, hadj, rfl⟩),
              (makesSeparation_leafGraph_old_iff hTD' hAB₀ hu₀).2 hmk'⟩
      refine ⟨Option ι', inferInstance, T, τ, hTD, ?_, hmade⟩
      rintro ⟨C, D⟩ hCD
      by_cases h1 : (C, D) = (A₀, B₀) ∨ (C, D) = (B₀, A₀)
      · refine ⟨s(none, some u₀),
          ⟨show (attachLeaf T' u₀).Adj none (some u₀) by simp [attachLeaf], ?_⟩, ?_⟩
        · refine (makesSeparation_leafGraph_new_iff hTD' hAB₀ hu₀).2 ?_
          rcases h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact Or.inl ⟨rfl, rfl⟩
          · exact Or.inr ⟨rfl, rfl⟩
        · rintro e ⟨he, hmk⟩
          rcases mem_leafGraph_edgeSet_iff.1 he with rfl | ⟨x, y, hadj, rfl⟩
          · rfl
          · exfalso
            have hmk' := (makesSeparation_leafGraph_old_iff hTD' hAB₀ hu₀).1 hmk
            have hmem' : (C, D) ∈ separationsMadeBy T' τ' := ⟨s(x, y), hadj, hmk'⟩
            rw [hmade'] at hmem'
            simp only [𝒮', Finset.mem_erase, Finset.mem_coe] at hmem'
            rcases h1 with h1 | h1
            · exact hmem'.2.1 h1
            · exact hmem'.1 h1
      · have hCD' : (C, D) ∈ 𝒮' := by
          simp only [𝒮', Finset.mem_erase]
          exact ⟨fun h ↦ h1 (Or.inr h), fun h ↦ h1 (Or.inl h), hCD⟩
        obtain ⟨e₀, ⟨he₀, hmk₀⟩, huniq₀⟩ := huniq' (C, D) hCD'
        induction e₀ using Sym2.ind with | _ x₀ y₀ =>
        have hadj₀ : T'.Adj x₀ y₀ := he₀
        refine ⟨s(some x₀, some y₀),
          ⟨mem_leafGraph_edgeSet_iff.2 (Or.inr ⟨x₀, y₀, hadj₀, rfl⟩),
            (makesSeparation_leafGraph_old_iff hTD' hAB₀ hu₀).2 hmk₀⟩, ?_⟩
        rintro e ⟨he, hmk⟩
        rcases mem_leafGraph_edgeSet_iff.1 he with rfl | ⟨x, y, hadj, rfl⟩
        · exfalso
          rcases (makesSeparation_leafGraph_new_iff hTD' hAB₀ hu₀).1 hmk with
            ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact h1 (Or.inl rfl)
          · exact h1 (Or.inr rfl)
        · have hmk' := (makesSeparation_leafGraph_old_iff hTD' hAB₀ hu₀).1 hmk
          have heq : s(x, y) = s(x₀, y₀) := huniq₀ s(x, y) ⟨hadj, hmk'⟩
          exact congrArg (Sym2.map some) heq

/-- Second part of **Graph Minors X, (9.1)** (page 177):
"Conversely, if $\{(A_i, B_i) : 1 \le i \le k\}$ is a laminar set of separations of $G$,
there is a tree-decomposition $(T, \tau)$ of $G$ such that* (i) *for $1 \le i \le k$, $(A_i,
B_i)$ is made by a unique edge of $T$* (ii) *for each edge $e$ of $T$, at least one of the
two separations made by $e$ equals $(A_i, B_i)$ for some $i$ ($1 \le i \le k$)." -/
theorem theorem_9_1_exists_treeDecomposition {G : Hypergraph α β}
    {𝒮 : Set (Hypergraph α β × Hypergraph α β)}
    (hsep : ∀ p ∈ 𝒮, G.IsSeparation p.1 p.2)
    (hlam : IsLaminar 𝒮) :
    ∃ (ι : Type) (_ : Fintype ι) (T : SimpleGraph ι) (τ : ι → Hypergraph α β),
      IsTreeDecomposition G T τ ∧
      (∀ p ∈ 𝒮, ∃! e : Sym2 ι, e ∈ T.edgeSet ∧ MakesSeparation T τ e p.1 p.2) ∧
      (∀ e ∈ T.edgeSet, ∃ p ∈ 𝒮, MakesSeparation T τ e p.1 p.2) ∧
      separationsMadeBy T τ = 𝒮 ∪ Prod.swap '' 𝒮 := by
  classical
  let 𝒮_symm : Set (Hypergraph α β × Hypergraph α β) := 𝒮 ∪ Prod.swap '' 𝒮
  have hsep_symm : ∀ p ∈ 𝒮_symm, G.IsSeparation p.1 p.2 := by
    rintro ⟨A, B⟩ (hp | ⟨⟨C, D⟩, hCD, heq⟩)
    · exact hsep (A, B) hp
    · simp only [Prod.swap_prod_mk, Prod.mk.injEq] at heq
      rcases heq with ⟨rfl, rfl⟩
      exact (hsep (C, D) hCD).symm
  have hlam_symm : IsLaminar 𝒮_symm := by
    rintro ⟨A₁, B₁⟩ (h1 | ⟨⟨C₁, D₁⟩, h1, heq1⟩) ⟨A₂, B₂⟩ (h2 | ⟨⟨C₂, D₂⟩, h2, heq2⟩)
    · exact hlam h1 h2
    · simp only [Prod.swap_prod_mk, Prod.mk.injEq] at heq2
      rcases heq2 with ⟨rfl, rfl⟩
      rw [separationsCross_swap_right]
      exact hlam h1 h2
    · simp only [Prod.swap_prod_mk, Prod.mk.injEq] at heq1
      rcases heq1 with ⟨rfl, rfl⟩
      rw [separationsCross_swap_left]
      exact hlam h1 h2
    · simp only [Prod.swap_prod_mk, Prod.mk.injEq] at heq1 heq2
      rcases heq1 with ⟨rfl, rfl⟩
      rcases heq2 with ⟨rfl, rfl⟩
      rw [separationsCross_swap_left, separationsCross_swap_right]
      exact hlam h1 h2
  have hfin : 𝒮_symm.Finite := finite_of_forall_isSeparation hsep_symm
  let F := hfin.toFinset
  have hF_sep : ∀ p ∈ F, G.IsSeparation p.1 p.2 :=
    fun p hp ↦ hsep_symm p (hfin.mem_toFinset.1 hp)
  have hF_sym : ∀ p ∈ F, p.swap ∈ F := by
    intro p hp
    rw [Set.Finite.mem_toFinset] at hp ⊢
    rcases hp with hp | ⟨q, hq, rfl⟩
    · exact Or.inr ⟨p, hp, rfl⟩
    · rw [Prod.swap_swap]
      exact Or.inl hq
  have hF_lam : IsLaminar (F : Set (Hypergraph α β × Hypergraph α β)) := by
    intro p₁ hp₁ p₂ hp₂
    rw [Set.Finite.coe_toFinset] at hp₁ hp₂
    exact hlam_symm hp₁ hp₂
  obtain ⟨ι, hfin_ι, T, τ, hTD, huniq, hmade⟩ :=
    exists_treeDecomposition_of_symm_laminar G F.card F rfl hF_sep hF_sym hF_lam
  rw [Set.Finite.coe_toFinset] at hmade
  refine ⟨ι, hfin_ι, T, τ, hTD, ?_, ?_, hmade⟩
  · intro p hp
    exact huniq p (hfin.mem_toFinset.2 (Or.inl hp))
  · intro e he
    induction e using Sym2.ind with | _ u v =>
    have hadj : T.Adj u v := he
    have hmem : (treeDecompSide T τ s(u, v) u, treeDecompSide T τ s(u, v) v) ∈
        separationsMadeBy T τ :=
      ⟨s(u, v), he, u, v, hadj, rfl, rfl, rfl⟩
    rw [hmade] at hmem
    rcases hmem with h1 | ⟨⟨A, B⟩, hAB, heq⟩
    · exact ⟨(treeDecompSide T τ s(u, v) u, treeDecompSide T τ s(u, v) v), h1,
        u, v, hadj, rfl, rfl, rfl⟩
    · simp only [Prod.swap_prod_mk, Prod.mk.injEq] at heq
      refine ⟨(A, B), hAB, (makesSeparation_symm).2 ?_⟩
      exact ⟨u, v, hadj, rfl, heq.1, heq.2⟩

/-- **Graph Minors X, (9.1)** (page 177):
Characterization of laminar sets of separations of a hypergraph `G` as those made by edges of a
tree-decomposition of `G`. -/
theorem theorem_9_1_proof {G : Hypergraph α β}
    {𝒮 : Set (Hypergraph α β × Hypergraph α β)}
    (hsep : ∀ p ∈ 𝒮, G.IsSeparation p.1 p.2) :
    IsLaminar 𝒮 ↔
      ∃ (ι : Type) (_ : Fintype ι) (T : SimpleGraph ι) (τ : ι → Hypergraph α β),
        IsTreeDecomposition G T τ ∧
        (∀ p ∈ 𝒮, ∃! e : Sym2 ι, e ∈ T.edgeSet ∧ MakesSeparation T τ e p.1 p.2) ∧
        (∀ e ∈ T.edgeSet, ∃ p ∈ 𝒮, MakesSeparation T τ e p.1 p.2) ∧
        separationsMadeBy T τ = 𝒮 ∪ Prod.swap '' 𝒮 := by
  constructor
  · exact theorem_9_1_exists_treeDecomposition hsep
  · rintro ⟨ι, _, T, τ, hTD, _, _, hmade⟩ p₁ hp₁ p₂ hp₂
    have hlam := theorem_9_1_laminar hTD
    rw [hmade] at hlam
    exact hlam (Or.inl hp₁) (Or.inl hp₂)

open Classical in
/-- An enumeration of unordered pairs in `L(G)`. -/
private noncomputable def sym2EquivFin (G : Hypergraph α β) :
    Sym2 (LType G) ≃ Fin (Fintype.card (Sym2 (LType G))) :=
  Fintype.equivFin (Sym2 (LType G))

open Classical in
/-- The weight function `μ(x, y) = 2 ^ enc({x, y})` on `L(G) × L(G)` in the proof of (9.2)
(page 178). -/
noncomputable def tieBreakerMu (G : Hypergraph α β) (x y : LType G) : ℕ :=
  2 ^ (sym2EquivFin G s(x, y)).val

private theorem tieBreakerMu_symm (G : Hypergraph α β) (x y : LType G) :
    tieBreakerMu G x y = tieBreakerMu G y x := by
  simp [tieBreakerMu, Sym2.eq_swap]

open Classical in
/-- Second component `N₂(A, B) = ∑_{x ∈ V(A ∩ B)} μ(x, x)` in the proof of (9.2) (page 178). -/
noncomputable def tieBreakerN2 (G A B : Hypergraph α β) : ℕ :=
  ∑ x ∈ LFinset G A ∩ LFinset G B, tieBreakerMu G x x

open Classical in
/-- Third component `N₃(A, B) = ∑_{x ∈ L(A) \ L(B), y ∈ L(B) \ L(A)} μ(x, y)` in the proof of (9.2)
(page 178). -/
noncomputable def tieBreakerN3 (G A B : Hypergraph α β) : ℕ :=
  ∑ x ∈ LFinset G A \ LFinset G B,
    ∑ y ∈ LFinset G B \ LFinset G A, tieBreakerMu G x y

/-- The concrete tie-breaker `λ(A, B) = (N₁, N₂, N₃)` in `ℕ ×ₗ (ℕ ×ₗ ℕ)` constructed in the
proof of (9.2) (page 178). -/
noncomputable def canonicalTieBreaker (G : Hypergraph α β)
    (p : Hypergraph α β × Hypergraph α β) : Lex (ℕ × Lex (ℕ × ℕ)) :=
  toLex (separationOrder p.1 p.2, toLex (tieBreakerN2 G p.1 p.2, tieBreakerN3 G p.1 p.2))

private theorem bipartite_sym2_Determine {γ : Type*} [DecidableEq γ]
    {X Y X' Y' : Finset γ} (hdisj : Disjoint X Y) (hdisj' : Disjoint X' Y')
    (hunion : X ∪ Y = X' ∪ Y')
    (hpairs : ∀ a b : γ, ((a ∈ X ∧ b ∈ Y) ∨ (b ∈ X ∧ a ∈ Y)) ↔
      ((a ∈ X' ∧ b ∈ Y') ∨ (b ∈ X' ∧ a ∈ Y'))) :
    (X' = X ∧ Y' = Y) ∨ (X' = Y ∧ Y' = X) := by
  rcases X.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · simp only [Finset.empty_union] at hunion
    rcases X'.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
    · simp only [Finset.empty_union] at hunion
      exact Or.inl ⟨rfl, hunion.symm⟩
    · have hY' : Y' = ∅ := by
        refine Finset.eq_empty_iff_forall_notMem.2 fun b hb ↦ ?_
        have := (hpairs a b).2 (Or.inl ⟨ha, hb⟩)
        simp at this
      subst hY'
      simp only [Finset.union_empty] at hunion
      exact Or.inr ⟨hunion.symm, rfl⟩
  · rcases Y.eq_empty_or_nonempty with rfl | ⟨y₀, hy₀⟩
    · simp only [Finset.union_empty] at hunion
      rcases Y'.eq_empty_or_nonempty with rfl | ⟨b, hb⟩
      · simp only [Finset.union_empty] at hunion
        exact Or.inl ⟨hunion.symm, rfl⟩
      · have hX' : X' = ∅ := by
          refine Finset.eq_empty_iff_forall_notMem.2 fun a ha ↦ ?_
          have := (hpairs a b).2 (Or.inl ⟨ha, hb⟩)
          simp at this
        subst hX'
        simp only [Finset.empty_union] at hunion
        exact Or.inr ⟨rfl, hunion.symm⟩
    · have hx₀_mem : x₀ ∈ X' ∪ Y' := hunion ▸ Finset.mem_union_left Y hx₀
      rcases Finset.mem_union.1 hx₀_mem with hx₀X' | hx₀Y'
      · left
        have hY_sub : Y ⊆ Y' := by
          intro y hy
          rcases (hpairs x₀ y).1 (Or.inl ⟨hx₀, hy⟩) with ⟨_, hyY'⟩ | ⟨_, hx₀Y'⟩
          · exact hyY'
          · exfalso; exact Finset.disjoint_left.1 hdisj' hx₀X' hx₀Y'
        have hy₀Y' : y₀ ∈ Y' := hY_sub hy₀
        have hX_sub : X ⊆ X' := by
          intro x hx
          rcases (hpairs x y₀).1 (Or.inl ⟨hx, hy₀⟩) with ⟨hxX', _⟩ | ⟨hy₀X', _⟩
          · exact hxX'
          · exfalso; exact Finset.disjoint_left.1 hdisj' hy₀X' hy₀Y'
        refine ⟨Finset.Subset.antisymm ?_ hX_sub, Finset.Subset.antisymm ?_ hY_sub⟩
        · intro x hx
          have hx_uy : x ∈ X ∪ Y := hunion.symm ▸ Finset.mem_union_left Y' hx
          rcases Finset.mem_union.1 hx_uy with hxX | hxY
          · exact hxX
          · exfalso; exact Finset.disjoint_left.1 hdisj' hx (hY_sub hxY)
        · intro y hy
          have hy_uy : y ∈ X ∪ Y := hunion.symm ▸ Finset.mem_union_right X' hy
          rcases Finset.mem_union.1 hy_uy with hyX | hyY
          · exfalso; exact Finset.disjoint_left.1 hdisj' (hX_sub hyX) hy
          · exact hyY
      · right
        have hY_sub : Y ⊆ X' := by
          intro y hy
          rcases (hpairs x₀ y).1 (Or.inl ⟨hx₀, hy⟩) with ⟨hx₀X', _⟩ | ⟨hyX', _⟩
          · exfalso; exact Finset.disjoint_left.1 hdisj' hx₀X' hx₀Y'
          · exact hyX'
        have hy₀X' : y₀ ∈ X' := hY_sub hy₀
        have hX_sub : X ⊆ Y' := by
          intro x hx
          rcases (hpairs x y₀).1 (Or.inl ⟨hx, hy₀⟩) with ⟨_, hy₀Y'⟩ | ⟨_, hxY'⟩
          · exfalso; exact Finset.disjoint_left.1 hdisj' hy₀X' hy₀Y'
          · exact hxY'
        refine ⟨Finset.Subset.antisymm ?_ hY_sub, Finset.Subset.antisymm ?_ hX_sub⟩
        · intro x hx
          have hx_uy : x ∈ X ∪ Y := hunion.symm ▸ Finset.mem_union_left Y' hx
          rcases Finset.mem_union.1 hx_uy with hxX | hxY
          · exfalso; exact Finset.disjoint_left.1 hdisj' hx (hX_sub hxX)
          · exact hxY
        · intro y hy
          have hy_uy : y ∈ X ∪ Y := hunion.symm ▸ Finset.mem_union_right X' hy
          rcases Finset.mem_union.1 hy_uy with hyX | hyY
          · exact hyX
          · exfalso; exact Finset.disjoint_left.1 hdisj' (hY_sub hyY) hy

/-- Claim (1) in the proof of **Graph Minors X, (9.2)** (page 178):
"If $(A, B)$ and $(A', B')$ are separations of $G$ with the same $\lambda$-order then $(A',
B') = (A, B)$ or $(B, A)$." -/
theorem theorem_9_2_claim_1 {G A B A' B' : Hypergraph α β}
    (hAB : G.IsSeparation A B) (hA'B' : G.IsSeparation A' B')
    (hlam : canonicalTieBreaker G (A, B) = canonicalTieBreaker G (A', B')) :
    (A' = A ∧ B' = B) ∨ (A' = B ∧ B' = A) := by
  classical
  have hN2 : tieBreakerN2 G A B = tieBreakerN2 G A' B' := by
    simpa [canonicalTieBreaker] using congrArg (fun x ↦ (ofLex (ofLex x).2).1) hlam
  have hN3 : tieBreakerN3 G A B = tieBreakerN3 G A' B' := by
    simpa [canonicalTieBreaker] using congrArg (fun x ↦ (ofLex (ofLex x).2).2) hlam
  let Z := LFinset G A ∩ LFinset G B
  let Z' := LFinset G A' ∩ LFinset G B'
  have hZ_eq : Z = Z' := by
    let diag : LType G ↪ Sym2 (LType G) :=
      ⟨fun x ↦ s(x, x), fun x y h ↦ by
        rcases Sym2.eq_iff.1 h with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> rfl⟩
    have hsum1 : ∀ S : Finset (LType G),
        ∑ s ∈ S.map diag, 2 ^ (sym2EquivFin G s).val = ∑ x ∈ S, tieBreakerMu G x x :=
      fun S ↦ Finset.sum_map S diag (fun s ↦ 2 ^ (sym2EquivFin G s).val)
    have hmap : Z.map diag = Z'.map diag :=
      eq_of_sum_two_pow_equiv (sym2EquivFin G) (by rw [hsum1 Z, hsum1 Z']; exact hN2)
    exact Finset.map_injective diag hmap
  let X := LFinset G A \ LFinset G B
  let Y := LFinset G B \ LFinset G A
  let X' := LFinset G A' \ LFinset G B'
  let Y' := LFinset G B' \ LFinset G A'
  have hdisj : Disjoint X Y := disjoint_sdiff_sdiff
  have hdisj' : Disjoint X' Y' := disjoint_sdiff_sdiff
  have hN3_image : ∀ (P Q : Finset (LType G)), Disjoint P Q →
      ∑ x ∈ P, ∑ y ∈ Q, tieBreakerMu G x y =
        ∑ s ∈ (P ×ˢ Q).image (fun p ↦ s(p.1, p.2)), 2 ^ (sym2EquivFin G s).val := by
    intro P Q hPQ
    rw [← Finset.sum_product', Finset.sum_image]
    · rfl
    · intro ⟨x₁, y₁⟩ h1 ⟨x₂, y₂⟩ h2 heq
      simp only [Finset.mem_coe, Finset.mem_product] at h1 h2
      rcases Sym2.eq_iff.1 heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rfl
      · exfalso; exact Finset.disjoint_left.1 hPQ h1.1 h2.2
  have himg_eq : (X ×ˢ Y).image (fun p ↦ s(p.1, p.2)) =
      (X' ×ˢ Y').image (fun p ↦ s(p.1, p.2)) := by
    apply eq_of_sum_two_pow_equiv (sym2EquivFin G)
    rw [← hN3_image X Y hdisj, ← hN3_image X' Y' hdisj']
    exact hN3
  have hpairs : ∀ a b : LType G, ((a ∈ X ∧ b ∈ Y) ∨ (b ∈ X ∧ a ∈ Y)) ↔
      ((a ∈ X' ∧ b ∈ Y') ∨ (b ∈ X' ∧ a ∈ Y')) := by
    intro a b
    have hmem : ∀ (P Q : Finset (LType G)),
        s(a, b) ∈ (P ×ˢ Q).image (fun p ↦ s(p.1, p.2)) ↔
          ((a ∈ P ∧ b ∈ Q) ∨ (b ∈ P ∧ a ∈ Q)) := by
      intro P Q
      simp only [Finset.mem_image, Finset.mem_product, Prod.exists, Sym2.eq_iff]
      constructor
      · rintro ⟨x, y, ⟨hx, hy⟩, ⟨rfl, rfl⟩ | ⟨h1, h2⟩⟩
        · exact Or.inl ⟨hx, hy⟩
        · subst h1 h2; exact Or.inr ⟨hx, hy⟩
      · rintro (⟨ha, hb⟩ | ⟨hb, ha⟩)
        · exact ⟨a, b, ⟨ha, hb⟩, Or.inl ⟨rfl, rfl⟩⟩
        · exact ⟨b, a, ⟨hb, ha⟩, Or.inr ⟨rfl, rfl⟩⟩
    rw [← hmem X Y, ← hmem X' Y', himg_eq]
  have hunion_Z : ∀ {P Q : Hypergraph α β}, G.IsSeparation P Q →
      (LFinset G P \ LFinset G Q) ∪ (LFinset G Q \ LFinset G P) =
        Finset.univ \ (LFinset G P ∩ LFinset G Q) := by
    intro P Q hPQ
    have hPQ_univ : LFinset G P ∪ LFinset G Q = Finset.univ := by
      rw [← LFinset_union, hPQ.union_eq, LFinset_self]
    ext x
    have hx_u : x ∈ LFinset G P ∪ LFinset G Q := hPQ_univ.symm ▸ Finset.mem_univ x
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter,
      Finset.mem_univ, true_and] at hx_u ⊢
    rcases hx_u with hxP | hxQ <;> tauto
  have hunion : X ∪ Y = X' ∪ Y' := by
    change (LFinset G A \ LFinset G B) ∪ (LFinset G B \ LFinset G A) =
      (LFinset G A' \ LFinset G B') ∪ (LFinset G B' \ LFinset G A')
    rw [hunion_Z hAB, hunion_Z hA'B']
    exact congrArg (Finset.univ \ ·) hZ_eq
  rcases bipartite_sym2_Determine hdisj hdisj' hunion hpairs with ⟨hX, hY⟩ | ⟨hX, hY⟩
  · left
    have hLA : LFinset G A' = LFinset G A := by
      rw [← Finset.sdiff_union_inter (LFinset G A') (LFinset G B'),
        ← Finset.sdiff_union_inter (LFinset G A) (LFinset G B)]
      exact congrArg₂ (· ∪ ·) hX hZ_eq.symm
    have hLB : LFinset G B' = LFinset G B := by
      rw [← Finset.sdiff_union_inter (LFinset G B') (LFinset G A'), Finset.inter_comm
        (LFinset G B'),
        ← Finset.sdiff_union_inter (LFinset G B) (LFinset G A), Finset.inter_comm (LFinset G B)]
      exact congrArg₂ (· ∪ ·) hY hZ_eq.symm
    exact ⟨eq_of_LFinset_eq hA'B'.left_le hAB.left_le hLA,
      eq_of_LFinset_eq hA'B'.right_le hAB.right_le hLB⟩
  · right
    have hLA : LFinset G A' = LFinset G B := by
      rw [← Finset.sdiff_union_inter (LFinset G A') (LFinset G B'),
        ← Finset.sdiff_union_inter (LFinset G B) (LFinset G A), Finset.inter_comm (LFinset G B)]
      exact congrArg₂ (· ∪ ·) hX hZ_eq.symm
    have hLB : LFinset G B' = LFinset G A := by
      rw [← Finset.sdiff_union_inter (LFinset G B') (LFinset G A'), Finset.inter_comm
        (LFinset G B'),
        ← Finset.sdiff_union_inter (LFinset G A) (LFinset G B)]
      exact congrArg₂ (· ∪ ·) hY hZ_eq.symm
    exact ⟨eq_of_LFinset_eq hA'B'.left_le hAB.right_le hLA,
      eq_of_LFinset_eq hA'B'.right_le hAB.left_le hLB⟩

private theorem sum_finset_eq_sum_univ {γ : Type*} [Fintype γ] [DecidableEq γ]
    (S : Finset γ) (f : γ → ℕ) :
    ∑ x ∈ S, f x = ∑ x : γ, if x ∈ S then f x else 0 := by
  rw [← Finset.sum_filter]
  congr 1
  ext x
  simp

private theorem indicator_add_eq {m : ℕ} {pa pb pc pd : Prop}
    [Decidable pa] [Decidable pb] [Decidable pc] [Decidable pd]
    (hxAB : pa ∨ pb) (hxCD : pc ∨ pd) :
    (if (pa ∨ pc) ∧ (pb ∧ pd) then m else 0) +
      (if (pa ∧ pc) ∧ (pb ∨ pd) then m else 0) =
    (if pa ∧ pb then m else 0) + (if pc ∧ pd then m else 0) := by
  rcases hxAB with hpa | hpb <;> rcases hxCD with hpc | hpd <;>
    by_cases hpa' : pa <;> by_cases hpb' : pb <;>
    by_cases hpc' : pc <;> by_cases hpd' : pd <;>
    simp_all

private theorem indicator_add_le {m : ℕ} {pa pb pc pd qa qb qc qd : Prop}
    [Decidable pa] [Decidable pb] [Decidable pc] [Decidable pd]
    [Decidable qa] [Decidable qb] [Decidable qc] [Decidable qd]
    (hxAB : pa ∨ pb) (hxCD : pc ∨ pd) (hyAB : qa ∨ qb) (hyCD : qc ∨ qd) :
    (if ((pa ∨ pc) ∧ ¬ (pb ∧ pd)) ∧ ((qb ∧ qd) ∧ ¬ (qa ∨ qc)) then m else 0) +
      (if ((pa ∧ pc) ∧ ¬ (pb ∨ pd)) ∧ ((qb ∨ qd) ∧ ¬ (qa ∧ qc)) then m else 0) ≤
    (if (pa ∧ ¬ pb) ∧ (qb ∧ ¬ qa) then m else 0) +
      (if (pc ∧ ¬ pd) ∧ (qd ∧ ¬ qc) then m else 0) := by
  by_cases h1 : ((pa ∨ pc) ∧ ¬ (pb ∧ pd)) ∧ ((qb ∧ qd) ∧ ¬ (qa ∨ qc)) <;>
    by_cases h2 : ((pa ∧ pc) ∧ ¬ (pb ∨ pd)) ∧ ((qb ∨ qd) ∧ ¬ (qa ∧ qc))
  · have hr1 : (pa ∧ ¬ pb) ∧ (qb ∧ ¬ qa) :=
      ⟨⟨h2.1.1.1, fun h ↦ h2.1.2 (Or.inl h)⟩, ⟨h1.2.1.1, fun h ↦ h1.2.2 (Or.inl h)⟩⟩
    have hr2 : (pc ∧ ¬ pd) ∧ (qd ∧ ¬ qc) :=
      ⟨⟨h2.1.1.2, fun h ↦ h2.1.2 (Or.inr h)⟩, ⟨h1.2.1.2, fun h ↦ h1.2.2 (Or.inr h)⟩⟩
    rw [ite_eq_left_iff.2 fun h ↦ (h h1).elim, ite_eq_left_iff.2 fun h ↦ (h h2).elim,
      ite_eq_left_iff.2 fun h ↦ (h hr1).elim, ite_eq_left_iff.2 fun h ↦ (h hr2).elim]
  · rw [ite_eq_left_iff.2 fun h ↦ (h h1).elim, ite_eq_right_iff.2 fun h ↦ (h2 h).elim, add_zero]
    by_cases hpb : pb
    · have hpd : ¬ pd := fun h ↦ h1.1.2 ⟨hpb, h⟩
      have hpc : pc := hxCD.resolve_right hpd
      have hr2 : (pc ∧ ¬ pd) ∧ (qd ∧ ¬ qc) :=
        ⟨⟨hpc, hpd⟩, ⟨h1.2.1.2, fun h ↦ h1.2.2 (Or.inr h)⟩⟩
      rw [ite_eq_left_iff.2 fun h ↦ (h hr2).elim]
      exact Nat.le_add_left _ _
    · have hpa : pa := hxAB.resolve_right hpb
      have hr1 : (pa ∧ ¬ pb) ∧ (qb ∧ ¬ qa) :=
        ⟨⟨hpa, hpb⟩, ⟨h1.2.1.1, fun h ↦ h1.2.2 (Or.inl h)⟩⟩
      rw [ite_eq_left_iff.2 fun h ↦ (h hr1).elim]
      exact Nat.le_add_right _ _
  · rw [ite_eq_right_iff.2 fun h ↦ (h1 h).elim, ite_eq_left_iff.2 fun h ↦ (h h2).elim, zero_add]
    by_cases hqa : qa
    · have hqc : ¬ qc := fun h ↦ h2.2.2 ⟨hqa, h⟩
      have hqd : qd := hyCD.resolve_left hqc
      have hr2 : (pc ∧ ¬ pd) ∧ (qd ∧ ¬ qc) :=
        ⟨⟨h2.1.1.2, fun h ↦ h2.1.2 (Or.inr h)⟩, ⟨hqd, hqc⟩⟩
      rw [ite_eq_left_iff.2 fun h ↦ (h hr2).elim]
      exact Nat.le_add_left _ _
    · have hqb : qb := hyAB.resolve_left hqa
      have hr1 : (pa ∧ ¬ pb) ∧ (qb ∧ ¬ qa) :=
        ⟨⟨h2.1.1.1, fun h ↦ h2.1.2 (Or.inl h)⟩, ⟨hqb, hqa⟩⟩
      rw [ite_eq_left_iff.2 fun h ↦ (h hr1).elim]
      exact Nat.le_add_right _ _
  · rw [ite_eq_right_iff.2 fun h ↦ (h1 h).elim, ite_eq_right_iff.2 fun h ↦ (h2 h).elim, add_zero]
    exact Nat.zero_le _

/-- Claim (2) in the proof of **Graph Minors X, (9.2)** (page 179):
"Let $(A, B)$, $(C, D)$ be separations of $G$. Then so are $(A \cup C, B \cap D)$, $(A \cap
C, B \cup D)$, and the sum of their $\lambda$-orders is at most the sum of the
$\lambda$-orders of $(A, B)$, $(C, D)$." -/
theorem theorem_9_2_claim_2 {G A B C D : Hypergraph α β}
    (hAB : G.IsSeparation A B) (hCD : G.IsSeparation C D) :
    separationOrder (A ∪ C) (B ∩ D) + separationOrder (A ∩ C) (B ∪ D) =
        separationOrder A B + separationOrder C D ∧
      tieBreakerN2 G (A ∪ C) (B ∩ D) + tieBreakerN2 G (A ∩ C) (B ∪ D) =
        tieBreakerN2 G A B + tieBreakerN2 G C D ∧
      tieBreakerN3 G (A ∪ C) (B ∩ D) + tieBreakerN3 G (A ∩ C) (B ∪ D) ≤
        tieBreakerN3 G A B + tieBreakerN3 G C D := by
  classical
  have hAB_univ : ∀ x : LType G, x ∈ LFinset G A ∨ x ∈ LFinset G B := by
    intro x
    have : x ∈ LFinset G A ∪ LFinset G B := by
      rw [← LFinset_union, hAB.union_eq, LFinset_self]
      exact Finset.mem_univ x
    exact Finset.mem_union.1 this
  have hCD_univ : ∀ x : LType G, x ∈ LFinset G C ∨ x ∈ LFinset G D := by
    intro x
    have : x ∈ LFinset G C ∪ LFinset G D := by
      rw [← LFinset_union, hCD.union_eq, LFinset_self]
      exact Finset.mem_univ x
    exact Finset.mem_union.1 this
  refine ⟨(add_comm _ _).trans (separationOrder_add_separationOrder hAB hCD).symm, ?_, ?_⟩
  · have hN2_rew : ∀ P Q : Hypergraph α β,
        tieBreakerN2 G P Q =
          ∑ x : LType G,
            if x ∈ LFinset G P ∩ LFinset G Q then tieBreakerMu G x x else 0 :=
      fun P Q ↦ sum_finset_eq_sum_univ (LFinset G P ∩ LFinset G Q) (fun x ↦ tieBreakerMu G x x)
    rw [hN2_rew, hN2_rew, hN2_rew, hN2_rew, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    simp only [LFinset_union, LFinset_inter, Finset.mem_union, Finset.mem_inter]
    exact indicator_add_eq (hAB_univ x) (hCD_univ x)
  · have hN3_rew : ∀ P Q : Hypergraph α β,
        tieBreakerN3 G P Q =
          ∑ x : LType G, ∑ y : LType G,
            if (x ∈ LFinset G P \ LFinset G Q ∧ y ∈ LFinset G Q \ LFinset G P) then
              tieBreakerMu G x y
            else 0 := by
      intro P Q
      unfold tieBreakerN3
      rw [sum_finset_eq_sum_univ]
      refine Finset.sum_congr rfl fun x _ ↦ ?_
      rw [sum_finset_eq_sum_univ]
      by_cases hx : x ∈ LFinset G P \ LFinset G Q <;> simp [hx]
    rw [hN3_rew, hN3_rew, hN3_rew, hN3_rew, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun x _ ↦ ?_
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun y _ ↦ ?_
    simp only [LFinset_union, LFinset_inter, Finset.mem_sdiff, Finset.mem_union, Finset.mem_inter]
    exact indicator_add_le (hAB_univ x) (hCD_univ x) (hAB_univ y) (hCD_univ y)

/-- `canonicalTieBreaker G` is a tie-breaker in `G`. -/
theorem isTieBreaker_canonicalTieBreaker (G : Hypergraph α β) :
    IsTieBreaker G (canonicalTieBreaker G) where
  axiom1 {A B C D} hAB hCD := by
    constructor
    · intro hlam
      rcases theorem_9_2_claim_1 hCD hAB hlam.symm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨rfl, rfl⟩
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · rfl
      · classical
        have h1 : separationOrder B A = separationOrder A B := by
          simp [separationOrder, inter_comm]
        have h2 : tieBreakerN2 G B A = tieBreakerN2 G A B := by
          simp [tieBreakerN2, Finset.inter_comm]
        have h3 : tieBreakerN3 G B A = tieBreakerN3 G A B := by
          unfold tieBreakerN3
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun x _ ↦ Finset.sum_congr rfl fun y _ ↦ ?_
          exact tieBreakerMu_symm G y x
        simp [canonicalTieBreaker, h1, h2, h3]
  axiom2 {A B C D} hAB hCD := by
    obtain ⟨h1, h2, h3⟩ := theorem_9_2_claim_2 hAB hCD
    by_contra! h
    rcases h with ⟨hlt1, hle2⟩
    rw [Prod.Lex.lt_iff] at hlt1
    rw [Prod.Lex.le_iff] at hle2
    simp only [canonicalTieBreaker, ofLex_toLex] at hlt1 hle2
    rcases hlt1 with h1_lt | ⟨h1_eq, hlt1'⟩
    · rcases hle2 with h2_lt | ⟨h2_eq, _⟩ <;> omega
    · rcases hle2 with h2_lt | ⟨_, hle2'⟩
      · omega
      · rw [Prod.Lex.lt_iff] at hlt1'
        rw [Prod.Lex.le_iff] at hle2'
        simp only [ofLex_toLex] at hlt1' hle2'
        rcases hlt1' with h2_lt | ⟨h2_eq', h3_lt⟩
        · rcases hle2' with h2_lt' | ⟨h2_eq'', _⟩ <;> omega
        · rcases hle2' with h2_lt' | ⟨_, h3_le⟩ <;> omega
  axiom3 {_ _ _ _} _ _ hord := Prod.Lex.left _ _ hord

/-- **Graph Minors X, (9.2)** (page 178):
"In every hypergraph there is a tie-breaker." -/
theorem theorem_9_2_proof (G : Hypergraph α β) :
    ∃ (lam : Hypergraph α β × Hypergraph α β → Lex (ℕ × Lex (ℕ × ℕ))),
      IsTieBreaker G lam :=
  ⟨canonicalTieBreaker G, isTieBreaker_canonicalTieBreaker G⟩

/-! ## Proof of (9.3) and (9.4) -/

/-- A tie-breaker assigns the same `λ`-order to `(A, B)` and `(B, A)`. -/
theorem IsTieBreaker.lam_swap {Λ : Type*} [LinearOrder Λ] {G : Hypergraph α β}
    {lam : Hypergraph α β × Hypergraph α β → Λ} (hTB : IsTieBreaker G lam)
    {A B : Hypergraph α β} (hAB : G.IsSeparation A B) :
    lam (B, A) = lam (A, B) :=
  (hTB.axiom1 hAB.symm hAB).2 (Or.inr ⟨rfl, rfl⟩)

/-- **Graph Minors X, (9.3)** (page 179):
"Let $\lambda$ be a tie-breaker in a hypergraph $G$, and let $(A, B)$, $(C, D)$ be
separations of $G$. Then either* (i) *$(A \cup C, B \cap D)$ has smaller $\lambda$-order
than $(A, B)$, or* (ii) *$(A \cap C, B \cup D)$ has smaller $\lambda$-order than $(C, D)$,
or* (iii) *$C \subseteq A$ and $B \subseteq D$, or* (iv) *$B = C = G$ and $A = D$ and $E(A)
= \emptyset$." -/
theorem theorem_9_3_proof {Λ : Type*} [LinearOrder Λ] {G : Hypergraph α β}
    {lam : Hypergraph α β × Hypergraph α β → Λ} (hTB : IsTieBreaker G lam)
    {A B C D : Hypergraph α β} (hAB : G.IsSeparation A B) (hCD : G.IsSeparation C D) :
    HasSmallerLambdaOrder lam (A ∪ C) (B ∩ D) A B ∨
      HasSmallerLambdaOrder lam (A ∩ C) (B ∪ D) C D ∨
      (C ≤ A ∧ B ≤ D) ∨
      (B = G ∧ C = G ∧ A = D ∧ A.edgeSet = ∅) := by
  unfold HasSmallerLambdaOrder
  rcases hTB.axiom2 hAB hCD with hle1 | hlt2
  · rcases lt_or_eq_of_le hle1 with hlt1 | heq1
    · exact Or.inl hlt1
    · have hsep_union : G.IsSeparation (A ∪ C) (B ∩ D) := hAB.union_inter hCD
      rcases (hTB.axiom1 hsep_union hAB).1 heq1 with ⟨hAC_A, hBD_B⟩ | ⟨hAC_B, hBD_A⟩
      · right; right; left
        exact ⟨hAC_A ▸ le_union_right hAB.left_le hCD.left_le,
          hBD_B ▸ inter_le_right hAB.right_le hCD.right_le⟩
      · have hA_le_B : A ≤ B := hBD_A ▸ inter_le_left hAB.right_le hCD.right_le
        have hB_eq_G : B = G := by
          rw [← hAB.union_eq]
          exact eq_of_le_of_vertexSet_eq_of_edgeSet_eq
            hAB.right_le (union_le hAB.left_le hAB.right_le)
            (Set.union_eq_right.2 hA_le_B.vertexSet_subset).symm
            (Set.union_eq_right.2 hA_le_B.edgeSet_subset).symm
        have hA_eq_D : A = D := by
          rw [← hBD_A, hB_eq_G]
          exact eq_of_le_of_vertexSet_eq_of_edgeSet_eq
            (inter_le le_rfl hCD.right_le) hCD.right_le
            (Set.inter_eq_right.2 hCD.right_le.vertexSet_subset)
            (Set.inter_eq_right.2 hCD.right_le.edgeSet_subset)
        have hsep_inter : G.IsSeparation (A ∩ C) (B ∪ D) :=
          (hAB.symm.union_inter hCD.symm).symm
        have hlam_DB_CA : lam (D ∪ B, C ∩ A) = lam (A ∩ C, B ∪ D) := by
          rw [union_comm D B, inter_comm C A]
          exact hTB.lam_swap hsep_inter
        have hlam_DC : lam (D, C) = lam (C, D) := hTB.lam_swap hCD
        have hlam_DB_CA_2 : lam (D ∩ B, C ∪ A) = lam (A ∪ C, B ∩ D) := by
          rw [inter_comm D B, union_comm C A]
          exact hTB.lam_swap hsep_union
        have hlam_BA : lam (B, A) = lam (A, B) := hTB.lam_swap hAB
        rcases hTB.axiom2 hCD.symm hAB.symm with hle2 | hlt1'
        · rw [hlam_DB_CA, hlam_DC] at hle2
          rcases lt_or_eq_of_le hle2 with hlt2 | heq2
          · exact Or.inr (Or.inl hlt2)
          · rcases (hTB.axiom1 hsep_inter hCD).1 heq2 with ⟨hAC_C, hBD_D⟩ | ⟨hAC_D, hBD_C⟩
            · right; right; left
              exact ⟨hAC_C ▸ inter_le_left hAB.left_le hCD.left_le,
                hBD_D ▸ le_union_left hAB.right_le hCD.right_le⟩
            · right; right; right
              have hC_eq_G : C = G := by
                rw [← hBD_C, hB_eq_G]
                exact eq_of_le_of_vertexSet_eq_of_edgeSet_eq
                  (union_le le_rfl hCD.right_le) le_rfl
                  (Set.union_eq_left.2 hCD.right_le.vertexSet_subset)
                  (Set.union_eq_left.2 hCD.right_le.edgeSet_subset)
              have hEA_empty : A.edgeSet = ∅ := by
                have := hAB.edgeSet_inter_eq
                rwa [inter_edgeSet, hB_eq_G,
                  Set.inter_eq_left.2 hAB.left_le.edgeSet_subset] at this
              exact ⟨hB_eq_G, hC_eq_G, hA_eq_D, hEA_empty⟩
        · rw [hlam_DB_CA_2, hlam_BA] at hlt1'
          exact Or.inl hlt1'
  · exact Or.inr (Or.inl hlt2)

/-- Helper for (9.4) when `(A ∩ C, B ∪ D)` has `λ`-order at most those of `(A ∩ D, B ∪ C)` and
`(B ∩ C, A ∪ D)`. -/
private theorem theorem_9_4_wlog {Λ : Type*} [LinearOrder Λ] {G : Hypergraph α β}
    {lam : Hypergraph α β × Hypergraph α β → Λ} (hTB : IsTieBreaker G lam)
    {A B C D : Hypergraph α β}
    (hAB : IsLambdaRobust G lam A B) (hCD : IsLambdaRobust G lam C D)
    (h12 : lam (A ∩ C, B ∪ D) ≤ lam (A ∩ D, B ∪ C))
    (h13 : lam (A ∩ C, B ∪ D) ≤ lam (B ∩ C, A ∪ D)) :
    ¬ SeparationsCross A B C D := by
  have hsepA : A.IsSeparation (A ∩ C) (A ∩ D) :=
    hCD.1.inter_left hAB.1.left_le
  have hB_AD : B ∪ (A ∩ D) = B ∪ D := by
    refine eq_of_le_of_vertexSet_eq_of_edgeSet_eq
      (union_le hAB.1.right_le (inter_le hAB.1.left_le hCD.1.right_le))
      (union_le hAB.1.right_le hCD.1.right_le) ?_ ?_
    · ext v
      simp only [union_vertexSet, inter_vertexSet, Set.mem_union, Set.mem_inter_iff]
      refine ⟨by tauto, fun h ↦ h.elim Or.inl fun hvD ↦ ?_⟩
      have hvAB : v ∈ A.vertexSet ∪ B.vertexSet :=
        hAB.1.vertexSet_union.symm ▸ hCD.1.right_le.vertexSet_subset hvD
      rcases hvAB with hvA | hvB
      · exact Or.inr ⟨hvA, hvD⟩
      · exact Or.inl hvB
    · ext e
      simp only [union_edgeSet, inter_edgeSet, Set.mem_union, Set.mem_inter_iff]
      refine ⟨by tauto, fun h ↦ h.elim Or.inl fun heD ↦ ?_⟩
      have heAB : e ∈ A.edgeSet ∪ B.edgeSet :=
        hAB.1.edgeSet_union.symm ▸ hCD.1.right_le.edgeSet_subset heD
      rcases heAB with heA | heB
      · exact Or.inr ⟨heA, heD⟩
      · exact Or.inl heB
  have hB_AC : B ∪ (A ∩ C) = B ∪ C := by
    refine eq_of_le_of_vertexSet_eq_of_edgeSet_eq
      (union_le hAB.1.right_le (inter_le hAB.1.left_le hCD.1.left_le))
      (union_le hAB.1.right_le hCD.1.left_le) ?_ ?_
    · ext v
      simp only [union_vertexSet, inter_vertexSet, Set.mem_union, Set.mem_inter_iff]
      refine ⟨by tauto, fun h ↦ h.elim Or.inl fun hvC ↦ ?_⟩
      have hvAB : v ∈ A.vertexSet ∪ B.vertexSet :=
        hAB.1.vertexSet_union.symm ▸ hCD.1.left_le.vertexSet_subset hvC
      rcases hvAB with hvA | hvB
      · exact Or.inr ⟨hvA, hvC⟩
      · exact Or.inl hvB
    · ext e
      simp only [union_edgeSet, inter_edgeSet, Set.mem_union, Set.mem_inter_iff]
      refine ⟨by tauto, fun h ↦ h.elim Or.inl fun heC ↦ ?_⟩
      have heAB : e ∈ A.edgeSet ∪ B.edgeSet :=
        hAB.1.edgeSet_union.symm ▸ hCD.1.left_le.edgeSet_subset heC
      rcases heAB with heA | heB
      · exact Or.inr ⟨heA, heC⟩
      · exact Or.inl heB
  have hrobA : lam (A, B) ≤ lam (A ∩ D, B ∪ C) := by
    rcases hAB.2 hsepA with h | h
    · rw [hB_AD] at h
      exact h.trans h12
    · rwa [hB_AC] at h
  have hsepC : C.IsSeparation (C ∩ A) (C ∩ B) :=
    hAB.1.inter_left hCD.1.left_le
  have hD_CB : D ∪ (C ∩ B) = B ∪ D := by
    rw [union_comm B D, inter_comm C B]
    refine eq_of_le_of_vertexSet_eq_of_edgeSet_eq
      (union_le hCD.1.right_le (inter_le hAB.1.right_le hCD.1.left_le))
      (union_le hCD.1.right_le hAB.1.right_le) ?_ ?_
    · ext v
      simp only [union_vertexSet, inter_vertexSet, Set.mem_union, Set.mem_inter_iff]
      refine ⟨by tauto, fun h ↦ h.elim Or.inl fun hvB ↦ ?_⟩
      have hvCD : v ∈ C.vertexSet ∪ D.vertexSet :=
        hCD.1.vertexSet_union.symm ▸ hAB.1.right_le.vertexSet_subset hvB
      rcases hvCD with hvC | hvD
      · exact Or.inr ⟨hvB, hvC⟩
      · exact Or.inl hvD
    · ext e
      simp only [union_edgeSet, inter_edgeSet, Set.mem_union, Set.mem_inter_iff]
      refine ⟨by tauto, fun h ↦ h.elim Or.inl fun heB ↦ ?_⟩
      have heCD : e ∈ C.edgeSet ∪ D.edgeSet :=
        hCD.1.edgeSet_union.symm ▸ hAB.1.right_le.edgeSet_subset heB
      rcases heCD with heC | heD
      · exact Or.inr ⟨heB, heC⟩
      · exact Or.inl heD
  have hD_CA : D ∪ (C ∩ A) = A ∪ D := by
    rw [union_comm A D, inter_comm C A]
    refine eq_of_le_of_vertexSet_eq_of_edgeSet_eq
      (union_le hCD.1.right_le (inter_le hAB.1.left_le hCD.1.left_le))
      (union_le hCD.1.right_le hAB.1.left_le) ?_ ?_
    · ext v
      simp only [union_vertexSet, inter_vertexSet, Set.mem_union, Set.mem_inter_iff]
      refine ⟨by tauto, fun h ↦ h.elim Or.inl fun hvA ↦ ?_⟩
      have hvCD : v ∈ C.vertexSet ∪ D.vertexSet :=
        hCD.1.vertexSet_union.symm ▸ hAB.1.left_le.vertexSet_subset hvA
      rcases hvCD with hvC | hvD
      · exact Or.inr ⟨hvA, hvC⟩
      · exact Or.inl hvD
    · ext e
      simp only [union_edgeSet, inter_edgeSet, Set.mem_union, Set.mem_inter_iff]
      refine ⟨by tauto, fun h ↦ h.elim Or.inl fun heA ↦ ?_⟩
      have heCD : e ∈ C.edgeSet ∪ D.edgeSet :=
        hCD.1.edgeSet_union.symm ▸ hAB.1.left_le.edgeSet_subset heA
      rcases heCD with heC | heD
      · exact Or.inr ⟨heA, heC⟩
      · exact Or.inl heD
  have hrobC : lam (C, D) ≤ lam (B ∩ C, A ∪ D) := by
    rcases hCD.2 hsepC with h | h
    · rw [inter_comm C A, hD_CB] at h
      exact h.trans h13
    · rwa [inter_comm C B, hD_CA] at h
  rcases theorem_9_3_proof hTB hAB.1.symm hCD.1 with h1 | h2 | ⟨hCB, hAD⟩ | ⟨hAG, hCG, hBD, _⟩
  · exfalso
    unfold HasSmallerLambdaOrder at h1
    have hsep_BC_AD : G.IsSeparation (B ∪ C) (A ∩ D) := hAB.1.symm.union_inter hCD.1
    rw [← hTB.lam_swap hsep_BC_AD, hTB.lam_swap hAB.1] at h1
    exact not_lt_of_ge hrobA h1
  · exfalso
    unfold HasSmallerLambdaOrder at h2
    exact not_lt_of_ge hrobC h2
  · unfold SeparationsCross
    rw [not_not]
    exact Or.inr (Or.inl ⟨hAD, hCB⟩)
  · unfold SeparationsCross
    rw [not_not]
    refine Or.inl ⟨?_, ?_⟩
    · rw [hAG, hCG]
    · rw [hBD]

/-- **Graph Minors X, (9.4)** (page 180):
"Let $(A, B)$, $(C, D)$ be doubly $\lambda$-robust separations of $G$. Then $(A, B)$ and $(C,
D)$ do not cross." -/
theorem theorem_9_4_proof {Λ : Type*} [LinearOrder Λ] {G : Hypergraph α β}
    {lam : Hypergraph α β × Hypergraph α β → Λ} (hTB : IsTieBreaker G lam)
    {A B C D : Hypergraph α β}
    (hAB : IsDoublyLambdaRobust G lam A B) (hCD : IsDoublyLambdaRobust G lam C D) :
    ¬ SeparationsCross A B C D := by
  let vAC := lam (A ∩ C, B ∪ D)
  let vAD := lam (A ∩ D, B ∪ C)
  let vBC := lam (B ∩ C, A ∪ D)
  let vBD := lam (B ∩ D, A ∪ C)
  rcases le_total (min vAC vAD) (min vBC vBD) with h1 | h2
  · rcases le_total vAC vAD with hAC | hAD
    · have hmin : min vAC vAD = vAC := min_eq_left hAC
      have hBC : vAC ≤ vBC := by
        rw [← hmin]
        exact h1.trans (min_le_left _ _)
      exact theorem_9_4_wlog hTB hAB.1 hCD.1 hAC hBC
    · have hmin : min vAC vAD = vAD := min_eq_right hAD
      have hBD : vAD ≤ vBD := by
        rw [← hmin]
        exact h1.trans (min_le_right _ _)
      rw [← separationsCross_swap_right]
      exact theorem_9_4_wlog hTB hAB.1 hCD.2 hAD (by simpa [union_comm] using hBD)
  · rcases le_total vBC vBD with hBC | hBD
    · have hmin : min vBC vBD = vBC := min_eq_left hBC
      have hAC : vBC ≤ vAC := by
        rw [← hmin]
        exact h2.trans (min_le_left _ _)
      rw [← separationsCross_swap_left]
      exact theorem_9_4_wlog hTB hAB.2 hCD.1 hBC (by simpa [union_comm] using hAC)
    · have hmin : min vBC vBD = vBD := min_eq_right hBD
      have hAD : vBD ≤ vAD := by
        rw [← hmin]
        exact h2.trans (min_le_right _ _)
      rw [← separationsCross_swap_left, ← separationsCross_swap_right]
      exact theorem_9_4_wlog hTB hAB.2 hCD.2 hBD (by simpa [union_comm] using hAD)

end GraphMinor.GM10
