/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Thomas.Basic

/-!
# Amalgamating tree-decompositions (Bellenbaum–Diestel, Section 2)

This file formalizes Section 2 of P. Bellenbaum and R. Diestel, *Two short proofs concerning
tree-decompositions*, Combin. Probab. Comput. 11 (2002) 541–547 (page 2):

- Given a tree-decomposition `D = (V_t)_{t ∈ T}` of `(G, V₀)`, a subset `X ⊆ V₀`, a union `C` of
  components of `G - X`, `H := G[C ∪ X]`, a node `s ∈ T`, and a choice of 'home' node `home x ∈ T`
  with `x ∈ V_{home x}` for each `x ∈ X`, we define
  $$W_t := (V_t \cap (C \cup X)) \cup \{\, x \in X \mid t \in t_x T s \,\}$$
  (`shiftBag`) and prove that `D_s(H) := (W_t)_{t ∈ T}` (`shift`) is a tree-decomposition of `H`
  with `X ⊆ W_s`.
- **Lemma 2** (`lemma_2`): If `G - C` contains a set `{P_x | x ∈ X}` of disjoint `X`–`V_s` paths
  with `x ∈ P_x` for all `x`, then `|W_t| ≤ |V_t|` for all `t ∈ T`.
- **Amalgamation** (`combine`): For two disjoint copies `T^1, T^2` of `T` joined by the edge
  `t₂^1 t₁^2` (`T' := T^1 ∪ T^2 + t₂^1 t₁^2`, indexed by `Bool × ι`), combining `D_{t₂}(H₁)` and
  `D_{t₁}(H₂)` yields a tree-decomposition `D'` of `G`.
-/

@[expose] public section

namespace GraphMinor.Thomas

open SimpleGraph

variable {α ι : Type*}

namespace TreeDecomp

variable [Fintype ι] {G : SimpleGraph α} {V₀ : Set α} (D : TreeDecomp G V₀ ι)

/-- The modified bag `W_t := (V_t ∩ (C ∪ X)) ∪ {x ∈ X | t ∈ t_x T s}` of `\mathcal{D}_s(H)`
(Bellenbaum and Diestel, Section 2, page 2). -/
def shiftBag (X C : Set α) (home : α → ι) (s : ι) (t : ι) : Set α :=
  (D.bag t ∩ (C ∪ X)) ∪ {x ∈ X | OnTreePath D.T (home x) s t}

@[simp]
theorem mem_shiftBag {X C : Set α} {home : α → ι} {s t : ι} {x : α} :
    x ∈ D.shiftBag X C home s t ↔
      (x ∈ D.bag t ∧ (x ∈ C ∨ x ∈ X)) ∨ (x ∈ X ∧ OnTreePath D.T (home x) s t) :=
  Iff.rfl

theorem subset_shiftBag_self (X C : Set α) (home : α → ι) (s : ι) :
    X ⊆ D.shiftBag X C home s s :=
  fun x hx ↦ Or.inr ⟨hx, onTreePath_right D.T (home x) s⟩

theorem shiftBag_sdiff_subset (X C : Set α) (home : α → ι) (s t : ι) :
    D.shiftBag X C home s t \ X ⊆ D.bag t ∩ C := by
  rintro x ⟨(⟨hbt, hxC | hxX⟩ | ⟨hxX, _⟩), hnotX⟩
  · exact ⟨hbt, hxC⟩
  · exact (hnotX hxX).elim
  · exact (hnotX hxX).elim

theorem shiftBag_inter_compl_eq (X C : Set α) (home : α → ι) (s t : ι) :
    D.shiftBag X C home s t \ D.bag t =
      {x ∈ X | OnTreePath D.T (home x) s t} \ D.bag t := by
  ext x
  simp only [shiftBag, Set.mem_sdiff, Set.mem_union, Set.mem_inter_iff, Set.mem_sep_iff]
  tauto

theorem shiftBag_subset (X C : Set α) (home : α → ι) (s t : ι)
    (hX : X ⊆ V₀) :
    D.shiftBag X C home s t ⊆ V₀ := by
  rintro x (⟨hbt, _⟩ | ⟨hxX, _⟩)
  · exact D.bag_subset t hbt
  · exact hX hxX

theorem shiftBag_finite (hV₀ : V₀.Finite) {X C : Set α} (hX : X ⊆ V₀)
    (home : α → ι) (s t : ι) :
    (D.shiftBag X C home s t).Finite :=
  hV₀.subset (D.shiftBag_subset X C home s t hX)

/-- `\mathcal{D}_s(H) := (W_t)_{t ∈ T}` is a tree-decomposition of `H = G[C ∪ X]`
(Bellenbaum and Diestel, Section 2, page 2). -/
def shift {X C : Set α} (hX : X ⊆ V₀) (hC : C ⊆ V₀)
    {home : α → ι} (hhome : ∀ x ∈ X, x ∈ D.bag (home x)) (s : ι) :
    TreeDecomp G (C ∪ X) ι where
  T := D.T
  isTree := D.isTree
  bag := D.shiftBag X C home s
  iUnion_bag := by
    ext x
    simp only [Set.mem_iUnion, mem_shiftBag, Set.mem_union]
    constructor
    · rintro ⟨t, ⟨_, h⟩ | ⟨hxX, _⟩⟩
      · exact h
      · exact Or.inr hxX
    · intro hx
      obtain ⟨t, hxt⟩ := D.exists_mem_bag (Set.union_subset hC hX hx)
      exact ⟨t, Or.inl ⟨hxt, hx⟩⟩
  adj_mem_bag u v hu hv hadj := by
    obtain ⟨t, hut, hvt⟩ := D.adj_mem_bag (Set.union_subset hC hX hu)
      (Set.union_subset hC hX hv) hadj
    exact ⟨t, Or.inl ⟨hut, hu⟩, Or.inl ⟨hvt, hv⟩⟩
  inter_subset_bag t₁ t₂ t₃ ht x := by
    rintro ⟨h₁, h₃⟩
    rcases h₁ with ⟨hx₁, hxCX⟩ | ⟨hxX, hpath₁⟩
    · rcases h₃ with ⟨hx₃, _⟩ | ⟨hxX, hpath₃⟩
      · exact Or.inl ⟨D.mem_bag_of_onTreePath ht hx₁ hx₃, hxCX⟩
      · rcases onTreePath_left_or_right D.isTree (home x) ht with h | h
        · exact Or.inl ⟨D.mem_bag_of_onTreePath (onTreePath_symm h) (hhome x hxX) hx₁, hxCX⟩
        · exact Or.inr ⟨hxX, onTreePath_trans_left D.isTree hpath₃ h⟩
    · rcases h₃ with ⟨hx₃, _⟩ | ⟨_, hpath₃⟩
      · rcases onTreePath_left_or_right D.isTree (home x) (onTreePath_symm ht) with h | h
        · exact Or.inl ⟨D.mem_bag_of_onTreePath (onTreePath_symm h) (hhome x hxX) hx₃, Or.inr hxX⟩
        · exact Or.inr ⟨hxX, onTreePath_trans_left D.isTree hpath₁ h⟩
      · rcases onTreePath_left_or_right D.isTree s ht with h | h
        · exact Or.inr ⟨hxX, onTreePath_trans_right D.isTree hpath₁ h⟩
        · exact Or.inr ⟨hxX, onTreePath_trans_right D.isTree hpath₃ (onTreePath_symm h)⟩

/-- **Lemma 2** of Bellenbaum and Diestel (Section 2, page 2):
If `G - C` contains a set `{P_x | x ∈ X}` of disjoint `X`–`V_s` paths with `x ∈ P_x` for all `x`,
then `|W_t| ≤ |V_t|` for all `t ∈ T`.

Here each `x ∈ X` has a walk `P x` in `G` from `x` to `endVert x ∈ D.bag s` whose support lies in
`V₀ \ C`, such that for distinct `x, y ∈ X` the supports of `P x` and `P y` are disjoint. -/
theorem lemma_2 (hV₀ : V₀.Finite) {X C : Set α} (hX : X ⊆ V₀)
    {home : α → ι} (hhome : ∀ x ∈ X, x ∈ D.bag (home x)) (s : ι)
    {endVert : α → α} (hend : ∀ x ∈ X, endVert x ∈ D.bag s)
    (P : ∀ x ∈ X, G.Walk x (endVert x))
    (hP_sub : ∀ x (hx : x ∈ X), ∀ z ∈ (P x hx).support, z ∈ V₀ \ C)
    (hP_disj : ∀ x (hx : x ∈ X) y (hy : y ∈ X), x ≠ y →
      Disjoint {z | z ∈ (P x hx).support} {z | z ∈ (P y hy).support})
    (t : ι) :
    (D.shiftBag X C home s t).ncard ≤ (D.bag t).ncard := by
  classical
  have hY_mem : ∀ x ∈ D.shiftBag X C home s t \ D.bag t, x ∈ X ∧ OnTreePath D.T (home x) s t := by
    intro x hx
    rw [shiftBag_inter_compl_eq] at hx
    exact hx.1
  have hY_ex : ∀ x (hx : x ∈ D.shiftBag X C home s t \ D.bag t),
      ∃ z ∈ (P x (hY_mem x hx).1).support, z ∈ D.bag t \ D.shiftBag X C home s t := by
    intro x hx
    have ⟨hxX, hpath⟩ := hY_mem x hx
    have hnotbag : x ∉ D.bag t := hx.2
    obtain ⟨z, hzP, hzt⟩ := D.lemma_1_vertex hpath (hhome x hxX) (hend x hxX) (P x hxX)
      (fun w hw ↦ (hP_sub x hxX w hw).1)
    refine ⟨z, hzP, hzt, ?_⟩
    intro hzW
    rcases hzW with ⟨_, hzC | hzX⟩ | ⟨hzX, _⟩
    · exact (hP_sub x hxX z hzP).2 hzC
    · have hzx : x = z := by
        by_contra hne
        exact Set.disjoint_left.1 (hP_disj x hxX z hzX hne) hzP (Walk.start_mem_support _)
      exact hnotbag (hzx ▸ hzt)
    · have hzx : x = z := by
        by_contra hne
        exact Set.disjoint_left.1 (hP_disj x hxX z hzX hne) hzP (Walk.start_mem_support _)
      exact hnotbag (hzx ▸ hzt)
  let f : α → α := fun x ↦
    if hx : x ∈ D.shiftBag X C home s t \ D.bag t then (hY_ex x hx).choose else x
  have hf_mem : ∀ x ∈ D.shiftBag X C home s t \ D.bag t,
      f x ∈ D.bag t \ D.shiftBag X C home s t := by
    intro x hx
    dsimp only [f]
    rw [dite_eq_left hx]
    exact (hY_ex x hx).choose_spec.2
  have hf_inj : Set.InjOn f (D.shiftBag X C home s t \ D.bag t) := by
    intro x hx y hy hxy
    dsimp only [f] at hxy
    rw [dite_eq_left hx, dite_eq_left hy] at hxy
    by_contra hne
    have h1 := (hY_ex x hx).choose_spec.1
    have h2 := hxy ▸ (hY_ex y hy).choose_spec.1
    exact Set.disjoint_left.1 (hP_disj x (hY_mem x hx).1 y (hY_mem y hy).1 hne) h1 h2
  rw [Set.ncard_le_ncard_iff_ncard_sdiff_le_ncard_sdiff
    (D.shiftBag_finite hV₀ hX home s t) (D.bag_finite hV₀ t)]
  exact Set.ncard_le_ncard_of_injOn f hf_mem hf_inj ((D.bag_finite hV₀ t).sdiff)

end TreeDecomp

/-! ## Combining two tree-decompositions (`T^1 ∪ T^2 + t₂^1 t₁^2`) -/

/-- Two disjoint copies `T^1 ∪ T^2` of a graph `T` on `Bool × ι`. -/
def disjointCopy (T : SimpleGraph ι) : SimpleGraph (Bool × ι) where
  Adj p q := p.1 = q.1 ∧ T.Adj p.2 q.2
  symm := ⟨fun _ _ h ↦ ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun p h ↦ T.loopless.irrefl p.2 h.2⟩

/-- Projection homomorphism from `disjointCopy T` to `T`. -/
def sndHom (T : SimpleGraph ι) : disjointCopy T →g T where
  toFun p := p.2
  map_rel' h := h.2

theorem disjointCopy_fst_eq_of_mem_support {T : SimpleGraph ι} {u v : Bool × ι}
    (w : (disjointCopy T).Walk u v) {x : Bool × ι} (hx : x ∈ w.support) :
    x.1 = u.1 := by
  induction w with
  | nil =>
    simp only [Walk.support_nil, List.mem_singleton] at hx
    rw [hx]
  | cons hadj p ih =>
    simp only [Walk.support_cons, List.mem_cons] at hx
    rcases hx with rfl | hx
    · rfl
    · exact (ih hx).trans hadj.1.symm

theorem not_reachable_disjointCopy (T : SimpleGraph ι) (t₂ t₁ : ι) :
    ¬ (disjointCopy T).Reachable (false, t₂) (true, t₁) := by
  rintro ⟨w⟩
  exact Bool.false_ne_true (disjointCopy_fst_eq_of_mem_support w w.end_mem_support).symm

theorem disjointCopy_support_eq {T : SimpleGraph ι} {u v : Bool × ι}
    (w : (disjointCopy T).Walk u v) :
    w.support = (w.map (sndHom T)).support.map (fun s ↦ (u.1, s)) := by
  rw [Walk.support_map, List.map_map]
  conv_lhs => rw [← List.map_id w.support]
  refine List.map_congr_left fun x hx ↦ ?_
  exact Prod.ext (disjointCopy_fst_eq_of_mem_support w hx) rfl

theorem disjointCopy_isPath_map {T : SimpleGraph ι} {u v : Bool × ι}
    {w : (disjointCopy T).Walk u v} (hw : w.IsPath) :
    (w.map (sndHom T)).IsPath := by
  rw [Walk.isPath_def]
  have h := hw.support_nodup
  rw [disjointCopy_support_eq w] at h
  exact h.of_map _

theorem disjointCopy_isAcyclic {T : SimpleGraph ι} (hT : T.IsAcyclic) :
    (disjointCopy T).IsAcyclic := by
  rw [isAcyclic_iff_subsingleton_path]
  intro u v
  refine ⟨fun ⟨p, hp⟩ ⟨q, hq⟩ ↦ Subtype.ext ?_⟩
  have hp' : (p.map (sndHom T)).IsPath := disjointCopy_isPath_map hp
  have hq' : (q.map (sndHom T)).IsPath := disjointCopy_isPath_map hq
  have heq : p.map (sndHom T) = q.map (sndHom T) :=
    Subtype.ext_iff.1 ((hT.subsingleton_path u.2 v.2).elim ⟨_, hp'⟩ ⟨_, hq'⟩)
  apply Walk.ext_support
  rw [disjointCopy_support_eq p, disjointCopy_support_eq q, heq]

/-- The tree `T' := T^1 ∪ T^2 + t₂^1 t₁^2` on `Bool × ι`, where `false` is copy `1` and `true` is
copy `2`, and the bridge edge joins `(false, t₂)` and `(true, t₁)` (Bellenbaum and Diestel, proof
of Theorem 3, page 3). -/
def combineTree (T : SimpleGraph ι) (t₂ t₁ : ι) : SimpleGraph (Bool × ι) where
  Adj p q :=
    (p.1 = q.1 ∧ T.Adj p.2 q.2) ∨
    (p = (false, t₂) ∧ q = (true, t₁)) ∨
    (p = (true, t₁) ∧ q = (false, t₂))
  symm := ⟨fun _ _ h ↦ by
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h1.symm, h2.symm⟩
    · exact Or.inr (Or.inr ⟨h2, h1⟩)
    · exact Or.inr (Or.inl ⟨h2, h1⟩)⟩
  loopless := ⟨fun p h ↦ by
    rcases h with ⟨_, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact T.loopless.irrefl p.2 h2
    · exact Bool.false_ne_true (congrArg Prod.fst (h1.symm.trans h2))
    · exact Bool.false_ne_true (congrArg Prod.fst (h2.symm.trans h1))⟩

theorem combineTree_eq_sup_edge (T : SimpleGraph ι) (t₂ t₁ : ι) :
    combineTree T t₂ t₁ = disjointCopy T ⊔ SimpleGraph.edge (false, t₂) (true, t₁) := by
  ext p q
  simp only [combineTree, SimpleGraph.sup_adj, disjointCopy, SimpleGraph.edge_adj, ne_eq]
  constructor
  · rintro (h | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨Or.inl ⟨rfl, rfl⟩, fun h ↦ Bool.false_ne_true (congrArg Prod.fst h)⟩
    · exact Or.inr ⟨Or.inr ⟨rfl, rfl⟩, fun h ↦ Bool.false_ne_true (congrArg Prod.fst h.symm)⟩
  · rintro (h | ⟨⟨rfl, rfl⟩ | ⟨rfl, rfl⟩, _⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · exact Or.inr (Or.inr ⟨rfl, rfl⟩)

theorem combineTree_adj_embed {T : SimpleGraph ι} (t₂ t₁ : ι) (b : Bool) {s₁ s₂ : ι}
    (h : T.Adj s₁ s₂) : (combineTree T t₂ t₁).Adj (b, s₁) (b, s₂) :=
  Or.inl ⟨rfl, h⟩

theorem combineTree_adj_bridge_left (T : SimpleGraph ι) (t₂ t₁ : ι) :
    (combineTree T t₂ t₁).Adj (false, t₂) (true, t₁) :=
  Or.inr (Or.inl ⟨rfl, rfl⟩)

theorem combineTree_adj_bridge_right (T : SimpleGraph ι) (t₂ t₁ : ι) :
    (combineTree T t₂ t₁).Adj (true, t₁) (false, t₂) :=
  Or.inr (Or.inr ⟨rfl, rfl⟩)

/-- Embedding a walk of `T` into copy `b : Bool` of `combineTree T t₂ t₁`. -/
abbrev embedCombineHom (T : SimpleGraph ι) (t₂ t₁ : ι) (b : Bool) :
    T →g combineTree T t₂ t₁ where
  toFun s := (b, s)
  map_rel' h := combineTree_adj_embed t₂ t₁ b h

theorem embedCombineHom_injective (b : Bool) :
    Function.Injective (fun s : ι ↦ (b, s)) :=
  fun _ _ h ↦ Prod.ext_iff.1 h |>.2

/-- Canonical path in `combineTree T t₂ t₁` between `u` and `v`. -/
noncomputable def combinePath {T : SimpleGraph ι} (hT : T.IsTree) (t₂ t₁ : ι) :
    ∀ u v : Bool × ι, (combineTree T t₂ t₁).Walk u v
  | (false, s₁), (false, s₂) =>
    (treePath hT s₁ s₂).map (embedCombineHom T t₂ t₁ false)
  | (true, s₁), (true, s₂) =>
    (treePath hT s₁ s₂).map (embedCombineHom T t₂ t₁ true)
  | (false, s₁), (true, s₂) =>
    ((treePath hT s₁ t₂).map (embedCombineHom T t₂ t₁ false)).append
      (Walk.cons (combineTree_adj_bridge_left T t₂ t₁)
        ((treePath hT t₁ s₂).map (embedCombineHom T t₂ t₁ true)))
  | (true, s₁), (false, s₂) =>
    ((treePath hT s₁ t₁).map (embedCombineHom T t₂ t₁ true)).append
      (Walk.cons (combineTree_adj_bridge_right T t₂ t₁)
        ((treePath hT t₂ s₂).map (embedCombineHom T t₂ t₁ false)))

theorem combinePath_isPath {T : SimpleGraph ι} (hT : T.IsTree) (t₂ t₁ : ι)
    (u v : Bool × ι) : (combinePath hT t₂ t₁ u v).IsPath := by
  rcases u with ⟨b₁, s₁⟩
  rcases v with ⟨b₂, s₂⟩
  cases b₁ <;> cases b₂
  · exact (treePath_isPath hT s₁ s₂).map (embedCombineHom_injective false)
  · dsimp [combinePath]
    have hp1 : ((treePath hT s₁ t₂).map (embedCombineHom T t₂ t₁ false)).IsPath :=
      (treePath_isPath hT s₁ t₂).map (embedCombineHom_injective false)
    have hp2 : ((treePath hT t₁ s₂).map (embedCombineHom T t₂ t₁ true)).IsPath :=
      (treePath_isPath hT t₁ s₂).map (embedCombineHom_injective true)
    rw [Walk.isPath_def, Walk.support_append, Walk.support_cons, List.tail_cons, List.nodup_append']
    refine ⟨hp1.support_nodup, hp2.support_nodup, ?_⟩
    intro x hx1 hx2
    rw [Walk.support_map, List.mem_map] at hx1 hx2
    obtain ⟨a1, _, rfl⟩ := hx1
    obtain ⟨a2, _, heq⟩ := hx2
    exact Bool.false_ne_true (congrArg Prod.fst heq).symm
  · dsimp [combinePath]
    have hp1 : ((treePath hT s₁ t₁).map (embedCombineHom T t₂ t₁ true)).IsPath :=
      (treePath_isPath hT s₁ t₁).map (embedCombineHom_injective true)
    have hp2 : ((treePath hT t₂ s₂).map (embedCombineHom T t₂ t₁ false)).IsPath :=
      (treePath_isPath hT t₂ s₂).map (embedCombineHom_injective false)
    rw [Walk.isPath_def, Walk.support_append, Walk.support_cons, List.tail_cons, List.nodup_append']
    refine ⟨hp1.support_nodup, hp2.support_nodup, ?_⟩
    intro x hx1 hx2
    rw [Walk.support_map, List.mem_map] at hx1 hx2
    obtain ⟨a1, _, rfl⟩ := hx1
    obtain ⟨a2, _, heq⟩ := hx2
    exact Bool.false_ne_true (congrArg Prod.fst heq)
  · exact (treePath_isPath hT s₁ s₂).map (embedCombineHom_injective true)

theorem combineTree_isTree {T : SimpleGraph ι} (hT : T.IsTree) (t₂ t₁ : ι) :
    (combineTree T t₂ t₁).IsTree where
  connected :=
    { preconnected := fun u v ↦ (combinePath hT t₂ t₁ u v).reachable
      nonempty := ⟨(false, t₂)⟩ }
  isAcyclic := by
    rw [combineTree_eq_sup_edge]
    exact (disjointCopy_isAcyclic hT.isAcyclic).sup_edge_of_not_reachable
      (not_reachable_disjointCopy T t₂ t₁)

theorem treePath_combineTree_eq {T : SimpleGraph ι} (hT : T.IsTree) (t₂ t₁ : ι)
    (u v : Bool × ι) :
    treePath (combineTree_isTree hT t₂ t₁) u v = combinePath hT t₂ t₁ u v :=
  (eq_treePath (combineTree_isTree hT t₂ t₁) (combinePath hT t₂ t₁ u v)
    (combinePath_isPath hT t₂ t₁ u v)).symm

theorem onTreePath_combineTree_same {T : SimpleGraph ι} (hT : T.IsTree) (t₂ t₁ : ι)
    (b : Bool) (s₁ s₂ : ι) (p : Bool × ι) :
    OnTreePath (combineTree T t₂ t₁) (b, s₁) (b, s₂) p ↔
      p.1 = b ∧ OnTreePath T s₁ s₂ p.2 := by
  rw [onTreePath_iff_mem_treePath (combineTree_isTree hT t₂ t₁), treePath_combineTree_eq hT]
  rcases p with ⟨bp, sp⟩
  cases b <;>
    · simp only [combinePath, Walk.support_map, List.mem_map, RelHom.coeFn_mk, Prod.mk.injEq,
        exists_eq_right_right, onTreePath_iff_mem_treePath hT]
      tauto

theorem onTreePath_combineTree_false_true {T : SimpleGraph ι} (hT : T.IsTree) (t₂ t₁ : ι)
    (s₁ s₂ : ι) (p : Bool × ι) :
    OnTreePath (combineTree T t₂ t₁) (false, s₁) (true, s₂) p ↔
      (p.1 = false ∧ OnTreePath T s₁ t₂ p.2) ∨ (p.1 = true ∧ OnTreePath T t₁ s₂ p.2) := by
  rw [onTreePath_iff_mem_treePath (combineTree_isTree hT t₂ t₁), treePath_combineTree_eq hT]
  rcases p with ⟨bp, sp⟩
  dsimp [combinePath]
  rw [Walk.support_append, Walk.support_cons, List.tail_cons, List.mem_append,
    Walk.support_map, Walk.support_map, List.mem_map, List.mem_map]
  cases bp <;>
    simp [onTreePath_iff_mem_treePath hT]

namespace TreeDecomp

variable [Fintype ι] {G : SimpleGraph α} {V₀ : Set α} (D : TreeDecomp G V₀ ι)

/-- The bags of the amalgamated tree-decomposition `\mathcal{D}'` on `T' = T^1 ∪ T^2 + t₂^1 t₁^2`
(Bellenbaum and Diestel, proof of Theorem 3, page 3). -/
def combineBag (X C₁ C₂ : Set α) (home : α → ι) (t₁ t₂ : ι) : Bool × ι → Set α
  | (false, t) => D.shiftBag X C₁ home t₂ t
  | (true, t) => D.shiftBag X C₂ home t₁ t

theorem shiftBag_subset_union (X C : Set α) (home : α → ι) (s t : ι) :
    D.shiftBag X C home s t ⊆ C ∪ X := by
  rintro x (⟨_, hx⟩ | ⟨hxX, _⟩)
  · exact hx
  · exact Or.inr hxX

/-- Amalgamating `\mathcal{D}_{t₂}(H₁)` and `\mathcal{D}_{t₁}(H₂)` along the edge `t₂^1 t₁^2` yields
a tree-decomposition `\mathcal{D}'` of `G` (Bellenbaum and Diestel, proof of Theorem 3, page 3). -/
def combine {X C₁ C₂ : Set α} (hX : X ⊆ V₀) (hC₁ : C₁ ⊆ V₀) (hC₂ : C₂ ⊆ V₀)
    (hcov : V₀ ⊆ C₁ ∪ C₂ ∪ X) (hdisj : Disjoint C₁ C₂)
    (hsep : ∀ ⦃u v : α⦄, u ∈ V₀ → v ∈ V₀ → G.Adj u v →
      (u ∈ C₁ ∪ X ∧ v ∈ C₁ ∪ X) ∨ (u ∈ C₂ ∪ X ∧ v ∈ C₂ ∪ X))
    {home : α → ι} (hhome : ∀ x ∈ X, x ∈ D.bag (home x)) (t₁ t₂ : ι) :
    TreeDecomp G V₀ (Bool × ι) where
  T := combineTree D.T t₂ t₁
  isTree := combineTree_isTree D.isTree t₂ t₁
  bag := D.combineBag X C₁ C₂ home t₁ t₂
  iUnion_bag := by
    have h1 := (D.shift hX hC₁ hhome t₂).iUnion_bag
    have h2 := (D.shift hX hC₂ hhome t₁).iUnion_bag
    ext x
    simp only [Set.mem_iUnion, Prod.exists, Bool.exists_bool, combineBag]
    have h1' : (∃ t, x ∈ D.shiftBag X C₁ home t₂ t) ↔ x ∈ C₁ ∪ X := by
      rw [← Set.mem_iUnion]; exact Eq.to_iff (congrArg (x ∈ ·) h1)
    have h2' : (∃ t, x ∈ D.shiftBag X C₂ home t₁ t) ↔ x ∈ C₂ ∪ X := by
      rw [← Set.mem_iUnion]; exact Eq.to_iff (congrArg (x ∈ ·) h2)
    rw [h1', h2']
    constructor
    · rintro ((hx | hx) | (hx | hx))
      · exact hC₁ hx
      · exact hX hx
      · exact hC₂ hx
      · exact hX hx
    · intro hx
      rcases hcov hx with (hx | hx) | hx
      · exact Or.inl (Or.inl hx)
      · exact Or.inr (Or.inl hx)
      · exact Or.inl (Or.inr hx)
  adj_mem_bag u v hu hv hadj := by
    rcases hsep hu hv hadj with ⟨hu1, hv1⟩ | ⟨hu2, hv2⟩
    · obtain ⟨t, hut, hvt⟩ := (D.shift hX hC₁ hhome t₂).adj_mem_bag hu1 hv1 hadj
      exact ⟨(false, t), hut, hvt⟩
    · obtain ⟨t, hut, hvt⟩ := (D.shift hX hC₂ hhome t₁).adj_mem_bag hu2 hv2 hadj
      exact ⟨(true, t), hut, hvt⟩
  inter_subset_bag := by
    rintro ⟨b₁, s₁⟩ ⟨b₂, s₂⟩ ⟨b₃, s₃⟩ hp x ⟨hx₁, hx₃⟩
    cases b₁ <;> cases b₃
    · rw [onTreePath_combineTree_same D.isTree t₂ t₁ false s₁ s₃ (b₂, s₂)] at hp
      rcases hp with ⟨rfl, hp⟩
      exact (D.shift hX hC₁ hhome t₂).inter_subset_bag hp ⟨hx₁, hx₃⟩
    · rw [onTreePath_combineTree_false_true D.isTree t₂ t₁ s₁ s₃ (b₂, s₂)] at hp
      have hxX : x ∈ X := by
        have h1 := D.shiftBag_subset_union X C₁ home t₂ s₁ hx₁
        have h2 := D.shiftBag_subset_union X C₂ home t₁ s₃ hx₃
        rcases h1 with hC1 | hX1
        · rcases h2 with hC2 | hX2
          · exact (Set.disjoint_left.1 hdisj hC1 hC2).elim
          · exact hX2
        · exact hX1
      rcases hp with ⟨rfl, hp⟩ | ⟨rfl, hp⟩
      · exact (D.shift hX hC₁ hhome t₂).inter_subset_bag hp
          ⟨hx₁, D.subset_shiftBag_self X C₁ home t₂ hxX⟩
      · exact (D.shift hX hC₂ hhome t₁).inter_subset_bag hp
          ⟨D.subset_shiftBag_self X C₂ home t₁ hxX, hx₃⟩
    · have hp' := onTreePath_symm hp
      rw [onTreePath_combineTree_false_true D.isTree t₂ t₁ s₃ s₁ (b₂, s₂)] at hp'
      have hxX : x ∈ X := by
        have h1 := D.shiftBag_subset_union X C₂ home t₁ s₁ hx₁
        have h2 := D.shiftBag_subset_union X C₁ home t₂ s₃ hx₃
        rcases h1 with hC2 | hX2
        · rcases h2 with hC1 | hX1
          · exact (Set.disjoint_left.1 hdisj hC1 hC2).elim
          · exact hX1
        · exact hX2
      rcases hp' with ⟨rfl, hp'⟩ | ⟨rfl, hp'⟩
      · exact (D.shift hX hC₁ hhome t₂).inter_subset_bag hp'
          ⟨hx₃, D.subset_shiftBag_self X C₁ home t₂ hxX⟩
      · exact (D.shift hX hC₂ hhome t₁).inter_subset_bag hp'
          ⟨D.subset_shiftBag_self X C₂ home t₁ hxX, hx₁⟩
    · rw [onTreePath_combineTree_same D.isTree t₂ t₁ true s₁ s₃ (b₂, s₂)] at hp
      rcases hp with ⟨rfl, hp⟩
      exact (D.shift hX hC₂ hhome t₁).inter_subset_bag hp ⟨hx₁, hx₃⟩

end TreeDecomp

end GraphMinor.Thomas
