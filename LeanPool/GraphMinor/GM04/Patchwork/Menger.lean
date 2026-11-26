/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM04.Patchwork.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Finset.Card

/-!
# Menger's theorem for robust patchworks (Graph Minors IV, Section 6)

This file proves the properties of free and robust patches from Graph Minors IV, Section 6
(pages 241–242) and Section 8 (page 248):

* `emptySubgraph_isPairing`, `completeSubgraph_isGrouping`: `N_V` is a pairing and `K_V` is a
  grouping.
* `Patch.IsFree.isRobust`: every free patch on a finite vertex set is robust.
* `Patch.IsRobust.emptySubgraph_mem` and `Patchwork.IsRobust.isRemovable`: every robust patch on a
  finite vertex set contains `N_{V(Δ)}`, so every robust patchwork is removable.
* `Theorem61Cond1`, `Theorem61Cond2`, `Theorem61Cond3`, and `theorem_6_1`: Graph Minors IV, (6.1),
  the equivalence of (i), (ii), and (iii) for a robust `Ω`-patchwork, assuming `MengerStatement`.
-/

public section

namespace GraphMinor.GM04

open SimpleGraph

universe u v w

variable {Ω : Type w} {α : Type u} {β : Type v}

/-! ### Basic groupings and pairings -/

/-- `N_V` (`emptySubgraph V`) is a grouping in `V`. -/
theorem emptySubgraph_isGrouping (V : Set α) : IsGrouping V (emptySubgraph V) := by
  rw [isGrouping_iff]
  exact ⟨subset_rfl, fun _ _ _ _ h ↦ False.elim h⟩

/-- `N_V` (`emptySubgraph V`) is a pairing in `V`. -/
theorem emptySubgraph_isPairing (V : Set α) : IsPairing V (emptySubgraph V) := by
  refine ⟨emptySubgraph_isGrouping V, ?_⟩
  rintro D ⟨x, rfl⟩
  have hsub : (component (emptySubgraph V) x).verts ⊆ {x.1} := by
    rintro w ⟨hw, hr⟩
    suffices ∀ y : (emptySubgraph V).verts, (emptySubgraph V).coe.Reachable x y → y.1 = x.1 from
      this ⟨w, hw⟩ hr
    intro y hy
    rw [reachable_iff_reflTransGen] at hy
    induction hy with
    | refl => rfl
    | @tail z u _ hzu => exact False.elim hzu
  exact (Set.encard_mono hsub).trans (by simp)

/-- `K_V` (`completeSubgraph V`) is a grouping in `V`. -/
theorem completeSubgraph_isGrouping (V : Set α) : IsGrouping V (completeSubgraph V) := by
  rw [isGrouping_iff]
  exact ⟨subset_rfl, fun a b c hac ⟨ha, _, _⟩ ⟨_, hc, _⟩ ↦ ⟨ha, hc, hac⟩⟩

/-- `N_V` pairs `∅, ∅` in `V`. -/
theorem emptySubgraph_pairs_empty (V : Set α) : Pairs V (emptySubgraph V) ∅ ∅ := by
  refine ⟨Set.empty_subset V, Set.empty_subset V, Set.disjoint_empty _, fun D hD hcard2 ↦ ?_,
    fun v hv ↦ by simp at hv⟩
  exfalso
  have hle1 : D.verts.ncard ≤ 1 := by
    rcases hD with ⟨x, rfl⟩
    have hsub : (component (emptySubgraph V) x).verts ⊆ {x.1} := by
      rintro w ⟨hw, hr⟩
      suffices ∀ y : (emptySubgraph V).verts, (emptySubgraph V).coe.Reachable x y → y.1 = x.1 from
        this ⟨w, hw⟩ hr
      intro y hy
      rw [reachable_iff_reflTransGen] at hy
      induction hy with
      | refl => rfl
      | @tail z u _ hzu => exact False.elim hzu
    exact (Set.ncard_le_ncard hsub (Set.toFinite {x.1})).trans (by simp)
  omega

/-- Given disjoint subsets `X, Y` of a finite set `V` with `|X| = |Y|`, there is a pairing in `V`
with vertex set `V` that pairs `X, Y`. -/
theorem exists_pairing_pairs {V X Y : Set α} (hV : V.Finite) (hX : X ⊆ V) (hY : Y ⊆ V)
    (hcard : X.ncard = Y.ncard) (hdisj : Disjoint X Y) :
    ∃ δ : (⊤ : SimpleGraph α).Subgraph,
      δ.verts = V ∧ IsPairing V δ ∧ Pairs V δ X Y := by
  classical
  have hXfin : X.Finite := hV.subset hX
  have hYfin : Y.Finite := hV.subset hY
  have : Fintype X := hXfin.fintype
  have : Fintype Y := hYfin.fintype
  have hcard' : Fintype.card X = Fintype.card Y := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      Nat.card_coe_set_eq, Nat.card_coe_set_eq, hcard]
  obtain ⟨e⟩ := Fintype.truncEquivOfCardEq hcard'
  let δ : (⊤ : SimpleGraph α).Subgraph :=
    { verts := V
      Adj := fun u v ↦
        (∃ (hu : u ∈ X), (e ⟨u, hu⟩).1 = v) ∨ (∃ (hv : v ∈ X), (e ⟨v, hv⟩).1 = u)
      adj_sub := by
        rintro u v (⟨hu, rfl⟩ | ⟨hv, rfl⟩)
        · simp only [top_adj]
          intro hEq
          exact Set.disjoint_left.mp hdisj hu (hEq ▸ (e ⟨u, hu⟩).2)
        · simp only [top_adj]
          intro hEq
          exact Set.disjoint_left.mp hdisj hv (hEq.symm ▸ (e ⟨v, hv⟩).2)
      edge_vert := by
        rintro u v (⟨hu, _⟩ | ⟨_, rfl⟩)
        · exact hX hu
        · exact hY (e _).2
      symm := ⟨fun _ _ h ↦ h.symm⟩ }
  have hpair : IsPairing V δ := by
    rw [isPairing_iff hV]
    refine ⟨subset_rfl, fun a b c hab hac ↦ ?_⟩
    rcases hab with ⟨ha, rfl⟩ | ⟨hb, hab⟩ <;> rcases hac with ⟨ha', rfl⟩ | ⟨hc, hac⟩
    · rfl
    · exfalso
      exact Set.disjoint_left.mp hdisj ha (hac ▸ (e ⟨c, hc⟩).2)
    · exfalso
      exact Set.disjoint_left.mp hdisj ha' (hab ▸ (e ⟨b, hb⟩).2)
    · have hbc : (⟨b, hb⟩ : X) = ⟨c, hc⟩ := e.injective (Subtype.ext (hab.trans hac.symm))
      exact congrArg Subtype.val hbc
  refine ⟨δ, rfl, hpair, ?_⟩
  rw [pairs_iff_of_isPairing hV hpair]
  refine ⟨hX, hY, hdisj, fun u v huv ↦ ?_, fun v hv ↦ ?_⟩
  · rcases huv with ⟨hu, rfl⟩ | ⟨hv, rfl⟩
    · exact Or.inl ⟨hu, (e ⟨u, hu⟩).2⟩
    · exact Or.inr ⟨(e ⟨v, hv⟩).2, hv⟩
  · rcases hv with hvX | hvY
    · exact ⟨(e ⟨v, hvX⟩).1, Or.inl ⟨hvX, rfl⟩⟩
    · exact ⟨(e.symm ⟨v, hvY⟩).1, Or.inr ⟨(e.symm ⟨v, hvY⟩).2, by simp⟩⟩

/-- Every free patch on a finite vertex set is robust (Graph Minors IV, Section 6, page 241:
"free patches are robust"). -/
theorem Patch.IsFree.isRobust {Δ : Patch α} (hfin : Δ.verts.Finite) (hfree : Δ.IsFree) :
    Δ.IsRobust := by
  refine ⟨hfin, ?_⟩
  intro X hX Y hY hcard hdisj
  obtain ⟨δ, hverts, hpair, hpairs⟩ := exists_pairing_pairs hfin hX hY hcard hdisj
  exact ⟨δ, hfree δ hpair.1 hverts, hpair, hpairs⟩

/-- Every robust patch contains `N_{V(Δ)}`. -/
theorem Patch.IsRobust.emptySubgraph_mem {Δ : Patch α} (hrob : Δ.IsRobust) :
    emptySubgraph Δ.verts ∈ Δ := by
  obtain ⟨δ, hδ, hpair, hpairs⟩ :=
    hrob.exists_pairing ∅ (Set.empty_subset _) ∅ (Set.empty_subset _) rfl (Set.disjoint_empty _)
  have hverts : δ.verts = Δ.verts := Δ.verts_eq δ hδ
  have hadj := (pairs_iff_of_isPairing hrob.finite_verts hpair).mp hpairs
  have hEq : δ = emptySubgraph Δ.verts := by
    ext u v
    · simp [hverts]
    · simp only [not_emptySubgraph_adj, iff_false]
      intro huv
      rcases hadj.2.2.2.1 u v huv with ⟨hu, _⟩ | ⟨hu, _⟩ <;> exact hu
  rwa [← hEq]

/-- Every robust `Ω`-patchwork is removable (Graph Minors IV, Section 8, page 248: "Evidently
robust patchworks are removable"). -/
theorem Patchwork.IsRobust.isRemovable {P : Patchwork Ω α β} (hrob : P.IsRobust) :
    P.IsRemovable := by
  intro e he
  have hmem := (hrob e he).emptySubgraph_mem
  rwa [P.Δ_verts e he] at hmem

/-! ### Properties of realizations -/

@[simp]
theorem realizationOf_verts {G : Hypergraph α β} {δ : β → (⊤ : SimpleGraph α).Subgraph}
    (hδ : ∀ e ∈ G.edgeSet, (δ e).verts = G.ends e) :
    (realizationOf G δ).verts = G.vertexSet := by
  ext v
  simp only [realizationOf, Subgraph.verts_sup, emptySubgraph_verts, Subgraph.verts_iSup,
    Set.mem_union, Set.mem_iUnion, exists_prop]
  refine ⟨?_, fun hv ↦ Or.inl hv⟩
  rintro (hv | ⟨e, he, hv⟩)
  · exact hv
  · rw [hδ e he] at hv
    exact G.vertex_mem_of_inc hv

theorem Patchwork.IsRealization.verts_eq {P : Patchwork Ω α β}
    {H : (⊤ : SimpleGraph α).Subgraph} (hH : P.IsRealization H) :
    H.verts = P.G.vertexSet := by
  obtain ⟨δ, hδ, rfl⟩ := hH
  exact realizationOf_verts fun e he ↦ ((P.Δ e).verts_eq (δ e) (hδ e he)).trans (P.Δ_verts e he)

theorem Patchwork.IsRealization.adj_imp_skeleton_adj {P : Patchwork Ω α β}
    {H : (⊤ : SimpleGraph α).Subgraph} (hH : P.IsRealization H) {u v : α} (huv : H.Adj u v) :
    P.G.toHypergraph.skeleton.Adj u v := by
  obtain ⟨δ, hδ, rfl⟩ := hH
  rw [realizationOf_adj] at huv
  obtain ⟨e, he, huv⟩ := huv
  have hverts : (δ e).verts = P.G.ends e :=
    ((P.Δ e).verts_eq (δ e) (hδ e he)).trans (P.Δ_verts e he)
  have hu : u ∈ P.G.ends e := hverts ▸ (δ e).edge_vert huv
  have hv : v ∈ P.G.ends e := hverts ▸ (δ e).edge_vert huv.symm
  exact ⟨huv.ne, e, hu, hv⟩

/-! ### Statements of (6.1)(i), (ii), (iii) -/

/-- Condition (i) of Graph Minors IV, (6.1) (page 241): "every separation $(G_1, G_2)$ of $G^-$ with
$X_i \subseteq V(G_i)$ ($i = 1, 2$) has order
$\ge k$". -/
@[expose] def Theorem61Cond1 (P : Patchwork Ω α β) (X₁ X₂ : Set α) (k : ℕ) : Prop :=
  ∀ G₁ G₂ : Hypergraph α β, P.G.toHypergraph.IsSeparation G₁ G₂ →
    X₁ ⊆ G₁.vertexSet → X₂ ⊆ G₂.vertexSet → k ≤ Hypergraph.separationOrder G₁ G₂

/-- Condition (ii) of Graph Minors IV, (6.1) (page 241): "there is a realization of $P$ such that
$k$ of its components have non-empty intersection
with both $X_1$ and $X_2$". -/
@[expose] def Theorem61Cond2 (P : Patchwork Ω α β) (X₁ X₂ : Set α) (k : ℕ) : Prop :=
  ∃ (H : (⊤ : SimpleGraph α).Subgraph) (D : Fin k → (⊤ : SimpleGraph α).Subgraph),
    P.IsRealization H ∧ Function.Injective D ∧
    (∀ i, IsComponent H (D i) ∧ ((D i).verts ∩ X₁).Nonempty ∧ ((D i).verts ∩ X₂).Nonempty)

/-- A subgraph `D` is a path of `H` from `X₁` to `X₂` with no vertex except its first in `X₁` and
no vertex except its last in `X₂`. -/
@[expose] def IsCleanPathSubgraph (H D : (⊤ : SimpleGraph α).Subgraph) (X₁ X₂ : Set α) : Prop :=
  ∃ p : PathFromTo H.spanningCoe X₁ X₂,
    D = H.induce {v | v ∈ p.walk.support} ∧
    (∀ u ∈ p.walk.support, ∀ v ∈ p.walk.support, H.Adj u v ↔ p.walk.toSubgraph.Adj u v) ∧
    (∀ v ∈ p.walk.support, v ∈ X₁ → v = p.first) ∧
    (∀ v ∈ p.walk.support, v ∈ X₂ → v = p.last)

/-- Condition (iii) of Graph Minors IV, (6.1) (page 242): "there is a realization of $P$ such that
$k$ of its components are paths from $X_1$ to $X_2$
with no vertex except their first in $X_1$, and no vertex except their last in $X_2$, and
the remainder of the components of this realization are isolated vertices." -/
@[expose] def Theorem61Cond3 (P : Patchwork Ω α β) (X₁ X₂ : Set α) (k : ℕ) : Prop :=
  ∃ (H : (⊤ : SimpleGraph α).Subgraph) (D : Fin k → (⊤ : SimpleGraph α).Subgraph),
    P.IsRealization H ∧ Function.Injective D ∧
    (∀ i, IsComponent H (D i) ∧ IsCleanPathSubgraph H (D i) X₁ X₂) ∧
    (∀ C, IsComponent H C → (∀ i, C ≠ D i) → C.verts.ncard = 1)

/-! ### Easy directions of (6.1) -/

/-- By Menger's theorem (`MengerStatement`), condition (i) of (6.1) is equivalent to `(i)'`: there
are `k` mutually vertex-disjoint paths of `P.G.toHypergraph.skeleton` from `X₁` to `X₂`
(Graph Minors IV, page 242). -/
theorem theorem_6_1_i_iff_disjointPaths (hM : MengerStatement.{u, v}) {P : Patchwork Ω α β}
    {X₁ X₂ : Set α} (hX₁ : X₁ ⊆ P.G.vertexSet) (hX₂ : X₂ ⊆ P.G.vertexSet) (k : ℕ) :
    Theorem61Cond1 P X₁ X₂ k ↔ HasDisjointPaths P.G.toHypergraph.skeleton X₁ X₂ k := by
  unfold Theorem61Cond1
  exact hM P.G.toHypergraph X₁ X₂ hX₁ hX₂ k

/-- Condition (iii) of (6.1) implies condition (ii) (Graph Minors IV, page 242: "Obviously (iii)
implies (ii)"). -/
theorem theorem_6_1_iii_imp_ii {P : Patchwork Ω α β} {X₁ X₂ : Set α} {k : ℕ}
    (h : Theorem61Cond3 P X₁ X₂ k) : Theorem61Cond2 P X₁ X₂ k := by
  obtain ⟨H, D, hH, hDinj, hD, _⟩ := h
  refine ⟨H, D, hH, hDinj, fun i ↦ ?_⟩
  obtain ⟨hcomp, p, hDeq, _, _, _⟩ := hD i
  refine ⟨hcomp, ⟨p.first, ?_, p.first_mem⟩, ⟨p.last, ?_, p.last_mem⟩⟩
  · rw [hDeq]
    exact p.walk.start_mem_support
  · rw [hDeq]
    exact p.walk.end_mem_support

private theorem walk_coe_to_skeleton {P : Patchwork Ω α β} {H : (⊤ : SimpleGraph α).Subgraph}
    (hH : P.IsRealization H) {x u v : H.verts} (hx : H.coe.Reachable x u)
    (w : H.coe.Walk u v) :
    ∃ w' : P.G.toHypergraph.skeleton.Walk u.1 v.1,
      ∀ z ∈ w'.support, z ∈ (component H x).verts := by
  induction w with
  | @nil a =>
    exact ⟨Walk.nil, fun z hz ↦ by
      rw [Walk.mem_support_nil_iff] at hz
      subst hz
      exact ⟨a.2, hx⟩⟩
  | @cons a b c hab w ih =>
    obtain ⟨w', hw'⟩ := ih (hx.trans (Adj.reachable hab))
    refine ⟨Walk.cons (hH.adj_imp_skeleton_adj hab) w', fun z hz ↦ ?_⟩
    rw [Walk.support_cons, List.mem_cons] at hz
    rcases hz with rfl | hz
    · exact ⟨a.2, hx⟩
    · exact hw' z hz

/-- Condition (ii) of (6.1) implies `(i)'` (Graph Minors IV, page 242: "and (ii) implies (i)'"). -/
theorem theorem_6_1_ii_imp_disjointPaths {P : Patchwork Ω α β} {X₁ X₂ : Set α} {k : ℕ}
    (h : Theorem61Cond2 P X₁ X₂ k) : HasDisjointPaths P.G.toHypergraph.skeleton X₁ X₂ k := by
  classical
  obtain ⟨H, D, hH, hDinj, hD⟩ := h
  have hpath : ∀ i : Fin k, ∃ p : PathFromTo P.G.toHypergraph.skeleton X₁ X₂,
      ∀ z ∈ p.walk.support, z ∈ (D i).verts := by
    intro i
    obtain ⟨⟨x, hDeq⟩, ⟨u, huD, huX₁⟩, ⟨v, hvD, hvX₂⟩⟩ := hD i
    have hu' : u ∈ componentVerts H x := by rwa [← component_verts, ← hDeq]
    have hv' : v ∈ componentVerts H x := by rwa [← component_verts, ← hDeq]
    obtain ⟨huH, hxu⟩ := hu'
    obtain ⟨hvH, hxv⟩ := hv'
    obtain ⟨w₀⟩ := hxu.symm.trans hxv
    obtain ⟨w₁, hw₁⟩ := walk_coe_to_skeleton hH hxu w₀
    refine ⟨⟨u, v, w₁.toPath, w₁.toPath.2, huX₁, hvX₂⟩, fun z hz ↦ ?_⟩
    rw [hDeq]
    exact hw₁ z (w₁.support_toPath_subset_support hz)
  choose P' hP' using hpath
  refine ⟨P', fun i j hij ↦ ?_⟩
  have hdisj := (hD i).1.disjoint_verts_of_ne (hD j).1 (fun hEq ↦ hij (hDinj hEq))
  exact Set.disjoint_left.mpr fun z hzi hzj ↦
    Set.disjoint_left.mp hdisj (hP' i z hzi) (hP' j z hzj)

/-! ### Minimality properties of shortest disjoint paths in (6.1) -/

private def IsDisjointPathFamily (K : SimpleGraph α) (X₁ X₂ : Set α) {k : ℕ}
    (Q : Fin k → PathFromTo K X₁ X₂) : Prop :=
  Pairwise fun i j ↦ Disjoint {x | x ∈ (Q i).walk.support} {x | x ∈ (Q j).walk.support}

private def familyLength (K : SimpleGraph α) (X₁ X₂ : Set α) {k : ℕ}
    (Q : Fin k → PathFromTo K X₁ X₂) : ℕ :=
  ∑ i, (Q i).walk.length

private theorem isDisjointPathFamily_update {K : SimpleGraph α} {X₁ X₂ : Set α} {k : ℕ}
    {Q : Fin k → PathFromTo K X₁ X₂} (hQ : IsDisjointPathFamily K X₁ X₂ Q)
    (i : Fin k) (p : PathFromTo K X₁ X₂) (hsub : ∀ z ∈ p.walk.support, z ∈ (Q i).walk.support) :
    IsDisjointPathFamily K X₁ X₂ (Function.update Q i p) := by
  classical
  intro a b hab
  by_cases ha : a = i
  · subst ha
    have hb : b ≠ a := hab.symm
    change Disjoint {x | x ∈ (Function.update Q a p a).walk.support}
      {x | x ∈ (Function.update Q a p b).walk.support}
    rw [Function.update_self, Function.update_of_ne hb]
    exact Set.disjoint_left.mpr fun z hza hzb ↦
      Set.disjoint_left.mp (hQ hab) (hsub z hza) hzb
  · by_cases hb : b = i
    · subst hb
      change Disjoint {x | x ∈ (Function.update Q b p a).walk.support}
        {x | x ∈ (Function.update Q b p b).walk.support}
      rw [Function.update_self, Function.update_of_ne ha]
      exact Set.disjoint_left.mpr fun z hza hzb ↦
        Set.disjoint_left.mp (hQ hab) hza (hsub z hzb)
    · change Disjoint {x | x ∈ (Function.update Q i p a).walk.support}
        {x | x ∈ (Function.update Q i p b).walk.support}
      rw [Function.update_of_ne ha, Function.update_of_ne hb]
      exact hQ hab

private theorem familyLength_update_lt {K : SimpleGraph α} {X₁ X₂ : Set α} {k : ℕ}
    (Q : Fin k → PathFromTo K X₁ X₂) (i : Fin k) (p : PathFromTo K X₁ X₂)
    (hlt : p.walk.length < (Q i).walk.length) :
    familyLength K X₁ X₂ (Function.update Q i p) < familyLength K X₁ X₂ Q := by
  classical
  unfold familyLength
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i),
    ← Finset.sum_erase_add Finset.univ (fun j ↦ (Q j).walk.length) (Finset.mem_univ i)]
  have hsum :
      ∑ x ∈ Finset.univ.erase i, (Function.update Q i p x).walk.length =
        ∑ x ∈ Finset.univ.erase i, (Q x).walk.length := by
    refine Finset.sum_congr rfl fun x hx ↦ ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hx)]
  rw [hsum, Function.update_self]
  exact Nat.add_lt_add_left hlt _

private theorem exists_min_disjointPathFamily {K : SimpleGraph α} {X₁ X₂ : Set α} {k : ℕ}
    (h : HasDisjointPaths K X₁ X₂ k) :
    ∃ Q : Fin k → PathFromTo K X₁ X₂,
      IsDisjointPathFamily K X₁ X₂ Q ∧
      ∀ Q' : Fin k → PathFromTo K X₁ X₂,
        IsDisjointPathFamily K X₁ X₂ Q' → familyLength K X₁ X₂ Q ≤ familyLength K X₁ X₂ Q' := by
  obtain ⟨Q₀, hQ₀⟩ := h
  have hne :
      {n : ℕ | ∃ Q : Fin k → PathFromTo K X₁ X₂,
        IsDisjointPathFamily K X₁ X₂ Q ∧ familyLength K X₁ X₂ Q = n}.Nonempty :=
    ⟨familyLength K X₁ X₂ Q₀, Q₀, hQ₀, rfl⟩
  obtain ⟨n, ⟨Q, hQ, rfl⟩, hmin⟩ := WellFounded.has_min Nat.lt_wfRel.wf _ hne
  refine ⟨Q, hQ, fun Q' hQ' ↦ ?_⟩
  by_contra hlt
  exact hmin (familyLength K X₁ X₂ Q') ⟨Q', hQ', rfl⟩ (Nat.lt_of_not_ge hlt)

private theorem min_family_mem_X₁_eq_first {K : SimpleGraph α} {X₁ X₂ : Set α} {k : ℕ}
    {Q : Fin k → PathFromTo K X₁ X₂} (hQ : IsDisjointPathFamily K X₁ X₂ Q)
    (hmin : ∀ Q' : Fin k → PathFromTo K X₁ X₂, IsDisjointPathFamily K X₁ X₂ Q' →
      familyLength K X₁ X₂ Q ≤ familyLength K X₁ X₂ Q')
    (i : Fin k) {v : α} (hv : v ∈ (Q i).walk.support) (hvX₁ : v ∈ X₁) :
    v = (Q i).first := by
  classical
  by_contra hne
  let w' := (Q i).walk.dropUntil v hv
  let p' : PathFromTo K X₁ X₂ :=
    ⟨v, (Q i).last, w', (Q i).isPath.dropUntil hv, hvX₁, (Q i).last_mem⟩
  have hsub : ∀ z ∈ p'.walk.support, z ∈ (Q i).walk.support :=
    fun _ hz ↦ (Q i).walk.support_dropUntil_subset_support hv hz
  have hlt : p'.walk.length < (Q i).walk.length :=
    Walk.length_dropUntil_lt_length hv hne
  exact absurd (hmin _ (isDisjointPathFamily_update hQ i p' hsub))
    (not_le_of_gt (familyLength_update_lt Q i p' hlt))

private theorem min_family_mem_X₂_eq_last {K : SimpleGraph α} {X₁ X₂ : Set α} {k : ℕ}
    {Q : Fin k → PathFromTo K X₁ X₂} (hQ : IsDisjointPathFamily K X₁ X₂ Q)
    (hmin : ∀ Q' : Fin k → PathFromTo K X₁ X₂, IsDisjointPathFamily K X₁ X₂ Q' →
      familyLength K X₁ X₂ Q ≤ familyLength K X₁ X₂ Q')
    (i : Fin k) {v : α} (hv : v ∈ (Q i).walk.support) (hvX₂ : v ∈ X₂) :
    v = (Q i).last := by
  classical
  by_contra hne
  let w' := (Q i).walk.takeUntil v hv
  let p' : PathFromTo K X₁ X₂ :=
    ⟨(Q i).first, v, w', (Q i).isPath.takeUntil hv, (Q i).first_mem, hvX₂⟩
  have hsub : ∀ z ∈ p'.walk.support, z ∈ (Q i).walk.support :=
    fun _ hz ↦ (Q i).walk.support_takeUntil_subset_support hv hz
  have hlt : p'.walk.length < (Q i).walk.length :=
    Walk.length_takeUntil_lt_length hv hne
  exact absurd (hmin _ (isDisjointPathFamily_update hQ i p' hsub))
    (not_le_of_gt (familyLength_update_lt Q i p' hlt))

private theorem min_family_consecutive_of_adj {K : SimpleGraph α} {X₁ X₂ : Set α} {k : ℕ}
    {Q : Fin k → PathFromTo K X₁ X₂} (hQ : IsDisjointPathFamily K X₁ X₂ Q)
    (hmin : ∀ Q' : Fin k → PathFromTo K X₁ X₂, IsDisjointPathFamily K X₁ X₂ Q' →
      familyLength K X₁ X₂ Q ≤ familyLength K X₁ X₂ Q')
    (i : Fin k) {a b : ℕ} (hab : a < b) (hb : b ≤ (Q i).walk.length)
    (hadj : K.Adj ((Q i).walk.getVert a) ((Q i).walk.getVert b)) :
    b = a + 1 := by
  classical
  by_contra hne
  have hab1 : a + 1 < b := Nat.lt_of_le_of_ne hab (Ne.symm hne)
  let w₀ := ((Q i).walk.take a).append (Walk.cons hadj ((Q i).walk.drop b))
  let p' : PathFromTo K X₁ X₂ :=
    ⟨(Q i).first, (Q i).last, w₀.toPath, w₀.toPath.2, (Q i).first_mem, (Q i).last_mem⟩
  have hsub₀ : ∀ z ∈ w₀.support, z ∈ (Q i).walk.support := by
    intro z hz
    rw [Walk.mem_support_append_iff] at hz
    rcases hz with hz | hz
    · rw [Walk.support_take] at hz
      exact List.mem_of_mem_take hz
    · rw [Walk.support_cons, List.mem_cons] at hz
      rcases hz with rfl | hz
      · exact Walk.getVert_mem_support _ _
      · rw [Walk.drop_support_eq_support_drop_min] at hz
        exact List.mem_of_mem_drop hz
  have hsub : ∀ z ∈ p'.walk.support, z ∈ (Q i).walk.support :=
    fun z hz ↦ hsub₀ z (w₀.support_toPath_subset_support hz)
  have hlen₀ : w₀.length < (Q i).walk.length := by
    simp only [w₀, Walk.length_append, Walk.take_length, Walk.length_cons, Walk.drop_length]
    omega
  have hlt : p'.walk.length < (Q i).walk.length :=
    (Walk.length_bypass_le_length w₀).trans_lt hlen₀
  exact absurd (hmin _ (isDisjointPathFamily_update hQ i p' hsub))
    (not_le_of_gt (familyLength_update_lt Q i p' hlt))

/-! ### Darts and patch pairings for (6.1) -/

private abbrev DartIdx {K : SimpleGraph α} {X₁ X₂ : Set α} {k : ℕ}
    (Q : Fin k → PathFromTo K X₁ X₂) : Type :=
  Σ i : Fin k, Fin (Q i).walk.length

private def dartMinus {K : SimpleGraph α} {X₁ X₂ : Set α} {k : ℕ}
    (Q : Fin k → PathFromTo K X₁ X₂) (d : DartIdx Q) : α :=
  (Q d.1).walk.getVert d.2.1

private def dartPlus {K : SimpleGraph α} {X₁ X₂ : Set α} {k : ℕ}
    (Q : Fin k → PathFromTo K X₁ X₂) (d : DartIdx Q) : α :=
  (Q d.1).walk.getVert (d.2.1 + 1)

private theorem dartMinus_mem_support {K : SimpleGraph α} {X₁ X₂ : Set α} {k : ℕ}
    (Q : Fin k → PathFromTo K X₁ X₂) (d : DartIdx Q) :
    dartMinus Q d ∈ (Q d.1).walk.support :=
  Walk.getVert_mem_support _ _

private theorem dartPlus_mem_support {K : SimpleGraph α} {X₁ X₂ : Set α} {k : ℕ}
    (Q : Fin k → PathFromTo K X₁ X₂) (d : DartIdx Q) :
    dartPlus Q d ∈ (Q d.1).walk.support :=
  Walk.getVert_mem_support _ _

private theorem eq_of_mem_support_of_disjoint {K : SimpleGraph α} {X₁ X₂ : Set α} {k : ℕ}
    {Q : Fin k → PathFromTo K X₁ X₂} (hQ : IsDisjointPathFamily K X₁ X₂ Q)
    {i j : Fin k} {v : α} (hvi : v ∈ (Q i).walk.support) (hvj : v ∈ (Q j).walk.support) :
    i = j := by
  by_contra hij
  exact Set.disjoint_left.mp (hQ hij) hvi hvj

private theorem dartMinus_injective {K : SimpleGraph α} {X₁ X₂ : Set α} {k : ℕ}
    {Q : Fin k → PathFromTo K X₁ X₂} (hQ : IsDisjointPathFamily K X₁ X₂ Q) :
    Function.Injective (dartMinus Q) := by
  rintro ⟨i₁, m₁⟩ ⟨i₂, m₂⟩ h
  have hi : i₁ = i₂ :=
    eq_of_mem_support_of_disjoint hQ (dartMinus_mem_support Q ⟨i₁, m₁⟩)
      (h ▸ dartMinus_mem_support Q ⟨i₂, m₂⟩)
  subst hi
  have hm : m₁.1 = m₂.1 :=
    (Q i₁).isPath.getVert_injOn (by simp [m₁.2.le]) (by simp [m₂.2.le]) h
  exact Sigma.ext rfl (heq_of_eq (Fin.ext hm))

private theorem dartPlus_injective {K : SimpleGraph α} {X₁ X₂ : Set α} {k : ℕ}
    {Q : Fin k → PathFromTo K X₁ X₂} (hQ : IsDisjointPathFamily K X₁ X₂ Q) :
    Function.Injective (dartPlus Q) := by
  rintro ⟨i₁, m₁⟩ ⟨i₂, m₂⟩ h
  have hi : i₁ = i₂ :=
    eq_of_mem_support_of_disjoint hQ (dartPlus_mem_support Q ⟨i₁, m₁⟩)
      (h ▸ dartPlus_mem_support Q ⟨i₂, m₂⟩)
  subst hi
  have hm1 : m₁.1 + 1 = m₂.1 + 1 :=
    (Q i₁).isPath.getVert_injOn (by simp [Nat.succ_le_of_lt m₁.2])
      (by simp [Nat.succ_le_of_lt m₂.2]) h
  exact Sigma.ext rfl (heq_of_eq (Fin.ext (Nat.succ.inj hm1)))

private theorem dartMinus_ne_last {K : SimpleGraph α} {X₁ X₂ : Set α} {k : ℕ}
    {Q : Fin k → PathFromTo K X₁ X₂} (hQ : IsDisjointPathFamily K X₁ X₂ Q)
    (d : DartIdx Q) (i : Fin k) : dartMinus Q d ≠ (Q i).last := by
  intro h
  have hmem : dartMinus Q d ∈ (Q i).walk.support := by
    rw [h]
    exact (Q i).walk.end_mem_support
  have hi : d.1 = i :=
    eq_of_mem_support_of_disjoint hQ (dartMinus_mem_support Q d) hmem
  rcases d with ⟨j, m⟩
  subst hi
  have hlen : (Q j).walk.getVert m.1 = (Q j).walk.getVert (Q j).walk.length := by
    simpa [dartMinus] using h
  have hm := (Q j).isPath.getVert_injOn (by simp [m.2.le]) (by simp) hlen
  exact m.2.ne hm

private theorem dartPlus_ne_first {K : SimpleGraph α} {X₁ X₂ : Set α} {k : ℕ}
    {Q : Fin k → PathFromTo K X₁ X₂} (hQ : IsDisjointPathFamily K X₁ X₂ Q)
    (d : DartIdx Q) (i : Fin k) : dartPlus Q d ≠ (Q i).first := by
  intro h
  have hmem : dartPlus Q d ∈ (Q i).walk.support := by
    rw [h]
    exact (Q i).walk.start_mem_support
  have hi : d.1 = i :=
    eq_of_mem_support_of_disjoint hQ (dartPlus_mem_support Q d) hmem
  rcases d with ⟨j, m⟩
  subst hi
  have hzero : (Q j).walk.getVert (m.1 + 1) = (Q j).walk.getVert 0 := by
    simpa [dartPlus] using h
  have hm := (Q j).isPath.getVert_injOn (by simp [Nat.succ_le_of_lt m.2]) (by simp) hzero
  exact Nat.succ_ne_zero m.1 hm

private theorem dart_adj {K : SimpleGraph α} {X₁ X₂ : Set α} {k : ℕ}
    (Q : Fin k → PathFromTo K X₁ X₂) (d : DartIdx Q) :
    K.Adj (dartMinus Q d) (dartPlus Q d) :=
  Walk.adj_getVert_succ _ d.2.2

private noncomputable def dartEdge {G : Hypergraph α β} {X₁ X₂ : Set α} {k : ℕ}
    (Q : Fin k → PathFromTo G.skeleton X₁ X₂) (d : DartIdx Q) : β :=
  (dart_adj Q d).2.choose

private theorem dartEdge_inc_minus {G : Hypergraph α β} {X₁ X₂ : Set α} {k : ℕ}
    (Q : Fin k → PathFromTo G.skeleton X₁ X₂) (d : DartIdx Q) :
    G.Inc (dartEdge Q d) (dartMinus Q d) :=
  (dart_adj Q d).2.choose_spec.1

private theorem dartEdge_inc_plus {G : Hypergraph α β} {X₁ X₂ : Set α} {k : ℕ}
    (Q : Fin k → PathFromTo G.skeleton X₁ X₂) (d : DartIdx Q) :
    G.Inc (dartEdge Q d) (dartPlus Q d) :=
  (dart_adj Q d).2.choose_spec.2

private theorem dartEdge_mem {G : Hypergraph α β} {X₁ X₂ : Set α} {k : ℕ}
    (Q : Fin k → PathFromTo G.skeleton X₁ X₂) (d : DartIdx Q) :
    dartEdge Q d ∈ G.edgeSet :=
  G.edge_mem_of_inc (dartEdge_inc_minus Q d)

private def dartSetA {G : Hypergraph α β} {X₁ X₂ : Set α} {k : ℕ}
    (Q : Fin k → PathFromTo G.skeleton X₁ X₂) (e : β) : Set α :=
  dartMinus Q '' {d | dartEdge Q d = e}

private def dartSetB {G : Hypergraph α β} {X₁ X₂ : Set α} {k : ℕ}
    (Q : Fin k → PathFromTo G.skeleton X₁ X₂) (e : β) : Set α :=
  dartPlus Q '' {d | dartEdge Q d = e}

private theorem dartSetA_subset_ends {G : Hypergraph α β} {X₁ X₂ : Set α} {k : ℕ}
    (Q : Fin k → PathFromTo G.skeleton X₁ X₂) (e : β) :
    dartSetA Q e ⊆ G.ends e := by
  rintro _ ⟨d, rfl, rfl⟩
  exact dartEdge_inc_minus Q d

private theorem dartSetB_subset_ends {G : Hypergraph α β} {X₁ X₂ : Set α} {k : ℕ}
    (Q : Fin k → PathFromTo G.skeleton X₁ X₂) (e : β) :
    dartSetB Q e ⊆ G.ends e := by
  rintro _ ⟨d, rfl, rfl⟩
  exact dartEdge_inc_plus Q d

private theorem dartSetA_ncard_eq_dartSetB_ncard {G : Hypergraph α β} {X₁ X₂ : Set α} {k : ℕ}
    {Q : Fin k → PathFromTo G.skeleton X₁ X₂} (hQ : IsDisjointPathFamily G.skeleton X₁ X₂ Q)
    (e : β) : (dartSetA Q e).ncard = (dartSetB Q e).ncard := by
  rw [dartSetA, dartSetB, Set.ncard_image_of_injective _ (dartMinus_injective hQ),
    Set.ncard_image_of_injective _ (dartPlus_injective hQ)]

private theorem disjoint_dartSetA_dartSetB {G : Hypergraph α β} {X₁ X₂ : Set α} {k : ℕ}
    {Q : Fin k → PathFromTo G.skeleton X₁ X₂} (hQ : IsDisjointPathFamily G.skeleton X₁ X₂ Q)
    (hmin : ∀ Q' : Fin k → PathFromTo G.skeleton X₁ X₂,
      IsDisjointPathFamily G.skeleton X₁ X₂ Q' →
      familyLength G.skeleton X₁ X₂ Q ≤ familyLength G.skeleton X₁ X₂ Q')
    (e : β) : Disjoint (dartSetA Q e) (dartSetB Q e) := by
  refine Set.disjoint_left.mpr ?_
  rintro _ ⟨d₁, hd₁, rfl⟩ ⟨d₂, hd₂, hEq⟩
  have hi : d₁.1 = d₂.1 :=
    eq_of_mem_support_of_disjoint hQ (dartMinus_mem_support Q d₁)
      (hEq.symm ▸ dartPlus_mem_support Q d₂)
  rcases d₁ with ⟨i, m₁⟩
  rcases d₂ with ⟨j, m₂⟩
  subst hi
  have hm : m₁.1 = m₂.1 + 1 :=
    (Q i).isPath.getVert_injOn (by simp [m₁.2.le]) (by simp [Nat.succ_le_of_lt m₂.2]) hEq.symm
  have hx : G.Inc e ((Q i).walk.getVert m₂.1) := hd₂ ▸ dartEdge_inc_minus Q ⟨i, m₂⟩
  have hy : G.Inc e ((Q i).walk.getVert (m₁.1 + 1)) := hd₁ ▸ dartEdge_inc_plus Q ⟨i, m₁⟩
  have hlt : m₂.1 < m₁.1 + 1 := by omega
  have hle : m₁.1 + 1 ≤ (Q i).walk.length := Nat.succ_le_of_lt m₁.2
  have hne : (Q i).walk.getVert m₂.1 ≠ (Q i).walk.getVert (m₁.1 + 1) := by
    intro hxy
    have hEqIdx := (Q i).isPath.getVert_injOn (by simp [m₂.2.le]) (by simp [hle]) hxy
    omega
  have hadj : G.skeleton.Adj ((Q i).walk.getVert m₂.1) ((Q i).walk.getVert (m₁.1 + 1)) :=
    ⟨hne, e, hx, hy⟩
  have hcons := min_family_consecutive_of_adj hQ hmin i hlt hle hadj
  omega

private theorem exists_realization_and_dartPerm {P : Patchwork Ω α β} (hrob : P.IsRobust)
    {X₁ X₂ : Set α} {k : ℕ} {Q : Fin k → PathFromTo P.G.toHypergraph.skeleton X₁ X₂}
    (hQ : IsDisjointPathFamily P.G.toHypergraph.skeleton X₁ X₂ Q)
    (hmin : ∀ Q' : Fin k → PathFromTo P.G.toHypergraph.skeleton X₁ X₂,
      IsDisjointPathFamily P.G.toHypergraph.skeleton X₁ X₂ Q' →
      familyLength P.G.toHypergraph.skeleton X₁ X₂ Q ≤
        familyLength P.G.toHypergraph.skeleton X₁ X₂ Q') :
    ∃ (H : (⊤ : SimpleGraph α).Subgraph) (π : DartIdx Q → DartIdx Q),
      P.IsRealization H ∧ Function.Injective π ∧
      (∀ x y, H.Adj x y ↔ ∃ d : DartIdx Q,
        (x = dartMinus Q d ∧ y = dartPlus Q (π d)) ∨
        (y = dartMinus Q d ∧ x = dartPlus Q (π d))) := by
  classical
  have hδ_ex : ∀ e ∈ P.G.edgeSet, ∃ δe ∈ P.Δ e,
      IsPairing (P.Δ e).verts δe ∧
      Pairs (P.Δ e).verts δe (dartSetA Q e) (dartSetB Q e) := by
    intro e he
    have hA : dartSetA Q e ⊆ (P.Δ e).verts := by
      rw [P.Δ_verts e he]
      exact dartSetA_subset_ends Q e
    have hB : dartSetB Q e ⊆ (P.Δ e).verts := by
      rw [P.Δ_verts e he]
      exact dartSetB_subset_ends Q e
    exact (hrob e he).exists_pairing (dartSetA Q e) hA (dartSetB Q e) hB
      (dartSetA_ncard_eq_dartSetB_ncard hQ e) (disjoint_dartSetA_dartSetB hQ hmin e)
  let δ : β → (⊤ : SimpleGraph α).Subgraph := fun e ↦
    if he : e ∈ P.G.edgeSet then (hδ_ex e he).choose else emptySubgraph ∅
  have hδ_mem : ∀ e ∈ P.G.edgeSet, δ e ∈ P.Δ e := by
    intro e he
    dsimp only [δ]
    rw [dite_eq_left_of_eq_true (eq_true he)]
    exact (hδ_ex e he).choose_spec.1
  have hδ_pair : ∀ e ∈ P.G.edgeSet, IsPairing (P.Δ e).verts (δ e) := by
    intro e he
    dsimp only [δ]
    rw [dite_eq_left_of_eq_true (eq_true he)]
    exact (hδ_ex e he).choose_spec.2.1
  have hδ_pairs : ∀ e ∈ P.G.edgeSet,
      Pairs (P.Δ e).verts (δ e) (dartSetA Q e) (dartSetB Q e) := by
    intro e he
    dsimp only [δ]
    rw [dite_eq_left_of_eq_true (eq_true he)]
    exact (hδ_ex e he).choose_spec.2.2
  have hfin : ∀ e ∈ P.G.edgeSet, (P.Δ e).verts.Finite := by
    intro e he
    rw [P.Δ_verts e he]
    exact P.G.vertexSet_finite.subset fun _ hv ↦ P.G.vertex_mem_of_inc hv
  have hδ_unique : ∀ e ∈ P.G.edgeSet, ∀ a b c, (δ e).Adj a b → (δ e).Adj a c → b = c :=
    fun e he ↦ ((isPairing_iff (hfin e he)).mp (hδ_pair e he)).2
  have hδ_ab : ∀ e ∈ P.G.edgeSet, ∀ u v, (δ e).Adj u v →
      (u ∈ dartSetA Q e ∧ v ∈ dartSetB Q e) ∨ (u ∈ dartSetB Q e ∧ v ∈ dartSetA Q e) :=
    fun e he ↦ ((pairs_iff_of_isPairing (hfin e he) (hδ_pair e he)).mp (hδ_pairs e he)).2.2.2.1
  have hδ_deg : ∀ e ∈ P.G.edgeSet, ∀ v ∈ dartSetA Q e ∪ dartSetB Q e, ∃ w, (δ e).Adj v w :=
    fun e he ↦ ((pairs_iff_of_isPairing (hfin e he) (hδ_pair e he)).mp (hδ_pairs e he)).2.2.2.2
  have hπ_ex : ∀ d : DartIdx Q, ∃ d' : DartIdx Q,
      dartEdge Q d' = dartEdge Q d ∧
      (δ (dartEdge Q d)).Adj (dartMinus Q d) (dartPlus Q d') := by
    intro d
    have he : dartEdge Q d ∈ P.G.edgeSet := dartEdge_mem Q d
    have hmemA : dartMinus Q d ∈ dartSetA Q (dartEdge Q d) := ⟨d, rfl, rfl⟩
    obtain ⟨w, hw⟩ := hδ_deg (dartEdge Q d) he (dartMinus Q d) (Or.inl hmemA)
    rcases hδ_ab (dartEdge Q d) he (dartMinus Q d) w hw with ⟨_, hwB⟩ | ⟨hB, _⟩
    · obtain ⟨d', hd', rfl⟩ := hwB
      exact ⟨d', hd', hw⟩
    · exact False.elim (Set.disjoint_left.mp
        (disjoint_dartSetA_dartSetB hQ hmin (dartEdge Q d)) hmemA hB)
  choose π hπ_edge hπ_adj using hπ_ex
  have hπ_inj : Function.Injective π := by
    intro d₁ d₂ hEq
    have heEq : dartEdge Q d₁ = dartEdge Q d₂ := by
      rw [← hπ_edge d₁, hEq, hπ_edge d₂]
    have he₁ : dartEdge Q d₁ ∈ P.G.edgeSet := dartEdge_mem Q d₁
    have hadj₁ : (δ (dartEdge Q d₁)).Adj (dartPlus Q (π d₁)) (dartMinus Q d₁) :=
      (hπ_adj d₁).symm
    have hadj₂ : (δ (dartEdge Q d₁)).Adj (dartPlus Q (π d₁)) (dartMinus Q d₂) := by
      rw [hEq, heEq]
      exact (hπ_adj d₂).symm
    exact dartMinus_injective hQ (hδ_unique (dartEdge Q d₁) he₁ _ _ _ hadj₁ hadj₂)
  let H := realizationOf P.G.toHypergraph δ
  refine ⟨H, π, ⟨δ, hδ_mem, rfl⟩, hπ_inj, fun x y ↦ ?_⟩
  simp only [H, realizationOf_adj]
  constructor
  · rintro ⟨e, he, hxy⟩
    rcases hδ_ab e he x y hxy with ⟨hxA, _⟩ | ⟨_, hyA⟩
    · obtain ⟨d, rfl, rfl⟩ := hxA
      have hyEq : y = dartPlus Q (π d) :=
        hδ_unique (dartEdge Q d) he (dartMinus Q d) y (dartPlus Q (π d)) hxy (hπ_adj d)
      exact ⟨d, Or.inl ⟨rfl, hyEq⟩⟩
    · obtain ⟨d, rfl, rfl⟩ := hyA
      have hxEq : x = dartPlus Q (π d) :=
        hδ_unique (dartEdge Q d) he (dartMinus Q d) x (dartPlus Q (π d)) hxy.symm (hπ_adj d)
      exact ⟨d, Or.inr ⟨rfl, hxEq⟩⟩
  · rintro ⟨d, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact ⟨dartEdge Q d, dartEdge_mem Q d, hπ_adj d⟩
    · exact ⟨dartEdge Q d, dartEdge_mem Q d, (hπ_adj d).symm⟩

/-! ### Rerouting paths patch by patch -/

private theorem reroute_step_adj {K : SimpleGraph α} {X₁ X₂ : Set α} {k : ℕ}
    {Q : Fin k → PathFromTo K X₁ X₂} {H : (⊤ : SimpleGraph α).Subgraph}
    {π : DartIdx Q → DartIdx Q}
    (hstep : ∀ d : DartIdx Q, H.spanningCoe.Adj (dartMinus Q d) (dartPlus Q (π d)))
    {z : α} (h : ∃ d : DartIdx Q, z = dartMinus Q d) :
    H.spanningCoe.Adj z (dartPlus Q (π h.choose)) := by
  have hz : z = dartMinus Q h.choose := h.choose_spec
  generalize h.choose = d at hz ⊢
  rw [hz]
  exact hstep d

private noncomputable def reroute {K : SimpleGraph α} {X₁ X₂ : Set α} {k : ℕ}
    (Q : Fin k → PathFromTo K X₁ X₂) {H : (⊤ : SimpleGraph α).Subgraph}
    (π : DartIdx Q → DartIdx Q)
    (hstep : ∀ d : DartIdx Q, H.spanningCoe.Adj (dartMinus Q d) (dartPlus Q (π d))) :
    ∀ (_ : ℕ) (z : α), Σ w : α, H.spanningCoe.Walk z w
  | 0, z => ⟨z, Walk.nil⟩
  | n + 1, z => by
    classical
    exact if h : ∃ d : DartIdx Q, z = dartMinus Q d then
      let r := reroute Q π hstep n (dartPlus Q (π h.choose))
      ⟨r.1, Walk.cons (reroute_step_adj hstep h) r.2⟩
    else ⟨z, Walk.nil⟩

private theorem reroute_zero {K : SimpleGraph α} {X₁ X₂ : Set α} {k : ℕ}
    (Q : Fin k → PathFromTo K X₁ X₂) {H : (⊤ : SimpleGraph α).Subgraph}
    (π : DartIdx Q → DartIdx Q)
    (hstep : ∀ d : DartIdx Q, H.spanningCoe.Adj (dartMinus Q d) (dartPlus Q (π d)))
    (z : α) : reroute Q π hstep 0 z = ⟨z, Walk.nil⟩ := rfl

private theorem reroute_succ_pos {K : SimpleGraph α} {X₁ X₂ : Set α} {k : ℕ}
    (Q : Fin k → PathFromTo K X₁ X₂) {H : (⊤ : SimpleGraph α).Subgraph}
    (π : DartIdx Q → DartIdx Q)
    (hstep : ∀ d : DartIdx Q, H.spanningCoe.Adj (dartMinus Q d) (dartPlus Q (π d)))
    (n : ℕ) {z : α} (h : ∃ d : DartIdx Q, z = dartMinus Q d) :
    reroute Q π hstep (n + 1) z =
      ⟨(reroute Q π hstep n (dartPlus Q (π h.choose))).1,
        Walk.cons (reroute_step_adj hstep h)
          (reroute Q π hstep n (dartPlus Q (π h.choose))).2⟩ := by
  dsimp only [reroute]
  rw [dite_eq_left_of_eq_true (eq_true h)]

private theorem reroute_succ_neg {K : SimpleGraph α} {X₁ X₂ : Set α} {k : ℕ}
    (Q : Fin k → PathFromTo K X₁ X₂) {H : (⊤ : SimpleGraph α).Subgraph}
    (π : DartIdx Q → DartIdx Q)
    (hstep : ∀ d : DartIdx Q, H.spanningCoe.Adj (dartMinus Q d) (dartPlus Q (π d)))
    (n : ℕ) {z : α} (h : ¬∃ d : DartIdx Q, z = dartMinus Q d) :
    reroute Q π hstep (n + 1) z = ⟨z, Walk.nil⟩ := by
  dsimp only [reroute]
  rw [dite_eq_right_of_eq_false (eq_false h)]

private theorem reroute_not_exists_or_length {K : SimpleGraph α} {X₁ X₂ : Set α} {k : ℕ}
    (Q : Fin k → PathFromTo K X₁ X₂) {H : (⊤ : SimpleGraph α).Subgraph}
    (π : DartIdx Q → DartIdx Q)
    (hstep : ∀ d : DartIdx Q, H.spanningCoe.Adj (dartMinus Q d) (dartPlus Q (π d)))
    (n : ℕ) (z : α) :
    (¬∃ d : DartIdx Q, (reroute Q π hstep n z).1 = dartMinus Q d) ∨
      (reroute Q π hstep n z).2.length = n := by
  induction n generalizing z with
  | zero => exact Or.inr rfl
  | succ n ih =>
    by_cases h : ∃ d : DartIdx Q, z = dartMinus Q d
    · rw [reroute_succ_pos Q π hstep n h]
      rcases ih (dartPlus Q (π h.choose)) with hnot | hlen
      · exact Or.inl hnot
      · exact Or.inr (by simp [hlen])
    · rw [reroute_succ_neg Q π hstep n h]
      exact Or.inl h

private theorem reroute_getVert_step {K : SimpleGraph α} {X₁ X₂ : Set α} {k : ℕ}
    (Q : Fin k → PathFromTo K X₁ X₂) {H : (⊤ : SimpleGraph α).Subgraph}
    (π : DartIdx Q → DartIdx Q)
    (hstep : ∀ d : DartIdx Q, H.spanningCoe.Adj (dartMinus Q d) (dartPlus Q (π d)))
    (n : ℕ) (z : α) {m : ℕ} (hm : m < (reroute Q π hstep n z).2.length) :
    ∃ d : DartIdx Q,
      (reroute Q π hstep n z).2.getVert m = dartMinus Q d ∧
      (reroute Q π hstep n z).2.getVert (m + 1) = dartPlus Q (π d) := by
  induction n generalizing z m with
  | zero =>
    rw [reroute_zero, Walk.length_nil] at hm
    omega
  | succ n ih =>
    by_cases h : ∃ d : DartIdx Q, z = dartMinus Q d
    · rw [reroute_succ_pos Q π hstep n h] at hm ⊢
      cases m with
      | zero =>
        exact ⟨h.choose, h.choose_spec, by simp⟩
      | succ m' =>
        rw [Walk.length_cons, Nat.add_lt_add_iff_right] at hm
        simpa using ih (dartPlus Q (π h.choose)) hm
    · rw [reroute_succ_neg Q π hstep n h, Walk.length_nil] at hm
      omega

private theorem reroute_support_mem {K : SimpleGraph α} {X₁ X₂ : Set α} {k : ℕ}
    (Q : Fin k → PathFromTo K X₁ X₂) {H : (⊤ : SimpleGraph α).Subgraph}
    (π : DartIdx Q → DartIdx Q)
    (hstep : ∀ d : DartIdx Q, H.spanningCoe.Adj (dartMinus Q d) (dartPlus Q (π d)))
    (n : ℕ) {z : α} (hz : ∃ i, z ∈ (Q i).walk.support)
    {v : α} (hv : v ∈ (reroute Q π hstep n z).2.support) :
    ∃ i, v ∈ (Q i).walk.support := by
  induction n generalizing z with
  | zero =>
    rw [reroute_zero, Walk.mem_support_nil_iff] at hv
    exact hv ▸ hz
  | succ n ih =>
    by_cases h : ∃ d : DartIdx Q, z = dartMinus Q d
    · rw [reroute_succ_pos Q π hstep n h, Walk.support_cons, List.mem_cons] at hv
      rcases hv with rfl | hv
      · exact hz
      · exact ih ⟨(π h.choose).1, dartPlus_mem_support Q (π h.choose)⟩ hv
    · rw [reroute_succ_neg Q π hstep n h, Walk.mem_support_nil_iff] at hv
      exact hv ▸ hz

private theorem reroute_getVert_inj {K : SimpleGraph α} {X₁ X₂ : Set α} {k : ℕ}
    {Q : Fin k → PathFromTo K X₁ X₂} (hQ : IsDisjointPathFamily K X₁ X₂ Q)
    {H : (⊤ : SimpleGraph α).Subgraph} {π : DartIdx Q → DartIdx Q}
    (hπ_inj : Function.Injective π)
    (hstep : ∀ d : DartIdx Q, H.spanningCoe.Adj (dartMinus Q d) (dartPlus Q (π d)))
    (n : ℕ) {i₁ i₂ : Fin k} {m₁ m₂ : ℕ}
    (hm₁ : m₁ ≤ (reroute Q π hstep n (Q i₁).first).2.length)
    (hm₂ : m₂ ≤ (reroute Q π hstep n (Q i₂).first).2.length)
    (hEq : (reroute Q π hstep n (Q i₁).first).2.getVert m₁ =
      (reroute Q π hstep n (Q i₂).first).2.getVert m₂) :
    i₁ = i₂ ∧ m₁ = m₂ := by
  induction m₁ generalizing m₂ with
  | zero =>
    cases m₂ with
    | zero =>
      simp only [Walk.getVert_zero] at hEq
      refine ⟨eq_of_mem_support_of_disjoint hQ (Q i₁).walk.start_mem_support ?_, rfl⟩
      rw [hEq]
      exact (Q i₂).walk.start_mem_support
    | succ m₂' =>
      exfalso
      obtain ⟨d₂, _, hd₂⟩ := reroute_getVert_step Q π hstep n (Q i₂).first
        (Nat.lt_of_succ_le hm₂)
      rw [Walk.getVert_zero, hd₂] at hEq
      exact dartPlus_ne_first hQ (π d₂) i₁ hEq.symm
  | succ m₁' ih =>
    cases m₂ with
    | zero =>
      exfalso
      obtain ⟨d₁, _, hd₁⟩ := reroute_getVert_step Q π hstep n (Q i₁).first
        (Nat.lt_of_succ_le hm₁)
      rw [Walk.getVert_zero, hd₁] at hEq
      exact dartPlus_ne_first hQ (π d₁) i₂ hEq
    | succ m₂' =>
      obtain ⟨d₁, hd₁_minus, hd₁_plus⟩ := reroute_getVert_step Q π hstep n (Q i₁).first
        (Nat.lt_of_succ_le hm₁)
      obtain ⟨d₂, hd₂_minus, hd₂_plus⟩ := reroute_getVert_step Q π hstep n (Q i₂).first
        (Nat.lt_of_succ_le hm₂)
      rw [hd₁_plus, hd₂_plus] at hEq
      have hdEq : d₁ = d₂ := hπ_inj (dartPlus_injective hQ hEq)
      have hprev : (reroute Q π hstep n (Q i₁).first).2.getVert m₁' =
          (reroute Q π hstep n (Q i₂).first).2.getVert m₂' := by
        rw [hd₁_minus, hd₂_minus, hdEq]
      obtain ⟨hi, hm⟩ := ih (Nat.le_of_succ_le hm₁) (Nat.le_of_succ_le hm₂) hprev
      exact ⟨hi, congrArg Nat.succ hm⟩

private theorem reroute_isPath {K : SimpleGraph α} {X₁ X₂ : Set α} {k : ℕ}
    {Q : Fin k → PathFromTo K X₁ X₂} (hQ : IsDisjointPathFamily K X₁ X₂ Q)
    {H : (⊤ : SimpleGraph α).Subgraph} {π : DartIdx Q → DartIdx Q}
    (hπ_inj : Function.Injective π)
    (hstep : ∀ d : DartIdx Q, H.spanningCoe.Adj (dartMinus Q d) (dartPlus Q (π d)))
    (n : ℕ) (i : Fin k) :
    (reroute Q π hstep n (Q i).first).2.IsPath := by
  rw [← Walk.IsPath.getVert_injOn_iff]
  intro a ha b hb hEq
  exact (reroute_getVert_inj hQ hπ_inj hstep n ha hb hEq).2

private theorem reroute_disjoint_support {K : SimpleGraph α} {X₁ X₂ : Set α} {k : ℕ}
    {Q : Fin k → PathFromTo K X₁ X₂} (hQ : IsDisjointPathFamily K X₁ X₂ Q)
    {H : (⊤ : SimpleGraph α).Subgraph} {π : DartIdx Q → DartIdx Q}
    (hπ_inj : Function.Injective π)
    (hstep : ∀ d : DartIdx Q, H.spanningCoe.Adj (dartMinus Q d) (dartPlus Q (π d)))
    (n : ℕ) {i₁ i₂ : Fin k} (hne : i₁ ≠ i₂) :
    Disjoint {v | v ∈ (reroute Q π hstep n (Q i₁).first).2.support}
      {v | v ∈ (reroute Q π hstep n (Q i₂).first).2.support} := by
  refine Set.disjoint_left.mpr fun v hv₁ hv₂ ↦ hne ?_
  rw [Set.mem_ofPred_eq, Walk.mem_support_iff_exists_getVert] at hv₁ hv₂
  obtain ⟨m₁, rfl, hm₁⟩ := hv₁
  obtain ⟨m₂, hEq, hm₂⟩ := hv₂
  exact (reroute_getVert_inj hQ hπ_inj hstep n hm₁ hm₂ hEq.symm).1

private theorem walk_toSubgraph_adj_getVert_succ {G : SimpleGraph α} {u v : α}
    (w : G.Walk u v) {m : ℕ} (hm : m < w.length) :
    w.toSubgraph.Adj (w.getVert m) (w.getVert (m + 1)) := by
  induction w generalizing m with
  | nil =>
    rw [Walk.length_nil] at hm
    omega
  | cons h p ih =>
    cases m with
    | zero =>
      simp [Walk.toSubgraph]
    | succ m' =>
      rw [Walk.length_cons, Nat.add_lt_add_iff_right] at hm
      simpa [Walk.toSubgraph] using Or.inr (ih hm)

private theorem walk_spanningCoe_reachable_coe {H : (⊤ : SimpleGraph α).Subgraph} {u v : α}
    (hu : u ∈ H.verts) (w : H.spanningCoe.Walk u v) {z : α} (hz : z ∈ w.support) :
    ∃ hzH : z ∈ H.verts, H.coe.Reachable ⟨u, hu⟩ ⟨z, hzH⟩ := by
  induction w with
  | nil =>
    rw [Walk.mem_support_nil_iff] at hz
    subst hz
    exact ⟨hu, Reachable.refl _⟩
  | @cons a b c hab p ih =>
    rw [Walk.support_cons, List.mem_cons] at hz
    rcases hz with rfl | hz
    · exact ⟨hu, Reachable.refl _⟩
    · have hb : b ∈ H.verts := H.edge_vert hab.symm
      obtain ⟨hzH, hreach⟩ := ih hb hz
      exact ⟨hzH, (Adj.reachable hab.coe).trans hreach⟩

/-- Condition `(i)'` of (6.1) implies condition (iii) for a robust `Ω`-patchwork
(Graph Minors IV, page 242). -/
theorem theorem_6_1_disjointPaths_imp_iii {P : Patchwork Ω α β} (hrob : P.IsRobust)
    {X₁ X₂ : Set α} (hX₁ : X₁ ⊆ P.G.vertexSet) (_hX₂ : X₂ ⊆ P.G.vertexSet) {k : ℕ}
    (hpaths : HasDisjointPaths P.G.toHypergraph.skeleton X₁ X₂ k) :
    Theorem61Cond3 P X₁ X₂ k := by
  classical
  let K := P.G.toHypergraph.skeleton
  obtain ⟨Q, hQ, hmin⟩ := exists_min_disjointPathFamily hpaths
  obtain ⟨H, π, hH, hπ_inj, hadj_iff⟩ := exists_realization_and_dartPerm hrob hQ hmin
  have hstep : ∀ d : DartIdx Q, H.spanningCoe.Adj (dartMinus Q d) (dartPlus Q (π d)) :=
    fun d ↦ (hadj_iff _ _).mpr ⟨d, Or.inl ⟨rfl, rfl⟩⟩
  let n := familyLength K X₁ X₂ Q + 1
  let endV : Fin k → α := fun i ↦ (reroute Q π hstep n (Q i).first).1
  let W : ∀ i : Fin k, H.spanningCoe.Walk (Q i).first (endV i) :=
    fun i ↦ (reroute Q π hstep n (Q i).first).2
  let StepIdx := Σ i : Fin k, Fin (W i).length
  have hstep_ex : ∀ s : StepIdx, ∃ d : DartIdx Q,
      (W s.1).getVert s.2.1 = dartMinus Q d ∧
      (W s.1).getVert (s.2.1 + 1) = dartPlus Q (π d) :=
    fun s ↦ reroute_getVert_step Q π hstep n (Q s.1).first s.2.2
  choose stepDart hstep_minus hstep_plus using hstep_ex
  have hstepDart_inj : Function.Injective stepDart := by
    rintro ⟨i₁, m₁⟩ ⟨i₂, m₂⟩ hEq
    have hvert : (W i₁).getVert m₁.1 = (W i₂).getVert m₂.1 := by
      rw [hstep_minus ⟨i₁, m₁⟩, hstep_minus ⟨i₂, m₂⟩, hEq]
    obtain ⟨hi, hm⟩ := reroute_getVert_inj hQ hπ_inj hstep n m₁.2.le m₂.2.le hvert
    subst hi
    exact Sigma.ext rfl (heq_of_eq (Fin.ext hm))
  have hsum_le : ∑ i : Fin k, (W i).length ≤ familyLength K X₁ X₂ Q := by
    have hcard := Fintype.card_le_of_injective stepDart hstepDart_inj
    simpa [StepIdx, DartIdx, familyLength] using hcard
  have hlen_lt : ∀ i : Fin k, (W i).length < n := by
    intro i
    have hle : (W i).length ≤ ∑ j : Fin k, (W j).length := by
      rw [← Finset.sum_erase_add Finset.univ (fun j ↦ (W j).length) (Finset.mem_univ i)]
      exact Nat.le_add_left _ _
    exact Nat.lt_succ_of_le (hle.trans hsum_le)
  have hend_not_minus : ∀ i : Fin k, ¬∃ d : DartIdx Q, endV i = dartMinus Q d := by
    intro i
    rcases reroute_not_exists_or_length Q π hstep n (Q i).first with hnot | hlen
    · exact hnot
    · exact absurd hlen (hlen_lt i).ne
  have hend_eq_last : ∀ i : Fin k, ∃ j : Fin k, endV i = (Q j).last := by
    intro i
    obtain ⟨j, hj⟩ := reroute_support_mem Q π hstep n ⟨i, (Q i).walk.start_mem_support⟩
      (W i).end_mem_support
    rw [Walk.mem_support_iff_exists_getVert] at hj
    obtain ⟨m, hmEq, hmle⟩ := hj
    rcases hmle.lt_or_eq with hmlt | rfl
    · exfalso
      exact hend_not_minus i ⟨⟨j, ⟨m, hmlt⟩⟩, hmEq.symm⟩
    · exact ⟨j, hmEq.symm.trans (Walk.getVert_length (Q j).walk)⟩
  have hend_mem_X₂ : ∀ i : Fin k, endV i ∈ X₂ := by
    intro i
    obtain ⟨j, hj⟩ := hend_eq_last i
    rw [hj]
    exact (Q j).last_mem
  have hH_le_K : H.spanningCoe ≤ K := fun _ _ h ↦ hH.adj_imp_skeleton_adj h
  let Q' : Fin k → PathFromTo K X₁ X₂ := fun i ↦
    { first := (Q i).first
      last := endV i
      walk := (W i).mapLe hH_le_K
      isPath := (reroute_isPath hQ hπ_inj hstep n i).mapLe _
      first_mem := (Q i).first_mem
      last_mem := hend_mem_X₂ i }
  have hQ'_disj : IsDisjointPathFamily K X₁ X₂ Q' := by
    intro i₁ i₂ hne
    simpa [Q'] using reroute_disjoint_support hQ hπ_inj hstep n hne
  have hsum_ge : familyLength K X₁ X₂ Q ≤ ∑ i : Fin k, (W i).length := by
    simpa [familyLength, Q'] using hmin Q' hQ'_disj
  have hstepDart_bij : Function.Bijective stepDart := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨hstepDart_inj, ?_⟩
    simpa [StepIdx, DartIdx, familyLength] using le_antisymm hsum_le hsum_ge
  have hadj_W : ∀ x y : α, H.Adj x y ↔ ∃ i : Fin k, (W i).toSubgraph.Adj x y := by
    intro x y
    constructor
    · intro hxy
      obtain ⟨d, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := (hadj_iff x y).mp hxy
      · obtain ⟨⟨i, m⟩, rfl⟩ := hstepDart_bij.2 d
        refine ⟨i, ?_⟩
        rw [← hstep_minus ⟨i, m⟩, ← hstep_plus ⟨i, m⟩]
        exact walk_toSubgraph_adj_getVert_succ (W i) m.2
      · obtain ⟨⟨i, m⟩, rfl⟩ := hstepDart_bij.2 d
        refine ⟨i, ?_⟩
        rw [← hstep_minus ⟨i, m⟩, ← hstep_plus ⟨i, m⟩]
        exact (walk_toSubgraph_adj_getVert_succ (W i) m.2).symm
    · rintro ⟨i, hxy⟩
      exact (W i).toSubgraph.adj_sub hxy
  have hW_mem_X₁ : ∀ (i : Fin k), ∀ v ∈ (W i).support, v ∈ X₁ → v = (Q i).first := by
    intro i v hv hvX₁
    obtain ⟨j, hj⟩ := reroute_support_mem Q π hstep n ⟨i, (Q i).walk.start_mem_support⟩ hv
    have hv_first : v = (Q j).first := min_family_mem_X₁_eq_first hQ hmin j hj hvX₁
    rw [Walk.mem_support_iff_exists_getVert] at hv
    obtain ⟨m, rfl, hm⟩ := hv
    have hzero : (W i).getVert m = (W j).getVert 0 := by simpa using hv_first
    obtain ⟨rfl, rfl⟩ := reroute_getVert_inj hQ hπ_inj hstep n hm (Nat.zero_le _) hzero
    exact hv_first
  have hW_mem_X₂ : ∀ (i : Fin k), ∀ v ∈ (W i).support, v ∈ X₂ → v = endV i := by
    intro i v hv hvX₂
    obtain ⟨j, hj⟩ := reroute_support_mem Q π hstep n ⟨i, (Q i).walk.start_mem_support⟩ hv
    have hv_last : v = (Q j).last := min_family_mem_X₂_eq_last hQ hmin j hj hvX₂
    rw [Walk.mem_support_iff_exists_getVert] at hv
    obtain ⟨m, rfl, hm⟩ := hv
    rcases hm.lt_or_eq with hmlt | rfl
    · exfalso
      have hminus := hstep_minus ⟨i, ⟨m, hmlt⟩⟩
      exact dartMinus_ne_last hQ (stepDart ⟨i, ⟨m, hmlt⟩⟩) j (hminus.symm.trans hv_last)
    · exact Walk.getVert_length (W i)
  let D : Fin k → (⊤ : SimpleGraph α).Subgraph := fun i ↦ H.induce {v | v ∈ (W i).support}
  have hfirst_H : ∀ i : Fin k, (Q i).first ∈ H.verts := by
    intro i
    rw [hH.verts_eq]
    exact hX₁ (Q i).first_mem
  have hD_eq_comp : ∀ i : Fin k, D i = component H ⟨(Q i).first, hfirst_H i⟩ := by
    intro i
    have hverts : {v | v ∈ (W i).support} = componentVerts H ⟨(Q i).first, hfirst_H i⟩ := by
      ext z
      simp only [Set.mem_ofPred_eq, mem_componentVerts_iff]
      constructor
      · intro hz
        exact walk_spanningCoe_reachable_coe (hfirst_H i) (W i) hz
      · rintro ⟨hzH, hreach⟩
        suffices ∀ y : H.verts, H.coe.Reachable ⟨(Q i).first, hfirst_H i⟩ y → y.1 ∈
          (W i).support from
          this ⟨z, hzH⟩ hreach
        intro y hy
        rw [reachable_iff_reflTransGen] at hy
        induction hy with
        | refl => exact (W i).start_mem_support
        | @tail a b _ hab ih =>
          obtain ⟨j, hj⟩ := (hadj_W a.1 b.1).mp hab
          have ha_j : a.1 ∈ (W j).support :=
            (Walk.mem_verts_toSubgraph (W j)).mp ((W j).toSubgraph.edge_vert hj)
          have hb_j : b.1 ∈ (W j).support :=
            (Walk.mem_verts_toSubgraph (W j)).mp ((W j).toSubgraph.edge_vert hj.symm)
          by_cases hij : i = j
          · subst hij
            exact hb_j
          · exact False.elim (Set.disjoint_left.mp
              (reroute_disjoint_support hQ hπ_inj hstep n hij) ih ha_j)
    simp only [D, component, hverts]
  have hD_comp : ∀ i : Fin k, IsComponent H (D i) :=
    fun i ↦ ⟨⟨(Q i).first, hfirst_H i⟩, hD_eq_comp i⟩
  have hD_inj : Function.Injective D := by
    intro i₁ i₂ hEq
    by_contra hne
    have hmem : (Q i₁).first ∈ (D i₂).verts := hEq ▸ (W i₁).start_mem_support
    exact Set.disjoint_left.mp (reroute_disjoint_support hQ hπ_inj hstep n hne)
      (W i₁).start_mem_support hmem
  have hD_clean : ∀ i : Fin k, IsCleanPathSubgraph H (D i) X₁ X₂ := by
    intro i
    refine ⟨⟨(Q i).first, endV i, W i, reroute_isPath hQ hπ_inj hstep n i,
      (Q i).first_mem, hend_mem_X₂ i⟩, rfl, ?_, hW_mem_X₁ i, hW_mem_X₂ i⟩
    intro u hu v _
    constructor
    · intro huv
      obtain ⟨j, hj⟩ := (hadj_W u v).mp huv
      have hu_j : u ∈ (W j).support :=
        (Walk.mem_verts_toSubgraph (W j)).mp ((W j).toSubgraph.edge_vert hj)
      by_cases hij : i = j
      · subst hij
        exact hj
      · exact False.elim (Set.disjoint_left.mp
          (reroute_disjoint_support hQ hπ_inj hstep n hij) hu hu_j)
    · intro huv
      exact (W i).toSubgraph.adj_sub huv
  refine ⟨H, D, hH, hD_inj, fun i ↦ ⟨hD_comp i, hD_clean i⟩, ?_⟩
  intro C hC hC_ne
  obtain ⟨x, rfl⟩ := hC
  have hx_not_W : ∀ i : Fin k, x.1 ∉ (W i).support := by
    intro i hxi
    exact hC_ne i (IsComponent.eq_of_mem ⟨x, rfl⟩ (hD_comp i)
      (self_mem_componentVerts H x) hxi)
  have hcomp_eq : (component H x).verts = {x.1} := by
    ext z
    simp only [component_verts, mem_componentVerts_iff, Set.mem_singleton_iff]
    refine ⟨?_, fun hEq ↦ hEq ▸ ⟨x.2, Reachable.refl x⟩⟩
    rintro ⟨hzH, hreach⟩
    suffices ∀ y : H.verts, H.coe.Reachable x y → y.1 = x.1 from this ⟨z, hzH⟩ hreach
    intro y hy
    rw [reachable_iff_reflTransGen] at hy
    induction hy with
    | refl => rfl
    | @tail a b _ hab ih =>
      obtain ⟨i, hi⟩ := (hadj_W a.1 b.1).mp hab
      have ha_i : a.1 ∈ (W i).support :=
        (Walk.mem_verts_toSubgraph (W i)).mp ((W i).toSubgraph.edge_vert hi)
      rw [ih] at ha_i
      exact False.elim (hx_not_W i ha_i)
  rw [hcomp_eq, Set.ncard_singleton]

/-- **Graph Minors IV, (6.1)** (pages 241–242): Let `P = (G, μ, Δ, φ)` be a robust `Ω`-patchwork,
let `X₁, X₂ ⊆ V(G)`, and let `k ≥ 0` be an integer. Then conditions (i), (ii), and (iii) are
equivalent. -/
theorem theorem_6_1_proof (hM : MengerStatement.{u, v}) {P : Patchwork Ω α β} (hrob : P.IsRobust)
    {X₁ X₂ : Set α} (hX₁ : X₁ ⊆ P.G.vertexSet) (hX₂ : X₂ ⊆ P.G.vertexSet) (k : ℕ) :
    (Theorem61Cond1 P X₁ X₂ k ↔ Theorem61Cond2 P X₁ X₂ k) ∧
    (Theorem61Cond2 P X₁ X₂ k ↔ Theorem61Cond3 P X₁ X₂ k) := by
  have hi := theorem_6_1_i_iff_disjointPaths hM hX₁ hX₂ k
  have h32 : Theorem61Cond3 P X₁ X₂ k → Theorem61Cond2 P X₁ X₂ k := theorem_6_1_iii_imp_ii
  have h2p : Theorem61Cond2 P X₁ X₂ k → HasDisjointPaths P.G.toHypergraph.skeleton X₁ X₂ k :=
    theorem_6_1_ii_imp_disjointPaths
  have hp3 : HasDisjointPaths P.G.toHypergraph.skeleton X₁ X₂ k → Theorem61Cond3 P X₁ X₂ k :=
    theorem_6_1_disjointPaths_imp_iii hrob hX₁ hX₂
  exact ⟨⟨fun h ↦ h32 (hp3 (hi.mp h)), fun h ↦ hi.mpr (h2p h)⟩,
    ⟨fun h ↦ hp3 (h2p h), h32⟩⟩

end GraphMinor.GM04
