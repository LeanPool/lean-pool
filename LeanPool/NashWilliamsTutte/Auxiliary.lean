/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Data.Set.Card.Arithmetic
public import Mathlib.Data.Set.Finite.Lemmas

/-!
# Auxiliary lemmas for the Nash-Williams–Tutte theorems

General counting lemmas for forests and connected graphs, and the core exchange lemma: for any
finite graph `G` there are `k` edge-disjoint forests `F i ≤ G` and a subgraph `H ≤ G` such that
each `F i ⊓ H` has the same connected components as `H`, and every edge of `G` outside `H` is
covered by some `F i`.
-/

public section

open Finset Fintype SimpleGraph Function

namespace NashWilliamsTutte

variable {V : Type*}

/-- Reachability transfers along a map that sends adjacent vertices to reachable ones. -/
theorem reachable_map_of_adj {W : Type*} {A : SimpleGraph V} {B : SimpleGraph W} (g : V → W)
    (h : ∀ a b, A.Adj a b → B.Reachable (g a) (g b)) {a b : V} (hab : A.Reachable a b) :
    B.Reachable (g a) (g b) := by
  obtain ⟨p⟩ := hab
  induction p with
  | nil => rfl
  | cons hadj _ ih => exact (h _ _ hadj).trans ih

/-- A predicate closed under adjacency is closed under reachability. -/
theorem reachable_closed {A : SimpleGraph V} (P : V → Prop) (h : ∀ a b, A.Adj a b → P a → P b)
    {a b : V} (hab : A.Reachable a b) (ha : P a) : P b := by
  obtain ⟨p⟩ := hab
  induction p with
  | nil => exact ha
  | cons hadj _ ih => exact ih (h _ _ hadj ha)

/-- Disjointness of simple graphs in terms of adjacency. -/
theorem disjoint_iff_adj {A B : SimpleGraph V} :
    Disjoint A B ↔ ∀ a b, A.Adj a b → ¬ B.Adj a b := by
  rw [← disjoint_edgeSet, Set.disjoint_left]
  constructor
  · intro h a b ha hb
    exact h (show s(a, b) ∈ A.edgeSet from ha) hb
  · intro h e
    induction e using Sym2.ind with
    | _ a b => exact fun ha hb ↦ h a b ha hb

/-- The sum of the sizes of pairwise disjoint subsets of a finite set is at most its size. -/
theorem sum_ncard_le_of_pairwise_disjoint {ι α : Type*} [Fintype ι] [Finite α] (A : ι → Set α)
    (B : Set α) (hAB : ∀ i, A i ⊆ B) (hd : Pairwise (Disjoint on A)) :
    ∑ i, (A i).ncard ≤ B.ncard := by
  have h := Set.ncard_iUnion_of_finite (s := A) (fun i ↦ Set.toFinite _) hd
  rw [finsum_eq_sum_of_fintype] at h
  rw [← h]
  exact Set.ncard_le_ncard (Set.iUnion_subset hAB)

/-- A forest on a finite nonempty vertex type has at most `|V| - 1` edges, and exactly `|V| - 1`
only if it is a tree. -/
theorem IsAcyclic.ncard_edgeSet_add_one_le [Finite V] [Nonempty V] {F : SimpleGraph V}
    (hF : F.IsAcyclic) :
    F.edgeSet.ncard + 1 ≤ Nat.card V ∧ (Nat.card V ≤ F.edgeSet.ncard + 1 → F.IsTree) := by
  obtain ⟨T, hFT, hT⟩ := exists_maximal_isAcyclic_of_le_isAcyclic (le_top : F ≤ ⊤) hF
  have hT' : T.IsTree := by
    rw [← maximal_isAcyclic_iff_isTree]
    exact ⟨hT.1.2, fun H hH hle ↦ hT.2 ⟨le_top, hH⟩ hle⟩
  have hcard := (isTree_iff_connected_and_card.1 hT').2
  rw [Nat.card_coe_set_eq] at hcard
  have hsub : F.edgeSet ⊆ T.edgeSet := edgeSet_mono hFT
  have hle : F.edgeSet.ncard ≤ T.edgeSet.ncard := Set.ncard_le_ncard hsub
  refine ⟨by omega, fun h ↦ ?_⟩
  have heq : F.edgeSet = T.edgeSet := Set.eq_of_subset_of_ncard_le hsub (by omega)
  rwa [edgeSet_inj.1 heq]

/-- If every vertex `v` is reachable in `K` from `f v`, then `K` has at least
`|V| - #(image f)` edges. -/
theorem card_le_ncard_edgeSet_add_card_image [Fintype V] [DecidableEq V] [Nonempty V]
    (K : SimpleGraph V) (f : V → V) (hf : ∀ v, K.Reachable v (f v)) :
    Nat.card V ≤ K.edgeSet.ncard + #(univ.image f) := by
  set r₀ := f (Classical.arbitrary V)
  have hr₀ : r₀ ∈ univ.image f := mem_image_of_mem _ (mem_univ _)
  set St : Set (Sym2 V) := (fun r ↦ s(r₀, r)) '' ↑((univ.image f).erase r₀)
  set L := K ⊔ fromEdgeSet St
  have hreach : ∀ a, L.Reachable a r₀ := by
    intro a
    refine ((hf a).mono le_sup_left).trans ?_
    by_cases ha : f a = r₀
    · rw [ha]
    · refine Adj.reachable (Or.inr ?_)
      refine ⟨⟨f a, ?_, ?_⟩, ha⟩
      · simp [ha]
      · exact Sym2.eq_swap
  have hL : L.Connected := by
    have : Nonempty V := inferInstance
    exact Connected.mk fun a b ↦ (hreach a).trans (hreach b).symm
  have h1 := hL.card_vert_le_card_edgeSet_add_one
  rw [Nat.card_coe_set_eq] at h1
  have h2 : L.edgeSet.ncard ≤ K.edgeSet.ncard + St.ncard := by
    refine (Set.ncard_le_ncard (t := K.edgeSet ∪ St) ?_).trans (Set.ncard_union_le _ _)
    rw [edgeSet_sup, edgeSet_fromEdgeSet]
    exact Set.union_subset_union_right _ Set.sdiff_subset
  have h3 : St.ncard ≤ #(univ.image f) - 1 := by
    refine (Set.ncard_image_le (Set.toFinite _)).trans ?_
    rw [Set.ncard_coe_finset, card_erase_of_mem hr₀]
  have h4 : 1 ≤ #(univ.image f) := card_pos.2 ⟨_, hr₀⟩
  omega

/-- A connected graph has at least `m - 1` edges joining different fibres of `f`, where `m` is the
number of nonempty fibres. -/
theorem card_image_le_ncard_crossing_add_one [Fintype V] [DecidableEq V] {T : SimpleGraph V}
    (hT : T.Connected) (f : V → V) :
    #(univ.image f) ≤ (T.edgeSet ∩ ((⊤ : SimpleGraph V).comap f).edgeSet).ncard + 1 := by
  set W := ↥(univ.image f)
  let g : V → W := fun a ↦ ⟨f a, mem_image_of_mem _ (mem_univ a)⟩
  let Q : SimpleGraph W := SimpleGraph.fromRel fun p q ↦ ∃ a b, T.Adj a b ∧ g a = p ∧ g b = q
  have hg : ∀ p : W, ∃ a, g a = p := by
    rintro ⟨p, hp⟩
    obtain ⟨a, -, rfl⟩ := mem_image.1 hp
    exact ⟨a, rfl⟩
  have hQ : Q.Connected := by
    have : Nonempty V := hT.nonempty
    have : Nonempty W := ⟨g (Classical.arbitrary V)⟩
    refine Connected.mk fun p q ↦ ?_
    obtain ⟨a, rfl⟩ := hg p
    obtain ⟨b, rfl⟩ := hg q
    refine reachable_map_of_adj g (fun x y hxy ↦ ?_) (hT.preconnected a b)
    by_cases hxy' : g x = g y
    · rw [hxy']
    · exact Adj.reachable ((fromRel_adj _ _ _).2 ⟨hxy', Or.inl ⟨x, y, hxy, rfl, rfl⟩⟩)
  have h1 := hQ.card_vert_le_card_edgeSet_add_one
  rw [Nat.card_coe_set_eq, Nat.card_eq_fintype_card, Fintype.card_coe] at h1
  have h2 : Q.edgeSet ⊆ Sym2.map g '' (T.edgeSet ∩ ((⊤ : SimpleGraph V).comap f).edgeSet) := by
    intro e he
    induction e using Sym2.ind with
    | _ p q =>
      have he' : Q.Adj p q := he
      obtain ⟨hpq, h | h⟩ := (fromRel_adj _ _ _).1 he'
      · obtain ⟨a, b, hab, rfl, rfl⟩ := h
        refine ⟨s(a, b), ⟨hab, ?_⟩, rfl⟩
        exact fun h' ↦ hpq (Subtype.ext h')
      · obtain ⟨a, b, hab, rfl, rfl⟩ := h
        refine ⟨s(a, b), ⟨hab, ?_⟩, Sym2.eq_swap⟩
        exact fun h' ↦ hpq (Subtype.ext h'.symm)
  have h3 := (Set.ncard_le_ncard h2 (Set.toFinite _)).trans (Set.ncard_image_le (Set.toFinite _))
  omega

/-- Deleting an edge of the unique path between `u` and `v` in a forest disconnects `u` from
`v`. -/
theorem not_reachable_deleteEdges_of_mem_edges {F : SimpleGraph V} (hF : F.IsAcyclic) {u v x y : V}
    (p : F.Walk u v) (hp : p.IsPath) (he : s(x, y) ∈ p.edges) :
    ¬ (F.deleteEdges {s(x, y)}).Reachable u v := by
  classical
  rintro ⟨q⟩
  have hq : (q.bypass.mapLe (deleteEdges_le _)).IsPath := (Walk.isPath_mapLe _).2 q.bypass_isPath
  have := (hF.subsingleton_path u v).elim ⟨p, hp⟩ ⟨_, hq⟩
  simp only [Subtype.mk.injEq] at this
  rw [this, Walk.edges_mapLe_eq_edges] at he
  have := q.bypass.edges_subset_edgeSet he
  simp [edgeSet_deleteEdges] at this

section Exchange

variable (G : SimpleGraph V) {k : ℕ}

/-- `k` pairwise edge-disjoint forests in `G`. -/
def ValidForests (F : Fin k → SimpleGraph V) : Prop :=
  (∀ i, F i ≤ G ∧ (F i).IsAcyclic) ∧ Pairwise fun i j ↦ Disjoint (F i) (F j)

/-- The total number of edges of a family of graphs. -/
noncomputable def totalEdges (F : Fin k → SimpleGraph V) : ℕ := ∑ i, (F i).edgeSet.ncard

/-- `uv` is an edge of `G` not covered by the family `F`. -/
def Uncovered (F : Fin k → SimpleGraph V) (u v : V) : Prop := G.Adj u v ∧ ∀ j, ¬ (F j).Adj u v

/-- One exchange step: an uncovered edge `uv` replaces an edge `xy` of some `F i`, keeping it
acyclic. -/
def ExchangeStep (F F' : Fin k → SimpleGraph V) : Prop :=
  ∃ i u v x y, Uncovered G F u v ∧ (F i).Adj x y ∧
    ((F i).deleteEdges {s(x, y)} ⊔ edge u v).IsAcyclic ∧
    F' = update F i ((F i).deleteEdges {s(x, y)} ⊔ edge u v)

variable {G}

theorem total_update (F : Fin k → SimpleGraph V) (i : Fin k) (X : SimpleGraph V) :
    totalEdges (update F i X) + (F i).edgeSet.ncard = totalEdges F + X.edgeSet.ncard := by
  simp only [totalEdges]
  rw [show (fun j ↦ (update F i X j).edgeSet.ncard) =
      update (fun j ↦ (F j).edgeSet.ncard) i X.edgeSet.ncard from
    funext fun j ↦ apply_update (fun _ (H : SimpleGraph V) ↦ H.edgeSet.ncard) F i X j]
  rw [Finset.sum_update_of_mem (mem_univ i), Finset.sdiff_singleton_eq_erase]
  have := Finset.add_sum_erase univ (fun j ↦ (F j).edgeSet.ncard) (mem_univ i)
  omega

theorem Uncovered.adj_iff {F : Fin k → SimpleGraph V} {u v : V} (h : Uncovered G F u v) {j : Fin k}
    {a b : V} (hab : s(a, b) = s(u, v)) : ¬ (F j).Adj a b := by
  rcases Sym2.eq_iff.1 hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact h.2 j
  · exact fun h' ↦ h.2 j h'.symm

theorem adj_new {F : SimpleGraph V} {x y u v a b : V}
    (h : (F.deleteEdges {s(x, y)} ⊔ edge u v).Adj a b) :
    (F.Adj a b ∧ s(a, b) ≠ s(x, y)) ∨ s(a, b) = s(u, v) := by
  rcases h with h | h
  · rw [deleteEdges_adj] at h
    exact Or.inl ⟨h.1, h.2⟩
  · rw [edge_adj] at h
    right
    rcases h.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exact Sym2.eq_swap

/-- Replacing `F i` by a graph `X ≤ G` whose edges are edges of `F i` or uncovered edges keeps
the family valid, provided `X` is acyclic. -/
theorem ValidForests.update {F : Fin k → SimpleGraph V} (hF : ValidForests G F)
    (i : Fin k) {X : SimpleGraph V}
    (hXG : X ≤ G) (hX : X.IsAcyclic)
    (hXadj : ∀ a b, X.Adj a b → (F i).Adj a b ∨ ∀ j, ¬ (F j).Adj a b) :
    ValidForests G (update F i X) := by
  refine ⟨fun j ↦ ?_, fun j₁ j₂ hj ↦ ?_⟩
  · by_cases hj : j = i
    · subst hj; simpa using ⟨hXG, hX⟩
    · simpa [hj] using hF.1 j
  · have key : ∀ j, j ≠ i → Disjoint X (F j) := by
      intro j hji
      rw [disjoint_iff_adj]
      intro a b hab
      rcases hXadj a b hab with h | h
      · exact (disjoint_iff_adj.1 (hF.2 (Ne.symm hji))) a b h
      · exact h j
    by_cases h₁ : j₁ = i
    · subst h₁
      simpa [Ne.symm hj] using key j₂ (Ne.symm hj)
    · by_cases h₂ : j₂ = i
      · subst h₂
        simpa [h₁] using (key j₁ h₁).symm
      · simpa [h₁, h₂] using hF.2 hj

theorem ExchangeStep.valid {F F' : Fin k → SimpleGraph V} (hF : ValidForests G F)
    (h : ExchangeStep G F F') :
    ValidForests G F' := by
  obtain ⟨i, u, v, x, y, huv, hxy, hac, rfl⟩ := h
  refine hF.update i (sup_le ((deleteEdges_le _).trans (hF.1 i).1)
    ((edge_le_iff _).2 (Or.inr huv.1))) hac fun a b hab ↦ ?_
  rcases adj_new hab with h | h
  · exact Or.inl h.1
  · exact Or.inr fun j ↦ huv.adj_iff h

theorem ExchangeStep.total_eq [Finite V] {F F' : Fin k → SimpleGraph V} (h : ExchangeStep G F F') :
    totalEdges F' = totalEdges F := by
  obtain ⟨i, u, v, x, y, huv, hxy, hac, rfl⟩ := h
  have h1 := total_update F i ((F i).deleteEdges {s(x, y)} ⊔ edge u v)
  have hne : u ≠ v := huv.1.ne
  have h2 : ((F i).deleteEdges {s(x, y)} ⊔ edge u v).edgeSet.ncard = (F i).edgeSet.ncard := by
    rw [edgeSet_sup, edgeSet_deleteEdges, edgeSet_edge_of_ne hne,
      Set.ncard_union_eq (Set.disjoint_singleton_right.2 fun h ↦ huv.2 i h.1) (Set.toFinite _)
        (Set.toFinite _), Set.ncard_singleton]
    exact Set.ncard_sdiff_singleton_add_one (show s(x, y) ∈ (F i).edgeSet from hxy)
      (Set.toFinite _)
  omega

/-- In a family with the maximum total number of edges, the endpoints of an uncovered edge are
joined in every forest. -/
theorem reachable_of_uncovered [Finite V] {F : Fin k → SimpleGraph V} (hF : ValidForests G F)
    (hmax : ∀ F' : Fin k → SimpleGraph V, ValidForests G F' → totalEdges F' ≤ totalEdges F)
    {u v : V}
    (huv : Uncovered G F u v) (i : Fin k) :
    (F i).Reachable u v := by
  by_contra h
  have hval : ValidForests G (update F i (F i ⊔ edge u v)) := by
    refine hF.update i (sup_le (hF.1 i).1 ((edge_le_iff _).2 (Or.inr huv.1)))
      ((hF.1 i).2.sup_edge_of_not_reachable h) fun a b hab ↦ ?_
    rcases hab with hab | hab
    · exact Or.inl hab
    · right
      intro j
      apply huv.adj_iff
      rw [edge_adj] at hab
      rcases hab.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rfl
      · exact Sym2.eq_swap
  have h1 := total_update F i (F i ⊔ edge u v)
  have h2 : (F i ⊔ edge u v).edgeSet.ncard = (F i).edgeSet.ncard + 1 := by
    rw [edgeSet_sup, edgeSet_edge_of_ne huv.1.ne,
      Set.ncard_union_eq
        (Set.disjoint_singleton_right.2 (show s(u, v) ∉ (F i).edgeSet from huv.2 i))
        (Set.toFinite _)
        (Set.toFinite _), Set.ncard_singleton]
  have h3 := hmax _ hval
  omega

theorem ExchangeStep.uncovered {F : Fin k → SimpleGraph V} (hF : ValidForests G F)
    {i : Fin k} {u v x y : V}
    (huv : Uncovered G F u v) (hxy : (F i).Adj x y) :
    Uncovered G (update F i ((F i).deleteEdges {s(x, y)} ⊔ edge u v)) x y := by
  refine ⟨(hF.1 i).1 hxy, fun j ↦ ?_⟩
  by_cases hj : j = i
  · subst hj
    simp only [update_self]
    intro h
    rcases adj_new h with h | h
    · exact h.2 rfl
    · exact huv.adj_iff h hxy
  · simp only [update_of_ne hj]
    exact disjoint_iff_adj.1 (hF.2 (Ne.symm hj)) x y hxy

end Exchange

section Core

variable {G : SimpleGraph V} {k : ℕ}

/-- The graph of all edges of `G` that are uncovered in some family obtained from `F₀` by a
sequence of exchange steps. -/
def exchangeGraph (G : SimpleGraph V) (F₀ : Fin k → SimpleGraph V) : SimpleGraph V where
  Adj a b := ∃ F, Relation.ReflTransGen (ExchangeStep G) F₀ F ∧ Uncovered G F a b
  symm := ⟨fun _ _ ⟨F, h, hu⟩ ↦ ⟨F, h, hu.1.symm, fun j h' ↦ hu.2 j h'.symm⟩⟩
  loopless := ⟨fun _ ⟨_, _, hu⟩ ↦ hu.1.ne rfl⟩

theorem exchangeGraph_adj {F₀ : Fin k → SimpleGraph V} {a b : V} :
    (exchangeGraph G F₀).Adj a b ↔
      ∃ F, Relation.ReflTransGen (ExchangeStep G) F₀ F ∧ Uncovered G F a b :=
  Iff.rfl

variable [Finite V] {F₀ : Fin k → SimpleGraph V} (hF₀ : ValidForests G F₀)
  (hmax : ∀ F : Fin k → SimpleGraph V, ValidForests G F → totalEdges F ≤ totalEdges F₀)
include hF₀ hmax

omit hmax in
theorem reach_valid {F : Fin k → SimpleGraph V} (hF : Relation.ReflTransGen (ExchangeStep G) F₀ F) :
    ValidForests G F ∧ totalEdges F = totalEdges F₀ := by
  induction hF with
  | refl => exact ⟨hF₀, rfl⟩
  | tail _ hstep ih => exact ⟨hstep.valid ih.1, hstep.total_eq.trans ih.2⟩

theorem reach_uncovered_reachable {F : Fin k → SimpleGraph V}
    (hF : Relation.ReflTransGen (ExchangeStep G) F₀ F) {u v : V}
    (huv : Uncovered G F u v) (i : Fin k) :
    (F i ⊓ exchangeGraph G F₀).Reachable u v := by
  classical
  obtain ⟨hval, htot⟩ := reach_valid hF₀ hF
  have hr := reachable_of_uncovered hval (fun F' hF' ↦ htot ▸ hmax F' hF') huv i
  obtain ⟨w⟩ := hr
  set p := w.bypass
  have hp : p.IsPath := w.bypass_isPath
  refine ⟨p.transfer _ fun e he ↦ ?_⟩
  induction e using Sym2.ind with
  | _ x y =>
    have hxy : (F i).Adj x y := p.edges_subset_edgeSet he
    refine ⟨hxy, exchangeGraph_adj.2
      ⟨update F i ((F i).deleteEdges {s(x, y)} ⊔ edge u v), ?_,
        ExchangeStep.uncovered hval huv hxy⟩⟩
    refine hF.tail ⟨i, u, v, x, y, huv, hxy, ?_, rfl⟩
    exact ((hval.1 i).2.anti (deleteEdges_le _)).sup_edge_of_not_reachable
      (not_reachable_deleteEdges_of_mem_edges (hval.1 i).2 p hp he)

theorem step_reachable_iff {F F' : Fin k → SimpleGraph V}
    (hF : Relation.ReflTransGen (ExchangeStep G) F₀ F) (hstep : ExchangeStep G F F')
    (j : Fin k) (a b : V) :
    (F j ⊓ exchangeGraph G F₀).Reachable a b ↔ (F' j ⊓ exchangeGraph G F₀).Reachable a b := by
  classical
  have hF' : Relation.ReflTransGen (ExchangeStep G) F₀ F' := hF.tail hstep
  have hval := (reach_valid hF₀ hF).1
  obtain ⟨i, u, v, x, y, huv, hxy, hac, rfl⟩ := hstep
  by_cases hj : j = i
  swap
  · simp only [update_of_ne hj]
  subst hj
  simp only [update_self]
  constructor
  · refine reachable_map_of_adj id fun c d hcd ↦ ?_
    by_cases hc : s(c, d) = s(x, y)
    · have h := reach_uncovered_reachable hF₀ hmax hF' (ExchangeStep.uncovered hval huv hxy) j
      simp only [update_self] at h
      rcases Sym2.eq_iff.1 hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact h
      · exact h.symm
    · exact Adj.reachable
        ⟨Or.inl (deleteEdges_adj.2 ⟨hcd.1, fun h ↦ hc (Set.mem_singleton_iff.1 h)⟩), hcd.2⟩
  · refine reachable_map_of_adj id fun c d hcd ↦ ?_
    rcases adj_new hcd.1 with h | h
    · exact Adj.reachable ⟨h.1, hcd.2⟩
    · have h' := reach_uncovered_reachable hF₀ hmax hF huv j
      rcases Sym2.eq_iff.1 h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact h'
      · exact h'.symm

theorem reach_reachable_iff {F : Fin k → SimpleGraph V}
    (hF : Relation.ReflTransGen (ExchangeStep G) F₀ F) (j : Fin k) (a b : V) :
    (F j ⊓ exchangeGraph G F₀).Reachable a b ↔ (F₀ j ⊓ exchangeGraph G F₀).Reachable a b := by
  induction hF with
  | refl => rfl
  | tail h hstep ih => exact (step_reachable_iff hF₀ hmax h hstep j a b).symm.trans ih

end Core

/-- **Core exchange lemma.** For every finite graph `G` there are `k` pairwise edge-disjoint
forests `F i ≤ G` and a subgraph `H ≤ G` such that each `F i ⊓ H` has the same connected
components as `H`, and every edge of `G` outside `H` belongs to some `F i`. -/
theorem exists_forests_core [Finite V] (G : SimpleGraph V) (k : ℕ) :
    ∃ (F : Fin k → SimpleGraph V) (H : SimpleGraph V), (∀ i, F i ≤ G ∧ (F i).IsAcyclic) ∧
      (Pairwise fun i j ↦ Disjoint (F i) (F j)) ∧ H ≤ G ∧
      (∀ i a b, H.Reachable a b → (F i ⊓ H).Reachable a b) ∧
      (∀ a b, G.Adj a b → ¬ H.Adj a b → ∃ i, (F i).Adj a b) := by
  have : Finite (SimpleGraph V) := Finite.of_injective _ fun _ _ h ↦ SimpleGraph.ext h
  have hval0 : ValidForests G (fun _ : Fin k ↦ (⊥ : SimpleGraph V)) :=
    ⟨fun _ ↦ ⟨bot_le, isAcyclic_bot⟩, fun _ _ _ ↦ disjoint_bot_left⟩
  obtain ⟨F₀, hF₀, hmax⟩ := Set.exists_max_image
    {F : Fin k → SimpleGraph V | ValidForests G F} totalEdges (Set.toFinite _) ⟨_, hval0⟩
  refine ⟨F₀, exchangeGraph G F₀, hF₀.1, hF₀.2, fun a b h ↦ ?_, fun i a b hab ↦ ?_,
    fun a b hab hH ↦ ?_⟩
  · obtain ⟨_, _, hu⟩ := exchangeGraph_adj.1 h
    exact hu.1
  · refine reachable_map_of_adj id (fun c d h ↦ ?_) hab
    obtain ⟨F, hF, hu⟩ := exchangeGraph_adj.1 h
    exact (reach_reachable_iff hF₀ hmax hF i c d).1 (reach_uncovered_reachable hF₀ hmax hF hu i)
  · by_contra h
    exact hH (exchangeGraph_adj.2 ⟨F₀, .refl, hab, fun j hj ↦ h ⟨j, hj⟩⟩)

end NashWilliamsTutte
