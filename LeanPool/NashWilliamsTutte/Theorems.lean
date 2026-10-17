/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Tactic.Push
public import LeanPool.NashWilliamsTutte.Auxiliary

/-!
# The Nash-Williams–Tutte tree packing theorem and Nash-Williams' arboricity theorem

For a finite simple graph `G` on `V`:

* `NashWilliamsTutte.tree_packing`: **Nash-Williams (1961), Tutte (1961).**
  `G` has `k` edge-disjoint spanning trees if and only if, for every partition of `V` into `m`
  parts, at least `k (m - 1)`
  edges of `G` join different parts. A partition is given by a map `f : V → V` (its parts are the
  nonempty fibres, `#(univ.image f)` of them), and the edges of `G` joining different parts are
  those of `G ⊓ (⊤ : SimpleGraph V).comap f`.
* `NashWilliamsTutte.arboricity`: **Nash-Williams (1964).** The edges of `G` can be covered by `k`
  forests if and only if every nonempty vertex set `S` spans at most `k (#S - 1)` edges.
* `NashWilliamsTutte.exists_trees_of_isEdgeConnected`: **corollary.** A `2k`-edge-connected finite
  graph (Mathlib's `SimpleGraph.IsEdgeConnected`) has `k` edge-disjoint spanning trees.

Spanning trees are subgraphs `T ≤ G` on the same vertex type with Mathlib's `SimpleGraph.IsTree`;
forests are subgraphs with `SimpleGraph.IsAcyclic`; edge-disjointness is `Disjoint` in the lattice
of simple graphs.
-/

@[expose] public section

open Finset Fintype SimpleGraph

namespace NashWilliamsTutte

/-- **Nash-Williams–Tutte tree packing theorem.** A finite graph on a nonempty vertex type has `k`
pairwise edge-disjoint spanning trees if and only if, for every map `f : V → V`, the number of
edges of `G` whose endpoints have different images under `f` is at least `k` times the number of
nonempty fibres of `f` minus one. -/
theorem tree_packing {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V)
    (k : ℕ) :
    (∃ T : Fin k → SimpleGraph V, (∀ i, T i ≤ G ∧ (T i).IsTree) ∧
        Pairwise fun i j ↦ Disjoint (T i) (T j)) ↔
      ∀ f : V → V,
        k * (#(univ.image f) - 1) ≤ (G ⊓ (⊤ : SimpleGraph V).comap f).edgeSet.ncard := by
  constructor
  · rintro ⟨T, hT, hdisj⟩ f
    have h1 : ∀ i, #(univ.image f) - 1 ≤
        ((T i).edgeSet ∩ ((⊤ : SimpleGraph V).comap f).edgeSet).ncard := fun i ↦ by
      have := card_image_le_ncard_crossing_add_one (hT i).2.connected f
      omega
    have h2 := sum_ncard_le_of_pairwise_disjoint
      (fun i ↦ (T i).edgeSet ∩ ((⊤ : SimpleGraph V).comap f).edgeSet)
      (G ⊓ (⊤ : SimpleGraph V).comap f).edgeSet
      (fun i ↦ by rw [edgeSet_inf]; exact Set.inter_subset_inter_left _ (edgeSet_mono (hT i).1))
      (fun i j hij ↦ (disjoint_edgeSet.2 (hdisj hij)).mono Set.inter_subset_left
        Set.inter_subset_left)
    calc k * (#(univ.image f) - 1) = ∑ _i : Fin k, (#(univ.image f) - 1) := by simp
      _ ≤ ∑ i, ((T i).edgeSet ∩ ((⊤ : SimpleGraph V).comap f).edgeSet).ncard :=
          sum_le_sum fun i _ ↦ h1 i
      _ ≤ _ := h2
  · intro hcond
    obtain ⟨F, H, hF, hdisj, -, hreach, hcov⟩ := exists_forests_core G k
    refine ⟨F, fun i ↦ ⟨(hF i).1, ?_⟩, hdisj⟩
    let f : V → V := fun v ↦ Quot.out (H.connectedComponentMk v)
    have hfr : ∀ v, H.Reachable v (f v) := fun v ↦
      (ConnectedComponent.exact (Quot.out_eq (H.connectedComponentMk v))).symm
    have hfeq : ∀ a b, H.Adj a b → f a = f b := fun a b hab ↦ by
      simp only [f, ConnectedComponent.sound hab.reachable]
    have hcf := hcond f
    set m := #(univ.image f)
    set C := (G ⊓ (⊤ : SimpleGraph V).comap f).edgeSet
    have hC : C ⊆ ⋃ j, (F j).edgeSet ∩ C := by
      intro e he
      induction e using Sym2.ind with
      | _ a b =>
        have he' : G.Adj a b ∧ f a ≠ f b := by simpa [C] using he
        obtain ⟨j, hj⟩ := hcov a b he'.1 fun h ↦ he'.2 (hfeq a b h)
        exact Set.mem_iUnion.2 ⟨j, hj, he⟩
    have hsum : C.ncard ≤ ∑ j, ((F j).edgeSet ∩ C).ncard :=
      (Set.ncard_le_ncard hC (Set.toFinite _)).trans (Set.ncard_iUnion_le_of_fintype _)
    have hbound : ∀ j, ((F j).edgeSet ∩ C).ncard + Nat.card V ≤
        (F j).edgeSet.ncard + m := by
      intro j
      have hLB := card_le_ncard_edgeSet_add_card_image (F j ⊓ H) f
        fun v ↦ hreach j _ _ (hfr v)
      have hdj : Disjoint ((F j).edgeSet ∩ C) (F j ⊓ H).edgeSet := by
        rw [Set.disjoint_left]
        intro e he he'
        induction e using Sym2.ind with
        | _ a b =>
          have h1 : G.Adj a b ∧ f a ≠ f b := by simpa [C] using he.2
          exact h1.2 (hfeq a b he'.2)
      have hsub : (F j).edgeSet ∩ C ∪ (F j ⊓ H).edgeSet ⊆ (F j).edgeSet :=
        Set.union_subset Set.inter_subset_left (edgeSet_mono inf_le_left)
      have := Set.ncard_le_ncard hsub (Set.toFinite _)
      rw [Set.ncard_union_eq hdj (Set.toFinite _) (Set.toFinite _)] at this
      omega
    by_contra hnt
    have hlt : ∑ j, ((F j).edgeSet ∩ C).ncard < ∑ _j : Fin k, (m - 1) := by
      refine Finset.sum_lt_sum (fun j _ ↦ ?_) ⟨i, mem_univ i, ?_⟩
      · have := (IsAcyclic.ncard_edgeSet_add_one_le (hF j).2).1
        have := hbound j
        omega
      · have h1 := IsAcyclic.ncard_edgeSet_add_one_le (hF i).2
        have h2 : ¬ Nat.card V ≤ (F i).edgeSet.ncard + 1 := fun h ↦ hnt (h1.2 h)
        have := hbound i
        omega
    simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul] at hlt
    omega

/-- **Nash-Williams' arboricity theorem.** The edges of a finite graph can be covered by `k`
forests if and only if every nonempty set `S` of vertices spans at most `k (#S - 1)` edges. -/
theorem arboricity {V : Type*} [Finite V] (G : SimpleGraph V) (k : ℕ) :
    (∃ F : Fin k → SimpleGraph V, (∀ i, F i ≤ G ∧ (F i).IsAcyclic) ∧ G = ⨆ i, F i) ↔
      ∀ S : Finset V, S.Nonempty → (G.induce (S : Set V)).edgeSet.ncard ≤ k * (#S - 1) := by
  constructor
  · rintro ⟨F, hF, hG⟩ S hS
    have : Nonempty (S : Set V) := ⟨⟨hS.choose, hS.choose_spec⟩⟩
    have hcardS : Nat.card (S : Set V) = #S := by
      rw [Nat.card_coe_set_eq, Set.ncard_coe_finset]
    have hsub : (G.induce (S : Set V)).edgeSet ⊆ ⋃ i, ((F i).induce (S : Set V)).edgeSet := by
      intro e he
      induction e using Sym2.ind with
      | _ a b =>
        have hab : G.Adj a b := he
        rw [hG, iSup_adj] at hab
        obtain ⟨i, hi⟩ := hab
        exact Set.mem_iUnion.2 ⟨i, hi⟩
    calc (G.induce (S : Set V)).edgeSet.ncard
        ≤ ∑ i, ((F i).induce (S : Set V)).edgeSet.ncard :=
          (Set.ncard_le_ncard hsub (Set.toFinite _)).trans (Set.ncard_iUnion_le_of_fintype _)
      _ ≤ ∑ _i : Fin k, (#S - 1) := sum_le_sum fun i _ ↦ by
          have := (IsAcyclic.ncard_edgeSet_add_one_le ((hF i).2.induce (S : Set V))).1
          omega
      _ = k * (#S - 1) := by simp
  · intro hcond
    have := Fintype.ofFinite V
    classical
    obtain ⟨F, H, hF, hdisj, -, hreach, hcov⟩ := exists_forests_core G k
    refine ⟨F, hF, le_antisymm (fun u v huv ↦ ?_) (iSup_le fun i ↦ (hF i).1)⟩
    rw [iSup_adj]
    by_contra hnot
    have hH : H.Adj u v := by
      by_contra h
      exact hnot (hcov u v huv h)
    let S : Finset V := univ.filter fun w ↦ H.Reachable u w
    have hu : u ∈ S := by simp [S]
    have hv : v ∈ S := by simpa [S] using hH.reachable
    have hcardS : Nat.card (S : Set V) = #S := by
      rw [Nat.card_coe_set_eq, Set.ncard_coe_finset]
    have hconn : ∀ i, ((F i ⊓ H).induce (S : Set V)).Connected := by
      intro i
      have hS : (S : Set V) = ((F i ⊓ H).connectedComponentMk u).supp := by
        ext w
        simp only [S, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq,
          ConnectedComponent.mem_supp_iff, ConnectedComponent.eq]
        exact ⟨fun h ↦ (hreach i u w h).symm, fun h ↦ (h.mono inf_le_right).symm⟩
      rw [hS]
      exact ((F i ⊓ H).connectedComponentMk u).connected_toSimpleGraph
    let e : Sym2 (S : Set V) := s(⟨u, hu⟩, ⟨v, hv⟩)
    have he : e ∈ (G.induce (S : Set V)).edgeSet := huv
    have h1 := sum_ncard_le_of_pairwise_disjoint
      (fun i ↦ ((F i ⊓ H).induce (S : Set V)).edgeSet) ((G.induce (S : Set V)).edgeSet \ {e})
      (fun i x hx ↦ by
        induction x using Sym2.ind with
        | _ a b =>
          have hab : (F i ⊓ H).Adj a b := hx
          refine ⟨(hF i).1 hab.1, fun h ↦ ?_⟩
          rcases Sym2.eq_iff.1 (Set.mem_singleton_iff.1 h) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact hnot ⟨i, hab.1⟩
          · exact hnot ⟨i, hab.1.symm⟩)
      (fun i j hij ↦ by
        rw [Function.onFun, disjoint_edgeSet, disjoint_iff_adj]
        intro a b hi hj
        exact disjoint_iff_adj.1 (hdisj hij) a b hi.1 hj.1)
    have h2 := Set.ncard_sdiff_singleton_add_one he (Set.toFinite _)
    have h3 := hcond S ⟨u, hu⟩
    have h4 : ∑ _i : Fin k, (#S - 1) ≤ ∑ i, ((F i ⊓ H).induce (S : Set V)).edgeSet.ncard :=
      sum_le_sum fun i _ ↦ by
        have := (hconn i).card_vert_le_card_edgeSet_add_one
        rw [Nat.card_coe_set_eq (((F i ⊓ H).induce (S : Set V)).edgeSet), hcardS] at this
        omega
    simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul] at h4
    omega

/-- **Corollary.** A finite `2k`-edge-connected graph on a nonempty vertex type has `k` pairwise
edge-disjoint spanning trees. -/
theorem exists_trees_of_isEdgeConnected {V : Type*} [Finite V] [Nonempty V]
    (G : SimpleGraph V) (k : ℕ) (hG : G.IsEdgeConnected (2 * k)) :
    ∃ T : Fin k → SimpleGraph V, (∀ i, T i ≤ G ∧ (T i).IsTree) ∧
      Pairwise fun i j ↦ Disjoint (T i) (T j) := by
  have := Fintype.ofFinite V
  classical
  refine (tree_packing G k).2 fun f ↦ ?_
  by_cases hm : #(univ.image f) ≤ 1
  · simp [Nat.sub_eq_zero_of_le hm]
  push Not at hm
  set K := G ⊓ (⊤ : SimpleGraph V).comap f
  have hfib : ∀ r ∈ univ.image f, 2 * k ≤ #(univ.filter fun d : K.Dart ↦ f d.fst = r) := by
    intro r hr
    obtain ⟨x, -, hx⟩ := mem_image.1 hr
    obtain ⟨r', hr', hr'r⟩ := exists_mem_ne hm r
    obtain ⟨y, -, hy⟩ := mem_image.1 hr'
    by_contra hlt
    push Not at hlt
    set s : Set (Sym2 V) :=
      ↑((univ.filter fun d : K.Dart ↦ f d.fst = r).image Dart.edge)
    have hs : s.encard < (2 * k : ℕ) := by
      rw [Set.encard_coe_eq_coe_finsetCard]
      exact_mod_cast card_image_le.trans_lt hlt
    have hreach := hG x y hs
    have : f y = r := reachable_closed (fun w ↦ f w = r) (fun a b hab ha ↦ by
      by_contra hb
      rw [deleteEdges_adj] at hab
      refine hab.2 ?_
      have hK : K.Adj a b := ⟨hab.1, by simp [ha, Ne.symm hb]⟩
      exact mem_image.2 ⟨⟨(a, b), hK⟩, by simp [ha], rfl⟩) hreach hx
    exact hr'r (hy.symm.trans this)
  have hdart : Fintype.card K.Dart =
      ∑ r ∈ univ.image f, #(univ.filter fun d : K.Dart ↦ f d.fst = r) :=
    card_eq_sum_card_fiberwise fun d _ ↦ mem_image_of_mem _ (mem_univ _)
  have hsum : ∑ _r ∈ univ.image f, 2 * k ≤
      ∑ r ∈ univ.image f, #(univ.filter fun d : K.Dart ↦ f d.fst = r) :=
    sum_le_sum hfib
  have h2 := K.dart_card_eq_twice_card_edges
  simp only [edgeFinset_card, Fintype.card_eq_nat_card, Nat.card_coe_set_eq] at h2 hdart
  rw [h2] at hdart
  rw [sum_const, smul_eq_mul, ← hdart] at hsum
  have hcount : k * #(univ.image f) ≤ K.edgeSet.ncard := by
    rw [Nat.mul_comm (#(univ.image f)) (2 * k), Nat.mul_assoc] at hsum
    omega
  exact (Nat.mul_le_mul_left _ (Nat.sub_le _ _)).trans hcount

end NashWilliamsTutte
