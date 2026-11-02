/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Tutte
public import Mathlib.Basic.Finite.Sum
public import Mathlib.Data.Fintype.Lattice
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Tactic.Choose
public import Mathlib.Tactic.Convert
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Tauto
/-!

Imported from [jtraverso/berge-matching](https://github.com/jtraverso/berge-matching/blob/b9c91bfbbe08ee7266ee3cb3543dff4e4ca8bc8c/BergeLib/Berge.lean), registered as PALOMAR-2026-10-16-000011. The original proof is retained; module paths and imports are adapted for this collection.

# Berge's augmenting path theorem and the Tutte–Berge formula

For a finite simple graph `G` and a matching `M` (Mathlib's `Subgraph.IsMatching`):

* `BergeMatching.isMaximum_iff_not_exists_augmenting`: **Berge (1957).** `M` has maximum size
  among all matchings if and only if there is no `M`-augmenting path: a path whose two distinct
  end vertices are not covered by `M` and whose edges alternate between edges outside `M` and
  edges of `M`, starting with an edge outside `M`.
* `BergeMatching.two_mul_card_add_le`: weak Tutte–Berge inequality: for every matching `M` and
  every vertex set `U`, `2 |M| + odd(G − U) ≤ |V| + |U|`, where `odd(G − U)` is the number of
  connected components of odd order of `G − U`.
* `BergeMatching.exists_tutte_berge`: **Tutte–Berge formula (Berge 1958).** There are a matching
  `M` and a vertex set `U` with `2 |M| + odd(G − U) = |V| + |U|`; so the maximum size of a
  matching is the minimum of `(|V| + |U| - odd(G - U)) / 2`.
-/

@[expose] public section

open SimpleGraph

namespace BergeMatching

variable {V : Type*}

/-- The number of connected components of odd order of `G − U` (as in Mathlib's
`SimpleGraph.IsTutteViolator`). -/
noncomputable def oddCount (G : SimpleGraph V) (U : Set V) : ℕ :=
  ((⊤ : G.Subgraph).deleteVerts U).coe.oddComponents.ncard

/-- `p` is an `M`-augmenting path: a path between two distinct vertices not covered by `M`, whose
`i`-th edge lies in `M` exactly when `i` is odd. -/
def IsAugmentingPath {G : SimpleGraph V} (M : G.Subgraph) {u v : V} (p : G.Walk u v) : Prop :=
  p.IsPath ∧ u ≠ v ∧ u ∉ M.verts ∧ v ∉ M.verts ∧
    ∀ i < p.length, (s(p.getVert i, p.getVert (i + 1)) ∈ M.edgeSet ↔ Odd i)

private lemma ncard_oddComponents_congr {W W' : Type*} {H : SimpleGraph W} {H' : SimpleGraph W'}
    (e : H ≃g H') : H.oddComponents.ncard = H'.oddComponents.ncard := by
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
  refine Nat.card_congr (e.connectedComponentEquiv.subtypeEquiv fun c => ?_)
  simp only [Set.mem_ofPred_eq]
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq,
    Nat.card_congr (ConnectedComponent.isoEquivSupp e c)]

open Finset in
private lemma ncard_verts_eq_two_mul [Finite V] {G : SimpleGraph V} {M : G.Subgraph}
    (hM : M.IsMatching) : M.verts.ncard = 2 * M.edgeSet.ncard := by
  classical
  have := Fintype.ofFinite V
  have h := M.spanningCoe.sum_degrees_eq_twice_card_edges
  have hdeg : ∀ v, M.spanningCoe.degree v = if v ∈ M.verts then 1 else 0 := by
    intro v
    rw [Subgraph.degree_spanningCoe]
    split_ifs with hv
    · exact (Subgraph.isMatching_iff_forall_degree.1 hM) v hv
    · exact Subgraph.degree_of_notMem_verts hv
  simp only [hdeg, Finset.sum_boole, Nat.cast_id] at h
  have e1 : M.verts.ncard = #{x | x ∈ M.verts} := by
    rw [← Set.ncard_coe_finset]; congr; ext; simp
  have e2 : M.edgeSet.ncard = #M.spanningCoe.edgeFinset := by
    rw [← Set.ncard_coe_finset, coe_edgeFinset, Subgraph.edgeSet_spanningCoe]
  rw [e1, e2, h]

/-- The graph `G` with `d` extra universal vertices. -/
private def aug (G : SimpleGraph V) (d : ℕ) : SimpleGraph (V ⊕ Fin d) where
  Adj x y := x ≠ y ∧ ∀ a b, x = .inl a → y = .inl b → G.Adj a b
  symm := ⟨fun _ _ h => ⟨h.1.symm, fun a b hx hy => (h.2 b a hy hx).symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

@[simp] private lemma aug_adj_inl_inl {G : SimpleGraph V} {d : ℕ} {a b : V} :
    (aug G d).Adj (.inl a) (.inl b) ↔ G.Adj a b := by
  change _ ∧ _ ↔ _
  refine ⟨fun h => h.2 a b rfl rfl, fun h => ⟨fun h' => h.ne (Sum.inl_injective h'), ?_⟩⟩
  rintro a' b' ha hb
  cases ha; cases hb; exact h

@[simp] private lemma aug_adj_inl_inr {G : SimpleGraph V} {d : ℕ} {a : V} {i : Fin d} :
    (aug G d).Adj (.inl a) (.inr i) :=
  show _ ∧ _ from ⟨Sum.inl_ne_inr, fun _ _ _ h => by cases h⟩

@[simp] private lemma aug_adj_inr_inl {G : SimpleGraph V} {d : ℕ} {a : V} {i : Fin d} :
    (aug G d).Adj (.inr i) (.inl a) :=
  aug_adj_inl_inr.symm

/-- The set of vertices of `aug G d` corresponding to `U` together with all new vertices. -/
private def augSet (U : Set V) (d : ℕ) : Set (V ⊕ Fin d) := Sum.inl '' U ∪ Set.range Sum.inr

@[simp] private lemma inl_mem_augSet {U : Set V} {d : ℕ} {a : V} :
    (Sum.inl a : V ⊕ Fin d) ∈ augSet U d ↔ a ∈ U := by
  simp [augSet]

@[simp] private lemma inr_mem_augSet {U : Set V} {d : ℕ} {i : Fin d} :
    (Sum.inr i : V ⊕ Fin d) ∈ augSet U d := by
  simp [augSet]

private lemma ncard_augSet [Finite V] (U : Set V) (d : ℕ) : (augSet U d).ncard = U.ncard + d := by
  rw [augSet, Set.ncard_union_eq, Set.ncard_image_of_injective _ Sum.inl_injective,
    Set.ncard_range_of_injective Sum.inr_injective, Nat.card_eq_fintype_card, Fintype.card_fin]
  rw [Set.disjoint_left]
  rintro _ ⟨a, _, rfl⟩ ⟨i, hi⟩
  cases hi

private lemma oddCount_aug_augSet (G : SimpleGraph V) (U : Set V) (d : ℕ) :
    oddCount (aug G d) (augSet U d) = oddCount G U := by
  let f : ((⊤ : G.Subgraph).deleteVerts U).verts →
      ((⊤ : (aug G d).Subgraph).deleteVerts (augSet U d)).verts :=
    fun a => ⟨Sum.inl a.1, by
      have := a.2
      simp only [Subgraph.deleteVerts_verts, Subgraph.verts_top, Set.mem_sdiff, Set.mem_univ,
        true_and, augSet, Set.mem_union, Set.mem_image, Sum.inl.injEq, exists_eq_right,
        Set.mem_range, reduceCtorEq, exists_false, or_false] at this ⊢
      exact this⟩
  have hf : Function.Bijective f := by
    refine ⟨fun a b h => Subtype.ext (Sum.inl_injective (congrArg Subtype.val h)), ?_⟩
    rintro ⟨x, hx⟩
    simp only [Subgraph.deleteVerts_verts, Subgraph.verts_top, Set.mem_sdiff, Set.mem_univ,
      true_and, augSet, Set.mem_union, Set.mem_image, Set.mem_range, not_or] at hx
    rcases x with a | i
    · refine ⟨⟨a, ?_⟩, rfl⟩
      simp only [Subgraph.deleteVerts_verts, Subgraph.verts_top, Set.mem_sdiff, Set.mem_univ,
        true_and]
      exact fun ha => hx.1 ⟨a, ha, rfl⟩
    · exact absurd ⟨i, rfl⟩ hx.2
  let e : ((⊤ : G.Subgraph).deleteVerts U).coe ≃g
      ((⊤ : (aug G d).Subgraph).deleteVerts (augSet U d)).coe :=
    { Equiv.ofBijective f hf with
      map_rel_iff' := by
        intro a b
        simp [f, inl_mem_augSet] }
  exact (ncard_oddComponents_congr e).symm

/-- The copy of a subgraph `M` of `G` inside `aug G d`. -/
private def liftSub {G : SimpleGraph V} (M : G.Subgraph) (d : ℕ) : (aug G d).Subgraph where
  verts := Sum.inl '' M.verts
  Adj x y := ∃ a b, x = .inl a ∧ y = .inl b ∧ M.Adj a b
  adj_sub := by
    rintro _ _ ⟨a, b, rfl, rfl, h⟩
    exact aug_adj_inl_inl.2 (M.adj_sub h)
  edge_vert := by
    rintro _ _ ⟨a, b, rfl, rfl, h⟩
    exact ⟨a, M.edge_vert h, rfl⟩
  symm := ⟨by
    rintro _ _ ⟨a, b, rfl, rfl, h⟩
    exact ⟨b, a, rfl, rfl, h.symm⟩⟩

private lemma liftSub_isMatching {G : SimpleGraph V} {M : G.Subgraph} (hM : M.IsMatching) (d : ℕ) :
    (liftSub M d).IsMatching := by
  rintro _ ⟨a, ha, rfl⟩
  obtain ⟨b, hb, hu⟩ := hM ha
  refine ⟨.inl b, ⟨a, b, rfl, rfl, hb⟩, ?_⟩
  rintro _ ⟨a', b', h1, rfl, h⟩
  cases h1
  rw [hu b' h]

private lemma card_deleteVerts_add [Finite V] (G : SimpleGraph V) (U : Set V) :
    Nat.card ((⊤ : G.Subgraph).deleteVerts U).verts + U.ncard = Nat.card V := by
  have : ((⊤ : G.Subgraph).deleteVerts U).verts = Uᶜ := by ext; simp
  rw [this, Nat.card_coe_set_eq, add_comm, Set.ncard_add_ncard_compl]

private lemma aug_no_tutteViolator [Finite V] (G : SimpleGraph V) (d : ℕ)
    (hd : ∀ U : Set V, oddCount G U ≤ U.ncard + d) (hpar : Even (Nat.card V + d))
    (W : Set (V ⊕ Fin d)) : ¬ (aug G d).IsTutteViolator W := by
  intro hW
  rw [IsTutteViolator] at hW
  by_cases h : ∀ i, Sum.inr i ∈ W
  · have hWeq : W = augSet (Sum.inl ⁻¹' W) d := by
      ext x
      rcases x with a | i
      · simp
      · simp [h i]
    have h1 : oddCount (aug G d) W ≤ W.ncard := by
      rw [hWeq, oddCount_aug_augSet, ncard_augSet]
      exact hd _
    exact absurd hW (not_lt.2 h1)
  · push Not at h
    obtain ⟨i, hi⟩ := h
    set H := ((⊤ : (aug G d).Subgraph).deleteVerts W).coe
    have hj : (Sum.inr i : V ⊕ Fin d) ∈ ((⊤ : (aug G d).Subgraph).deleteVerts W).verts := by
      simpa using hi
    have hconn : ∀ x : ((⊤ : (aug G d).Subgraph).deleteVerts W).verts,
        H.connectedComponentMk x = H.connectedComponentMk ⟨_, hj⟩ := by
      rintro ⟨x, hx⟩
      by_cases hxi : x = Sum.inr i
      · subst hxi; rfl
      · apply ConnectedComponent.connectedComponentMk_eq_of_adj
        have hx' : x ∉ W := by simpa using hx
        simp only [H, Subgraph.coe_adj, Subgraph.deleteVerts_adj, Subgraph.verts_top,
          Set.mem_univ, true_and, Subgraph.top_adj]
        refine ⟨hx', hi, ?_⟩
        rcases x with a | i'
        · exact aug_adj_inl_inr
        · refine ⟨hxi, fun _ _ h _ => by cases h⟩
    have hle : H.oddComponents.ncard ≤ 1 := by
      refine (Set.ncard_le_one (Set.toFinite _)).2 fun c _ c' _ => ?_
      induction c using ConnectedComponent.ind
      induction c' using ConnectedComponent.ind
      exact (hconn _).trans (hconn _).symm
    have hW0 : W.ncard = 0 := by
      change W.ncard < H.oddComponents.ncard at hW
      omega
    have hodd : Odd H.oddComponents.ncard := by
      change W.ncard < H.oddComponents.ncard at hW
      have : H.oddComponents.ncard = 1 := by omega
      rw [this]; exact odd_one
    rw [odd_ncard_oddComponents] at hodd
    have := card_deleteVerts_add (aug G d) W
    rw [hW0, Nat.card_sum, Nat.card_eq_fintype_card (α := Fin d), Fintype.card_fin] at this
    rw [Nat.add_zero] at this
    change Odd (Nat.card ((⊤ : (aug G d).Subgraph).deleteVerts W).verts) at hodd
    rw [this] at hodd
    exact (Nat.not_even_iff_odd.2 hodd) hpar

section BergeHelpers

variable {G : SimpleGraph V}

/-- Deleting a matched pair from a matching. -/
private lemma deleteVerts_pair_isMatching {M : G.Subgraph} (hM : M.IsMatching) {a b : V}
    (hab : M.Adj a b) : (M.deleteVerts {a, b}).IsMatching := by
  intro x hx
  simp only [Subgraph.deleteVerts_verts, Set.mem_sdiff, Set.mem_insert_iff,
    Set.mem_singleton_iff, not_or] at hx
  obtain ⟨y, hy, hu⟩ := hM hx.1
  have hya : y ≠ a := by
    rintro rfl
    exact hx.2.2 (hM.eq_of_adj_left hy.symm hab)
  have hyb : y ≠ b := by
    rintro rfl
    exact hx.2.1 (hM.eq_of_adj_right hy hab)
  refine ⟨y, ?_, fun z hz => hu z (Subgraph.deleteVerts_adj.1 hz).2.2.2.2⟩
  simp only [Subgraph.deleteVerts_adj, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
  exact ⟨hx.1, hx.2, M.edge_vert hy.symm, ⟨hya, hyb⟩, hy⟩

private lemma deleteVerts_pair_adj_iff {M : G.Subgraph} (hM : M.IsMatching) {a b x y : V}
    (hab : M.Adj a b) (hx : x ≠ a) (hy : y ≠ a) :
    (M.deleteVerts {a, b}).Adj x y ↔ M.Adj x y := by
  simp only [Subgraph.deleteVerts_adj, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
  refine ⟨fun h => h.2.2.2.2, fun h => ⟨M.edge_vert h, ⟨hx, ?_⟩, M.edge_vert h.symm, ⟨hy, ?_⟩, h⟩⟩
  · rintro rfl; exact hy (hM.eq_of_adj_left h hab.symm)
  · rintro rfl; exact hx (hM.eq_of_adj_right h hab)

private lemma edgeSet_deleteVerts_pair {M : G.Subgraph} (hM : M.IsMatching) {a b : V}
    (hab : M.Adj a b) : (M.deleteVerts {a, b}).edgeSet = M.edgeSet \ {s(a, b)} := by
  ext e
  induction e using Sym2.ind with
  | h x y =>
  simp only [Subgraph.mem_edgeSet, Subgraph.deleteVerts_adj, Set.mem_insert_iff,
    Set.mem_singleton_iff, not_or, Set.mem_sdiff]
  constructor
  · rintro ⟨_, ⟨hxa, hxb⟩, _, _, h⟩
    refine ⟨h, fun he => ?_⟩
    rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hxa rfl
    · exact hxb rfl
  · rintro ⟨h, hne⟩
    have hxa : x ≠ a := by
      rintro rfl; exact hne (by rw [hM.eq_of_adj_left h hab])
    have hxb : x ≠ b := by
      rintro rfl; exact hne (by rw [hM.eq_of_adj_left h hab.symm, Sym2.eq_swap])
    have hya : y ≠ a := by
      rintro rfl; exact hne (by rw [hM.eq_of_adj_right h hab.symm, Sym2.eq_swap])
    have hyb : y ≠ b := by
      rintro rfl; exact hne (by rw [hM.eq_of_adj_right h hab])
    exact ⟨M.edge_vert h, ⟨hxa, hxb⟩, M.edge_vert h.symm, ⟨hya, hyb⟩, h⟩

private lemma ncard_edgeSet_deleteVerts_pair {M : G.Subgraph} (hM : M.IsMatching)
    {a b : V}
    (hab : M.Adj a b) : (M.deleteVerts {a, b}).edgeSet.ncard = M.edgeSet.ncard - 1 := by
  rw [edgeSet_deleteVerts_pair hM hab,
    Set.ncard_sdiff_singleton_of_mem (show s(a, b) ∈ M.edgeSet from hab)]

private lemma not_mem_edgeSet_of_not_mem_verts {M : G.Subgraph} {a b : V} (ha : a ∉ M.verts) :
    s(a, b) ∉ M.edgeSet := fun h => ha (M.edge_vert h)

private lemma IsAugmentingPath.odd_length {M : G.Subgraph} {u v : V} {p : G.Walk u v}
    (hp : IsAugmentingPath M p) : Odd p.length := by
  have hL : p.length ≠ 0 := fun h => hp.2.1 (Walk.eq_of_length_eq_zero h)
  have := hp.2.2.2.2 (p.length - 1) (by omega)
  rw [show p.length - 1 + 1 = p.length by omega, Walk.getVert_length] at this
  have h2 : ¬ Odd (p.length - 1) := fun h => by
    rw [← this, Sym2.eq_swap] at h
    exact not_mem_edgeSet_of_not_mem_verts hp.2.2.2.1 h
  rcases Nat.even_or_odd p.length with h | h
  · exfalso; apply h2
    obtain ⟨k, hk⟩ := h
    exact ⟨k - 1, by omega⟩
  · exact h

private lemma IsAugmentingPath.reverse {M : G.Subgraph} {u v : V} {p : G.Walk u v}
    (hp : IsAugmentingPath M p) : IsAugmentingPath M p.reverse := by
  have hodd := hp.odd_length
  refine ⟨hp.1.reverse, hp.2.1.symm, hp.2.2.2.1, hp.2.2.1, fun i hi => ?_⟩
  rw [Walk.length_reverse] at hi
  rw [Walk.getVert_reverse, Walk.getVert_reverse]
  have := hp.2.2.2.2 (p.length - (i + 1)) (by omega)
  rw [show p.length - (i + 1) + 1 = p.length - i by omega, Sym2.eq_swap] at this
  rw [this]
  obtain ⟨k, hk⟩ := hodd
  rw [Nat.odd_iff, Nat.odd_iff]
  omega

private lemma IsMatching.sup_subgraphOfAdj_deleteVerts {M : G.Subgraph} (hM : M.IsMatching)
    {u w1 w2 : V}
    (h : G.Adj u w1) (hu : u ∉ M.verts) (e1 : M.Adj w1 w2) :
    (M.deleteVerts {w1, w2} ⊔ G.subgraphOfAdj h).IsMatching := by
  refine (deleteVerts_pair_isMatching hM e1).sup (Subgraph.IsMatching.subgraphOfAdj h) ?_
  rw [(deleteVerts_pair_isMatching hM e1).support_eq_verts,
    (Subgraph.IsMatching.subgraphOfAdj h).support_eq_verts, subgraphOfAdj_verts,
    Set.disjoint_left]
  intro x hx hx'
  simp only [Subgraph.deleteVerts_verts, Set.mem_sdiff, Set.mem_insert_iff,
    Set.mem_singleton_iff, not_or] at hx hx'
  rcases hx' with rfl | rfl
  · exact hu hx.1
  · exact hx.2.1 rfl

private theorem exists_larger_of_augmenting [Finite V] :
    ∀ {u v : V} (p : G.Walk u v) (M : G.Subgraph), M.IsMatching → IsAugmentingPath M p →
      ∃ M' : G.Subgraph, M'.IsMatching ∧ M.edgeSet.ncard < M'.edgeSet.ncard
  | _, _, .nil, _, _, hp => absurd rfl hp.2.1
  | _, _, .cons h .nil, M, hM, hp => by
    refine ⟨M ⊔ G.subgraphOfAdj h, hM.sup (Subgraph.IsMatching.subgraphOfAdj h) ?_, ?_⟩
    · rw [hM.support_eq_verts, (Subgraph.IsMatching.subgraphOfAdj h).support_eq_verts,
        subgraphOfAdj_verts, Set.disjoint_left]
      intro x hx hx'
      rcases hx' with rfl | rfl
      · exact hp.2.2.1 hx
      · exact hp.2.2.2.1 hx
    · rw [Subgraph.edgeSet_sup, edgeSet_subgraphOfAdj, Set.union_singleton,
        Set.ncard_insert_of_notMem (not_mem_edgeSet_of_not_mem_verts hp.2.2.1)]
      omega
  | u, v, .cons (v := w1) h (.cons (v := w2) h2 r), M, hM, hp => by
    obtain ⟨hpath, huv, hu, hv, he⟩ := hp
    have e1 : M.Adj w1 w2 := by
      have := (he 1 (by simp)).2 odd_one
      simpa using this
    rw [Walk.cons_isPath_iff, Walk.cons_isPath_iff, Walk.support_cons, List.mem_cons,
      not_or] at hpath
    obtain ⟨⟨hr, hw1⟩, huw1, hur⟩ := hpath
    set M1 := M.deleteVerts {w1, w2} ⊔ G.subgraphOfAdj h with hM1def
    have hM1 : M1.IsMatching := IsMatching.sup_subgraphOfAdj_deleteVerts hM h hu e1
    have hcount : M1.edgeSet.ncard = M.edgeSet.ncard := by
      have hpos : 0 < M.edgeSet.ncard :=
        (Set.ncard_pos (Set.toFinite _)).2 ⟨_, show s(w1, w2) ∈ M.edgeSet from e1⟩
      rw [hM1def, Subgraph.edgeSet_sup, edgeSet_deleteVerts_pair hM e1, edgeSet_subgraphOfAdj,
        Set.union_singleton, Set.ncard_insert_of_notMem
          (fun hm => not_mem_edgeSet_of_not_mem_verts hu hm.1),
        Set.ncard_sdiff_singleton_of_mem (show s(w1, w2) ∈ M.edgeSet from e1)]
      omega
    have hadj : ∀ a b, a ∈ r.support → b ∈ r.support → (M1.Adj a b ↔ M.Adj a b) := by
      intro a b ha hb
      have hau : a ≠ u := fun h' => hur (h' ▸ ha)
      have haw : a ≠ w1 := fun h' => hw1 (h' ▸ ha)
      have hbw : b ≠ w1 := fun h' => hw1 (h' ▸ hb)
      rw [hM1def, Subgraph.sup_adj, subgraphOfAdj_adj, deleteVerts_pair_adj_iff hM e1 haw hbw]
      refine ⟨fun h' => h'.elim id fun he' => ?_, Or.inl⟩
      rcases Sym2.eq_iff.1 he' with ⟨h1, _⟩ | ⟨_, h1⟩
      · exact absurd h1.symm hau
      · exact absurd h1.symm haw
    have hr' : IsAugmentingPath M1 r := by
      refine ⟨hr, ?_, ?_, ?_, fun i hi => ?_⟩
      · rintro rfl; exact hv (M.edge_vert e1.symm)
      · have h2u : w2 ≠ u := fun h' => hur (h' ▸ r.start_mem_support)
        have h2w : w2 ≠ w1 := fun h' => hw1 (h' ▸ r.start_mem_support)
        rw [hM1def, Subgraph.verts_sup, subgraphOfAdj_verts]
        simp [h2u, h2w]
      · have hvu : v ≠ u := fun h' => hur (h' ▸ r.end_mem_support)
        have hvw : v ≠ w1 := fun h' => hw1 (h' ▸ r.end_mem_support)
        rw [hM1def, Subgraph.verts_sup, subgraphOfAdj_verts]
        simp [hv, hvu, hvw]
      · have := he (i + 2) (by simp; omega)
        simp only [Walk.getVert_cons_succ] at this
        rw [Subgraph.mem_edgeSet, hadj _ _ (r.getVert_mem_support _) (r.getVert_mem_support _),
          ← Subgraph.mem_edgeSet, this, Nat.odd_iff, Nat.odd_iff]
        omega
    obtain ⟨M2, hM2, hlt⟩ := exists_larger_of_augmenting r M1 hM1 hr'
    exact ⟨M2, hM2, hcount ▸ hlt⟩

private lemma IsAugmentingPath.of_deleteVerts_pair {M : G.Subgraph} (hM : M.IsMatching)
    {x1 x2 a b : V}
    (hx12 : M.Adj x1 x2) {Q : G.Walk a b} (hQ : IsAugmentingPath (M.deleteVerts {x1, x2}) Q)
    (hQx1 : ∀ w ∈ Q.support, w ≠ x1) (ha : a ≠ x2) (hb : b ≠ x2) : IsAugmentingPath M Q := by
  obtain ⟨hpath, hab, ha0, hb0, he⟩ := hQ
  refine ⟨hpath, hab, fun h => ha0 ?_, fun h => hb0 ?_, fun i hi => ?_⟩
  · simp [h, hQx1 a Q.start_mem_support, ha]
  · simp [h, hQx1 b Q.end_mem_support, hb]
  · rw [← he i hi, Subgraph.mem_edgeSet, Subgraph.mem_edgeSet,
      deleteVerts_pair_adj_iff hM hx12 (hQx1 _ (Q.getVert_mem_support _))
        (hQx1 _ (Q.getVert_mem_support _))]

private lemma IsAugmentingPath.cons_cons_deleteVerts_pair {M : G.Subgraph} (hM : M.IsMatching)
    {x x1 x2 b : V} (hx12 : M.Adj x1 x2) (h : G.Adj x x1) (hx : x ∉ M.verts) {Q : G.Walk x2 b}
    (hQ : IsAugmentingPath (M.deleteVerts {x1, x2}) Q)
    (hQx : ∀ w ∈ Q.support, w ≠ x ∧ w ≠ x1) :
    IsAugmentingPath M (.cons h (.cons (M.adj_sub hx12) Q)) := by
  obtain ⟨hpath, hab, ha0, hb0, he⟩ := hQ
  have hxx1 : x ≠ x1 := h.ne
  refine ⟨?_, fun h' => (hQx b Q.end_mem_support).1 h'.symm, hx, fun h' => hb0 ?_,
    fun i hi => ?_⟩
  · rw [Walk.cons_isPath_iff, Walk.cons_isPath_iff, Walk.support_cons, List.mem_cons, not_or]
    exact ⟨⟨hpath, fun h' => (hQx _ h').2 rfl⟩, hxx1, fun h' => (hQx _ h').1 rfl⟩
  · simp [h', (hQx b Q.end_mem_support).2, hab.symm]
  · rcases i with _ | _ | j
    · simp only [Walk.getVert_zero, zero_add, Walk.getVert_cons_succ]
      simp only [Nat.not_odd_zero, iff_false]
      exact not_mem_edgeSet_of_not_mem_verts hx
    · simp only [zero_add, Walk.getVert_cons_succ, Walk.getVert_zero, odd_one, iff_true]
      exact hx12
    · simp only [Walk.getVert_cons_succ, Walk.length_cons] at hi ⊢
      rw [Subgraph.mem_edgeSet, ← deleteVerts_pair_adj_iff hM hx12
        (hQx _ (Q.getVert_mem_support _)).2 (hQx _ (Q.getVert_mem_support _)).2,
        ← Subgraph.mem_edgeSet, he j (by omega), Nat.odd_iff, Nat.odd_iff]
      omega

private theorem exists_augmenting_aux [Finite V] (n : ℕ) :
    ∀ (F : Set V) (M M' : G.Subgraph), M.IsMatching → M'.IsMatching →
      M'.edgeSet.ncard = n → M.edgeSet.ncard < n → Disjoint M'.verts F →
      ∃ (u v : V) (p : G.Walk u v), IsAugmentingPath M p ∧ ∀ w ∈ p.support, w ∉ F := by
  induction n with
  | zero => intros; omega
  | succ n ih =>
    intro F M M' hM hM' hn hlt hF
    obtain ⟨x, hxM', hxM⟩ : ∃ x, x ∈ M'.verts ∧ x ∉ M.verts := by
      by_contra hcon
      push Not at hcon
      have := Set.ncard_le_ncard hcon
      rw [ncard_verts_eq_two_mul hM, ncard_verts_eq_two_mul hM'] at this
      omega
    obtain ⟨x1, hx1, -⟩ := hM' hxM'
    have hxF : x ∉ F := Set.disjoint_left.1 hF hxM'
    have hx1F : x1 ∉ F := Set.disjoint_left.1 hF (M'.edge_vert hx1.symm)
    have hxx1 : x ≠ x1 := (M'.adj_sub hx1).ne
    by_cases hx1M : x1 ∉ M.verts
    · refine ⟨x, x1, .cons (M'.adj_sub hx1) .nil, ⟨?_, hxx1, hxM, hx1M, ?_⟩, ?_⟩
      · simp [Walk.cons_isPath_iff, hxx1]
      · intro i hi
        simp only [Walk.length_cons, Walk.length_nil, zero_add, Nat.lt_one_iff] at hi
        subst hi
        simp only [Walk.getVert_zero, zero_add, Walk.getVert_cons_succ, Nat.not_odd_zero,
          iff_false]
        exact not_mem_edgeSet_of_not_mem_verts hxM
      · simp [hxF, hx1F]
    · push Not at hx1M
      obtain ⟨x2, hx12, -⟩ := hM hx1M
      have hM0 := deleteVerts_pair_isMatching hM hx12
      have hM0' := deleteVerts_pair_isMatching hM' hx1
      have hn0 : (M'.deleteVerts {x, x1}).edgeSet.ncard = n := by
        rw [ncard_edgeSet_deleteVerts_pair hM' hx1]; omega
      have hlt0 : (M.deleteVerts {x1, x2}).edgeSet.ncard < n := by
        have hpos : 0 < M.edgeSet.ncard :=
          (Set.ncard_pos (Set.toFinite _)).2 ⟨_, show s(x1, x2) ∈ M.edgeSet from hx12⟩
        rw [ncard_edgeSet_deleteVerts_pair hM hx12]; omega
      have hF0 : Disjoint (M'.deleteVerts {x, x1}).verts (insert x (insert x1 F)) := by
        rw [Set.disjoint_left]
        intro a ha
        simp only [Subgraph.deleteVerts_verts, Set.mem_sdiff, Set.mem_insert_iff,
          Set.mem_singleton_iff, not_or] at ha ⊢
        exact ⟨ha.2.1, ha.2.2, Set.disjoint_left.1 hF ha.1⟩
      obtain ⟨y, z, P, hP, hPF⟩ := ih _ _ _ hM0 hM0' hn0 hlt0 hF0
      have hPx : ∀ w ∈ P.support, w ≠ x ∧ w ≠ x1 ∧ w ∉ F := by
        intro w hw
        have := hPF w hw
        simp only [Set.mem_insert_iff, not_or] at this
        exact this
      by_cases hy : y = x2
      · subst hy
        refine ⟨x, z, _, hP.cons_cons_deleteVerts_pair hM hx12 (M'.adj_sub hx1) hxM
          fun w hw => ⟨(hPx w hw).1, (hPx w hw).2.1⟩, ?_⟩
        intro w hw
        simp only [Walk.support_cons, List.mem_cons] at hw
        rcases hw with rfl | rfl | hw
        · exact hxF
        · exact hx1F
        · exact (hPx w hw).2.2
      · by_cases hz : z = x2
        · subst hz
          have hPx' : ∀ w ∈ P.reverse.support, w ≠ x ∧ w ≠ x1 ∧ w ∉ F := by
            intro w hw
            rw [Walk.support_reverse, List.mem_reverse] at hw
            exact hPx w hw
          refine ⟨x, y, _, hP.reverse.cons_cons_deleteVerts_pair hM hx12 (M'.adj_sub hx1) hxM
            fun w hw => ⟨(hPx' w hw).1, (hPx' w hw).2.1⟩, ?_⟩
          intro w hw
          simp only [Walk.support_cons, List.mem_cons] at hw
          rcases hw with rfl | rfl | hw
          · exact hxF
          · exact hx1F
          · exact (hPx' w hw).2.2
        · exact ⟨y, z, P, hP.of_deleteVerts_pair hM hx12 (fun w hw => (hPx w hw).2.1) hy hz,
            fun w hw => (hPx w hw).2.2⟩

end BergeHelpers

/-- **Berge's theorem (1957).** A matching of a finite graph is maximum if and only if there is no
augmenting path. -/
theorem isMaximum_iff_not_exists_augmenting [Finite V] {G : SimpleGraph V} {M : G.Subgraph}
    (hM : M.IsMatching) :
    (∀ M' : G.Subgraph, M'.IsMatching → M'.edgeSet.ncard ≤ M.edgeSet.ncard) ↔
      ¬ ∃ (u v : V) (p : G.Walk u v), IsAugmentingPath M p := by
  constructor
  · rintro hmax ⟨u, v, p, hp⟩
    obtain ⟨M', hM', hlt⟩ := exists_larger_of_augmenting p M hM hp
    exact absurd (hmax M' hM') (not_le.2 hlt)
  · intro hno M' hM'
    by_contra hlt
    push Not at hlt
    obtain ⟨u, v, p, hp, -⟩ := exists_augmenting_aux _ ∅ M M' hM hM' rfl hlt
      (Set.disjoint_empty _)
    exact hno ⟨u, v, p, hp⟩

/-- **Weak Tutte–Berge inequality.** For every matching `M` and vertex set `U` of a finite graph,
`2 |M| + odd(G − U) ≤ |V| + |U|`. -/
theorem two_mul_card_add_le [Finite V] {G : SimpleGraph V} {M : G.Subgraph} (hM : M.IsMatching)
    (U : Set V) : 2 * M.edgeSet.ncard + oddCount G U ≤ Nat.card V + U.ncard := by
  classical
  set d := (M.vertsᶜ).ncard with hd
  let s : Set (V ⊕ Fin d) := Sum.inl '' M.vertsᶜ
  let t : Set (V ⊕ Fin d) := Set.range Sum.inr
  have hst : Disjoint s t := by
    rw [Set.disjoint_left]
    rintro _ ⟨a, _, rfl⟩ ⟨i, hi⟩
    cases hi
  have hcard : Nat.card s = Nat.card t := by
    rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq, Set.ncard_image_of_injective _ Sum.inl_injective,
      Set.ncard_range_of_injective Sum.inr_injective, Nat.card_eq_fintype_card, Fintype.card_fin]
  obtain ⟨f⟩ := Finite.card_eq.1 hcard
  have hadj : ∀ v : s, (aug G d).Adj v (f v) := by
    rintro ⟨_, a, _, rfl⟩
    generalize f _ = y
    obtain ⟨_, i, rfl⟩ := y
    exact aug_adj_inl_inr
  obtain ⟨M2, hM2v, hM2⟩ := Subgraph.IsMatching.exists_of_disjoint_sets_of_equiv hst f hadj
  have hM1 := liftSub_isMatching hM d
  have hdisj : Disjoint (liftSub M d).support M2.support := by
    rw [hM1.support_eq_verts, hM2.support_eq_verts, hM2v, Set.disjoint_union_right]
    refine ⟨?_, ?_⟩
    · rw [Set.disjoint_left]
      rintro _ ⟨a, ha, rfl⟩ ⟨b, hb, hab⟩
      cases hab
      exact hb ha
    · rw [Set.disjoint_left]
      rintro _ ⟨a, _, rfl⟩ ⟨i, hi⟩
      cases hi
  have hperf : (liftSub M d ⊔ M2).IsPerfectMatching := by
    refine ⟨hM1.sup hM2 hdisj, fun x => ?_⟩
    rw [Subgraph.verts_sup, hM2v]
    rcases x with a | i
    · by_cases ha : a ∈ M.verts
      · exact Or.inl ⟨a, ha, rfl⟩
      · exact Or.inr (Or.inl ⟨a, ha, rfl⟩)
    · exact Or.inr (Or.inr ⟨i, rfl⟩)
  have h1 := not_isTutteViolator_of_isPerfectMatching hperf (augSet U d)
  rw [IsTutteViolator, not_lt] at h1
  have h2 : oddCount (aug G d) (augSet U d) ≤ U.ncard + d := by
    rw [← ncard_augSet]; exact h1
  rw [oddCount_aug_augSet] at h2
  have h3 := Set.ncard_add_ncard_compl M.verts
  rw [ncard_verts_eq_two_mul hM] at h3
  omega

/-- **The Tutte–Berge formula.** A finite graph has a matching `M` and a vertex set `U` with
`2 |M| + odd(G − U) = |V| + |U|`. -/
theorem exists_tutte_berge [Finite V] (G : SimpleGraph V) :
    ∃ (M : G.Subgraph) (U : Set V), M.IsMatching ∧
      2 * M.edgeSet.ncard + oddCount G U = Nat.card V + U.ncard := by
  classical
  obtain ⟨U0, hU0⟩ := Finite.exists_max (fun U : Set V => (oddCount G U : ℤ) - U.ncard)
  have hge : U0.ncard ≤ oddCount G U0 := by
    have := hU0 ∅
    simp only [Set.ncard_empty, Nat.cast_zero, sub_zero] at this
    omega
  set d := oddCount G U0 - U0.ncard with hd
  have hdU : ∀ U : Set V, oddCount G U ≤ U.ncard + d := by
    intro U
    have := hU0 U
    omega
  have hpar : Even (Nat.card V + d) := by
    have h1 := (odd_ncard_oddComponents (G := ((⊤ : G.Subgraph).deleteVerts U0).coe))
    have h2 := card_deleteVerts_add G U0
    change Odd (oddCount G U0) ↔ _ at h1
    rw [← h2]
    rcases Nat.even_or_odd (oddCount G U0) with he | ho
    · have : Even (Nat.card ((⊤ : G.Subgraph).deleteVerts U0).verts) := by
        rw [← Nat.not_odd_iff_even, ← h1, Nat.not_odd_iff_even]; exact he
      have : Nat.card ((⊤ : G.Subgraph).deleteVerts U0).verts + U0.ncard + d =
          Nat.card ((⊤ : G.Subgraph).deleteVerts U0).verts + oddCount G U0 := by omega
      rw [this]; exact Even.add (by assumption) he
    · have h3 := h1.1 ho
      have : Nat.card ((⊤ : G.Subgraph).deleteVerts U0).verts + U0.ncard + d =
          Nat.card ((⊤ : G.Subgraph).deleteVerts U0).verts + oddCount G U0 := by omega
      rw [this]; exact Odd.add_odd h3 ho
  obtain ⟨M', hM'⟩ := tutte.2 (aug_no_tutteViolator G d hdU hpar)
  let M : G.Subgraph :=
    { verts := {a | ∃ b, M'.Adj (.inl a) (.inl b)}
      Adj a b := M'.Adj (.inl a) (.inl b)
      adj_sub := fun h => aug_adj_inl_inl.1 (M'.adj_sub h)
      edge_vert := fun h => ⟨_, h⟩
      symm := ⟨fun _ _ h => h.symm⟩ }
  have hM : M.IsMatching := by
    rintro a ⟨b, hb⟩
    exact ⟨b, hb, fun c hc => Sum.inl_injective (hM'.1.eq_of_adj_left hc hb)⟩
  have hp : ∀ a : V, ∃ y, M'.Adj (.inl a) y := fun a => (hM'.1 (hM'.2 (.inl a))).exists
  choose p hp using hp
  have hcompl : (M.vertsᶜ).ncard ≤ d := by
    have := Set.ncard_le_ncard_of_injOn (s := M.vertsᶜ)
      (t := Set.range (Sum.inr : Fin d → V ⊕ Fin d)) p ?_ ?_
    · rwa [Set.ncard_range_of_injective Sum.inr_injective, Nat.card_eq_fintype_card,
        Fintype.card_fin] at this
    · intro a ha
      rcases hpa : p a with b | i
      · exact absurd ⟨b, hpa ▸ hp a⟩ ha
      · exact ⟨i, rfl⟩
    · intro a _ a' _ h
      have := hM'.1.eq_of_adj_right (hp a) (h ▸ hp a')
      exact Sum.inl_injective this
  have hweak := two_mul_card_add_le hM U0
  have h3 := Set.ncard_add_ncard_compl M.verts
  rw [ncard_verts_eq_two_mul hM] at h3
  exact ⟨M, U0, hM, by omega⟩

end BergeMatching
